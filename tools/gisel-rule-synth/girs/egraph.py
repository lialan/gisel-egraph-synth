"""Candidates from the e-graph combiner (GIEGraph).

`llc -gisel-egraph-export=<file>` writes one JSON record per region for
which equality saturation found a cheaper form: the typed DAG of the region
and the DAG the extractor selected (format versions 1 to 3, see README.md).
This module turns each record into *candidates* for the same pipeline the
enumerative search feeds: a concrete source expression with the known bits
of its inputs, and a replacement.

A record is a proposal, not a rule. Nothing the e-graph derived is trusted:
each candidate is proved here by SMT under the concrete facts, and then
generalized and proved again by ``synth.Synthesizer.add``.

A region is much larger than the rewrite that made it cheaper, so each
(root of the region, selected expression) pair is reduced:

1. *Common subterms.* A subterm that the source and the replacement share
   is a value the rewrite does not look into. It becomes a variable with
   the known bits of that value. This also removes the operators that have
   no model (a PHI, a pointer operation) when the rewrite leaves them alone.
2. *Context.* If both sides have the same operator at the root, the rewrite
   happened in the operands: each differing operand pair is a candidate of
   its own, if it can be proved without the root. If not (the root makes
   the rewrite valid, e.g. a mask), the pair with the root is the candidate.
3. *Repeated subterms.* A subterm of the source can be any value if the
   candidate is still provable with a variable in its place.

Every reduction step is checked by an SMT proof; a step that cannot be
proved is not taken. Candidates that cannot enter the pipeline are counted
by reason (``Importer.stats``), never dropped silently.

Where the precondition of a candidate comes from (``precondition_source``):

* ``lhs``: the candidate is proved with no fact of its inputs (no known
  bit, no ``noundef``), so the condition of the rewrite follows from the
  matched source; the rule has no guard.
* ``guard``: the proof needs known bits of the inputs; CEGIS turns them
  into the precondition of the rule, which the emitted guard tests.
  A candidate whose facts have no expression in the precondition grammar,
  or that the solver does not decide, is rejected and counted by reason
  (``stats['precondition']``).

Version 3 records also list the e-graph rules whose precondition needed
the known bits of the inputs (``context_facts``, FactSource::Context in
GIEGraph). ``cross_check`` puts every such record in one bucket: it gave a
guarded rule, or a counted rejection, or only candidates that were proved
without facts, or no candidate (``stats['context_facts']``).

A record whose roots are results of one instruction with several results
in the selected DAG (one G_UADDO for the sum and for the carry) is a
rewrite of several roots. If one root reads the other (``c = icmp ult s,
a`` with ``s = add a, b``), the candidate of the reading root is a seed of
a rule with several outputs (``Candidate.joint``, region.py). Roots that do
not read each other are a rule for several roots (sibling.py), which the
import does not make: they are counted (``stats['multi_root']``).
"""

import copy
import json
import os

from . import corpus
from . import discover
from . import ir
from . import ops
from . import synth
from . import vector

# Version 2: fixed vectors ("imm": the constant index of a lane, "mask": the
# mask of a shuffle, the known bits of a vector are those of a lane).
# Version 3: "features" (the parts of the engine that were on), "views"
# (statistics of the analysis views) and "context_facts" (the rules whose
# precondition needed known bits of the inputs, and "known-constant").
FORMAT_VERSIONS = (1, 2, 3)
FORMAT_VERSION = 3


def parse_type(t):
    """The type code (ops.vec) of a type name of the export, or None for a
    type without a model: the parser of the corpus (ops.parse_llt), so a
    scalar, a floating-point value with an IEEE format, or a fixed vector
    of them. A floating-point value is its bit pattern."""
    r = ops.parse_llt(t)
    return None if r is None else r[0]


class Limits:
    """The budgets of the import. A type has separate limits: the bits of
    a lane (``max_width``), the number of lanes and the bits of the whole
    value; a candidate has a limit of operations, of inputs and of SMT
    checks per record."""

    def __init__(self, max_cost=8, max_vars=6, max_width=64, max_proofs=64,
                 max_lanes=ops.MAX_LANES, max_bits=512):
        self.max_cost = max_cost      # operations of a candidate source
        self.max_vars = max_vars
        self.max_width = max_width    # bits of a scalar or of a lane
        self.max_lanes = max_lanes
        self.max_bits = max_bits      # bits of a value
        self.max_proofs = max_proofs  # SMT checks per record

    def type_error(self, t):
        if ops.elem(t) > self.max_width:
            return 'wider than %d bits' % self.max_width
        if ops.lanes(t) > self.max_lanes:
            return 'more than %d lanes' % self.max_lanes
        if ops.bits(t) > self.max_bits:
            return 'more than %d bits in all lanes' % self.max_bits
        return None


def _node_key(n):
    """The operator key of a node: as corpus.node_key, the predicate, the
    immediate (the constant index of a lane), the mask of a shuffle and
    the result."""
    attr = n.get('pred', n.get('imm'))
    if 'mask' in n:
        attr = ops.mask_attr(n['mask'])
    return ops.make_key(n['op'], attr, n.get('res', 0))


class _Region:
    """The expressions of one record. A node the synthesizer has no model
    for is still an expression (its operator key is unknown to the
    registry, or its type is not a scalar); ``_modeled`` rejects it."""

    def __init__(self, rec):
        self.rec = rec
        self.vw = []          # variable -> width (None: not a scalar)
        self.facts = []       # variable -> (zero, one)
        self.info = []        # variable -> description
        by_id = {}
        for i in rec['inputs']:
            assert i['in'] == len(self.vw)
            w = parse_type(i['type'])
            self.vw.append(w)
            self.facts.append(self._kb(i, w))
            self.info.append({'reg': i['reg'], 'def': i['def']})
            by_id[i['id']] = ('var', i['in'])
        for c in rec['constants']:
            by_id[c['id']] = ('const', parse_type(c['type']),
                              int(c['value'], 16))
        opt = {}
        for n in rec['optimized']:
            if 'in' in n:
                opt[n['id']] = ('var', n['in'])
            elif 'value' in n:
                opt[n['id']] = ('const', parse_type(n['type']),
                                int(n['value'], 16))
            else:
                opt[n['id']] = self._expr(n, opt)
        self.opt = opt
        self.node_facts = {}   # normalized expression -> (zero, one)
        self.node_uses = {}
        self.flags = {}
        # Per value of the region: the selected expression of the value,
        # and the node with the selected expressions of its operands in
        # place of the operands (a *local* step of the rewrite).
        best = {}
        self.steps = []
        for n in rec['original']:
            e = self._expr(n, by_id)
            by_id.setdefault(n['id'], e)
            if 'reg' not in n:
                continue
            w = e[1] if isinstance(e[1], int) else None
            kb = self._kb(n, w)
            if 'zero' in n:
                self.node_facts.setdefault(e, kb)
                self.node_uses.setdefault(e, n.get('uses', 1))
            if n.get('flags'):
                self.flags[e] = n['flags']
            if n.get('best') not in opt:
                continue
            b = opt[n['best']]
            local = self._expr(n, best_env(best, by_id))
            best.setdefault(n['id'], b)
            for x in (b, local):
                if ir.is_op(x) and 'zero' in n:
                    self.node_facts.setdefault(x, kb)
            self.steps.append((n, local, b))
        self.orig = by_id

    @staticmethod
    def _kb(n, w):
        """The facts of an input or of a value: its known bits and, if the
        compiler says so, that it is neither undef nor poison."""
        defined = bool(n.get('not_undef') and n.get('not_poison'))
        if w is None or 'zero' not in n:
            return (0, 0, True) if defined else (0, 0)
        # The known bits of a vector are those of each lane.
        w = ops.elem(w)
        kb = (int(n['zero'], 16), int(n['one'], 16))
        return kb + (True,) if defined else kb

    @staticmethod
    def _expr(n, env):
        key = _node_key(n)
        if 'site' in n:
            # The value depends on the instruction, not only on the
            # operands.
            key += '@%d' % n['site']
        w = parse_type(n.get('type'))
        e = (key, w if w is not None else n.get('type')) + \
            tuple(env[a] for a in n['args'])
        # The operands are normalized already.
        if ops.known(key) and ir.is_commutative(key):
            e = e[:2] + tuple(sorted(e[2:4], key=repr)) + e[4:]
        return e


def best_env(best, by_id):
    """Operand lookup that prefers the selected expression of a value."""
    class Env(dict):
        def __missing__(self, k):
            return best[k] if k in best else by_id[k]
    return Env()


def _normalize(e):
    """Operand order of commutative operations, for comparison."""
    if not ir.is_op(e):
        return e
    args = tuple(_normalize(a) for a in e[2:])
    if ops.known(e[0]) and ir.is_commutative(e[0]):
        args = tuple(sorted(args[:2], key=repr)) + args[2:]
    return e[:2] + args


def _subterms(e, out):
    if ir.is_op(e) and e not in out:
        out.add(e)
        for a in e[2:]:
            _subterms(a, out)
    return out


def _modeled(e, limits):
    """None if every node of ``e`` has a type and an SMT model, else the
    reason."""
    if ir.is_var(e):
        return None
    if not isinstance(e[1], int):
        return 'type %s has no model' % e[1]
    r = limits.type_error(e[1])
    if r:
        return r
    if not ir.is_op(e):
        return None
    if not ops.known(e[0]):
        return 'operator %s has no model' % e[0].split('@')[0]
    info = ops.parse(e[0])[0]
    if info.smt is None:
        return 'operator %s: %s' % (info.name, info.unsupported['smt'])
    for a in e[2:]:
        r = _modeled(a, limits)
        if r:
            return r
    return None


class Candidate:
    def __init__(self, inst, tgt, rules, refinement, group=None):
        self.inst = inst
        self.tgt = tgt
        self.rules = rules            # e-graph rules that fired
        self.refinement = refinement  # the e-graph used a one-way rewrite
        # Candidates with the same group are recipes for the same computed
        # constant, best first: the first that is proved is the rule.
        self.group = group
        # 'lhs' (proved without a fact of the inputs) or 'guard' (the
        # proof needs known bits of the inputs).
        self.precondition_source = None
        # The rules of the records that needed context facts (version 3),
        # and the records of the candidate that have such rules.
        self.context_facts = set()
        self.records = set()
        # The candidate of a root that reads another root, both results of
        # one instruction with several results: a seed of a rule with
        # several outputs (region.py).
        self.joint = False

    def provenance(self):
        """The provenance of a rule made from the candidate."""
        return {'discovery': 'egraph', 'egraph_rules': self.rules,
                'egraph_refinement': self.refinement,
                'egraph_context_facts': sorted(self.context_facts),
                'precondition_source': self.precondition_source}

    def key(self):
        return (self.inst.expr, self.tgt, self.inst.vw, self.inst.facts,
                self.inst.const_vars)


# The most recipes that are tried for one computed constant.
MAX_RECIPES = 3


def recipes(value, w, consts, vw, prefer=(), widths=()):
    """Expressions that have the value ``value`` at width ``w``: the
    candidates for a constant of the replacement that the source does not
    have. A recipe is the mask of the low bits of a narrower type of the
    source (``widths``), or an expression over the constant variables
    ``consts`` (variable -> value). Smallest first, then the operators of
    ``prefer``, in a deterministic order."""
    for wm in sorted(widths):
        if wm < w and value == ir.mask(wm):
            return [('G_ZEXT', w, ('lit', wm, '-1'))]
    atoms = []
    for v in sorted(consts):
        x = ('var', v)
        xw = vw[v]
        atoms.append(x)
        atoms.append(('G_XOR', xw, x, ('lit', xw, '-1')))
        atoms.append(('G_SUB', xw, ('lit', xw, '0'), x))
        atoms.append(('G_SHL', w, ('lit', w, '1'), x))
    env = {v: c for v, c in consts.items()}

    def val(e):
        if not ir.well_typed(e, vw) or ir.width(e, vw) != w:
            return None
        r = ir.evaluate(e, vw, env)
        return None if r is ir.UB else r

    found = [a for a in atoms if ir.is_op(a) and val(a) == value]
    for op in ir.RECIPE_OPS:
        for i, a in enumerate(atoms):
            for j, b in enumerate(atoms):
                if ir.is_commutative(op) and j < i:
                    continue
                e = (op, w, a, b)
                if val(e) == value:
                    found.append(e)
            for k in ('1', '-1'):
                e = (op, w, a, ('lit', w, k))
                if val(e) == value:
                    found.append(e)

    def rank(e):
        return (ir.cost(e), -len(ir.variables(e)),
                0 if e[0] in prefer else 1,
                0 if e[0] in ir.BASE_RECIPE_OPS + ('G_ZEXT',) else 1,
                ir.to_sexpr(e))
    out = []
    for e in sorted(found, key=rank):
        if e not in out:
            out.append(e)
    return out[:MAX_RECIPES]


class Importer:
    """Reads export records and collects the distinct candidates."""

    def __init__(self, backend, limits=None):
        self.backend = backend
        self.limits = limits or Limits()
        self.by_key = {}
        self.stats = {'records': 0, 'roots': 0, 'roots_unchanged': 0,
                      'roots_effect': 0, 'steps': 0, 'steps_not_cheaper': 0,
                      'pairs': 0, 'candidates': 0, 'distinct': 0,
                      'computed_constants': 0,
                      'smt_checks': 0, 'rejected': {},
                      'versions': {}, 'features': {}, 'views': {},
                      'precondition': {
                          s: {'candidates': 0, 'distinct': 0, 'rules': 0,
                              'known': 0, 'rejected': {}}
                          for s in ('lhs', 'guard')},
                      'context_facts': {'records': 0, 'rules': {}},
                      'multi_root': {'records': 0, 'groups': 0,
                                     'region_seeds': 0, 'parts': 0}}
        self.rejected_examples = {}
        self._proved = {}
        self._free = {}
        # Per record with context facts (its index): the record, the
        # rejections counted while it was read, its candidates and what
        # became of them (synthesize).
        self._records = {}
        self._rec = None

    # -- bookkeeping --

    def _reject(self, reason, rec, src=None, tgt=None, kind='step'):
        """Counts a rewrite that gives no candidate. ``kind`` is 'step' (a
        local step: an opportunity that is lost), 'root' (the complete
        rewrite of a root; its local steps are candidates of their own) or
        'multi-root' (roots of one instruction with several results)."""
        r = self.stats['rejected'].setdefault(kind, {})
        r[reason] = r.get(reason, 0) + 1
        if self._rec is not None:
            self._rec['rejected'] += 1
        ex = self.rejected_examples.setdefault(kind + ': ' + reason, [])
        if len(ex) < 3:
            ex.append({'fn': rec['fn'], 'bb': rec['bb'],
                       'source': _show(src), 'replacement': _show(tgt)})

    # -- proofs --

    def _instance(self, reg, s, t):
        """An Instance for the pair with its variables renumbered, and the
        renumbered replacement."""
        order = ir.variables(s)
        m = {o: n for n, o in enumerate(order)}
        inst = corpus.Instance(
            ir.rename(s, m), [reg.vw[o] for o in order],
            [reg.facts[o] for o in order], [None] * len(order), [], [],
            [])
        return inst, ir.rename(t, m)

    def _provable(self, reg, s, t):
        """True if ``t`` refines ``s`` under the facts of the region."""
        if not ir.is_op(s) or ir.width(s, reg.vw) != ir.width(t, reg.vw):
            return False
        if not set(ir.variables(t)) <= set(ir.variables(s)):
            return False
        if _modeled(s, self.limits) or _modeled(t, self.limits):
            return False
        if any(reg.vw[v] is None for v in ir.variables(s)):
            return False
        if ir.repeated_nondet(s):
            return False
        inst, tgt = self._instance(reg, s, t)
        if not ir.well_typed(inst.expr, inst.vw) or \
                not ir.well_typed(tgt, inst.vw):
            return False
        key = (inst.expr, tgt, inst.vw, inst.vk, inst.facts)
        if key not in self._proved:
            if self._budget <= 0:
                return False
            self._budget -= 1
            self.stats['smt_checks'] += 1
            r = discover.prove_concrete(inst, tgt, self.backend)
            self._proved[key] = r.status == 'unsat'
        return self._proved[key]

    # -- reduction --

    def _abstract(self, reg, s, t):
        """Step 1: the maximal common subterms become variables."""
        common = _subterms(s, set()) & _subterms(t, set())
        if not common:
            return s, t
        sub = {}
        # Largest first, so that a variable stands for a maximal subterm.
        for e in sorted(common, key=lambda e: (-_size(e), repr(e))):
            if any(e in _subterms(big, set()) and e != big for big in sub):
                continue
            sub[e] = ('var', len(reg.vw))
            w = e[1] if isinstance(e[1], int) else None
            reg.vw.append(w)
            reg.facts.append(reg.node_facts.get(e, (0, 0)))
            reg.info.append({'expr': e})
        return ir.substitute(s, sub), ir.substitute(t, sub)

    def _split(self, reg, s, t, memo):
        """Step 2. Returns the proved pairs that explain s -> t, or None."""
        if s == t:
            return []
        k = (s, t)
        if k in memo:
            return memo[k]
        out = None
        if ir.is_op(s) and ir.is_op(t) and s[:2] == t[:2] and \
                len(s) == len(t):
            orders = [t[2:]]
            if ops.known(s[0]) and ir.is_commutative(s[0]):
                orders.append((t[3], t[2]) + t[4:])
            for targs in orders:
                subs = []
                for a, b in zip(s[2:], targs):
                    r = self._split(reg, a, b, memo)
                    if r is None:
                        subs = None
                        break
                    subs += r
                if subs is not None:
                    out = subs
                    break
        if out is None and self._provable(reg, s, t):
            out = [(s, t)]
        memo[k] = out
        return out

    def _generalize(self, reg, s, t):
        """Step 3: subterms of the source that can be any value."""
        changed = True
        while changed:
            changed = False
            for e in sorted(_subterms(s, set()) - {s},
                            key=lambda e: (-_size(e), repr(e))):
                if not isinstance(e[1], int):
                    continue
                v = ('var', len(reg.vw))
                reg.vw.append(e[1])
                reg.facts.append(reg.node_facts.get(e, (0, 0)))
                reg.info.append({'expr': e})
                s2 = ir.substitute(s, {e: v})
                t2 = ir.substitute(t, {e: v})
                if self._provable(reg, s2, t2):
                    s, t = s2, t2
                    changed = True
                    break
                reg.vw.pop()
                reg.facts.pop()
                reg.info.pop()
        return s, t

    # -- one record --

    def add_record(self, rec, source=''):
        if rec.get('version') not in FORMAT_VERSIONS:
            raise ValueError('%s: export format version %r, expected one of '
                             '%s' % (source, rec.get('version'),
                                     FORMAT_VERSIONS))
        self.stats['records'] += 1
        v = self.stats['versions']
        v[rec['version']] = v.get(rec['version'], 0) + 1
        self._read_v3(rec)
        reg = _Region(rec)
        self._budget = self.limits.max_proofs
        rules = sorted(rec.get('rules', {}))
        ctx = rec.get('context_facts') or {}
        self._rec = None
        if ctx:
            self._rec = {'fn': rec['fn'], 'bb': rec['bb'],
                         'context_facts': sorted(ctx), 'rejected': 0,
                         'candidates': 0, 'outcomes': set()}
            self._records[self.stats['records']] = self._rec
        joint, parts = self._multi_root(reg, rec)
        # The local steps: one per value whose selected expression is not
        # the node itself.
        for n, s, t in reg.steps:
            if s == t:
                continue
            self.stats['steps'] += 1
            self._add_rewrite(reg, rec, n['reg'], s, t, rules, source,
                              local=True)
        # The complete rewrite of each root, from the original
        # instructions. It is a rule of its own if it is small.
        for root in rec['roots']:
            self.stats['roots'] += 1
            if 'reg' not in root:
                self.stats['roots_effect'] += 1
                continue
            s = reg.orig[root['original']]
            t = reg.opt.get(root['optimized'])
            if t is None or s == t:
                self.stats['roots_unchanged'] += 1
                continue
            if root['reg'] in parts:
                # A result of an instruction that the rewrite of several
                # roots computes once; alone it is not the rewrite.
                self.stats['multi_root']['parts'] += 1
                continue
            self._joint = root['reg'] in joint
            self._add_rewrite(reg, rec, root['reg'], s, t, rules, source,
                              local=False)
            self._joint = False
        self._rec = None

    def _read_v3(self, rec):
        """The statistics of the fields of version 3: the features that
        were on, the views, and the rules that needed context facts."""
        for f in rec.get('features', ()):
            self.stats['features'][f] = self.stats['features'].get(f, 0) + 1
        for name, vs in (rec.get('views') or {}).items():
            out = self.stats['views'].setdefault(name, {})
            for k, n in vs.items():
                out[k] = out.get(k, 0) + n
        ctx = rec.get('context_facts') or {}
        if ctx:
            c = self.stats['context_facts']
            c['records'] += 1
            for name, n in ctx.items():
                c['rules'][name] = c['rules'].get(name, 0) + n

    def _multi_root(self, reg, rec):
        """The roots of the record that the rewrite changes into results
        of one instruction with several results. Returns (the registers of
        the roots that read another root of their group: seeds of a rule
        with several outputs, the registers of the other roots of a
        group)."""
        groups = {}
        for root in rec['roots']:
            t = reg.opt.get(root.get('optimized'))
            if 'reg' not in root or t is None or not ir.is_op(t) or \
                    '@' in t[0] or not ops.known(t[0]) or \
                    reg.orig[root['original']] == t:
                # Not a rewrite: a root that the region computes as it is
                # (the instruction with several results is in the source).
                continue
            info, attr, _ = ops.parse(t[0])
            if (info.results or 1) < 2:
                continue
            groups.setdefault((info.name, attr) + t[2:], []).append(root)
        joint, parts = set(), set()
        groups = [g for g in groups.values() if len(g) > 1]
        if groups:
            self.stats['multi_root']['records'] += 1
        for g in groups:
            self.stats['multi_root']['groups'] += 1
            srcs = {r['reg']: reg.orig[r['original']] for r in g}
            # A root whose source has every other root of the group as a
            # value below it.
            prim = [r for r in g if all(
                o == r['reg'] or srcs[o] in _subterms(srcs[r['reg']], set())
                for o in srcs)]
            if prim:
                joint.add(prim[0]['reg'])
                parts |= set(srcs) - {prim[0]['reg']}
                self.stats['multi_root']['region_seeds'] += 1
            else:
                parts |= set(srcs)
                self._reject('roots that do not read each other are '
                             'results of one instruction with several '
                             'results: a rule for several roots, which '
                             'the import does not make (synth --siblings '
                             'searches them in the corpus)', rec,
                             srcs[g[0]['reg']], reg.opt[g[0]['optimized']],
                             'multi-root')
        return joint, parts

    def _add_rewrite(self, reg, rec, root_reg, s, t, rules, source, local):
        kind = 'step' if local else 'root'
        s, t = self._abstract(reg, s, t)
        if local and ir.is_op(s) and ops.known(s[0]) and \
                _dag_cost(t) >= _dag_cost(s):
            # The extractor selected another form of equal cost.
            self.stats['steps_not_cheaper'] += 1
            return
        pairs = self._split(reg, s, t, {})
        if pairs is None:
            why = _modeled(s, self.limits) or _modeled(t, self.limits)
            if not why and not set(ir.variables(t)) <= \
                    set(ir.variables(s)):
                why = 'the replacement has an input the source has not'
            if not why and self._budget <= 0:
                why = 'proof budget of the record used'
            self._reject(why or 'not proved under the known bits', rec,
                         s, t, kind)
            return
        for s, t in pairs:
            self.stats['pairs'] += 1
            s, t = self._generalize(reg, s, t)
            self._add_pair(reg, rec, root_reg, s, t, rules, source, kind)

    def _add_pair(self, reg, rec, root_reg, s, t, rules, source, kind):
        lim = self.limits
        if ir.cost(s) > lim.max_cost:
            return self._reject('source larger than %d operations' %
                                lim.max_cost, rec, s, t, kind)
        # Constants of the source become inputs with exact known bits, as
        # in the enumerative corpus; a constant of the replacement that is
        # a literal or a constant of the source refers to it.
        consts = {}
        for c in ir.constants(s):
            consts[c] = len(reg.vw)
            reg.vw.append(c[1])
            reg.facts.append((~c[2] & ir.mask(c[1]), c[2]))
            reg.info.append({'const': c[2]})
        tsub = {}
        computed = []
        for c in ir.constants(t):
            if c in consts:
                # The register of the constant: the rule then holds for
                # every value with these known bits.
                tsub[c] = ('var', consts[c])
                continue
            for k in ir.LITERALS:
                if ir.lit_value(c[1], k) == c[2]:
                    tsub[c] = ('lit', c[1], k)
                    break
            else:
                computed.append(c)
        const_of = {v: c[2] for c, v in consts.items()}
        s = ir.substitute(s, {c: ('var', v) for c, v in consts.items()})
        if len(computed) > 1:
            return self._reject('the replacement has more than one '
                                'computed constant', rec, s, t, kind)
        # A constant that the source does not have is computed from the
        # constants of the source. Each recipe is a candidate.
        alts = [tsub]
        if computed:
            c = computed[0]
            rs = recipes(c[2], c[1], const_of, reg.vw,
                         {n[0] for n in ir.nodes(s)},
                         {n[1] for n in ir.nodes(s)} |
                         {reg.vw[v] for v in ir.variables(s)})
            if not rs:
                return self._reject('a constant of the replacement has no '
                                    'recipe from the constants of the '
                                    'source', rec, s, t, kind)
            alts = [dict(list(tsub.items()) + [(c, r)]) for r in rs]
            self.stats['computed_constants'] += 1
        group = (rec['fn'], rec['bb'], root_reg, ir.to_sexpr(s),
                 ir.to_sexpr(t)) if computed else None
        for sub in alts:
            self._add_candidate(reg, rec, root_reg, s,
                                ir.substitute(t, sub), const_of, rules,
                                source, kind, group)

    def _add_candidate(self, reg, rec, root_reg, s, t, const_of, rules,
                       source, kind, group):
        lim = self.limits
        order = ir.variables(s)
        if len(order) > lim.max_vars:
            return self._reject('more than %d inputs' % lim.max_vars, rec,
                                s, t, kind)
        if ir.repeated_nondet(s):
            return self._reject('the source has one term with a value of '
                                'its own twice (they are two '
                                'instructions)', rec, s, t, kind)
        cvars = sorted({v for c in ir.computed_constants(t, set(const_of))
                        for v in ir.variables(c)})
        if not ir.is_linear_in(t, cvars):
            return self._reject('the replacement uses an input twice '
                                '(not sound for an undef input)', rec, s, t,
                                kind)
        m = {o: n for n, o in enumerate(order)}
        expr = ir.rename(s, m)
        tgt = ir.rename(t, m)
        sub_facts = {}
        uses = []
        back = {('var', m[o]): reg.info[o].get('expr') for o in order}
        for n in ir.interior_nodes(expr):
            orig = ir.substitute(n, {v: e for v, e in back.items()
                                     if e is not None})
            orig = _normalize(_restore_consts(orig, order, const_of, reg))
            uses.append(reg.node_uses.get(orig, 1))
            if orig in reg.node_facts:
                sub_facts[n] = reg.node_facts[orig]
        flags = sorted({f for fl in reg.flags.values() for f in fl})
        inst = corpus.Instance(
            expr, [reg.vw[o] for o in order],
            [reg.facts[o] for o in order],
            [const_of.get(o) for o in order], uses, flags,
            [(source, rec['fn'], root_reg)], sub_facts)
        inst.const_vars = tuple(sorted(m[v] for v in cvars))
        if vector.has_vector(inst.vw, inst.expr, tgt) and not cvars:
            # A pair that computes each lane from the same lanes is a pair
            # of scalars for each lane (corpus.lift_source), with a guard
            # that also accepts the vectors.
            low = corpus.lift_source(inst.expr, inst.vw, inst.sub_facts)
            tlow = vector.lift(tgt, inst.vw, low[3]) if low else None
            if low and tlow:
                lifted = corpus.Instance(
                    low[0], low[1], inst.facts, inst.consts,
                    inst.interior_uses, inst.flags, inst.prov, low[2])
                lifted.lifted, lifted.lift_scalars = True, low[3]
                inst, tgt = lifted, tlow[0]
                self.stats['lifted'] = self.stats.get('lifted', 0) + 1
            else:
                self.stats['vector'] = self.stats.get('vector', 0) + 1
        self.stats['candidates'] += 1
        c = Candidate(inst, tgt, rules, bool(rec.get('refinement')), group)
        old = self.by_key.get(c.key())
        if old is None:
            self.by_key[c.key()] = c
            self.stats['distinct'] += 1
            c.precondition_source = self._precondition_source(inst, tgt)
            self.stats['precondition'][c.precondition_source][
                'distinct'] += 1
        else:
            old.inst.prov.extend(inst.prov)
            old.rules = sorted(set(old.rules) | set(rules))
            c = old
        c.context_facts |= set(rec.get('context_facts') or ())
        if self._rec is not None:
            c.records.add(self.stats['records'])
            self._rec['candidates'] += 1
        if getattr(self, '_joint', False) and kind == 'root':
            c.joint = True

    def _precondition_source(self, inst, tgt):
        """'lhs' if ``tgt`` refines the source of ``inst`` with no fact of
        the inputs (each value, poison and undef included; the constant
        inputs of computed constants for every value), else 'guard'. An
        answer that is not a proof is 'guard'."""
        free = copy.copy(inst)
        free.facts = tuple((0, 0) for _ in inst.vw)
        key = (inst.expr, tgt, inst.vw, inst.vk, inst.const_vars)
        if key not in self._free:
            self.stats['smt_checks'] += 1
            r = discover.prove_concrete(free, tgt, self.backend)
            self._free[key] = 'lhs' if r.status == 'unsat' else 'guard'
        return self._free[key]

    def synthesize(self, c, sy, provenance=None):
        """``sy.add`` of the candidate ``c`` with its provenance, and the
        record of the result: per precondition source the rules and the
        rejections by reason (a candidate whose facts have no expression
        in the precondition grammar, or that the solver does not decide).
        Returns the rule id or None."""
        prov = c.provenance()
        prov.update(provenance or {})
        before = dict(sy.stats)
        rid = sy.add(c.inst, c.tgt, provenance=prov)
        p = self.stats['precondition'][c.precondition_source]
        p['candidates'] += 1
        # A rule of the catalog that covers the candidate is its rule.
        outcome = 'guarded' if c.precondition_source == 'guard' else 'lhs'
        if rid:
            p['rules'] += 1
            guarded = any(d['_pred'] for d in sy.rules[rid]['disjuncts'])
            if c.precondition_source == 'guard' and not guarded:
                p['guard_without_guarded_rule'] = p.get(
                    'guard_without_guarded_rule', 0) + 1
        else:
            why = _why_not_added(c, sy, before)
            if why == 'known':
                p['known'] += 1
            else:
                p['rejected'][why] = p['rejected'].get(why, 0) + 1
                outcome = 'rejected'
        for r in c.records:
            self._records[r]['outcomes'].add(outcome)
        return rid

    def cross_check(self):
        """Puts each record with context facts in one bucket: 'guarded' (a
        candidate of it is a rule with a guard, new or of the catalog),
        'rejected' (a rejection was counted for it: while it was read, or
        of a candidate in synthesize), 'proved_without_facts' (each
        candidate of it was proved with no fact of its inputs: the rewrite
        that needed the facts did not give a candidate),
        'not_synthesized' (candidates that synthesize did not see, e.g. at
        a deadline) or 'no_candidate'. Returns the counts, also in
        stats['context_facts']['outcome']."""
        out = dict.fromkeys(('guarded', 'rejected', 'proved_without_facts',
                             'not_synthesized', 'no_candidate'), 0)
        examples = {}
        for i, r in sorted(self._records.items()):
            o = r['outcomes']
            if 'guarded' in o:
                b = 'guarded'
            elif 'rejected' in o or r['rejected']:
                b = 'rejected'
            elif 'lhs' in o:
                b = 'proved_without_facts'
            elif r['candidates']:
                b = 'not_synthesized'
            else:
                b = 'no_candidate'
            out[b] += 1
            if b not in ('guarded', 'rejected'):
                ex = examples.setdefault(b, [])
                if len(ex) < 3:
                    ex.append({'fn': r['fn'], 'bb': r['bb'],
                               'context_facts': r['context_facts']})
        self.stats['context_facts']['outcome'] = out
        if examples:
            self.stats['context_facts']['examples'] = examples
        return out

    def add_file(self, path):
        with open(path) as f:
            for line in f:
                line = line.strip()
                if line:
                    self.add_record(json.loads(line), path)

    def candidates(self):
        """The distinct candidates, most frequent and most valuable
        first, in a deterministic order."""
        order = {}
        for i, c in enumerate(self.by_key.values()):
            order[id(c)] = i
        return sorted(self.by_key.values(), key=lambda c: (
            -len(c.inst.prov) * (ir.cost(c.inst.expr) -
                                 ir.rule_cost(c.tgt, c.inst.const_vars)),
            ir.to_sexpr(c.inst.expr),
            # The recipes of one constant stay in their order.
            order[id(c)] if c.group else 0,
            ir.to_sexpr(c.tgt), c.inst.vw, c.inst.facts))


def _why_not_added(c, sy, before):
    """Why ``sy.add`` gave no rule for the candidate ``c``: the reason of
    the rejected class (no precondition in the grammar, solver unknown),
    'known' (a rule of the catalog covers it), or the counter of the
    synthesizer that the call increased."""
    grew = sorted(k for k, v in sy.stats.items()
                  if isinstance(v, int) and v > before.get(k, 0) and
                  k not in ('discoveries',))
    if 'known' in grew:
        return 'known'
    try:
        src, tgt, vw, facts, perm = synth.canonicalize(
            c.inst.expr, c.tgt, c.inst.vw, c.inst.facts)
        cv = tuple(sorted(new for new, old in enumerate(perm)
                          if old in c.inst.const_vars))
        rej = sy.rejected.get(synth.class_key(src, tgt, vw, cv))
    except (AssertionError, KeyError, ValueError, TypeError):
        rej = None
    if rej is not None:
        return rej['reason']
    if 'uncovered' in grew:
        return 'no_precondition_in_grammar'
    return grew[0] if grew else 'not_added'


def _restore_consts(e, order, const_of, reg):
    """The expression with the variables that stand for constants written
    as constants again (to look an interior node up in the region)."""
    if ir.is_var(e):
        o = order[e[1]] if e[1] < len(order) else None
        if o in const_of:
            return ('const', reg.vw[o], const_of[o])
        return ('var', o) if o is not None else e
    if not ir.is_op(e):
        return e
    return e[:2] + tuple(_restore_consts(a, order, const_of, reg)
                         for a in e[2:])


def _size(e):
    """The number of operations of the tree ``e``."""
    return 1 + sum(_size(a) for a in e[2:]) if ir.is_op(e) else 0


def _dag_cost(e):
    """ir.dag_cost for an expression that can have operators without a
    model (they cost 1)."""
    seen = set()

    def walk(x):
        if not ir.is_op(x) or x in seen:
            return 0
        seen.add(x)
        c = ops.cost(x[0]) if ops.known(x[0]) else 1
        return c + sum(walk(a) for a in x[2:])
    return walk(e)


def _show(e):
    if e is None:
        return None
    if ir.is_var(e):
        return 'x%d' % e[1]
    if not ir.is_op(e):
        return '%#x' % ir.leaf_value(e)
    return '(%s %s)' % (e[0], ' '.join(_show(a) for a in e[2:]))


def export_files(paths):
    """The .jsonl files of the given files and directories, sorted."""
    out = []
    for p in paths:
        if os.path.isdir(p):
            out += [os.path.join(p, f) for f in sorted(os.listdir(p))
                    if f.endswith('.jsonl')]
        else:
            out.append(p)
    return out
