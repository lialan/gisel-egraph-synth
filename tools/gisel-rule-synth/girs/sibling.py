"""Regions with several roots.

region.py extends a rule to the values *below* its root. This module
searches rules for roots that are not in one tree: the root of an
expression tree (the primary root, which the combine rule matches) and up
to MAX_SIBLINGS other instructions of the same basic block that read
values of the region (the siblings). Example: ``x - y`` and
``icmp ult x, y`` are two roots with the inputs x and y, and one G_USUBO
computes both.

The values of a region have an identity:

  - an input (a variable): of the tree, or one that only a sibling reads
    (a constant operand of the sibling);
  - a node of the tree: one matched instruction. A node that occurs twice
    in the tree is two instructions with one model term, so it is not a
    value that a sibling can read;
  - the result of an earlier sibling.

Each operand of a sibling is one of these values (operand_refs), and at
least one is a value that the tree or an earlier sibling has. The
generated matcher finds the sibling from that value and compares the
other operands by register, so a value that two roots read is one
instruction. A G_FREEZE instruction is one term of the proof: a region
with two G_FREEZE instructions of one value is rejected (freeze_ok).

The corpus has one tree per root. The groups come from the registers of
the records (load_pairs): the records of one basic block.

The search has no rewrite of its own. The values that a replacement can
have for no added cost are *leaves* of the term bank of the single-root
search:

  - a sibling stays: the results of its instruction are leaves;
  - a sibling is replaced by a result of a new instruction with several
    results: the other results are leaves, and the cost of the
    instruction counts once;
  - a value below the root that has another user stays, so it is a leaf.

A term of the bank that has the samples of the primary root and that reads
a leaf is a candidate. The leaf is then replaced by its definition, so
that the candidate is an expression over the inputs, and the proof is the
joint proof of region.py: one query with the values of all roots. A
sibling that stays and that a new instruction computes also (another
result of that instruction) is then replaced by that result.

Limits (each is a rejection, not an assumption):
  - one basic block; a sibling is one instruction;
  - a sibling that is replaced has one result;
  - a sibling that stays is read by a replacement, and it does not read a
    sibling that is replaced;
  - no computed constants;
  - the replacements read each input once in all (region.joint_reads).
"""

import hashlib
import itertools
import json

from . import corpus
from . import discover
from . import ir
from . import ops
from . import precond
from . import region
from . import smt
from . import synth

import numpy as np

U64 = np.uint64

# Replacements of one group that are proved, cheapest first.
MAX_TRIES = 4
# Leaves that one bank has next to the inputs.
MAX_LEAVES = 3
# Siblings of one rule.
MAX_SIBLINGS = 2
# Siblings of one tree that are put in groups.
MAX_PER_ROOT = 6


class Pair:
    """A primary instance and its siblings: expressions over the variables
    of the instance, of which each is one instruction over values of the
    region."""

    def __init__(self, inst, sibs, prov, base_key=None):
        self.inst = inst
        # One expression, or a sequence of expressions.
        self.sibs = tuple(sibs) if sibs and isinstance(sibs[0], tuple) \
            else (sibs,)
        self.prov = prov           # [(file, fn, root, sibling roots)]
        # The key of the instance of the tree alone: the rules that the
        # single-root search found for it.
        self.base_key = base_key if base_key is not None else inst.key()

    @property
    def sib(self):
        return self.sibs[0]

    def key(self):
        # The users of the values below the root are part of the key: a
        # value with another user stays, so the group has another cost.
        return (self.inst.key(), self.inst.interior_uses, self.sibs)


def operand_refs(a, sibs):
    """The value that each operand of each sibling is: ('var', i),
    ('node', k) (the node k of the tree ``a``: its pre-order index below
    the root plus 1) or ('sib', j) (the result of the sibling j). None if
    an operand is not one value of the region, or if a sibling reads no
    value that the tree or an earlier sibling has."""
    nodes = ir.interior_nodes(a)
    shared = set(ir.variables(a))
    out = []
    for j, b in enumerate(sibs):
        if not ir.is_op(b):
            return None
        refs = []
        for x in b[2:]:
            if ir.is_var(x):
                refs.append(('var', x[1]))
            elif not ir.is_op(x):
                return None
            elif nodes.count(x) == 1:
                refs.append(('node', nodes.index(x) + 1))
            elif x not in nodes and list(sibs[:j]).count(x) == 1:
                refs.append(('sib', list(sibs[:j]).index(x)))
            else:
                return None
        if not any(r[0] != 'var' or r[1] in shared for r in refs):
            return None
        out.append(tuple(refs))
    return out


def freeze_ok(a, sibs):
    """True if each G_FREEZE term of the region is one instruction. The
    proof has one value per term, and two G_FREEZE instructions of one
    poison value can have different values. An operand of a sibling is a
    value of the region (operand_refs), so only a sibling that is a
    G_FREEZE itself is a new instruction."""
    if ir.repeated_freeze(a):
        return False
    # A rule with several roots has no G_PHI: its replacement is built at
    # a position in the block of the roots that the rule finds, and a
    # G_PHI is in another block.
    if ir.phi_nodes(a) or any(ir.phi_nodes(b) for b in sibs):
        return False
    # And no constrained operation: the roots have one position, and each
    # constrained operation has its own position in the environment.
    if any(ir.constrained_nodes(x) for x in [a] + list(sibs)):
        return False
    # And no load after a G_STORE: the value of the load is no operand of
    # its instruction, so the rule cannot find the load from the value.
    if any(ir.has_forwarded_load(x) for x in [a] + list(sibs)):
        return False
    have = set(ir.freeze_terms(a))
    for b in sibs:
        if ir.is_op(b) and ops.parse(b[0])[0].freeze:
            if b in have:
                return False
            have.add(b)
    return True


def _instr(node):
    """The identity of the instruction of a corpus node: the results of
    one instruction with several results are one instruction."""
    return node.get('mi', node['reg'])


def _instrs(node, out):
    if 'op' in node:
        out.add(_instr(node))
        for a in node['args']:
            _instrs(a, out)
    return out


def _single(rec):
    """The record of the root instruction of ``rec`` alone: each operand
    is an input. A sibling is one instruction, and its operands are
    values of the region by their registers."""
    expr = rec['expr']
    if all('in' in x for x in expr['args']):
        return rec
    inputs, args = [], []
    for x in expr['args']:
        if 'in' in x:
            src = rec['inputs'][x['in']]
        else:
            src = {'reg': x['reg'], 'w': x['w'], 'type': x.get('type', ''),
                   'zero': x.get('zero', '0x0'), 'one': x.get('one', '0x0'),
                   'noundef': x.get('noundef', False), 'def': x['op']}
        regs = [i['reg'] for i in inputs]
        if src['reg'] not in regs:
            regs.append(src['reg'])
            inputs.append(src)
        args.append({'in': regs.index(src['reg'])})
    return dict(rec, expr=dict(expr, args=args), inputs=inputs)


def _group(a, bs):
    """The group of the tree ``a`` and the single-instruction records
    ``bs`` (each (instance, root register)), or None. Returns (instance
    over all variables, sibling expressions)."""
    nodes = ir.interior_nodes(a.expr)
    value = {r: ('var', i) for i, r in enumerate(a.regs)}
    if a.node_regs is not None and len(a.node_regs) == len(nodes):
        for n, r in zip(nodes, a.node_regs):
            if nodes.count(n) == 1:
                value.setdefault(r, n)
    vw, facts, consts = list(a.vw), list(a.facts), list(a.consts)
    kinds, regs = list(a.vk), list(a.regs)
    sibs = []
    for b, broot in bs:
        if not all(ir.is_var(x) for x in b.expr[2:]):
            return None
        sub = {}
        for i, r in enumerate(b.regs):
            if r not in value:
                # An input that only this sibling reads: a constant.
                if b.consts[i] is None:
                    return None
                value[r] = ('var', len(vw))
                vw.append(b.vw[i])
                facts.append(b.facts[i])
                consts.append(b.consts[i])
                kinds.append(b.vk[i])
                regs.append(r)
            sub[('var', i)] = value[r]
        e = ir.substitute(b.expr, sub)
        sibs.append(e)
        value.setdefault(broot, e)
    if operand_refs(a.expr, sibs) is None or not freeze_ok(a.expr, sibs):
        return None
    if len(vw) == len(a.vw):
        return a, tuple(sibs)
    inst = corpus.Instance(a.expr, vw, facts, consts, a.interior_uses,
                           a.flags, list(a.prov), a.sub_facts, kinds)
    inst.regs = tuple(regs)
    inst.node_regs = a.node_regs
    if not all(ir.well_typed(e, inst.vw) for e in sibs):
        return None
    return inst, tuple(sibs)


def load_pairs(paths, stats=None, max_siblings=MAX_SIBLINGS):
    """The groups of the corpus files: per file, per basic block, each
    record with the records of one instruction that read its values (one
    sibling, and two siblings up to ``max_siblings``). Returns the
    distinct groups, most occurrences first."""
    stats = {} if stats is None else stats
    stats.update({'records': 0, 'pairs': 0, 'with_two_siblings': 0,
                  'with_a_value_below_the_root': 0,
                  'with_an_input_of_the_sibling': 0})
    by_key = {}
    for path in paths:
        groups = {}
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                if 'bb' not in rec:
                    continue
                inst = corpus.parse_record(rec, path)
                if inst is None:
                    continue
                stats['records'] += 1
                one = inst if not ir.interior_nodes(inst.expr) else \
                    corpus.parse_record(_single(rec), path)
                groups.setdefault((rec['fn'], rec['bb']), []).append(
                    (inst, _instr(rec['expr']), _instrs(rec['expr'], set()),
                     rec['root'], one))
        for g in groups.values():
            # The root instruction of each record, as a sibling.
            singles = [(x[4], x[1], x[3]) for x in g if x[4] is not None]
            for a, aroot, anodes, areg_root, _ in g:
                ain = set(a.regs)
                have = ain | set(a.node_regs or ())
                cands, instrs = [], set()
                for b, broot, breg_root in singles:
                    # Not an instruction of the tree, and not an input
                    # of it. The results of one instruction are one
                    # sibling.
                    if broot in anodes or breg_root in ain or \
                            broot in instrs:
                        continue
                    if any(r in have for r in b.regs):
                        cands.append((b, breg_root))
                        instrs.add(broot)
                    if len(cands) >= MAX_PER_ROOT:
                        break
                sets = [(c,) for c in cands]
                if max_siblings >= 2:
                    # Two siblings have one order: that of their
                    # expressions, and the order of the block for two
                    # equal expressions. The same three roots in another
                    # order in another block are then the same group.
                    sets += [tuple(sorted(c, key=lambda x: ir.to_sexpr(
                        x[0].expr))) for c in itertools.combinations(
                            cands, 2)]
                done = set()
                for bs in sets:
                    grp = _group(a, bs)
                    if grp is None and len(bs) == 2:
                        # The second can read the result of the first
                        # only.
                        bs = bs[::-1]
                        grp = _group(a, bs)
                    if grp is None:
                        continue
                    inst, sibs = grp
                    p = Pair(inst, sibs, [(path, a.prov[0][1], areg_root,
                                           [r for _, r in bs])], a.key())
                    if p.key() in done:
                        continue
                    done.add(p.key())
                    stats['pairs'] += 1
                    stats['with_two_siblings'] += len(sibs) == 2
                    refs = operand_refs(inst.expr, sibs)
                    stats['with_a_value_below_the_root'] += any(
                        r[0] == 'node' for rs in refs for r in rs)
                    stats['with_an_input_of_the_sibling'] += \
                        len(inst.vw) > len(a.vw)
                    old = by_key.get(p.key())
                    if old is None:
                        by_key[p.key()] = p
                    else:
                        old.prov += p.prov
    out = sorted(by_key.values(),
                 key=lambda p: (-len(p.prov), ir.to_sexpr(p.inst.expr),
                                tuple(ir.to_sexpr(b) for b in p.sibs),
                                p.inst.vw, p.inst.facts))
    stats['distinct'] = len(out)
    return out


def kept_nodes(inst, refs=(), rsibs=()):
    """The values below the root of ``inst`` that stay, whatever replaces
    the root: the ones with a user outside the region, and the results of
    an instruction with several results. A sibling that the rule replaces
    (``rsibs``: the replacement of each sibling, None if it stays;
    ``refs``: operand_refs) is not such a user."""
    nodes = ir.interior_nodes(inst.expr)
    uses = getattr(inst, 'interior_uses', ())
    if len(nodes) != len(uses):
        return list(nodes)
    gone = {}
    for rs, r in zip(refs, rsibs):
        if r is not None:
            for x in rs:
                if x[0] == 'node':
                    gone[x[1]] = gone.get(x[1], 0) + 1
    # The corpus has the users of one result: an instruction with several
    # results stays, because another result can have a user.
    return [n for k, (n, u) in enumerate(zip(nodes, uses))
            if u > 1 + gone.get(k + 1, 0) or
            ops.parse(n[0])[0].results != 1]


def results_of(e, vw):
    """The values of the results of the instruction of the node ``e``, in
    the order of the results."""
    info, attr, _ = ops.parse(e[0])
    if info.results == 1 or 'result_kinds' not in info.meta:
        return [e]
    main = ir.width(e[2], vw)
    return [(ops.make_key(info.name, attr, r), main if k == 'main' else 1) +
            e[2:] for r, k in enumerate(info.meta['result_kinds'])]


def _values(e, inst, envs):
    return [None if v is ir.UB else v
            for v in (ir.evaluate(e, inst.vw, env) for env in envs)]


def _agrees(want, e, like, inst, envs):
    got = [ir.evaluate(e, inst.vw, env) for env in envs]
    return all(w is None or (g is not None and g is not ir.UB and
                             ir.same_value(w, g, like))
               for w, g in zip(want, got))


def _atoms(pair):
    """The values that a new instruction can read: the inputs, and the
    values below the root (one occurrence in the tree). The ones that
    stay in every case come first. A value that a replacement reads is
    an instruction of the replacement, so its cost counts."""
    inst = pair.inst
    nodes = ir.interior_nodes(inst.expr)
    kept = kept_nodes(inst)
    return [('var', i) for i in range(len(inst.vw))] + [
        n for n in dict.fromkeys(kept + nodes) if nodes.count(n) == 1]


def providers(pair, limits, ctx, envs, names):
    """Per sibling, the instruction sets whose values a replacement can
    read for no added cost. Each is (leaves, replacement of the sibling
    or None): None means that the sibling stays."""
    inst = pair.inst
    atoms = _atoms(pair)
    types = [ir.type_of(x, inst.vw, inst.vk) for x in atoms]
    out = []
    for sib in pair.sibs:
        opts = [(results_of(sib, inst.vw), None)]
        out.append(opts)
        if ops.parse(sib[0])[0].results != 1:
            continue
        want = _values(sib, inst, envs)
        if all(v is None for v in want):
            continue
        sib_cost = ir.op_cost(sib[0])
        for name in names:
            info = ops.REGISTRY[name]
            if (info.results or 1) < 2 or info.attr is not None or \
                    'result_kinds' not in info.meta or \
                    info.operands is None or info.operands > len(atoms) or \
                    ops.cost(name) > sib_cost + ir.op_cost(inst.expr[0]) - 1:
                continue
            for args in itertools.permutations(range(len(atoms)),
                                               info.operands):
                otypes = [types[a] for a in args]
                res = []
                for r, k in enumerate(info.meta['result_kinds']):
                    w = otypes[0][0] if k == 'main' else 1
                    key = ops.make_key(name, None, r)
                    if not ops.signature_ok(key, (w, 'i'), otypes):
                        res = None
                        break
                    res.append((key, w) + tuple(atoms[a] for a in args))
                if not res:
                    continue
                for r, e in enumerate(res):
                    if e[1] == sib[1] and _agrees(want, e, sib, inst, envs):
                        opts.append(([x for k, x in enumerate(res)
                                      if k != r], e))
    return out


def _instructions(exprs):
    return {region.instruction_key(n) for e in exprs for n in ir.nodes(e)}


def search(pair, limits, ctx, best=None):
    """Replacements of the group, cheapest first: (cost, replacement of
    the primary root, replacements of the siblings). The replacement of
    a sibling that stays is None; with one sibling the third element is
    that replacement, not a tuple. ``best`` is the cost that a result
    must be cheaper than (default: the cost of the roots as they are)."""
    inst, sibs = pair.inst, pair.sibs
    sig = discover.signature(inst)
    refs = operand_refs(inst.expr, sibs)
    if sig is None or refs is None:
        return []
    var_cls, types, _ = sig
    envs = discover.instance_envs(inst, limits, ctx)
    want = _values(inst.expr, inst, envs)
    if all(v is None for v in want):
        return []
    source = region.joint_cost([inst.expr] + list(sibs))
    best = source if best is None else min(best, source)
    names = discover.grammar_stages(inst, limits, types)[-1][1]
    keys = discover.grammar_keys(names, inst)
    rty = ir.type_of(inst.expr, inst.vw, inst.vk)
    nvars = len(inst.vw)
    cols = [np.array([env[i] for env in envs], U64) for i in range(nvars)]
    ok = np.array([v is not None for v in want], bool)
    wantv = discover._canon_nan(np.array([v or 0 for v in want], U64), rty)
    same = set(ir.commuted_variants(inst.expr))
    # A value below the root is a leaf too.
    node_leaves = [x for x in _atoms(pair) if ir.is_op(x)]
    out, seen = [], set()
    for combo in itertools.product(*providers(pair, limits, ctx, envs,
                                              names)):
        rsibs = [r for _, r in combo]
        # A sibling that stays does not read one that is replaced.
        if any(rsibs[j] is None and any(
                r[0] == 'sib' and rsibs[r[1]] is not None for r in refs[j])
               for j in range(len(sibs))):
            continue
        leaves = [l for ls, _ in combo for l in ls] + node_leaves
        leaves = [l for l in dict.fromkeys(leaves)
                  if ir.result_kind(l) in (None, 'i')][:MAX_LEAVES]
        if not leaves:
            continue
        base = [s if r is None else r for s, r in zip(sibs, rsibs)]
        fixed = region.joint_cost(base + kept_nodes(inst, refs, rsibs))
        if fixed >= best:
            continue
        ltypes = [(l[1], 'i') for l in leaves]
        types2 = tuple(sorted(set(types) | set(ltypes)))
        canon2 = discover.canonical_types(types2)
        if canon2 is None:
            continue
        cls2 = {t: i for i, t in enumerate(types2)}
        vcls = tuple(cls2[types[c]] for c in var_cls) + \
            tuple(cls2[t] for t in ltypes)
        lvals = [_values(l, inst, envs) for l in leaves]
        lok = np.array([all(v[k] is not None for v in lvals)
                        for k in range(len(envs))], bool)
        lcols = [np.array([x or 0 for x in v], U64) for v in lvals]
        # The new instructions next to the ones that are there anyway.
        max_cost = min(discover.max_search_cost(inst, limits),
                       best - fixed - 1)
        if max_cost < 0:
            continue
        bank = ctx.bank(vcls, canon2, max_cost, keys)
        V, OK = bank.evaluate(types2, cols + lcols, max_cost, ctx.counters)
        n = V.shape[0]
        rows = np.nonzero(bank.cls_np[:n] == cls2[rty])[0]
        agree = (((discover._canon_nan(V[rows], rty) == wantv) & OK[rows]) |
                 ~ok | ~lok).all(axis=1)
        sub = {('var', nvars + k): l for k, l in enumerate(leaves)}
        for i in rows[agree].tolist():
            t = bank.expr(i, types2)
            if not any(v >= nvars for v in ir.variables(t)):
                continue
            e = ir.substitute(t, sub)
            if e in same or not ir.well_typed(e, inst.vw):
                continue
            rs = list(rsibs)
            # A sibling that stays and that no replacement reads: a
            # result of a new instruction replaces it, or the sibling is
            # not a part of this region.
            used = _instructions([e] + [r for r in rs if r is not None])
            for j, b in enumerate(sibs):
                if rs[j] is not None or region.instruction_key(b) in used:
                    continue
                free = []
                if ops.parse(b[0])[0].results == 1:
                    bw = _values(b, inst, envs)
                    free = [x for x in region.computed_values(
                        [e] + [r for r in rs if r is not None], inst.vw)
                        if x[1] == b[1] and
                        ir.result_kind(x) == ir.result_kind(b) and
                        _agrees(bw, x, b, inst, envs)]
                if not free:
                    rs = None
                    break
                rs[j] = free[0]
            if rs is None or any(
                    rs[j] is None and any(
                        r[0] == 'sib' and rs[r[1]] is not None
                        for r in refs[j]) for j in range(len(sibs))):
                continue
            tgts = [e] + [s if r is None else r for s, r in zip(sibs, rs)]
            cost = region.joint_cost(tgts + kept_nodes(inst, refs, rs))
            k = (e, tuple(rs))
            if cost >= best or k in seen:
                continue
            if any(c > 1 for c in region.joint_reads(tgts).values()):
                continue
            seen.add(k)
            out.append((cost, ir.to_sexpr(e), e, tuple(rs)))
    out.sort(key=lambda x: (x[0], x[1], tuple(
        '' if r is None else ir.to_sexpr(r) for r in x[3])))
    if len(sibs) == 1:
        return [(c, e, rs[0]) for c, _, e, rs in out]
    return [(c, e, rs) for c, _, e, rs in out]


# ------------------------------------------------------------- rules ---

def _widths(exprs, vw):
    ws = set(vw)
    for e in exprs:
        for n in ir.nodes(e):
            ws.add(n[1])
        if not ir.is_var(e):
            ws.add(e[1])
    return sorted(ws)


def _seq(x):
    """The siblings (or their replacements) as a tuple: one of them, or a
    sequence."""
    if x is None or (isinstance(x, tuple) and x and
                     isinstance(x[0], str)):
        return (x,)
    return tuple(x)


def _exprs(a, ra, sibs, rbs):
    return [e for e in (a, ra) + tuple(sibs) + tuple(rbs) if e is not None]


def _normalize(e, a):
    """synth.normalize_commutative, but a part of ``e`` that is a node of
    the tree ``a`` (with its operands in any order) becomes that node: an
    operand of a sibling stays one value of the region."""
    table = {synth.normalize_commutative(n): n
             for n in ir.interior_nodes(a)}

    def norm(x):
        if not ir.is_op(x):
            return x
        hit = table.get(synth.normalize_commutative(x))
        if hit is not None:
            return hit
        args = tuple(norm(y) for y in x[2:])
        if ir.is_commutative(x[0]):
            args = tuple(sorted(args[:2], key=ir.to_sexpr)) + args[2:]
        return x[:2] + args
    return norm(e)


def canonicalize(a, ra, b, rb, vw, facts):
    """The expressions with the variables renamed by first occurrence in
    the primary source and then in the siblings, of which the commutative
    operands have a canonical order. ``b`` and ``rb`` are one sibling and
    its replacement, or sequences of them. Returns (a, ra, b, rb, vw,
    facts, perm) with perm[new] = old."""
    one = not (isinstance(b, (tuple, list)) and b and
               isinstance(b[0], tuple))
    sibs, rbs = _seq(b), _seq(rb)
    n = len(sibs)
    # The siblings have no order of their own: each order in which a
    # sibling reads only the tree and earlier siblings is a form of the
    # same region, and the smallest form is the canonical one.
    orders = [o for o in itertools.permutations(range(n))
              if operand_refs(a, [sibs[i] for i in o]) is not None] or \
        [tuple(range(n))]
    best = None
    for o in orders:
        ps, prs = tuple(sibs[i] for i in o), tuple(rbs[i] for i in o)
        cls = {w: 1000 + i for i, w in enumerate(
            _widths(_exprs(a, ra, ps, prs), vw))}
        for sv in ir.commuted_variants(a):
            order = list(ir.variables(sv))
            for e in ps:
                order += [v for v in ir.variables(e) if v not in order]
            order += [v for v in range(len(vw)) if v not in order]
            m = {old: new for new, old in enumerate(order)}
            a2 = ir.rename(sv, m)
            out = [a2] + [None if e is None else
                          _normalize(ir.rename(e, m), a2)
                          for e in (ra,) + ps + prs]
            # A sibling that stays has no replacement: the key has its
            # place, so that two forms have keys of the same length.
            k = tuple('' if e is None else
                      ir.to_sexpr(ir.map_widths(e, cls)) for e in out)
            if best is None or k < best[0]:
                best = (k, out, order)
    _, out, order = best
    cs, crs = tuple(out[2:2 + n]), tuple(out[2 + n:])
    return (out[0], out[1], cs[0] if one else cs, crs[0] if one else crs,
            tuple(vw[o] for o in order), tuple(facts[o] for o in order),
            tuple(order))


def class_key(a, ra, b, rb, vw):
    sibs, rbs = _seq(b), _seq(rb)
    cls = {w: 1000 + i
           for i, w in enumerate(_widths(_exprs(a, ra, sibs, rbs), vw))}
    return ('sibling',) + tuple(
        None if e is None else ir.to_sexpr(ir.map_widths(e, cls))
        for e in (a, ra) + sibs + rbs) + (tuple(cls[w] for w in vw),)


def pairs_of(a, ra, b, rb):
    """(source value, replacement) of the roots. A sibling that stays is
    its own replacement: its instruction is one of the instructions of
    the replacements."""
    return [(a, ra)] + [(s, s if r is None else r)
                        for s, r in zip(_seq(b), _seq(rb))]


def schedules(a, ra, b, rb, vw, limits, first=None):
    """The width schedules (pairs, variable widths, width map) of a rule
    with siblings; the map ``first`` (default: the identity) comes
    first."""
    ps = pairs_of(a, ra, b, rb)
    ws = _widths([e for p in ps for e in p], vw)
    first = first or {w: w for w in ws}
    head = [first[w] for w in ws]
    pool = sorted(set(synth.WIDTHS) | set(ws) | set(head))
    out = []
    for combo in [tuple(head)] + list(itertools.combinations(pool, len(ws))):
        if out and list(combo) == head:
            continue
        wmap = dict(zip(ws, combo))
        mapped = [(ir.map_widths(s, wmap), ir.map_widths(t, wmap))
                  for s, t in ps]
        v = tuple(wmap[w] for w in vw)
        if all(ir.well_typed(e, v) for p in mapped for e in p):
            out.append((mapped, v, wmap))
        if len(out) >= limits.max_schedules:
            break
    return out


def rule_siblings(rule):
    """(siblings, their replacements) of a rule with siblings; the
    replacement of a sibling that stays is None."""
    ss = rule['region']['siblings']
    return (tuple(ir.from_json(s['source_json']) for s in ss),
            tuple(None if s['stays'] else ir.from_json(s['replacement_json'])
                  for s in ss))


def rule_exprs(rule):
    """(primary source, its replacement, sibling, its replacement or
    None) of a rule with one sibling. With more siblings the last two are
    tuples."""
    sibs, rbs = rule_siblings(rule)
    one = len(sibs) == 1
    return (ir.from_json(rule['source_json']),
            ir.from_json(rule['replacement_json']),
            sibs[0] if one else sibs, rbs[0] if one else rbs)


def rule_schedules(rule, maps):
    """The schedules of a stored rule with siblings for the given width
    maps, or None for a map at which an expression is not well typed."""
    return region.schedules(rule, maps)


def structural(rule):
    """True if a rule with siblings has the form that the proof needs
    (region.structural), and if each sibling is one instruction over
    values of the region, as the rule says."""
    ss = rule['region'].get('siblings')
    if not ss or not region.structural(rule):
        return False
    a = ir.from_json(rule['source_json'])
    sibs, rbs = rule_siblings(rule)
    refs = operand_refs(a, sibs)
    if refs is None or not freeze_ok(a, sibs):
        return False
    for j, (s, b, rb) in enumerate(zip(ss, sibs, rbs)):
        if 'operands' in s and \
                [_ref_json(x) for x in refs[j]] != s['operands']:
            return False
        # A sibling that is replaced has one result, and one that stays
        # does not read one that is replaced.
        if rb is not None and ops.parse(b[0])[0].results != 1:
            return False
        if rb is None and any(x[0] == 'sib' and rbs[x[1]] is not None
                              for x in refs[j]):
            return False
    # The variables that the tree does not have.
    return rule['region'].get('sibling_vars', []) == sorted(
        set(range(len(rule['vw']))) - set(ir.variables(a)))


def _verify(sched, dnf, backend, const_vars=()):
    return region.verify(sched, dnf, backend)


def _text(ra, b, rb):
    return '; '.join([ir.to_sexpr(ra)] + [
        '%s stays' % ir.to_sexpr(s) if r is None else
        '%s = %s' % (ir.to_sexpr(s), ir.to_sexpr(r))
        for s, r in zip(_seq(b), _seq(rb))])


def _ref_json(r):
    return {'var': r[1]} if r[0] == 'var' else \
        {'node': r[1]} if r[0] == 'node' else {'sibling': r[1]}


def dead_nodes(a, ra, b, rb, uses):
    """The values below the root (1-based, pre-order) that the rule needs
    to remove: without that, it has more new instructions than it
    removes. ``uses`` has the number of users of each value below the
    root in the instance of the rule. A value that a replacement reads
    stays, and so does one with a user outside the region."""
    sibs, rbs = _seq(b), _seq(rb)
    nodes = ir.interior_nodes(a)
    tgts = [ra] + [s if r is None else r for s, r in zip(sibs, rbs)]
    have = {n for t in tgts for n in ir.nodes(t)}
    # The instructions that are there: the siblings that stay, and the
    # values below the root that a replacement reads.
    there = [s for s, r in zip(sibs, rbs) if r is None] + \
        [n for n in nodes if nodes.count(n) == 1 and n in have]
    new = region.joint_cost(tgts) - region.joint_cost(there)
    # A sibling is one instruction: its operands are other values.
    sure = ir.op_cost(a[0]) + sum(ir.op_cost(s[0])
                                  for s, r in zip(sibs, rbs)
                                  if r is not None)
    # The generic cost does not say what the target makes of the new
    # instructions: a rule with as many new instructions as it removes is
    # a candidate, and the selection measures it.
    if new <= sure:
        return []
    gone = {}
    for rs, r in zip(operand_refs(a, sibs), rbs):
        if r is not None:
            for x in rs:
                if x[0] == 'node':
                    gone[x[1]] = gone.get(x[1], 0) + 1
    return [k + 1 for k, (n, u) in enumerate(zip(nodes, uses))
            if u <= 1 + gone.get(k + 1, 0) and n not in there and
            ops.parse(n[0])[0].results == 1]


def _new_rule(sy, a, ra, b, rb, vw, st, pool, uses=None):
    sibs, rbs = _seq(b), _seq(rb)
    tgts = [ra] + [s if r is None else r for s, r in zip(sibs, rbs)]
    nodes = ir.interior_nodes(a)
    dead = dead_nodes(a, ra, sibs, rbs,
                      uses if uses is not None else [1] * len(nodes))
    refs = operand_refs(a, sibs)
    h = hashlib.sha256(repr(class_key(a, ra, b, rb, vw) + (
        tuple(vw),)).encode()).hexdigest()[:8]
    return {
        'id': 'synth_sibling_' + h,
        'source': '; '.join(ir.to_sexpr(e) for e in (a,) + sibs),
        'source_json': ir.to_json(a),
        'replacement': _text(ra, sibs, rbs),
        'replacement_json': ir.to_json(ra),
        'vw': list(vw),
        'region': {
            'outputs': [{'node': 0, 'result': ops.parse(a[0])[2],
                         'source': ir.to_sexpr(a),
                         'replacement': ir.to_sexpr(ra),
                         'replacement_json': ir.to_json(ra)}],
            # The variables that the tree does not have: the generated
            # matcher takes them from the operands of the siblings.
            'sibling_vars': sorted(set(range(len(vw))) -
                                   set(ir.variables(a))),
            # The values below the root that must have no user outside
            # the region: the rule needs to remove them.
            'dead_nodes': dead,
            'siblings': [dict(
                {'source': ir.to_sexpr(s), 'source_json': ir.to_json(s),
                 # The value of the region that each operand is.
                 'operands': [_ref_json(x) for x in rf],
                 'result': ops.parse(s[0])[2], 'stays': r is None},
                **({} if r is None else {
                    'replacement': ir.to_sexpr(r),
                    'replacement_json': ir.to_json(r)}))
                for s, r, rf in zip(sibs, rbs, refs)]},
        'disjuncts': [],
        'unselected_disjuncts': [],
        'class': 'reduces_cost',
        'cost': {'source': region.joint_cost([a] + list(sibs)),
                 'replacement': region.joint_cost(tgts)},
        # The rule removes the primary root, and each sibling that has a
        # replacement. With more new instructions than that, values
        # below the primary root must have no other user (dead_nodes).
        'needs_one_use': bool(dead),
        'widens_operation': False,
        'semantic_status': {
            'kind': 'verified_refinement', 'model': synth.SEMANTIC_MODEL,
            'direction': 'source -> replacement',
            'solver': '%s %s' % (sy.backend.name, sy.backend.version),
            'joint_outputs': 1 + len(sibs)},
        'search': st,
        'provenance': {'discovery': 'joint-sibling+smt',
                       'generalization': 'symbolic-known-bits',
                       'sources': ['enumerative']},
        'support': {'instances': 0, 'occurrences': 0, 'examples': [],
                    'training_constants': {}, 'source_flags': []},
        'coverage': {'match_instances': 0, 'match_occurrences': 0,
                     'pass_instances': 0, 'pass_occurrences': 0,
                     'disjunct_occurrences': []},
        '_cex': pool,
    }


def _support(rule, d, pair, perm, facts, vw):
    n = len(pair.prov)
    for sup in (rule['support'], d['support']):
        sup['instances'] += 1
        sup['occurrences'] += n
    d.setdefault('example', {
        'vw': list(vw), 'facts': [[hex(f[0]), hex(f[1])] + list(f[2:])
                                  for f in facts]})
    sup = rule['support']
    for p in pair.prov[:2]:
        if len(sup['examples']) < 5:
            ex = {'file': p[0].rsplit('/', 1)[-1], 'fn': p[1],
                  'root': p[2]}
            if isinstance(p[3], list):
                ex['siblings'] = p[3]
            else:
                ex['sibling'] = p[3]
            sup['examples'].append(ex)
    for new, old in enumerate(perm):
        c = pair.inst.consts[old]
        if c is not None:
            vals = sup['training_constants'].setdefault('x%d' % new, [])
            if hex(c) not in vals and len(vals) < 8:
                vals.append(hex(c))
    for fl in pair.inst.flags:
        if fl not in sup['source_flags']:
            sup['source_flags'].append(fl)
    cov = rule['coverage']
    for k in ('match_instances', 'pass_instances'):
        cov[k] += 1
    for k in ('match_occurrences', 'pass_occurrences'):
        cov[k] += n
    k = rule['disjuncts'].index(d)
    cov['disjunct_occurrences'] += [0] * (k + 1 - len(
        cov['disjunct_occurrences']))
    cov['disjunct_occurrences'][k] += n
    d['coverage_occurrences'] = cov['disjunct_occurrences'][k]


def add(sy, by_key, pair, ra, rb, stats):
    """Generalizes and proves one candidate of a group. ``rb`` is the
    replacement of the sibling (None: it stays), or a sequence with one
    entry per sibling. Returns the id of the rule, or None."""
    inst = pair.inst
    rbs = _seq(rb)
    a, ra, sibs, rbs, vw, facts, perm = canonicalize(
        inst.expr, ra, pair.sibs, rbs, inst.vw, inst.facts)
    # In the canonical form each operand of a sibling is still one value
    # of the region.
    if operand_refs(a, sibs) is None or not freeze_ok(a, sibs):
        stats['not_a_region'] = stats.get('not_a_region', 0) + 1
        return None
    key = class_key(a, ra, sibs, rbs, vw)
    rule = sy.rules.get(by_key.get(key))
    rw = a[1]
    if rule is not None:
        pa, pra = (ir.from_json(rule['source_json']),
                   ir.from_json(rule['replacement_json']))
        psibs, prbs = rule_siblings(rule)
        pvw = tuple(rule['vw'])
    else:
        pa, pra, psibs, prbs, pvw = a, ra, sibs, rbs, vw
    first = dict(zip(_widths(_exprs(pa, pra, psibs, prbs), pvw),
                     _widths(_exprs(a, ra, sibs, rbs), vw)))
    if rule is not None:
        fkey = synth._map_key(first.items())
        for d in rule['disjuncts']:
            if not precond.eval_pred(d['_pred'], facts, vw, rw):
                continue
            if fkey not in {synth._map_key(m) for m in d['width_maps']}:
                sched = rule_schedules(rule, [sorted(first.items())])
                if None in sched:
                    continue
                stats['smt_checks'] += 1
                st, proofs = region.verify(sched, [d['_pred']], sy.backend)
                if st != 'valid':
                    continue
                sy._add_disjunct(rule, d['_pred'], proofs)
            _support(rule, d, pair, perm, facts, vw)
            stats['reused'] += 1
            return rule['id']
    pool = rule['_cex'] if rule is not None else []
    sched = schedules(pa, pra, psibs, prbs, pvw, sy.limits, first)
    calls = sy.backend.calls
    valid, st = synth.synthesize_precondition(
        pa, pra, pvw, facts, sched, sy.backend, sy.limits, pool, vw, rw,
        verify_fn=_verify)
    if not valid and len(sched) > 1 and not st['unknown']:
        # Only at the widths of the instance.
        valid, st = synth.synthesize_precondition(
            pa, pra, pvw, facts, sched[:1], sy.backend, sy.limits, None,
            vw, rw, verify_fn=_verify)
    stats['smt_checks'] += sy.backend.calls - calls
    stats['counterexamples'] += st['counterexamples']
    stats['unknown'] += st['unknown']
    if not valid:
        stats['no_precondition'] += 1
        return None
    if rule is None:
        # The users of the values below the root, in the canonical form.
        m = {o: n for n, o in enumerate(perm)}
        by_node = {}
        for n, u in zip(ir.interior_nodes(inst.expr), inst.interior_uses):
            k = synth.normalize_commutative(ir.rename(n, m))
            by_node[k] = max(u, by_node.get(k, 0))
        uses = [by_node.get(synth.normalize_commutative(n), 2)
                for n in ir.interior_nodes(a)]
        rule = _new_rule(sy, a, ra, sibs, rbs, vw, st, pool, uses)
        if rule['id'] in sy.rules:
            return None
        sy.rules[rule['id']] = rule
        by_key[key] = rule['id']
        stats['rules'] += 1
        stats['rules_with_two_siblings'] += len(sibs) == 2
    first_d = None
    for pred, proofs in synth.weakest(valid, vw, sy.backend, rw):
        d = sy._add_disjunct(rule, pred, proofs)
        first_d = first_d or d
    rule['precondition'] = synth.precondition_text(rule)
    rule['width_specific'] = all(len(d['width_maps']) == 1
                                 for d in rule['disjuncts'])
    _support(rule, first_d, pair, perm, facts, vw)
    return rule['id']


def extend(sy, pairs, found, backend, limits, ctx, max_pairs=0):
    """Adds the rules with siblings to the synthesizer ``sy``. ``found``
    maps the key of an instance to the replacements of its root that the
    single-root search proved: a group must be cheaper than those rules.
    Returns the statistics of the step."""
    stats = {'pairs': 0, 'pairs_with_candidates': 0, 'candidates': 0,
             'smt_checks': 0, 'refuted_concrete': 0, 'counterexamples': 0,
             'unknown': 0, 'no_precondition': 0, 'bank_full': 0,
             'rules': 0, 'rules_with_two_siblings': 0, 'reused': 0,
             'not_searched': 0}
    by_key = {}
    for n, pair in enumerate(pairs):
        if max_pairs and n >= max_pairs:
            stats['not_searched'] = len(pairs) - n
            break
        stats['pairs'] += 1
        inst = pair.inst
        kept = kept_nodes(inst)
        sibs = list(pair.sibs)
        best = min([region.joint_cost([inst.expr] + sibs)] + [
            region.joint_cost([t] + sibs + kept)
            for t in found.get(pair.base_key, ())])
        try:
            cands = search(pair, limits, ctx, best)
        except discover._Full:
            stats['bank_full'] += 1
            continue
        if not cands:
            continue
        stats['pairs_with_candidates'] += 1
        for _, ra, rb in cands[:MAX_TRIES]:
            stats['candidates'] += 1
            if add(sy, by_key, pair, ra, rb, stats):
                break
    for rid in by_key.values():
        r = sy.rules[rid]
        r['precondition'] = synth.precondition_text(r)
        r['width_specific'] = all(len(d['width_maps']) == 1
                                  for d in r['disjuncts'])
    return stats
