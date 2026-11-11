"""Generalization, precondition synthesis (CEGIS) and verification.

Pipeline for one concrete discovery (instance S, replacement T, proved under
the instance's concrete facts):

1. Generalize. Every input becomes a pattern variable with *symbolic* known
   bits, including inputs that were constants (a constant is just a value
   whose known bits are exact, so a rule that only needs the known bits of
   ``255`` also applies to any register with the same known bits). Widths
   become width classes; the rule is re-verified for every class-to-width
   schedule drawn from WIDTHS that keeps the cast directions valid, and the
   emitted guard only accepts verified schedules.
2. Canonicalize. Variables are renamed by first occurrence and commutative
   operands are ordered, so rules that differ by renaming or commutation get
   the same key.
3. Synthesize preconditions by counterexample-guided enumeration over the
   grammar in precond.py: conjunctions are tried smallest first; each must
   hold on the training instance's facts, must not admit any stored
   counterexample, and must make the refinement query UNSAT for every width
   schedule. A SAT answer adds its fact assignment to the counterexample
   pool of the rule. UNKNOWN (e.g. timeout) never counts as a proof. The
   search keeps every *minimal* valid conjunction (a superset of a valid
   conjunction is only stronger), not just the smallest one.
4. One rule per (source, replacement) class. Its precondition is the
   disjunction of the conjunctions found from all training instances; an
   instance that no disjunct covers starts a new search. A disjunct that
   implies another one with the same verified widths is dropped.
5. Select (``Synthesizer.finalize``). The disjuncts of a rule are ranked by
   the corpus occurrences they cover and by their run-time cost (known-bits
   queries), greedily: a disjunct that covers nothing new is not emitted.
   The selected disjunction is proved again as a whole for every schedule.

Each disjunct keeps its own list of verified width schedules. A schedule
fixes the width of *every* node of the source and of the replacement, not
only of the variables and the root.
"""

import hashlib
import itertools
import os

from . import ir
from . import ops
from . import precond
from . import smt

WIDTHS = (8, 16, 32, 64)
# v2: each input can be poison, G_FREEZE, the conversions between integers
# and floating-point values.
SEMANTIC_MODEL = 'gmir-v2'


class SynthLimits:
    def __init__(self, max_atoms=2, max_solver_calls=400, max_schedules=8,
                 max_valid=8, max_disjuncts=4):
        self.max_atoms = max_atoms
        self.max_solver_calls = max_solver_calls  # per precondition search
        self.max_schedules = max_schedules
        self.max_valid = max_valid           # conjunctions per search
        self.max_disjuncts = max_disjuncts   # emitted per rule


# ------------------------------------------------------ canonical form ---

def normalize_commutative(e):
    """Orders the operands of commutative operations (used for the
    replacement, whose operand order does not matter)."""
    if not ir.is_op(e):
        return e
    args = tuple(normalize_commutative(a) for a in e[2:])
    if ir.is_commutative(e[0]):
        args = tuple(sorted(args[:2], key=ir.to_sexpr)) + args[2:]
    return e[:2] + args


def widens_operation(src, tgt):
    """True if the replacement computes a non-cast operation in a type wider
    than every non-cast operation of the source (e.g. turning an s16 mul of
    truncs into an s32 mul). Such rules are verified but not emitted: they
    are not profitable on targets with native narrow operations and would
    fight the existing narrowing combines."""
    return widened_width(src, tgt) != 0


def widened_width(src, tgt):
    """The width of the widest non-cast operation of the replacement, if
    it is wider than every non-cast operation of the source; else 0."""
    def non_casts(e):
        return [n for n in [e] + ir.interior_nodes(e)
                if ir.is_op(n) and ops.parse(n[0])[0].shape != 'cast']
    sw = max([n[1] for n in non_casts(src)] or [0])
    tw = max([n[1] for n in non_casts(tgt)] or [0])
    return tw if tw > sw else 0


def canonicalize(src, tgt, vw, facts):
    """Returns (src', tgt', vw', facts', perm) with variables renamed by first
    occurrence and commutative operands of src in a canonical order.
    perm[new] = old."""
    best = None
    # Compare with width classes, so that instances of one rule class at
    # different widths get the same variable order.
    cls = {w: 1000 + i for i, w in enumerate(all_widths(src, tgt, vw))}
    for sv in ir.commuted_variants(src):
        order = ir.variables(sv)
        m = {old: new for new, old in enumerate(order)}
        s2 = ir.rename(sv, m)
        t2 = normalize_commutative(ir.rename(tgt, m))
        k = (ir.to_sexpr(ir.map_widths(s2, cls)),
             ir.to_sexpr(ir.map_widths(t2, cls)))
        if best is None or k < best[0]:
            best = (k, s2, t2, order)
    _, s2, t2, order = best
    return (s2, t2, tuple(vw[o] for o in order),
            tuple(facts[o] for o in order), tuple(order))


def all_widths(src, tgt, vw):
    ws = set(vw)
    for e in [src, tgt] + ir.interior_nodes(src) + ir.interior_nodes(tgt):
        if not ir.is_var(e):
            ws.add(e[1])
    return sorted(ws)


def class_key(src, tgt, vw, const_vars=()):
    """Width-independent key of a canonical (src, tgt) pair."""
    ws = all_widths(src, tgt, vw)
    cls = {w: 1000 + i for i, w in enumerate(ws)}
    key = (ir.to_sexpr(ir.map_widths(src, cls)),
           ir.to_sexpr(ir.map_widths(tgt, cls)),
           tuple(cls[w] for w in vw))
    return key + (tuple(const_vars),) if const_vars else key


def schedules(src, tgt, vw, limits, first=None):
    """Width schedules (src_i, tgt_i, vw_i, width_map) to verify. ``first``
    maps the pattern widths to the training widths (default: identity); that
    schedule comes first."""
    ws = all_widths(src, tgt, vw)
    first = first or {w: w for w in ws}
    head = [first[w] for w in ws]
    pool = sorted(set(WIDTHS) | set(ws) | set(head))
    out = []
    for combo in [tuple(head)] + list(itertools.combinations(pool, len(ws))):
        if out and list(combo) == head:
            continue
        wmap = dict(zip(ws, combo))
        s = ir.map_widths(src, wmap)
        t = ir.map_widths(tgt, wmap)
        v = tuple(wmap[w] for w in vw)
        if ir.well_typed(s, v) and ir.well_typed(t, v):
            out.append((s, t, v, wmap))
        if len(out) >= limits.max_schedules:
            break
    return out


# ------------------------------------------------------------- CEGIS ---

def _facts_from_model(vals, n):
    _, kz, ko, xp = smt.split_model(vals, n)
    # A value that is not poison in the model counts as defined: the
    # counterexample then also excludes the preconditions with 'def'.
    return tuple((z, o, True) if not p else (z, o)
                 for z, o, p in zip(kz, ko, xp))


def verify(sched, dnf, backend, const_vars=()):
    """Proves (p1 || p2 || ...) => (tgt refines src) for every schedule;
    ``dnf`` is a list of conjunctions. ``const_vars`` are the variables
    that are constants (their known bits are exact). Returns ('valid',
    proofs) | ('invalid', (vw, facts, root width)) | ('unknown', None)."""
    assert dnf, 'an empty disjunction is false and proves nothing'
    proofs = []
    for s, t, v, wmap in sched:
        enc = smt.Encoder(v, s[1], const_vars)
        f = smt.refinement_violation(enc, s, t, precond.z3_dnf(dnf, enc))
        r = backend.check(f, want_model_of=enc.model_terms())
        if r.status == 'sat':
            return 'invalid', (v, _facts_from_model(r.model, len(v)), s[1])
        if r.status != 'unsat':
            return 'unknown', None
        proofs.append({'vw': list(v), 'root_w': s[1],
                       'width_map': sorted([a, b] for a, b in wmap.items()),
                       'result': 'unsat',
                       'seconds': round(r.seconds, 4), 'smt2': r.smt2})
    return 'valid', proofs


def synthesize_precondition(src, tgt, vw, facts, sched, backend, limits,
                            pool=None, fvw=None, frw=None, const_vars=(),
                            verify_fn=None):
    """CEGIS over the precondition grammar. Returns (valid, stats) where
    valid lists every minimal valid conjunction as (pred, proofs), smallest
    first. ``pool`` is the counterexample pool of the rule class; it is
    extended in place. ``facts`` are the training facts, for variables of
    widths ``fvw`` and root width ``frw`` (default: the pattern's).
    ``verify_fn`` proves the schedules ``sched`` (default: verify; a rule
    with several outputs has schedules and a proof of its own)."""
    verify_fn = verify_fn or verify
    fvw = vw if fvw is None else fvw
    frw = src[1] if frw is None else frw
    atoms = [a for a in precond.enumerate_atoms(fvw, frw)
             if precond.eval_atom(a, facts, fvw, frw)]
    if pool is None:
        pool = []
    stats = {'atoms': len(atoms), 'tried': 0, 'pruned_by_cex': 0,
             'counterexamples': 0, 'unknown': 0, 'solver_calls': 0}
    calls0 = backend.calls
    valid = []
    done = False
    for size in range(0, limits.max_atoms + 1):
        for p in itertools.combinations(atoms, size):
            # A superset of a valid conjunction is valid but stronger.
            if any(set(q) <= set(p) for q, _ in valid):
                continue
            if backend.calls - calls0 >= limits.max_solver_calls:
                stats['budget_exhausted'] = True
                done = True
                break
            stats['tried'] += 1
            if any(precond.eval_pred(p, f, v, r) for v, f, r in pool):
                stats['pruned_by_cex'] += 1
                continue
            status, info = verify_fn(sched, [p], backend, const_vars)
            if status == 'invalid':
                pool.append(info)
                stats['counterexamples'] += 1
            elif status == 'unknown':
                stats['unknown'] += 1
            else:
                valid.append((p, info))
                if len(valid) >= limits.max_valid or size == 0:
                    done = True
                    break
        if done:
            break
    stats['solver_calls'] = backend.calls - calls0
    return valid, stats


def weakest(valid, vw, backend, rw=None):
    """Drops preconditions strictly stronger than another valid one. The
    rest is ordered deterministically."""
    keep = []
    for i, (p, pr) in enumerate(valid):
        dominated = False
        for j, (q, _) in enumerate(valid):
            if i == j:
                continue
            if precond.implies(p, q, vw, backend, rw):
                if not precond.implies(q, p, vw, backend, rw) or j < i:
                    dominated = True   # strictly stronger, or equivalent
                    break              # to an earlier one
        if not dominated:
            keep.append((p, pr))
    keep.sort(key=lambda x: precond.pred_str(x[0]))
    return keep


# ------------------------------------------------------------- rules ---

def rule_id(src, tgt, vw, const_vars=()):
    h = hashlib.sha256(repr(class_key(src, tgt, vw, const_vars))
                       .encode()).hexdigest()
    return 'synth_%s_%s' % (ops.base(src[0])[2:].lower(), h[:8])


def save_proofs(proofs, proof_dir):
    out = []
    for p in proofs:
        p = dict(p)
        smt2 = p.pop('smt2')
        p.pop('seconds', None)
        h = hashlib.sha256(smt2.encode()).hexdigest()[:16]
        if proof_dir:
            os.makedirs(proof_dir, exist_ok=True)
            path = os.path.join(proof_dir, h + '.smt2')
            if not os.path.exists(path):
                with open(path, 'w') as f:
                    f.write(smt2)
        p['smt2_sha256'] = h
        out.append(p)
    return out


def _map_key(wmap):
    return tuple(sorted((a, b) for a, b in wmap))


def rule_schedules(rule, maps):
    """(src, tgt, vw, width map) tuples of a stored rule for the given
    width maps (lists of [pattern width, width] pairs)."""
    src = ir.from_json(rule['source_json'])
    tgt = ir.from_json(rule['replacement_json'])
    vw = tuple(rule['vw'])
    out = []
    for m in maps:
        m = dict(m)
        out.append((ir.map_widths(src, m), ir.map_widths(tgt, m),
                    tuple(m[w] for w in vw), m))
    return out


def _source_of(provenance):
    """The engine that proposed a discovery: 'enumerative', 'composition'
    or 'egraph'."""
    d = (provenance or {}).get('discovery', 'enumerative')
    return d if d in ('composition', 'egraph') else 'enumerative'


def rule_class(src, tgt, const_vars=()):
    if widens_operation(src, tgt):
        return 'widens_operation'
    if ir.rule_cost(tgt, const_vars) >= ir.cost(src):
        return 'equal_cost'
    return 'reduces_cost'


class Synthesizer:
    """Accumulates verified and rejected rules over many discoveries. There
    is one rule per (source, replacement) class; its precondition is a
    disjunction of independently proved conjunctions."""

    MAX_REJECT_RETRIES = 3

    def __init__(self, backend, limits=None, proof_dir=None):
        self.backend = backend
        self.limits = limits or SynthLimits()
        self.proof_dir = proof_dir
        self.rules = {}       # id -> rule dict
        self.by_key = {}      # class_key -> rule id
        self.rejected = {}    # class_key -> record
        self.stats = {'discoveries': 0, 'generalized': 0, 'reused': 0,
                      'rejected': 0, 'disjuncts_added': 0,
                      'schedules_added': 0, 'uncovered': 0}

    # -- support bookkeeping --

    def _support(self, rule, d, inst, perm, facts, vw):
        for sup in (rule['support'], d['support']):
            sup['instances'] += 1
            sup['occurrences'] += len(inst.prov)
        if 'example' not in d:
            # Canonical-order facts of the first training instance of this
            # disjunct, used to rebuild a test case.
            d['example'] = {'vw': list(vw),
                            'facts': [[hex(f[0]), hex(f[1])] + list(f[2:])
                                      for f in facts]}
        sup = rule['support']
        for p in inst.prov[:2]:
            if len(sup['examples']) < 5:
                sup['examples'].append({'file': os.path.basename(p[0]),
                                        'fn': p[1], 'root': p[2]})
        for new, old in enumerate(perm):
            c = inst.consts[old]
            if c is not None:
                vals = sup['training_constants'].setdefault('x%d' % new, [])
                if hex(c) not in vals and len(vals) < 8:
                    vals.append(hex(c))
        for fl in inst.flags:
            if fl not in sup['source_flags']:
                sup['source_flags'].append(fl)

    def _add_disjunct(self, rule, pred, proofs):
        pred = precond.canonical_pred(pred)
        for d in rule['disjuncts']:
            if d['_pred'] == pred:
                break
        else:
            d = {'pred': precond.pred_str(pred),
                 'pred_json': [precond.atom_to_json(a) for a in pred],
                 'width_maps': [], 'proofs': [],
                 'support': {'instances': 0, 'occurrences': 0},
                 '_pred': pred}
            rule['disjuncts'].append(d)
            self.stats['disjuncts_added'] += 1
        have = {_map_key(m) for m in d['width_maps']}
        for p in save_proofs(proofs, self.proof_dir):
            if _map_key(p['width_map']) not in have:
                have.add(_map_key(p['width_map']))
                d['width_maps'].append(p['width_map'])
                d['proofs'].append(p)
        return d

    # -- one discovery --

    def add(self, inst, tgt, provenance=None):
        """Generalizes and verifies one concrete discovery. Returns the rule
        id, or None if no precondition was found."""
        self.stats['discoveries'] += 1
        src, tgt, vw, facts, perm = canonicalize(inst.expr, tgt, inst.vw,
                                                 inst.facts)
        cv = tuple(sorted(new for new, old in enumerate(perm)
                          if old in inst.const_vars))
        # Structural soundness conditions of the refinement argument
        # (README.md, "Semantic model").
        assert set(ir.variables(tgt)) <= set(ir.variables(src))
        assert ir.is_linear_in(tgt, cv)
        key = class_key(src, tgt, vw, cv)
        rw = src[1]
        rule = self.rules.get(self.by_key.get(key))
        rej = self.rejected.get(key)
        if rule is None and rej is not None:
            rej['instances'] += 1
            if rej['_retries'] >= self.MAX_REJECT_RETRIES:
                return None
            rej['_retries'] += 1
        if rule is not None:
            psrc = ir.from_json(rule['source_json'])
            ptgt = ir.from_json(rule['replacement_json'])
            pvw = tuple(rule['vw'])
            source = _source_of(provenance)
            if source not in rule['provenance']['sources']:
                rule['provenance']['sources'] = sorted(
                    rule['provenance']['sources'] + [source])
            if provenance and provenance['discovery'] not in \
                    rule['provenance']['discovery']:
                rule['provenance']['discovery'] += '+' + \
                    provenance['discovery']
                rule['provenance'].update(
                    {k: v for k, v in provenance.items()
                     if k != 'discovery'})
        else:
            psrc, ptgt, pvw = src, tgt, vw
        # Width map from the stored pattern to this instance.
        first = dict(zip(all_widths(psrc, ptgt, pvw),
                         all_widths(src, tgt, vw)))
        if rule is not None:
            fkey = _map_key(first.items())
            for d in rule['disjuncts']:
                if not precond.eval_pred(d['_pred'], facts, vw, rw):
                    continue
                if fkey not in {_map_key(m) for m in d['width_maps']}:
                    # Same rule at widths not proved yet: prove them.
                    st, proofs = verify(
                        rule_schedules(rule, [sorted(first.items())]),
                        [d['_pred']], self.backend, cv)
                    if st != 'valid':
                        continue
                    self._add_disjunct(rule, d['_pred'], proofs)
                    self.stats['schedules_added'] += 1
                self._support(rule, d, inst, perm, facts, vw)
                self.stats['reused'] += 1
                return rule['id']
        pool = rule['_cex'] if rule is not None else \
            (rej['_cex'] if rej is not None else [])
        sched = schedules(psrc, ptgt, pvw, self.limits, first)
        valid, st = synthesize_precondition(psrc, ptgt, pvw, facts, sched,
                                            self.backend, self.limits, pool,
                                            vw, rw, cv)
        if not valid and len(sched) > 1 and not st['unknown']:
            # Some identities only hold at the training widths (e.g.
            # xor == add for s1). Retry with the training schedule alone;
            # the guard then only accepts those widths.
            valid, st2 = synthesize_precondition(psrc, ptgt, pvw, facts,
                                                 sched[:1], self.backend,
                                                 self.limits, None, vw, rw,
                                                 cv)
            st = {k: st.get(k, 0) + st2.get(k, 0) for k in set(st) | set(st2)
                  if isinstance(st.get(k, st2.get(k)), int)}
        if not valid:
            if rule is not None:
                self.stats['uncovered'] += 1
                return None
            if rej is None:
                self.stats['rejected'] += 1
                self.rejected[key] = {
                    'source': ir.to_sexpr(src),
                    'replacement': ir.to_sexpr(tgt), 'vw': list(vw),
                    'reason': ('solver_unknown' if st['unknown'] else
                               'no_precondition_in_grammar'),
                    'search': st, 'instances': 1, '_retries': 1,
                    '_cex': pool,
                    'example': {'file': os.path.basename(inst.prov[0][0]),
                                'fn': inst.prov[0][1],
                                'root': inst.prov[0][2],
                                'facts': [[hex(f[0]), hex(f[1])] +
                                          list(f[2:]) for f in facts]}}
            return None
        if rule is None:
            if rej is not None:
                del self.rejected[key]
                self.stats['rejected'] -= 1
            rule = self._new_rule(src, tgt, vw, key, st, pool, provenance,
                                  cv)
        best = weakest(valid, vw, self.backend, rw)
        first_d = None
        for pred, proofs in best:
            d = self._add_disjunct(rule, pred, proofs)
            first_d = first_d or d
        self._support(rule, first_d, inst, perm, facts, vw)
        return rule['id']

    def _new_rule(self, src, tgt, vw, key, st, pool, provenance, cv=()):
        rid = rule_id(src, tgt, vw, cv)
        assert rid not in self.rules
        self.stats['generalized'] += 1
        rule = {
            'id': rid,
            'source': ir.to_sexpr(src),
            'source_json': ir.to_json(src),
            'replacement': ir.to_sexpr(tgt),
            'replacement_json': ir.to_json(tgt),
            'vw': list(vw),
            'disjuncts': [],
            'class': rule_class(src, tgt, cv),
            'cost': {'source': ir.cost(src),
                     'replacement': ir.rule_cost(tgt, cv)},
            # If the replacement costs no more than the root instruction,
            # the rewrite never increases the instruction count even when
            # the interior instructions stay alive for other users.
            'needs_one_use': ir.rule_cost(tgt, cv) > ir.op_cost(src[0]) and
            bool(ir.interior_nodes(src)),
            'widens_operation': widens_operation(src, tgt),
            'semantic_status': {
                'kind': 'verified_refinement',
                'model': SEMANTIC_MODEL,
                'direction': 'source -> replacement',
                'solver': '%s %s' % (self.backend.name,
                                     self.backend.version),
            },
            'search': st,
            'provenance': dict(provenance or
                               {'discovery': 'enumerative-fingerprint+smt'},
                               generalization='symbolic-known-bits',
                               sources=[_source_of(provenance)]),
            'support': {'instances': 0, 'occurrences': 0, 'examples': [],
                        'training_constants': {}, 'source_flags': []},
            '_cex': pool,
        }
        if cv:
            # The variables that the rule only matches as constants.
            rule['const_vars'] = list(cv)
        self.rules[rid] = rule
        self.by_key[key] = rid
        return rule

    # -- selection of the emitted disjunction --

    def _drop_dominated(self, rule):
        """Drops a disjunct that implies another one proved for at least
        the same widths."""
        ds = rule['disjuncts']
        vw = tuple(rule['vw'])
        rw = rule['source_json']['w']
        keep = []
        for i, a in enumerate(ds):
            ma = {_map_key(m) for m in a['width_maps']}
            dominated = False
            for j, b in enumerate(ds):
                if i == j or not ma <= {_map_key(m)
                                        for m in b['width_maps']}:
                    continue
                if precond.implies(a['_pred'], b['_pred'], vw, self.backend,
                                   rw) and (
                        j < i or not precond.implies(
                            b['_pred'], a['_pred'], vw, self.backend, rw)):
                    dominated = True
                    b['support']['instances'] += a['support']['instances']
                    b['support']['occurrences'] += \
                        a['support']['occurrences']
                    break
            if not dominated:
                keep.append(a)
        dropped = len(ds) - len(keep)
        rule['disjuncts'] = keep
        return dropped

    def finalize(self, insts):
        """Chooses the emitted disjuncts of every rule by corpus coverage
        and run-time cost, and proves the chosen disjunction as a whole.
        Returns statistics."""
        from . import match
        stats = {'dominated_disjuncts': 0, 'unselected_disjuncts': 0,
                 'rules_with_disjunction': 0}
        for rule in self.rules.values():
            stats['dominated_disjuncts'] += self._drop_dominated(rule)
        cov = match.coverage(list(self.rules.values()), insts)
        occ = [len(i.prov) for i in insts]
        for rid in sorted(self.rules):
            rule = self.rules[rid]
            ds = rule['disjuncts']
            covered_by = cov[rid]['_covered']
            chosen, covered, have = [], set(), set()
            rest = list(range(len(ds)))
            while rest and len(chosen) < self.limits.max_disjuncts:
                def gain(k):
                    return sum(occ[i] for i in covered_by[k] - covered)
                best = max(rest, key=lambda k: (
                    gain(k), -precond.pred_cost(ds[k]['_pred'], have),
                    ds[k]['pred']))
                if chosen and gain(best) == 0:
                    break
                chosen.append(best)
                rest.remove(best)
                covered |= covered_by[best]
                have |= set(precond.pred_vars(ds[best]['_pred']))
            for k, d in enumerate(ds):
                d['coverage_occurrences'] = \
                    cov[rid]['disjunct_occurrences'][k]
            rule['unselected_disjuncts'] = [ds[k] for k in rest]
            rule['disjuncts'] = [ds[k] for k in chosen]
            stats['unselected_disjuncts'] += len(rest)
            stats['rules_with_disjunction'] += len(chosen) > 1
            rule['precondition'] = precondition_text(rule)
            rule['width_specific'] = all(len(d['width_maps']) == 1
                                         for d in rule['disjuncts'])
            rule['coverage'] = {k: v for k, v in cov[rid].items()
                                if not k.startswith('_')}
            rule['coverage']['disjunct_occurrences'] = [
                cov[rid]['disjunct_occurrences'][k] for k in chosen]
            rule['semantic_status']['dnf_proofs'] = \
                self._prove_disjunction(rule)
        stats['dominated_rules'] = self._mark_dominated()
        return stats

    def _mark_dominated(self):
        """Rules with the same source: one whose replacement is no cheaper
        and whose precondition implies another's is never the better
        choice. It stays in the library, marked ``dominated_by``."""
        from . import match
        groups = {}
        for rid in sorted(self.rules):
            r = self.rules[rid]
            src = ir.from_json(r['source_json'])
            vw = tuple(r['vw'])
            ws = sorted(set(vw) | {n[1] for n in [src] +
                                   ir.interior_nodes(src)})
            cls = {w: 1000 + i for i, w in enumerate(ws)}
            key = min(ir.to_sexpr(ir.rename(ir.map_widths(v, cls), {
                o: n for n, o in enumerate(ir.variables(v))}))
                for v in ir.commuted_variants(src))
            groups.setdefault(key, []).append(r)

        def better(a, b):
            """Preference when two rules dominate each other."""
            return (a['cost']['replacement'], -a['support']['occurrences'],
                    a['id']) < (b['cost']['replacement'],
                                -b['support']['occurrences'], b['id'])

        n = 0
        for rules in groups.values():
            for b in rules:
                for a in rules:
                    if a is b or 'dominated_by' in a or \
                            a['cost']['replacement'] > \
                            b['cost']['replacement']:
                        continue
                    if not self._implies_rule(b, a, match):
                        continue
                    if a['cost']['replacement'] == \
                            b['cost']['replacement'] and \
                            self._implies_rule(a, b, match) and \
                            not better(a, b):
                        continue
                    b['dominated_by'] = a['id']
                    n += 1
                    break
        return n

    def _implies_rule(self, b, a, match):
        """True if rule ``a`` applies wherever rule ``b`` does: for some
        alignment of their (equal) sources, every disjunct of b at each of
        its proved widths implies the disjunction of a at those widths."""
        asrc, avw = ir.from_json(a['source_json']), tuple(a['vw'])
        bsrc, bvw = ir.from_json(b['source_json']), tuple(b['vw'])
        aws = all_widths(asrc, ir.from_json(a['replacement_json']), avw)
        for bind, wmap in match.match(asrc, avw, bsrc, bvw,
                                      leaves_only=True):
            sigma = {i: e[1] for i, e in bind.items()}
            if len(set(sigma.values())) != len(sigma):
                continue
            # a matches some variables only as constants: b must do so too.
            if not {sigma[i] for i in a.get('const_vars', ())} <= \
                    set(b.get('const_vars', ())):
                continue
            ok = True
            for db in b['disjuncts']:
                for mb in db['width_maps']:
                    mb = dict(mb)
                    # a's width map that gives the same concrete widths.
                    want = {pw: mb[wmap[pw]] for pw in wmap}
                    dnf = []
                    for da in a['disjuncts']:
                        if any(all(dict(ma).get(pw) == w
                                   for pw, w in want.items())
                               for ma in da['width_maps']):
                            dnf.append([precond.rename_atom(x, sigma)
                                        for x in da['_pred']])
                    if not dnf or not precond.implies_dnf(
                            db['_pred'], dnf,
                            tuple(mb[w] for w in bvw), self.backend,
                            mb[bsrc[1]]):
                        ok = False
                        break
                if not ok:
                    break
            if ok and set(wmap) <= set(aws):
                return True
        return False

    def _prove_disjunction(self, rule):
        """Proves the emitted guard as a whole: for every width schedule
        some disjunct accepts, the disjunction of the disjuncts that accept
        it implies the refinement."""
        ds = rule['disjuncts']
        maps = {}
        for d in ds:
            for m in d['width_maps']:
                maps.setdefault(_map_key(m), m)
        out = []
        for key in sorted(maps):
            dnf = [d['_pred'] for d in ds
                   if key in {_map_key(m) for m in d['width_maps']}]
            st, proofs = verify(rule_schedules(rule, [maps[key]]), dnf,
                                self.backend,
                                tuple(rule.get('const_vars', ())))
            if st != 'valid':
                raise AssertionError('disjunction of proved disjuncts is '
                                     'not valid: %s' % rule['id'])
            out += save_proofs(proofs, self.proof_dir)
        return out


def precondition_text(rule):
    """The emitted precondition. A disjunct proved for fewer widths than
    the others says so."""
    ds = rule['disjuncts']
    keys = [{_map_key(m) for m in d['width_maps']} for d in ds]
    if all(k == keys[0] for k in keys):
        return precond.dnf_str([d['_pred'] for d in ds])
    parts = []
    most = max(len(k) for k in keys)
    for d, k in zip(ds, keys):
        t = d['pred']
        if len(k) < most:
            rows = sorted(tuple(dict(m)[w] for w in rule['vw']) +
                          (dict(m)[rule['source_json']['w']],)
                          for m in d['width_maps'])
            t += ' @ widths ' + '; '.join(','.join(map(str, r))
                                          for r in rows)
        parts.append('(%s)' % t)
    return ' || '.join(parts)


def strip_private(obj):
    """Deep copy without the in-memory keys (leading underscore)."""
    if isinstance(obj, dict):
        return {k: strip_private(v) for k, v in obj.items()
                if not k.startswith('_')}
    if isinstance(obj, list):
        return [strip_private(v) for v in obj]
    return obj
