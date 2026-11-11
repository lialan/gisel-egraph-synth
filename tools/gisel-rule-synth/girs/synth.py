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
3. Synthesize a precondition by counterexample-guided enumeration over the
   grammar in precond.py: conjunctions are tried smallest first; each must
   hold on the training instance's facts, must not admit any stored
   counterexample, and must make the refinement query UNSAT for every width
   schedule. A SAT answer adds its fact assignment to the counterexample
   pool. UNKNOWN (e.g. timeout) never counts as a proof.
4. Among the valid preconditions of minimal size, keep the logically weakest
   (decided by SMT implication over the facts).
"""

import hashlib
import itertools
import os

from . import ir
from . import precond
from . import smt

WIDTHS = (8, 16, 32, 64)
SEMANTIC_MODEL = 'gmir-int-v1'


class SynthLimits:
    def __init__(self, max_atoms=2, max_solver_calls=400, max_schedules=8,
                 max_valid=6):
        self.max_atoms = max_atoms
        self.max_solver_calls = max_solver_calls  # per precondition search
        self.max_schedules = max_schedules
        self.max_valid = max_valid


# ------------------------------------------------------ canonical form ---

def normalize_commutative(e):
    """Orders the operands of commutative operations (used for the
    replacement, whose operand order does not matter)."""
    if not ir.is_op(e):
        return e
    args = tuple(normalize_commutative(a) for a in e[2:])
    if e[0] in ir.COMMUTATIVE:
        args = tuple(sorted(args, key=ir.to_sexpr))
    return e[:2] + args


def widens_operation(src, tgt):
    """True if the replacement computes a non-cast operation in a type wider
    than every non-cast operation of the source (e.g. turning an s16 mul of
    truncs into an s32 mul). Such rules are verified but not emitted: they
    are not profitable on targets with native narrow operations and would
    fight the existing narrowing combines."""
    def ops(e):
        return [n for n in [e] + ir.interior_nodes(e)
                if ir.is_op(n) and n[0] not in ir.CASTS]
    sw = [n[1] for n in ops(src)] or [0]
    return any(n[1] > max(sw) for n in ops(tgt))


def canonicalize(src, tgt, vw, facts):
    """Returns (src', tgt', vw', facts', perm) with variables renamed by first
    occurrence and commutative operands of src in a canonical order.
    perm[new] = old."""
    best = None
    for sv in ir.commuted_variants(src):
        order = ir.variables(sv)
        m = {old: new for new, old in enumerate(order)}
        s2 = ir.rename(sv, m)
        t2 = normalize_commutative(ir.rename(tgt, m))
        k = (ir.to_sexpr(s2), ir.to_sexpr(t2))
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


def class_key(src, tgt, vw):
    """Width-independent key of a canonical (src, tgt) pair."""
    ws = all_widths(src, tgt, vw)
    cls = {w: 1000 + i for i, w in enumerate(ws)}
    return (ir.to_sexpr(ir.map_widths(src, cls)),
            ir.to_sexpr(ir.map_widths(tgt, cls)),
            tuple(cls[w] for w in vw))


def schedules(src, tgt, vw, limits):
    """Width schedules (src_i, tgt_i, vw_i, width_map) to verify, the
    training schedule first."""
    ws = all_widths(src, tgt, vw)
    pool = sorted(set(WIDTHS) | set(ws))
    out = [(src, tgt, vw, {w: w for w in ws})]
    for combo in itertools.combinations(pool, len(ws)):
        wmap = dict(zip(ws, combo))
        if list(combo) == ws:
            continue
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
    _, kz, ko = smt.split_model(vals, n)
    return tuple(zip(kz, ko))


def verify(sched, pred, backend):
    """Proves pred => (tgt refines src) for every schedule. Returns
    ('valid', proofs) | ('invalid', (vw, facts)) | ('unknown', None)."""
    proofs = []
    for s, t, v, wmap in sched:
        enc = smt.Encoder(v, s[1])
        f = smt.refinement_violation(enc, s, t, precond.z3_pred(pred, enc))
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


def synthesize_precondition(src, tgt, vw, facts, sched, backend, limits):
    """CEGIS over the precondition grammar. Returns (valid, stats) where
    valid is a list of (pred, proofs), all of minimal size."""
    rw = src[1]
    atoms = [a for a in precond.enumerate_atoms(vw, rw)
             if precond.eval_atom(a, facts, vw, rw)]
    pool = []   # counterexample fact assignments: (vw, facts, root width)
    stats = {'atoms': len(atoms), 'tried': 0, 'pruned_by_cex': 0,
             'counterexamples': 0, 'unknown': 0, 'solver_calls': 0}
    calls0 = backend.calls
    valid = []
    for size in range(0, limits.max_atoms + 1):
        for p in itertools.combinations(atoms, size):
            if backend.calls - calls0 >= limits.max_solver_calls:
                stats['budget_exhausted'] = True
                break
            stats['tried'] += 1
            if any(precond.eval_pred(p, f, v, r) for v, f, r in pool):
                stats['pruned_by_cex'] += 1
                continue
            status, info = verify(sched, p, backend)
            if status == 'invalid':
                pool.append(info)
                stats['counterexamples'] += 1
            elif status == 'unknown':
                stats['unknown'] += 1
            else:
                valid.append((p, info))
                if len(valid) >= limits.max_valid:
                    break
        if valid:
            break
    stats['solver_calls'] = backend.calls - calls0
    return valid, stats


def weakest(valid, vw, backend, rw=None):
    """Drops preconditions strictly stronger than another valid one. The
    rest is ordered deterministically (first = chosen)."""
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

def rule_id(src, tgt, vw, pred):
    key = repr(class_key(src, tgt, vw)) + precond.pred_str(pred)
    h = hashlib.sha256(key.encode()).hexdigest()[:8]
    return 'synth_%s_%s' % (src[0][2:].lower(), h)


def save_proofs(proofs, proof_dir):
    out = []
    for p in proofs:
        smt2 = p.pop('smt2')
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


class Synthesizer:
    """Accumulates verified and rejected rules over many discoveries."""

    def __init__(self, backend, limits=None, proof_dir=None):
        self.backend = backend
        self.limits = limits or SynthLimits()
        self.proof_dir = proof_dir
        self.rules = {}       # id -> rule dict
        self.by_key = {}      # class_key -> [rule id]
        self.rejected = {}    # (class_key) -> record
        self.stats = {'discoveries': 0, 'generalized': 0, 'reused': 0,
                      'rejected': 0}

    def _support(self, rule, inst, perm, facts=None):
        sup = rule['support']
        if facts is not None and 'example_facts' not in sup:
            # Canonical-order facts of the first training instance, used to
            # rebuild a test case (eval/baseline.py).
            sup['example_facts'] = [[hex(z), hex(o)] for z, o in facts]
            sup['example_vw'] = list(rule['vw'])
        sup['instances'] += 1
        sup['occurrences'] += len(inst.prov)
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

    def add(self, inst, tgt):
        """Generalizes and verifies one concrete discovery."""
        self.stats['discoveries'] += 1
        src, tgt, vw, facts, perm = canonicalize(inst.expr, tgt, inst.vw,
                                                 inst.facts)
        # Structural soundness conditions of the refinement argument
        # (README.md, "Semantic model").
        assert set(ir.variables(tgt)) <= set(ir.variables(src))
        assert ir.is_linear(tgt)
        key = class_key(src, tgt, vw)
        for rid in self.by_key.get(key, []):
            r = self.rules[rid]
            if precond.eval_pred(r['_pred'], facts, vw, src[1]):
                self._support(r, inst, perm)
                self.stats['reused'] += 1
                return rid
        if key in self.rejected:
            self.rejected[key]['instances'] += 1
            return None
        sched = schedules(src, tgt, vw, self.limits)
        valid, st = synthesize_precondition(src, tgt, vw, facts, sched,
                                            self.backend, self.limits)
        width_specific = False
        if not valid and len(sched) > 1 and not st['unknown']:
            # Some identities only hold at the training widths (e.g.
            # xor == add for s1). Retry with the training schedule alone;
            # the guard then only accepts those widths.
            valid, st2 = synthesize_precondition(src, tgt, vw, facts,
                                                 sched[:1], self.backend,
                                                 self.limits)
            st = {k: st.get(k, 0) + st2.get(k, 0) for k in set(st) | set(st2)
                  if isinstance(st.get(k, st2.get(k)), int)}
            width_specific = bool(valid)
        if not valid:
            self.stats['rejected'] += 1
            self.rejected[key] = {
                'source': ir.to_sexpr(src), 'replacement': ir.to_sexpr(tgt),
                'vw': list(vw),
                'reason': ('solver_unknown' if st['unknown'] else
                           'no_precondition_in_grammar'),
                'search': st, 'instances': 1,
                'example': {'file': os.path.basename(inst.prov[0][0]),
                            'fn': inst.prov[0][1], 'root': inst.prov[0][2],
                            'facts': [[hex(z), hex(o)] for z, o in facts]}}
            return None
        best = weakest(valid, vw, self.backend, src[1])
        pred, proofs = best[0]
        rid = rule_id(src, tgt, vw, pred)
        if rid in self.rules:   # same rule found from a different instance
            self._support(self.rules[rid], inst, perm)
            return rid
        self.stats['generalized'] += 1
        rule = {
            'id': rid,
            'source': ir.to_sexpr(src),
            'source_json': ir.to_json(src),
            'replacement': ir.to_sexpr(tgt),
            'replacement_json': ir.to_json(tgt),
            'vw': list(vw),
            'precondition': precond.pred_str(pred),
            'precondition_json': [precond.atom_to_json(a) for a in pred],
            'alternatives': [precond.pred_str(p) for p, _ in best[1:]],
            'cost': {'source': ir.cost(src), 'replacement': ir.cost(tgt)},
            # If the replacement costs no more than the root instruction,
            # the rewrite never increases the instruction count even when
            # the interior instructions stay alive for other users.
            'needs_one_use': ir.cost(tgt) > ir.OP_COST[src[0]] and
            bool(ir.interior_nodes(src)),
            'width_specific': width_specific,
            'widens_operation': widens_operation(src, tgt),
            'semantic_status': {
                'kind': 'verified_refinement',
                'model': SEMANTIC_MODEL,
                'direction': 'source -> replacement',
                'solver': '%s %s' % (self.backend.name,
                                     self.backend.version),
                'schedules': [p['vw'] + [p['root_w']] for p in proofs],
                'proofs': save_proofs(proofs, self.proof_dir),
            },
            'search': st,
            'provenance': {'discovery': 'enumerative-fingerprint+smt',
                           'generalization': 'symbolic-known-bits'},
            'support': {'instances': 0, 'occurrences': 0, 'examples': [],
                        'training_constants': {}, 'source_flags': []},
            '_pred': pred,
        }
        self.rules[rid] = rule
        self.by_key.setdefault(key, []).append(rid)
        self._support(rule, inst, perm, facts)
        return rid

    def finalize(self):
        """Subsumption: for rules with the same source and replacement,
        drop a rule whose precondition implies another's."""
        dropped = []
        for key, ids in self.by_key.items():
            for a in ids:
                ra = self.rules.get(a)
                if ra is None:
                    continue
                for b in ids:
                    rb = self.rules.get(b)
                    if a == b or rb is None:
                        continue
                    if precond.implies(ra['_pred'], rb['_pred'],
                                       tuple(ra['vw']), self.backend,
                                       ra['source_json']['w']):
                        rb['support']['instances'] += \
                            ra['support']['instances']
                        rb['support']['occurrences'] += \
                            ra['support']['occurrences']
                        rb.setdefault('subsumes', []).append(a)
                        del self.rules[a]
                        dropped.append(a)
                        break
        return dropped
