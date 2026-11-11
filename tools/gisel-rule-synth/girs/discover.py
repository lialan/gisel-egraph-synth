"""Candidate discovery by bounded enumerative synthesis.

For a concrete corpus instance S (an expression plus concrete known bits of
its inputs) the search enumerates every *linear* expression over S's inputs
and the literals 0 / 1 / -1, bottom-up by cost, up to a cost bound below
cost(S). Terms are pruned by observational equivalence (as in Ruler /
enumerative superoptimizers): two terms of the same width whose values agree
on every sample input are kept once, the cheaper first.

Sample inputs are drawn so that they respect the instance's known bits.
Sampling is only a filter: a term whose fingerprint agrees with S on the
samples becomes a *candidate*, and a candidate is only reported as a concrete
discovery after an SMT proof that it refines S for every input consistent
with the instance's facts.

There is no table of rewrite rules anywhere in the search.
"""

import random

import z3

from . import ir
from . import smt


class Limits:
    def __init__(self, samples=48, max_terms=20000, max_candidates=3,
                 equal_cost_max=1, max_proofs=32, seed=0):
        self.samples = samples
        self.max_terms = max_terms          # per instance
        self.max_candidates = max_candidates  # proved candidates per instance
        self.max_proofs = max_proofs  # concrete SMT checks per instance
        # Also search replacements of *equal* cost when cost(S) <= this
        # (canonicalization candidates such as add -> or).
        self.equal_cost_max = equal_cost_max
        self.seed = seed


def _special(w):
    m = ir.mask(w)
    return [0, 1, 2, 3, m, m >> 1, (m >> 1) + 1, 0x55555555 & m,
            0xaaaaaaaa & m, w - 1 if w > 1 else 0, w // 2]


def sample_envs(inst, n, rng):
    envs = []
    for k in range(n):
        env = []
        for i, w in enumerate(inst.vw):
            z, o = inst.facts[i]
            m = ir.mask(w)
            if inst.consts[i] is not None:
                env.append(inst.consts[i])
                continue
            kind = k % 3
            if kind == 0:
                r = rng.getrandbits(w)
            elif kind == 1:
                r = rng.randrange(0, 2 * w + 2) & m
            else:
                sp = _special(w)
                r = sp[rng.randrange(len(sp))]
            env.append(((r & ~z) | o) & m)
        envs.append(tuple(env))
    return envs


def _apply(op, w, sw, va, vb):
    """Concrete op on fingerprint entries (None = poison)."""
    if va is None or (vb is None and op not in ir.CASTS):
        return None
    m = ir.mask(w)
    if op == 'G_TRUNC':
        return va & m
    if op == 'G_ZEXT':
        return va
    if op == 'G_SEXT':
        return (va - (1 << sw) if va >> (sw - 1) & 1 else va) & m
    if op == 'G_ADD':
        return (va + vb) & m
    if op == 'G_SUB':
        return (va - vb) & m
    if op == 'G_MUL':
        return (va * vb) & m
    if op == 'G_AND':
        return va & vb
    if op == 'G_OR':
        return va | vb
    if op == 'G_XOR':
        return va ^ vb
    if vb >= w:
        return None
    if op == 'G_SHL':
        return (va << vb) & m
    if op == 'G_LSHR':
        return va >> vb
    sa = va - (1 << w) if va >> (w - 1) & 1 else va
    return (sa >> vb) & m


class Term:
    __slots__ = ('expr', 'w', 'fp', 'cost', 'vars')

    def __init__(self, expr, w, fp, cost, vars_):
        self.expr, self.w, self.fp, self.cost, self.vars = \
            expr, w, fp, cost, vars_


def enumerate_terms(inst, envs, max_cost, limits, on_term=None):
    """Bottom-up enumeration of linear terms, pruned by fingerprint.

    ``on_term`` sees every well-typed term *before* the observational
    equivalence check, so a term equivalent to an earlier one (for instance
    to the source expression itself) can still be a candidate."""
    widths = sorted(set(inst.vw) |
                    {e[1] for e in [inst.expr] + ir.interior_nodes(inst.expr)})
    seen = {}   # (width, fingerprint) -> cheapest cost
    by_cost = {0: []}
    count = 0

    def add(t):
        nonlocal count
        key = (t.w, t.fp)
        best = seen.get(key)
        # A term with a strictly cheaper observational equivalent is never
        # a useful replacement (e.g. x + 0 vs x).
        if on_term is not None and (best is None or best >= t.cost):
            on_term(t)
        if best is not None:
            return False
        seen[key] = t.cost
        by_cost.setdefault(t.cost, []).append(t)
        count += 1
        return True

    for i, w in enumerate(inst.vw):
        add(Term(('var', i), w, tuple(env[i] for env in envs), 0,
                 frozenset([i])))
    for w in widths:
        for k in ir.LITERALS:
            v = ir.lit_value(w, k)
            add(Term(('lit', w, k), w, tuple(v for _ in envs), 0,
                     frozenset()))

    for c in range(1, max_cost + 1):
        if count >= limits.max_terms:
            break
        # Casts of cost c-1 terms.
        for a in list(by_cost.get(c - 1, [])):
            for op in ir.CASTS:
                for w in widths:
                    if (op == 'G_TRUNC') != (w < a.w) or w == a.w:
                        continue
                    fp = tuple(_apply(op, w, a.w, va, None) for va in a.fp)
                    add(Term((op, w, a.expr), w, fp, c, a.vars))
        for op in ir.BINOPS:
            oc = ir.OP_COST[op]
            for ca in range(0, c - oc + 1):
                cb = c - oc - ca
                for ia, a in enumerate(list(by_cost.get(ca, []))):
                    for ib, b in enumerate(list(by_cost.get(cb, []))):
                        if a.vars & b.vars:
                            continue  # keep terms linear
                        if op not in ir.SHIFTS and a.w != b.w:
                            continue
                        # Literal shift amounts use the value type.
                        if ir.is_lit(b.expr) and b.w != a.w:
                            continue
                        # (b op a) has the same fingerprint as (a op b).
                        if op in ir.COMMUTATIVE and ca == cb and ia > ib:
                            continue
                        fp = tuple(_apply(op, a.w, 0, va, vb)
                                   for va, vb in zip(a.fp, b.fp))
                        add(Term((op, a.w, a.expr, b.expr), a.w, fp, c,
                                 a.vars | b.vars))
                        if count >= limits.max_terms:
                            break
    return by_cost


def _agrees(src_fp, t_fp):
    for s, t in zip(src_fp, t_fp):
        if s is not None and (t is None or t != s):
            return False
    return True


def prove_concrete(inst, tgt, backend):
    """SMT: tgt refines inst.expr for every input consistent with the
    instance's *concrete* facts. Returns a smt.Result."""
    enc = smt.Encoder(inst.vw)
    eqs = []
    for i, (z, o) in enumerate(inst.facts):
        w = inst.vw[i]
        eqs += [enc.kz[i] == z3.BitVecVal(z, w),
                enc.ko[i] == z3.BitVecVal(o, w)]
    guard = z3.And(eqs) if eqs else z3.BoolVal(True)
    f = smt.refinement_violation(enc, inst.expr, tgt, guard)
    return backend.check(f, want_model_of=enc.x)


def discover(inst, backend, limits):
    """Returns (candidates, stats). Each candidate is a dict with the
    replacement expression and its concrete proof result."""
    src_cost = ir.cost(inst.expr)
    stats = {'terms': 0, 'fingerprint_matches': 0, 'smt_refuted': 0,
             'smt_unknown': 0}
    if src_cost == 0:
        return [], stats
    max_cost = src_cost - 1
    if src_cost <= limits.equal_cost_max:
        max_cost = src_cost
    rng = random.Random('%d:%s:%s' % (limits.seed, ir.to_sexpr(inst.expr),
                                      inst.facts))
    envs = sample_envs(inst, limits.samples, rng)
    src_fp = tuple(ir.evaluate(inst.expr, inst.vw, env) for env in envs)
    if all(v is None for v in src_fp):
        return [], stats  # always poison on the samples: nothing to learn
    root_w = inst.expr[1]
    src_variants = set(ir.commuted_variants(inst.expr))
    # A replacement equal to a subtree of the source is realized by the
    # smaller pattern that treats that subtree as a leaf, so skip it here.
    for sub in ir.interior_nodes(inst.expr):
        src_variants.update(ir.commuted_variants(sub))
    matches = []

    def on_term(t):
        if (t.w == root_w and t.expr not in src_variants and
                _agrees(src_fp, t.fp)):
            matches.append(t)

    by_cost = enumerate_terms(inst, envs, max_cost, limits, on_term)
    stats['terms'] = sum(len(v) for v in by_cost.values())
    out = []
    for t in sorted(matches, key=lambda t: (t.cost, ir.to_sexpr(t.expr))):
        stats['fingerprint_matches'] += 1
        if stats['fingerprint_matches'] > limits.max_proofs:
            break
        r = prove_concrete(inst, t.expr, backend)
        if r.status == 'sat':
            stats['smt_refuted'] += 1
            continue
        if r.status != 'unsat':
            stats['smt_unknown'] += 1
            continue
        out.append({'tgt': t.expr, 'cost': t.cost, 'proof': r})
        if len(out) >= limits.max_candidates:
            break
    return out, stats
