"""Candidate discovery by bounded enumerative synthesis.

For a concrete corpus instance S (an expression plus concrete known bits of
its inputs) the search considers every *linear* expression over S's inputs
and the literals 0 / 1 / -1 up to a cost bound below cost(S). A term whose
values agree with S on sample inputs becomes a *candidate*, and a candidate
is only reported as a concrete discovery after an SMT proof that it refines S
for every input consistent with the instance's facts. Sampling is only a
filter. There is no table of rewrite rules anywhere in the search.

The enumeration is split in two so that most of it is shared:

* A ``Bank`` holds the terms of one *signature* (the width class of every
  variable plus the number of width classes). It is built once, bottom-up by
  cost, and pruned by observational equivalence on unconstrained samples (as
  in Ruler / enumerative superoptimizers): of two terms that agree on every
  sample only the first, cheapest one is kept. Because the samples are
  unconstrained, a pruned term is equivalent to its representative under any
  known-bits facts, so the bank does not depend on the facts and is reused by
  every instance with the same signature, whatever its shape or its concrete
  bit widths. Terms are stored with width classes, not widths.
* Per instance the bank is only *evaluated* on samples that respect the
  instance's known bits, and compared with S. Evaluation is vectorized over
  all terms of a (operation, width) segment.

Refuting SMT models are kept and used as additional samples, for the rest of
the instance and for later instances with compatible facts. A candidate that
an already proved, no more expensive candidate refines on the samples is
dropped without a solver call.
"""

import random
import time

import numpy as np
import z3

from . import ir
from . import smt

U64 = np.uint64

# Canonical widths a bank is built at, by number of width classes. A bank is
# evaluated at the instance's own widths; the canonical widths only decide
# which terms are observationally distinct, so they are the widest ones.
CANON_WIDTHS = {1: (64,), 2: (32, 64), 3: (16, 32, 64), 4: (8, 16, 32, 64)}


class Limits:
    def __init__(self, samples=48, max_terms=50000, max_candidates=6,
                 equal_cost_max=1, max_proofs=48, seed=0, bank_samples=64,
                 max_cex_samples=16):
        self.samples = samples
        self.max_terms = max_terms          # per bank
        self.max_candidates = max_candidates  # proved candidates per instance
        self.max_proofs = max_proofs  # concrete SMT checks per instance
        # Also search replacements of *equal* cost when cost(S) <= this
        # (canonicalization candidates such as add -> or).
        self.equal_cost_max = equal_cost_max
        self.seed = seed
        self.bank_samples = bank_samples
        self.max_cex_samples = max_cex_samples


def _special(w):
    m = ir.mask(w)
    return [0, 1, 2, 3, m, m >> 1, (m >> 1) + 1, 0x55555555 & m,
            0xaaaaaaaa & m, w - 1 if w > 1 else 0, w // 2]


def _draw(w, rng):
    """One sample value. The kind is drawn per value, so the kinds of
    different variables are independent: a shift needs a small amount next
    to an arbitrary value."""
    kind = rng.random()
    if kind < 0.4:
        return rng.getrandbits(w)
    if kind < 0.75:
        return rng.randrange(0, 2 * w + 2) & ir.mask(w)
    sp = _special(w)
    return sp[rng.randrange(len(sp))]


def sample_envs(inst, n, rng):
    envs = []
    for _ in range(n):
        env = []
        for i, w in enumerate(inst.vw):
            z, o = inst.facts[i]
            if inst.consts[i] is not None:
                env.append(inst.consts[i])
                continue
            env.append(((_draw(w, rng) & ~z) | o) & ir.mask(w))
        envs.append(tuple(env))
    return envs


def consistent(env, inst):
    """True if the input assignment respects the instance's facts."""
    for v, (z, o), c in zip(env, inst.facts, inst.consts):
        if v & z or (v & o) != o or (c is not None and v != c):
            return False
    return True


# ------------------------------------------------------- vector kernel ---

def _m(w):
    return U64(ir.mask(w))


def kernel(op, w, wa, va, vb):
    """Vectorized generic MIR semantics on uint64 arrays (widths <= 64).
    Returns (values, poison) where poison is None or a bool array."""
    m = _m(w)
    if op == 'G_TRUNC':
        return va & m, None
    if op == 'G_ZEXT':
        return va, None
    if op == 'G_SEXT':
        sign = (va >> U64(wa - 1)) & U64(1)
        return va | (sign * (m ^ _m(wa))), None
    if op == 'G_ADD':
        return (va + vb) & m, None
    if op == 'G_SUB':
        return (va - vb) & m, None
    if op == 'G_MUL':
        return (va * vb) & m, None
    if op == 'G_AND':
        return va & vb, None
    if op == 'G_OR':
        return va | vb, None
    if op == 'G_XOR':
        return va ^ vb, None
    bad = vb >= U64(w)
    amt = np.where(bad, U64(0), vb)
    if op == 'G_SHL':
        return (va << amt) & m, bad
    if op == 'G_LSHR':
        return va >> amt, bad
    sign = (va >> U64(w - 1)) & U64(1)
    return (va >> amt) | (sign * (m ^ (m >> amt))), bad


class Bank:
    """Terms of one signature, stored structurally with width classes."""

    CHUNK = 1 << 17

    def __init__(self, var_cls, ncls, limits):
        self.var_cls = tuple(var_cls)
        self.ncls = ncls
        self.limits = limits
        self.cw = CANON_WIDTHS[ncls]
        rng = random.Random('bank:%d:%r:%d' % (limits.seed, self.var_cls,
                                               ncls))
        n = limits.bank_samples
        self.op = []      # 'var' | 'lit' | G_*
        self.arg = []     # variable index / literal key / None
        self.cls = []     # width class of the value
        self.cost = []
        self.vars = []    # bit set of the variables used
        self.a = []       # operand term indices (-1 if none)
        self.b = []
        self.segs = []    # (op, cls, cls_a, cost, start, end)
        self.cost_end = []  # cost_end[c] = number of terms of cost <= c
        self.truncated = False
        self._expr = {}
        self._seen = set()
        self._r1 = np.array([rng.getrandbits(64) | 1 for _ in range(n)], U64)
        self._r2 = np.array([rng.getrandbits(64) | 1 for _ in range(n)], U64)
        self._V = np.zeros((256, n), U64)
        self._OK = np.ones((256, n), bool)
        for i, c in enumerate(self.var_cls):
            w = self.cw[c]
            vals = np.array([_draw(w, rng) for _ in range(n)], U64)
            self._leaf('var', i, c, 1 << i, vals)
        for c in range(ncls):
            for k in ir.LITERALS:
                v = ir.lit_value(self.cw[c], k)
                self._leaf('lit', k, c, 0, np.full(n, v, U64))
        self.n_leaves = len(self.op)
        self.cost_end.append(len(self.op))
        self._arrays()

    # -- construction --

    def _grow(self, n):
        cap = self._V.shape[0]
        if n <= cap:
            return
        while cap < n:
            cap *= 2
        for name in ('_V', '_OK'):
            old = getattr(self, name)
            new = np.ones((cap, old.shape[1]), old.dtype)
            new[:old.shape[0]] = old
            setattr(self, name, new)

    def _key(self, cls, vals, ok):
        vz = np.where(ok, vals, U64(0))
        h = (vz * self._r1).sum(axis=1, dtype=U64)
        h ^= (ok.astype(U64) * self._r2).sum(axis=1, dtype=U64)
        return h * U64(0x9e3779b97f4a7c15) + U64(cls + 1)

    def _leaf(self, op, arg, cls, vars_, vals):
        i = len(self.op)
        self._grow(i + 1)
        self._V[i] = vals
        self._OK[i] = True
        key = int(self._key(cls, vals[None, :], self._OK[i][None, :])[0])
        self._seen.add(key)   # leaves are never dropped
        self.op.append(op)
        self.arg.append(arg)
        self.cls.append(cls)
        self.cost.append(0)
        self.vars.append(vars_)
        self.a.append(-1)
        self.b.append(-1)

    def _arrays(self):
        self.cls_np = np.array(self.cls, np.int16)
        self.cost_np = np.array(self.cost, np.int16)
        self.vars_np = np.array(self.vars, np.int64)
        self.lit_np = np.array([o == 'lit' for o in self.op], bool)
        self.a_np = np.array(self.a, np.int64)
        self.b_np = np.array(self.b, np.int64)

    def _add_segment(self, op, cls, cls_a, cost, ai, bi):
        """Evaluates candidate terms on the bank samples, drops duplicates
        and appends the rest as one segment. ``bi`` is None for casts."""
        room = self.limits.max_terms - len(self.op)
        if room <= 0:
            self.truncated = True
            return
        w, wa = self.cw[cls], self.cw[cls_a]
        va = self._V[ai]
        ok = self._OK[ai]
        if bi is None:
            vals, bad = kernel(op, w, wa, va, None)
        else:
            vals, bad = kernel(op, w, wa, va, self._V[bi])
            ok = ok & self._OK[bi]
        if bad is not None:
            ok = ok & ~bad
        keep = ok.any(axis=1)   # a term that is always poison is useless
        key = self._key(cls, vals, ok)
        _, first = np.unique(key, return_index=True)
        first.sort()
        chosen = []
        for j, k in zip(first.tolist(), key[first].tolist()):
            if keep[j] and k not in self._seen:
                self._seen.add(k)
                chosen.append(j)
                if len(chosen) >= room:
                    self.truncated = True
                    break
        if not chosen:
            return
        start = len(self.op)
        end = start + len(chosen)
        self._grow(end)
        self._V[start:end] = vals[chosen]
        self._OK[start:end] = ok[chosen]
        al = ai[chosen].tolist()
        bl = bi[chosen].tolist() if bi is not None else [-1] * len(chosen)
        for x, y in zip(al, bl):
            self.op.append(op)
            self.arg.append(None)
            self.cls.append(cls)
            self.cost.append(cost)
            self.vars.append(self.vars[x] | (self.vars[y] if y >= 0 else 0))
            self.a.append(x)
            self.b.append(y)
        self.segs.append((op, cls, cls_a, cost, start, end))

    def _level(self, c):
        return np.arange(self.cost_end[c - 1] if c else 0, self.cost_end[c])

    def ensure(self, max_cost):
        """Extends the bank to all terms of cost <= max_cost."""
        while len(self.cost_end) <= max_cost:
            self._extend(len(self.cost_end))
            self.cost_end.append(len(self.op))
            self._arrays()

    def _extend(self, c):
        if self.truncated:
            return
        prev = self._level(c - 1)
        for op in ir.CASTS:
            for k in range(self.ncls):
                for ka in range(self.ncls):
                    if ka == k or (op == 'G_TRUNC') != (k < ka):
                        continue
                    ai = prev[(self.cls_np[prev] == ka) &
                              ~self.lit_np[prev]]
                    if len(ai):
                        self._add_segment(op, k, ka, c, ai, None)
        for op in ir.BINOPS:
            oc = ir.OP_COST[op]
            comm = op in ir.COMMUTATIVE
            shift = op in ir.SHIFTS
            for ca in range(0, c - oc + 1):
                cb = c - oc - ca
                # (b op a) is the same term as (a op b).
                if comm and ca > cb:
                    continue
                la, lb = self._level(ca), self._level(cb)
                for ka in range(self.ncls):
                    A = la[self.cls_np[la] == ka]
                    if not len(A):
                        continue
                    for kb in range(self.ncls):
                        if not shift and kb != ka:
                            continue
                        B = lb[self.cls_np[lb] == kb]
                        if kb != ka:
                            # Literal shift amounts use the value type.
                            B = B[~self.lit_np[B]]
                        if not len(B):
                            continue
                        step = max(1, self.CHUNK // len(B))
                        for s in range(0, len(A), step):
                            ai = np.repeat(A[s:s + step], len(B))
                            bi = np.tile(B, len(A[s:s + step]))
                            va, vb = self.vars_np[ai], self.vars_np[bi]
                            # Linear terms only; an operation on literals
                            # alone is a constant, which costs nothing and
                            # is not in the grammar.
                            sel = ((va & vb) == 0) & ((va | vb) != 0)
                            if comm and ca == cb:
                                sel &= ai < bi
                            if sel.any():
                                self._add_segment(op, ka, ka, c, ai[sel],
                                                  bi[sel])
                            if self.truncated:
                                return

    # -- use --

    def size(self, max_cost):
        return self.cost_end[min(max_cost, len(self.cost_end) - 1)]

    def evaluate(self, widths, env_cols, max_cost):
        """Values of every term of cost <= max_cost for the samples
        ``env_cols`` (one uint64 array per variable), at the instance's
        ``widths`` (indexed by width class). Returns (V, OK)."""
        n = self.size(max_cost)
        ns = len(env_cols[0]) if env_cols else 1
        V = np.zeros((n, ns), U64)
        OK = np.ones((n, ns), bool)
        for i in range(self.n_leaves):
            if self.op[i] == 'var':
                V[i] = env_cols[self.arg[i]]
            else:
                V[i] = U64(ir.lit_value(widths[self.cls[i]], self.arg[i]))
        for op, cls, cls_a, cost, s, e in self.segs:
            if cost > max_cost:
                break
            ai = self.a_np[s:e]
            va = V[ai]
            ok = OK[ai]
            if op in ir.CASTS:
                vals, bad = kernel(op, widths[cls], widths[cls_a], va, None)
            else:
                bi = self.b_np[s:e]
                vals, bad = kernel(op, widths[cls], widths[cls_a], va,
                                   V[bi])
                ok = ok & OK[bi]
            if bad is not None:
                ok = ok & ~bad
            V[s:e] = vals
            OK[s:e] = ok
        return V, OK

    def expr(self, i, widths):
        """The term as an ir expression at the given widths."""
        key = (i, widths)
        e = self._expr.get(key)
        if e is None:
            op = self.op[i]
            if op == 'var':
                e = ('var', self.arg[i])
            elif op == 'lit':
                e = ('lit', widths[self.cls[i]], self.arg[i])
            elif self.b[i] < 0:
                e = (op, widths[self.cls[i]], self.expr(self.a[i], widths))
            else:
                e = (op, widths[self.cls[i]], self.expr(self.a[i], widths),
                     self.expr(self.b[i], widths))
            self._expr[key] = e
        return e


class Context:
    """State shared by all instances of one synthesis run: the term banks,
    the counterexample pool and the timers."""

    def __init__(self, limits=None):
        self.limits = limits or Limits()
        self.banks = {}
        self.cex = {}     # variable widths -> [input assignment]
        self.seconds = {'bank_build': 0.0, 'bank_eval': 0.0, 'smt': 0.0}
        self.bank_hits = 0

    def bank(self, var_cls, ncls, max_cost):
        key = (tuple(var_cls), ncls)
        b = self.banks.get(key)
        if b is None:
            b = self.banks[key] = Bank(var_cls, ncls, self.limits)
        else:
            self.bank_hits += 1
        if len(b.cost_end) <= max_cost:
            t0 = time.monotonic()
            b.ensure(max_cost)
            self.seconds['bank_build'] += time.monotonic() - t0
        return b

    def add_cex(self, vw, env):
        pool = self.cex.setdefault(tuple(vw), [])
        if env not in pool:
            pool.append(env)

    def stats(self):
        return {'banks': len(self.banks), 'bank_reuses': self.bank_hits,
                'bank_terms': sum(len(b.op) for b in self.banks.values()),
                'banks_truncated': sum(b.truncated
                                       for b in self.banks.values()),
                'counterexample_pool': sum(len(v)
                                           for v in self.cex.values()),
                'seconds': {k: round(v, 2)
                            for k, v in self.seconds.items()}}


def signature(inst):
    """(width classes of the variables, widths by class) or None if the
    instance has more width classes than a bank supports."""
    widths = sorted(set(inst.vw) |
                    {e[1] for e in [inst.expr] + ir.interior_nodes(inst.expr)})
    if len(widths) not in CANON_WIDTHS or max(widths) > 64:
        return None
    cls = {w: i for i, w in enumerate(widths)}
    return tuple(cls[w] for w in inst.vw), tuple(widths)


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


def refines_on(inst, tgt, env):
    """Concrete refinement check of one input assignment."""
    s = ir.evaluate(inst.expr, inst.vw, env)
    return s is None or ir.evaluate(tgt, inst.vw, env) == s


def instance_envs(inst, limits, ctx):
    rng = random.Random('%d:%s:%s' % (limits.seed, ir.to_sexpr(inst.expr),
                                      inst.facts))
    envs = sample_envs(inst, limits.samples, rng)
    extra = [e for e in ctx.cex.get(inst.vw, []) if consistent(e, inst)]
    return envs + extra[-limits.max_cex_samples:]


def max_search_cost(inst, limits):
    src_cost = ir.cost(inst.expr)
    if src_cost <= limits.equal_cost_max:
        return src_cost
    return src_cost - 1


def prove_candidates(inst, cands, backend, limits, ctx, stats, envs=None):
    """Proves candidate replacements (cheapest first) under the instance's
    concrete facts. A refuting model becomes a sample: it filters the
    remaining candidates and is kept for later instances."""
    out = []
    cex = []
    envs = envs or []
    vals = {}

    def values(e):
        if e not in vals:
            vals[e] = [ir.evaluate(e, inst.vw, env) for env in envs]
        return vals[e]

    def dominated(tgt):
        # A proved candidate that is no more expensive and refines this one
        # on the samples makes it pointless (x for x & 1, 0 for 0 << x).
        # Two candidates that are equal on the samples are both kept.
        tv = values(tgt)
        for c in out:
            cv = values(c['tgt'])
            if cv != tv and all(t is None or t == v
                                for t, v in zip(tv, cv)):
                return True
            if cv == tv and c['cost'] < ir.cost(tgt):
                return True
        return False

    for tgt in cands:
        if any(not refines_on(inst, tgt, e) for e in cex):
            stats['cex_filtered'] += 1
            continue
        if envs and dominated(tgt):
            stats['dominated'] += 1
            continue
        if stats['smt_checks'] >= limits.max_proofs:
            break
        stats['smt_checks'] += 1
        t0 = time.monotonic()
        r = prove_concrete(inst, tgt, backend)
        ctx.seconds['smt'] += time.monotonic() - t0
        if r.status == 'sat':
            stats['smt_refuted'] += 1
            env = tuple(r.model)
            cex.append(env)
            ctx.add_cex(inst.vw, env)
            continue
        if r.status != 'unsat':
            stats['smt_unknown'] += 1
            continue
        out.append({'tgt': tgt, 'cost': ir.cost(tgt), 'proof': r})
        if len(out) >= limits.max_candidates:
            break
    return out


def literal_spellings(inst):
    """The source with constant inputs that equal a grammar literal
    replaced by that literal (each one alone, and all of them)."""
    subs = {}
    for i, c in enumerate(inst.consts):
        if c is None:
            continue
        for k in ir.LITERALS:
            if ir.lit_value(inst.vw[i], k) == c:
                subs[i] = ('lit', inst.vw[i], k)
                break

    def subst(e, which):
        if ir.is_var(e):
            return subs[e[1]] if e[1] in which else e
        if ir.is_lit(e):
            return e
        return e[:2] + tuple(subst(a, which) for a in e[2:])
    out = [subst(inst.expr, {i}) for i in subs]
    if len(subs) > 1:
        out.append(subst(inst.expr, set(subs)))
    return out


def new_stats():
    return {'terms': 0, 'fingerprint_matches': 0, 'smt_checks': 0,
            'smt_refuted': 0, 'smt_unknown': 0, 'cex_filtered': 0,
            'dominated': 0}


def discover(inst, backend, limits=None, ctx=None):
    """Returns (candidates, stats). Each candidate is a dict with the
    replacement expression and its concrete proof result."""
    ctx = ctx or Context(limits)
    limits = limits or ctx.limits
    stats = new_stats()
    if ir.cost(inst.expr) == 0:
        return [], stats
    sig = signature(inst)
    if sig is None:
        return [], stats
    var_cls, widths = sig
    max_cost = max_search_cost(inst, limits)
    envs = instance_envs(inst, limits, ctx)
    src = [ir.evaluate(inst.expr, inst.vw, env) for env in envs]
    if all(v is None for v in src):
        return [], stats  # always poison on the samples: nothing to learn
    bank = ctx.bank(var_cls, len(widths), max_cost)
    t0 = time.monotonic()
    cols = [np.array([env[i] for env in envs], U64)
            for i in range(len(inst.vw))]
    V, OK = bank.evaluate(widths, cols, max_cost)
    n = V.shape[0]
    stats['terms'] = n
    src_ok = np.array([v is not None for v in src], bool)
    src_val = np.array([v or 0 for v in src], U64)
    root_cls = widths.index(inst.expr[1])
    rows = np.nonzero(bank.cls_np[:n] == root_cls)[0]
    agree = (((V[rows] == src_val) & OK[rows]) | ~src_ok).all(axis=1)
    ctx.seconds['bank_eval'] += time.monotonic() - t0

    src_variants = set(ir.commuted_variants(inst.expr))
    # A replacement equal to a subtree of the source is realized by the
    # smaller pattern that treats that subtree as a leaf, so skip it here.
    for sub in ir.interior_nodes(inst.expr):
        src_variants.update(ir.commuted_variants(sub))
    # Neither is the source with a constant input spelled as a literal.
    for e in literal_spellings(inst):
        src_variants.update(ir.commuted_variants(e))
    cands = []
    for i in rows[agree].tolist():
        e = bank.expr(i, widths)
        if e not in src_variants:
            cands.append((bank.cost[i], ir.to_sexpr(e), e))
    cands.sort()
    stats['fingerprint_matches'] = len(cands)
    out = prove_candidates(inst, [e for _, _, e in cands], backend, limits,
                           ctx, stats, envs)
    return out, stats
