"""SMT encoding and solver interface.

Only the offline synthesizer uses this module; nothing in LLVM links a solver.

The solver is behind ``Backend`` so another QF_BV solver (e.g. Bitwuzla) can
be added by implementing ``check``. Formulas are built with the z3 Python API
and also serialized as SMT-LIB2 for the proof records, so a proof can be
re-checked with any SMT-LIB2 solver.
"""

import time

import z3

from . import ir


class Result:
    def __init__(self, status, model=None, smt2=None, seconds=0.0):
        self.status = status   # 'unsat' | 'sat' | 'unknown'
        self.model = model     # counterexample assignment if 'sat'
        self.smt2 = smt2
        self.seconds = seconds


class Z3Backend:
    name = 'z3'

    def __init__(self, timeout_ms=10000):
        self.timeout_ms = timeout_ms
        self.calls = 0
        self.seconds = 0.0

    @property
    def version(self):
        return z3.get_version_string()

    def check(self, formula, want_model_of=None):
        """Checks satisfiability of ``formula``. ``want_model_of`` is a list
        of z3 bitvector terms whose values are returned for 'sat'.

        The formula is copied into a fresh z3 context first. Term numbering
        in the shared context depends on everything built before, and it
        shows in the SMT-LIB text and in the models the solver picks; in a
        fresh context both depend on the formula alone, so a run is
        reproducible."""
        ctx = z3.Context()
        s = z3.SolverFor('QF_BV', ctx=ctx)
        s.set('timeout', self.timeout_ms)
        s.add(formula.translate(ctx))
        t0 = time.monotonic()
        r = s.check()
        dt = time.monotonic() - t0
        self.calls += 1
        self.seconds += dt
        smt2 = s.to_smt2()
        if r == z3.unsat:
            return Result('unsat', smt2=smt2, seconds=dt)
        if r == z3.sat:
            m = s.model()
            vals = None
            if want_model_of is not None:
                vals = [m.eval(t.translate(ctx),
                               model_completion=True).as_long()
                        for t in want_model_of]
            return Result('sat', model=vals, smt2=smt2, seconds=dt)
        return Result('unknown', smt2=smt2, seconds=dt)


class Encoder:
    """Symbolic inputs for one width schedule: a value x_i and known-bits
    masks KZ_i / KO_i per pattern variable."""

    def __init__(self, vw, rw=None):
        self.vw = tuple(vw)
        self.rw = rw  # source root width, for 'r' operands of atoms
        self.x = [z3.BitVec('x%d' % i, w) for i, w in enumerate(vw)]
        self.kz = [z3.BitVec('kz%d' % i, w) for i, w in enumerate(vw)]
        self.ko = [z3.BitVec('ko%d' % i, w) for i, w in enumerate(vw)]

    def fact_consistency(self):
        """KZ and KO never claim the same bit."""
        return z3.And([(z & o) == 0 for z, o in zip(self.kz, self.ko)] or
                      [z3.BoolVal(True)])

    def well_formed(self):
        """Soundness of the facts for the (non-poison) values: every bit in
        KZ is 0 in x and every bit in KO is 1 in x. This is exactly the
        KnownBits contract GISelValueTracking guarantees."""
        cs = [self.fact_consistency()]
        for x, z, o in zip(self.x, self.kz, self.ko):
            cs += [(x & z) == 0, (x & o) == o]
        return z3.And(cs)

    def enc(self, e):
        """Returns (value, poison) z3 terms for expression ``e``."""
        if ir.is_var(e):
            return self.x[e[1]], z3.BoolVal(False)
        if ir.is_lit(e):
            return z3.BitVecVal(ir.lit_value(e[1], e[2]), e[1]), \
                z3.BoolVal(False)
        op, w = e[0], e[1]
        args = [self.enc(a) for a in e[2:]]
        poison = z3.Or([p for _, p in args])
        if op in ir.CASTS:
            v = args[0][0]
            sw = ir.width(e[2], self.vw)
            if op == 'G_TRUNC':
                return z3.Extract(w - 1, 0, v), poison
            if op == 'G_ZEXT':
                return z3.ZeroExt(w - sw, v), poison
            return z3.SignExt(w - sw, v), poison
        (a, _), (b, _) = args
        if op in ir.SHIFTS:
            aw = ir.width(e[3], self.vw)
            # amount >= width is poison (generic MIR / LLVM semantics).
            oob = z3.UGE(b, z3.BitVecVal(w, aw)) if w < (1 << aw) else \
                z3.BoolVal(False)
            poison = z3.Or(poison, oob)
            if aw < w:
                b = z3.ZeroExt(w - aw, b)
            elif aw > w:
                b = z3.Extract(w - 1, 0, b)
            fn = {'G_SHL': lambda: a << b, 'G_LSHR': lambda: z3.LShR(a, b),
                  'G_ASHR': lambda: a >> b}[op]
            return fn(), poison
        fn = {'G_ADD': lambda: a + b, 'G_SUB': lambda: a - b,
              'G_MUL': lambda: a * b, 'G_AND': lambda: a & b,
              'G_OR': lambda: a | b, 'G_XOR': lambda: a ^ b}[op]
        return fn(), poison

    def model_terms(self):
        return self.x + self.kz + self.ko


def refinement_violation(enc, src, tgt, guard):
    """Formula satisfiable iff some input satisfying the facts and the guard
    makes the source non-poison while the target is poison or different."""
    sv, sp = enc.enc(src)
    tv, tp = enc.enc(tgt)
    return z3.And(enc.well_formed(), guard, z3.Not(sp), z3.Or(tp, sv != tv))


def split_model(vals, n):
    return vals[:n], vals[n:2 * n], vals[2 * n:]
