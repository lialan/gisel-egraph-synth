"""SMT encoding and solver interface.

Only the offline synthesizer uses this module; nothing in LLVM links a solver.

The solver is behind ``Backend`` so another QF_BV solver (e.g. Bitwuzla) can
be added by implementing ``check``. Formulas are built with the z3 Python API
and also serialized as SMT-LIB2 for the proof records, so a proof can be
re-checked with any SMT-LIB2 solver.
"""

import time

import z3

from . import fp
from . import ir
from . import ops


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
        # The conversions between integers and floating-point values need
        # the floating-point theory.
        logic = 'QF_BVFP' if fp.uses_theory(formula) else 'QF_BV'
        s = z3.SolverFor(logic, ctx=ctx)
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
    """Symbolic inputs for one width schedule: a value x_i, a poison flag
    xp_i and known-bits masks KZ_i / KO_i per pattern variable.

    ``const_vars`` are the variables that the rule only matches as
    constants: their known bits are exact, and they are not poison.

    A G_FREEZE term has the value of its operand, or a value of its own
    (``frozen``) if the operand is poison. The terms of the source and of
    the replacement have different values: a G_FREEZE of the replacement is
    a new instruction. One term must not occur twice in the source (see
    ir.repeated_freeze)."""

    def __init__(self, vw, rw=None, const_vars=()):
        self.vw = tuple(vw)
        self.nreal = len(vw)
        self.rw = rw  # source root width, for 'r' operands of atoms
        self.const_vars = tuple(const_vars)
        self.x = [z3.BitVec('x%d' % i, w) for i, w in enumerate(vw)]
        self.kz = [z3.BitVec('kz%d' % i, w) for i, w in enumerate(vw)]
        self.ko = [z3.BitVec('ko%d' % i, w) for i, w in enumerate(vw)]
        self.xp = [z3.Bool('xp%d' % i) for i in range(len(vw))]
        self.frozen = {}   # (side, term) -> value for a poison operand

    def recipe_guard(self, tgt):
        """The condition on the computed constants of the replacement
        ``tgt`` that the generated guard checks before the rule applies:
        each computed constant is defined, and a computed shift amount is
        smaller than the width of its shift."""
        cs = []
        for c in ir.computed_constants(tgt, self.const_vars):
            _, p, ub = self.enc_full(c)
            cs.append(z3.Not(z3.Or(p, ub)))
        for w, c in ir.computed_amounts(tgt, self.const_vars):
            cs.append(z3.Not(ops._oob(self.enc_full(c)[0], w)))
        return z3.And(cs) if cs else z3.BoolVal(True)

    def fact_consistency(self):
        """KZ and KO never claim the same bit, and the known bits of a
        constant are exact."""
        cs = [(self.kz[i] & self.ko[i]) == 0 for i in range(self.nreal)]
        for i in self.const_vars:
            cs.append(self.kz[i] == ~self.ko[i])
            cs.append(z3.Not(self.xp[i]))
        return z3.And(cs or [z3.BoolVal(True)])

    def well_formed(self):
        """Soundness of the facts for the (non-poison) values: every bit in
        KZ is 0 in x and every bit in KO is 1 in x. This is exactly the
        KnownBits contract GISelValueTracking guarantees."""
        cs = [self.fact_consistency()]
        for i in range(self.nreal):
            x, z, o = self.x[i], self.kz[i], self.ko[i]
            cs += [(x & z) == 0, (x & o) == o]
        return z3.And(cs)

    def enc(self, e):
        """Returns (value, poison) z3 terms for expression ``e``; for an
        expression without operations that can have undefined behaviour."""
        v, p, _ = self.enc_full(e)
        return v, p

    def enc_full(self, e, memo=None, side='src'):
        """Returns (value, poison, ub) z3 terms for expression ``e``. ``ub``
        is true if any operation of ``e`` has undefined behaviour: every
        instruction of a pattern executes, whatever uses its result.
        ``side`` says which G_FREEZE instructions ``e`` has: those of the
        source ('src') or those of the replacement ('tgt')."""
        if memo is None:
            memo = {}
        if e in memo:
            return memo[e]
        false = z3.BoolVal(False)
        if ir.is_var(e):
            r = self.x[e[1]], self.xp[e[1]], false
        elif not ir.is_op(e):
            r = z3.BitVecVal(ir.leaf_value(e), e[1]), false, false
        else:
            info, attr, res = ops.parse(e[0])
            args = [self.enc_full(a, memo, side) for a in e[2:]]
            ws = [ir.width(a, self.vw) for a in e[2:]]
            v, p, ub = info.smt(e[1], ws, attr, res, [a[0] for a in args])
            ubs = [a[2] for a in args] + ([ub] if ub is not None else [])
            if info.freeze:
                if (side, e) not in self.frozen:
                    self.frozen[side, e] = z3.BitVec(
                        'fr%d' % len(self.frozen), e[1])
                v = z3.If(args[0][1], self.frozen[side, e], v)
                ps = []
            elif info.strict:
                ps = [a[1] for a in args]
            else:
                # G_SELECT: the condition and the selected arm.
                ps = [args[0][1], z3.If(args[0][0] == 1, args[1][1],
                                        args[2][1])]
            if p is not None:
                ps.append(p)
            r = v, z3.Or(ps) if ps else false, z3.Or(ubs)
        memo[e] = r
        return r

    def model_terms(self):
        n = self.nreal
        one, zero = z3.BitVecVal(1, 1), z3.BitVecVal(0, 1)
        return self.x[:n] + self.kz[:n] + self.ko[:n] + \
            [z3.If(p, one, zero) for p in self.xp[:n]]


def _made_nan(enc, e):
    """The condition that the value of the source expression ``e`` is a NaN
    that a floating-point conversion made. The payload of such a NaN is not
    specified, so each NaN is a correct result of the replacement. A NaN of
    an input keeps its bits through G_SELECT and G_FREEZE: there the
    replacement must give the same bits."""
    if not ir.is_op(e) or not ops.known(e[0]):
        return z3.BoolVal(False)
    info = ops.parse(e[0])[0]
    if info.fp_result:
        return z3.fpIsNaN(fp.z3_value(enc.enc_full(e)[0]))
    if info.freeze:
        return _made_nan(enc, e[2])
    if info.shape == 'select':
        return z3.If(enc.enc_full(e[2])[0] == 1, _made_nan(enc, e[3]),
                     _made_nan(enc, e[4]))
    return z3.BoolVal(False)


def refinement_violation(enc, src, tgt, guard):
    """Formula satisfiable iff some input satisfying the facts and the guard
    gives the source defined behaviour, while the target has undefined
    behaviour, or the source is not poison and the target is poison or
    different."""
    assert not ir.repeated_freeze(src), 'one G_FREEZE term twice'
    sv, sp, su = enc.enc_full(src)
    tv, tp, tu = enc.enc_full(tgt, side='tgt')
    same = z3.Or(sv == tv, z3.And(_made_nan(enc, src),
                                  z3.fpIsNaN(fp.z3_value(tv)))) \
        if ir.result_kind(src) == 'f' else sv == tv
    return z3.And(enc.well_formed(), guard, enc.recipe_guard(tgt),
                  z3.Not(su),
                  z3.Or(tu, z3.And(z3.Not(sp), z3.Or(tp, z3.Not(same)))))


def split_model(vals, n):
    """(values, known zeros, known ones, poison flags) of a model."""
    return vals[:n], vals[n:2 * n], vals[2 * n:3 * n], vals[3 * n:]
