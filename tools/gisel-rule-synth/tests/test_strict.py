#!/usr/bin/env python3
"""Tests of the constrained floating-point operations (G_STRICT_*): the
value in each rounding mode, the exceptions, the kernels, the rules and
the floating-point environment of a tree.

Run:  python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests
"""

import importlib.util
import json
import os
import random
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import numpy as np  # noqa: E402
import z3  # noqa: E402

from girs import corpus, discover, emit, fp, ir, kernels  # noqa: E402
from girs import ops, precond, smt, synth, targets  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    'gi_rule_synth_cli', os.path.join(ROOT, 'gi-rule-synth.py'))
cli = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cli)

LLC = os.environ.get('GIRS_LLC') or os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(ROOT))), 'build', 'bin',
    'llc')
HAVE_LLC = os.path.exists(LLC)
F = fp.Fraction
W = 32
ENV = fp.ENV_BITS


def V(i):
    return ('var', i)


def L(k, w=W):
    return ('lit', w, k)


def op(name, w, *args):
    return (name, w) + args


def fbits(x, w=W):
    """The bit pattern of the number x (a Fraction or an int)."""
    x = F(x)
    return fp.encode(int(x < 0), abs(x), w)


def instance(src, vw, consts=None, nofpe=False):
    """An instance of the corpus: a constant has its bits as facts, and
    the environment says if the program reads the exceptions."""
    consts = consts or [None] * len(vw)
    env = ir.env_vars(src)
    facts = [((0, fp.ENV_IGNORE, True) if nofpe else
              (fp.ENV_IGNORE, 0, True)) if i in env else
             (0, 0) if c is None else (~c & ops.mask(w), c, True)
             for i, (c, w) in enumerate(zip(consts, vw))]
    return corpus.Instance(src, tuple(vw), facts, consts,
                           [1] * len(ir.interior_nodes(src)), [],
                           [('f', 'fn', '%0')])


def rule_of(src, tgt, vw, consts=None, nofpe=False, cv=None):
    """The rule that the synthesizer makes of a candidate, or None."""
    s = synth.Synthesizer(smt.Z3Backend())
    inst = instance(src, vw, consts, nofpe)
    if cv is not None:
        inst.const_vars = cv
    if s.add(inst, tgt) is None:
        return None
    s.finalize([inst])
    (rule,) = s.rules.values()
    return rule


def cpp(rule):
    out = emit._cpp_guard(rule)
    if emit._rule_needs_cpp_apply(rule):
        out += emit._cpp_apply(rule)
    return out


def targets_of(inst, **limits):
    lim = discover.Limits(grammar='auto', **limits)
    cands, _ = discover.discover(inst, smt.Z3Backend(), lim,
                                 discover.Context(lim), {})
    return [c['tgt'] for c in cands]

E = V(2)
ONE, TWO, HALF = (fp.literal_bits(k, W) for k in ('f1', 'f2', 'f0.5'))
ALL_FLAGS = (fp.FE_INVALID | fp.FE_DIVBYZERO | fp.FE_OVERFLOW |
             fp.FE_UNDERFLOW_B | fp.FE_UNDERFLOW_A | fp.FE_INEXACT)


def float_values(w, rng, n):
    """Special values and numbers near the limits of the format."""
    eb, p = fp.FORMATS[w]
    bias = fp._bias(w)
    sp = [0, 1, 2, 3, fp.inf(w), fp.qnan(w), fp.inf(w) + 1, fp.inf(w) - 1,
          fp.inf(w) - 2, 1 << (p - 1), (1 << (p - 1)) - 1,
          (1 << (p - 1)) + 1]
    sp += [fp.literal_bits(k, w) for k in fp.LITERALS]
    for num, den in ((3, 2), (5, 2), (1, 3), (1 << (p - 1), 1),
                     ((1 << p) - 1, 2), ((1 << p) + 1, 2), ((1 << p) - 1, 1),
                     (3, 1 << p), (1, 1 << (p - 1)), (1, 1 << (p + 1))):
        sp.append(fp.encode(0, F(num, den), w))
    sp += [v ^ fp.sign_bit(w) for v in sp]
    for _ in range(n):
        e = rng.choice([0, 0, 1, 2, p, bias - p, bias - 1, bias, bias + 1,
                        bias + p - 1, bias + p, (1 << eb) - 2,
                        rng.randrange(1 << eb)])
        m = rng.choice([0, 1, (1 << (p - 1)) - 1, rng.getrandbits(p - 1),
                        rng.getrandbits(p - 1)])
        sp.append((rng.getrandbits(1) << (w - 1)) | (e << (p - 1)) | m)
    return sp


class StrictEvaluatorTest(unittest.TestCase):
    """fp.strict: the value in each rounding mode and the exceptions."""

    def test_environment(self):
        self.assertEqual([fp.rm_of(e) for e in range(8)],
                         [0, 1, 2, 3, 4, fp.RM_EVEN, fp.RM_EVEN,
                          fp.RM_EVEN])
        # The bit ENV_IGNORE does not change the mode.
        self.assertEqual(fp.rm_of(fp.ENV_IGNORE | fp.RM_UP), fp.RM_UP)
        # The numbers of llvm::RoundingMode.
        self.assertEqual((fp.RM_ZERO, fp.RM_EVEN, fp.RM_UP, fp.RM_DOWN,
                          fp.RM_AWAY), (0, 1, 2, 3, 4))

    def test_nearest_is_the_default_operation(self):
        rng = random.Random(4)
        for w in (16, 32):
            vs = float_values(w, rng, 40)
            for name, fn, k in (('add', fp.add, 2), ('sub', fp.sub, 2),
                                ('mul', fp.mul, 2), ('div', fp.div, 2),
                                ('rem', fp.rem, 2), ('fma', fp.fma, 3),
                                ('sqrt', fp.sqrt, 1)):
                for _ in range(300):
                    xs = tuple(rng.choice(vs) for _ in range(k))
                    got, flags = fp.strict(name, fp.RM_EVEN, xs, w)
                    self.assertTrue(fp.same_bits(got, fn(*xs, w), w),
                                    (name, w, xs))
                    self.assertEqual(flags & ~ALL_FLAGS, 0)

    def test_division_by_zero_and_invalid(self):
        for rm in range(5):
            self.assertEqual(fp.strict('div', rm, (ONE, 0), W),
                             (fp.inf(W), fp.FE_DIVBYZERO))
            self.assertEqual(fp.strict('div', rm, (0, 0), W),
                             (fp.qnan(W), fp.FE_INVALID))
            self.assertEqual(
                fp.strict('add', rm, (fp.inf(W), fp.inf(W, 1)), W),
                (fp.qnan(W), fp.FE_INVALID))
            self.assertEqual(fp.strict('mul', rm, (fp.inf(W), 0), W),
                             (fp.qnan(W), fp.FE_INVALID))
            self.assertEqual(fp.strict('sqrt', rm, (fbits(-1),), W),
                             (fp.qnan(W), fp.FE_INVALID))
            self.assertEqual(fp.strict('rem', rm, (ONE, 0), W),
                             (fp.qnan(W), fp.FE_INVALID))
            # An infinity is exact.
            self.assertEqual(fp.strict('add', rm, (fp.inf(W), ONE), W),
                             (fp.inf(W), 0))

    def test_nan_operands(self):
        snan = fp.inf(W) | 1
        self.assertTrue(fp.is_snan(snan, W))
        # A signaling NaN is invalid; a quiet NaN raises nothing.
        self.assertEqual(fp.strict('add', fp.RM_EVEN, (snan, ONE), W),
                         (fp.qnan(W), fp.FE_INVALID))
        self.assertEqual(fp.strict('mul', fp.RM_UP, (fp.qnan(W), ONE), W),
                         (fp.qnan(W), 0))
        self.assertEqual(fp.strict_nan_flags((fp.qnan(W), ONE), W), 0)
        self.assertEqual(fp.strict_nan_flags((snan, ONE), W), fp.FE_INVALID)
        # A signaling comparison: each NaN is invalid.
        self.assertEqual(
            fp.strict_nan_flags((fp.qnan(W), ONE), W, any_nan=True),
            fp.FE_INVALID)
        self.assertEqual(fp.strict_nan_flags((ONE, TWO), W, any_nan=True), 0)

    def test_overflow_in_each_mode(self):
        big = fp.max_finite(W)
        ovf = fp.FE_OVERFLOW | fp.FE_INEXACT
        want = {fp.RM_EVEN: fp.inf(W), fp.RM_AWAY: fp.inf(W),
                fp.RM_UP: fp.inf(W), fp.RM_ZERO: big, fp.RM_DOWN: big}
        for rm, v in want.items():
            self.assertEqual(fp.strict('mul', rm, (big, TWO), W), (v, ovf))
        neg = fp.max_finite(W, 1)
        want = {fp.RM_EVEN: fp.inf(W, 1), fp.RM_AWAY: fp.inf(W, 1),
                fp.RM_DOWN: fp.inf(W, 1), fp.RM_ZERO: neg, fp.RM_UP: neg}
        for rm, v in want.items():
            self.assertEqual(fp.strict('mul', rm, (neg, TWO), W), (v, ovf))

    def test_inexact_result_in_each_mode(self):
        three = fbits(3)
        lo, flags = fp.strict('div', fp.RM_DOWN, (ONE, three), W)
        hi, _ = fp.strict('div', fp.RM_UP, (ONE, three), W)
        self.assertEqual(flags, fp.FE_INEXACT)
        self.assertEqual(hi, lo + 1)
        self.assertEqual(fp.strict('div', fp.RM_ZERO, (ONE, three), W)[0],
                         lo)
        # 1 / 3 = 0.0101...: the nearest number is the larger one.
        self.assertEqual(fp.strict('div', fp.RM_EVEN, (ONE, three), W)[0],
                         0x3EAAAAAB)
        self.assertEqual(hi, 0x3EAAAAAB)
        # An exact result raises nothing.
        for rm in range(5):
            self.assertEqual(fp.strict('div', rm, (ONE, TWO), W), (HALF, 0))
            self.assertEqual(fp.strict('sqrt', rm, (fbits(4),), W),
                             (TWO, 0))

    def test_ties(self):
        # 1 + 2^-24 is the middle of 1 and the next number.
        p = fp.FORMATS[W][1]
        tie = fbits(F(1, 1 << p))
        self.assertEqual(fp.strict('add', fp.RM_EVEN, (ONE, tie), W)[0], ONE)
        self.assertEqual(fp.strict('add', fp.RM_AWAY, (ONE, tie), W)[0],
                         ONE + 1)
        self.assertEqual(fp.strict('add', fp.RM_ZERO, (ONE, tie), W)[0], ONE)
        self.assertEqual(fp.strict('add', fp.RM_UP, (ONE, tie), W)[0],
                         ONE + 1)
        # ... of the next two numbers: ties to even rounds up.
        self.assertEqual(
            fp.strict('add', fp.RM_EVEN, (ONE + 1, tie), W)[0], ONE + 2)

    def test_sign_of_an_exact_zero(self):
        neg1 = fbits(-1)
        nz = fp.sign_bit(W)
        for rm in range(5):
            want = nz if rm == fp.RM_DOWN else 0
            self.assertEqual(fp.strict('add', rm, (ONE, neg1), W), (want, 0))
            self.assertEqual(fp.strict('sub', rm, (ONE, ONE), W), (want, 0))
            self.assertEqual(fp.strict('add', rm, (0, nz), W), (want, 0))
            self.assertEqual(fp.strict('add', rm, (nz, nz), W), (nz, 0))
            self.assertEqual(fp.strict('fma', rm, (ONE, ONE, neg1), W),
                             (want, 0))
            self.assertEqual(fp.strict('mul', rm, (neg1, 0), W), (nz, 0))

    def test_underflow(self):
        mn = fp.min_normal(W)
        both = fp.FE_INEXACT | fp.FE_UNDERFLOW_B | fp.FE_UNDERFLOW_A
        # An exact subnormal result raises nothing.
        self.assertEqual(fp.strict('mul', fp.RM_EVEN, (mn, HALF), W),
                         (mn >> 1, 0))
        # Half of the smallest number: a tie, to even (zero).
        self.assertEqual(fp.strict('mul', fp.RM_EVEN, (1, HALF), W),
                         (0, both))
        self.assertEqual(fp.strict('mul', fp.RM_UP, (1, HALF), W),
                         (1, both))
        self.assertEqual(fp.strict('mul', fp.RM_AWAY, (1, HALF), W),
                         (1, both))
        # A value below the smallest normal number that rounds to it is
        # tiny before the rounding only.
        mag = fp.decode(mn, W)[2] * (1 - F(1, 1 << 26))
        self.assertEqual(
            fp.round_mag(0, mag, W, fp.RM_EVEN),
            (mn, fp.FE_INEXACT | fp.FE_UNDERFLOW_B))
        self.assertEqual(
            fp.round_mag(0, mag, W, fp.RM_ZERO), (mn - 1, both))
        views = fp.flag_views(fp.FE_INEXACT | fp.FE_UNDERFLOW_B)
        self.assertEqual({v[3] for v in views}, {True, False})
        self.assertTrue(all(v[4] for v in views))

    def test_choice_of_the_fused_operation(self):
        q = fp.qnan(W)
        self.assertEqual(fp.fma_invalid_choice((0, fp.inf(W), q), W),
                         fp.FE_INVALID_FMA)
        self.assertEqual(fp.fma_invalid_choice((fp.inf(W, 1), 0, q), W),
                         fp.FE_INVALID_FMA)
        self.assertEqual(fp.fma_invalid_choice((ONE, fp.inf(W), q), W), 0)
        self.assertEqual(fp.fma_invalid_choice((0, fp.inf(W), ONE), W), 0)
        views = fp.flag_views(fp.FE_INVALID_FMA)
        self.assertEqual({v[0] for v in views}, {True, False})

    def test_ldexp(self):
        for rm in range(5):
            self.assertEqual(fp.strict('ldexp', rm, (ONE, 1), W, 32),
                             (TWO, 0))
            self.assertEqual(
                fp.strict('ldexp', rm, (ONE, 0xFFFFFFFF), W, 32), (HALF, 0))
        v, flags = fp.strict('ldexp', fp.RM_ZERO, (ONE, 1000), W, 32)
        self.assertEqual((v, flags), (fp.max_finite(W),
                                      fp.FE_OVERFLOW | fp.FE_INEXACT))

    def test_solver_agrees_with_the_evaluator(self):
        # The value and the exceptions of the solver encoding, for both
        # choices of an implementation.
        rng = random.Random(6)
        w = 16
        vs = float_values(w, rng, 20)
        for name, k in (('add', 2), ('sub', 2), ('mul', 2), ('div', 2),
                        ('fma', 3), ('sqrt', 1), ('rem', 2)):
            xs = [z3.BitVec('a%d' % i, w) for i in range(k)]
            env = z3.BitVec('env', ENV)
            zv, zf = fp.z3_strict(name, env, xs)
            for _ in range(12):
                cs = tuple(rng.choice(vs) for _ in range(k))
                e = rng.randrange(1 << ENV)
                ev, ef = fp.strict(name, e, cs, w)
                if name == 'fma':
                    ef |= fp.fma_invalid_choice(cs, w)
                sub = [(x, z3.BitVecVal(c, w)) for x, c in zip(xs, cs)]
                sub.append((env, z3.BitVecVal(e, ENV)))
                for tb in (True, False):
                    for fi in (True, False):
                        s2 = sub + [(fp.z3_tiny_before(), z3.BoolVal(tb)),
                                    (fp.z3_fma_invalid(), z3.BoolVal(fi))]
                        gv = z3.simplify(z3.substitute(zv, *s2))
                        # The bits of a NaN of the solver are not
                        # specified.
                        gv = gv.as_long() if z3.is_bv_value(gv) \
                            else fp.qnan(w)
                        gf = z3.simplify(z3.substitute(zf, *s2)).as_long()
                        self.assertTrue(fp.same_bits(gv, ev, w),
                                        (name, e, cs))
                        self.assertEqual(gf, fp.z3_flag_view(ef, tb, fi),
                                         (name, e, cs))


class StrictKernelTest(unittest.TestCase):
    def test_kernels_match_the_evaluator_in_each_mode(self):
        rng = random.Random(8)
        U64 = np.uint64
        ints = [0, 1, 2, 5, 24, 25, 126, 127, 149, 150, 151, 280, 281, 70000]
        ints += [-x & 0xffffffff for x in ints]
        names = list(ops._STRICT) + list(ops._STRICT_CMP) + \
            ['G_FLDEXP', 'G_FREM']
        for name in names:
            info = ops.REGISTRY[name]
            for key in ops.search_keys(name, [3]):
                _, attr, res = ops.parse(key)
                for w in (16, 32):
                    rw = 1 if 'FCMP' in name else w
                    ws = [w] * info.operands
                    if 'LDEXP' in name:
                        ws[1] = 32
                    if info.constrained:
                        ws[-1] = ENV
                    self.assertTrue(info.typecheck(rw, ws, attr, res), key)
                    vs = float_values(w, rng, 30)
                    cols = []
                    for i in range(len(ws)):
                        pool = range(1 << ENV) \
                            if info.constrained and i == len(ws) - 1 else \
                            ints if 'LDEXP' in name and i == 1 else vs
                        pool = list(pool)
                        cols.append(np.array(
                            [[rng.choice(pool) for _ in vs]
                             for _ in range(5)], U64))
                    if len(ws) > 2 and 'LDEXP' not in name:
                        # Sums that are zero and sums of near values.
                        cols[1][0] = cols[0][0] ^ U64(fp.sign_bit(w))
                        cols[1][1] = cols[0][1] + U64(1)
                    oks = [np.ones(c.shape, bool) for c in cols]
                    counters = {}
                    v, _ = kernels.apply(key, rw, ws, cols, oks, counters)
                    self.assertEqual(counters, {}, key)
                    g, _ = kernels.generic(key, rw, ws, cols, oks)
                    self.assertTrue(np.array_equal(v, g), (key, w))

    def test_fused_operation_at_a_tie_in_each_mode(self):
        U64 = np.uint64
        for w in (16, 32):
            eb, p = fp.FORMATS[w]
            a, b, c, e = [], [], [], []
            for k in range(1, p):
                for cv in (0, fp.sign_bit(w), 1, 1 | fp.sign_bit(w),
                           fbits(F(1, 2), w), fbits(F(-1, 2), w)):
                    for rm in range(5):
                        a.append(fp.encode(k & 1, F(2 ** k + 1), w))
                        b.append(fp.encode(0, F(2 ** (p - k) + 1), w))
                        c.append(cv)
                        e.append(rm)
            cols = [np.array([x], U64) for x in (a, b, c, e)]
            oks = [np.ones(x.shape, bool) for x in cols]
            ws = [w, w, w, ENV]
            v, _ = kernels.apply('G_STRICT_FMA', w, ws, cols, oks)
            g, _ = kernels.generic('G_STRICT_FMA', w, ws, cols, oks)
            self.assertTrue(np.array_equal(v, g), w)


class StrictRuleTest(unittest.TestCase):
    """Rules with constrained operations: the value in each rounding
    mode, and the same exceptions."""

    def test_subtract_a_negation(self):
        src = op('G_STRICT_FSUB', W, V(0), op('G_FNEG', W, V(1)), E)
        tgt = op('G_STRICT_FADD', W, V(0), V(1), E)
        r = rule_of(src, tgt, (W, W, ENV))
        self.assertIsNotNone(r)
        self.assertEqual(r['precondition'], 'true')
        self.assertIsNone(emit.why_not_emittable(r))
        text = cpp(r)
        self.assertIn('G_STRICT_FADD', text)
        # The replacement keeps the exception flag of the source.
        self.assertIn('MachineInstr::NoFPExcept', text)

    def test_search_finds_the_rule(self):
        src = op('G_STRICT_FSUB', W, V(0), op('G_FNEG', W, V(1)), E)
        self.assertIn(op('G_STRICT_FADD', W, V(0), V(1), E),
                      targets_of(instance(src, (W, W, ENV))))

    def test_signaling_comparison_needs_ignored_exceptions(self):
        # A signaling comparison raises "invalid" for a quiet NaN; the
        # quiet comparison does not.
        src = op('G_STRICT_FCMPS:olt', 1, V(0), V(1), E)
        tgt = op('G_STRICT_FCMP:olt', 1, V(0), V(1), E)
        self.assertIsNone(rule_of(src, tgt, (W, W, ENV)))
        r = rule_of(src, tgt, (W, W, ENV), nofpe=True)
        self.assertIsNotNone(r)
        self.assertEqual(r['precondition'], 'nofpexcept')
        text = cpp(r)
        self.assertIn('ignoresFPExceptions(MRI, Dst)', text)
        self.assertIn('bool Pass = NoFPExcept;', text)

    def test_multiply_by_one(self):
        # x * 1.0 is not x: a constrained operation is the IEEE
        # operation, which makes a signaling NaN quiet (and raises
        # "invalid"). The operation without the environment can give
        # the NaN operand.
        src = op('G_STRICT_FMUL', W, V(0), V(1), E)
        consts = [None, ONE, None]
        self.assertIsNone(rule_of(src, V(0), (W, W, ENV), consts))
        self.assertIsNone(rule_of(src, V(0), (W, W, ENV), consts,
                                  nofpe=True))
        i = instance(src, (W, W, ENV), consts, nofpe=True)
        model = discover.prove_concrete(i, V(0), smt.Z3Backend())
        self.assertEqual(model.status, 'sat')
        r = rule_of(op('G_FMUL', W, V(0), V(1)), V(0), (W, W), consts[:2])
        self.assertIsNotNone(r)
        self.assertIn('1.0', r['precondition'])

    def test_rounding_mode_refutes_a_rule(self):
        # x + (-0.0) is x to nearest. Toward negative, (+0.0) + (-0.0)
        # is -0.0.
        nz = fp.literal_bits('f-0', W)
        r = rule_of(op('G_FADD', W, V(0), V(1)), V(0), (W, W), [None, nz])
        self.assertIsNotNone(r)
        src = op('G_STRICT_FADD', W, V(0), V(1), E)
        self.assertIsNone(rule_of(src, V(0), (W, W, ENV), [None, nz, None],
                                  nofpe=True))
        i = instance(src, (W, W, ENV), [None, nz, None], nofpe=True)
        res = discover.prove_concrete(i, V(0), smt.Z3Backend())
        self.assertEqual(res.status, 'sat')

    def test_constant_of_the_replacement(self):
        # x / 2.0 -> x * 0.5 with the exceptions of the source: the
        # value and the flags agree in each rounding mode.
        src = op('G_STRICT_FDIV', W, V(0), V(1), E)
        i = instance(src, (W, W, ENV), [None, TWO, None])
        tgt = op('G_STRICT_FMUL', W, V(0), L('f0.5'), E)
        self.assertEqual(
            discover.prove_concrete(i, tgt, smt.Z3Backend()).status, 'unsat')
        # x / 3.0 -> x * (1 / 3.0) is refuted.
        i = instance(src, (W, W, ENV), [None, fbits(3), None])
        tgt = op('G_STRICT_FMUL', W, V(0),
                 op('G_FDIV', W, L('f1'), V(1)), E)
        self.assertEqual(
            discover.prove_concrete(i, tgt, smt.Z3Backend(),
                                    const_vars=(1,)).status, 'sat')
        # A replacement without the environment is no rule: an operation
        # that is not constrained next to a constrained one.
        self.assertIsNotNone(
            ir.env_error(src, op('G_FMUL', W, V(0), L('f0.5'))))

    def test_form_of_the_environment(self):
        a = op('G_STRICT_FADD', W, V(0), V(1), E)
        self.assertIsNone(ir.env_error(a))
        self.assertEqual(ir.env_vars(a), {2})
        # Two environments.
        two = op('G_STRICT_FADD', W, op('G_STRICT_FMUL', W, V(0), V(1), E),
                 V(0), V(3))
        self.assertIn('one environment', ir.env_error(two))
        # A constrained operation only in the replacement.
        self.assertIn('replacement only',
                      ir.env_error(op('G_FNEG', W, V(0)),
                                   op('G_STRICT_FADD', W, V(0), V(0), E)))
        # An operator that reads the environment as a value.
        self.assertIn('reads', ir.env_error(
            op('G_STRICT_FADD', W, V(0), op('G_FNEG', W, E), E)))
        # A constant that the compiler computes is not an operation of
        # the program.
        src = op('G_STRICT_FDIV', W, V(0), V(1), E)
        tgt = op('G_STRICT_FMUL', W, V(0),
                 op('G_FDIV', W, L('f1'), V(1)), E)
        self.assertIsNotNone(ir.env_error(src, tgt))
        self.assertIsNone(ir.env_error(src, tgt, const_vars=(1,)))

    def test_divide_by_a_constant_with_an_exact_inverse(self):
        src = op('G_STRICT_FDIV', W, V(0), V(1), E)
        tgt = op('G_STRICT_FMUL', W, V(0),
                 op('G_FDIV', W, L('f1'), V(1)), E)
        r = rule_of(src, tgt, (W, W, ENV), [None, fbits(4), None], cv=(1,))
        self.assertIsNotNone(r)
        self.assertIn('exact_inverse(x1)', r['precondition'])
        self.assertNotIn('nofpexcept', r['precondition'])


STRICT_MIR = '''
---
name: strict
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0, $vgpr1
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s32) = G_FNEG %1
    %3:_(s32) = G_STRICT_FSUB %0, %2
    $vgpr0 = COPY %3
    SI_RETURN implicit $vgpr0
...
---
name: ignore
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = G_FCONSTANT float 1.000000e+00
    %2:_(s32) = nofpexcept G_STRICT_FMUL %0, %1
    $vgpr0 = COPY %2
    SI_RETURN implicit $vgpr0
...
---
name: window
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0, $vgpr1
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s32) = G_STRICT_FMUL %0, %1
    %3:_(s32) = G_AND %0, %1
    %4:_(s32) = G_STRICT_FADD %2, %3
    $vgpr0 = COPY %4
    SI_RETURN implicit $vgpr0
...
---
name: barrier
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0, $vgpr1, $vgpr2
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %5:_(s32) = COPY $vgpr2
    %6:_(p1) = G_MERGE_VALUES %1, %5
    %2:_(s32) = G_STRICT_FMUL %0, %1
    G_STORE %0(s32), %6(p1) :: (store (s32), addrspace 1)
    %4:_(s32) = G_STRICT_FADD %2, %0
    $vgpr0 = COPY %4
    SI_RETURN implicit $vgpr0
...
'''


@unittest.skipUnless(HAVE_LLC, 'no llc (set GIRS_LLC)')
class RealExtractionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        mir = os.path.join(cls.tmp.name, 'strict.mir')
        with open(mir, 'w') as f:
            f.write(STRICT_MIR)
        _, out = cli._extract_one(LLC, mir, cls.tmp.name, 'mir',
                                  targets.get('AMDGPU'))
        assert out, 'the extractor failed'
        with open(out) as f:
            cls.records = [json.loads(l) for l in f if l.strip()]
        cls.insts, cls.stats = corpus.load([out])

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _sources(self, fn):
        out = []
        for r in self.records:
            if r['fn'] == fn:
                i = corpus.parse_record(r)
                out.append((ir.to_sexpr(i.expr), i))
        return out

    def test_every_record_is_read(self):
        self.assertEqual(self.stats['unsupported'], 0)

    def test_environment_is_the_last_operand(self):
        srcs = dict(self._sources('strict'))
        i = srcs['(G_STRICT_FSUB:s32 x0 (G_FNEG:s32 x1) x2)']
        self.assertEqual(tuple(i.vw), (W, W, ENV))
        # The program reads the exceptions: the bit ENV_IGNORE is 0.
        self.assertEqual(tuple(i.facts[2]), (fp.ENV_IGNORE, 0, True))

    def test_flag_nofpexcept(self):
        (i,) = [i for _, i in self._sources('ignore')]
        self.assertEqual(tuple(i.facts[2]), (0, fp.ENV_IGNORE, True))
        self.assertEqual(list(i.consts), [None, ONE, None])

    def test_operations_of_one_window_are_one_tree(self):
        srcs = dict(self._sources('window'))
        self.assertIn('(G_STRICT_FADD:s32 (G_STRICT_FMUL:s32 x0 x1 x2) '
                      '(G_AND:s32 x0 x1) x2)', srcs)

    def test_a_write_to_memory_ends_the_window(self):
        for s, _ in self._sources('barrier'):
            self.assertLessEqual(s.count('G_STRICT_'), 1, s)


class VectorTest(unittest.TestCase):
    def test_lanes_of_a_constrained_operation(self):
        # The lanes of a vector have one environment: the record of a
        # constrained operation on vectors is a source for scalars.
        def node(opc, reg, args):
            return {'op': opc, 'w': 32, 'lanes': 2, 'type': '<2 x f32>',
                    'reg': reg, 'zero': '0x0', 'one': '0x0',
                    'noundef': False, 'uses': 1, 'flags': [], 'args': args}
        rec = {'fn': 'f', 'bb': 1, 'root': '%3', 'interior': 2,
               'expr': node('G_STRICT_FMA', '%3',
                            [node('G_FNEG', '%2', [{'in': 0}]), {'in': 1},
                             {'in': 2}]),
               'inputs': [{'reg': '%%%d' % k, 'w': 32, 'lanes': 2,
                           'type': '<2 x f32>', 'zero': '0x0', 'one': '0x0',
                           'noundef': False, 'def': 'COPY'}
                          for k in range(3)]}
        why = []
        i = corpus.parse_record(rec, 'x', why)
        self.assertIsNotNone(i, why)
        self.assertTrue(i.lifted)
        self.assertEqual(ir.to_sexpr(i.expr),
                         '(G_STRICT_FMA:s32 (G_FNEG:s32 x0) x1 x2 x3)')
        self.assertEqual(tuple(i.vw), (W, W, W, ENV))


if __name__ == '__main__':
    unittest.main()
