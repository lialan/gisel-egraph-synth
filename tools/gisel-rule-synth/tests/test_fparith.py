#!/usr/bin/env python3
"""Tests of the models of the floating-point operations on the value of a
number: arithmetic (G_FADD, G_FSUB, G_FMUL, G_FDIV, G_FREM, G_FMA, G_FMAD,
G_FSQRT), rounding to an integral value and to an integer, the minimum /
maximum operators, G_FCANONICALIZE, and the parts of a value (G_FMODF,
G_FLDEXP, G_FFREXP).

Run:  python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests
"""

import importlib.util
import os
import random
import struct
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import numpy as np  # noqa: E402
import z3  # noqa: E402

from girs import corpus, emit, fp, ir, opcheck, ops, smt  # noqa: E402
from girs import targets  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    'gi_rule_synth_cli', os.path.join(ROOT, 'gi-rule-synth.py'))
cli = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cli)

LLC = os.environ.get('GIRS_LLC') or os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(ROOT))), 'build', 'bin',
    'llc')
HAVE_LLC = os.path.exists(LLC)


def V(i):
    return ('var', i)


def op(name, w, *args):
    return (name, w) + args


def refines(src, tgt, vw):
    enc = smt.Encoder(vw, src[1])
    f = smt.refinement_violation(enc, src, tgt, z3.BoolVal(True))
    return smt.Z3Backend(timeout_ms=60000).check(f).status == 'unsat'


_PACK = {16: ('<e', '<H'), 32: ('<f', '<I'), 64: ('<d', '<Q')}


def bits(x, w):
    f, i = _PACK[w]
    return struct.unpack(i, struct.pack(f, x))[0]


def C(x, w):
    """The floating-point constant x of w bits."""
    return ('const', w, bits(x, w))


_NP = {16: (np.float16, np.uint16), 32: (np.float32, np.uint32),
       64: (np.float64, np.uint64)}


def np_value(b, w):
    return np.array([b], _NP[w][1]).view(_NP[w][0])[0]


def np_bits(x, w):
    return int(np.array([x], _NP[w][0]).view(_NP[w][1])[0])


class EvaluatorTest(unittest.TestCase):
    """The exact evaluator against the IEEE arithmetic of the host."""

    def test_arithmetic_and_rounding(self):
        rng = random.Random(7)
        old = np.seterr(all='ignore')
        self.addCleanup(np.seterr, **old)
        for w in (16, 32, 64):
            sp = opcheck._fp_specials(w)
            for _ in range(1500):
                a, b = (rng.choice(sp) if rng.random() < 0.5
                        else rng.getrandbits(w) for _ in range(2))
                fa, fb = np_value(a, w), np_value(b, w)
                for name, got, want in (
                        ('add', fp.add(a, b, w), fa + fb),
                        ('sub', fp.sub(a, b, w), fa - fb),
                        ('mul', fp.mul(a, b, w), fa * fb),
                        ('div', fp.div(a, b, w), fa / fb),
                        ('sqrt', fp.sqrt(a, w), np.sqrt(fa)),
                        ('floor', fp.round_integral(a, w, 'floor'),
                         np.floor(fa)),
                        ('ceil', fp.round_integral(a, w, 'ceil'),
                         np.ceil(fa)),
                        ('trunc', fp.round_integral(a, w, 'trunc'),
                         np.trunc(fa)),
                        ('even', fp.round_integral(a, w, 'even'),
                         np.rint(fa))):
                    self.assertTrue(
                        fp.same_bits(got, np_bits(want, w), w),
                        (name, w, hex(a), hex(b), hex(got)))

    def test_parts(self):
        """G_FREM, G_FMODF, G_FLDEXP and G_FFREXP against the host."""
        rng = random.Random(11)
        old = np.seterr(all='ignore')
        self.addCleanup(np.seterr, **old)
        for w in (16, 32, 64):
            sp = opcheck._fp_specials(w)
            for _ in range(1500):
                a, b = (rng.choice(sp) if rng.random() < 0.5
                        else rng.getrandbits(w) for _ in range(2))
                n = rng.choice([0, 1, -1, 2, -3, 24, -24, 150, -150, 1100,
                                -1100, 3000, -3000,
                                rng.getrandbits(32) - (1 << 31)])
                fa, fb = np_value(a, w), np_value(b, w)
                frac, ipart = np.modf(fa)
                mant, exp = np.frexp(fa)
                scaled = _NP[w][0](np.ldexp(np.float64(fa),
                                            max(-5000, min(5000, n))))
                for name, got, want in (
                        ('rem', fp.rem(a, b, w), np.fmod(fa, fb)),
                        ('modf0', fp.modf(a, w, 0), frac),
                        ('modf1', fp.modf(a, w, 1), ipart),
                        ('ldexp', fp.ldexp(a, n & 0xffffffff, 32, w),
                         scaled),
                        ('frexp0', fp.frexp(a, w, 0), mant)):
                    self.assertTrue(
                        fp.same_bits(got, np_bits(want, w), w),
                        (name, w, hex(a), hex(b), n))
                e = fp.frexp(a, w, 1)
                if fp.decode(a, w)[0] == 'num':
                    self.assertEqual(e, int(exp), (w, hex(a)))
                else:
                    self.assertIsNone(e)
        # The exponent has the width of its type: 16 bits here.
        one = bits(1.0, 32)
        self.assertEqual(fp.ldexp(one, 0xffff, 16, 32), bits(0.5, 32))
        self.assertEqual(fp.ldexp(one, 0x8000, 16, 32), 0)
        self.assertEqual(fp.ldexp(one, 0x7fff, 16, 32), fp.inf(32))

    def test_fma_has_one_rounding(self):
        # (1 + 2**-10) * (1 - 2**-10) is 1 - 2**-20: a half has it as 1.
        w = 16
        x = fp.encode(0, 1 + fp.Fraction(1, 1 << 10), w)
        y = fp.encode(0, 1 - fp.Fraction(1, 1 << 10), w)
        neg_one = bits(-1.0, w)
        fused = fp.fma(x, y, neg_one, w)
        two_steps = fp.add(fp.mul(x, y, w), neg_one, w)
        self.assertEqual(fp.decode(fused, w)[2], -fp.Fraction(1, 1 << 20))
        self.assertEqual(two_steps, 0)
        self.assertEqual(ops.REGISTRY['G_FMAD'].eval(
            w, [w] * 3, None, 0, [x, y, neg_one]), two_steps)
        self.assertEqual(ops.REGISTRY['G_FMA'].eval(
            w, [w] * 3, None, 0, [x, y, neg_one]), fused)

    def test_zero_signs(self):
        w = 32
        pz, nz = 0, fp.sign_bit(w)
        one = bits(1.0, w)
        self.assertEqual(fp.add(pz, nz, w), pz)
        self.assertEqual(fp.add(nz, nz, w), nz)
        self.assertEqual(fp.sub(one, one, w), pz)
        self.assertEqual(fp.mul(nz, one, w), nz)
        self.assertEqual(fp.fma(nz, one, nz, w), nz)
        self.assertEqual(fp.fma(nz, one, pz, w), pz)
        self.assertEqual(fp.sqrt(nz, w), nz)
        self.assertEqual(fp.round_integral(bits(-0.25, w), w, 'ceil'), nz)
        self.assertEqual(fp.round_integral(bits(0.5, w), w, 'even'), pz)
        self.assertEqual(fp.round_integral(bits(0.5, w), w, 'away'), one)
        self.assertEqual(fp.round_integral(bits(2.5, w), w, 'even'),
                         bits(2.0, w))

    def test_round_to_int(self):
        w = 32
        self.assertEqual(fp.round_to_int(bits(2.5, w), w, 32, 'away'), 3)
        self.assertEqual(fp.round_to_int(bits(2.5, w), w, 32, 'even'), 2)
        self.assertEqual(fp.round_to_int(bits(-2.5, w), w, 8, 'away'),
                         0xfd)
        # Outside of the range, an infinity and a NaN: not specified.
        self.assertIsNone(fp.round_to_int(bits(128.0, w), w, 8, 'even'))
        self.assertEqual(fp.round_to_int(bits(-128.4, w), w, 8, 'even'),
                         0x80)
        self.assertIsNone(fp.round_to_int(fp.inf(w), w, 64, 'even'))
        self.assertIsNone(fp.round_to_int(fp.qnan(w), w, 64, 'even'))

    def test_minmax(self):
        w = 32
        pz, nz = 0, fp.sign_bit(w)
        one, two = bits(1.0, w), bits(2.0, w)
        q, sn = fp.qnan(w), fp.inf(w) | 1
        for kind in fp.MINMAX_KINDS:
            self.assertEqual(fp.minmax(kind, False, one, two, w), one)
            self.assertEqual(fp.minmax(kind, True, one, two, w), two)
            # -0.0 is less than +0.0.
            self.assertEqual(fp.minmax(kind, False, pz, nz, w), nz)
            self.assertEqual(fp.minmax(kind, True, nz, pz, w), pz)
            self.assertTrue(fp.is_nan(fp.minmax(kind, False, q, sn, w), w))
        # A quiet NaN and a number.
        self.assertEqual(fp.minmax('imum', False, q, one, w), q)
        for kind in ('num', 'ieee', 'imumnum'):
            self.assertEqual(fp.minmax(kind, False, q, one, w), one)
            self.assertEqual(fp.minmax(kind, True, one, q, w), one)
        # A signaling NaN and a number.
        self.assertTrue(fp.is_nan(fp.minmax('ieee', False, sn, one, w), w))
        self.assertEqual(fp.minmax('imumnum', False, sn, one, w), one)
        self.assertEqual(fp.minmax('num', False, sn, one, w), one)
        # The results that only LLVM permits for G_FMINNUM.
        self.assertTrue(
            fp.is_nan(fp.minmax('num', False, sn, one, w, choice=2), w))
        self.assertEqual(fp.minmax('num', False, pz, nz, w, choice=1), pz)
        self.assertEqual(fp.minmax('num', False, nz, nz, w, choice=1), nz)
        self.assertEqual(fp.minmax('ieee', False, pz, nz, w, choice=1), nz)


class RegistryTest(unittest.TestCase):
    def test_capabilities(self):
        names = ops._MAKES_NAN + tuple(ops._FP_ROUND_INT)
        self.assertEqual(len(names), 31)
        for n in names:
            info = ops.REGISTRY[n]
            self.assertEqual(info.lhs(), 'yes', n)
            # A rule does not create G_FFREXP.
            self.assertEqual(info.rhs() == 'yes', n != 'G_FFREXP', n)
            self.assertTrue(info.denormal, n)
            self.assertTrue(info.fp_operand, n)
        for n in ops._MAKES_NAN:
            self.assertTrue(ops.REGISTRY[n].makes_nan, n)
            self.assertTrue(ops.REGISTRY[n].fp_result, n)
            self.assertTrue(ops.REGISTRY[n].typecheck(
                32, [32] * ops.REGISTRY[n].operands, None, 0))
            # bfloat and quad have no model.
            self.assertFalse(ops.REGISTRY[n].typecheck(
                128, [128] * ops.REGISTRY[n].operands, None, 0))
        # The exponent of G_FLDEXP and of G_FFREXP is an integer of a
        # width of its own.
        ld, fr = ops.REGISTRY['G_FLDEXP'], ops.REGISTRY['G_FFREXP']
        self.assertEqual(ld.result_kind(['f', 'i']), 'f')
        self.assertIsNone(ld.result_kind(['f', 'f']))
        self.assertTrue(ld.typecheck(64, [64, 16], None, 0))
        self.assertEqual(fr.result_kind(['f'], 0), 'f')
        self.assertEqual(fr.result_kind(['f'], 1), 'i')
        self.assertTrue(fr.typecheck(32, [64], None, 1))
        self.assertFalse(fr.typecheck(8, [64], None, 1))
        self.assertFalse(fr.typecheck(32, [64], None, 0))
        self.assertTrue(fr.makes_nan_at(0))
        self.assertFalse(fr.makes_nan_at(1))
        self.assertFalse(fr.unspecified_at(0))
        self.assertTrue(fr.unspecified_at(1))
        self.assertEqual(ir.result_kind(op('G_FFREXP#1', 32, V(0))), 'i')
        self.assertEqual(ir.result_kind(op('G_FFREXP', 32, V(0))), 'f')
        self.assertEqual(
            ir.operand_kind(op('G_FLDEXP', 32, V(0), V(1)), 1), 'i')
        self.assertEqual(ir.var_kinds(op('G_FLDEXP', 32, V(0), V(1))),
                         {0: 'f', 1: 'i'})
        for n in ops._FP_ROUND_INT:
            info = ops.REGISTRY[n]
            self.assertFalse(info.fp_result)
            self.assertTrue(info.typecheck(64, [32], None, 0))
            self.assertFalse(info.typecheck(64, [8], None, 0))
            self.assertIsNotNone(info.unspecified_if)
        self.assertTrue(ops.REGISTRY['G_FADD'].commutative)
        self.assertFalse(ops.REGISTRY['G_FSUB'].commutative)
        self.assertEqual(ops.REGISTRY['G_FMINNUM'].tgt_choice, 2)
        self.assertTrue(ops.REGISTRY['G_FMINNUM_IEEE'].nan_quiet)
        self.assertTrue(ops.REGISTRY['G_FCANONICALIZE'].nan_quiet)
        self.assertFalse(ops.REGISTRY['G_FMINIMUM'].nan_quiet)
        # Operations on the bits do not depend on the denormal mode.
        for n in ('G_FNEG', 'G_FABS', 'G_FCOPYSIGN', 'G_IS_FPCLASS',
                  'G_BITCAST', 'G_FPTOSI', 'G_SITOFP'):
            self.assertFalse(ops.REGISTRY[n].denormal, n)
        for n in ('G_FCMP', 'G_FPEXT', 'G_FPTRUNC'):
            self.assertTrue(ops.REGISTRY[n].denormal, n)

    def test_models_agree(self):
        names = set(ops._MAKES_NAN + tuple(ops._FP_ROUND_INT))
        n, bad = opcheck.check_models(samples=12, names=names)
        self.assertGreater(n, 1700)
        self.assertEqual(bad, [])


class ProofTest(unittest.TestCase):
    def check(self, src, tgt, vw, want=True):
        self.assertEqual(refines(src, tgt, vw), want,
                         (ir.to_sexpr(src), ir.to_sexpr(tgt)))

    def test_arithmetic(self):
        w = 32
        x, y = V(0), V(1)
        vw = (w, w)
        self.check(op('G_FADD', w, x, y), op('G_FADD', w, y, x), vw)
        self.check(op('G_FSUB', w, x, y),
                   op('G_FADD', w, x, op('G_FNEG', w, y)), vw)
        # -(x - y) is -0.0 and y - x is +0.0 for x == y.
        self.check(op('G_FNEG', w, op('G_FSUB', w, x, y)),
                   op('G_FSUB', w, y, x), vw, False)
        # LangRef: "fmul SNaN, 1.0" may be simplified to SNaN.
        self.check(op('G_FMUL', w, x, C(1.0, w)), x, (w,))
        self.check(op('G_FADD', w, x, C(-0.0, w)), x, (w,))
        # -0.0 + +0.0 is +0.0.
        self.check(op('G_FADD', w, x, C(0.0, w)), x, (w,), False)
        self.check(op('G_FSUB', w, x, C(0.0, w)), x, (w,))
        self.check(op('G_FMUL', w, x, C(2.0, w)), op('G_FADD', w, x, x),
                   (w,))
        self.check(op('G_FSUB', w, x, x), C(0.0, w), (w,), False)

    def test_division(self):
        w = 16
        x = V(0)
        self.check(op('G_FDIV', w, x, C(2.0, w)),
                   op('G_FMUL', w, x, C(0.5, w)), (w,))
        self.check(op('G_FDIV', w, x, C(3.0, w)),
                   op('G_FMUL', w, x, C(1.0 / 3, w)), (w,), False)
        self.check(op('G_FDIV', w, x, C(1.0, w)), x, (w,))

    def test_fma(self):
        w = 16
        x, y, z = V(0), V(1), V(2)
        vw = (w, w, w)
        mad = op('G_FADD', w, op('G_FMUL', w, x, y), z)
        self.check(op('G_FMAD', w, x, y, z), mad, vw)
        self.check(mad, op('G_FMAD', w, x, y, z), vw)
        # One rounding and two roundings give different results.
        self.check(op('G_FMA', w, x, y, z), mad, vw, False)
        self.check(op('G_FMA', w, x, y, C(-0.0, w)),
                   op('G_FMUL', w, x, y), (w, w))
        self.check(op('G_FMA', w, x, C(1.0, w), y),
                   op('G_FADD', w, x, y), (w, w))

    def test_sqrt(self):
        w = 16
        x = V(0)
        # The square root of -0.0 is -0.0.
        self.check(op('G_FABS', w, op('G_FSQRT', w, x)),
                   op('G_FSQRT', w, x), (w,), False)
        self.check(op('G_FSQRT', w, op('G_FABS', w, x)),
                   op('G_FABS', w, op('G_FSQRT', w, op('G_FABS', w, x))),
                   (w,))
        self.check(op('G_FCMP:uno', 1, op('G_FSQRT', w, x),
                      op('G_FSQRT', w, x)),
                   op('G_FCMP:ult', 1, x, C(-0.0, w)), (w,))

    def test_rounding(self):
        w = 32
        x = V(0)
        for a in ('G_FFLOOR', 'G_FCEIL', 'G_INTRINSIC_TRUNC', 'G_FRINT',
                  'G_INTRINSIC_ROUND'):
            for b in ('G_FFLOOR', 'G_INTRINSIC_ROUNDEVEN'):
                # A second rounding of an integral value changes nothing.
                self.check(op(a, w, op(b, w, x)), op(b, w, x), (w,))
        self.check(op('G_FRINT', w, x), op('G_FNEARBYINT', w, x), (w,))
        self.check(op('G_FRINT', w, x), op('G_INTRINSIC_ROUNDEVEN', w, x),
                   (w,))
        self.check(op('G_FRINT', w, x), op('G_INTRINSIC_ROUND', w, x),
                   (w,), False)
        self.check(op('G_FCEIL', w, op('G_FNEG', w, x)),
                   op('G_FNEG', w, op('G_FFLOOR', w, x)), (w,))
        self.check(op('G_FFLOOR', w, x), op('G_INTRINSIC_TRUNC', w, x),
                   (w,), False)
        # For a value that is not negative, they are equal.
        self.check(op('G_FFLOOR', w, op('G_FABS', w, x)),
                   op('G_INTRINSIC_TRUNC', w, op('G_FABS', w, x)), (w,))

    def test_round_to_int(self):
        w = 32
        x = V(0)
        rounded = op('G_FPTOSI', 64, op('G_INTRINSIC_ROUND', w, x))
        # The conversion is poison where G_LROUND has a value that is not
        # specified: the first direction is a refinement.
        self.check(rounded, op('G_LROUND', 64, x), (w,))
        self.check(op('G_LROUND', 64, x), rounded, (w,), False)
        self.check(op('G_LROUND', 64, x), op('G_LLROUND', 64, x), (w,))
        self.check(op('G_LROUND', 64, x), op('G_INTRINSIC_LRINT', 64, x),
                   (w,), False)
        self.check(op('G_INTRINSIC_LRINT', 32, x),
                   op('G_LROUND', 32, op('G_FRINT', w, x)), (w,))
        self.check(op('G_LROUND', 32, x), ('const', 32, 0), (w,), False)
        # A value outside of the range of 32 bits: the source has some
        # value, so a narrower result can replace the wider one only in
        # one direction.
        self.check(op('G_LROUND', 32, x),
                   op('G_TRUNC', 32, op('G_LROUND', 64, x)), (w,))
        self.check(op('G_TRUNC', 32, op('G_LROUND', 64, x)),
                   op('G_LROUND', 32, x), (w,), False)

    def test_minmax(self):
        w = 32
        x, y = V(0), V(1)
        vw = (w, w)
        # A signaling NaN x: G_FMINNUM_IEEE gives a quiet NaN.
        self.check(op('G_FMINNUM', w, x, x), x, (w,))
        self.check(op('G_FMINIMUM', w, x, x), x, (w,))
        self.check(op('G_FMINIMUMNUM', w, x, x), x, (w,))
        self.check(op('G_FMINNUM_IEEE', w, x, x), x, (w,), False)
        self.check(op('G_IS_FPCLASS:%d' % fp.FC_SNAN, 1,
                      op('G_FMINNUM_IEEE', w, x, y)), ('const', 1, 0), vw)
        self.check(op('G_FMINNUM_IEEE', w, x, x),
                   op('G_FCANONICALIZE', w, x), (w,))
        # LangRef: minnum can be refined into minimumnum.
        self.check(op('G_FMINNUM', w, x, y), op('G_FMINIMUMNUM', w, x, y),
                   vw)
        # A new G_FMINNUM has each result that LLVM permits: a NaN for a
        # signaling NaN, and each zero for two different zeros.
        self.check(op('G_FMINIMUMNUM', w, x, y), op('G_FMINNUM', w, x, y),
                   vw, False)
        self.check(op('G_FMINNUM', w, x, y), op('G_FMINNUM', w, y, x),
                   vw, False)
        for name in ('G_FMINNUM_IEEE', 'G_FMINIMUM', 'G_FMINIMUMNUM',
                     'G_FMAXNUM_IEEE', 'G_FMAXIMUM', 'G_FMAXIMUMNUM'):
            self.check(op(name, w, x, y), op(name, w, y, x), vw)
        self.check(op('G_FNEG', w, op('G_FMINIMUM', w, op('G_FNEG', w, x),
                                      op('G_FNEG', w, y))),
                   op('G_FMAXIMUM', w, x, y), vw)
        self.check(op('G_FMINIMUM', w, x, y), op('G_FMINIMUMNUM', w, x, y),
                   vw, False)
        # A comparison and a select are not the minimum for a NaN or for
        # two zeros.
        self.check(op('G_SELECT', w, op('G_FCMP:olt', 1, x, y), x, y),
                   op('G_FMINIMUM', w, x, y), vw, False)

    def test_canonicalize(self):
        w = 32
        x = V(0)
        can = op('G_FCANONICALIZE', w, x)
        self.check(op('G_FCANONICALIZE', w, can), can, (w,))
        self.check(can, x, (w,), False)
        self.check(op('G_FMUL', w, x, C(1.0, w)), can, (w,))
        # The result is never a signaling NaN.
        snan = 'G_IS_FPCLASS:%d' % fp.FC_SNAN
        mul = op('G_FMUL', w, x, C(1.0, w))
        self.check(op(snan, 1, can), ('const', 1, 0), (w,))
        self.check(op(snan, 1, can), op(snan, 1, x), (w,), False)
        # A multiplication gives some NaN of its set: it can be quiet,
        # and it can be the signaling NaN of the operand.
        self.check(op(snan, 1, mul), ('const', 1, 0), (w,))
        self.check(op(snan, 1, mul), op(snan, 1, x), (w,))
        self.check(op(snan, 1, mul), ('const', 1, 1), (w,), False)

    def test_remainder(self):
        w = 16
        x, y = V(0), V(1)
        vw = (w, w)
        rem = op('G_FREM', w, x, y)
        # The sign of the divisor has no effect. (The solver gives no
        # answer in 10 minutes for the sign of the dividend, a proof with
        # two remainders of different operands: such a rule is not
        # proved.)
        self.check(op('G_FREM', w, x, op('G_FNEG', w, y)), rem, vw)
        self.check(op('G_FREM', w, x, op('G_FABS', w, y)), rem, vw)
        self.check(rem, op('G_FREM', w, y, x), vw, False)
        # x rem 1.0 is not x - trunc(x) for an infinity (a NaN, and 0).
        self.check(op('G_FREM', w, x, C(1.0, w)),
                   op('G_FMODF', w, x), (w,), False)
        self.check(op('G_FREM', w, x, C(1.0, w)),
                   op('G_FSUB', w, x, op('G_INTRINSIC_TRUNC', w, x)),
                   (w,), False)

    def test_modf(self):
        w = 32
        x = V(0)
        self.check(op('G_FMODF#1', w, x), op('G_INTRINSIC_TRUNC', w, x),
                   (w,))
        self.check(op('G_INTRINSIC_TRUNC', w, x), op('G_FMODF#1', w, x),
                   (w,))
        self.check(op('G_FMODF', w, op('G_FNEG', w, x)),
                   op('G_FNEG', w, op('G_FMODF', w, x)), (w,))
        self.check(op('G_FMODF', w, op('G_FMODF#1', w, x)),
                   op('G_FCOPYSIGN', w, C(0.0, w), x), (w,), False)  # NaN
        # The parts have the sign of the value: -0.0 for -1.0, and x -
        # trunc(x) is +0.0 there.
        self.check(op('G_FMODF', w, x),
                   op('G_FSUB', w, x, op('G_INTRINSIC_TRUNC', w, x)),
                   (w,), False)

    def test_ldexp(self):
        w = 16
        x, n, m = V(0), V(1), V(2)
        ld = op('G_FLDEXP', w, x, n)
        self.check(op('G_FLDEXP', w, x, ('const', 32, 0)), x, (w,))
        self.check(op('G_FLDEXP', w, x, ('const', 32, 1)),
                   op('G_FADD', w, x, x), (w,))
        self.check(op('G_FLDEXP', w, x, ('const', 32, 0xffffffff)),
                   op('G_FMUL', w, x, C(0.5, w)), (w,))
        self.check(op('G_FNEG', w, ld), op('G_FLDEXP', w, op(
            'G_FNEG', w, x), n), (w, 32))
        # The exponent is a signed integer: a zero extension is not a
        # sign extension, and a truncation loses a large exponent.
        self.check(op('G_FLDEXP', w, x, op('G_SEXT', 32, n)), ld, (w, 16))
        self.check(op('G_FLDEXP', w, x, op('G_ZEXT', 32, n)), ld, (w, 16),
                   False)
        self.check(op('G_FLDEXP', w, x, op('G_TRUNC', 8, n)), ld, (w, 32),
                   False)
        # Two scalings have two roundings (a subnormal result), and the
        # sum of the exponents can wrap.
        self.check(op('G_FLDEXP', w, ld, m),
                   op('G_FLDEXP', w, x, op('G_ADD', 32, n, m)),
                   (w, 32, 32), False)
        # The integer exponent is not a floating-point operand: a NaN
        # result does not get its bits.
        self.check(op('G_FLDEXP', 32, x, n), op('G_BITCAST', 32, n),
                   (32, 32), False)

    def test_frexp(self):
        w = 16
        x = V(0)
        fr, ex = op('G_FFREXP', w, x), op('G_FFREXP#1', 32, x)
        self.check(op('G_FFREXP', w, op('G_FNEG', w, x)),
                   op('G_FNEG', w, fr), (w,))
        # An exponent that is not specified (a NaN, an infinity) can be
        # each value in the replacement.
        self.check(op('G_FFREXP#1', 32, op('G_FNEG', w, x)), ex, (w,))
        self.check(op('G_FFREXP#1', 32, op('G_FABS', w, x)), ex, (w,))
        self.check(ex, ('const', 32, 0), (w,), False)
        # The exponent of a fraction is 0, and 0 is a correct value where
        # it is not specified.
        self.check(op('G_FFREXP#1', 32, fr), ('const', 32, 0), (w,))
        self.check(op('G_FFREXP#1', 32, fr), ('const', 32, 1), (w,), False)
        # The fraction of a fraction is the fraction.
        self.check(op('G_FFREXP', w, fr), fr, (w,))
        # The value is the fraction times 2 ** exponent. An infinity
        # stays one for each exponent.
        self.check(op('G_FLDEXP', w, fr, ex), x, (w,))
        self.check(op('G_FLDEXP', w, fr, op('G_ADD', 32, ex, (
            'const', 32, 1))), x, (w,), False)
        # An exponent of the width of the value is an integer: the bit
        # pattern of a NaN is a number.
        self.check(op('G_AND', 16, op('G_FFREXP#1', 16, x),
                      ('const', 16, 0xffff)), op('G_FFREXP#1', 16, x),
                   (w,))

    def test_subnormal_numbers(self):
        # With subnormal numbers, a difference is zero only for equal
        # values. The rule is correct for the IEEE treatment only.
        w = 16
        x, y = V(0), V(1)
        self.check(op('G_FCMP:oeq', 1, op('G_FSUB', w, x, y), C(0.0, w)),
                   op('G_FCMP:oeq', 1, x, y), (w, w), False)  # inf - inf
        self.check(op('G_FCMP:olt', 1, op('G_FSUB', w, x, y), C(0.0, w)),
                   op('G_FCMP:olt', 1, x, y), (w, w))


class GuardTest(unittest.TestCase):
    def rule(self, src, tgt):
        return {'source_json': ir.to_json(src),
                'replacement_json': ir.to_json(tgt)}

    def test_denormal_mode(self):
        w = 32
        x = V(0)
        self.assertTrue(emit.needs_ieee_denormal(self.rule(
            op('G_FMUL', w, x, C(1.0, w)), x)))
        self.assertTrue(emit.needs_ieee_denormal(self.rule(
            op('G_FNEG', w, op('G_FNEG', w, x)),
            op('G_FCANONICALIZE', w, x))))
        self.assertFalse(emit.needs_ieee_denormal(self.rule(
            op('G_FNEG', w, op('G_FNEG', w, x)), x)))
        self.assertFalse(emit.needs_ieee_denormal(self.rule(
            op('G_ADD', w, x, ('const', w, 0)), x)))


PARTS_MIR = '''
---
name: parts
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0, $vgpr1, $vgpr2
    %0:_(f32) = COPY $vgpr0
    %1:_(f32) = COPY $vgpr1
    %2:_(i32) = COPY $vgpr2
    %3:_(f32) = G_FNEG %0
    %4:_(f32) = G_FREM %3, %1
    %5:_(f32), %6:_(f32) = G_FMODF %4
    %7:_(i16) = G_TRUNC %2
    %8:_(f32) = G_FLDEXP %5, %7
    %9:_(f32), %10:_(i32) = G_FFREXP %8
    %11:_(i32) = G_ADD %10, %2
    %12:_(f32) = G_FADD %9, %6
    %13:_(f32) = G_FMA %12, %0, %1
    %14:_(f32) = G_FMINNUM %13, %0
    %15:_(f32) = G_INTRINSIC_ROUNDEVEN %14
    %16:_(i32) = G_INTRINSIC_LRINT %15
    $vgpr0 = COPY %11
    $vgpr1 = COPY %15
    $vgpr2 = COPY %16
    SI_RETURN implicit $vgpr0, implicit $vgpr1, implicit $vgpr2
...
'''


@unittest.skipUnless(HAVE_LLC, 'no llc (set GIRS_LLC)')
class RealExtractionTest(unittest.TestCase):
    """MIR through the extractor of the compiler to search instances."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        mir = os.path.join(cls.tmp.name, 'parts.mir')
        with open(mir, 'w') as f:
            f.write(PARTS_MIR)
        _, out = cli._extract_one(LLC, mir, cls.tmp.name, 'mir',
                                  targets.get('AMDGPU'))
        assert out, 'the extractor failed'
        cls.insts, cls.stats = corpus.load([out])

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _inst(self, expr):
        return next(i for i in self.insts if i.expr == expr)

    def test_each_operator_is_read(self):
        self.assertEqual(self.stats['unsupported'], 0)
        for n in ('G_FREM', 'G_FMODF', 'G_FLDEXP', 'G_FFREXP', 'G_FADD',
                  'G_FMA', 'G_FMINNUM', 'G_INTRINSIC_ROUNDEVEN',
                  'G_INTRINSIC_LRINT'):
            self.assertIn(n, self.stats['operators'], n)

    def test_results_and_kinds(self):
        # The exponent of G_FLDEXP is an integer of its own type.
        i = self._inst(op('G_FLDEXP', 32, V(0), V(1)))
        self.assertEqual((i.vk, i.input_types), (('f', 'i'), ('f32', 'i16')))
        # Each result of G_FFREXP and of G_FMODF is a tree of its own,
        # and the exponent is an integer.
        i = self._inst(op('G_ADD', 32, op('G_FFREXP#1', 32, V(0)), V(1)))
        self.assertEqual(i.vk, ('f', 'i'))
        self._inst(op('G_FFREXP', 32, op('G_FLDEXP', 32, V(0), V(1))))
        i = self._inst(op('G_FADD', 32, op('G_FFREXP', 32, V(0)),
                          op('G_FMODF#1', 32, V(1))))
        self.assertEqual(i.vk, ('f', 'f'))
        self._inst(op('G_FMODF', 32, op('G_FREM', 32, V(0), V(1))))


if __name__ == '__main__':
    unittest.main()
