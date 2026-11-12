#!/usr/bin/env python3
"""Tests of the models of the operators with bits that are not specified
(G_ANYEXT, G_IMPLICIT_DEF), of the hints (G_ASSERT_ZEXT, G_ASSERT_SEXT,
G_ASSERT_ALIGN), of G_BITCAST between an integer and a floating-point value,
and of the operations on the bits of a floating-point value (G_FNEG, G_FABS,
G_FCOPYSIGN, G_FCMP, G_IS_FPCLASS).

Run:  python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests
"""

import os
import struct
import subprocess
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import z3  # noqa: E402

from girs import (corpus, discover, fp, ir, ops, precond,  # noqa: E402
                  select, smt, synth, targets)

LLC = os.environ.get('GIRS_LLC') or os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(ROOT))), 'build', 'bin',
    'llc')
HAVE_LLC = os.path.exists(LLC)


def V(i):
    return ('var', i)


def L(w, k):
    """The constant k of w bits."""
    k &= (1 << w) - 1
    for name in ir.LITERALS:
        if ir.lit_value(w, name) == k:
            return ('lit', w, name)
    return ('const', w, k)


def op(name, w, *args):
    return (name, w) + args


def refines(src, tgt, vw, guard=None):
    enc = smt.Encoder(vw, src[1])
    g = z3.BoolVal(True) if guard is None else precond.z3_pred(guard, enc)
    f = smt.refinement_violation(enc, src, tgt, g)
    return smt.Z3Backend().check(f).status == 'unsat'


_PACK = {16: ('<e', '<H'), 32: ('<f', '<I'), 64: ('<d', '<Q')}


def bits(x, w):
    f, i = _PACK[w]
    return struct.unpack(i, struct.pack(f, x))[0]


class UnspecifiedBitsTest(unittest.TestCase):
    def test_registry(self):
        for n in ('G_ANYEXT', 'G_IMPLICIT_DEF'):
            self.assertTrue(ops.has_unspecified(n), n)
            self.assertEqual(ops.REGISTRY[n].lhs(), 'yes')
        self.assertEqual(ops.REGISTRY['G_ANYEXT'].rhs(), 'yes')
        # A rule matches a value without specified bits and does not
        # create one.
        self.assertNotEqual(ops.REGISTRY['G_IMPLICIT_DEF'].rhs(), 'yes')
        self.assertTrue(ops.REGISTRY['G_ANYEXT'].typecheck(32, [8], None, 0))
        self.assertFalse(ops.REGISTRY['G_ANYEXT'].typecheck(8, [8], None, 0))

    def test_low_bits_are_the_operand(self):
        x = op('G_ANYEXT', 32, V(0))
        self.assertTrue(refines(op('G_TRUNC', 8, x), V(0), (8,)))
        self.assertTrue(refines(op('G_AND', 32, x, L(32, 255)),
                                op('G_ZEXT', 32, V(0)), (8,)))
        self.assertTrue(refines(op('G_SEXT_INREG:8', 32, x),
                                op('G_SEXT', 32, V(0)), (8,)))

    def test_high_bits_are_some_value(self):
        """The source can have each value: an extension that gives one of
        them is a correct replacement, and the other direction is not."""
        a = op('G_ANYEXT', 32, V(0))
        for ext in ('G_ZEXT', 'G_SEXT'):
            self.assertTrue(refines(a, op(ext, 32, V(0)), (8,)), ext)
            self.assertFalse(refines(op(ext, 32, V(0)), a, (8,)), ext)
        # The replacement can have the value that the source has if its
        # high bits are zero.
        self.assertTrue(refines(op('G_LSHR', 32, a, L(32, 8)), L(32, 0),
                                (8,)))
        self.assertTrue(refines(op('G_AND', 32, a, L(32, 256)), L(32, 0),
                                (8,)))
        # A bit of the operand is not such a bit.
        self.assertFalse(refines(op('G_LSHR', 32, a, L(32, 7)), L(32, 0),
                                 (8,)))
        self.assertFalse(refines(op('G_AND', 32, a, L(32, 255)), L(32, 0),
                                 (8,)))
        # No value of the high bits makes the source another operand.
        self.assertFalse(refines(a, op('G_ZEXT', 32, V(1)), (8, 8)))

    def test_one_term_of_the_source_has_one_value(self):
        """Two matches of one term can be one instruction: the proof does
        not use two values for it."""
        a = op('G_ANYEXT', 32, V(0))
        self.assertTrue(refines(op('G_SUB', 32, a, a), L(32, 0), (8,)))
        self.assertTrue(refines(op('G_XOR', 32, a, a), L(32, 0), (8,)))

    def test_each_occurrence_of_the_replacement_has_its_value(self):
        """The replacement builds an instruction per occurrence: the proof
        holds for each value of each of them."""
        a = op('G_ANYEXT', 32, V(0))
        z = op('G_ZEXT', 32, V(0))
        self.assertFalse(refines(L(32, 0), op('G_SUB', 32, a, a), (8,)))
        self.assertFalse(refines(op('G_ADD', 32, z, z),
                                 op('G_ADD', 32, a, a), (8,)))
        # The low bits are the same for each value.
        self.assertTrue(refines(
            op('G_TRUNC', 8, op('G_ADD', 32, z, z)),
            op('G_TRUNC', 8, op('G_ADD', 32, a, a)), (8,)))

    def test_anyext_through_an_operation(self):
        """anyext(x) + anyext(y) -> anyext(x + y): each value of the high
        bits of the replacement is a value that the source can have."""
        a, b = op('G_ANYEXT', 32, V(0)), op('G_ANYEXT', 32, V(1))
        self.assertTrue(refines(
            op('G_TRUNC', 8, op('G_ADD', 32, a, b)),
            op('G_ADD', 8, V(0), V(1)), (8, 8)))
        self.assertTrue(refines(
            op('G_ANYEXT', 64, op('G_ANYEXT', 32, V(0))),
            op('G_ANYEXT', 64, V(0)), (8,)))
        self.assertTrue(refines(
            op('G_ANYEXT', 64, op('G_ZEXT', 32, V(0))),
            op('G_ZEXT', 64, V(0)), (8,)))
        # zext(anyext x) has zeros above 32 bits; anyext does not.
        self.assertFalse(refines(
            op('G_ZEXT', 64, op('G_ANYEXT', 32, V(0))),
            op('G_ANYEXT', 64, V(0)), (8,)))

    def test_implicit_def(self):
        u = ('G_IMPLICIT_DEF', 32)
        self.assertEqual(ops.parse(u[0])[0].typecheck(32, [], None, 0), True)
        # Some value: x & undef can be 0, x | undef can be -1.
        self.assertTrue(refines(op('G_AND', 32, V(0), u), L(32, 0), (32,)))
        self.assertTrue(refines(op('G_OR', 32, V(0), u), L(32, -1), (32,)))
        self.assertTrue(refines(op('G_ADD', 32, V(0), u), V(0), (32,)))
        # One term has one value.
        self.assertTrue(refines(op('G_XOR', 32, u, u), L(32, 0), (32,)))
        # x * undef is not each value (if x is even, the product is even).
        self.assertFalse(refines(op('G_MUL', 32, V(0), u), L(32, 1), (32,)))
        # A constant is not a correct source for a value without bits.
        self.assertFalse(refines(L(32, 0), op('G_ANYEXT', 32, V(0)), (8,)))

    def test_evaluator_gives_ones(self):
        self.assertEqual(ir.evaluate(op('G_ANYEXT', 32, V(0)), (8,), (0x12,)),
                         0xffffff12)
        self.assertEqual(ir.evaluate(('G_IMPLICIT_DEF', 16), (), ()), 0xffff)


class HintTest(unittest.TestCase):
    def test_registry(self):
        for n in ('G_ASSERT_ZEXT', 'G_ASSERT_SEXT', 'G_ASSERT_ALIGN'):
            info = ops.REGISTRY[n]
            self.assertEqual(info.lhs(), 'yes')
            self.assertNotEqual(info.rhs(), 'yes')
            self.assertEqual(info.cost, 0)
        tc = ops.REGISTRY['G_ASSERT_ZEXT'].typecheck
        self.assertTrue(tc(32, [32], 8, 0))
        self.assertFalse(tc(32, [32], 32, 0))
        self.assertFalse(tc(32, [32], 0, 0))

    def test_evaluator(self):
        z = op('G_ASSERT_ZEXT:8', 32, V(0))
        s = op('G_ASSERT_SEXT:8', 32, V(0))
        a = op('G_ASSERT_ALIGN:8', 32, V(0))
        self.assertEqual(ir.evaluate(z, (32,), (0xff,)), 0xff)
        self.assertIsNone(ir.evaluate(z, (32,), (0x100,)))
        self.assertEqual(ir.evaluate(s, (32,), (0xffffff80,)), 0xffffff80)
        self.assertEqual(ir.evaluate(s, (32,), (0x7f,)), 0x7f)
        self.assertIsNone(ir.evaluate(s, (32,), (0x80,)))
        self.assertEqual(ir.evaluate(a, (32,), (0x18,)), 0x18)
        self.assertIsNone(ir.evaluate(a, (32,), (0x14,)))
        # An alignment of 1 is no condition.
        self.assertEqual(ir.evaluate(op('G_ASSERT_ALIGN:1', 32, V(0)),
                                     (32,), (7,)), 7)

    def test_hint_is_a_fact(self):
        z = op('G_ASSERT_ZEXT:8', 32, V(0))
        self.assertTrue(refines(op('G_AND', 32, z, L(32, 255)), z, (32,)))
        self.assertTrue(refines(op('G_AND', 32, z, L(32, 255)), V(0),
                                (32,)))
        self.assertTrue(refines(op('G_LSHR', 32, z, L(32, 8)), L(32, 0),
                                (32,)))
        self.assertFalse(refines(op('G_LSHR', 32, z, L(32, 7)), L(32, 0),
                                 (32,)))
        s = op('G_ASSERT_SEXT:8', 32, V(0))
        self.assertTrue(refines(op('G_SEXT_INREG:8', 32, s), V(0), (32,)))
        self.assertFalse(refines(op('G_SEXT_INREG:7', 32, s), V(0), (32,)))
        a = op('G_ASSERT_ALIGN:8', 32, V(0))
        self.assertTrue(refines(op('G_AND', 32, a, L(32, 7)), L(32, 0),
                                (32,)))
        self.assertFalse(refines(op('G_AND', 32, a, L(32, 8)), L(32, 0),
                                 (32,)))

    def test_hint_can_go_and_cannot_come(self):
        z = op('G_ASSERT_ZEXT:8', 32, V(0))
        # Correct, and without a gain: a hint costs nothing.
        self.assertTrue(refines(z, V(0), (32,)))
        self.assertEqual(ir.cost(z), 0)
        # The replacement must not be poison where the source is a value.
        self.assertFalse(refines(V(0), z, (32,)))

    def test_no_replacement_for_a_hint_alone(self):
        z = op('G_ASSERT_ZEXT:8', 32, V(0))
        inst = corpus.Instance(z, (32,), [(0, 0)], [None], [], [],
                               [('f', 'fn', '%0')])
        cands, st = discover.discover(inst, smt.Z3Backend(),
                                      discover.Limits())
        self.assertEqual(cands, [])


class BitcastTest(unittest.TestCase):
    def test_kinds(self):
        info = ops.REGISTRY['G_BITCAST']
        self.assertEqual(info.result_kind(['i']), 'f')
        self.assertEqual(info.result_kind(['f']), 'i')
        self.assertTrue(info.typecheck(32, [32], None, 0))
        self.assertFalse(info.typecheck(32, [64], None, 0))
        # No floating-point format of 8 bits.
        self.assertFalse(info.typecheck(8, [8], None, 0))

    def test_the_bits_do_not_change(self):
        # Variable 0 is an integer: bitcast to float and back.
        x = op('G_BITCAST', 32, op('G_BITCAST', 32, V(0)))
        self.assertTrue(refines(x, V(0), (32,)))
        # fneg(bitcast x) is the integer with the other sign bit.
        self.assertTrue(refines(
            op('G_BITCAST', 32, op('G_FNEG', 32, op('G_BITCAST', 32, V(0)))),
            op('G_XOR', 32, V(0), L(32, 0x80000000)), (32,)))
        self.assertTrue(refines(
            op('G_BITCAST', 32, op('G_FABS', 32, op('G_BITCAST', 32, V(0)))),
            op('G_AND', 32, V(0), L(32, 0x7fffffff)), (32,)))
        self.assertFalse(refines(
            op('G_BITCAST', 32, op('G_FABS', 32, op('G_BITCAST', 32, V(0)))),
            V(0), (32,)))

    def test_nan_of_a_conversion_through_a_bitcast(self):
        """The bits of a NaN that G_FPEXT makes are not specified: the
        integer that has them is not one value."""
        # Variable 0 is a floating-point value (operand of G_FPEXT).
        e = op('G_FPEXT', 64, V(0))
        src = op('G_BITCAST', 64, e)
        self.assertTrue(refines(src, src, (32,)))
        # The exponent of a NaN is all ones for each payload.
        hi = op('G_LSHR', 64, src, L(64, 52))
        self.assertTrue(refines(op('G_LSHR', 64, hi, L(64, 12)), L(64, 0),
                                (32,)))


class SignOperationTest(unittest.TestCase):
    def test_evaluator(self):
        for w in (16, 32, 64):
            for x in (0.0, -0.0, 1.5, -2.5):
                b = bits(x, w)
                self.assertEqual(ir.evaluate(op('G_FNEG', w, V(0)), (w,),
                                             (b,)), bits(-x, w))
                self.assertEqual(ir.evaluate(op('G_FABS', w, V(0)), (w,),
                                             (b,)), bits(abs(x), w))
        # The sign of a NaN changes, its payload does not.
        n = fp.qnan(32) | 5
        self.assertEqual(ir.evaluate(op('G_FNEG', 32, V(0)), (32,), (n,)),
                         n | 0x80000000)
        # The sign comes from a value of another format.
        self.assertEqual(ir.evaluate(op('G_FCOPYSIGN', 32, V(0), V(1)),
                                     (32, 64), (bits(1.5, 32),
                                                bits(-0.0, 64))),
                         bits(-1.5, 32))

    def test_identities(self):
        x = V(0)
        n = op('G_FNEG', 32, x)
        a = op('G_FABS', 32, x)
        self.assertTrue(refines(op('G_FNEG', 32, n), x, (32,)))
        self.assertTrue(refines(op('G_FABS', 32, n), a, (32,)))
        self.assertTrue(refines(op('G_FABS', 32, a), a, (32,)))
        self.assertTrue(refines(op('G_FCOPYSIGN', 32, x, x), x, (32,)))
        self.assertTrue(refines(op('G_FCOPYSIGN', 32, n, V(1)),
                                op('G_FCOPYSIGN', 32, x, V(1)), (32, 64)))
        self.assertTrue(refines(op('G_FCOPYSIGN', 32, x, op('G_FABS', 64,
                                                            V(1))),
                                a, (32, 64)))
        self.assertFalse(refines(n, x, (32,)))
        self.assertFalse(refines(op('G_FABS', 32, x), x, (32,)))
        self.assertFalse(refines(op('G_FCOPYSIGN', 32, x, V(1)), x,
                                 (32, 32)))

    def test_sign_of_a_nan_that_an_operation_made(self):
        """fneg(fpext x) -> fpext(fneg x): the NaN of the source has bits
        that are not specified, also after the negation."""
        self.assertTrue(refines(
            op('G_FNEG', 64, op('G_FPEXT', 64, V(0))),
            op('G_FPEXT', 64, op('G_FNEG', 32, V(0))), (32,)))
        # The NaN of fabs(fpext x) is positive; fpext(fabs x) gives each
        # NaN.
        self.assertTrue(refines(
            op('G_FPEXT', 64, op('G_FABS', 32, V(0))),
            op('G_FABS', 64, op('G_FPEXT', 64, V(0))), (32,)))
        self.assertFalse(refines(
            op('G_FABS', 64, op('G_FPEXT', 64, V(0))),
            op('G_FPEXT', 64, op('G_FABS', 32, V(0))), (32,)))
        # One operation on each side reads the bits of the NaN.
        e = op('G_FABS', 64, op('G_FPEXT', 64, V(0)))
        self.assertTrue(refines(e, e, (32,)))
        self.assertTrue(refines(op('G_FABS', 64, e), e, (32,)))


class CompareAndClassTest(unittest.TestCase):
    def test_compare_evaluator(self):
        one, two, nan = bits(1.0, 32), bits(2.0, 32), fp.qnan(32)
        pz, nz = bits(0.0, 32), bits(-0.0, 32)

        def cmp(pred, a, b):
            return ir.evaluate(op('G_FCMP:' + pred, 1, V(0), V(1)),
                               (32, 32), (a, b))
        self.assertEqual(cmp('olt', one, two), 1)
        self.assertEqual(cmp('ogt', one, two), 0)
        self.assertEqual(cmp('oeq', pz, nz), 1)
        self.assertEqual(cmp('une', pz, nz), 0)
        # A NaN operand: an ordered predicate is false, an unordered one
        # is true.
        for p in ('oeq', 'ogt', 'oge', 'olt', 'ole', 'one', 'ord'):
            self.assertEqual(cmp(p, nan, one), 0, p)
        for p in ('ueq', 'ugt', 'uge', 'ult', 'ule', 'une', 'uno'):
            self.assertEqual(cmp(p, one, nan), 1, p)
        self.assertEqual(cmp('true', nan, nan), 1)
        self.assertEqual(cmp('false', one, one), 0)

    def test_compare_identities(self):
        x, y = V(0), V(1)

        def c(pred, a, b):
            return op('G_FCMP:' + pred, 1, a, b)
        self.assertTrue(refines(c('olt', x, y), c('ogt', y, x), (32, 32)))
        self.assertTrue(refines(c('uno', x, x), c('une', x, x), (32,)))
        self.assertTrue(refines(c('oeq', x, x), c('ord', x, x), (32,)))
        self.assertTrue(refines(
            op('G_XOR', 1, c('olt', x, y), L(1, 1)), c('uge', x, y),
            (32, 32)))
        # The sign of a zero is not a part of the comparison.
        self.assertTrue(refines(c('oeq', op('G_FABS', 32, x), L(32, 0)),
                                c('oeq', x, L(32, 0)), (32,)))
        # x == x is false for a NaN; not(olt) is not oge.
        self.assertFalse(refines(c('oeq', x, x), L(1, 1), (32,)))
        self.assertFalse(refines(
            op('G_XOR', 1, c('olt', x, y), L(1, 1)), c('oge', x, y),
            (32, 32)))
        # An integer comparison of the bits is not the comparison.
        self.assertFalse(refines(c('oeq', x, y),
                                 op('G_ICMP:eq', 1, x, y), (32, 32)))

    def test_class(self):
        nan_set = fp.FC_SNAN | fp.FC_QNAN

        def cls(mask, v, w=32):
            return ir.evaluate(op('G_IS_FPCLASS:%d' % mask, 1, V(0)), (w,),
                               (v,))
        self.assertEqual(cls(nan_set, fp.qnan(32)), 1)
        self.assertEqual(cls(fp.FC_QNAN, fp.qnan(32)), 1)
        self.assertEqual(cls(fp.FC_SNAN, fp.qnan(32)), 0)
        self.assertEqual(cls(fp.FC_PINF, fp.inf(32)), 1)
        self.assertEqual(cls(fp.FC_NINF, fp.inf(32)), 0)
        self.assertEqual(cls(fp.FC_NZERO, bits(-0.0, 32)), 1)
        self.assertEqual(cls(fp.FC_PSUB, 1), 1)
        self.assertEqual(cls(fp.FC_PNORM, bits(1.0, 64), 64), 1)
        self.assertEqual(cls(fp.FC_ALL, bits(-3.0, 16), 16), 1)
        x = V(0)
        self.assertTrue(refines(
            op('G_IS_FPCLASS:%d' % nan_set, 1, x),
            op('G_FCMP:uno', 1, x, x), (32,)))
        self.assertTrue(refines(
            op('G_IS_FPCLASS:%d' % nan_set, 1, op('G_FNEG', 32, x)),
            op('G_IS_FPCLASS:%d' % nan_set, 1, x), (32,)))
        self.assertTrue(refines(
            op('G_IS_FPCLASS:%d' % fp.FC_NINF, 1, op('G_FNEG', 32, x)),
            op('G_IS_FPCLASS:%d' % fp.FC_PINF, 1, x), (32,)))
        self.assertFalse(refines(
            op('G_IS_FPCLASS:%d' % fp.FC_QNAN, 1, x),
            op('G_FCMP:uno', 1, x, x), (32,)))

    def test_class_of_a_nan_that_an_operation_made(self):
        """A conversion of a signaling NaN gives a quiet NaN or the NaN
        unchanged, and a conversion of a quiet NaN gives a quiet NaN."""
        e = op('G_FPEXT', 64, V(0))
        nan_set = fp.FC_SNAN | fp.FC_QNAN

        def cls(mask, x):
            return op('G_IS_FPCLASS:%d' % mask, 1, x)
        self.assertTrue(refines(cls(nan_set, e), cls(nan_set, V(0)), (32,)))
        self.assertTrue(refines(cls(fp.FC_QNAN, e), cls(fp.FC_QNAN, V(0)),
                                (32,)))
        # The source can make each NaN quiet.
        self.assertTrue(refines(cls(fp.FC_QNAN, e), cls(nan_set, V(0)),
                                (32,)))
        self.assertTrue(refines(cls(fp.FC_SNAN, e), L(1, 0), (32,)))
        # It cannot make a quiet NaN signaling.
        self.assertFalse(refines(cls(fp.FC_SNAN, e), cls(nan_set, V(0)),
                                 (32,)))
        self.assertFalse(refines(cls(fp.FC_QNAN, e), L(1, 0), (32,)))


class NaNSetTest(unittest.TestCase):
    """The NaN values that an operation can give (LangRef, "Behavior of
    Floating-Point NaN values")."""

    def test_member(self):
        q, s_ = fp.qnan(32) | 5, (fp.qnan(32) ^ (1 << 22)) | 5
        self.assertTrue(fp.is_quiet(q, 32))
        self.assertFalse(fp.is_quiet(s_, 32))
        ops_ = [(q, 32)]
        # Preferred, with each sign.
        self.assertTrue(fp.nan_member(fp.qnan(32), 32, ops_))
        self.assertTrue(fp.nan_member(fp.qnan(32) | 1 << 31, 32, ops_))
        # The payload of the operand, quiet.
        self.assertTrue(fp.nan_member(q, 32, ops_))
        self.assertFalse(fp.nan_member(q + 1, 32, ops_))
        # No signaling NaN from a quiet operand.
        self.assertFalse(fp.nan_member(s_, 32, ops_))
        self.assertTrue(fp.nan_member(s_, 32, [(s_, 32)]))
        self.assertTrue(fp.nan_member(q, 32, [(s_, 32)]))
        # No operand that is a NaN: the preferred NaN only.
        self.assertFalse(fp.nan_member(q, 32, [(0x3f800000, 32)]))
        self.assertFalse(fp.nan_member(0x3f800000, 32, ops_))
        # A conversion keeps the first bits of the payload.
        self.assertEqual(fp.nan_payload(q, 32, 64), 5 << 29)
        self.assertTrue(fp.nan_member(fp.qnan(64) | 5 << 29, 64, ops_))
        self.assertFalse(fp.nan_member(fp.qnan(64) | 5, 64, ops_))
        self.assertTrue(fp.nan_member(q, 32, [(fp.qnan(64) | 5 << 29 | 3,
                                               64)]))

    def test_formula_is_the_function(self):
        import random
        rnd = random.Random(1)
        nans = lambda w: [fp.qnan(w), fp.qnan(w) | 1 << (w - 1),  # noqa
                          fp.qnan(w) | 5, (fp.qnan(w) | 5) ^
                          1 << (fp.FORMATS[w][1] - 2), fp.inf(w),
                          fp.inf(w) | 1, 1 << (w - 2)]
        for w, aw in ((32, 32), (64, 32), (32, 64), (16, 64), (64, 16)):
            c, a = z3.BitVec('c', w), z3.BitVec('a', aw)
            f = fp.z3_nan_member(c, [a])
            for _ in range(200):
                cv = rnd.choice(nans(w) + [rnd.getrandbits(w) |
                                           fp.inf(w)])
                av = rnd.choice(nans(aw) + [rnd.getrandbits(aw) |
                                            fp.inf(aw)])
                if rnd.random() < 0.3:
                    # A member: the payload of the operand.
                    cv = fp.inf(w) | fp.nan_payload(av, aw, w) | \
                        rnd.getrandbits(1) << (fp.FORMATS[w][1] - 2)
                got = z3.is_true(z3.simplify(z3.substitute(
                    f, (c, z3.BitVecVal(cv, w)), (a, z3.BitVecVal(av, aw)))))
                self.assertEqual(got, fp.nan_member(cv, w, [(av, aw)]),
                                 (w, aw, hex(cv), hex(av)))

    @staticmethod
    def _proved(src, tgt, vw, known=None):
        """``known``: the value of variable 0, as known bits."""
        enc = smt.Encoder(vw, src[1])
        guard = z3.BoolVal(True) if known is None else z3.And(
            enc.ko[0] == known, enc.kz[0] == ~known & ((1 << vw[0]) - 1))
        f = smt.refinement_violation(enc, src, tgt, guard)
        return smt.Z3Backend().check(f).status == 'unsat'

    def test_payload_of_the_operand_goes_through(self):
        """fptrunc(fpext x) -> x: the source can give the NaN x back."""
        src = op('G_FPTRUNC', 32, op('G_FPEXT', 64, V(0)))
        self.assertTrue(self._proved(src, V(0), (32,)))
        # x is a NaN constant: its payload or the payload zero, not
        # another payload.
        x = fp.qnan(32) | 5
        self.assertTrue(self._proved(src, L(32, x), (32,), x))
        self.assertTrue(self._proved(src, L(32, fp.qnan(32)), (32,), x))
        self.assertTrue(self._proved(src, L(32, x | 1 << 31), (32,), x))
        self.assertFalse(self._proved(src, L(32, fp.qnan(32) | 7), (32,), x))

    def test_no_new_payload(self):
        """fpext(x) for a NaN x is not each NaN: the constant with all
        bits one is a NaN with a payload that x does not give."""
        e = op('G_FPEXT', 64, V(0))
        x = 0xffffffff
        self.assertFalse(self._proved(e, L(64, -1), (32,), x))
        # The first bits of the payload are the payload of x.
        self.assertTrue(self._proved(e, L(64, 0xffffffffe0000000), (32,),
                                     x))
        self.assertTrue(self._proved(e, L(64, fp.qnan(64)), (32,), x))


class SearchTest(unittest.TestCase):
    def _find(self, src, vw, grammar='source', consts=None):
        n = len(vw)
        consts = consts or [None] * n
        facts = [(0, 0) if c is None else (~c & ((1 << w) - 1), c)
                 for c, w in zip(consts, vw)]
        inst = corpus.Instance(src, vw, facts, consts, [], [],
                               [('f', 'fn', '%0')])
        cands, _ = discover.discover(inst, smt.Z3Backend(),
                                     discover.Limits(grammar=grammar))
        return [c['tgt'] for c in cands]

    def test_trunc_of_anyext(self):
        src = op('G_TRUNC', 8, op('G_ANYEXT', 32, V(0)))
        self.assertIn(V(0), self._find(src, (8,)))

    def test_mask_of_anyext_is_a_zext(self):
        src = op('G_AND', 32, op('G_ANYEXT', 32, V(0)), V(1))
        self.assertIn(op('G_ZEXT', 32, V(0)),
                      self._find(src, (8, 32), grammar='all',
                                 consts=[None, 255]))

    def test_double_negation(self):
        src = op('G_FNEG', 32, op('G_FNEG', 32, V(0)))
        self.assertIn(V(0), self._find(src, (32,)))

    def test_abs_of_negation(self):
        src = op('G_FABS', 32, op('G_FNEG', 32, V(0)))
        self.assertIn(op('G_FABS', 32, V(0)), self._find(src, (32,)))


@unittest.skipUnless(HAVE_LLC, 'no llc (set GIRS_LLC)')
class ProbeTest(unittest.TestCase):
    """The function that selection runs a rule on is valid MIR."""

    def _probe(self, src, tgt, vw):
        s = synth.Synthesizer(smt.Z3Backend())
        n = len(vw)
        inst = corpus.Instance(src, vw, [(0, 0)] * n, [None] * n, [], [],
                               [('f', 'fn', '%0')])
        self.assertIsNotNone(s.add(inst, tgt))
        s.finalize([inst])
        (rule,) = s.rules.values()
        (name, ex), = select.examples(rule)
        mir = select.build_mir(rule, ex, name, targets.get('AMDGPU'))
        p = subprocess.run(
            [LLC, '-mtriple=amdgcn-amd-amdhsa', '-x', 'mir',
             '-run-pass=none', '-verify-machineinstrs', '-o', '/dev/null',
             '-'], input=mir, capture_output=True, text=True)
        self.assertEqual(p.returncode, 0, p.stderr)
        return mir

    def test_float_predicate(self):
        mir = self._probe(
            op('G_FCMP:olt', 1, op('G_FNEG', 32, V(0)),
               op('G_FNEG', 32, V(1))),
            op('G_FCMP:ogt', 1, V(0), V(1)), (32, 32))
        self.assertIn('G_FCMP floatpred(olt)', mir)

    def test_bitcast_has_two_types(self):
        mir = self._probe(
            op('G_BITCAST', 32, op('G_FABS', 32, op('G_BITCAST', 32, V(0)))),
            op('G_AND', 32, V(0), L(32, 0x7fffffff)), (32,))
        self.assertIn(':_(f32) = G_BITCAST', mir)
        self.assertIn(':_(i32) = G_BITCAST', mir)


if __name__ == '__main__':
    unittest.main()
