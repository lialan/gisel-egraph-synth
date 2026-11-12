#!/usr/bin/env python3
"""Tests of the models of G_FREEZE and of the conversions between integers
and floating-point values.

Run:  python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests
"""

import os
import struct
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import z3  # noqa: E402

from girs import (corpus, discover, emit, fp, ir, ops, precond,  # noqa: E402
                  smt, synth)


def V(i):
    return ('var', i)


def L(w, k):
    return ('lit', w, k)


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


class FormatTest(unittest.TestCase):
    def test_encode_is_the_machine_format(self):
        for w in (16, 32, 64):
            for x in (0.0, 1.0, -1.0, 0.5, 2.5, -2.5, 1000.0, 65504.0,
                      1e-5, 3.0e-5, 0.1, 1.0 / 3):
                try:
                    want = bits(x, w)
                except OverflowError:
                    continue
                kind, sign, val = fp.decode(want, w)
                self.assertEqual(kind, 'num')
                self.assertEqual(fp.encode(sign, abs(val), w), want)

    def test_rounding_to_nearest_even(self):
        # 2^24 + 1 is a tie between two floats.
        self.assertEqual(fp.from_int((1 << 24) + 1, 32), bits(16777216.0, 32))
        self.assertEqual(fp.from_int((1 << 24) + 3, 32), bits(16777220.0, 32))
        self.assertEqual(fp.from_int(-3, 16), bits(-3.0, 16))
        # Too large for a half: infinity.
        self.assertEqual(fp.from_int(65520, 16), fp.inf(16))
        self.assertEqual(fp.from_int(65519, 16), bits(65504.0, 16))

    def test_subnormal_numbers(self):
        tiny = 1                       # the smallest positive float
        self.assertEqual(fp.convert(fp.convert(tiny, 32, 64), 64, 32), tiny)
        # Half of it is a tie that rounds to the even neighbour, zero.
        half = bits(2.0 ** -150, 64)
        self.assertEqual(fp.convert(half, 64, 32), 0)

    def test_to_int(self):
        f = lambda x: bits(x, 32)
        self.assertEqual(fp.to_int(f(2.75), 32, 8, True, False), 2)
        self.assertEqual(fp.to_int(f(-2.75), 32, 8, True, False), 0xfe)
        self.assertEqual(fp.to_int(f(-0.5), 32, 8, False, False), 0)
        self.assertIsNone(fp.to_int(f(-1.0), 32, 8, False, False))
        self.assertIsNone(fp.to_int(f(128.0), 32, 8, True, False))
        self.assertEqual(fp.to_int(f(-128.9), 32, 8, True, False), 0x80)
        self.assertIsNone(fp.to_int(fp.qnan(32), 32, 8, True, False))
        self.assertEqual(fp.to_int(fp.qnan(32), 32, 8, True, True), 0)
        self.assertEqual(fp.to_int(fp.inf(32), 32, 8, True, True), 0x7f)
        self.assertEqual(fp.to_int(fp.inf(32, 1), 32, 8, True, True), 0x80)
        self.assertEqual(fp.to_int(f(1000.0), 32, 8, False, True), 0xff)
        self.assertEqual(fp.to_int(f(-7.0), 32, 8, False, True), 0)

    def test_registry(self):
        for name in ('G_FPEXT', 'G_FPTRUNC', 'G_SITOFP', 'G_UITOFP',
                     'G_FPTOSI', 'G_FPTOUI', 'G_FPTOSI_SAT', 'G_FPTOUI_SAT'):
            info = ops.REGISTRY[name]
            for stage in ops.STAGES:
                self.assertIn(ops.capability(info, stage),
                              ('yes', 'enumerative+egraph'),
                              (name, stage))
        tc = ops.REGISTRY['G_FPEXT'].typecheck
        self.assertTrue(tc(64, [32], None, 0))
        self.assertFalse(tc(32, [64], None, 0))
        self.assertFalse(tc(32, [8], None, 0))     # no format of 8 bits
        self.assertTrue(ops.REGISTRY['G_SITOFP'].typecheck(32, [1], None, 0))
        self.assertFalse(ops.REGISTRY['G_FPTOSI'].typecheck(32, [8], None, 0))


class ConversionProofTest(unittest.TestCase):
    def test_integer_through_a_format_that_has_it(self):
        f = op('G_SITOFP', 32, V(0))
        self.assertTrue(refines(op('G_FPTOSI', 16, f), V(0), (16,)))
        self.assertTrue(refines(op('G_FPTOSI', 32, f),
                                op('G_SEXT', 32, V(0)), (16,)))
        self.assertTrue(refines(op('G_FPTOSI_SAT', 32, f),
                                op('G_SEXT', 32, V(0)), (16,)))
        self.assertTrue(refines(op('G_FPEXT', 64, f),
                                op('G_SITOFP', 64, V(0)), (16,)))
        # The unsigned reading of the same bits is another number.
        self.assertFalse(refines(op('G_FPTOSI', 32, f),
                                 op('G_ZEXT', 32, V(0)), (16,)))

    def test_integer_through_a_format_that_does_not_have_it(self):
        f = op('G_SITOFP', 32, V(0))
        self.assertFalse(refines(op('G_FPTOSI', 32, f), V(0), (32,)))
        self.assertFalse(refines(op('G_FPEXT', 64, f),
                                 op('G_SITOFP', 64, V(0)), (32,)))
        # G_FPTOSI is poison for a number outside of the range of an s16;
        # the saturating conversion is not.
        self.assertTrue(refines(op('G_FPTOSI', 16, f),
                                op('G_TRUNC', 16, V(0)), (32,)))
        self.assertFalse(refines(op('G_FPTOSI_SAT', 16, f),
                                 op('G_TRUNC', 16, V(0)), (32,)))

    def test_extension_is_exact(self):
        e = op('G_FPEXT', 64, V(0))
        # Also for a NaN: the payload of the result is not specified.
        self.assertTrue(refines(op('G_FPTRUNC', 32, e), V(0), (32,)))
        self.assertTrue(refines(op('G_FPTOSI', 32, e),
                                op('G_FPTOSI', 32, V(0)), (32,)))
        self.assertTrue(refines(
            op('G_FPEXT', 64, op('G_FPEXT', 32, V(0))),
            op('G_FPEXT', 64, V(0)), (16,)))
        # A truncation is not exact.
        self.assertFalse(refines(
            op('G_FPEXT', 64, op('G_FPTRUNC', 32, V(0))), V(0), (64,)))

    def test_nan_of_an_input_keeps_its_bits(self):
        # fptrunc(fpext y) is y for each number, and some NaN for a NaN.
        conv = op('G_FPTRUNC', 32, op('G_FPEXT', 64, V(1)))
        src = op('G_SELECT', 32, V(0), conv, V(1))
        # y is one of the NaNs that the conversion can give.
        self.assertTrue(refines(src, V(1), (1, 32)))
        # The conversion can change the payload of the NaN that the source
        # gives unchanged for a false condition.
        self.assertFalse(refines(src, conv, (1, 32)))
        both = op('G_SELECT', 32, V(0), conv,
                  op('G_FPTRUNC', 32, op('G_FPEXT', 64, V(2))))
        self.assertTrue(refines(
            both, op('G_FPTRUNC', 32, op('G_FPEXT', 64, op(
                'G_SELECT', 32, V(0), V(1), V(2)))), (1, 32, 32)))

    def test_poison_of_the_replacement(self):
        # The saturating conversion is defined where G_FPTOSI is poison,
        # not the other way.
        sat, plain = op('G_FPTOSI_SAT', 32, V(0)), op('G_FPTOSI', 32, V(0))
        self.assertTrue(refines(plain, sat, (32,)))
        self.assertFalse(refines(sat, plain, (32,)))

    def test_kinds(self):
        src = op('G_FPTOSI', 32, op('G_SITOFP', 32, V(0)))
        self.assertEqual(ir.result_kind(src), 'i')
        self.assertEqual(ir.result_kind(src[2]), 'f')
        self.assertEqual(ir.var_kinds(src), {0: 'i'})
        sel = op('G_SELECT', 32, V(0), V(1), op('G_FPEXT', 32, V(2)))
        self.assertEqual(ir.result_kind(sel), 'f')
        self.assertEqual(ir.var_kinds(sel), {0: 'i', 1: 'f', 2: 'f'})
        both = op('G_ADD', 32, V(0), op('G_FPTOSI', 32, V(0)))
        self.assertEqual(ir.var_kinds(both), {0: 'x'})


class FreezeTest(unittest.TestCase):
    def test_freeze_of_a_value_that_can_be_poison_stays(self):
        src = op('G_FREEZE', 32, V(0))
        self.assertFalse(refines(src, V(0), (32,)))
        self.assertTrue(refines(src, V(0), (32,), (('def', 0),)))

    def test_frozen_value_is_not_poison(self):
        f = op('G_FREEZE', 32, V(0))
        # x - x is 0 also for a frozen poison value ...
        self.assertTrue(refines(op('G_SUB', 32, f, V(0)), L(32, '0'), (32,)))
        # ... but the frozen value itself is some value, not 0.
        self.assertFalse(refines(f, L(32, '0'), (32,)))
        self.assertFalse(refines(op('G_AND', 32, f, V(1)), V(1), (32, 32)))
        # A second G_FREEZE of a frozen value has the same value.
        self.assertEqual(ir.evaluate(op('G_FREEZE', 32, f), (32,), [7]), 7)

    def test_new_freeze_is_another_instruction(self):
        # The replacement has a G_FREEZE of its own: for a poison x its
        # value is not the value of the G_FREEZE of the source.
        f = op('G_FREEZE', 32, V(0))
        self.assertFalse(refines(op('G_ADD', 32, f, L(32, '0')), f, (32,)))
        self.assertTrue(refines(op('G_ADD', 32, f, L(32, '0')), f, (32,),
                                (('def', 0),)))

    def test_one_term_twice(self):
        f = op('G_FREEZE', 32, V(0))
        self.assertTrue(ir.repeated_freeze(op('G_XOR', 32, f, f)))
        self.assertFalse(ir.repeated_freeze(
            op('G_XOR', 32, f, op('G_FREEZE', 32, V(1)))))

    def test_select_does_not_take_poison_of_the_other_operand(self):
        # select c, x, 0 -> c & x is wrong if x is poison and c is false.
        src = op('G_SELECT', 1, V(0), V(1), L(1, '0'))
        tgt = op('G_AND', 1, V(0), V(1))
        self.assertFalse(refines(src, tgt, (1, 1)))
        self.assertTrue(refines(src, tgt, (1, 1), (('def', 1),)))

    def test_defined_atom(self):
        a = ('def', 1)
        self.assertEqual(precond.atom_from_json(precond.atom_to_json(a)), a)
        self.assertEqual(precond.rename_atom(a, {1: 0}), ('def', 0))
        self.assertFalse(precond.eval_atom(a, ((0, 0), (0, 0)), (32, 32)))
        self.assertTrue(precond.eval_atom(a, ((0, 0), (0, 0, True)),
                                          (32, 32)))
        self.assertIn(a, precond.enumerate_atoms((32, 32), 32))
        # The fact of the compiler, and each address constant.
        self.assertEqual(precond.cpp_atom(a), 'isDefinedValue(X1, MRI)')
        self.assertEqual(precond.pred_vars((a,)), [])

    def test_precondition_is_found_from_the_fact(self):
        src, tgt, vw = op('G_FREEZE', 32, V(0)), V(0), (32,)
        lim = synth.SynthLimits()
        be = smt.Z3Backend()
        sched = synth.schedules(src, tgt, vw, lim)
        valid, _ = synth.synthesize_precondition(
            src, tgt, vw, ((0, 0, True),), sched, be, lim)
        self.assertEqual([p for p, _ in valid], [(('def', 0),)])
        # Without the fact there is nothing to prove the rule with.
        valid, _ = synth.synthesize_precondition(
            src, tgt, vw, ((0, 0),), sched, be, lim)
        self.assertEqual(valid, [])

    def test_concrete_proof_uses_the_fact(self):
        src = op('G_FREEZE', 32, V(0))
        for fact, want in (((0, 0), 'sat'), ((0, 0, True), 'unsat')):
            i = corpus.Instance(src, (32,), (fact,), [None], [], [],
                                [('test', 'f', '%0')])
            self.assertEqual(
                discover.prove_concrete(i, V(0), smt.Z3Backend()).status,
                want)


class EmitTest(unittest.TestCase):
    @staticmethod
    def rule(src, tgt, vw):
        return {'id': 'r', 'vw': list(vw), 'source_json': ir.to_json(src),
                'replacement_json': ir.to_json(tgt), 'source': '',
                'replacement': ''}

    def test_float_value_takes_the_type_of_a_float_value(self):
        # fpext(sitofp x) -> sitofp x: the result has the type of the root.
        src = op('G_FPEXT', 64, op('G_SITOFP', 32, V(0)))
        tgt = op('G_SITOFP', 64, V(0))
        r = self.rule(src, tgt, (16,))
        self.assertIsNone(emit.why_not_emittable(r))
        self.assertEqual(emit._type_sources(r),
                         [(64, 'f', 'Dst'), (16, 'i', 'X0'), (32, 'f', 'T0')])
        self.assertEqual(emit._apply_patterns(tgt, (16,), 64, src),
                         ['(G_SITOFP $dst, $x0)'])

    def test_no_integer_type_for_a_float_value(self):
        # The new float value has the width of x, which is an integer.
        src = op('G_FPTOSI', 32, op('G_FPEXT', 64,
                                    op('G_SITOFP', 16, V(0))))
        tgt = op('G_FPTOSI', 32, op('G_SITOFP', 32, V(0)))
        r = self.rule(src, tgt, (32,))
        self.assertEqual(emit.why_not_emittable(r),
                         'no floating-point operand with width 32')

    def test_float_constant_is_built_by_the_builder(self):
        # An apply pattern has G_CONSTANT with an integer type only: the
        # apply function builds a G_FCONSTANT.
        src = op('G_FPEXT', 64, op('G_SITOFP', 32, V(0)))
        r = self.rule(src, L(64, '0'), (16,))
        self.assertIsNone(emit.why_not_emittable(r))
        self.assertTrue(emit._rule_needs_cpp_apply(r))
        self.assertIn('buildConstantBits(B, Dst, ', emit._cpp_apply(r))
        self.assertIn('/*IsFP=*/true', emit._cpp_apply(r))

    def test_freeze_is_matched_but_not_created(self):
        src = op('G_FREEZE', 32, V(0))
        self.assertIsNone(emit.why_not_emittable(self.rule(src, V(0),
                                                           (32,))))
        tgt = op('G_FREEZE', 32, V(0))
        why = emit.why_not_emittable(
            self.rule(op('G_ADD', 32, V(0), L(32, '0')), tgt, (32,)))
        self.assertIn('must not create', why)


if __name__ == '__main__':
    unittest.main()
