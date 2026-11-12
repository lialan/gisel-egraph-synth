#!/usr/bin/env python3
"""Tests of the intrinsics of a target (girs/amdgcn.py). An intrinsic with
a model is an operator of the namespace of its target: a pure function of
its arguments that the compiler has an exact definition of. A rule creates
an intrinsic only where the source has the same intrinsic with the same
types, and a target without the namespace does not get the rule.

Run:  python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests
"""

import importlib.util
import json
import os
import struct
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import z3  # noqa: E402

from girs import (amdgcn, corpus, discover, emit, fp, ir,  # noqa: E402
                  opcheck, ops, select, smt, synth, targets)

_spec = importlib.util.spec_from_file_location(
    'gi_rule_synth_cli', os.path.join(ROOT, 'gi-rule-synth.py'))
cli = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cli)

LLVM = os.path.dirname(os.path.dirname(os.path.dirname(ROOT)))
LLC = os.environ.get('GIRS_LLC') or os.path.join(LLVM, 'build', 'bin', 'llc')
OPT = os.path.join(os.path.dirname(LLC), 'opt')
HAVE_LLC = os.path.exists(LLC)

U24 = 'llvm.amdgcn.mul.u24'
I24 = 'llvm.amdgcn.mul.i24'
UBFE = 'llvm.amdgcn.ubfe'
SBFE = 'llvm.amdgcn.sbfe'
CLASS = 'llvm.amdgcn.class'
MANT = 'llvm.amdgcn.frexp.mant'
EXP = 'llvm.amdgcn.frexp.exp'
OFF = 'llvm.amdgcn.cvt.off.f32.i4'
ALL = (U24, I24, UBFE, SBFE, CLASS, MANT, EXP, OFF)


def V(i):
    return ('var', i)


def C(v, w):
    return ('const', w, v)


def op(name, w, *args):
    return (name, w) + args


def status(src, tgt, vw):
    enc = smt.Encoder(vw, src[1])
    f = smt.refinement_violation(enc, src, tgt, z3.BoolVal(True))
    return smt.Z3Backend().check(f).status


def instance(src, vw, consts=None):
    """``consts``: per variable the value of its G_CONSTANT, or None."""
    consts = consts or [None] * len(vw)
    facts = [(0, 0) if c is None else (~c & ops.mask(w), c)
             for c, w in zip(consts, vw)]
    return corpus.Instance(src, vw, facts, consts,
                           [1] * len(ir.interior_nodes(src)), [],
                           [('f', 'fn', '%0')])


def rule_of(src, tgt, vw, consts=None):
    s = synth.Synthesizer(smt.Z3Backend())
    inst = instance(src, vw, consts)
    if s.add(inst, tgt) is None:
        return None
    s.finalize([inst])
    (rule,) = s.rules.values()
    return rule


M24 = C(0xFFFFFF, 32)
MUL_MASK = op(U24, 32, op('G_AND', 32, V(0), M24), V(1))
MUL = op(U24, 32, V(0), V(1))


def mul_mask_rule():
    """mul.u24(x & -1, y) => mul.u24(x, y), the mask a G_CONSTANT. (The
    precondition grammar has no atom for a mask of 24 bits: ProofTest has
    that form.)"""
    return rule_of(op(U24, 32, op('G_AND', 32, V(0), V(1)), V(2)),
                   op(U24, 32, V(0), V(2)), (32, 32, 32),
                   [None, 0xFFFFFFFF, None])


def mul_one_rule():
    """mul.u24(x, 1) => x & 0xFFFFFF: a generic operator in the place of
    the intrinsic."""
    return rule_of(op(U24, 32, V(0), V(1)),
                   op('G_AND', 32, V(0), C(0xFFFFFF, 32)), (32, 32),
                   [None, 1])


def bfe_rule():
    """ubfe(x, y, 0) => 0."""
    return rule_of(op(UBFE, 32, V(0), V(1), V(2)), C(0, 32), (32, 32, 32),
                   [None, None, 0])


class RegistryTest(unittest.TestCase):
    def test_contract(self):
        for name in ALL:
            info = ops.REGISTRY[name]
            self.assertEqual(info.namespace, 'amdgcn')
            self.assertEqual(info.intrinsic,
                             'amdgcn_' + name[12:].replace('.', '_'))
            self.assertEqual(info.td_name(), 'int_' + info.intrinsic)
            # The instructions of the target take scalars.
            self.assertFalse(info.lanewise)
            self.assertIsNotNone(info.eval)
            self.assertIsNotNone(info.smt)
            self.assertIn(info.meta['reference'], ('knownbits',
                                                   'instcombine'))

    def test_capabilities(self):
        rows = ops.capability_matrix('amdgcn')
        self.assertEqual([r['name'] for r in rows], list(ALL))
        for r in rows:
            self.assertEqual([r[st] for st in ops.STAGES],
                             ['yes'] * 4 + ['enumerative', 'yes'])
        self.assertFalse({r['name'] for r in ops.capability_matrix()} &
                         set(ALL))

    def test_generic_namespace_has_no_intrinsic(self):
        for name in ops.rhs_operators('generic'):
            self.assertIsNone(ops.REGISTRY[name].intrinsic, name)

    def test_call_instructions(self):
        # The instruction of a call is no operator: the intrinsic is.
        for name in ('G_INTRINSIC', 'G_INTRINSIC_W_SIDE_EFFECTS',
                     'G_INTRINSIC_CONVERGENT',
                     'G_INTRINSIC_CONVERGENT_W_SIDE_EFFECTS'):
            info = ops.REGISTRY[name]
            self.assertIsNone(info.smt)
            self.assertIsNone(info.intrinsic)
            self.assertFalse(ops.has_semantics(name))
            for st in ops.STAGES[1:]:
                self.assertNotEqual(ops.capability(info, st), 'yes')
        self.assertIn('side effect',
                      ops.capability(ops.REGISTRY['G_INTRINSIC_CONVERGENT'],
                                     'smt'))

    def test_no_model_has_a_reason(self):
        for name, why in amdgcn.NO_MODEL.items():
            self.assertNotIn(name, ops.REGISTRY)
            self.assertTrue(why)
        # One reason for each group, and no name in two groups.
        self.assertEqual(len(set(amdgcn.NO_MODEL.values())), 9)
        self.assertIn('approximation', amdgcn.NO_MODEL['llvm.amdgcn.rcp'])
        self.assertIn('lane', amdgcn.NO_MODEL['llvm.amdgcn.mbcnt.lo'])

    def test_types(self):
        tc = ops.REGISTRY[U24].typecheck
        self.assertTrue(tc(32, [32, 32], None, 0))
        self.assertTrue(tc(64, [32, 32], None, 0))
        self.assertFalse(tc(64, [64, 64], None, 0))
        self.assertFalse(tc(16, [16, 16], None, 0))
        tc = ops.REGISTRY[UBFE].typecheck
        self.assertTrue(tc(64, [64, 32, 32], None, 0))
        self.assertFalse(tc(64, [64, 64, 64], None, 0))
        tc = ops.REGISTRY[EXP].typecheck
        self.assertTrue(tc(32, [64], None, 0))
        self.assertTrue(tc(16, [16], None, 0))
        self.assertFalse(tc(64, [64], None, 0))

    def test_names_for_the_extractor(self):
        self.assertEqual(amdgcn.intrinsic_names(('generic', 'amdgcn')),
                         sorted(ALL))
        self.assertEqual(amdgcn.intrinsic_names(('generic',)), [])


class EvalTest(unittest.TestCase):
    def ev(self, name, w, ws, *vals):
        return ops.REGISTRY[name].eval(w, ws, None, 0, list(vals))

    def test_mul24(self):
        self.assertEqual(self.ev(U24, 32, [32, 32], 0xFF000003, 5), 15)
        self.assertEqual(self.ev(U24, 64, [32, 32], 0xFFFFFF, 0xFFFFFF),
                         0xFFFFFF * 0xFFFFFF)
        # -1 * -1 in 24 bits.
        self.assertEqual(self.ev(I24, 64, [32, 32], 0xFFFFFF, 0xFFFFFF), 1)
        self.assertEqual(self.ev(I24, 64, [32, 32], 0x800000, 1),
                         (-0x800000) & ops.mask(64))
        # The product of two 24-bit values does not fit in 32 bits.
        self.assertEqual(self.ev(U24, 32, [32, 32], 0xFFFFFF, 0xFFFFFF),
                         (0xFFFFFF * 0xFFFFFF) & ops.mask(32))

    def test_bfe(self):
        ws = [32, 32, 32]
        self.assertEqual(self.ev(UBFE, 32, ws, 0xABCD1234, 4, 8), 0x23)
        self.assertEqual(self.ev(SBFE, 32, ws, 0xABCD1234, 16, 4),
                         0xD | 0xFFFFFFF0)
        # The width 0 (also 32: modulo the width of the value).
        self.assertEqual(self.ev(UBFE, 32, ws, 0xABCD1234, 4, 0), 0)
        self.assertEqual(self.ev(SBFE, 32, ws, 0xABCD1234, 4, 32), 0)
        # The field ends above the value: a shift.
        self.assertEqual(self.ev(UBFE, 32, ws, 0xABCD1234, 28, 8), 0xA)
        self.assertEqual(self.ev(SBFE, 32, ws, 0xABCD1234, 28, 8),
                         0xFFFFFFFA)
        # The index is modulo the width of the value.
        self.assertEqual(self.ev(UBFE, 32, ws, 0xABCD1234, 36, 8), 0x23)
        self.assertEqual(self.ev(UBFE, 64, [64, 32, 32], 1 << 40, 104, 9),
                         1)

    def test_class(self):
        inf = 0x7F800000
        self.assertEqual(self.ev(CLASS, 1, [32, 32], inf, fp.FC_PINF), 1)
        self.assertEqual(self.ev(CLASS, 1, [32, 32], inf, fp.FC_NINF), 0)
        self.assertEqual(self.ev(CLASS, 1, [32, 32], inf, 0), 0)
        # The bits above the classes have no effect.
        self.assertEqual(self.ev(CLASS, 1, [32, 32], inf, 1 << 20), 0)

    def test_frexp(self):
        eight = 0x41000000
        self.assertEqual(self.ev(MANT, 32, [32], eight), 0x3F000000)
        self.assertEqual(self.ev(EXP, 32, [32], eight), 4)
        # The exponent of an infinity and of a NaN is 0.
        self.assertEqual(self.ev(EXP, 32, [32], 0x7F800000), 0)
        self.assertEqual(self.ev(EXP, 32, [32], 0x7FC00000), 0)
        self.assertEqual(self.ev(EXP, 32, [32], 0), 0)

    def test_sample_offset(self):
        ev = lambda v: self.ev(OFF, 32, [32], v)  # noqa: E731
        single = lambda x: struct.unpack(  # noqa: E731
            '<I', struct.pack('<f', x))[0]
        self.assertEqual(ev(0), 0)
        self.assertEqual(ev(1), single(0.0625))
        self.assertEqual(ev(7), single(0.4375))
        self.assertEqual(ev(8), single(-0.5))
        self.assertEqual(ev(15), single(-0.0625))
        # Only the low 4 bits.
        self.assertEqual(ev(0xFFFFFFF3), single(0.1875))

    def test_evaluator_is_the_smt_model(self):
        n, bad = opcheck.check_models(samples=30, names=set(ALL))
        self.assertGreater(n, 500)
        self.assertEqual(bad, [])


class ProofTest(unittest.TestCase):
    def test_mask_of_an_operand(self):
        self.assertEqual(status(MUL_MASK, MUL, (32, 32)), 'unsat')

    def test_mask_of_23_bits_is_needed(self):
        src = op(U24, 32, op('G_AND', 32, V(0), C(0x7FFFFF, 32)), V(1))
        self.assertEqual(status(src, MUL, (32, 32)), 'sat')

    def test_not_the_multiply(self):
        self.assertEqual(status(MUL, op('G_MUL', 32, V(0), V(1)), (32, 32)),
                         'sat')
        # The low 24 bits are the bits of the multiply.
        low = lambda e: op('G_AND', 32, e, M24)  # noqa: E731
        self.assertEqual(status(low(MUL), low(op('G_MUL', 32, V(0), V(1))),
                                (32, 32)), 'unsat')

    def test_signed_is_not_unsigned(self):
        i = op(I24, 32, V(0), V(1))
        self.assertEqual(status(i, MUL, (32, 32)), 'sat')
        low = lambda e: op('G_AND', 32, e, M24)  # noqa: E731
        self.assertEqual(status(low(i), low(MUL), (32, 32)), 'unsat')
        wide = lambda n: op(n, 64, V(0), V(1))  # noqa: E731
        self.assertEqual(status(wide(I24), wide(U24), (32, 32)), 'sat')

    def test_wide_product_has_48_bits(self):
        m = op(U24, 64, V(0), V(1))
        self.assertEqual(status(
            op('G_AND', 64, m, C((1 << 48) - 1, 64)), m, (32, 32)), 'unsat')
        self.assertEqual(status(
            op('G_AND', 64, m, C((1 << 47) - 1, 64)), m, (32, 32)), 'sat')

    def test_trunc_of_the_wide_product(self):
        self.assertEqual(status(
            op('G_TRUNC', 32, op(U24, 64, V(0), V(1))), MUL, (32, 32)),
            'unsat')

    def test_bit_field(self):
        vw = (32,)
        low = op(UBFE, 32, V(0), C(0, 32), C(8, 32))
        self.assertEqual(status(low, op('G_AND', 32, V(0), C(255, 32)), vw),
                         'unsat')
        self.assertEqual(status(low, op('G_AND', 32, V(0), C(127, 32)), vw),
                         'sat')
        s = op(SBFE, 32, V(0), C(0, 32), C(8, 32))
        self.assertEqual(status(s, op('G_SEXT_INREG:8', 32, V(0)), vw),
                         'unsat')
        # The width 32 is the width 0.
        z = op(SBFE, 32, V(0), V(1), C(32, 32))
        self.assertEqual(status(z, C(0, 32), (32, 32)), 'unsat')
        self.assertEqual(status(z, V(0), (32, 32)), 'sat')

    def test_bit_field_index_is_modulo_the_width(self):
        a = op(UBFE, 32, V(0), op('G_AND', 32, V(1), C(31, 32)), V(2))
        b = op(UBFE, 32, V(0), V(1), V(2))
        self.assertEqual(status(a, b, (32, 32, 32)), 'unsat')
        c = op(UBFE, 32, V(0), op('G_AND', 32, V(1), C(15, 32)), V(2))
        self.assertEqual(status(c, b, (32, 32, 32)), 'sat')

    def test_bit_field_is_a_shift_and_a_mask(self):
        # For a field inside the value only.
        f = op(UBFE, 32, V(0), C(4, 32), C(8, 32))
        self.assertEqual(status(
            f, op('G_AND', 32, op('G_LSHR', 32, V(0), C(4, 32)),
                  C(255, 32)), (32,)), 'unsat')
        f = op(UBFE, 32, V(0), C(28, 32), C(8, 32))
        self.assertEqual(status(
            f, op('G_LSHR', 32, V(0), C(28, 32)), (32,)), 'unsat')

    def test_class(self):
        none = op(CLASS, 1, V(0), C(0, 32))
        self.assertEqual(status(none, C(0, 1), (32,)), 'unsat')
        every = op(CLASS, 1, V(0), C(fp.FC_ALL, 32))
        self.assertEqual(status(every, C(1, 1), (32,)), 'unsat')
        nan = op(CLASS, 1, V(0), C(fp.FC_SNAN | fp.FC_QNAN, 32))
        self.assertEqual(status(nan, C(0, 1), (32,)), 'sat')
        self.assertEqual(status(
            nan, op('G_FCMP:uno', 1, V(0), V(0)), (32,)), 'unsat')

    def test_class_of_fabs(self):
        neg = fp.FC_NINF | fp.FC_NNORM | fp.FC_NSUB | fp.FC_NZERO
        e = op(CLASS, 1, op('G_FABS', 32, V(0)), C(neg, 32))
        self.assertEqual(status(e, C(0, 1), (32,)), 'unsat')
        p = op(CLASS, 1, op('G_FABS', 32, V(0)), C(fp.FC_PINF, 32))
        self.assertEqual(status(p, C(0, 1), (32,)), 'sat')

    def test_frexp(self):
        # The exponent does not read the sign.
        e = op(EXP, 32, op('G_FNEG', 32, V(0)))
        self.assertEqual(status(e, op(EXP, 32, V(0)), (32,)), 'unsat')
        self.assertEqual(status(e, C(0, 32), (32,)), 'sat')
        # The fraction of the fraction.
        m = op(MANT, 32, V(0))
        self.assertEqual(status(op(MANT, 32, m), m, (32,)), 'unsat')
        self.assertEqual(status(m, V(0), (32,)), 'sat')


class SampleOffsetTest(unittest.TestCase):
    def test_low_bits(self):
        e = op(OFF, 32, op('G_AND', 32, V(0), C(15, 32)))
        self.assertEqual(status(e, op(OFF, 32, V(0)), (32,)), 'unsat')
        e = op(OFF, 32, op('G_AND', 32, V(0), C(7, 32)))
        self.assertEqual(status(e, op(OFF, 32, V(0)), (32,)), 'sat')

    def test_not_a_nan(self):
        e = op('G_FCMP:uno', 1, op(OFF, 32, V(0)), op(OFF, 32, V(0)))
        self.assertEqual(status(e, C(0, 1), (32,)), 'unsat')

    def test_sign(self):
        # The bit 3 of the operand is the sign of each value but 0... and
        # of 8: -0.5.
        neg = op('G_FCMP:olt', 1, op(OFF, 32, V(0)), C(0, 32))
        bit = op('G_ICMP:ne', 1, op('G_AND', 32, V(0), C(8, 32)), C(0, 32))
        self.assertEqual(status(neg, bit, (32,)), 'unsat')


class ProductTest(unittest.TestCase):
    """The first step of a check has each product of two operands that
    are not constants as an uninterpreted function (smt.abstract_products):
    it gives 'unsat' only."""

    def setUp(self):
        self.x, self.y, self.m = z3.BitVecs('x y m', 32)

    def test_no_product(self):
        self.assertIsNone(smt.abstract_products(self.x + self.y == 3))
        # A product with a constant is not hard.
        self.assertIsNone(smt.abstract_products(self.x * 3 == self.y))

    def test_function_for_each_width(self):
        a = z3.ZeroExt(32, self.x)
        f = z3.And(self.x * self.y == 1, a * a == 1)
        text = smt.abstract_products(f).sexpr()
        self.assertIn('product!32', text)
        self.assertIn('product!64', text)
        self.assertNotIn('bvmul', text)

    def test_order_of_the_operands(self):
        f = smt.abstract_products(self.x * self.y != self.y * self.x)
        s = z3.Solver()
        s.add(f)
        self.assertEqual(s.check(), z3.unsat)

    def test_nested_product(self):
        f = smt.abstract_products(
            (self.x * self.y) * self.m != self.m * (self.y * self.x))
        s = z3.Solver()
        s.add(f)
        self.assertEqual(s.check(), z3.unsat)

    def test_equal_operands(self):
        # x & m == x for each m that has the bits of x: not a syntactic
        # equality of the operands.
        f = z3.And(self.m | ~self.x == -1,
                   (self.x & self.m) * self.y != self.x * self.y)
        r = smt.Z3Backend(timeout_ms=5000).check(f)
        self.assertEqual(r.status, 'unsat')
        self.assertLess(r.seconds, 2)
        self.assertIn('product!32', r.smt2)

    def test_sat_is_from_the_products(self):
        # Satisfiable with a function, not with the product: no result
        # of the first step.
        f = self.x * self.y != self.y * self.x + self.m * 0
        g = z3.And(self.x == 3, self.y == 5, (self.x * self.y) != 15)
        b = smt.Z3Backend(timeout_ms=5000)
        self.assertEqual(b.check(g).status, 'unsat')
        r = b.check(self.x * self.y == 15, want_model_of=[self.x, self.y])
        self.assertEqual(r.status, 'sat')
        self.assertEqual((r.model[0] * r.model[1]) & ops.mask(32), 15)
        self.assertNotIn('product!', r.smt2)
        self.assertEqual(b.check(f).status, 'unsat')

    def test_one_call(self):
        b = smt.Z3Backend(timeout_ms=5000)
        b.check(self.x * self.y == 15)
        self.assertEqual(b.calls, 1)


class CreationTest(unittest.TestCase):
    """A rule creates an intrinsic only where the source has it."""

    def test_error(self):
        mul = op('G_MUL', 32, op('G_AND', 32, V(0), M24),
                 op('G_AND', 32, V(1), M24))
        self.assertIsNotNone(ir.intrinsic_error([mul], [MUL], (32, 32)))
        self.assertIsNone(ir.intrinsic_error([MUL_MASK], [MUL], (32, 32)))
        self.assertIsNone(ir.intrinsic_error([MUL], [mul], (32, 32)))

    def test_other_types(self):
        wide = op(U24, 64, V(0), V(1))
        src = op('G_TRUNC', 32, wide)
        # The source has the intrinsic with a 64-bit result only.
        self.assertIsNotNone(ir.intrinsic_error([src], [MUL], (32, 32)))
        self.assertIsNone(ir.intrinsic_error([src], [wide], (32, 32)))

    def test_other_intrinsic(self):
        s = op(SBFE, 32, V(0), V(1), V(2))
        u = op(UBFE, 32, V(0), V(1), V(2))
        self.assertIsNotNone(ir.intrinsic_error([s], [u], (32, 32, 32)))

    def test_synthesizer_refuses(self):
        mul = op('G_AND', 32, op('G_MUL', 32, V(0), V(1)), M24)
        tgt = op('G_AND', 32, MUL, M24)
        self.assertEqual(status(mul, tgt, (32, 32)), 'unsat')
        s = synth.Synthesizer(smt.Z3Backend())
        self.assertIsNone(s.add(instance(mul, (32, 32)), tgt))
        self.assertEqual(s.stats['intrinsic_rejected'], 1)

    def test_synthesizer_accepts(self):
        rule = mul_mask_rule()
        self.assertIsNotNone(rule)
        self.assertTrue(rule['id'].startswith('synth_amdgcn_mul_u24_'))

    def test_grammar(self):
        limits = discover.Limits(grammar='registry',
                                 namespaces=('generic', 'amdgcn'))
        plain = instance(op('G_MUL', 32, V(0), V(1)), (32, 32))
        names = {n for _, g in discover.grammar_stages(plain, limits)
                 for n in g}
        self.assertFalse(names & set(ALL))
        names = {n for _, g in discover.grammar_stages(
            instance(MUL_MASK, (32, 32)), limits) for n in g}
        self.assertEqual(names & set(ALL), {U24})
        # The source has the intrinsic: its namespace is not needed.
        limits = discover.Limits(grammar='source')
        names = {n for _, g in discover.grammar_stages(
            instance(MUL_MASK, (32, 32)), limits) for n in g}
        self.assertEqual(names & set(ALL), {U24})


class TargetTest(unittest.TestCase):
    def test_namespaces(self):
        self.assertIn('amdgcn', targets.get('AMDGPU').namespaces)
        self.assertEqual(targets.get('AArch64').namespaces, ('generic',))
        self.assertTrue(targets.get('AMDGPU').has([MUL_MASK, MUL]))
        self.assertFalse(targets.get('AArch64').has([MUL_MASK, MUL]))
        self.assertTrue(targets.get('AArch64').has(
            [op('G_MUL', 32, V(0), V(1))]))

    def test_candidates(self):
        rule = mul_mask_rule()
        db = {'rules': [rule]}
        self.assertEqual([r['id'] for r in
                          emit.candidates(db, targets.get('AMDGPU'))][0],
                         rule['id'])
        self.assertEqual(emit.candidates(db, targets.get('AArch64')), [])

    def test_extractor_flags(self):
        (flag,) = targets.get('AMDGPU').corpus_flags()
        self.assertEqual(flag, '-gisel-synth-corpus-intrinsics=' +
                         ','.join(sorted(ALL)))
        self.assertEqual(targets.get('AArch64').corpus_flags(), [])


class EmitTest(unittest.TestCase):
    def test_pattern_and_apply(self):
        rule = mul_mask_rule()
        self.assertIsNone(emit.why_not_emittable(rule))
        # A variant for each order of the operands of the G_AND.
        for pats in emit.variants(rule):
            self.assertIn('(int_amdgcn_mul_u24 $dst, ', ' '.join(pats))
        self.assertTrue(emit._rule_needs_cpp_apply(rule))
        self.assertIn('B.buildIntrinsic(Intrinsic::amdgcn_mul_u24, '
                      'ArrayRef<DstOp>({', emit._cpp_apply(rule))
        self.assertEqual(emit._cpp_apply(rule).count('.addUse('), 2)

    def test_intrinsic_to_a_generic_operator(self):
        for rule, name in ((mul_one_rule(), 'int_amdgcn_mul_u24'),
                           (bfe_rule(), 'int_amdgcn_ubfe')):
            self.assertIsNotNone(rule)
            self.assertIsNone(emit.why_not_emittable(rule))
            td = emit.emit_td([rule], {'AMDGPU': [rule]})[0]
            self.assertIn(name, td)
            self.assertNotIn('buildIntrinsic', emit._cpp_apply(rule)
                             if emit._rule_needs_cpp_apply(rule) else '')

    def test_not_emittable_with_a_new_intrinsic(self):
        rule = mul_mask_rule()
        bad = dict(rule)
        bad['replacement_json'] = ir.to_json(op(I24, 32, V(0), V(2)))
        self.assertIn('the source has no', emit.why_not_emittable(bad))


INTR_LL = '''
declare i32 @llvm.amdgcn.mul.u24.i32(i32, i32)
declare i64 @llvm.amdgcn.mul.i24.i64(i32, i32)
declare i32 @llvm.amdgcn.ubfe.i32(i32, i32, i32)
declare i64 @llvm.amdgcn.sbfe.i64(i64, i32, i32)
declare i1 @llvm.amdgcn.class.f32(float, i32)
declare float @llvm.amdgcn.frexp.mant.f32(float)
declare i32 @llvm.amdgcn.frexp.exp.i32.f64(double)
declare float @llvm.amdgcn.cvt.off.f32.i4(i32)
declare float @llvm.amdgcn.rcp.f32(float)
declare i32 @llvm.amdgcn.sffbh.i32(i32)

define i32 @mul(i32 %x, i32 %y) {
  %a = and i32 %x, 16777215
  %r = call i32 @llvm.amdgcn.mul.u24.i32(i32 %a, i32 %y)
  ret i32 %r
}
define i64 @mulw(i32 %x, i32 %y) {
  %r = call i64 @llvm.amdgcn.mul.i24.i64(i32 %x, i32 %y)
  %n = sub i64 0, %r
  ret i64 %n
}
define i32 @bfe(i32 %x, i32 %o) {
  %r = call i32 @llvm.amdgcn.ubfe.i32(i32 %x, i32 %o, i32 5)
  %n = xor i32 %r, -1
  ret i32 %n
}
define i64 @bfe64(i64 %x, i32 %o, i32 %w) {
  %r = call i64 @llvm.amdgcn.sbfe.i64(i64 %x, i32 %o, i32 %w)
  %n = xor i64 %r, -1
  ret i64 %n
}
define i1 @cls(float %x, i32 %m) {
  %r = call i1 @llvm.amdgcn.class.f32(float %x, i32 %m)
  %n = xor i1 %r, true
  ret i1 %n
}
define float @mant(float %x) {
  %r = call float @llvm.amdgcn.frexp.mant.f32(float %x)
  %n = fneg float %r
  ret float %n
}
define i32 @exp(double %x) {
  %r = call i32 @llvm.amdgcn.frexp.exp.i32.f64(double %x)
  %n = sub i32 0, %r
  ret i32 %n
}
define float @off(i32 %x) {
  %a = and i32 %x, 15
  %r = call float @llvm.amdgcn.cvt.off.f32.i4(i32 %a)
  ret float %r
}
define float @rcp(float %x) {
  %r = call float @llvm.amdgcn.rcp.f32(float %x)
  %n = fneg float %r
  ret float %n
}
define i32 @sffbh(i32 %x) {
  %r = call i32 @llvm.amdgcn.sffbh.i32(i32 %x)
  %n = xor i32 %r, -1
  ret i32 %n
}
'''


def _ops_of(e, out):
    if 'op' in e:
        out.add(e['op'])
        for a in e.get('args', ()):
            _ops_of(a, out)
    return out


@unittest.skipUnless(HAVE_LLC, 'no llc (set GIRS_LLC)')
class RealExtractionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        src = os.path.join(cls.tmp.name, 'intr.ll')
        with open(src, 'w') as f:
            f.write(INTR_LL)
        cls.target = targets.get('AMDGPU')
        _, out = cli._extract_one(LLC, src, cls.tmp.name, 'll', cls.target)
        assert out, 'the extractor failed'
        with open(out) as f:
            cls.records = [json.loads(l) for l in f if l.strip()]
        cls.insts, cls.stats = corpus.load([out])
        cls.src = src

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _ops(self, fn):
        out = set()
        for r in self.records:
            if r['fn'] == fn:
                _ops_of(r['expr'], out)
        return out

    def test_every_record_is_read(self):
        self.assertEqual(self.stats['unsupported'], 0)

    def test_each_intrinsic_is_a_node(self):
        for fn, name in (('mul', U24), ('mulw', I24), ('bfe', UBFE),
                         ('bfe64', SBFE), ('cls', CLASS), ('mant', MANT),
                         ('exp', EXP), ('off', OFF)):
            self.assertIn(name, self._ops(fn), fn)

    def test_types_of_the_node(self):
        got = {}
        for r in self.records:
            e = r['expr']
            if e.get('op', '').startswith('llvm.'):
                got[e['op']] = (e['w'], [
                    r['inputs'][a['in']]['w'] if 'in' in a else a['w']
                    for a in e['args']])
        self.assertEqual(got[I24], (64, [32, 32]))
        self.assertEqual(got[SBFE], (64, [64, 32, 32]))
        self.assertEqual(got[EXP], (32, [64]))
        self.assertEqual(got[CLASS][0], 1)

    def test_no_model_is_an_input(self):
        # The result of an intrinsic without a model is a leaf.
        for fn in ('rcp', 'sffbh'):
            names = self._ops(fn)
            self.assertTrue(names, fn)
            self.assertFalse({n for n in names if n.startswith('llvm.')},
                             fn)
        defs = {i.get('def') for r in self.records if r['fn'] == 'sffbh'
                for i in r['inputs']}
        self.assertIn('G_INTRINSIC', defs)

    def test_without_the_list_no_intrinsic_is_a_node(self):
        out = os.path.join(self.tmp.name, 'plain.jsonl')
        subprocess.run(
            [LLC] + self.target.ll_flags +
            [self.target.corpus_flag, self.src, '-o', os.devnull,
             '-gisel-synth-corpus-out=' + out],
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
        with open(out) as f:
            self.assertTrue(f.read().strip())
        with open(out) as f:
            for l in f:
                self.assertFalse(
                    {n for n in _ops_of(json.loads(l)['expr'], set())
                     if n.startswith('llvm.')})

    def test_instances_have_the_operator(self):
        srcs = {ir.to_sexpr(i.expr) for i in self.insts}
        self.assertTrue(any(s.startswith('(G_SUB:s64 0:s64 (%s:s64' % I24)
                            or I24 in s for s in srcs))
        self.assertTrue(any(U24 in s and 'G_AND' in s for s in srcs))


@unittest.skipUnless(HAVE_LLC, 'no llc (set GIRS_LLC)')
class ProbeTest(unittest.TestCase):
    """The function that selection runs a rule on is valid MIR."""

    def _probe(self, rule):
        self.assertIsNotNone(rule)
        (name, ex), = select.examples(rule)
        mir = select.build_mir(rule, ex, name, targets.get('AMDGPU'))
        p = subprocess.run(
            [LLC, '-mtriple=amdgcn-amd-amdhsa', '-x', 'mir',
             '-run-pass=none', '-verify-machineinstrs', '-o', '/dev/null',
             '-'], input=mir, capture_output=True, text=True)
        self.assertEqual(p.returncode, 0, p.stderr + mir)
        return mir

    def test_multiply(self):
        mir = self._probe(mul_mask_rule())
        self.assertIn('G_INTRINSIC intrinsic(@llvm.amdgcn.mul.u24)', mir)

    def test_bit_field(self):
        mir = self._probe(bfe_rule())
        self.assertIn('G_INTRINSIC intrinsic(@llvm.amdgcn.ubfe)', mir)

    def test_multiply_by_one(self):
        mir = self._probe(mul_one_rule())
        self.assertIn('G_INTRINSIC intrinsic(@llvm.amdgcn.mul.u24)', mir)

    def test_class(self):
        mir = self._probe(rule_of(op(CLASS, 1, V(0), V(1)), C(0, 1),
                                  (32, 32), [None, 0]))
        self.assertIn('G_INTRINSIC intrinsic(@llvm.amdgcn.class)', mir)


@unittest.skipUnless(HAVE_LLC and os.path.exists(OPT), 'no llc and opt')
class CompilerReferenceTest(unittest.TestCase):
    def test_evaluator_is_the_compiler(self):
        n, bad, none = opcheck.check_intrinsics(
            LLC, OPT, targets.get('AMDGPU').triple_flags, samples=12)
        self.assertGreater(n, 100)
        self.assertEqual(bad, [])
        # Each intrinsic has a reference for some cases.
        for name in ALL:
            cases = 12 * len(opcheck.instances(ops.REGISTRY[name]))
            self.assertLess(none.get(name, 0), cases, name)


if __name__ == '__main__':
    unittest.main()
