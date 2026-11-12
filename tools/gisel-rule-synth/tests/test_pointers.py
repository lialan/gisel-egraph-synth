#!/usr/bin/env python3
"""Tests of the model of pointers: G_PTR_ADD, G_PTRMASK, G_PTRTOINT and
G_INTTOPTR, the pointer kind of a value, and the guard of a rule with
pointers.

Run:  python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests
"""

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import z3  # noqa: E402

from girs import (corpus, discover, emit, ir, ops, select,  # noqa: E402
                  smt, synth, targets)

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


def L(w, v):
    return ('const', w, v)


def op(name, w, *args):
    return (name, w) + args


def proved(src, tgt, vw):
    enc = smt.Encoder(vw, src[1])
    f = smt.refinement_violation(enc, src, tgt, z3.BoolVal(True))
    return smt.Z3Backend().check(f).status == 'unsat'


def instance(src, vw, kinds=None):
    n = len(vw)
    return corpus.Instance(src, vw, [(0, 0)] * n, [None] * n, [], [],
                           [('f', 'fn', '%0')], kinds=kinds)


def rule_of(src, tgt, vw, kinds=None):
    s = synth.Synthesizer(smt.Z3Backend())
    inst = instance(src, vw, kinds)
    if s.add(inst, tgt) is None:
        return None
    s.finalize([inst])
    (rule,) = s.rules.values()
    return rule


CHAIN = op('G_PTR_ADD', 64, op('G_PTR_ADD', 64, V(0), V(1)), V(2))
CHAIN_TGT = op('G_PTR_ADD', 64, V(0), op('G_ADD', 64, V(1), V(2)))


class RegistryTest(unittest.TestCase):
    def test_signatures(self):
        P, I = (64, 'p'), (64, 'i')
        self.assertTrue(ops.signature_ok('G_PTR_ADD', P, [P, I]))
        self.assertFalse(ops.signature_ok('G_PTR_ADD', P, [I, I]))
        self.assertFalse(ops.signature_ok('G_PTR_ADD', P, [P, P]))
        self.assertFalse(ops.signature_ok('G_PTR_ADD', I, [P, I]))
        # The offset has the width of the pointer.
        self.assertFalse(ops.signature_ok('G_PTR_ADD', P, [P, (32, 'i')]))
        self.assertTrue(ops.signature_ok('G_PTRMASK', P, [P, I]))
        # A conversion extends with zeros or truncates.
        for w in (16, 64):
            self.assertTrue(ops.signature_ok('G_PTRTOINT', (w, 'i'),
                                             [(32, 'p')]))
            self.assertTrue(ops.signature_ok('G_INTTOPTR', (32, 'p'),
                                             [(w, 'i')]))
        self.assertFalse(ops.signature_ok('G_PTRTOINT', P, [P]))
        self.assertFalse(ops.signature_ok('G_INTTOPTR', I, [I]))

    def test_other_operators_and_pointers(self):
        P, I, B = (64, 'p'), (64, 'i'), (1, 'i')
        # G_ICMP compares the bits of two pointers.
        self.assertTrue(ops.signature_ok('G_ICMP:eq', B, [P, P]))
        self.assertFalse(ops.signature_ok('G_ICMP:eq', B, [P, I]))
        self.assertTrue(ops.signature_ok('G_SELECT', P, [B, P, P]))
        self.assertFalse(ops.signature_ok('G_SELECT', P, [B, P, I]))
        self.assertTrue(ops.signature_ok('G_FREEZE', P, [P]))
        # No arithmetic and no G_BITCAST on a pointer.
        self.assertFalse(ops.signature_ok('G_ADD', P, [P, I]))
        self.assertFalse(ops.signature_ok('G_AND', I, [P, I]))
        self.assertFalse(ops.signature_ok('G_BITCAST', I, [P]))
        self.assertFalse(ops.signature_ok('G_BITCAST', (64, 'f'), [P]))
        self.assertFalse(ops.signature_ok('G_FCMP:oeq', B, [P, P]))

    def test_values(self):
        e = op('G_PTRTOINT', 16, op('G_PTR_ADD', 32, op(
            'G_INTTOPTR', 32, V(0)), V(1)))
        self.assertEqual(ir.evaluate(e, (64, 32), (0x1ffffffff, 5)), 4)
        e = op('G_PTRTOINT', 64, op('G_PTRMASK', 32, op(
            'G_INTTOPTR', 32, V(0)), V(1)))
        self.assertEqual(ir.evaluate(e, (64, 32), (0x1f0f0f0f0, 0xff00)),
                         0xf000)

    def test_capabilities(self):
        for name in ('G_PTR_ADD', 'G_PTRMASK', 'G_PTRTOINT', 'G_INTTOPTR'):
            info = ops.REGISTRY[name]
            self.assertEqual(info.lhs(), 'yes', name)
            self.assertEqual(info.rhs(), 'yes', name)


class KindTest(unittest.TestCase):
    def test_kinds_of_an_expression(self):
        self.assertEqual(ir.result_kind(CHAIN), 'p')
        self.assertEqual(ir.var_kinds(CHAIN), {0: 'p', 1: 'i', 2: 'i'})
        e = op('G_PTRTOINT', 64, V(0))
        self.assertEqual(ir.result_kind(e), 'i')
        self.assertEqual(ir.var_kinds(e), {0: 'p'})
        self.assertEqual(ir.type_of(CHAIN, (64, 64, 64), ('p', 'i', 'i')),
                         (64, 'p'))
        self.assertIsNone(ir.type_of(CHAIN, (64, 64, 64), ('i', 'i', 'i')))

    def test_compare_of_pointers(self):
        """An operand that is a pointer makes the other operand one. Two
        values of an unknown kind are integers."""
        e = op('G_ICMP:eq', 1, op('G_PTR_ADD', 64, V(0), V(1)), V(2))
        self.assertEqual(ir.var_kinds(e), {0: 'p', 1: 'i', 2: 'p'})
        e = op('G_ICMP:eq', 1, V(0), V(1))
        self.assertEqual(ir.var_kinds(e), {0: 'i', 1: 'i'})
        e = op('G_ICMP:eq', 1, V(1), op(
            'G_SELECT', 64, V(0), op('G_INTTOPTR', 64, V(2)), V(3)))
        self.assertEqual(ir.var_kinds(e),
                         {0: 'i', 1: 'p', 2: 'i', 3: 'p'})

    def test_kinds_of_an_instance(self):
        # The type of the register: a select of two pointers.
        e = op('G_SELECT', 64, V(0), V(1), V(2))
        self.assertEqual(instance(e, (1, 64, 64),
                                  [None, 'p', 'p']).vk, ('i', 'p', 'p'))
        # The operators: a compare of two registers is a compare of
        # integers, whatever the registers are.
        e = op('G_ICMP:eq', 1, V(0), V(1))
        self.assertEqual(instance(e, (64, 64), ['p', 'p']).vk, ('i', 'i'))
        self.assertEqual(corpus._type_kind('p0'), 'p')
        self.assertEqual(corpus._type_kind('p13'), 'p')
        self.assertEqual(corpus._type_kind('f32'), 'f')
        self.assertIsNone(corpus._type_kind('ppcf128'))
        self.assertIsNone(corpus._type_kind('i32'))
        self.assertIsNone(corpus._type_kind(''))

    def test_search_classes(self):
        """A pointer and the integers of its width get one canonical
        width: the offset of G_PTR_ADD has the width of the pointer."""
        self.assertEqual(
            discover.canonical_types(((32, 'i'), (32, 'p'))),
            ((64, 'i'), (64, 'p')))
        self.assertEqual(
            discover.canonical_types(((1, 'i'), (32, 'p'), (64, 'i'))),
            ((1, 'i'), (32, 'p'), (64, 'i')))
        self.assertEqual(
            discover.canonical_types(((16, 'i'), (64, 'i'))),
            ((32, 'i'), (64, 'i')))


class ProofTest(unittest.TestCase):
    def test_add_chain(self):
        self.assertTrue(proved(CHAIN, CHAIN_TGT, (64, 64, 64)))
        # Not with a subtraction.
        self.assertFalse(proved(CHAIN, op('G_PTR_ADD', 64, V(0), op(
            'G_SUB', 64, V(1), V(2))), (64, 64, 64)))

    def test_add_is_the_addition_of_the_bits(self):
        src = op('G_PTRTOINT', 64, op('G_PTR_ADD', 64, V(0), V(1)))
        tgt = op('G_ADD', 64, op('G_PTRTOINT', 64, V(0)), V(1))
        self.assertTrue(proved(src, tgt, (64, 64)))
        # A truncation: the low bits of the sum.
        src = op('G_PTRTOINT', 32, op('G_PTR_ADD', 64, V(0), V(1)))
        tgt = op('G_ADD', 32, op('G_PTRTOINT', 32, V(0)),
                 op('G_TRUNC', 32, V(1)))
        self.assertTrue(proved(src, tgt, (64, 64)))
        # An extension: the sum of the pointer does not have a carry out
        # of its width.
        src = op('G_PTRTOINT', 64, op('G_PTR_ADD', 32, V(0), V(1)))
        tgt = op('G_ADD', 64, op('G_PTRTOINT', 64, V(0)),
                 op('G_ZEXT', 64, V(1)))
        self.assertFalse(proved(src, tgt, (32, 32)))

    def test_round_trips(self):
        src = op('G_INTTOPTR', 64, op('G_PTRTOINT', 64, V(0)))
        self.assertTrue(proved(src, V(0), (64,)))
        # Through a narrower integer: the high bits are zero.
        src = op('G_INTTOPTR', 64, op('G_PTRTOINT', 32, V(0)))
        self.assertFalse(proved(src, V(0), (64,)))
        src = op('G_PTRTOINT', 64, op('G_INTTOPTR', 64, V(0)))
        self.assertTrue(proved(src, V(0), (64,)))
        # Through a wider pointer.
        src = op('G_PTRTOINT', 32, op('G_INTTOPTR', 64, V(0)))
        self.assertTrue(proved(src, V(0), (32,)))
        # Through a narrower pointer.
        src = op('G_PTRTOINT', 64, op('G_INTTOPTR', 32, V(0)))
        self.assertFalse(proved(src, V(0), (64,)))
        self.assertTrue(proved(src, op('G_AND', 64, V(0),
                                       L(64, 0xffffffff)), (64,)))

    def test_mask(self):
        src = op('G_PTRMASK', 64, V(0), V(1))
        tgt = op('G_INTTOPTR', 64, op(
            'G_AND', 64, op('G_PTRTOINT', 64, V(0)), V(1)))
        self.assertTrue(proved(src, tgt, (64, 64)))
        self.assertFalse(proved(src, V(0), (64, 64)))

    def test_compare(self):
        a = op('G_PTR_ADD', 64, V(0), V(1))
        b = op('G_PTR_ADD', 64, V(0), V(2))
        self.assertTrue(proved(op('G_ICMP:eq', 1, a, b),
                               op('G_ICMP:eq', 1, V(1), V(2)),
                               (64, 64, 64)))
        # The addition can wrap: no order of the offsets.
        self.assertFalse(proved(op('G_ICMP:ult', 1, a, b),
                                op('G_ICMP:ult', 1, V(1), V(2)),
                                (64, 64, 64)))

    def test_poison(self):
        """G_PTR_ADD is poison if an operand is."""
        src = op('G_SELECT', 64, V(0), op('G_PTR_ADD', 64, V(1), V(2)),
                 V(1))
        tgt = op('G_PTR_ADD', 64, V(1), op(
            'G_SELECT', 64, V(0), V(2), L(64, 0)))
        self.assertTrue(proved(src, tgt, (1, 64, 64)))
        # The replacement reads the offset for each condition.
        tgt = op('G_PTR_ADD', 64, V(1), op(
            'G_AND', 64, op('G_SEXT', 64, V(0)), V(2)))
        self.assertFalse(proved(src, tgt, (1, 64, 64)))


class RuleTest(unittest.TestCase):
    def test_guard_checks_the_pointers(self):
        r = rule_of(CHAIN, CHAIN_TGT, (64, 64, 64))
        self.assertIsNotNone(r)
        self.assertIsNone(emit.why_not_emittable(r))
        g = emit._cpp_guard(r)
        # The registers of the guard: X0 X1 X2 T0 Dst. X0, T0 and Dst are
        # pointers.
        self.assertIn('getScalarWidths(MRI, {X0, X1, X2, T0, Dst}, W, '
                      'UINT64_C(0x19))', g)

    def test_guard_of_a_rule_without_pointers(self):
        r = rule_of(op('G_ADD', 32, op('G_SUB', 32, V(0), V(1)), V(1)),
                    V(0), (32, 32))
        self.assertIn('getScalarWidths(MRI, {X0, X1, T0, Dst}, W))',
                      emit._cpp_guard(r))

    def test_new_pointer_has_the_type_of_a_pointer(self):
        """ptr_add(p, a) + b with the integer sum outside: the new
        G_PTR_ADD has the type of a pointer register, the new G_ADD the
        type of an integer register."""
        r = rule_of(CHAIN, CHAIN_TGT, (64, 64, 64))
        pats = emit._apply_patterns(
            ir.from_json(r['replacement_json']), r['vw'], 64,
            ir.from_json(r['source_json']))
        self.assertEqual(
            pats, ['(G_ADD GITypeOf<"$x1">:$n0, $x1, $x2)',
                   '(G_PTR_ADD $dst, $x0, $n0)'])
        # An integer result from pointers: the integer type is the type
        # of the root, not of a pointer.
        src = op('G_PTRTOINT', 64, op('G_PTR_ADD', 64, V(0), V(1)))
        tgt = op('G_ADD', 64, op('G_PTRTOINT', 64, V(0)), V(1))
        r = rule_of(src, tgt, (64, 64))
        pats = emit._apply_patterns(
            ir.from_json(r['replacement_json']), r['vw'], 64,
            ir.from_json(r['source_json']))
        self.assertEqual(
            pats, ['(G_PTRTOINT GITypeOf<"$dst">:$n0, $x0)',
                   '(G_ADD $dst, $n0, $x1)'])

    def test_no_pointer_register_for_a_new_pointer(self):
        """A new pointer needs the type of a pointer of the rule."""
        types = [(64, 'i', 'Dst'), (64, None, 'X0'), (32, 'p', 'X1')]
        self.assertEqual(emit._type_source(types, 32, 'p'), 'X1')
        with self.assertRaises(ValueError):
            emit._type_source(types, 64, 'p')
        # A pointer does not give the type of another value.
        with self.assertRaises(ValueError):
            emit._type_source(types, 32, 'i')
        with self.assertRaises(ValueError):
            emit._type_source(types, 32)
        self.assertEqual(emit._type_source(types, 64), 'Dst')

    def test_no_pointer_constant(self):
        zero = ('lit', 64, '0')
        src = op('G_PTRMASK', 64, V(0), zero)
        self.assertTrue(proved(src, zero, (64,)))
        with self.assertRaisesRegex(ValueError, 'a pointer constant'):
            emit._apply_patterns(zero, (64,), 64, src)

    def test_replacement_of_another_kind(self):
        """The bits are the same and the register types are not."""
        src = op('G_PTR_ADD', 64, V(0), V(1))
        self.assertIsNone(rule_of(src, op('G_ADD', 64, V(0), V(1)),
                                  (64, 64)))
        src = op('G_INTTOPTR', 64, V(0))
        self.assertIsNone(rule_of(src, V(0), (64,)))


class MergeTest(unittest.TestCase):
    """Rules with G_MERGE_VALUES and G_UNMERGE_VALUES."""

    def _patterns(self, rule):
        return emit.variants(rule)[0]

    def test_match_and_build_a_merge(self):
        # The low half of (lo, hi & m) is lo.
        src = op('G_TRUNC', 32, op('G_MERGE_VALUES', 64, V(0), V(1)))
        r = rule_of(src, V(0), (32, 32))
        self.assertIsNotNone(r)
        self.assertIsNone(emit.why_not_emittable(r))
        self.assertEqual(self._patterns(r),
                         ['(G_MERGE_VALUES $t0, $x0, $x1)',
                          '(G_TRUNC $dst, $t0)'])
        # A replacement with a merge.
        src = op('G_ZEXT', 64, V(0))
        tgt = op('G_MERGE_VALUES', 64, V(0), ('lit', 32, '0'))
        r = rule_of(src, tgt, (32,))
        self.assertIsNotNone(r)
        self.assertIsNone(emit.why_not_emittable(r))
        self.assertEqual(
            emit._apply_patterns(tgt, r['vw'], 64, src),
            ['(G_MERGE_VALUES $dst, $x0, (GITypeOf<"$x0"> 0))'])

    def test_match_an_unmerge_below_the_root(self):
        """The pattern names each result of the instruction: four parts
        of 16 bits, and the third one is in the tree."""
        src = op('G_ZEXT', 32, op('G_UNMERGE_VALUES#2', 16, V(0)))
        tgt = op('G_AND', 32, op('G_TRUNC', 32, op(
            'G_LSHR', 64, V(0), ('const', 64, 32))), ('const', 32, 0xffff))
        self.assertTrue(proved(src, tgt, (64,)))
        r = rule_of(src, tgt, (64,))
        self.assertIsNotNone(r)
        self.assertIsNone(emit.why_not_emittable(r))
        self.assertEqual(
            self._patterns(r),
            ['(G_UNMERGE_VALUES $t0_r0, $t0_r1, $t0, $t0_r3, $x0)',
             '(G_ZEXT $dst, $t0)'])

    def test_unmerge_is_not_a_root_and_is_not_built(self):
        src = op('G_UNMERGE_VALUES', 32, op('G_MERGE_VALUES', 64, V(0),
                                             V(1)))
        r = rule_of(src, V(0), (32, 32))
        self.assertEqual(emit.why_not_emittable(r),
                         'the root instruction has several results')
        src = op('G_TRUNC', 32, V(0))
        tgt = op('G_UNMERGE_VALUES', 32, V(0))
        self.assertTrue(proved(src, tgt, (64,)))
        r = rule_of(src, tgt, (64,))
        self.assertIn('does not create it', emit.why_not_emittable(r))
        self.assertEqual(ops.REGISTRY['G_MERGE_VALUES'].unsupported.get(
            'emit'), None)

    def test_no_merge_of_pointers(self):
        self.assertIsNone(
            ops.REGISTRY['G_UNMERGE_VALUES'].result_kind(['p']))
        self.assertIsNone(
            ops.REGISTRY['G_MERGE_VALUES'].result_kind(['i', 'p']))
        self.assertEqual(
            ops.REGISTRY['G_MERGE_VALUES'].result_kind(['i', 'i']), 'i')


class SearchTest(unittest.TestCase):
    def _find(self, src, vw, grammar='source'):
        cands, _ = discover.discover(instance(src, vw), smt.Z3Backend(),
                                     discover.Limits(grammar=grammar))
        return [c['tgt'] for c in cands]

    def test_add_and_subtract(self):
        """(p + x) + (y - x) -> p + y. (A search keeps a replacement that
        is cheaper: the two additions of CHAIN have the cost of
        CHAIN_TGT.)"""
        src = op('G_PTR_ADD', 64, op('G_PTR_ADD', 64, V(0), V(1)),
                 op('G_SUB', 64, V(2), V(1)))
        self.assertIn(op('G_PTR_ADD', 64, V(0), V(2)),
                      self._find(src, (64, 64, 64)))

    def test_integer_through_a_pointer(self):
        src = op('G_PTRTOINT', 64, op('G_PTR_ADD', 64, op(
            'G_INTTOPTR', 64, V(0)), V(1)))
        self.assertIn(op('G_ADD', 64, V(0), V(1)),
                      self._find(src, (64, 64)))

    def test_round_trip(self):
        src = op('G_INTTOPTR', 64, op('G_PTRTOINT', 64, V(0)))
        self.assertIn(V(0), self._find(src, (64,)))

    def test_narrow_pointer(self):
        """A pointer of 32 bits with offsets of 32 bits."""
        src = op('G_PTR_ADD', 32, op('G_PTR_ADD', 32, V(0), V(1)),
                 op('G_SUB', 32, V(2), V(1)))
        self.assertIn(op('G_PTR_ADD', 32, V(0), V(2)),
                      self._find(src, (32, 32, 32)))


POINTER_MIR = '''
---
name: pointers
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0_vgpr1, $vgpr2_vgpr3, $vgpr4, $vgpr5
    %0:_(p0) = COPY $vgpr0_vgpr1
    %1:_(i64) = COPY $vgpr2_vgpr3
    %2:_(p3) = COPY $vgpr4
    %3:_(i32) = COPY $vgpr5
    %4:_(p0) = nuw inbounds G_PTR_ADD %0, %1
    %5:_(p0) = G_PTR_ADD %4, %1
    %6:_(i64) = G_PTRTOINT %5
    %7:_(p3) = G_PTR_ADD %2, %3
    %8:_(i32) = G_PTRTOINT %7
    %9:_(p0) = G_INTTOPTR %8
    %10:_(i1) = G_ICMP intpred(eq), %5, %9
    %11:_(p0) = G_CONSTANT i64 0
    %12:_(i1) = G_ICMP intpred(eq), %5, %11
    %13:_(i32) = G_ZEXT %10
    %14:_(i32) = G_ZEXT %12
    $vgpr0_vgpr1 = COPY %6
    $vgpr2 = COPY %13
    $vgpr3 = COPY %14
    SI_RETURN implicit $vgpr0_vgpr1, implicit $vgpr2, implicit $vgpr3
...
'''


@unittest.skipUnless(HAVE_LLC, 'no llc (set GIRS_LLC)')
class RealExtractionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        mir = os.path.join(cls.tmp.name, 'pointers.mir')
        with open(mir, 'w') as f:
            f.write(POINTER_MIR)
        _, out = cli._extract_one(LLC, mir, cls.tmp.name, 'mir',
                                  targets.get('AMDGPU'))
        assert out, 'the extractor failed'
        with open(out) as f:
            cls.records = [json.loads(l) for l in f if l.strip()]
        cls.insts, cls.stats = corpus.load([out])
        ll = os.path.join(cls.tmp.name, 'one.ll')
        with open(ll, 'w') as f:
            f.write('define ptr @f(ptr %p, i64 %a) {\n'
                    '  %q = getelementptr i8, ptr %p, i64 %a\n'
                    '  ret ptr %q\n}\n')
        cls.legality = cli._legality(
            LLC, targets.get('AMDGPU'), ll,
            os.path.join(cls.tmp.name, 'legality.json'))

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _root(self, reg, interior):
        return next(r for r in self.records
                    if r['root'] == reg and r['interior'] == interior)

    def test_types(self):
        r = self._root('%5', 2)
        self.assertEqual(r['expr']['op'], 'G_PTR_ADD')
        self.assertEqual(r['expr']['type'], 'p0')
        self.assertEqual([i['type'] for i in r['inputs']], ['p0', 'i64'])
        r = self._root('%8', 2)
        self.assertEqual([i['type'] for i in r['inputs']], ['p3', 'i32'])

    def test_instances(self):
        inst = next(i for i in self.insts if i.expr == op(
            'G_PTR_ADD', 64, op('G_PTR_ADD', 64, V(0), V(1)), V(1)))
        self.assertEqual(inst.vk, ('p', 'i'))
        inst = next(i for i in self.insts if i.expr == op(
            'G_PTRTOINT', 32, op('G_PTR_ADD', 32, V(0), V(1))))
        self.assertEqual(inst.vk, ('p', 'i'))
        self.assertEqual(inst.input_types, ('p3', 'i32'))
        # A compare of a pointer of the tree and another pointer.
        inst = next(i for i in self.insts if i.expr == op(
            'G_ICMP:eq', 1, op('G_PTR_ADD', 64, V(0), V(1)), V(2)))
        self.assertEqual(inst.vk, ('p', 'i', 'p'))

    def test_pointer_constant_is_an_input(self):
        # A constant of a pointer type has its bits, like an integer.
        r = self._root('%12', 1)
        self.assertEqual(r['inputs'][1]['type'], 'p0')
        self.assertEqual(r['inputs'][1]['def'], 'G_CONSTANT')
        self.assertEqual(r['inputs'][1]['const'], '0x0')
        self.assertEqual(r['inputs'][1]['zero'], '0xFFFFFFFFFFFFFFFF')

    def test_legality_table(self):
        self.assertIsNotNone(self.legality)
        cap = targets.Capability.load(self.legality)
        self.assertEqual(cap.action('G_PTR_ADD', (64, 64)), 'Legal')
        self.assertEqual(cap.action('G_PTR_ADD', (32, 32)), 'Legal')
        # The target has no pointer of 16 bits.
        self.assertEqual(cap.action('G_PTR_ADD', (16, 16)), 'Unsupported')
        self.assertTrue(cap.capable('G_PTR_ADD', [(64, 'p'), (64, 'i')]))
        self.assertTrue(cap.capable('G_PTRTOINT', [(64, 'p'), (64, 'i')]))


@unittest.skipUnless(HAVE_LLC, 'no llc (set GIRS_LLC)')
class ProbeTest(unittest.TestCase):
    """The function that selection runs a rule on is valid MIR."""

    def _probe(self, src, tgt, vw):
        rule = rule_of(src, tgt, vw)
        self.assertIsNotNone(rule)
        (name, ex), = select.examples(rule)
        mir = select.build_mir(rule, ex, name, targets.get('AMDGPU'))
        p = subprocess.run(
            [LLC, '-mtriple=amdgcn-amd-amdhsa', '-x', 'mir',
             '-run-pass=none', '-verify-machineinstrs', '-o', '/dev/null',
             '-'], input=mir, capture_output=True, text=True)
        self.assertEqual(p.returncode, 0, p.stderr + mir)
        return mir

    def test_add_chain(self):
        mir = self._probe(CHAIN, CHAIN_TGT, (64, 64, 64))
        # One pointer register for the variable, and an integer output.
        self.assertEqual(mir.count(':_(p0) = G_INTTOPTR'), 1)
        self.assertEqual(mir.count(':_(p0) = G_PTR_ADD'), 2)
        self.assertIn('G_PTRTOINT', mir)

    def test_narrow_pointer(self):
        src = op('G_PTR_ADD', 32, op('G_PTR_ADD', 32, V(0), V(1)), V(2))
        tgt = op('G_PTR_ADD', 32, V(0), op('G_ADD', 32, V(1), V(2)))
        mir = self._probe(src, tgt, (32, 32, 32))
        self.assertEqual(mir.count(':_(p3) = G_PTR_ADD'), 2)

    def test_no_pointer_of_the_width(self):
        rule = rule_of(op('G_PTR_ADD', 16, op('G_PTR_ADD', 16, V(0), V(1)),
                          V(2)),
                       op('G_PTR_ADD', 16, V(0), op('G_ADD', 16, V(1),
                                                    V(2))), (16, 16, 16))
        (name, ex), = select.examples(rule)
        with self.assertRaises(ValueError):
            select.build_mir(rule, ex, name, targets.get('AMDGPU'))


if __name__ == '__main__':
    unittest.main()
