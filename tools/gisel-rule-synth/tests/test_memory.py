#!/usr/bin/env python3
"""Tests of the model of memory. A load after a G_STORE through the same
pointer register, with no instruction between them that can write memory,
reads the low bits of the stored value: the load is an operator on that
value. The result of each other load is an input, and the result of an
extending load has the fact of a G_ASSERT_ZEXT or G_ASSERT_SEXT. Each
other instruction that reads or writes memory is no operator of a tree.

Run:  python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests
"""

import importlib.util
import json
import os
import re
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import z3  # noqa: E402

from girs import (compose, corpus, emit, ir, ops, select, sibling,  # noqa: E402
                  smt, synth, targets)

_spec = importlib.util.spec_from_file_location(
    'gi_rule_synth_cli', os.path.join(ROOT, 'gi-rule-synth.py'))
cli = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cli)

LLVM = os.path.dirname(os.path.dirname(os.path.dirname(ROOT)))
LLC = os.environ.get('GIRS_LLC') or os.path.join(LLVM, 'build', 'bin', 'llc')
HAVE_LLC = os.path.exists(LLC)


def V(i):
    return ('var', i)


def op(name, w, *args):
    return (name, w) + args


def status(src, tgt, vw):
    enc = smt.Encoder(vw, src[1])
    f = smt.refinement_violation(enc, src, tgt, z3.BoolVal(True))
    return smt.Z3Backend().check(f).status


def instance(src, vw, facts=None):
    n = len(vw)
    return corpus.Instance(src, vw, facts or [(0, 0)] * n, [None] * n,
                           [1] * len(ir.interior_nodes(src)), [],
                           [('f', 'fn', '%0')])


def rule_of(src, tgt, vw, facts=None):
    s = synth.Synthesizer(smt.Z3Backend())
    inst = instance(src, vw, facts)
    if s.add(inst, tgt) is None:
        return None
    s.finalize([inst])
    (rule,) = s.rules.values()
    return rule


LOAD32 = op('G_LOAD:32', 32, V(0))
LOAD8 = op('G_LOAD:8', 8, V(0))
ZEXT8 = op('G_ZEXTLOAD:8', 32, V(0))
SEXT8 = op('G_SEXTLOAD:8', 32, V(0))


class RegistryTest(unittest.TestCase):
    def test_contract(self):
        for name in ops.LOADS:
            info = ops.REGISTRY[name]
            self.assertTrue(info.forwarded)
            self.assertEqual(info.attr, 'imm')
            self.assertFalse(info.lanewise)
            # A rule does not create a load.
            self.assertNotEqual(info.rhs(), 'yes')
            self.assertNotEqual(ops.capability(info, 'emit'), 'yes')
            for st in ('typecheck', 'eval', 'smt'):
                self.assertEqual(ops.capability(info, st), 'yes')

    def test_signatures(self):
        tc = ops.REGISTRY['G_LOAD'].typecheck
        # The result has the bits of the memory. (A G_LOAD with a wider
        # result has no model: its high bits are not specified.)
        self.assertTrue(tc(32, [32], 32, 0))
        self.assertTrue(tc(8, [32], 8, 0))
        self.assertFalse(tc(32, [32], 8, 0))
        self.assertFalse(tc(32, [16], 32, 0))
        self.assertFalse(tc(32, [32], None, 0))
        for name in ('G_ZEXTLOAD', 'G_SEXTLOAD'):
            tc = ops.REGISTRY[name].typecheck
            self.assertTrue(tc(32, [32], 8, 0))
            self.assertTrue(tc(32, [8], 8, 0))
            self.assertFalse(tc(32, [32], 32, 0))
            self.assertFalse(tc(32, [8], 16, 0))
        # No lanes of a vector in memory.
        self.assertFalse(ops.REGISTRY['G_LOAD'].typecheck(
            ops.vec(2, 32), [ops.vec(2, 32)], 64, 0))

    def test_values(self):
        vw = (32,)
        self.assertEqual(ir.evaluate(LOAD32, vw, [0x12345678]), 0x12345678)
        self.assertEqual(ir.evaluate(LOAD8, vw, [0x12345678]), 0x78)
        self.assertEqual(ir.evaluate(ZEXT8, vw, [0x123456f8]), 0xf8)
        self.assertEqual(ir.evaluate(SEXT8, vw, [0x123456f8]), 0xfffffff8)
        self.assertEqual(ir.evaluate(SEXT8, vw, [0x12345678]), 0x78)
        # The memory has the poison of the stored value.
        self.assertIsNone(ir.evaluate(SEXT8, vw, [None]))

    def test_kind_of_the_stored_value(self):
        info = ops.REGISTRY['G_LOAD']
        for k in 'ifp':
            self.assertEqual(info.result_kind([k]), k)

    def test_other_memory_instructions(self):
        """Each generic opcode that reads or writes memory is in the
        registry: a load with a model, or an instruction that is no
        operator of a tree, with the reason."""
        path = os.path.join(LLVM, 'llvm', 'include', 'llvm', 'Support',
                            'TargetOpcodes.def')
        with open(path) as f:
            names = re.findall(r'HANDLE_TARGET_OPCODE\((G_\w+)\)', f.read())
        mem = [n for n in names if re.search(
            r'LOAD|(?<!RE)STORE|ATOMIC|^G_MEM|BZERO', n)]
        self.assertGreater(len(mem), 40)
        for n in mem:
            self.assertIn(n, ops.REGISTRY, n)
        for n in ops.MEMORY_WRITERS + ops.MEMORY_READERS:
            self.assertIn(n, mem)
            info = ops.REGISTRY[n]
            self.assertEqual(ops.capability(info, 'import'), 'yes')
            for st in ops.STAGES[1:]:
                self.assertIn('memory', ops.capability(info, st))
            self.assertNotEqual(info.rhs(), 'yes')
        for n in ops.MEMORY_WRITERS:
            self.assertFalse(ops.known(n) and ops.has_semantics(n))


class ProofTest(unittest.TestCase):
    def test_same_bits(self):
        self.assertEqual(status(LOAD32, V(0), (32,)), 'unsat')

    def test_low_bits_of_a_wider_value(self):
        self.assertEqual(status(LOAD8, op('G_TRUNC', 8, V(0)), (32,)),
                         'unsat')
        self.assertEqual(status(
            ZEXT8, op('G_AND', 32, V(0), ('const', 32, 255)), (32,)),
            'unsat')
        self.assertEqual(status(SEXT8, op('G_SEXT_INREG:8', 32, V(0)),
                                (32,)), 'unsat')

    def test_extension_is_not_the_value(self):
        self.assertEqual(status(ZEXT8, V(0), (32,)), 'sat')
        self.assertEqual(status(SEXT8, V(0), (32,)), 'sat')
        self.assertEqual(status(ZEXT8, op('G_SEXT_INREG:8', 32, V(0)),
                                (32,)), 'sat')
        self.assertEqual(status(SEXT8, op(
            'G_AND', 32, V(0), ('const', 32, 255)), (32,)), 'sat')

    def test_extension_of_a_value_with_the_bits_of_the_memory(self):
        self.assertEqual(status(ZEXT8, op('G_ZEXT', 32, V(0)), (8,)),
                         'unsat')
        self.assertEqual(status(SEXT8, op('G_SEXT', 32, V(0)), (8,)),
                         'unsat')
        self.assertEqual(status(SEXT8, op('G_ZEXT', 32, V(0)), (8,)), 'sat')

    def test_through_an_operator(self):
        src = op('G_AND', 32, ZEXT8, ('const', 32, 0xff))
        self.assertEqual(status(src, ZEXT8, (32,)), 'unsat')


class SynthesisTest(unittest.TestCase):
    def test_rule(self):
        rule = rule_of(LOAD32, V(0), (32,))
        self.assertIsNotNone(rule)
        self.assertEqual(rule['precondition'], 'true')
        self.assertEqual(rule['class'], 'reduces_cost')

    def test_wrong_replacement(self):
        self.assertIsNone(rule_of(SEXT8, V(0), (32,)))


    def test_no_rule_with_several_roots(self):
        """The value of the load is no operand of its instruction: a rule
        cannot find the load from the value."""
        add = op('G_ADD', 32, V(0), V(1))
        self.assertTrue(ir.has_forwarded_load(LOAD32))
        self.assertTrue(ir.has_forwarded_load(op('G_ADD', 32, LOAD32, V(1))))
        self.assertFalse(ir.has_forwarded_load(add))
        self.assertTrue(sibling.freeze_ok(add, [op('G_SUB', 32, V(0), V(1))]))
        self.assertFalse(sibling.freeze_ok(add, [LOAD32]))
        self.assertFalse(sibling.freeze_ok(LOAD32, [add]))

    def test_no_composition_step(self):
        rule = rule_of(LOAD32, V(0), (32,))
        index = compose.Index([rule], with_axioms=False)
        self.assertNotIn(rule['id'], index.ids)


class ReaderTest(unittest.TestCase):
    def test_forwarded_load(self):
        rec = {'fn': 'f', 'bb': 0, 'root': '%5', 'interior': 1, 'inputs': [
            {'reg': '%0', 'w': 32, 'type': 's32', 'zero': '0x0',
             'one': '0x0'}],
            'expr': {'op': 'G_SEXTLOAD', 'imm': 8, 'w': 32, 'type': 's32',
                     'reg': '%5', 'zero': '0x0', 'one': '0x0', 'uses': 1,
                     'args': [{'in': 0}]}}
        inst = corpus.parse_record(rec)
        self.assertEqual(inst.expr, SEXT8)
        self.assertEqual(inst.vw, (32,))

    def test_extending_load_is_a_hint(self):
        """The result of the load is the input, and the hint is a node
        with the register of the load."""
        rec = {'fn': 'f', 'bb': 0, 'root': '%7', 'interior': 2, 'inputs': [
            {'reg': '%4', 'w': 32, 'type': 's32', 'zero': '0xffffff00',
             'one': '0x0', 'def': 'G_ZEXTLOAD'},
            {'reg': '%1', 'w': 32, 'type': 's32', 'zero': '0x0',
             'one': '0x0'}],
            'expr': {'op': 'G_ADD', 'w': 32, 'type': 's32', 'reg': '%7',
                     'zero': '0x0', 'one': '0x0', 'uses': 1, 'args': [
                         {'op': 'G_ASSERT_ZEXT', 'imm': 8, 'load': True,
                          'w': 32, 'type': 's32', 'reg': '%4',
                          'zero': '0xffffff00', 'one': '0x0', 'uses': 2,
                          'args': [{'in': 0}]},
                         {'in': 1}]}}
        inst = corpus.parse_record(rec)
        self.assertEqual(inst.expr, op(
            'G_ADD', 32, op('G_ASSERT_ZEXT:8', 32, V(0)), V(1)))


class EmitTest(unittest.TestCase):
    def test_root_load(self):
        rule = rule_of(SEXT8, op('G_SEXT_INREG:8', 32, V(0)), (32,))
        self.assertIsNone(emit.why_not_emittable(rule))
        (pats,) = emit.variants(rule)
        # The load and its pointer: no operand of the load has the value.
        self.assertEqual(pats[0], '(G_SEXTLOAD $dst, $dst_ptr)')
        self.assertIn('gisynth::getForwardedStoreValue(MRI, '
                      '${dst}.getReg(), 8).isValid()', pats[1])
        td = emit.emit_td([rule], {'AMDGPU': [rule]})[0]
        # The guard and the apply function take the value of the G_STORE.
        value = 'gisynth::getForwardedStoreValue(MRI, ${dst}.getReg(), 8)'
        self.assertEqual(td.count(value), 3)
        self.assertNotIn('${x0}', td)
        self.assertNotIn('$x0', td)

    def test_replacement_is_the_value(self):
        rule = rule_of(LOAD32, V(0), (32,))
        self.assertTrue(emit._rule_needs_cpp_apply(rule))
        self.assertIn('B.buildCopy(Dst, X0);', emit._cpp_apply(rule))

    def test_load_below_the_root(self):
        """The guard finds the G_STORE of the root only."""
        src = op('G_AND', 32, ZEXT8, ('const', 32, 0xff))
        rule = rule_of(src, ZEXT8, (32,))
        if rule is not None:
            self.assertIn('load', emit.why_not_emittable(rule))

    def test_extending_load_in_the_place_of_a_hint(self):
        src = op('G_SEXT_INREG:16', 32, op('G_ASSERT_SEXT:16', 32, V(0)))
        rule = rule_of(src, V(0), (32,))
        self.assertIsNone(emit.why_not_emittable(rule))
        hint, load = emit.variants(rule)
        self.assertIn('(G_ASSERT_SEXT $t0, $x0, $t0_i)', hint)
        self.assertEqual(hint.subst, {})
        # The load defines the variable, and the hint is no instruction.
        self.assertIn('(G_SEXTLOAD $x0, $t0_ptr)', load)
        self.assertIn('(G_SEXT_INREG $dst, $x0, $dst_i)', load)
        self.assertFalse(any('G_ASSERT' in p for p in load))
        self.assertIn('gisynth::isExtLoadOf(MRI, ${x0}.getReg(), '
                      '/*Signed=*/true, 16)', load[-1])
        self.assertEqual(load.subst, {'t0': 'x0'})
        td = emit.emit_td([rule], {'AMDGPU': [rule]})[0]
        records = td.split('def synth_')[1:3]
        self.assertIn('${t0}.getReg()', records[0])
        self.assertNotIn('${t0}', records[1])
        self.assertNotIn('$t0,', records[1])

    def test_zero_extending_load(self):
        src = op('G_AND', 32, op('G_ASSERT_ZEXT:8', 32, V(0)), V(1))
        rule = rule_of(src, V(0), (32, 32),
                       [(0xffffff00, 0), (0xffffff00, 0xff)])
        self.assertIsNotNone(rule)
        loads = [p for p in emit.variants(rule) if p.subst]
        self.assertTrue(loads)
        for p in loads:
            self.assertIn('(G_ZEXTLOAD $x0, $t0_ptr)', p)
            self.assertIn('/*Signed=*/false, 8)', p[-1])

    def test_no_load_form_without_a_gain(self):
        """A hint is no instruction: a rule that only removes the hint
        removes nothing from a source with a load."""
        src = op('G_ADD', 32, op('G_ASSERT_ZEXT:8', 32, V(0)), V(1))
        rule = rule_of(src, op('G_ADD', 32, V(0), V(1)), (32, 32))
        self.assertIsNotNone(rule)
        self.assertFalse([p for p in emit.variants(rule) if p.subst])


MEM_MIR = '''
---
name: fwd_int
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0, $vgpr1, $vgpr2
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s32) = COPY $vgpr2
    %3:_(p1) = G_MERGE_VALUES %1, %2
    G_STORE %0(s32), %3(p1) :: (store (s32), addrspace 1)
    %4:_(s32) = G_ADD %0, %1
    %5:_(s32) = G_LOAD %3(p1) :: (load (s32), addrspace 1)
    %6:_(s32) = G_XOR %5, %4
    $vgpr0 = COPY %6
    SI_RETURN implicit $vgpr0
...
---
name: fwd_trunc
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0, $vgpr1, $vgpr2
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s32) = COPY $vgpr2
    %3:_(p1) = G_MERGE_VALUES %1, %2
    G_STORE %0(s32), %3(p1) :: (store (s8), addrspace 1)
    %4:_(s32) = G_ZEXTLOAD %3(p1) :: (load (s8), addrspace 1)
    %5:_(s32) = G_SEXTLOAD %3(p1) :: (load (s8), addrspace 1)
    %6:_(s8) = G_LOAD %3(p1) :: (load (s8), addrspace 1)
    %7:_(s32) = G_ANYEXT %6
    %8:_(s32) = G_ADD %4, %5
    %9:_(s32) = G_ADD %8, %7
    $vgpr0 = COPY %9
    SI_RETURN implicit $vgpr0
...
---
name: barriers
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0, $vgpr1, $vgpr2, $vgpr3
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s32) = COPY $vgpr2
    %10:_(s32) = COPY $vgpr3
    %3:_(p1) = G_MERGE_VALUES %1, %2
    %11:_(p1) = G_MERGE_VALUES %0, %10
    ; Another store between them.
    G_STORE %0(s32), %3(p1) :: (store (s32), addrspace 1)
    G_STORE %1(s32), %11(p1) :: (store (s32), addrspace 1)
    %20:_(s32) = G_LOAD %3(p1) :: (load (s32), addrspace 1)
    ; A volatile store.
    G_STORE %0(s32), %3(p1) :: (volatile store (s32), addrspace 1)
    %21:_(s32) = G_LOAD %3(p1) :: (load (s32), addrspace 1)
    ; A volatile load.
    G_STORE %0(s32), %3(p1) :: (store (s32), addrspace 1)
    %22:_(s32) = G_LOAD %3(p1) :: (volatile load (s32), addrspace 1)
    ; An atomic load.
    G_STORE %0(s32), %3(p1) :: (store (s32), addrspace 1)
    %23:_(s32) = G_LOAD %3(p1) :: (load seq_cst (s32), addrspace 1)
    ; Another number of bits.
    G_STORE %0(s32), %3(p1) :: (store (s32), addrspace 1)
    %24:_(s32) = G_ZEXTLOAD %3(p1) :: (load (s8), addrspace 1)
    ; Another pointer register.
    G_STORE %0(s32), %3(p1) :: (store (s32), addrspace 1)
    %25:_(s32) = G_LOAD %11(p1) :: (load (s32), addrspace 1)
    ; An atomic read-modify-write between them.
    G_STORE %0(s32), %3(p1) :: (store (s32), addrspace 1)
    %30:_(s32) = G_ATOMICRMW_ADD %11(p1), %1 :: (load store seq_cst (s32), addrspace 1)
    %26:_(s32) = G_LOAD %3(p1) :: (load (s32), addrspace 1)
    ; A memory intrinsic between them.
    G_STORE %0(s32), %3(p1) :: (store (s32), addrspace 1)
    %31:_(s64) = G_CONSTANT i64 4
    G_MEMCPY %11(p1), %3(p1), %31(s64), 0 :: (store (s8), addrspace 1), (load (s8), addrspace 1)
    %27:_(s32) = G_LOAD %3(p1) :: (load (s32), addrspace 1)
    ; The bits of an integer as a pointer.
    G_STORE %2(s32), %3(p1) :: (store (s32), addrspace 1)
    %28:_(p3) = G_LOAD %3(p1) :: (load (p3), addrspace 1)
    %29:_(s32) = G_PTRTOINT %28
    ; A result that is wider than the memory: the high bits are not
    ; specified.
    G_STORE %2(s32), %3(p1) :: (store (s8), addrspace 1)
    %32:_(s32) = G_LOAD %3(p1) :: (load (s8), addrspace 1)
    %40:_(s32) = G_OR %20, %21
    %41:_(s32) = G_OR %40, %22
    %42:_(s32) = G_OR %41, %23
    %43:_(s32) = G_OR %42, %24
    %44:_(s32) = G_OR %43, %25
    %45:_(s32) = G_OR %44, %26
    %46:_(s32) = G_OR %45, %27
    %47:_(s32) = G_OR %46, %29
    %48:_(s32) = G_OR %47, %30
    %49:_(s32) = G_OR %48, %32
    $vgpr0 = COPY %49
    SI_RETURN implicit $vgpr0
...
---
name: extload
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0, $vgpr1, $vgpr2
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s32) = COPY $vgpr2
    %3:_(p1) = G_MERGE_VALUES %1, %2
    %4:_(s32) = G_ZEXTLOAD %3(p1) :: (load (s8), addrspace 1)
    %5:_(s32) = G_SEXTLOAD %3(p1) :: (load (s16), addrspace 1)
    %6:_(s32) = G_CONSTANT i32 255
    %7:_(s32) = G_AND %4, %6
    %8:_(s32) = G_SEXT_INREG %5, 16
    %9:_(s32) = G_ADD %7, %8
    $vgpr0 = COPY %9
    SI_RETURN implicit $vgpr0
...
'''

_LOADS = ('G_LOAD', 'G_ZEXTLOAD', 'G_SEXTLOAD')


@unittest.skipUnless(HAVE_LLC, 'no llc (set GIRS_LLC)')
class RealExtractionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        mir = os.path.join(cls.tmp.name, 'mem.mir')
        with open(mir, 'w') as f:
            f.write(MEM_MIR)
        _, out = cli._extract_one(LLC, mir, cls.tmp.name, 'mir',
                                  targets.get('AMDGPU'))
        assert out, 'the extractor failed'
        with open(out) as f:
            cls.records = [json.loads(l) for l in f if l.strip()]
        cls.insts, cls.stats = corpus.load([out])

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _roots(self, fn):
        return {r['root']: r['expr'] for r in self.records
                if r['fn'] == fn and r['expr'].get('op') in _LOADS}

    def test_every_record_is_read(self):
        self.assertEqual(self.stats['unsupported'], 0)

    def test_load_after_a_store(self):
        (e,) = self._roots('fwd_int').values()
        self.assertEqual((e['op'], e['imm'], e['w']), ('G_LOAD', 32, 32))
        self.assertEqual(e['args'], [{'in': 0}])
        srcs = {ir.to_sexpr(i.expr) for i in self.insts}
        self.assertIn('(G_LOAD:32:s32 x0)', srcs)

    def test_value_is_the_stored_register(self):
        (rec,) = [r for r in self.records if r['fn'] == 'fwd_int' and
                  r['expr'].get('op') == 'G_LOAD']
        self.assertEqual(rec['inputs'][0]['reg'], '%0')

    def test_low_bits_of_a_wider_value(self):
        roots = self._roots('fwd_trunc')
        self.assertEqual(sorted((e['op'], e['imm'], e['w'])
                                for e in roots.values()),
                         [('G_LOAD', 8, 8), ('G_SEXTLOAD', 8, 32),
                          ('G_ZEXTLOAD', 8, 32)])

    def test_no_value_across_a_writer(self):
        self.assertEqual(self._roots('barriers'), {})

    def test_load_is_no_node_below_a_root(self):
        def walk(n, root=True):
            if not root:
                self.assertNotIn(n.get('op'), _LOADS, n)
            for a in n.get('args', ()):
                walk(a, False)
        for r in self.records:
            walk(r['expr'])

    def test_extending_load_is_a_fact(self):
        hints = []

        def walk(n):
            if n.get('load'):
                hints.append((n['op'], n['imm']))
                # The operand is the result of the load.
                self.assertEqual(n['args'], [{'in': 0}])
            for a in n.get('args', ()):
                walk(a)
        for r in self.records:
            if r['fn'] == 'extload' and r['interior'] == 2:
                walk(r['expr'])
        self.assertEqual(sorted(set(hints)),
                         [('G_ASSERT_SEXT', 16), ('G_ASSERT_ZEXT', 8)])
        srcs = {ir.to_sexpr(i.expr) for i in self.insts}
        self.assertIn('(G_SEXT_INREG:16:s32 (G_ASSERT_SEXT:16:s32 x0))',
                      srcs)


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

    def test_store_then_load(self):
        mir = self._probe(rule_of(LOAD32, V(0), (32,)))
        self.assertRegex(mir, r'G_STORE %\d+, (%\d+) :: \(store \(s32\), '
                         r'addrspace \d+\)\n.* = G_LOAD \1 :: \(load \(s32\)')

    def test_extending_load(self):
        mir = self._probe(rule_of(SEXT8, op('G_SEXT_INREG:8', 32, V(0)),
                                  (32,)))
        self.assertIn('G_SEXTLOAD', mir)
        self.assertIn('(store (s8)', mir)

    def test_narrow_load(self):
        mir = self._probe(rule_of(LOAD8, op('G_TRUNC', 8, V(0)), (32,)))
        self.assertIn('(load (s8)', mir)


if __name__ == '__main__':
    unittest.main()
