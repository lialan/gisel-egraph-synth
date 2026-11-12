#!/usr/bin/env python3
"""Tests of the model of G_PHI: the value is the incoming value of the edge
that the control flow took. The edge is an input of the source that no
register has: a proof holds for each edge, and a replacement, a precondition
and a pattern do not read it.

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

from girs import (compose, corpus, discover, emit, ir, ops,  # noqa: E402
                  precond, select, sibling, smt, synth, targets, vector)

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


def phi(w, edge, *ins):
    return ('G_PHI', w, V(edge)) + ins


def status(src, tgt, vw, guard=None):
    enc = smt.Encoder(vw, src[1])
    f = smt.refinement_violation(
        enc, src, tgt, z3.BoolVal(True) if guard is None else guard(enc))
    return smt.Z3Backend().check(f).status


def instance(src, vw, facts=None, kinds=None):
    n = len(vw)
    return corpus.Instance(src, vw, facts or [(0, 0)] * n, [None] * n,
                           [1] * len(ir.interior_nodes(src)), [],
                           [('f', 'fn', '%0')], kinds=kinds)


def rule_of(src, tgt, vw, facts=None, kinds=None):
    s = synth.Synthesizer(smt.Z3Backend())
    inst = instance(src, vw, facts, kinds)
    if s.add(inst, tgt) is None:
        return None
    s.finalize([inst])
    (rule,) = s.rules.values()
    return rule


# x1 & 15 == 0 and x2 & 15 == 0: the G_AND with 15 is 0 for each edge.
MASKED = op('G_AND', 32, phi(32, 0, V(1), V(2)), V(3))
MASKED_VW = (1, 32, 32, 32)
MASKED_FACTS = [(0, 0, True), (0xff, 0), (0xffff, 0),
                (0xfffffff0, 0xf, True)]


class RegistryTest(unittest.TestCase):
    def test_contract(self):
        info = ops.REGISTRY['G_PHI']
        self.assertTrue(info.phi)
        self.assertEqual(info.lhs(), 'yes')
        self.assertNotEqual(info.rhs(), 'yes')
        self.assertEqual(ops.capability(info, 'emit'),
                         'a rule can match G_PHI but does not create it')
        self.assertEqual(ops.capability(info, 'discovery'),
                         'enumerative-source+egraph')
        self.assertNotIn('G_PHI', ops.rhs_operators())

    def test_signatures(self):
        ok = ops.typecheck
        self.assertTrue(ok('G_PHI', 32, [1, 32]))
        self.assertTrue(ok('G_PHI', 32, [1, 32, 32]))
        self.assertTrue(ok('G_PHI', 32, [2, 32, 32, 32]))
        self.assertTrue(ok('G_PHI', 32, [2, 32, 32, 32, 32]))
        # The edge has the width for the number of incoming values.
        self.assertFalse(ok('G_PHI', 32, [1, 32, 32, 32]))
        self.assertFalse(ok('G_PHI', 32, [2, 32, 32]))
        self.assertFalse(ok('G_PHI', 32, [1, 32, 16]))
        self.assertFalse(ok('G_PHI', 32, [1]))
        self.assertFalse(ok('G_PHI', 32, [4] + [32] * 5))
        # One edge for all the lanes of a vector.
        v4 = ops.vec(4, 32)
        self.assertTrue(ok('G_PHI', v4, [1, v4, v4]))
        self.assertFalse(ok('G_PHI', v4, [1, v4, 32]))

    def test_kinds(self):
        e = op('G_FNEG', 32, phi(32, 0, V(1), V(2)))
        self.assertEqual(ir.var_kinds(e), {0: 'i', 1: 'f', 2: 'f'})
        e = op('G_PTR_ADD', 64, phi(64, 0, V(1), V(2)), V(3))
        self.assertEqual(ir.var_kinds(e), {0: 'i', 1: 'p', 2: 'p', 3: 'i'})
        info = ops.REGISTRY['G_PHI']
        self.assertEqual(info.result_kind(['i', 'f', 'f']), 'f')
        self.assertIsNone(info.result_kind(['i', 'f', 'i']))

    def test_values(self):
        e = phi(32, 0, V(1), V(2), V(3))
        vw = (2, 32, 32, 32)
        self.assertEqual(ir.evaluate(e, vw, [0, 7, 8, 9]), 7)
        self.assertEqual(ir.evaluate(e, vw, [1, 7, 8, 9]), 8)
        self.assertEqual(ir.evaluate(e, vw, [2, 7, 8, 9]), 9)
        # An edge that no incoming value has: the last one.
        self.assertEqual(ir.evaluate(e, vw, [3, 7, 8, 9]), 9)
        # Poison only if the incoming value of the edge is poison.
        self.assertEqual(ir.evaluate(e, vw, [0, 7, None, 9]), 7)
        self.assertIsNone(ir.evaluate(e, vw, [1, 7, None, 9]))


class FormTest(unittest.TestCase):
    def test_edge_vars(self):
        self.assertEqual(ir.edge_vars(MASKED), {0})
        self.assertEqual(ir.edge_vars(op('G_AND', 32, V(0), V(1))), set())
        self.assertIsNone(ir.phi_error(MASKED))
        self.assertIsNone(ir.phi_error(op('G_AND', 32, V(0), V(1))))

    def test_one_edge_for_two_phis(self):
        """A pattern matches each G_PHI with an instruction of its own:
        two of them can have different edges."""
        e = op('G_SUB', 32, phi(32, 0, V(1), V(2)), phi(32, 0, V(1), V(2)))
        self.assertIsNotNone(ir.phi_error(e))
        e = op('G_SUB', 32, phi(32, 0, V(1), V(2)), phi(32, 3, V(1), V(2)))
        self.assertIsNone(ir.phi_error(e))
        # With an edge of its own for each, the two are not equal.
        self.assertEqual(status(e, ('lit', 32, '0'), (1, 32, 32, 1)), 'sat')

    def test_edge_is_read_only_by_its_phi(self):
        e = op('G_SELECT', 32, V(0), phi(32, 0, V(1), V(2)), V(1))
        self.assertIsNotNone(ir.phi_error(e))
        e = phi(32, 0, op('G_ADD', 32, V(1), V(2)), V(1))
        self.assertIsNotNone(ir.phi_error(e))


class ProofTest(unittest.TestCase):
    def test_equal_incoming_values(self):
        self.assertEqual(status(phi(32, 0, V(1), V(1)), V(1), (1, 32)),
                         'unsat')
        e = phi(32, 0, V(1), V(1), V(1), V(1))
        self.assertEqual(status(e, V(1), (2, 32)), 'unsat')

    def test_each_edge(self):
        e = phi(32, 0, V(1), V(2))
        self.assertEqual(status(e, V(1), (1, 32, 32)), 'sat')
        self.assertEqual(status(e, V(2), (1, 32, 32)), 'sat')
        # The last of three incoming values has two numbers.
        e = phi(32, 0, V(1), V(1), V(2))
        self.assertEqual(status(e, V(1), (2, 32, 32)), 'sat')

    def test_condition_for_each_incoming_value(self):
        zero = ('lit', 32, '0')
        rule = rule_of(MASKED, zero, MASKED_VW, MASKED_FACTS)
        (both,) = emit.rule_dnf(rule)
        self.assertEqual(len(both), 2)

        def guard(atoms):
            return lambda enc: precond.z3_dnf([atoms], enc)
        self.assertEqual(status(MASKED, zero, MASKED_VW, guard(both)),
                         'unsat')
        for a in both:
            self.assertEqual(status(MASKED, zero, MASKED_VW, guard([a])),
                             'sat')

    def test_poison_of_the_other_edge(self):
        """The replacement reads both incoming values: it is poison if
        the incoming value of the other edge is poison."""
        e = phi(32, 0, V(1), V(2))
        tgt = op('G_OR', 32, op('G_AND', 32, V(1), V(2)), V(1))
        self.assertEqual(status(phi(32, 0, V(1), V(1)), V(1), (1, 32)),
                         'unsat')
        self.assertEqual(status(e, tgt, (1, 32, 32)), 'sat')

    def test_through_an_operator(self):
        src = op('G_XOR', 32, phi(32, 0, V(1), V(1)), V(2))
        self.assertEqual(status(src, op('G_XOR', 32, V(1), V(2)),
                                (1, 32, 32)), 'unsat')

    def test_float(self):
        src = op('G_FNEG', 32, op('G_FNEG', 32, phi(32, 0, V(1), V(1))))
        self.assertEqual(status(src, V(1), (1, 32)), 'unsat')


class SynthesisTest(unittest.TestCase):
    def test_replacement_does_not_read_the_edge(self):
        """phi(e; 0, 1) of one bit has the value of the edge, and no
        register has the edge."""
        src = phi(1, 0, V(1), V(2))
        facts = [(0, 0, True), (1, 0, True), (0, 1, True)]
        s = synth.Synthesizer(smt.Z3Backend())
        inst = instance(src, (1, 1, 1), facts)
        inst.consts = (None, 0, 1)
        self.assertIsNone(s.add(inst, V(0)))
        self.assertEqual(s.stats['phi_rejected'], 1)
        cands, _ = discover.discover(inst, smt.Z3Backend(),
                                     discover.Limits(grammar='all'))
        for c in cands:
            self.assertNotIn(0, ir.variables(c['tgt']), c)

    def test_precondition_does_not_read_the_edge(self):
        rule = rule_of(MASKED, ('lit', 32, '0'), MASKED_VW, MASKED_FACTS)
        self.assertIsNotNone(rule)
        edge = ir.edge_vars(ir.from_json(rule['source_json']))
        self.assertEqual(len(edge), 1)
        for p in emit.rule_dnf(rule):
            self.assertTrue(p)
            for a in p:
                self.assertFalse(edge & set(precond.atom_all_vars(a)), a)
        # Both incoming values are in each condition.
        self.assertEqual(rule['precondition'],
                         'all(KZ(x1) | KZ(x3)) && all(KZ(x2) | KZ(x3))')

    def test_search(self):
        inst = instance(op('G_ADD', 32, phi(32, 0, V(1), V(1)), V(2)),
                        (1, 32, 32))
        cands, _ = discover.discover(inst, smt.Z3Backend())
        self.assertIn(op('G_ADD', 32, V(1), V(2)),
                      [c['tgt'] for c in cands])

    def test_no_rule_with_several_roots(self):
        a = op('G_ADD', 32, phi(32, 0, V(1), V(1)), V(2))
        self.assertFalse(sibling.freeze_ok(a, []))
        self.assertFalse(sibling.freeze_ok(op('G_ADD', 32, V(1), V(2)),
                                           [phi(32, 0, V(1), V(1))]))

    def test_no_composition_step(self):
        rule = rule_of(op('G_XOR', 32, phi(32, 0, V(1), V(1)), V(2)),
                       op('G_XOR', 32, V(1), V(2)), (1, 32, 32))
        index = compose.Index([rule], with_axioms=False)
        self.assertNotIn(rule['id'], index.ids)


class ReaderTest(unittest.TestCase):
    REC = {'fn': 'f', 'bb': 2, 'root': '%5', 'interior': 2, 'inputs': [
        {'reg': '%0', 'w': 32, 'type': 's32', 'zero': '0xff', 'one': '0x0'},
        {'reg': '%1', 'w': 32, 'type': 's32', 'zero': '0xffff',
         'one': '0x0'},
        {'reg': '%2', 'w': 32, 'type': 's32', 'zero': '0xfffffff0',
         'one': '0xf', 'const': '0xf'}],
        'expr': {'op': 'G_AND', 'w': 32, 'type': 's32', 'reg': '%5',
                 'zero': '0xffffffff', 'one': '0x0', 'args': [
                     {'op': 'G_PHI', 'w': 32, 'type': 's32', 'reg': '%4',
                      'zero': '0xff', 'one': '0x0', 'uses': 1,
                      'args': [{'in': 0}, {'in': 1}]},
                     {'in': 2}]}}

    def test_edge_input(self):
        inst = corpus.parse_record(json.loads(json.dumps(self.REC)))
        self.assertEqual(inst.expr, MASKED)
        self.assertEqual(inst.vw, MASKED_VW)
        self.assertEqual(inst.vk, ('i', 'i', 'i', 'i'))
        # No register has the edge, and it is never poison.
        self.assertEqual(inst.regs, (None, '%0', '%1', '%2'))
        self.assertEqual(inst.facts[0], (0, 0, True))
        self.assertEqual(ir.to_sexpr(inst.expr),
                         '(G_AND:s32 (G_PHI:s32 x0 x1 x2) x3)')

    def test_edge_width(self):
        rec = json.loads(json.dumps(self.REC))
        rec['expr']['args'][0]['args'].append({'in': 0})
        inst = corpus.parse_record(rec)
        self.assertEqual(inst.vw, (2, 32, 32, 32))
        self.assertEqual(inst.expr, op(
            'G_AND', 32, phi(32, 0, V(1), V(2), V(1)), V(3)))

    def test_one_phi_twice_is_an_input(self):
        rec = json.loads(json.dumps(self.REC))
        p = rec['expr']['args'][0]
        rec['expr']['args'] = [p, json.loads(json.dumps(p))]
        inst = corpus.parse_record(rec)
        self.assertEqual(inst.expr, op('G_AND', 32, V(0), V(0)))

    def test_vector_is_read_lane_by_lane(self):
        rec = json.loads(json.dumps(self.REC))

        def widen(n):
            if 'w' in n:
                n['lanes'] = 4
                n['type'] = '<4 x s32>'
            for a in n.get('args', ()):
                widen(a)
        widen(rec['expr'])
        for i in rec['inputs']:
            widen(i)
        inst = corpus.parse_record(rec)
        self.assertTrue(inst.lifted)
        self.assertEqual(inst.expr, MASKED)
        self.assertEqual(inst.vw, MASKED_VW)


class EmitTest(unittest.TestCase):
    def test_pattern_and_guard(self):
        rule = rule_of(MASKED, ('lit', 32, '0'), MASKED_VW, MASKED_FACTS)
        self.assertIsNone(emit.why_not_emittable(rule))
        pats = emit.variants(rule)
        # The two incoming values are the same after a renaming: one
        # order, and the two orders of the G_AND.
        self.assertEqual(len(pats), 2)
        self.assertEqual(pats[0][0], '(G_PHI $t0, $x1, $t0_b0, $x2, $t0_b1)')
        self.assertEqual(pats[0][1], '(G_AND $dst, $t0, $x3)')
        self.assertEqual(
            pats[0][2], '[{ return gisynth::isStablePhi(MRI, Helper, '
            '${t0}.getReg()); }]')
        guard = emit._cpp_guard(rule)
        # No register for the edge: the widths of x1, x2, x3, t0, root.
        self.assertIn('Register Dst, Register X1, Register X2, Register X3, '
                      'Register T0)', guard)
        self.assertIn('getScalarWidths(MRI, {X1, X2, X3, T0, Dst}, W)',
                      guard)
        self.assertIn('unsigned W[5];', guard)
        self.assertNotIn('X0', guard)
        self.assertIn('{32, 32, 32, 32, 32}', guard)
        td, _ = emit.emit_td([rule], {})
        self.assertNotIn('${x0}', td)

    def test_each_order_of_the_incoming_values(self):
        """x1 is also an operand of the root: the two orders differ."""
        src = op('G_OR', 32, phi(32, 0, V(1), V(2)), V(1))
        facts = [(0, 0, True), (0, 0xff), (0xffffff00, 0)]
        rule = rule_of(src, V(1), (1, 32, 32), facts)
        self.assertIsNotNone(rule)
        phis = {p[0] for p in emit.variants(rule)}
        self.assertEqual(phis, {'(G_PHI $t0, $x1, $t0_b0, $x2, $t0_b1)',
                                '(G_PHI $t0, $x2, $t0_b0, $x1, $t0_b1)'})

    def test_root(self):
        rule = rule_of(phi(32, 0, V(1), V(1)), V(1), (1, 32))
        self.assertIsNone(emit.why_not_emittable(rule))
        td, _ = emit.emit_td([rule], {})
        self.assertIn('(match (G_PHI $dst, $x1, $dst_b0, $x1, $dst_b1),', td)
        self.assertIn('gisynth::isStablePhi(MRI, Helper, ${dst}.getReg())',
                      td)
        self.assertIn('(apply (GIReplaceReg $dst, $x1))', td)

    def test_root_with_a_new_instruction(self):
        src = phi(32, 0, V(1), V(2))
        facts = [(0, 0, True), (0xffffffff, 0, True), (0xffffffff, 0, True)]
        rule = rule_of(src, ('lit', 32, '0'), (1, 32, 32), facts)
        self.assertIsNotNone(rule)
        self.assertIn('G_PHI root', emit.why_not_emittable(rule))

    def test_scalar_rule_also_for_vectors(self):
        s = synth.Synthesizer(smt.Z3Backend())
        inst = instance(op('G_XOR', 32, phi(32, 0, V(1), V(1)), V(2)),
                        (1, 32, 32))
        inst.lifted = True
        rid = s.add(inst, op('G_XOR', 32, V(1), V(2)))
        s.finalize([inst])
        rule = s.rules[rid]
        self.assertTrue(emit.lifts(rule))
        self.assertIn('/*Lift=*/true', emit._cpp_guard(rule))


PHI_MIR = '''
---
name: same
tracksRegLiveness: true
body: |
  bb.0:
    successors: %bb.2, %bb.1
    liveins: $vgpr0, $vgpr1, $vgpr2
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s32) = COPY $vgpr2
    %3:_(s1) = G_TRUNC %2
    G_BRCOND %3(s1), %bb.2
    G_BR %bb.1
  bb.1:
    successors: %bb.2
    G_BR %bb.2
  bb.2:
    %4:_(s32) = G_PHI %0, %bb.0, %0, %bb.1
    %5:_(s32) = G_ADD %4, %1
    $vgpr0 = COPY %5
    SI_RETURN implicit $vgpr0
...
---
name: masked
tracksRegLiveness: true
body: |
  bb.0:
    successors: %bb.2, %bb.1
    liveins: $vgpr0, $vgpr1, $vgpr2
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s32) = COPY $vgpr2
    %3:_(s1) = G_TRUNC %2
    %10:_(s32) = G_CONSTANT i32 8
    %11:_(s32) = G_CONSTANT i32 16
    %12:_(s32) = G_CONSTANT i32 15
    %13:_(s32) = G_SHL %0, %10
    %14:_(s32) = G_SHL %1, %11
    G_BRCOND %3(s1), %bb.2
    G_BR %bb.1
  bb.1:
    successors: %bb.2
    G_BR %bb.2
  bb.2:
    %4:_(s32) = G_PHI %13, %bb.0, %14, %bb.1
    %5:_(s32) = G_AND %4, %12
    $vgpr0 = COPY %5
    SI_RETURN implicit $vgpr0
...
---
name: sunk
tracksRegLiveness: true
body: |
  bb.0:
    successors: %bb.2, %bb.1
    liveins: $vgpr0, $vgpr1, $vgpr2
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s32) = COPY $vgpr2
    %3:_(s1) = G_TRUNC %2
    %10:_(s32) = G_CONSTANT i32 8
    %12:_(s32) = G_CONSTANT i32 15
    G_BRCOND %3(s1), %bb.2
    G_BR %bb.1
  bb.1:
    successors: %bb.2
    %14:_(s32) = G_SHL %1, %10
    G_BR %bb.2
  bb.2:
    %4:_(s32) = G_PHI %0, %bb.0, %14, %bb.1
    %5:_(s32) = G_AND %4, %12
    $vgpr0 = COPY %5
    SI_RETURN implicit $vgpr0
...
---
name: loop
tracksRegLiveness: true
body: |
  bb.0:
    successors: %bb.1
    liveins: $vgpr0, $vgpr1
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s32) = G_CONSTANT i32 1
    G_BR %bb.1
  bb.1:
    successors: %bb.1, %bb.2
    %3:_(s32) = G_PHI %0, %bb.0, %4, %bb.1
    %4:_(s32) = G_ADD %3, %2
    %5:_(s1) = G_ICMP intpred(ult), %4, %1
    G_BRCOND %5(s1), %bb.1
    G_BR %bb.2
  bb.2:
    %6:_(s32) = G_PHI %4, %bb.1
    %7:_(s32) = G_XOR %6, %0
    $vgpr0 = COPY %7
    SI_RETURN implicit $vgpr0
...
'''


@unittest.skipUnless(HAVE_LLC, 'no llc (set GIRS_LLC)')
class RealExtractionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        mir = os.path.join(cls.tmp.name, 'phi.mir')
        with open(mir, 'w') as f:
            f.write(PHI_MIR)
        _, out = cli._extract_one(LLC, mir, cls.tmp.name, 'mir',
                                  targets.get('AMDGPU'))
        assert out, 'the extractor failed'
        with open(out) as f:
            cls.records = [json.loads(l) for l in f if l.strip()]
        cls.insts, cls.stats = corpus.load([out])

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _phis(self, fn):
        out = []

        def walk(n):
            if n.get('op') == 'G_PHI':
                out.append(n['reg'])
            for a in n.get('args', ()):
                walk(a)
        for r in self.records:
            if r['fn'] == fn:
                walk(r['expr'])
        return sorted(set(out))

    def test_every_record_is_read(self):
        self.assertEqual(self.stats['unsupported'], 0)

    def test_incoming_values_of_dominating_blocks(self):
        self.assertEqual(len(self._phis('same')), 1)
        self.assertEqual(len(self._phis('masked')), 1)
        srcs = {ir.to_sexpr(i.expr) for i in self.insts}
        self.assertIn('(G_ADD:s32 (G_PHI:s32 x0 x1 x1) x2)', srcs)
        self.assertIn('(G_AND:s32 (G_PHI:s32 x0 x1 x2) x3)', srcs)
        self.assertIn('(G_PHI:s32 x0 x1 x1)', srcs)

    def test_incoming_value_of_a_predecessor(self):
        """The block of %14 does not dominate the block of the G_PHI: the
        rule cannot read %14 at the G_AND."""
        self.assertEqual(self._phis('sunk'), [])

    def test_loop(self):
        """The G_PHI of the loop header reads a value of its own block
        (the value of the iteration before). The G_PHI after the loop
        reads a value of a block that dominates it."""
        self.assertEqual(len(self._phis('loop')), 1)
        srcs = {ir.to_sexpr(i.expr) for i in self.insts}
        self.assertIn('(G_XOR:s32 (G_PHI:s32 x0 x1) x2)', srcs)

    def test_incoming_values_are_inputs(self):
        for r in self.records:
            def walk(n):
                if n.get('op') == 'G_PHI':
                    self.assertTrue(all('in' in a for a in n['args']), n)
                for a in n.get('args', ()):
                    walk(a)
            walk(r['expr'])


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

    def test_two_incoming_values(self):
        mir = self._probe(rule_of(MASKED, ('lit', 32, '0'), MASKED_VW,
                                  MASKED_FACTS))
        self.assertIn('G_PHI', mir)
        self.assertIn('%bb.0, ', mir)
        self.assertIn('G_BRCOND', mir)

    def test_one_incoming_value(self):
        mir = self._probe(rule_of(
            op('G_XOR', 32, phi(32, 0, V(1)), V(2)),
            op('G_XOR', 32, V(1), V(2)), (1, 32, 32)))
        self.assertNotIn('G_BRCOND', mir)

    def test_four_incoming_values(self):
        mir = self._probe(rule_of(
            op('G_XOR', 32, phi(32, 0, V(1), V(1), V(1), V(1)), V(2)),
            op('G_XOR', 32, V(1), V(2)), (2, 32, 32)))
        self.assertEqual(mir.count('G_BRCOND'), 3)
        self.assertIn('bb.4:', mir)

    def test_root_and_float(self):
        self._probe(rule_of(phi(32, 0, V(1), V(1)), V(1), (1, 32)))
        self._probe(rule_of(
            op('G_FNEG', 32, op('G_FNEG', 32, phi(32, 0, V(1), V(1)))),
            V(1), (1, 32)))


if __name__ == '__main__':
    unittest.main()
