#!/usr/bin/env python3
"""Tests of the unified discovery pipeline: the operator registry, the
import of e-graph candidates and the rules with a computed constant.

Run:  python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests
"""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import z3  # noqa: E402

from girs import (corpus, egraph, emit, ir, match, opcheck,  # noqa: E402
                  ops, smt, synth)


def V(i):
    return ('var', i)


def L(w, k):
    return ('lit', w, k)


def exact(w, c):
    """The known bits of the constant ``c``."""
    return (~c & ir.mask(w), c)


def inst(expr, vw, facts, consts=None, const_vars=()):
    consts = consts or [None] * len(vw)
    i = corpus.Instance(expr, vw, facts, consts, [], [],
                        [('test', 'f', '%0')])
    i.const_vars = tuple(const_vars)
    return i


def refines(src, tgt, vw, const_vars=()):
    """True if ``tgt`` refines ``src`` for every input, with the variables
    ``const_vars`` matched as constants."""
    enc = smt.Encoder(vw, src[1], const_vars)
    f = smt.refinement_violation(enc, src, tgt, z3.BoolVal(True))
    return smt.Z3Backend().check(f).status == 'unsat'


class OpsTest(unittest.TestCase):
    def test_evaluator_agrees_with_smt(self):
        n, bad = opcheck.check_models(samples=8)
        self.assertGreater(n, 5000)
        self.assertEqual(bad, [])

    def test_capability_matrix_is_complete(self):
        rows = ops.capability_matrix()
        self.assertGreater(len(rows), 80)
        for r in rows:
            info = ops.REGISTRY[r['name']]
            for st in ops.STAGES:
                # 'yes', the discovery engines, or the reason.
                self.assertTrue(r[st], (r['name'], st))
            # A stage that is supported has its implementation.
            if r['eval'] == 'yes':
                self.assertIsNotNone(info.eval, r['name'])
            if r['smt'] == 'yes':
                self.assertIsNotNone(info.smt, r['name'])
            if r['typecheck'] == 'yes':
                self.assertIsNotNone(info.typecheck, r['name'])
            # An operator without a model is not a discovery or emission
            # candidate.
            if r['smt'] != 'yes':
                self.assertNotIn(r['discovery'],
                                 ('enumerative-source+egraph',
                                  'enumerative+egraph'), r['name'])
                self.assertNotEqual(r['emit'], 'yes', r['name'])

    def test_enumerated_operators_keep_their_models(self):
        for name in ops.ENUMERATED:
            row = [r for r in ops.capability_matrix()
                   if r['name'] == name][0]
            self.assertEqual([row[st] for st in ops.STAGES],
                             ['yes', 'yes', 'yes', 'yes',
                              'enumerative+egraph', 'yes'])

    def test_target_provider_is_opt_in(self):
        class TestOps(ops.Provider):
            namespace = 'TEST'

            def operators(self):
                info = ops.OpInfo('G_TEST_ANDN', 'binary', 2,
                                  namespace='TEST')
                info.typecheck = lambda w, ws, at, r: ws == [w, w]
                info.eval = lambda w, ws, at, r, v: v[0] & ~v[1] & \
                    ops.mask(w)
                info.smt = lambda w, ws, at, r, x: (x[0] & ~x[1], None,
                                                    None)
                return [info]

        self.assertFalse(ops.known('G_TEST_ANDN'))
        TestOps().install()
        try:
            ops.parse.cache_clear()
            self.assertEqual([r['name']
                              for r in ops.capability_matrix('TEST')],
                             ['G_TEST_ANDN'])
            self.assertNotIn('G_TEST_ANDN',
                             [r['name'] for r in ops.capability_matrix()])
            andn = ('G_TEST_ANDN', 32, V(0), V(1))
            self.assertTrue(ir.well_typed(andn, (32, 32)))
            self.assertEqual(ir.evaluate(andn, (32, 32), [0xff, 0x0f]),
                             0xf0)
            # The core proves a rule with the operator of the provider.
            src = ('G_AND', 32, V(0), ('G_XOR', 32, V(1), L(32, '-1')))
            self.assertTrue(refines(src, andn, (32, 32)))
            self.assertFalse(refines(src, ('G_TEST_ANDN', 32, V(1), V(0)),
                                     (32, 32)))
        finally:
            del ops.REGISTRY['G_TEST_ANDN']
            ops.parse.cache_clear()


class EGraphImportTest(unittest.TestCase):
    def setUp(self):
        self.backend = smt.Z3Backend()
        self.imp = egraph.Importer(self.backend)
        self.imp.add_file(os.path.join(HERE, 'data', 'egraph-umin.jsonl'))

    def test_candidates(self):
        cands = self.imp.candidates()
        got = {(ir.to_sexpr(c.inst.expr), ir.to_sexpr(c.tgt))
               for c in cands}
        # The local steps of the region, each with the smallest source
        # that is still proved. The e-graph gives the operands of a
        # commutative operator in its own order.
        self.assertEqual(got, {
            ('(G_SELECT:s32 (G_ICMP:ugt:s1 x0 x1) x1 x0)',
             '(G_UMIN:s32 x1 x0)'),
            ('(G_AND:s32 (G_AND:s32 x0 x1) x2)', '(G_AND:s32 x2 x1)'),
            ('(G_SUB:s32 x0 x0)', '0:s32'),
            ('(G_ADD:s32 x0 x1)', 'x0')})
        for c in cands:
            self.assertIn('umin-from-select-ult', c.rules)
            self.assertTrue(ir.well_typed(c.inst.expr, c.inst.vw))
            self.assertTrue(ir.well_typed(c.tgt, c.inst.vw))
        self.assertEqual(self.imp.stats['records'], 1)
        # Every local step is a candidate. The complete rewrite of the
        # root is a tree of 10 operations: too large for one rule.
        self.assertEqual(self.imp.stats['rejected'],
                         {'root': {'source larger than 8 operations': 1}})

    def test_candidates_are_deterministic(self):
        again = egraph.Importer(self.backend)
        again.add_file(os.path.join(HERE, 'data', 'egraph-umin.jsonl'))
        self.assertEqual([c.key() for c in self.imp.candidates()],
                         [c.key() for c in again.candidates()])

    def test_candidates_go_through_the_proofs(self):
        sy = synth.Synthesizer(self.backend)
        ids = {}
        for c in self.imp.candidates():
            rid = sy.add(c.inst, c.tgt, provenance={'discovery': 'egraph'})
            self.assertIsNotNone(rid)
            ids[ir.to_sexpr(c.tgt)] = rid
        r = sy.rules[ids['(G_UMIN:s32 x1 x0)']]
        self.assertEqual(r['semantic_status']['kind'], 'verified_refinement')
        self.assertEqual(r['class'], 'reduces_cost')
        self.assertEqual(synth.precondition_text(r), 'true')
        self.assertTrue(emit.emittable(r))
        # The mask rule needs its known-bits condition: the e-graph only
        # proved it for the constants of the region.
        r = sy.rules[ids['(G_AND:s32 x2 x1)']]
        self.assertNotEqual(synth.precondition_text(r), 'true')

    def test_wrong_candidate_is_rejected(self):
        # A candidate is a proposal: a wrong one gives no rule.
        c = self.imp.candidates()[0]
        sy = synth.Synthesizer(self.backend)
        i = inst(('G_SELECT', 32, ('G_ICMP:ult', 1, V(0), V(1)), V(0),
                  V(1)), (32, 32), [(0, 0), (0, 0)])
        self.assertIsNone(sy.add(i, ('G_UMAX', 32, V(0), V(1))))
        self.assertIsNotNone(c)

    def test_version_is_checked(self):
        with self.assertRaises(ValueError):
            self.imp.add_record({'version': 99})


class ComputedConstantTest(unittest.TestCase):
    XOR_SRC = ('G_XOR', 32, ('G_AND', 32, V(0), V(1)),
               ('G_AND', 32, V(0), V(2)))

    def test_recipes(self):
        vw = [32, 32, 32]
        rs = egraph.recipes(16 ^ 18, 32, {1: 16, 2: 18}, vw, {'G_XOR'})
        self.assertEqual(rs[0], ('G_XOR', 32, V(1), V(2)))
        self.assertLessEqual(len(rs), egraph.MAX_RECIPES)
        for r in rs:
            self.assertEqual(ir.evaluate(r, vw, [0, 16, 18]), 16 ^ 18)
        self.assertEqual(egraph.recipes(12345, 32, {1: 16, 2: 18}, vw), [])
        # The mask of a narrower type of the source.
        self.assertEqual(egraph.recipes(0xffff, 32, {}, [32], (),
                                        {16, 32}),
                         [('G_ZEXT', 32, L(16, '-1'))])

    def test_proof_holds_for_every_constant(self):
        good = ('G_AND', 32, V(0), ('G_XOR', 32, V(1), V(2)))
        bad = ('G_AND', 32, V(0), ('G_SUB', 32, V(2), V(1)))
        self.assertTrue(refines(self.XOR_SRC, good, (32, 32, 32), (1, 2)))
        # 18 - 16 is 16 ^ 18, but not for every pair of constants.
        self.assertEqual(18 - 16, 16 ^ 18)
        self.assertFalse(refines(self.XOR_SRC, bad, (32, 32, 32), (1, 2)))

    def test_shift_amount_guard(self):
        src = ('G_SHL', 32, ('G_SHL', 32, V(0), V(1)), V(2))
        tgt = ('G_SHL', 32, V(0), ('G_ADD', 32, V(1), V(2)))
        # (x << 20) << 20 is 0, but x << 40 is poison: the rule is only
        # correct with the guard on the computed amount.
        self.assertEqual(ir.computed_amounts(tgt, (1, 2)),
                         [(32, ('G_ADD', 32, V(1), V(2)))])
        self.assertTrue(refines(src, tgt, (32, 32, 32), (1, 2)))
        enc = smt.Encoder((32, 32, 32), 32, (1, 2))
        sv, sp, su = enc.enc_full(src)
        tv, tp, tu = enc.enc_full(tgt)
        no_guard = z3.And(enc.well_formed(), z3.Not(su), z3.Not(sp),
                          z3.Or(tp, sv != tv))
        self.assertEqual(smt.Z3Backend().check(no_guard).status, 'sat')

    def _rule(self, i, tgt):
        sy = synth.Synthesizer(smt.Z3Backend())
        rid = sy.add(i, tgt, provenance={'discovery': 'egraph'})
        self.assertIsNotNone(rid)
        sy.finalize([i])
        return sy.rules[rid]

    def test_rule_and_emission(self):
        i = inst(self.XOR_SRC, (32, 32, 32),
                 [(0, 0), exact(32, 16), exact(32, 18)], [None, 16, 18],
                 (1, 2))
        r = self._rule(i, ('G_AND', 32, V(0), ('G_XOR', 32, V(1), V(2))))
        self.assertEqual(r['semantic_status']['kind'], 'verified_refinement')
        self.assertEqual(synth.precondition_text(r), 'true')
        self.assertEqual(len(r['const_vars']), 2)
        # The computed constant costs nothing: 3 operations become 1.
        self.assertEqual(r['cost'], {'source': 3, 'replacement': 1})
        self.assertEqual(r['class'], 'reduces_cost')
        self.assertIsNone(emit.why_not_emittable(r))
        guard = emit._cpp_guard(r)
        for v in r['const_vars']:
            self.assertIn('OptC%d = getIConstantVRegVal(X%d, MRI);' % (v, v),
                          guard)
        cv = r['const_vars']
        self.assertIn('B.buildConstant(MRI.getType(Dst), (C%d ^ C%d))' %
                      tuple(cv), emit._cpp_apply(r))
        # The matcher needs constants for the constant variables.
        m = match.RuleMatcher(r)
        self.assertTrue(m.check(i))
        self.assertFalse(m.check(inst(self.XOR_SRC, (32, 32, 32),
                                       [(0, 0)] * 3)))

    def test_constant_rule_does_not_dominate_the_general_rule(self):
        # The rule for constants has the cheaper replacement, but it does
        # not apply where the general rule does.
        sy = synth.Synthesizer(smt.Z3Backend())
        gen = inst(self.XOR_SRC, (32, 32, 32), [(0, 0)] * 3)
        cst = inst(self.XOR_SRC, (32, 32, 32),
                   [(0, 0), exact(32, 16), exact(32, 18)], [None, 16, 18],
                   (1, 2))
        tgt = ('G_AND', 32, V(0), ('G_XOR', 32, V(1), V(2)))
        a = sy.add(gen, tgt)
        b = sy.add(cst, tgt, provenance={'discovery': 'egraph'})
        self.assertNotEqual(a, b)
        sy.finalize([gen, cst])
        self.assertEqual(sy.rules[a]['cost']['replacement'], 2)
        self.assertEqual(sy.rules[b]['cost']['replacement'], 1)
        self.assertNotIn('dominated_by', sy.rules[a])
        self.assertNotIn('dominated_by', sy.rules[b])

    def test_shift_rule_emits_the_guard(self):
        src = ('G_SHL', 32, ('G_SHL', 32, V(0), V(1)), V(2))
        i = inst(src, (32, 32, 32), [(0, 0), exact(32, 3), exact(32, 2)],
                 [None, 3, 2], (1, 2))
        r = self._rule(i, ('G_SHL', 32, V(0), ('G_ADD', 32, V(1), V(2))))
        self.assertEqual(synth.precondition_text(r), 'true')
        a, b = r['const_vars']
        self.assertIn('if (!(C%d + C%d).ult(MRI.getType(Dst).'
                      'getScalarSizeInBits()))' % (a, b),
                      emit._cpp_guard(r))

    def test_low_mask_rule(self):
        i = inst(('G_ZEXT', 32, ('G_TRUNC', 16, V(0))), (32,), [(0, 0)])
        r = self._rule(i, ('G_AND', 32, V(0), ('G_ZEXT', 32, L(16, '-1'))))
        self.assertEqual(synth.precondition_text(r), 'true')
        self.assertNotIn('const_vars', r)
        self.assertIsNone(emit.why_not_emittable(r))
        self.assertIn('APInt::getAllOnes(MRI.getType(T0).'
                      'getScalarSizeInBits()).zext(MRI.getType(Dst).'
                      'getScalarSizeInBits())', emit._cpp_apply(r))
        # Other widths of the same class are proved with the same rule.
        widths = {tuple(w for _, w in m) for d in r['disjuncts']
                  for m in d['width_maps']}
        self.assertGreater(len(widths), 1)


if __name__ == '__main__':
    unittest.main()
