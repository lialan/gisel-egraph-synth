"""Rules with several outputs (girs/region.py): the root of a tree and the
values below it that have other users are replaced together. The search
builds the replacements, the proof has every output in one query."""

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from girs import corpus, discover, emit, ir, region, smt, synth  # noqa


def V(i):
    return ('var', i)


def inst(expr, vw, uses, facts=None):
    n = len(vw)
    return corpus.Instance(expr, vw, facts or [(0, 0)] * n, [None] * n,
                           uses, [], [('test', 'f', '%0')])


ADD_CMP = ('G_ICMP:ult', 1, ('G_ADD', 32, V(0), V(1)), V(0))
SUB_CMP = ('G_ICMP:ugt', 1, ('G_SUB', 64, V(0), V(1)), V(0))


def run(cases, grammar='registry'):
    """The synthesizer after the single-root search and the region step of
    ``cases`` ((expression, widths, users of each value below the root))."""
    backend = smt.Z3Backend()
    lim = discover.Limits(grammar=grammar)
    ctx = discover.Context(lim)
    sy = synth.Synthesizer(backend, synth.SynthLimits())
    joint, insts = [], []
    for e, vw, uses in cases:
        i = inst(e, vw, uses)
        insts.append(i)
        cands, _ = discover.discover(i, backend, lim, ctx)
        tgts = [c['tgt'] for c in cands]
        for alt in region.root_alternatives(i, lim, ctx):
            if alt not in tgts and discover.prove_concrete(
                    i, alt, backend).status == 'unsat':
                tgts.append(alt)
        for t in tgts:
            rid = sy.add(i, t)
            if rid and region.interior_outputs(i):
                joint.append((i, t, rid))
    sy.finalize(insts)
    stats = region.extend(sy, joint, backend, lim, ctx)
    return sy, stats


def region_rules(sy):
    return [synth.strip_private(r) for r in sy.rules.values()
            if r.get('region')]


class OutputsTest(unittest.TestCase):
    def test_a_value_with_another_user_is_an_output(self):
        i = inst(ADD_CMP, (32, 32), (2,))
        self.assertEqual(region.interior_outputs(i), [ADD_CMP[2]])
        # One user: the rule of the root alone removes the value.
        self.assertEqual(region.interior_outputs(
            inst(ADD_CMP, (32, 32), (1,))), [])

    def test_a_value_that_occurs_twice_is_not_an_output(self):
        a = ('G_ADD', 32, V(0), V(1))
        e = ('G_XOR', 32, ('G_SHL', 32, a, V(2)), ('G_LSHR', 32, a, V(2)))
        i = inst(e, (32, 32, 32), (1, 2, 1, 2))
        self.assertEqual(region.interior_outputs(i), [])

    def test_a_result_of_an_instruction_with_several_results(self):
        # The old instruction of an output is erased, so it has one
        # result.
        e = ('G_ZEXT', 32, ('G_UADDO#1', 1, V(0), V(1)))
        self.assertEqual(region.interior_outputs(
            inst(e, (8, 8), (2,))), [])

    def test_corpus_keeps_the_most_users(self):
        import json
        import tempfile

        def rec(uses):
            return {'fn': 'f', 'bb': 0, 'root': '%3', 'interior': 2,
                    'expr': {'op': 'G_ICMP', 'pred': 'ult', 'w': 1,
                             'reg': '%3', 'zero': '0x0', 'one': '0x0',
                             'uses': 1, 'flags': [], 'args': [
                                 {'op': 'G_ADD', 'w': 32, 'reg': '%2',
                                  'zero': '0x0', 'one': '0x0', 'uses': uses,
                                  'flags': [],
                                  'args': [{'in': 0}, {'in': 1}]},
                                 {'in': 0}]},
                    'inputs': [{'reg': '%0', 'w': 32, 'zero': '0x0',
                                'one': '0x0', 'def': 'COPY'},
                               {'reg': '%1', 'w': 32, 'zero': '0x0',
                                'one': '0x0', 'def': 'COPY'}]}
        with tempfile.NamedTemporaryFile('w', suffix='.jsonl') as f:
            for u in (1, 3, 2):
                f.write(json.dumps(rec(u)) + '\n')
            f.flush()
            insts, _ = corpus.load([f.name])
        self.assertEqual(len(insts), 1)
        self.assertEqual(insts[0].interior_uses, (3,))
        self.assertEqual(len(region.interior_outputs(insts[0])), 1)


class CostTest(unittest.TestCase):
    def test_results_of_one_instruction_count_once(self):
        c = ('G_UADDO#1', 1, V(0), V(1))
        s = ('G_UADDO', 32, V(0), V(1))
        self.assertEqual(region.joint_cost([c, s]), 1)
        self.assertEqual(region.joint_cost([c, ('G_ADD', 32, V(0), V(1))]),
                         2)
        # Two widths of one operator are two instructions.
        self.assertEqual(region.joint_cost([('G_ZEXT', 32, V(0)),
                                            ('G_ZEXT', 64, V(0))]), 2)

    def test_reads(self):
        c = ('G_UADDO#1', 1, V(0), V(1))
        s = ('G_UADDO', 32, V(0), V(1))
        self.assertEqual(region.joint_reads([c, s]), {0: 1, 1: 1})
        # Two instructions read x0: a proof with one value of x0 does not
        # hold for an undef x0.
        self.assertEqual(region.joint_reads(
            [c, ('G_ADD', 32, V(0), V(1))])[0], 2)


class SearchTest(unittest.TestCase):
    def test_add_and_carry(self):
        sy, stats = run([(ADD_CMP, (32, 32), (2,))])
        rules = region_rules(sy)
        self.assertEqual(len(rules), 1)
        r = rules[0]
        outs = r['region']['outputs']
        self.assertEqual([o['node'] for o in outs], [0, 1])
        self.assertEqual(outs[0]['replacement'], '(G_UADDO#1:s1 x0 x1)')
        self.assertEqual(outs[1]['replacement'], '(G_UADDO:s32 x0 x1)')
        self.assertEqual(r['cost'], {'source': 2, 'replacement': 1,
                                     'root_alone': 2})
        # Each width map of the rule has a joint proof.
        self.assertTrue(all(p['outputs'] == 2 and p['result'] == 'unsat'
                            for d in r['disjuncts'] for p in d['proofs']))
        self.assertIn([[1, 1], [32, 64]],
                      [m for d in r['disjuncts'] for m in d['width_maps']])
        self.assertEqual(stats['rules'], 1)

    def test_no_rule_without_another_user(self):
        sy, stats = run([(ADD_CMP, (32, 32), (1,))])
        self.assertEqual(region_rules(sy), [])
        self.assertEqual(stats['instances'], 0)

    def test_no_rule_without_the_operator(self):
        # The base grammar has no instruction with two results.
        sy, _ = run([(ADD_CMP, (32, 32), (2,))], grammar='base')
        self.assertEqual(region_rules(sy), [])

    def test_subtract_and_borrow_needs_another_root(self):
        # The single-root search gives a comparison for the root. The
        # borrow of G_USUBO has the same samples; the region step finds it
        # because the difference is the other result.
        i = inst(SUB_CMP, (64, 64), (2,))
        lim = discover.Limits(grammar='registry')
        ctx = discover.Context(lim)
        cands, _ = discover.discover(i, smt.Z3Backend(), lim, ctx)
        self.assertNotIn(('G_USUBO#1', 1, V(0), V(1)),
                         [c['tgt'] for c in cands])
        self.assertEqual(region.root_alternatives(i, lim, ctx),
                         [('G_USUBO#1', 1, V(0), V(1))])
        sy, _ = run([(SUB_CMP, (64, 64), (2,))])
        rules = region_rules(sy)
        self.assertEqual(len(rules), 1)
        self.assertEqual(rules[0]['replacement'],
                         '(G_USUBO#1:s1 x0 x1); $t0 = (G_USUBO:s64 x0 x1)')

    def test_no_alternative_without_a_shared_value(self):
        # No value below the root has another user.
        i = inst(SUB_CMP, (64, 64), (1,))
        lim = discover.Limits(grammar='registry')
        self.assertEqual(region.root_alternatives(
            i, lim, discover.Context(lim)), [])


class ProofTest(unittest.TestCase):
    def rule(self):
        sy, _ = run([(ADD_CMP, (32, 32), (2,))])
        return region_rules(sy)[0]

    def test_joint_proof(self):
        r = self.rule()
        maps = r['disjuncts'][0]['width_maps']
        st, proofs = region.verify(region.schedules(r, maps), [()],
                                   smt.Z3Backend())
        self.assertEqual(st, 'valid')
        self.assertEqual(len(proofs), len(maps))

    def test_a_wrong_output_is_refuted(self):
        # The root is right and the second output is wrong: the query
        # with both outputs has a counterexample.
        r = self.rule()
        bad = dict(r, region={'outputs': [
            r['region']['outputs'][0],
            dict(r['region']['outputs'][1], replacement_json=ir.to_json(
                ('G_USUBO', 32, V(0), V(1))))]})
        maps = r['disjuncts'][0]['width_maps'][:1]
        st, _ = region.verify(region.schedules(bad, maps), [()],
                              smt.Z3Backend())
        self.assertEqual(st, 'invalid')

    def test_poison_of_one_output_does_not_free_the_other(self):
        # (shl x, y) is poison for a large y; the root (x & 1) is not.
        # A replacement of the root must still be right for that input.
        enc = smt.Encoder((8, 8))
        shl = ('G_SHL', 8, V(0), V(1))
        pairs = [(('G_OR', 8, shl, V(0)), ('G_OR', 8, shl, V(0))),
                 (shl, ('G_SHL', 8, V(0), V(1)))]
        import z3
        ok = smt.Z3Backend().check(smt.joint_violation(
            enc, pairs, z3.BoolVal(True)))
        self.assertEqual(ok.status, 'unsat')
        wrong = [(V(0), ('lit', 8, '0')), (shl, shl)]
        bad = smt.Z3Backend().check(smt.joint_violation(
            smt.Encoder((8, 8)), wrong, z3.BoolVal(True)))
        self.assertEqual(bad.status, 'sat')

    def test_structural_conditions(self):
        r = self.rule()
        self.assertTrue(region.structural(r))
        twice = dict(r, region={'outputs': [
            r['region']['outputs'][0],
            dict(r['region']['outputs'][1], replacement_json=ir.to_json(
                ('G_ADD', 32, V(0), V(1))))]})
        self.assertFalse(region.structural(twice))


class EmitTest(unittest.TestCase):
    def test_guard_and_apply(self):
        sy, _ = run([(ADD_CMP, (32, 32), (2,))])
        r = region_rules(sy)[0]
        self.assertIsNone(emit.why_not_emittable(r))
        self.assertIsNone(emit.one_use_variant(r))
        guard = emit._cpp_guard(r)
        # The match step finds the position and puts it in the plan.
        self.assertIn('isJointRegion(MRI, Dst, {T0}, {X0, X1}, Plan)', guard)
        apply = emit._cpp_apply(r)
        # One instruction defines the old register of the sum and the
        # root, before the old sum; then the old instructions go.
        self.assertIn('MachineInstr *Old0 = MRI.getVRegDef(T0);', apply)
        self.assertIn('B.setInstrAndDebugLoc(applyRegionPlan(Plan));', apply)
        self.assertNotIn('firstRegionOutput', apply)
        td, _, _ = emit.emit({'rules': [r]}, all_candidates=True)
        self.assertIn('(defs root:$dst, gisynth_region_plan:$plan),', td)
        self.assertIn('B.buildInstr(TargetOpcode::G_UADDO, {T0, Dst}, '
                      '{X0, X1})', apply)
        self.assertLess(apply.index('buildInstr'),
                        apply.index('Old0->eraseFromParent()'))
        self.assertEqual(apply.count('buildInstr'), 1)
        # The old instructions release their registers before the new
        # instruction defines them: no register has two definitions.
        for rel in ('releaseResults(MRI, *Old0);',
                    'releaseResults(MRI, Root);'):
            self.assertLess(apply.index('Old0 = MRI.getVRegDef(T0)'),
                            apply.index(rel))
            self.assertLess(apply.index(rel), apply.index('buildInstr'))

    def test_the_example_function_has_a_user_of_each_output(self):
        from girs import select, targets
        sy, _ = run([(ADD_CMP, (32, 32), (2,))])
        r = region_rules(sy)[0]
        # The example of the rule of the root.
        name, ex = select.examples(r)[0]
        mir = select.build_mir(r, ex, name, targets.get('AMDGPU'))
        lines = [ln.strip() for ln in mir.splitlines()]
        add = [ln for ln in lines if '= G_ADD ' in ln]
        self.assertEqual(len(add), 1)
        reg = add[0].split(':')[0]
        # The sum has the comparison and a second user.
        self.assertEqual(len([ln for ln in lines if '= G_ICMP ' in ln and
                              reg + ',' in ln]), 1)
        self.assertIn('$vgpr1 = COPY ' + reg, lines)
        self.assertIn('SI_RETURN implicit $vgpr0, implicit $vgpr1', lines)

    def test_the_region_rule_comes_before_the_rule_of_the_root(self):
        sy, _ = run([(ADD_CMP, (32, 32), (2,))])
        db = {'rules': [synth.strip_private(r) for r in sy.rules.values()]}
        ids = [r['id'] for r in emit.candidates(db)]
        reg = [i for i in ids if i.startswith('synth_region_')]
        self.assertEqual(len(reg), 1)
        self.assertEqual(ids.index(reg[0]), 0)

    def test_single_root_apply_is_unchanged(self):
        sy, _ = run([(ADD_CMP, (32, 32), (1,))])
        r = [synth.strip_private(x) for x in sy.rules.values()][0]
        apply = emit._cpp_apply(r)
        self.assertIn('B.setInstrAndDebugLoc(Root);', apply)
        self.assertIn('{MRI.getType(X0), Dst}', apply)
        self.assertNotIn('Old0', apply)


if __name__ == '__main__':
    unittest.main()
