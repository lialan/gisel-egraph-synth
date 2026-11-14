"""Whole-vector knowledge must not consume the quota for new proposals."""

import copy
from pathlib import Path
import sys
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from girs import corpus, discover, ir, known, ops, smt, synth, targets, vector_search


def instance(width=32, facts=None, uses=1):
    src = ('G_BUILD_VECTOR', ops.vec(4, width)) + tuple(
        ('G_EXTRACT_VECTOR_ELT:%d' % j, width, ('var', 0)) for j in range(4))
    return corpus.Instance(src, (ops.vec(8, width),), facts or [(0, 0)],
                           [None], [uses] * len(ir.interior_nodes(src)), [],
                           [('input.ll', 'fn', '%0')])


def extract(width=32):
    return ('G_EXTRACT_SUBVECTOR:0', ops.vec(4, width), ('var', 0))


def shuffle(width=32):
    return ('G_SHUFFLE_VECTOR:0.1.2.3', ops.vec(4, width),
            ('var', 0), ('var', 0))


class VectorKnownCandidateBudgetTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        inst = instance()
        sy = synth.Synthesizer(smt.Z3Backend())
        cls.extract_id = sy.add(inst, extract())
        cls.shuffle_id = sy.add(inst, shuffle())
        if cls.extract_id is None or cls.shuffle_id is None:
            raise AssertionError('vector fixture did not prove')
        sy.finalize([inst])
        cls.both = known.stamp({'rules': [
            synth.strip_private(sy.rules[r])
            for r in (cls.extract_id, cls.shuffle_id)]})

    def catalog(self, ids=None):
        ids = {self.extract_id} if ids is None else set(ids)
        db = copy.deepcopy(self.both)
        db['rules'] = [r for r in db['rules'] if r['id'] in ids]
        return db

    def setup_search(self, db=None, **kw):
        dlim = discover.Limits(**kw)
        ctx = discover.Context(dlim)
        ctx.known = known.Index(self.catalog() if db is None else db)
        return dlim, vector_search.Limits.of(dlim), ctx

    def search(self, dlim, vlim, ctx, inst=None):
        return vector_search.search(inst or instance(), smt.Z3Backend(),
                                    vlim, dlim, ctx)

    def test_known_whole_vector_leaves_a_slot_for_another_rhs(self):
        dlim, vlim, ctx = self.setup_search(max_candidates=1)
        out, st = self.search(dlim, vlim, ctx)
        self.assertEqual([c['tgt'] for c in out], [extract(), shuffle()])
        self.assertEqual(out[0]['known'], self.extract_id)
        self.assertNotIn('known', out[1])
        self.assertNotIn('proof', out[0])
        self.assertEqual((st['known_candidates'], st['vector_new_candidates'],
                          st['smt_checks'], ctx.known.hits), (1, 1, 0, 1))
        self.assertEqual((st['stop'], st['limits']), ('complete', []))

    def test_known_tail_survives_a_full_new_quota(self):
        dlim, vlim, ctx = self.setup_search(self.catalog([self.shuffle_id]),
                                           max_candidates=1)
        out, st = self.search(dlim, vlim, ctx)
        self.assertEqual([c['tgt'] for c in out], [extract(), shuffle()])
        self.assertNotIn('known', out[0])
        self.assertEqual(out[1]['known'], self.shuffle_id)
        self.assertEqual(st['stop'], 'complete')

    def test_zero_quota_keeps_both_known_seeds_without_proof(self):
        dlim, vlim, ctx = self.setup_search(self.both, max_candidates=0,
                                           max_proofs=0)
        backend = smt.Z3Backend()
        with mock.patch.object(backend, 'check',
                               side_effect=AssertionError('reproved vector rule')):
            out, st = vector_search.search(instance(), backend, vlim, dlim, ctx)
        self.assertEqual({c['known'] for c in out},
                         {self.extract_id, self.shuffle_id})
        self.assertEqual((st['stop'], st['known_candidates'], st['not_tried']),
                          ('complete', 2, 0))

    def test_zero_quota_defers_new_but_preserves_known(self):
        dlim, vlim, ctx = self.setup_search(max_candidates=0)
        out, st = self.search(dlim, vlim, ctx)
        self.assertEqual([c['known'] for c in out], [self.extract_id])
        self.assertEqual((st['stop'], st['limits'], st['candidate_deferred']),
                          ('candidate_limit', ['candidates'], 1))
        self.assertEqual((st['fingerprint_matches'], st['not_tried']), (2, 1))

    def test_guard_and_one_use_misses_still_consume_a_new_slot(self):
        for change, inst in (
                ('guard', instance()), ('one_use', instance(uses=2))):
            with self.subTest(change=change):
                db = self.catalog()
                if change == 'guard':
                    for d in db['rules'][0]['disjuncts']:
                        d['pred_json'] = [['def', 0]]
                else:
                    db['rules'][0]['needs_one_use'] = True
                dlim, vlim, ctx = self.setup_search(db, max_candidates=1)
                out, st = self.search(dlim, vlim, ctx, inst)
                self.assertEqual([c['tgt'] for c in out], [extract()])
                self.assertNotIn('known', out[0])
                self.assertEqual((st['known_candidates'], st['not_tried']), (0, 1))
                self.assertEqual(st['limits'], ['candidates'])

    def test_unproved_vector_width_is_not_a_known_edge(self):
        db = self.catalog()
        for d in db['rules'][0]['disjuncts']:
            d['width_maps'] = [[[32, 32], [ops.vec(4, 32), ops.vec(4, 32)],
                               [ops.vec(8, 32), ops.vec(8, 32)]]]
        dlim, vlim, ctx = self.setup_search(db, max_candidates=1)
        out, st = self.search(dlim, vlim, ctx, instance(16))
        self.assertEqual([c['tgt'] for c in out], [extract(16)])
        self.assertNotIn('known', out[0])
        self.assertEqual(st['known_candidates'], 0)

    def test_current_postlegalizer_legality_still_filters_known_edges(self):
        cap = targets.Capability({
            'target': 'amdgcn-amd-amdhsa', 'operators': {},
            'type_operands': {'G_EXTRACT_SUBVECTOR': [0, 1],
                              'G_SHUFFLE_VECTOR': [0, 1]},
            'typed': {
                'G_EXTRACT_SUBVECTOR': {'<4 x s32>,<8 x s32>': 'Custom'},
                'G_SHUFFLE_VECTOR': {'<4 x s32>,<8 x s32>': 'Legal'}}}, 'cap')
        dlim, vlim, ctx = self.setup_search(max_candidates=1, capability=cap,
                                           legalizer_stage='post-legalizer')
        self.assertEqual(vlim.stage, 'post-legalizer')
        out, st = self.search(dlim, vlim, ctx)
        self.assertEqual([c['tgt'] for c in out], [shuffle()])
        self.assertEqual((st['known_candidates'], ctx.known.hits,
                          st['vector_not_legalizable']), (0, 0, 1))
        self.assertEqual(st['stop'], 'complete')

    def test_expired_deadline_prevents_vector_generation(self):
        dlim, _, ctx = self.setup_search()
        dlim.deadline = 0
        vlim = vector_search.Limits.of(dlim)
        self.assertNotIn('deadline', vlim.identity())
        with mock.patch.object(vector_search, 'revectorize',
                               side_effect=AssertionError('generated after deadline')):
            out, st = self.search(dlim, vlim, ctx)
        self.assertEqual(out, [])
        self.assertEqual((st['stop'], st['limits']), ('time_budget', ['time']))

    def test_known_scan_also_obeys_the_deadline(self):
        dlim, _, ctx = self.setup_search(max_candidates=0)
        dlim.deadline = 10
        vlim = vector_search.Limits.of(dlim)
        now = [0]
        original = ctx.known.covers

        def lookup(*args, **kwargs):
            result = original(*args, **kwargs)
            now[0] = 20
            return result

        with mock.patch.object(vector_search.time, 'monotonic',
                               side_effect=lambda: now[0]), \
                mock.patch.object(ctx.known, 'covers', side_effect=lookup):
            out, st = self.search(dlim, vlim, ctx)
        self.assertEqual([c['known'] for c in out], [self.extract_id])
        self.assertEqual((st['stop'], st['limits']), ('time_budget', ['time']))
        self.assertGreater(st['vector_unscanned_proposals'], 0)

    def test_scalar_template_proof_budget_is_not_lost(self):
        v2 = ops.vec(2, 32)
        sh = ('G_SHUFFLE_VECTOR:1.0', v2, ('var', 0), ('var', 1))
        src = ('G_SUB', v2, sh, sh)
        inst = corpus.Instance(src, (v2, v2), [(0, 0)] * 2, [None] * 2,
                               [1] * len(ir.interior_nodes(src)), [],
                               [('input.ll', 'fn', '%0')])
        dlim, vlim, ctx = self.setup_search(max_proofs=0)
        _, st = self.search(dlim, vlim, ctx, inst)
        self.assertEqual(st['smt_checks'], 0)
        self.assertIn('proofs', st['limits'])
        self.assertEqual(st['stop'], 'proof_budget')

    def test_known_scalar_template_is_only_a_vector_proposal(self):
        scalar = corpus.Instance(('G_SUB', 32, ('var', 0), ('var', 0)),
                                 (32,), [(0, 0)], [None], [], [],
                                 [('scalar.ll', 'fn', '%0')])
        sy = synth.Synthesizer(smt.Z3Backend())
        rid = sy.add(scalar, ('lit', 32, '0'))
        sy.finalize([scalar])
        db = known.stamp({'rules': [synth.strip_private(sy.rules[rid])]})

        v2 = ops.vec(2, 32)
        sh = ('G_SHUFFLE_VECTOR:1.0', v2, ('var', 0), ('var', 1))
        src = ('G_SUB', v2, sh, sh)
        inst = corpus.Instance(src, (v2, v2), [(0, 0)] * 2, [None] * 2,
                               [1] * len(ir.interior_nodes(src)), [],
                               [('input.ll', 'fn', '%0')])
        dlim, vlim, ctx = self.setup_search(db, max_candidates=1, max_proofs=0)
        backend = smt.Z3Backend()
        with mock.patch.object(backend, 'check',
                               side_effect=AssertionError('reproved scalar template')):
            out, st = vector_search.search(inst, backend, vlim, dlim, ctx)
        zero = next(c for c in out if c['tgt'] == ('lit', v2, '0'))
        # The old theorem is scalar. The new whole-vector proposal must
        # still go through the vector synthesizer before becoming a rule.
        self.assertNotIn('known', zero)
        self.assertNotIn('proof', zero)
        self.assertEqual(st['vector_template_known_candidates'], 1)
        self.assertEqual((st['known_candidates'], st['smt_checks']), (0, 0))
        self.assertIsNone(dlim.deadline)


if __name__ == '__main__':
    unittest.main()
