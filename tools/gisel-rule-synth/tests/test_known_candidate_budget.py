"""Exact known edges are reusable seeds, not a quota on new discoveries."""

import copy
from pathlib import Path
import sys
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from girs import corpus, discover, known, smt, synth


def var(i=0):
    return ('var', i)


def instance(width=32, facts=None):
    return corpus.Instance(('G_AND', width, var(), var()), (width,),
                           facts or [(0, 0)], [None], [], [],
                           [('input.ll', 'fn', '%0')])


class KnownCandidateBudgetTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        inst = instance()
        sy = synth.Synthesizer(smt.Z3Backend())
        cls.rid = sy.add(inst, var())
        sy.finalize([inst])
        cls.db = known.stamp({'rules': [synth.strip_private(sy.rules[cls.rid])]})

    def context(self, db=None, **limits):
        lim = discover.Limits(**limits)
        ctx = discover.Context(lim)
        ctx.known = known.Index(self.db if db is None else db)
        return lim, ctx

    def prove(self, cands, lim, ctx, inst=None, envs=None, backend=None):
        backend = backend or smt.Z3Backend()
        stats = discover.new_stats()
        out = discover.prove_candidates(inst or instance(), cands, backend,
                                        lim, ctx, stats, envs)
        return out, stats

    def test_known_edge_leaves_room_for_a_different_rhs(self):
        lim, ctx = self.context(max_candidates=1)
        alt = ('G_OR', 32, var(), var())
        later = ('G_ADD', 32, var(), ('lit', 32, '0'))
        out, st = self.prove([var(), alt, later], lim, ctx)
        self.assertEqual([c['tgt'] for c in out], [var(), alt])
        self.assertEqual(out[0]['known'], self.rid)
        self.assertNotIn('proof', out[0])
        self.assertEqual(out[1]['proof'].status, 'unsat')
        self.assertEqual((st['known_candidates'], st['new_candidates'],
                          st['smt_checks']), (1, 1, 1))
        self.assertEqual((st['stop'], st['candidate_deferred'],
                          st['not_tried']), ('candidate_limit', 1, 1))

    def test_known_edge_does_not_discard_a_more_expensive_rhs(self):
        lim, ctx = self.context(max_candidates=1)
        inst = instance()
        alt = ('G_OR', 32, var(), var())
        envs = discover.instance_envs(inst, lim, ctx)
        out, st = self.prove([var(), alt], lim, ctx, inst, envs)
        self.assertEqual([c['tgt'] for c in out], [var(), alt])
        self.assertEqual((st['dominated'], st['smt_checks']), (0, 1))

    def test_known_tail_is_kept_after_the_new_candidate_quota(self):
        lim, ctx = self.context(max_candidates=1)
        first = ('G_OR', 32, var(), var())
        deferred = ('G_ADD', 32, var(), ('lit', 32, '0'))
        out, st = self.prove([first, deferred, var()], lim, ctx)
        self.assertEqual([c['tgt'] for c in out], [first, var()])
        self.assertEqual(out[-1]['known'], self.rid)
        self.assertEqual((st['new_candidates'], st['known_candidates'],
                          st['not_tried']), (1, 1, 1))

    def test_zero_new_budget_reuses_known_seeds_without_proofs(self):
        lim, ctx = self.context(max_candidates=0, max_proofs=0)
        backend = smt.Z3Backend()
        with mock.patch.object(backend, 'check',
                               side_effect=AssertionError('reproved known rule')):
            out, st = self.prove([var()], lim, ctx, backend=backend)
        self.assertEqual([c['known'] for c in out], [self.rid])
        self.assertEqual((st['stop'], st['new_candidates'],
                          st['smt_checks']), ('complete', 0, 0))

    def test_zero_new_budget_defers_unknown_but_keeps_known_tail(self):
        lim, ctx = self.context(max_candidates=0, max_proofs=0)
        out, st = self.prove([('G_OR', 32, var(), var()), var()], lim, ctx)
        self.assertEqual([c['known'] for c in out], [self.rid])
        self.assertEqual((st['stop'], st['smt_checks'], st['not_tried']),
                          ('candidate_limit', 0, 1))

    def test_proof_budget_still_bounds_new_work(self):
        lim, ctx = self.context(max_candidates=4, max_proofs=1)
        first = ('G_OR', 32, var(), var())
        deferred = ('G_ADD', 32, var(), ('lit', 32, '0'))
        out, st = self.prove([first, deferred, var()], lim, ctx)
        self.assertEqual([c['tgt'] for c in out], [first, var()])
        self.assertEqual((st['stop'], st['proof_deferred'], st['smt_checks']),
                          ('proof_budget', 1, 1))

    def test_exact_duplicate_edges_do_not_repeat_lookup_or_proof(self):
        lim, ctx = self.context(max_candidates=3)
        alt = ('G_OR', 32, var(), var())
        out, st = self.prove([var(), var(), alt, alt], lim, ctx)
        self.assertEqual([c['tgt'] for c in out], [var(), alt])
        self.assertEqual((st['duplicate_candidates'], st['smt_checks'],
                          st['known_candidates'], ctx.known.hits), (2, 1, 1, 1))

    def test_exact_knowledge_is_checked_before_exception_sampling(self):
        lim, ctx = self.context(max_candidates=0, max_proofs=0)
        backend = smt.Z3Backend()
        with mock.patch.object(discover, 'flags_refine_on',
                               side_effect=AssertionError('sampled known edge')), \
                mock.patch.object(backend, 'check',
                                  side_effect=AssertionError('reproved known edge')):
            out, st = discover.discover(instance(), backend, lim, ctx)
        self.assertEqual([c['known'] for c in out], [self.rid])
        self.assertEqual((st['known_prechecked'], st['new_candidates'],
                          ctx.known.hits), (1, 0, 1))

    def test_guard_miss_does_not_specialize_a_shared_bank(self):
        db = copy.deepcopy(self.db)
        for d in db['rules'][0]['disjuncts']:
            d['pred_json'] = [['def', 0]]
        lim, ctx = self.context(db, max_candidates=1)
        backend = smt.Z3Backend()
        covered, cs = discover.discover(instance(facts=[(0, 0, True)]),
                                         backend, lim, ctx)
        bank = next(iter(ctx.banks.values()))
        uncovered, us = discover.discover(instance(), backend, lim, ctx)
        self.assertEqual(covered[0]['known'], self.rid)
        self.assertNotIn('known', uncovered[0])
        self.assertEqual((cs['known_candidates'], us['new_candidates'],
                          us['smt_checks']), (1, 1, 1))
        self.assertIs(next(iter(ctx.banks.values())), bank)
        self.assertEqual(ctx.bank_hits, 1)

    def test_unproved_width_and_one_use_miss_remain_new(self):
        db = copy.deepcopy(self.db)
        for d in db['rules'][0]['disjuncts']:
            d['width_maps'] = [[[32, 32]]]
        lim, ctx = self.context(db)
        out, st = self.prove([var()], lim, ctx, instance(16))
        self.assertNotIn('known', out[0])
        self.assertEqual((st['known_candidates'], st['new_candidates']), (0, 1))

        db = copy.deepcopy(self.db)
        db['rules'][0]['needs_one_use'] = True
        lim, ctx = self.context(db)
        out, st = self.prove([var()], lim, ctx)
        self.assertNotIn('known', out[0])
        self.assertEqual((st['known_candidates'], st['smt_checks']), (0, 1))

    def test_expired_deadline_prevents_new_scan(self):
        lim, ctx = self.context()
        lim.deadline = 0
        with mock.patch.object(ctx, 'bank',
                               side_effect=AssertionError('built bank past deadline')):
            out, st = discover.discover(instance(), smt.Z3Backend(), lim, ctx)
        self.assertEqual(out, [])
        self.assertEqual((st['stop'], st['limits']), ('time_budget', ['time']))


if __name__ == '__main__':
    unittest.main()
