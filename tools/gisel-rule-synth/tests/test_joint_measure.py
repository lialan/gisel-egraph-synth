"""The attribution of eval/joint_measure.py, on a model of a compiler: the
instructions of each file for a set of enabled rules. The model has the
cases that a per-file total hides: two implementations of one window (the
first enabled one takes the instance), a rule that takes the instance of
another rule, a rule that makes a file worse and a rule with no instance."""

import os
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'eval'))

import joint_measure as jm  # noqa: E402
from girs import joint_measure as shared, measure  # noqa: E402

BASE = {'f1': 100, 'f2': 50, 'f3': 10}


def model(path, enabled):
    saved, passed = 0, {}
    if path == 'f1':
        # A1 and A2: two implementations of one window; A1 comes first.
        if 'A1' in enabled:
            saved, passed = 2, {'A1': 1}
        elif 'A2' in enabled:
            saved, passed = 3, {'A2': 1}
    elif path == 'f2':
        # A2 also replaces the instructions that B would replace.
        if 'A2' in enabled:
            saved, passed = 2, {'A2': 1}
        elif 'B' in enabled:
            saved, passed = 1, {'B': 1}
    elif path == 'f3' and 'C' in enabled:
        saved, passed = -1, {'C': 1}
    n = BASE[path] - saved
    return {'rc': 0, 'insns': n, 'code_bytes': 4 * n, 'sgpr': 0, 'vgpr': 0,
            'spills': 0, 'scratch': 0, 'passed': passed, 'fallback': []}


class Model:
    def many(self, jobs):
        return [model(p, set(en)) for p, en, screen, count in jobs]


def rule(rid, window, before=3, after=3):
    return {'id': rid, 'window': window,
            'candidate': {'estimated_cost': {'before': before,
                                             'after': after},
                          'text': rid},
            'semantic_status': {'kind': 'verified_refinement'},
            'plan': {'original_only': after >= before}}


class AttributionTest(unittest.TestCase):

    def setUp(self):
        self.rules = [rule('A1', 'wA'), rule('A2', 'wA', after=2),
                      rule('B', 'wB'), rule('C', 'wC'), rule('D', 'wD')]
        self.cids = [r['id'] for r in self.rules]
        # The files where each rule screened (it would match there).
        self.screened = {'A1': ['f1'], 'A2': ['f1', 'f2'], 'B': ['f2'],
                         'C': ['f3']}
        self.base = {p: model(p, set()) for p in BASE}
        solo = {rid: {p: model(p, {rid}) for p in fs}
                for rid, fs in self.screened.items()}
        self.info = jm.solo_info(self.rules, self.screened, solo, self.base)

    def test_solo_status(self):
        st = {r: self.info[r]['profitability_status'] for r in self.cids}
        self.assertEqual(st, {'A1': 'profitable', 'A2': 'profitable',
                              'B': 'profitable', 'C': 'regression',
                              'D': 'never_matched'})
        self.assertEqual(self.info['A2']['solo']['insns_saved'], 5)
        self.assertEqual(self.info['C']['solo']['worse_files'],
                         [('f3', 'regression')])

    def test_window_and_set(self):
        best, report = jm.per_window(self.cids, self.info)
        # A2 beats A1 in their window although A1 shadows it when both
        # are enabled; both were measured on their own.
        self.assertEqual(best, ['A2', 'B'])
        self.assertEqual(self.info['A1']['selection'], 'dominated_in_window')
        self.assertEqual(report['wA']['candidates'], ['A2', 'A1'])
        S = jm.greedy(Model(), self.base, [], best, self.screened,
                      self.info, lambda ids: [])
        self.assertEqual(S, ['A2'])
        # B alone saves one instruction, nothing next to A2.
        self.assertEqual(self.info['B']['selection'], 'no_gain_in_set')
        self.assertEqual(self.info['B']['in_set']['insns_saved'], 0)
        self.assertIn('overlaps', self.info['B']['interaction'])

    def test_a_cycle_keeps_a_rule_out(self):
        best, _ = jm.per_window(self.cids, self.info)
        S = jm.greedy(Model(), self.base, [], best, self.screened, self.info,
                      lambda ids: [ids] if 'A2' in ids else [])
        self.assertEqual(S, ['B'])
        self.assertEqual(self.info['A2']['selection'], 'cycle')

    def test_candidate_enabled_by_baseline_is_measured(self):
        class BaselineModel:
            def many(self, jobs):
                out = []
                for path, enabled, screen, count in jobs:
                    applied = not screen and 'joint_candidate' in enabled
                    res = {'rc': 0, 'insns': 10 - applied,
                           'fallback': [], 'passed': {}, 'matched': {}}
                    if screen == ('joint_base',):
                        res['matched'] = {'joint_candidate': 1}
                    elif applied:
                        res['passed'] = {'joint_candidate': 1}
                    out.append(res)
                return out
        rules = [rule('joint_candidate', 'w')]
        info, screened, report = shared.measure_candidates(
            BaselineModel(), ['f'], rules, ['joint_base'],
            {'f': {'rc': 0, 'insns': 10, 'fallback': []}})
        self.assertEqual(screened, {'joint_candidate': ['f']})
        self.assertEqual(info['joint_candidate']['profitability_status'], 'profitable')
        self.assertEqual(report['baseline_only'], {'f': ['joint_candidate']})

    def test_screen_failure_falls_back_to_solo_and_rejects_compile_failure(self):
        class FailingModel:
            def many(self, jobs):
                return [{'rc': 1, 'matched': {}, 'passed': {}} for _ in jobs]
        info, screened, report = shared.measure_candidates(
            FailingModel(), ['f'], [rule('joint_candidate', 'w')], [],
            {'f': {'rc': 0, 'insns': 10, 'fallback': []}})
        self.assertEqual(screened, {'joint_candidate': ['f']})
        self.assertTrue(report['failed'])
        self.assertEqual(info['joint_candidate']['profitability_status'], 'regression')

    def test_baseline_screen_has_distinct_flags_and_cache(self):
        with tempfile.TemporaryDirectory() as d:
            llc, source = os.path.join(d, 'llc'), os.path.join(d, 'f.ll')
            for p in (llc, source):
                with open(p, 'w') as f:
                    f.write(p)
            t = jm.joint_target('AMDGPU')
            M = shared.Measurer(llc, t, ['joint_base', 'joint_candidate'], None, 1)
            with mock.patch.object(measure, 'compile_ll', return_value={'rc': 0}) as compile:
                M.one(source, M.all_ids, True)
                M.one(source, M.all_ids, ('joint_base',))
                M.one(source, M.all_ids, ('joint_base',))
            self.assertEqual(compile.call_count, 2)
            self.assertEqual(compile.call_args_list[0].kwargs['flags'],
                             [shared.SCREEN_FLAG])
            self.assertEqual(compile.call_args_list[1].kwargs['flags'],
                             [shared.SCREEN_FLAG, shared.SCREEN_APPLY_FLAG + 'joint_base'])
            self.assertEqual(M.hits, 1)


if __name__ == '__main__':
    unittest.main()
