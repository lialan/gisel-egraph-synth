"""Joint candidates use mine's baseline, selection, freeze and export gates."""
import copy
import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import types
import unittest
from unittest import mock

from test_agenda import cli
from test_joint import dsq
import test_incremental
from girs import joint_emit, measure, mine, mine_joint, targets


class JointMineTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.db = mine_joint.load(mine_joint.catalog_path())
        self.rules = self.db['rules'][:2]
        self.r = mine.Run.__new__(mine.Run)
        self.r.dir = self.tmp.name
        self.r.cfg = copy.deepcopy(mine.DEFAULTS)
        self.r.cfg['jobs'] = 1
        self.r.cfg['joint']['jobs'] = 1
        self.r.cfg['cache_dir'] = str(self.root / 'cache')
        self.r.target = copy.copy(targets.get('AArch64'))
        self.r.target.joint = True
        self.r.cli = cli
        self.r.state = {'stages': {}}
        self.r.log = lambda _: None

    def write(self, name, obj):
        p = self.root / name
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(json.dumps(obj))

    def baseline(self, pins=()):
        self.write('joint/baseline/rules.json', self.db)
        for n in targets.TARGETS:
            p = mine_joint.pin(self.db, {'target': n, 'rules': {
                i: {'selection': 'emitted'} for i in pins}})
            self.write('joint/baseline/' + n + '.json', p)
        self.write('joint/library/rules.json', self.db)
        mine_joint.copy_proofs(self.db, self.r.joint.p('baseline', 'proofs'),
            [str(Path(mine_joint.catalog_path()).parent / 'proofs')])

    def test_joint_is_integrated_by_default_but_respects_vector_only_scope(self):
        self.assertTrue(self.r.joint.enabled())
        self.baseline([self.rules[0]['id']])
        self.r.cfg['search']['only_vectors'] = True
        self.assertFalse(self.r.joint.search_enabled())
        self.assertEqual(self.r.joint.active(), [self.rules[0]['id']])
        self.assertEqual(self.r.joint.delta(), [])

    def test_shipped_rules_are_candidates_not_pinned_baselines(self):
        self.baseline()
        self.assertFalse(self.r.joint.pinned())
        self.assertEqual(set(self.r.joint.delta()), {x['id'] for x in self.db['rules']})
        base = self.r.joint.build_files(True)
        self.assertNotIn('def joint_', next(v for k, v in base.items() if k.endswith('.td')))
        self.assertIn('def joint_', next(v for k, v in self.r.joint.build_files(False).items()
                                         if k.endswith('.td')))

    def test_joint_only_delta_does_not_skip_evaluation_stages(self):
        self.baseline()
        r = self.r
        r.delta = lambda: []
        r.state_path = r.p('state.json')
        calls = []
        stages = ('build', 'measure', 'select', 'verify', 'freeze', 'heldout')
        for name in stages:
            setattr(r, 'inputs_' + name, lambda: {})
            setattr(r, 'stage_' + name, lambda n=name: calls.append(n))
        with mock.patch.object(mine, 'STAGES', stages):
            r.run()
        self.assertEqual(calls, list(stages))
        self.assertTrue(all(v['status'] == 'done' for v in r.state['stages'].values()))

    def test_target_profiles_restrict_the_shared_emitter(self):
        a, b = self.rules
        profiles = {n: mine_joint.pin(self.db, {'rules': {
            rule['id']: {'selection': 'emitted'}}})
            for n, rule in [('AMDGPU', a), ('AArch64', b)]}
        td, inc = mine_joint.generated(self.db, profiles)
        for rule, check in [(a, 'TT.isAMDGPU()'), (b, 'TT.isAArch64()')]:
            body = inc.split('inline bool match_' + rule['id'])[1].split('inline void')[0]
            self.assertIn(check, body)
        # Independent target profile additions cannot reorder the pinned
        # subset; emission has a canonical order, not target merge order.
        self.assertEqual([i for i in sorted((a['id'], b['id']))],
                         [l.split()[1] for l in td.splitlines() if l.startswith('def joint_')])

    def test_standalone_emission_keeps_existing_behavior(self):
        _, inc, _ = joint_emit.emit(self.rules)
        self.assertNotIn('TT.is', inc)

    def test_profile_detects_changed_rule_content_and_model(self):
        rid = self.rules[0]['id']
        p = mine_joint.pin(self.db, {'rules': {rid: {'selection': 'emitted'}}})
        self.write('profile.json', p)
        altered = copy.deepcopy(self.db)
        altered['rules'][0]['candidate']['text'] += ' changed'
        with self.assertRaisesRegex(ValueError, 'baseline changed'):
            mine_joint.profile(altered, 'AArch64', str(self.root / 'profile.json'))
        with mock.patch.object(mine_joint, 'model', return_value='another-model'):
            with self.assertRaisesRegex(ValueError, 'baseline changed'):
                mine_joint.profile(self.db, 'AArch64', str(self.root / 'profile.json'))

    def test_merge_never_replaces_a_pinned_revision(self):
        rule = copy.deepcopy(self.rules[0])
        rule['candidate']['text'] += ' revision'
        merged = mine_joint.merge(self.db, [rule])
        self.assertEqual(len(merged['rules']), len(self.db['rules']) + 1)
        self.assertEqual(next(r for r in merged['rules'] if r['id'] == rule['id']),
                         self.rules[0])

    def test_proofs_are_preserved_and_corruption_is_rejected(self):
        destination = self.root / 'proofs'
        roots = [str(Path(mine_joint.catalog_path()).parent / 'proofs')]
        mine_joint.copy_proofs(self.db, str(destination), roots)
        proof = self.rules[0]['proofs'][0]['smt2_file'].split('/')[-1]
        (destination / proof).write_text('corrupt')
        with self.assertRaisesRegex(ValueError, 'hash mismatch'):
            mine_joint.copy_proofs(self.db, str(destination), roots)

    def test_residual_extraction_runs_after_both_pinned_combiners(self):
        for name in targets.TARGETS:
            t = copy.copy(targets.get(name))
            t.joint = True
            calls = []
            def run(command, **kwargs):
                calls.append((command, kwargs))
                return types.SimpleNamespace(returncode=0, stdout=b'residual MIR')
            with mock.patch.object(cli.subprocess, 'run', side_effect=run):
                cli._joint_extract_one('llc', 'f.ll', self.tmp.name, t, baseline=True)
            self.assertIn(t.enable_flag, calls[0][0])
            self.assertIn('-gisel-synth-joint-combines', calls[0][0])
            self.assertIn('-stop-after=' + t.synth_pass, calls[0][0])
            self.assertIn('-run-pass=gisel-synth-regions', calls[1][0])
            self.assertEqual(calls[1][1]['input'], b'residual MIR')

    def test_flags_counters_and_disabled_rules_cover_both_combiners(self):
        t = self.r.target
        rid = self.rules[0]['id']
        calls = []
        def compile(command, *args):
            calls.append(command)
            Path(command[-1]).write_text('\tadd w0, w0, w1\n')
            return 0, ('gisel-synth: matched: ordinary\n'
                       'gisel-synth: guard passed: ordinary\n'
                       'gisel-synth-joint: anchor: ' + rid + '\n'
                       'gisel-synth-joint: applied: ' + rid + '\n'), .1
        with mock.patch.object(measure, 'run_timed', side_effect=compile):
            res = measure.compile_ll('llc', t, 'f.ll', synth=True,
                                     disabled=['ordinary', rid])
        self.assertEqual(res['matched'], {'ordinary': 1, rid: 1})
        self.assertEqual(res['passed'], {'ordinary': 1, rid: 1})
        self.assertIn(t.disable_rule_flag + 'ordinary', calls[0])
        self.assertIn('--gisynthjointcombiner-disable-rule=' + rid, calls[0])
        self.assertIn('-debug-only=gisel-synth,gisel-synth-joint', calls[0])

    def select_with(self, behavior, pins=()):
        self.baseline(pins)
        r = self.r
        r.pinned = lambda: ['ordinary']
        r.names = lambda db: {'ordinary': ['ordinary']}
        r.library = lambda: {}
        prof = {'rules': {'ordinary': {'selection': 'emitted', 'pinned': True}}}
        names = r.all_names()
        (self.root / 'build').mkdir(exist_ok=True)
        (self.root / 'build' / 'llc').write_text('compiler')
        def compile(llc, target, path, synth=True, disabled=(), **kwargs):
            enabled = set(names) - set(disabled)
            delta, fallback, rc = behavior(enabled, os.path.basename(path))
            return {'rc': rc, 'insns': 10 + delta, 'fallback': fallback,
                    'matched': dict.fromkeys(enabled, 1), 'passed': dict.fromkeys(enabled, 1)}
        base = {'rc': 0, 'insns': 10, 'fallback': []}
        files = [self.root / p for p in ('a.ll', 'b.ll')]
        for p in files:
            p.write_text(p.name)
        # Each invocation of this helper models a different compiler.
        (self.root / 'build' / 'llc').write_text(repr(behavior))
        compare = {str(p): {'base': base, 'synth': base} for p in files}
        with mock.patch.object(measure, 'compile_ll', side_effect=compile), \
                mock.patch.object(measure, 'failing_rules', return_value=list(names)):
            r.joint.select(prof, compare)
        return mine_joint.load(r.joint.p(r.target.name + '.selected.json'))

    def test_joint_rule_requires_marginal_gain(self):
        profitable = self.rules[0]['id']
        p = self.select_with(lambda enabled, path: (-1 if profitable in enabled else 0, [], 0))
        self.assertEqual(p['rules'][profitable]['selection'], 'emitted')
        self.assertTrue(all(v['selection'] == 'no_measured_gain'
                            for i, v in p['rules'].items() if i != profitable))

    def test_combined_per_file_regression_is_removed_even_with_net_gain(self):
        bad = self.rules[0]['id']
        p = self.select_with(lambda enabled, path:
            ((-3 if path == 'a.ll' else 1) if bad in enabled else 0, [], 0))
        self.assertEqual(p['rules'][bad]['selection'], 'final_set_violation')

    def test_combined_fallback_change_and_crash_are_removed(self):
        bad = self.rules[0]['id']
        for crash in (False, True):
            with self.subTest(crash=crash):
                p = self.select_with(lambda enabled, path:
                    (-1, ['f'] if bad in enabled and not crash else [],
                     1 if bad in enabled and crash else 0))
                self.assertEqual(p['rules'][bad]['selection'], 'final_set_violation')

    def test_joint_pinned_baseline_is_never_removed_for_zero_gain(self):
        pinned = self.rules[0]['id']
        p = self.select_with(lambda enabled, path: (0, [], 0), pins=[pinned])
        self.assertEqual(p['rules'][pinned]['selection'], 'emitted')
        self.assertTrue(p['rules'][pinned]['pinned'])

    def test_partial_joint_search_failure_is_not_marked_complete(self):
        self.baseline()
        for field in ('failed_tasks', 'missing_rules', 'failed_shards'):
            with self.subTest(field=field):
                def search(args):
                    self.write('joint/search/stats.json', {'status': {}, field: ['failure']})
                with mock.patch.object(cli, 'cmd_joint_search', side_effect=search):
                    with self.assertRaisesRegex(RuntimeError, 'joint search failed'):
                        self.r.joint.discover()

    def test_search_controls_and_partial_queue_are_forwarded_and_resumed(self):
        self.baseline()
        self.r.cfg = mine._merge(self.r.cfg, {'joint': {
            'cost_slack': 1, 'semantic_variants': 4, 'max_proofs': 1,
            'cache': str(self.root / 'persistent'), 'time_budget_s': 2,
            'priority': str(self.root / 'feedback.json')}})
        calls = []
        def search(args):
            calls.append(args)
            self.write('joint/search/rules.json', {'rules': []})
            self.write('joint/search/stats.json', {'status': {},
                'queue': {'not_searched': 1 if len(calls) == 1 else 0}})
            return 0
        with mock.patch.object(cli, 'cmd_joint_search', side_effect=search):
            first = self.r.joint.discover()
            second = self.r.joint.discover()
        self.assertTrue(first['incomplete'])
        self.assertFalse(second['incomplete'])
        self.assertEqual(len(calls), 2)
        self.assertEqual(calls[0].cache, str(self.root / 'persistent'))
        self.assertEqual(calls[0].priority, str(self.root / 'feedback.json'))
        self.assertEqual((calls[0].cost_slack, calls[0].semantic_variants), (1, 4))
        self.assertEqual(calls[0].max_proofs, 1)

    def test_joint_interruption_keeps_results_and_stops_mine(self):
        self.baseline()
        def search(args):
            self.write('joint/search/rules.json', {'rules': []})
            self.write('joint/search/stats.json', {'status': {}, 'interrupted': True})
            return 130
        with mock.patch.object(cli, 'cmd_joint_search', side_effect=search):
            with self.assertRaises(SystemExit) as ex:
                self.r.joint.discover()
        self.assertEqual(ex.exception.code, 130)
        self.assertEqual(len(self.r.joint.library()['rules']), len(self.db['rules']))

    def test_measured_and_legacy_feedback_follow_the_selected_policy(self):
        self.write('joint/feedback.json', {'candidates': {'new': {'marginal': {'gain': 4}}}})
        self.write('joint/selection.json', {'candidates': {'old': {}}})
        self.assertEqual(self.r.joint.feedback(), self.r.joint.p('feedback.json'))
        before = self.r.joint.feedback_identity()
        self.write('joint/feedback.json', {'candidates': {}})
        self.assertNotEqual(before, self.r.joint.feedback_identity())
        self.r.cfg['select']['strategy'] = 'legacy'
        self.assertEqual(self.r.joint.feedback(), self.r.joint.p('selection.json'))

    def test_same_window_alternatives_are_measured_separately(self):
        a, b = self.rules
        for rule in self.db['rules']:
            rule['window'] = 'shared-window' if rule['id'] in (a['id'], b['id']) else rule['id']
        def behavior(enabled, path):
            return (-1 if a['id'] in enabled else -3 if b['id'] in enabled else 0, [], 0)
        p = self.select_with(behavior)
        self.assertEqual(p['rules'][b['id']]['selection'], 'emitted')
        self.assertEqual(p['rules'][a['id']]['selection'], 'dominated_in_window')
        feedback = mine_joint.load(self.r.joint.feedback())
        self.assertEqual(feedback['candidates'][a['id']]['marginal']['insns_saved'], 2)
        self.assertEqual(feedback['candidates'][b['id']]['marginal']['insns_saved'], 6)

    def test_frozen_joint_artifacts_detect_profile_and_library_changes(self):
        self.baseline()
        self.write('joint/AArch64.json', {'rules': {}})
        frozen = self.r.joint.artifacts()
        self.write('joint/AArch64.json', {'rules': {'different': {}}})
        self.assertNotEqual(frozen, self.r.joint.artifacts())
        frozen = self.r.joint.artifacts()
        self.write('joint/library/rules.json', {'rules': []})
        self.assertNotEqual(frozen, self.r.joint.artifacts())

    def test_mine_runs_joint_only_additions_through_report_and_resume(self):
        """Real search/proof/selection/stage driver; compiler IO is simulated.

        Backend code generation itself is covered by the LLVM integration
        tests. This catches missing stage wiring and incompatible artifacts.
        """
        manifests = {}
        for role in ('discovery', 'validation', 'heldout'):
            source = self.root / (role + '.ll')
            source.write_text('define i32 @' + role + '(i32 %x) { ret i32 %x }\n')
            manifest = self.root / (role + '.txt')
            manifest.write_text(str(source) + '\n')
            manifests[role] = str(manifest)
        cfg = {'target': 'AArch64', 'llc': '/usr/bin/true', 'opt': '/usr/bin/true',
               'build_dir': str(self.root / 'compiler'), 'jobs': 1,
               'cache_dir': str(self.root / 'cache'), 'pipelines': ['direct'],
               'manifests': manifests, 'restore_build': False,
               'search': {'search_jobs': 0, 'max_terms': 100, 'max_evals': 1000},
               'joint': {'jobs': 1, 'time_s': .1, 'max_terms': 5000, 'max_helpers': 8}}
        self.write('config-input.json', cfg)
        win = dsq()
        rec = {'kind': 'region', 'fn': 'discovery', 'bb': 0,
               'inputs': win.to_json()['inputs'], 'instrs': []}
        for k, ins in enumerate(win.instrs):
            rec['instrs'].append({'op': ins.name, 'flags': [],
                'defs': [{'w': w, 'uses': ins.uses[j], 'reg': '%%%d_%d' % (k, j),
                          'defined': True} for j, w in enumerate(ins.ws)],
                'args': [{'in': a[1]} if a[0] == 'in' else {'node': a[1], 'res': a[2]}
                         for a in ins.args]})
        def extract(llc, source, output, *args, **kwargs):
            out = Path(output) / ('input.regions.jsonl' if 'joint' in output else 'input.jsonl')
            out.write_text(json.dumps(rec) + '\n' if 'joint' in output else '')
            return source, str(out)
        builds = []
        def build(run, db, profiles, directory):
            builds.append(directory)
            from girs import emit
            text = emit.emit(db, profiles)[0]
            text += ''.join(run.joint.build_files(directory == 'baseline').values())
            Path(run.p(directory)).mkdir(exist_ok=True)
            Path(run.p(directory, 'llc')).write_text(text)
            return {'rules': len(db['rules'])}
        profitable = self.rules[0]['id']
        def compile(llc, target, path, flags=(), synth=False, disabled=(), **kwargs):
            off = set(disabled) | set(getattr(target, 'joint_disabled', ()))
            used = synth and profitable not in off
            out = {'rc': 0, 'insns': 10 - used, 'bytes': 20, 'user': .01, 'fallback': []}
            if used:
                out.update(matched={profitable: 1}, passed={profitable: 1})
            return out
        cwd = os.getcwd()
        try:
            with mock.patch.object(mine.paths, 'LLVM_ROOT', self.tmp.name), \
                    mock.patch.object(cli, '_git', return_value='06e517fab802'), \
                    mock.patch.object(mine.Run, 'build_identity', return_value={}), \
                    mock.patch.object(mine.Run, '_build', build), \
                    mock.patch.object(cli, '_extract_one', side_effect=extract), \
                    mock.patch.object(cli, '_joint_extract_one', side_effect=extract), \
                    mock.patch.object(cli, '_legality', return_value=None), \
                    mock.patch.object(measure, 'compile_ll', side_effect=compile), \
                    contextlib.redirect_stdout(io.StringIO()):
                run = mine.Run(str(self.root / 'config-input.json'),
                               str(self.root / 'complete'), cli, log=lambda _: None)
                run.run()
                self.assertEqual(run.delta(), [])
                self.assertEqual(run.joint.final(), [profitable])
                self.assertEqual(builds, ['baseline', 'build'])
                report = mine._load(run.p('report.json'))
                self.assertTrue(report['evaluated'])
                self.assertEqual(report['joint']['selected'], [profitable])
                self.assertEqual(report['evaluation']['final']['heldout/direct']['files_worse'], 0)
                self.assertIn('Joint DAG rules', Path(run.p('report.md')).read_text())
                self.assertIn('joint_profile_sha256', mine._load(run.p('frozen.json')))
                # Feedback is consumed on the next invocation. A pending
                # budget row remains pending, but its decided work is cached.
                run.run()
                stats = mine._load(run.joint.p('search', 'stats.json'))
                self.assertEqual(stats['searched_in_this_run'], 0)
                self.assertEqual(builds, ['baseline', 'build'])
        finally:
            os.chdir(cwd)


class JointExportTest(test_incremental.ExportTest):
    """Exercise the actual shared export path with both catalogs."""
    def setUp(self):
        super().setUp()
        source = Path(mine_joint.catalog_path()).parent
        db = mine_joint.validate(mine_joint.load(str(source / 'rules.json')))
        local = Path(self.tmp) / 'maintained-joint'
        local.mkdir()
        patch = mock.patch.object(mine_joint, 'catalog_path', return_value=str(local / 'rules.json'))
        patch.start()
        self.addCleanup(patch.stop)
        mine._dump(db, str(local / 'rules.json'))
        mine_joint.copy_proofs(db, str(local / 'proofs'), [str(source / 'proofs')])
        r = self.run
        r.cfg = copy.deepcopy(mine.DEFAULTS)
        for folder in ('baseline', 'library'):
            Path(r.joint.p(folder)).mkdir(parents=True)
            mine._dump(db, r.joint.p(folder, 'rules.json'))
            mine_joint.copy_proofs(db, r.joint.p(folder, 'proofs'), [str(source / 'proofs')])
        for n in targets.TARGETS:
            p = mine_joint.profile(db, n)
            mine._dump(p, r.joint.p('baseline', n + '.json'))
        self.joint_id = db['rules'][0]['id']
        selected = mine_joint.pin(db, {'rules': {
            self.joint_id: {'selection': 'emitted', 'in_set': {'insns': -1}}},
            'final_check': {'violations': {}}})
        mine._dump(selected, r.joint.p(r.target.name + '.json'))
        frozen = mine._load(r.p('frozen.json'))
        frozen.update(r.joint.artifacts())
        mine._dump(frozen, r.p('frozen.json'))

    def test_joint_export_preserves_proofs_and_other_target(self):
        r = self.run
        other = mine_joint.profile(r.joint.library(), 'AArch64')
        Path(mine_joint.profile_path('AArch64')).parent.mkdir(parents=True)
        mine._dump(other, mine_joint.profile_path('AArch64'))
        mine.export(r, self.cli, log=lambda _: None)
        live = mine_joint.load(mine_joint.catalog_path())
        self.assertEqual(mine_joint.profile(live, 'AMDGPU')['baseline']['order'], [self.joint_id])
        self.assertEqual(mine_joint.profile(live, 'AArch64'), other)
        mine_joint.copy_proofs(live, str(Path(self.tmp) / 'verify-proofs'),
                              [str(Path(mine_joint.catalog_path()).parent / 'proofs')])

    def test_export_refuses_changed_joint_baseline(self):
        r = self.run
        changed = mine_joint.pin(r.joint.library(), {'rules': {
            self.joint_id: {'selection': 'emitted'}}})
        Path(mine_joint.profile_path(r.target.name)).parent.mkdir(parents=True)
        mine._dump(changed, mine_joint.profile_path(r.target.name))
        with self.assertRaisesRegex(SystemExit, 'joint target baseline changed'):
            mine.export(r, self.cli)

    def test_export_refuses_changed_joint_frozen_profile(self):
        p = self.run.joint.p(self.run.target.name + '.json')
        changed = mine._load(p)
        changed['rules'][self.joint_id]['selection'] = 'no_measured_gain'
        mine._dump(changed, p)
        with self.assertRaisesRegex(SystemExit, 'artifacts changed'):
            mine.export(self.run, self.cli)


if __name__ == '__main__':
    unittest.main()
