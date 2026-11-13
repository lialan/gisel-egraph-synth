"""Selection objectives, round budgets and corpus split integrity."""
import copy
import contextlib
import io
import json
import os
from pathlib import Path
import struct
import tempfile
import types
import unittest
from unittest import mock

from test_agenda import cli
from girs import campaign, joint_tasks, measure, mine, portfolio
from girs.objective import Objective


def result(insns, size, fired=(), **extra):
    return dict(rc=0, insns=insns, code_bytes=size, fallback=[],
                passed=dict.fromkeys(fired, 1), **extra)


class SelectionTest(unittest.TestCase):
    def choose(self, effects, policy=Objective(), pins=(), cycles=lambda _: []):
        def compile_set(ids):
            return {p: result(*v, fired=ids) for p, v in effects(frozenset(ids)).items()}
        return portfolio.choose(['a', 'b'], pins, compile_set, policy, cycles, lambda _: None)

    def test_objectives_choose_different_implementations(self):
        def effects(ids):
            return {'f': (9, 48) if 'a' in ids else (11, 36) if 'b' in ids else (10, 40)}
        self.assertEqual(self.choose(effects)[0], {'a'})
        self.assertEqual(self.choose(effects, Objective('code_bytes'))[0], {'b'})

    def test_guardrail_rejects_smaller_instruction_count_with_larger_code(self):
        effects = lambda ids: {'f': (9, 48) if 'a' in ids else (10, 40)}
        selected, info, _ = self.choose(effects, Objective('insns', {'code_bytes': 0}))
        self.assertEqual(selected, set())
        self.assertEqual(info['a']['violations'], {'f': 'guardrail:code_bytes'})

    def test_per_file_regression_is_not_hidden_by_total_gain(self):
        effects = lambda ids: {'f': (5, 20), 'g': (11, 44)} if 'a' in ids else \
            {'f': (10, 40), 'g': (10, 40)}
        self.assertFalse(self.choose(effects)[0])

    def test_overlap_is_measured_inside_set(self):
        selected, info, summary = self.choose(
            lambda ids: {'f': (8, 32) if ids else (10, 40)})
        self.assertEqual(selected, {'a'})
        self.assertEqual(info['b']['selection'], 'no_gain_in_set')
        self.assertEqual(summary['objective_gain'], 2)

    def test_candidate_enabled_only_by_baseline_is_measured(self):
        selected, _, _ = self.choose(lambda ids:
            {'f': (8, 32) if {'base', 'a'} <= ids else (10, 40)}, pins=['base'])
        self.assertEqual(selected, {'base', 'a'})

    def test_cycles_are_not_promoted(self):
        selected, info, _ = self.choose(lambda ids: {'f': (9, 36) if ids else (10, 40)},
                                       cycles=lambda ids: [['a']] if 'a' in ids else [])
        self.assertEqual(selected, {'b'})
        self.assertEqual(info['a']['selection'], 'cycle')

    def test_missing_metric_and_changed_fallback_are_not_gains(self):
        with self.assertRaisesRegex(ValueError, 'measurement'):
            Objective('code_bytes').value({'insns': 1})
        base = result(10, 40)
        changed = result(8, 32)
        changed['fallback'] = ['f']
        self.assertEqual(Objective().violation(base, changed), 'fallback_changed')
        self.assertEqual(Objective().violation(base, {'rc': 1}), 'compile_failure')

    def test_feedback_uses_configured_gain(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / 'feedback.json'
            p.write_text(json.dumps({'candidates': {'a': {'window': 'w',
                'profitability_status': 'profitable', 'marginal': {'gain': 16, 'metric': 'code_bytes'}}}}))
            self.assertEqual(joint_tasks.load_feedback(str(p))[1], {'w': 16})


class CampaignBudgetTest(unittest.TestCase):
    def test_total_allowance_is_split_across_rounds_and_search_paths(self):
        c = copy.deepcopy(mine.DEFAULTS)
        c['loop'].update(rounds=3, search_budget_s=90, joint_share=.75)
        for i in range(3):
            r = campaign.round_config(c, i, 90 - i * 30, None)
            self.assertEqual(r['search']['time_budget_s'], 7.5)
            self.assertEqual(r['joint']['time_budget_s'], 22.5)
            self.assertEqual(r['loop']['search_budget_s'], 0)
        self.assertEqual(c['loop']['rounds'], 3)

    def test_disabled_joint_gives_all_time_to_ordinary_search(self):
        c = copy.deepcopy(mine.DEFAULTS)
        c['loop'].update(rounds=2, search_budget_s=60)
        c['joint']['enabled'] = False
        r = campaign.round_config(c, 0, 60, None)
        self.assertEqual(r['search']['time_budget_s'], 30)

    def test_invalid_budget_does_not_turn_into_unbounded_search(self):
        for key, value in [('rounds', 0), ('search_budget_s', -1),
                           ('search_budget_s', float('nan')), ('joint_share', 1)]:
            c = copy.deepcopy(mine.DEFAULTS['loop'])
            c[key] = value
            with self.assertRaises(ValueError):
                campaign.validate(c)

    def test_all_joint_configuration_options_reach_the_cli(self):
        cfg = {k: v for k, v in mine_joint_defaults().items() if k != 'enabled'}
        args = cli.default_args('joint-search', regions=['corpus'], out='out', **cfg)
        limits = cli._joint_limits(args)
        self.assertEqual(limits.cost_slack, 0)
        self.assertEqual(limits.semantic_variants, 6)
        self.assertEqual(limits.max_evals, cfg['max_evals'])


def mine_joint_defaults():
    return mine.DEFAULTS['joint']


class EncodedSizeTest(unittest.TestCase):
    def test_elf_counts_executable_sections_not_data_or_object_length(self):
        data = bytearray(64 + 3 * 64)
        data[:6] = b'\x7fELF\x02\x01'
        struct.pack_into('<Q', data, 40, 64)
        struct.pack_into('<HH', data, 58, 64, 3)
        struct.pack_into('<IIQQQQIIQQ', data, 128, 0, 1, 6, 0, 256, 20, 0, 0, 4, 0)
        struct.pack_into('<IIQQQQIIQQ', data, 192, 0, 1, 3, 0, 276, 500, 0, 0, 8, 0)
        self.assertEqual(measure.elf_code_bytes(data), 20)
        with self.assertRaises(ValueError):
            measure.elf_code_bytes(b'assembly text')

    def test_summary_uses_selected_metric_and_preserves_instruction_counts(self):
        units = [mine.Unit('heldout', 'direct', 'f', 'f')]
        a = {'f': result(10, 40, bytes=100, user=1)}
        b = {'f': result(9, 48, bytes=90, user=1)}
        s = mine.summarize(units, a, b, Objective('code_bytes'))['heldout/direct']
        self.assertEqual(s['insns_delta'], -1)
        self.assertEqual(s['code_bytes_delta'], 8)
        self.assertEqual(s['files_worse'], 1)


class CorpusMetadataTest(unittest.TestCase):
    def test_projects_must_be_disjoint_and_ir_hashes_current(self):
        with tempfile.TemporaryDirectory() as d:
            r = mine.Run.__new__(mine.Run)
            files, units = {}, []
            for role in ('discovery', 'validation'):
                p = Path(d) / (role + '.ll')
                p.write_text(role)
                files[role] = [str(p)]
                units.append({'ir': str(p), 'role': role, 'project': 'same', 'sha256': mine._sha_file(p)})
            metadata = Path(d) / 'metadata.json'
            metadata.write_text(json.dumps({'units': units}))
            r.cfg = {'manifests': files, 'corpus_metadata': str(metadata)}
            r.manifest = lambda role: files[role]
            with self.assertRaisesRegex(ValueError, 'program group'):
                r.validate_manifests()
            units[1]['project'] = 'other'
            metadata.write_text(json.dumps({'units': units}))
            r.validate_manifests()
            Path(files['validation'][0]).write_text('changed')
            with self.assertRaisesRegex(ValueError, 'stale'):
                r.validate_manifests()


class CampaignEndToEndTest(unittest.TestCase):
    def test_two_rounds_promote_locally_freeze_once_and_resume_without_search(self):
        from girs import emit, mine_joint
        from test_joint import dsq
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            manifests = {}
            for role in ('discovery', 'validation', 'heldout'):
                src = root / (role + '.ll')
                src.write_text('define i32 @' + role + '(i32 %x) { ret i32 %x }\n')
                manifest = root / (role + '.txt')
                manifest.write_text(str(src) + '\n')
                manifests[role] = str(manifest)
            config = {'target': 'AArch64', 'llc': '/usr/bin/true', 'opt': '/usr/bin/true',
                'cache_dir': str(root / 'cache'), 'build_dir': str(root / 'compiler'),
                'jobs': 1, 'pipelines': ['direct'], 'manifests': manifests,
                'loop': {'rounds': 2}, 'search': {'search_jobs': 0, 'max_terms': 100, 'max_evals': 1000},
                'joint': {'jobs': 1, 'time_s': .05, 'max_terms': 1000, 'max_helpers': 2}}
            cfg = root / 'input.json'
            cfg.write_text(json.dumps(config))
            win = dsq()
            rec = {'kind': 'region', 'fn': 'f', 'bb': 0,
                   'inputs': win.to_json()['inputs'], 'instrs': []}
            for k, ins in enumerate(win.instrs):
                rec['instrs'].append({'op': ins.name, 'flags': [],
                    'defs': [{'w': w, 'uses': ins.uses[j], 'reg': '%%%d_%d' % (k, j),
                              'defined': True} for j, w in enumerate(ins.ws)],
                    'args': [{'in': a[1]} if a[0] == 'in' else {'node': a[1], 'res': a[2]}
                             for a in ins.args]})
            profitable = mine_joint.load(mine_joint.catalog_path())['rules'][0]['id']
            heldout_calls = []
            def extract(llc, source, output, *args, **kw):
                out = Path(output) / ('a.regions.jsonl' if 'joint' in output else 'a.jsonl')
                out.write_text(json.dumps(rec) + '\n' if 'joint' in output else '')
                return source, str(out)
            def build(run, db, profiles, directory):
                Path(run.p(directory)).mkdir(exist_ok=True)
                text = emit.emit(db, profiles)[0] + ''.join(run.joint.build_files(directory == 'baseline').values())
                Path(run.p(directory, 'llc')).write_text(text)
                return {'rules': len(db['rules'])}
            def compile(llc, target, path, flags=(), synth=False, disabled=(), **kw):
                if 'heldout' in path:
                    heldout_calls.append(str(llc))
                used = synth and profitable not in disabled
                return result(10 - used, 40 - 4 * used, [profitable] if used else [], bytes=100, user=.01)
            cwd = os.getcwd()
            try:
                with mock.patch.object(mine.paths, 'LLVM_ROOT', d), \
                     mock.patch.object(cli, '_git', return_value='fixed'), \
                     mock.patch.object(mine.Run, 'build_identity', return_value={}), \
                     mock.patch.object(mine.Run, '_build', build), \
                     mock.patch.object(cli, '_extract_one', side_effect=extract), \
                     mock.patch.object(cli, '_joint_extract_one', side_effect=extract), \
                     mock.patch.object(cli, '_legality', return_value=None), \
                     mock.patch.object(measure, 'compile_ll', side_effect=compile), \
                     contextlib.redirect_stdout(io.StringIO()):
                    run = mine.Run(str(cfg), str(root / 'run'), cli, log=lambda _: None)
                    final = campaign.execute(run, until='verify')
                    self.assertEqual(heldout_calls, [])
                    self.assertIn(profitable, final.joint.pinned())
                    final = campaign.execute(run)
                    self.assertEqual(len(heldout_calls), 2)
                    report = mine._load(run.p('report.json'))
                    self.assertEqual(len(report['campaign']['rounds']), 2)
                    self.assertEqual(report['campaign']['new_selected'], [profitable])
                    self.assertEqual(report['evaluation']['final']['heldout/direct']['insns_delta'], -1)
                    with mock.patch.object(cli, 'cmd_joint_search', side_effect=AssertionError('researched')):
                        campaign.execute(run)
                    self.assertEqual(len(heldout_calls), 2)
            finally:
                os.chdir(cwd)


if __name__ == '__main__':
    unittest.main()
