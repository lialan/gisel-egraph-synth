"""Shared knowledge, pinned baselines and interrupted incremental runs."""

import copy
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import time
import types
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from girs import corpus, discover, emit, history, ir, known, mine, select, smt, synth, targets
import z3

spec = importlib.util.spec_from_file_location('incremental_cli', ROOT / 'gi-rule-synth.py')
cli = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = cli
spec.loader.exec_module(cli)


def instance(width=32):
    return corpus.Instance(('G_AND', width, ('var', 0), ('var', 0)),
                           (width,), [(0, 0)], [None], [], [],
                           [('f.ll', 'fn', '%0')])


def library(proofs=None):
    i = instance()
    sy = synth.Synthesizer(smt.Z3Backend(), proof_dir=proofs)
    rid = sy.add(i, ('var', 0))
    sy.finalize([i])
    return known.stamp({'rules': [synth.strip_private(sy.rules[rid])]})


class KnowledgeTest(unittest.TestCase):
    def test_known_pair_skips_concrete_and_generalization_proofs(self):
        db = library()
        idx = known.Index(db)
        i = instance()
        limits = discover.Limits(max_proofs=1)
        ctx = discover.Context(limits)
        ctx.known = idx
        backend = smt.Z3Backend()
        with mock.patch.object(backend, 'check', side_effect=AssertionError('old proof')):
            st = discover.new_stats()
            result = discover.prove_candidates(i, [('var', 0)], backend,
                                                limits, ctx, st)
            # The known rule is a result of the search, without a proof.
            self.assertEqual([(c['tgt'], c['known']) for c in result],
                             [(('var', 0), db['rules'][0]['id'])])
            self.assertNotIn('proof', result[0])
            self.assertEqual(st['known_candidates'], 1)
            self.assertEqual(st['smt_checks'], 0)
            sy = synth.Synthesizer(backend)
            sy.known = idx
            self.assertIsNone(sy.add(i, ('var', 0)))

    def test_different_rhs_and_unproved_width_are_still_new(self):
        db = library()
        for d in db['rules'][0]['disjuncts']:
            d['width_maps'] = [[[32, 32]]]
        idx = known.Index(db)
        self.assertIsNotNone(idx.covers(instance(), ('var', 0)))
        self.assertIsNone(idx.covers(instance(16), ('var', 0)))
        self.assertIsNone(idx.covers(instance(), ('lit', 32, '0')))

    def test_facts_outside_the_known_guard_remain_candidates(self):
        db = library()
        for d in db['rules'][0]['disjuncts']:
            d['pred_json'] = [['def', 0]]
        idx = known.Index(db)
        self.assertIsNone(idx.covers(instance(), ('var', 0)))
        i = instance()
        i.facts = ((0, 0, True),)
        self.assertIsNotNone(idx.covers(i, ('var', 0)))

    def test_scalar_knowledge_does_not_hide_a_new_vector_domain(self):
        db = library()
        rid = db['rules'][0]['id']
        target = targets.get('AMDGPU')
        profile = known.pin(db, {'rules': {rid: {'selection': 'emitted'}}}, target)
        inst = instance()
        inst.lifted = True
        idx = known.Index(db)
        self.assertIsNone(idx.covers(inst, ('var', 0)))
        sy = synth.Synthesizer(smt.Z3Backend())
        sy.known = idx
        new = sy.add(inst, ('var', 0))
        self.assertIsNotNone(new)
        sy.finalize([inst])
        rule = synth.strip_private(sy.rules[new])
        self.assertTrue(emit.lifts(rule))
        combined, delta = known.merge(db, [rule])
        self.assertEqual(len(delta), 1)
        self.assertNotEqual(delta[0], rid)
        self.assertEqual(known.validate_profile(combined, profile, target), [rid])
        self.assertIsNotNone(known.Index(combined).covers(inst, ('var', 0)))

    def test_one_use_and_region_not_pruned_as_plain_tree(self):
        db = library()
        db['rules'][0]['needs_one_use'] = True
        self.assertIsNone(known.Index(db).covers(instance(), ('var', 0)))
        db['rules'][0]['region'] = {'outputs': []}
        self.assertEqual(known.Index(db).by_key, {})

    def test_guard_and_width_changes_do_not_replace_baseline(self):
        db = library()
        target = targets.get('AMDGPU')
        rid = db['rules'][0]['id']
        p = known.pin(db, {'rules': {rid: {'selection': 'emitted'}}}, target)
        revised = copy.deepcopy(db['rules'][0])
        revised['disjuncts'][0]['width_maps'].append([[32, 128]])
        combined, added = known.merge(db, [revised])
        self.assertEqual(len(added), 1)
        self.assertNotEqual(added[0], rid)
        self.assertEqual(known.validate_profile(combined, p, target), [rid])
        self.assertEqual(known.merge(combined, [revised])[1], [])
        changed = copy.deepcopy(db)
        changed['rules'][0]['needs_one_use'] = True
        with self.assertRaisesRegex(ValueError, 'content changed'):
            known.validate_profile(changed, p, target)

    def test_support_changes_are_not_a_new_revision(self):
        db = library()
        r = copy.deepcopy(db['rules'][0])
        r['support']['occurrences'] += 100
        self.assertEqual(known.merge(db, [r])[1], [])

    def test_stale_semantics_require_explicit_refresh(self):
        db = library()
        with mock.patch.object(known, 'semantics_sha', return_value='new model'):
            with self.assertRaisesRegex(ValueError, 'refresh-known'):
                known.Index(db)

    def test_semantic_refresh_cannot_repin_a_target_implicitly(self):
        db = library()
        t = targets.get('AMDGPU')
        rid = db['rules'][0]['id']
        p = known.pin(db, {'rules': {rid: {'selection': 'emitted'}}}, t)
        changed = copy.deepcopy(db)
        changed['knowledge']['semantics_sha256'] = 'changed matcher contract'
        with self.assertRaisesRegex(ValueError, 'semantic model changed'):
            known.validate_profile(changed, p, t)

    def test_refresh_rejects_old_aliasing_nondeterministic_proofs(self):
        minimum = ('G_FMINNUM', 32, ('var', 0), ('var', 1))
        bits = ('G_BITCAST', 32, minimum)
        src = ('G_XOR', 32, bits, bits)
        db = library()
        db['rules'][0]['source_json'] = ir.to_json(src)
        db['rules'][0]['vw'] = [32, 32]
        backend = smt.Z3Backend()
        with tempfile.TemporaryDirectory() as d, \
                mock.patch.object(backend, 'check', side_effect=AssertionError('aliased proof')):
            with self.assertRaisesRegex(ValueError, 'structural'):
                known.refresh(db, backend, d)


class HistoryTest(unittest.TestCase):
    def test_model_identity_survives_mine_changing_directory(self):
        expected = cli._model_sha()
        old = os.getcwd()
        with tempfile.TemporaryDirectory() as d, \
                mock.patch.object(cli, '__file__', 'tools/gisel-rule-synth/gi-rule-synth.py'):
            try:
                os.chdir(d)
                self.assertEqual(cli._model_sha(), expected)
            finally:
                os.chdir(old)

    def test_symbol_sorts_are_part_of_a_proof_key(self):
        with tempfile.TemporaryDirectory() as d:
            b = smt.Z3Backend()
            b.history = history.Proofs(d, 'model')
            x1, x2 = z3.BitVec('x', 1), z3.BitVec('x', 2)
            self.assertEqual((-x1 != x1).sexpr(), (-x2 != x2).sexpr())
            self.assertEqual(b.check(-x1 != x1).status, 'unsat')
            self.assertEqual(b.check(-x2 != x2, [x2]).status, 'sat')
            self.assertEqual(b.calls, 2)
            b.history.close()

    def test_sat_and_unsat_survive_budget_increase(self):
        x = z3.BitVec('x', 8)
        with tempfile.TemporaryDirectory() as d:
            b = smt.Z3Backend(timeout_ms=100)
            b.history = history.Proofs(d, 'model')
            self.assertEqual(b.check(x != x).status, 'unsat')
            sat = b.check(x == 7, [x])
            self.assertEqual(sat.model, [7])
            b.history.close()
            b = smt.Z3Backend(timeout_ms=10000)
            b.history = history.Proofs(d, 'model')
            with mock.patch.object(b, '_check', side_effect=AssertionError('solver')):
                self.assertEqual(b.check(x != x).status, 'unsat')
                self.assertEqual(b.check(x == 7, [x]).model, [7])
            self.assertEqual(b.calls, 0)
            self.assertEqual(b.history.hits, 2)
            b.history.close()

    def test_unknown_is_retryable_and_model_change_invalidates(self):
        f = z3.BoolVal(False)
        with tempfile.TemporaryDirectory() as d:
            b = smt.Z3Backend()
            b.history = history.Proofs(d, 'old')
            with mock.patch.object(b, '_check', return_value=smt.Result('unknown')):
                self.assertEqual(b.check(f).status, 'unknown')
            self.assertEqual(b.check(f).status, 'unsat')
            self.assertEqual(b.calls, 1)
            b.history.close()
            b.history = history.Proofs(d, 'new')
            self.assertEqual(b.check(f).status, 'unsat')
            self.assertEqual(b.calls, 2)
            b.history.close()

    def test_slow_retry_cannot_extend_overall_deadline(self):
        b = smt.Z3Backend()
        b.deadline = time.monotonic() - 1
        old = b.deadline
        with b.limit(120000, 300):
            self.assertEqual(b.deadline, old)
            self.assertEqual(b.check(z3.BoolVal(False)).status, 'unknown')
        self.assertEqual(b.deadline, old)

    def test_truncated_search_is_not_an_exhausted_checkpoint(self):
        from girs import agenda
        key = cli._instance_task(instance())
        with tempfile.TemporaryDirectory() as d:
            lim = discover.Limits().identity()
            dom = agenda.domain(lim, vars(synth.SynthLimits()))
            for reason in agenda.REASONS:
                a = agenda.Agenda(d, dom, agenda.depth(lim, 1000))
                a.record('single', key, [reason])
                a.close()
                # More of the budget that ended the search opens it.
                deeper = {k: v * 2 for k, v in
                          agenda.depth(lim, 1000).items()}
                b = agenda.Agenda(d, dom, deeper)
                self.assertEqual(b.pending('single', key), agenda.RETRY,
                                 reason)
                self.assertEqual(b.row('single', key)['state'], 'partial')
                b.close()
            a = agenda.Agenda(d, dom, agenda.depth(lim, 1000))
            a.record('single', key)
            a.close()
            b = agenda.Agenda(d, dom, agenda.depth(lim, 1000))
            self.assertIsNone(b.pending('single', key))
            b.close()

    def test_scalar_checkpoint_cannot_exhaust_a_new_vector_instance(self):
        vector_inst = instance()
        vector_inst.lifted = True
        self.assertNotEqual(cli._instance_task(instance()),
                            cli._instance_task(vector_inst))


class PipelineTest(unittest.TestCase):
    def test_changed_direct_input_invalidates_stages_without_manifest_edit(self):
        with tempfile.TemporaryDirectory() as d:
            src = Path(d) / 'input.ll'
            src.write_text('first input')
            r = mine.Run.__new__(mine.Run)
            r.dir = d
            r.cfg = copy.deepcopy(mine.DEFAULTS)
            r.cfg['manifests'] = {'discovery': 'unchanged manifest'}
            r.manifest = lambda role: [str(src)]
            r._done = lambda stage: 'unchanged'
            r.inputs_identity = lambda: {'manifests': {'discovery': 'unchanged'}}
            r.candidate_llc = lambda: str(src)
            before = [fn() for fn in (r.inputs_extract, r.inputs_measure,
                                      r.inputs_freeze, r.inputs_heldout)]
            src.write_text('changed input')
            after = [fn() for fn in (r.inputs_extract, r.inputs_measure,
                                     r.inputs_freeze, r.inputs_heldout)]
            self.assertTrue(all(a != b for a, b in zip(before, after)))

    def test_budget_limited_discovery_runs_again_on_resume(self):
        with tempfile.TemporaryDirectory() as d:
            r = mine.Run.__new__(mine.Run)
            r.dir = d
            r.state_path = str(Path(d) / 'state.json')
            r.state = {'stages': {}}
            r.log = lambda _: None
            r.inputs_discover = lambda: {'same': 'budget'}
            r.stage_discover = mock.Mock(return_value={'incomplete': True})
            with mock.patch.object(mine, 'STAGES', ('discover',)):
                r.run()
                self.assertEqual(r.state['stages']['discover']['status'], 'pending')
                r.run()
            self.assertEqual(r.stage_discover.call_count, 2)

    def test_mir_cost_counts_vectors_flags_and_multiple_results(self):
        mir = ('name: f\n'
               '  %0:_(<2 x s32>) = G_ADD %1, %2\n'
               '  %3:_(f32) = nofpexcept G_STRICT_FADD %4, %5\n'
               '  %6:_(s32), %7:_(s1) = G_UADDO %8, %9\n')
        self.assertEqual(select.count(mir), {'f': 3})

    def test_novelty_runs_identical_pipeline_with_pinned_rules(self):
        r = library()['rules'][0]
        rid = r['id']
        calls = []
        def run(llc, target, text, synth=False, disabled=()):
            calls.append((synth, set(disabled)))
            return text
        with mock.patch.object(select.measure, 'run_combiner', side_effect=run):
            select.novelty('llc', targets.get('AMDGPU'), [r], ['old'],
                           {'old': ['old_record'], rid: emit.record_names(r),
                            'other': ['other_record']})
        self.assertEqual(len(calls), 2)
        self.assertTrue(all(s for s, _ in calls))
        self.assertTrue(all('old_record' not in off for _, off in calls))
        self.assertIn('other_record', calls[1][1])
        self.assertTrue(set(emit.record_names(r)) <= calls[0][1])

    def test_enforcement_never_ablates_pinned_rules(self):
        names = {'old': ['old_record'], 'new': ['new_record']}
        calls = []
        def compile_ll(llc, target, path, **kw):
            calls.append(kw['disabled'])
            self.assertNotIn('old_record', kw['disabled'])
            return {'rc': 0, 'insns': 11 if 'new_record' not in kw['disabled']
                    else 10, 'passed': {'old': 1, 'new': 1}}
        with mock.patch.object(select.measure, 'compile_ll', side_effect=compile_ll):
            final, dropped, cur, unexplained = select.enforce(
                'llc', targets.get('AMDGPU'), ['a'],
                {'a': {'rc': 0, 'insns': 10}}, names, set(names), 1,
                log=lambda _: None, pinned=['old'])
        self.assertEqual(final, {'old'})
        self.assertEqual(set(dropped), {'new'})
        self.assertEqual(cur['a']['insns'], 10)
        self.assertEqual(unexplained, {})

    def test_measurement_cache_rechecks_inputs_and_partial_identity(self):
        with tempfile.TemporaryDirectory() as d:
            r = mine.Run.__new__(mine.Run)
            r.cfg = {'jobs': 1}
            r.target = targets.get('AMDGPU')
            compiler, source, out = [str(Path(d) / n) for n in ('llc', 'a.ll', 'out')]
            Path(compiler).write_text('compiler1')
            Path(source).write_text('source1')
            Path(out + '.part').write_text(json.dumps([source, {'rc': 0, 'insns': 99}]) + '\n')
            with mock.patch.object(mine.measure, 'compile_ll',
                                   return_value={'rc': 0, 'insns': 1}) as comp:
                self.assertEqual(r._compile_many(compiler, [source], out)[source]['insns'], 1)
                r._compile_many(compiler, [source], out)
                self.assertEqual(comp.call_count, 1)
                Path(source).write_text('source2')
                r._compile_many(compiler, [source], out)
                Path(compiler).write_text('compiler2')
                r._compile_many(compiler, [source], out)
                r._compile_many(compiler, [source], out, synth=True, disabled=['delta'])
                self.assertEqual(comp.call_count, 4)

    def test_empty_delta_skips_build_and_evaluation(self):
        with tempfile.TemporaryDirectory() as d:
            r = mine.Run.__new__(mine.Run)
            r.dir = d
            r.state_path = str(Path(d) / 'state.json')
            r.state = {'stages': {}}
            r.log = lambda _: None
            r.delta = lambda: []
            r.inputs_report = lambda: {}
            r.stage_report = lambda: {'status': 'no_new_rules'}
            with mock.patch.object(mine, 'STAGES', (
                    'build', 'measure', 'select', 'verify', 'freeze', 'heldout', 'report')):
                r.run()
            self.assertEqual(r.state['stages']['report']['status'], 'done')
            for n in ('build', 'measure', 'select', 'verify', 'freeze', 'heldout'):
                self.assertEqual(r.state['stages'][n]['status'], 'skipped')

    def test_residual_extraction_after_baseline_on_both_targets(self):
        for name in ('AMDGPU', 'AArch64'):
            t = targets.get(name)
            calls = []
            def run(command, **kw):
                calls.append(command)
                return mock.Mock(returncode=0, stdout=b'mir')
            with tempfile.TemporaryDirectory() as d, \
                    mock.patch.object(cli.subprocess, 'run', side_effect=run):
                cli._extract_one('llc', 'f.ll', d, 'll', t, baseline=True)
            self.assertIn(t.enable_flag, calls[0])
            if name == 'AArch64':
                self.assertIn('-stop-after=' + t.synth_pass, calls[0])
                self.assertIn('-run-pass=gisel-synth-corpus', calls[1])


class ExportTest(unittest.TestCase):
    def setUp(self):
        # (TestCase.enterContext needs Python 3.11.)
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.tmp = tmp.name
        patch = mock.patch.object(targets, 'PROFILE_DIR', self.tmp)
        patch.start()
        self.addCleanup(patch.stop)
        self.run = mine.Run.__new__(mine.Run)
        r = self.run
        r.dir = str(Path(self.tmp) / 'run')
        r.target = targets.get('AMDGPU')
        r.state = {'stages': {'report': {'status': 'done'}}}
        r.roles = lambda group: ['heldout']
        r.source_identity = lambda group=None: {}
        for subdir in ('library/proofs', 'profile', 'eval', 'build', 'frozen-baseline'):
            Path(r.p(subdir)).mkdir(parents=True, exist_ok=True)
        proofs = r.p('library', 'proofs')
        base = library(proofs)
        i = instance()
        i.expr = ('G_XOR', 32, ('var', 0), ('var', 0))
        sy = synth.Synthesizer(smt.Z3Backend(), proof_dir=proofs)
        sy.add(i, ('lit', 32, '0'))
        sy.finalize([i])
        db, delta = known.merge(base, [synth.strip_private(v) for v in sy.rules.values()])
        db['incremental'] = {'delta': delta}
        known.write(db, r.p('library', 'rules.json'))
        self.cli = types.SimpleNamespace(
            DEFAULT_DB=str(Path(self.tmp) / 'rules.json'),
            DEFAULT_PROOFS=str(Path(self.tmp) / 'proofs'),
            _model_sha=lambda: 'model')
        known.write(base, self.cli.DEFAULT_DB)
        known.copy_proofs(base, self.cli.DEFAULT_PROOFS, [proofs])
        rid = base['rules'][0]['id']
        for t in targets.TARGETS.values():
            profile = known.pin(base, {'rules': {rid: {'selection': 'emitted'}}}, t)
            known.write(profile, t.profile_path)
        initial = mine._load(r.target.profile_path)
        known.write(initial, r.p('frozen-baseline', 'AMDGPU.json'))
        initial['rules'][delta[0]] = {'selection': 'emitted'}
        initial['baseline']['order'].extend(delta)
        profile = known.pin(db, initial, r.target)
        profile['final_check'] = {'files': 1, 'violations': {}}
        known.write(profile, r.p('profile', 'AMDGPU.json'))
        Path(r.candidate_llc()).write_text('compiler')
        known.write({}, r.p('config.json'))
        known.write({
            'library_sha256': mine._sha_file(r.p('library', 'rules.json')),
            'profile_sha256': mine._sha_file(r.p('profile', 'AMDGPU.json')),
            'model_sha256': 'model',
            'compiler_sha256': mine._sha_file(r.candidate_llc()),
            'config_sha256': mine._sha_file(r.p('config.json')),
            'source_files': {}}, r.p('frozen.json'))
        self.evaluation = {'final': {'heldout/direct': {
            'compared': 1, 'compile_failures': [], 'fallback_changed': [],
            'files_worse': 0}}}
        known.write(self.evaluation, r.p('eval', 'summary.json'))

    def test_export_preserves_existing_knowledge_and_other_target(self):
        other = Path(targets.get('AArch64').profile_path).read_bytes()
        mine.export(self.run, self.cli, log=lambda _: None)
        db = known.load(self.cli.DEFAULT_DB)
        self.assertEqual(len(db['rules']), 2)
        self.assertEqual(len(known.validate_profile(db, mine._load(
            self.run.target.profile_path), self.run.target)), 2)
        self.assertEqual(Path(targets.get('AArch64').profile_path).read_bytes(), other)

    def test_export_refuses_a_changed_baseline(self):
        p = mine._load(self.run.target.profile_path)
        p['promotion'] = 'another run'
        known.write(p, self.run.target.profile_path)
        with self.assertRaisesRegex(SystemExit, 'target baseline changed'):
            mine.export(self.run, self.cli)
        self.assertEqual(len(known.load(self.cli.DEFAULT_DB)['rules']), 1)

    def test_export_refuses_missing_or_regressing_heldout(self):
        results = [{}] + [{'heldout/direct': dict(
            self.evaluation['final']['heldout/direct'], **change)} for change in (
                {'files_worse': 1}, {'compile_failures': ['a.ll']},
                {'fallback_changed': ['a.ll']}, {'compared': 0})]
        for result in results:
            known.write({'final': result}, self.run.p('eval', 'summary.json'))
            with self.assertRaisesRegex(SystemExit, 'held-out evaluation'):
                mine.export(self.run, self.cli)
        self.assertEqual(len(known.load(self.cli.DEFAULT_DB)['rules']), 1)

    def test_export_refuses_changed_source_content(self):
        self.run.source_identity = lambda group=None: {'heldout': {'a.ll': 'changed'}}
        with self.assertRaisesRegex(SystemExit, 'frozen evaluation artifacts changed'):
            mine.export(self.run, self.cli)


if __name__ == '__main__':
    unittest.main()
