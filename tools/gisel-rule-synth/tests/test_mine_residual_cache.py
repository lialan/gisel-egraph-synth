"""Mine resumes by residual content while compiler measurements stay fresh.

The stage callbacks are fakes: these regressions exercise the real stage
driver, corpus identities, instance keys and agenda without invoking llc or
performing a synthesis search.
"""

import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from girs import agenda, corpus, ir, known, mine, residual  # noqa: E402

spec = importlib.util.spec_from_file_location(
    'mine_residual_cli', ROOT / 'gi-rule-synth.py')
cli = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = cli
spec.loader.exec_module(cli)


def value(reg, **extra):
    return dict(reg=reg, w=32, type='s32', zero='0x0', one='0x0',
                noundef=True, **extra)


def tree(op='G_ADD'):
    return {
        'fn': 'f', 'bb': 5, 'root': '%12', 'interior': 1,
        'inputs': [value('%9', **{'def': 'COPY'}),
                   value('%10', **{'def': 'COPY'})],
        'expr': value('%12', op=op, bb=5, uses=2, flags=[],
                      args=[{'in': 0}, {'in': 1}]),
    }


def renamed(record):
    out = copy.deepcopy(record)
    out.update(fn='new_function', bb=15, root='%112')
    out['expr'].update(bb=15, reg='%112')
    for inp, reg in zip(out['inputs'], ('%109', '%110')):
        inp['reg'] = reg
    return out


def rule(op='G_AND'):
    x = ('var', 0)
    return {
        'id': 'idempotent_' + op,
        'source_json': ir.to_json((op, 32, x, x)),
        'replacement_json': ir.to_json(x), 'vw': [32],
        'disjuncts': [{'pred_json': [], 'width_maps': [[[32, 32]]]}],
        'semantic_status': {'kind': 'verified_refinement'},
        'support': {'occurrences': 1},
        'provenance': {'sources': ['semantic']},
    }


class MineResidualCacheTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        r = self.mine_run = mine.Run.__new__(mine.Run)
        r.dir, r.state_path = str(self.root), str(self.root / 'state.json')
        r.state = {'stages': {
            'baseline': {'status': 'done', 'inputs': 'producer-1'},
            'prepare': {'status': 'done', 'inputs': 'prepared-1'},
        }}
        r.log = lambda _: None
        r.cfg = copy.deepcopy(mine.DEFAULTS)
        r.cfg['joint']['enabled'] = False
        r.cfg['cache_dir'] = str(self.root / 'cache')
        r.cli = types.SimpleNamespace(_model_sha=lambda: 'model',
                                      _generator_sha=lambda: 'generator')
        r.target = types.SimpleNamespace(name=r.cfg['target'])
        r.has_delta = lambda: True
        r.inputs_identity = lambda: {'manifests': {'discovery': 'manifest'}}
        self.sources = [self.write('sources/a.ll', 'source a'),
                        self.write('sources/b.ll', 'source b')]
        r.source_identity = lambda *args: {
            str(p): mine._sha_file(p) for p in self.sources}
        self.write('baseline/llc', 'baseline compiler 1')
        self.write('build/llc', 'candidate compiler 1')
        self.write_json('frozen-baseline/rules.json', {'rules': []})
        self.capture = self.capture_file([tree()])
        self.calls = {}
        for name in ('extract', 'discover', 'measure'):
            call = self.calls[name] = mock.Mock(return_value={})
            setattr(r, 'stage_' + name, call)

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def write_json(self, name, obj):
        return self.write(name, json.dumps(obj))

    def capture_file(self, records, name='a.jsonl', source=0,
                     directory='corpus'):
        path = self.write(directory + '/' + name,
                          ''.join(json.dumps(r) + '\n' for r in records))
        index_path = self.root / directory / 'index.json'
        index = json.loads(index_path.read_text()) if index_path.exists() else {}
        src = str(self.sources[source])
        index[src] = {'source': src, 'pipeline': 'direct', 'out': name}
        self.write_json(directory + '/index.json', index)
        return path

    def discovery_identity(self):
        # The public input dictionaries also contain configuration objects;
        # snapshot them before a test mutates that configuration in place.
        return copy.deepcopy(self.mine_run.inputs_discover())

    def instance(self, record):
        why = []
        inst = corpus.parse_record(record, str(self.capture), why)
        self.assertIsNotNone(inst, why)
        return inst

    def assert_discovery_reruns(self, before):
        self.assertNotEqual(before, self.discovery_identity())
        calls = self.calls['discover'].call_count
        self.mine_run.run(stages=('discover',))
        self.assertEqual(self.calls['discover'].call_count, calls + 1)

    def test_same_capture_skips_discovery_after_compiler_and_producer_change(self):
        r = self.mine_run
        stages = ('extract', 'discover', 'measure')
        before = self.discovery_identity()
        r.run(stages=stages)
        r.run(stages=stages)
        self.assertEqual([self.calls[n].call_count for n in stages], [1, 1, 1])
        r.state['stages']['baseline']['inputs'] = 'producer-2'
        self.write('baseline/llc', 'baseline compiler 2')
        self.write('build/llc', 'candidate compiler 2')
        # Recapture produces the exact same files. Its producer record and
        # compiler bytes must not force the completed discovery to repeat.
        self.assertEqual(before, self.discovery_identity())
        r.run(stages=stages)
        self.assertEqual([self.calls[n].call_count for n in stages], [2, 1, 2])
        self.assertEqual(before, self.discovery_identity())

    def test_replacing_baseline_binary_invalidates_extraction_at_same_stamp(self):
        r = self.mine_run
        before = copy.deepcopy(r.inputs_extract())
        r.run(stages=('extract',))
        self.write('baseline/llc', 'replacement binary at the same path')
        self.assertNotEqual(before, r.inputs_extract())
        r.run(stages=('extract',))
        self.assertEqual(self.calls['extract'].call_count, 2)

    def test_renaming_refreshes_locations_but_reuses_completed_instance(self):
        original = tree()
        renamed_record = renamed(original)
        old = self.instance(original)
        new = self.instance(renamed_record)
        self.assertNotEqual(old.prov, new.prov)
        self.assertNotEqual(old.regs, new.regs)
        self.assertEqual(cli._instance_task(old), cli._instance_task(new))
        pending = []

        def discover():
            record = json.loads(self.capture.read_text())
            key = cli._instance_task(self.instance(record))
            a = agenda.Agenda(self.mine_run.cfg['cache_dir'], 'fixed-search-domain', {})
            try:
                pending.append(a.pending('single', key))
                if pending[-1] is not None:
                    a.record('single', key, result={'targets': []})
                    a.commit()
            finally:
                a.close()
            return {}

        self.calls['discover'].side_effect = discover
        self.mine_run.run(stages=('discover',))
        before = self.discovery_identity()
        semantic = residual.fingerprint([self.capture])
        self.capture_file([renamed_record])
        self.assertEqual(semantic, residual.fingerprint([self.capture]))
        self.assert_discovery_reruns(before)
        self.assertEqual(pending, [agenda.NEW, None])

    def test_shape_and_facts_refresh_discovery_and_instance_identity(self):
        mutations = (
            ('shape', lambda r: r['expr'].update(op='G_XOR')),
            ('known bits', lambda r: r['inputs'][0].update(zero='0xff')),
            ('definedness', lambda r: r['inputs'][0].update(noundef=False)),
            ('flags', lambda r: r['expr'].update(flags=['nuw'])),
        )
        for name, mutate in mutations:
            with self.subTest(change=name):
                original = tree()
                self.capture_file([original])
                self.mine_run.run(stages=('discover',))
                before = self.discovery_identity()
                changed = copy.deepcopy(original)
                mutate(changed)
                self.capture_file([changed])
                self.assertNotEqual(cli._instance_task(self.instance(original)),
                                    cli._instance_task(self.instance(changed)))
                self.assert_discovery_reruns(before)

    def test_instance_key_includes_search_context_beyond_shape(self):
        record = tree()
        record['expr']['args'][0] = value(
            '%11', op='G_XOR', bb=5, uses=1, flags=[],
            args=[{'in': 0}, {'in': 1}])
        original = self.instance(record)
        original.lifted = True
        key = cli._instance_task(original)
        changes = {
            'consts': (3, None),
            'lift_scalars': (0,),
            'sub_facts': {('G_XOR', 32, ('var', 0), ('var', 1)):
                          (0xff, 0, True)},
            'input_types': ('i32', 's32'),
        }
        for name, changed in changes.items():
            with self.subTest(field=name):
                inst = copy.deepcopy(original)
                setattr(inst, name, changed)
                self.assertEqual(inst.key(), original.key())
                self.assertNotEqual(cli._instance_task(inst), key)
        location = copy.deepcopy(original)
        location.regs = ('%109', '%110')
        location.node_regs = ('%111',)
        location.prov = [('other.jsonl', 'new_function', '%112')]
        self.assertEqual(cli._instance_task(location), key)

    def test_swapping_residuals_between_sources_refreshes_the_wrapper(self):
        other = self.capture_file([tree('G_XOR')], 'b.jsonl', source=1)
        self.mine_run.run(stages=('discover',))
        semantic = residual.fingerprint([self.capture, other])
        before = self.discovery_identity()
        a, b = self.capture.read_text(), other.read_text()
        self.capture.write_text(b)
        other.write_text(a)
        self.assertEqual(semantic, residual.fingerprint([self.capture, other]))
        self.assert_discovery_reruns(before)
        # An index can change the source association without changing any
        # capture bytes. That must refresh provenance as well.
        before = self.discovery_identity()
        path = self.root / 'corpus' / 'index.json'
        index = json.loads(path.read_text())
        a, b = (index[str(src)] for src in self.sources)
        a['out'], b['out'] = b['out'], a['out']
        path.write_text(json.dumps(index))
        self.assert_discovery_reruns(before)

    def test_legality_and_source_changes_refresh_discovery(self):
        self.write_json('corpus/legality.json', {'G_ADD': 'legal'})
        self.mine_run.run(stages=('discover',))
        before = self.discovery_identity()
        self.write_json('corpus/legality.json', {'G_ADD': 'lower'})
        self.assert_discovery_reruns(before)
        before = self.discovery_identity()
        self.sources[0].write_text('changed source with identical residual MIR')
        self.assert_discovery_reruns(before)

    def test_hybrid_search_parameters_refresh_discovery(self):
        self.mine_run.cfg['mode'] = 'hybrid'
        self.mine_run.run(stages=('discover',))
        for name, value in (('compose_steps', 4), ('compose_axioms', True),
                            ('egraph_max_cost', 9)):
            with self.subTest(parameter=name):
                before = self.discovery_identity()
                self.mine_run.cfg['hybrid'][name] = value
                self.assert_discovery_reruns(before)

    def test_joint_and_hybrid_capture_changes_refresh_discovery(self):
        self.mine_run.cfg['mode'] = 'hybrid'
        self.mine_run.cfg['joint']['enabled'] = True
        directories = ('joint/corpus', 'corpus-deep', 'egraph')
        for directory in directories:
            self.capture_file([tree()], directory=directory)
        self.mine_run.run(stages=('discover',))
        for directory in directories:
            with self.subTest(capture=directory):
                before = self.discovery_identity()
                self.capture_file([tree('G_XOR')], directory=directory)
                self.assert_discovery_reruns(before)

    def test_learned_revisions_refresh_discovery_without_metadata_churn(self):
        self.mine_run.run(stages=('discover',))
        before = self.discovery_identity()
        db = known.stamp({'rules': [rule()]})
        path = self.write_json('cache/learned.json', db)
        self.assert_discovery_reruns(before)
        before = self.discovery_identity()
        db['rules'][0]['support']['occurrences'] = 90
        db['rules'][0]['provenance']['sources'].append('egraph')
        db['rules'][0]['proofs'] = [{'seconds': 17, 'smt2_file': 'proofs/a.smt2'}]
        db['seconds'] = 23
        path.write_text(json.dumps(db))
        self.assertEqual(before, self.discovery_identity())
        calls = self.calls['discover'].call_count
        self.mine_run.run(stages=('discover',))
        self.assertEqual(self.calls['discover'].call_count, calls)
        db['rules'].append(rule('G_OR'))
        path.write_text(json.dumps(db))
        self.assert_discovery_reruns(before)
        before = self.discovery_identity()
        db['rules'].reverse()
        path.write_text(json.dumps(db))
        self.assertEqual(before, self.discovery_identity())
        # A broader proved width domain is a new reusable revision even if
        # its family ID and the residual corpus have not changed.
        db['rules'][0]['disjuncts'][0]['width_maps'].append([[32, 64]])
        path.write_text(json.dumps(db))
        self.assert_discovery_reruns(before)

    def test_capture_coverage_and_extra_inputs_cannot_be_hidden(self):
        self.mine_run.run(stages=('discover',))
        before = self.discovery_identity()
        path = self.root / 'corpus' / 'index.json'
        index = json.loads(path.read_text())
        src = str(self.sources[1])
        index[src] = {'source': src, 'pipeline': 'direct', 'out': None}
        path.write_text(json.dumps(index))
        self.assert_discovery_reruns(before)
        before = self.discovery_identity()
        # cmd_synth also reads JSONL files not named in the extraction index.
        self.write('corpus/additional.jsonl', json.dumps(tree('G_XOR')) + '\n')
        self.assert_discovery_reruns(before)
        # A published but missing output is an error, not an empty capture.
        index[src]['out'] = 'missing.jsonl'
        path.write_text(json.dumps(index))
        with self.assertRaises(FileNotFoundError):
            self.mine_run.inputs_discover()


if __name__ == '__main__':
    unittest.main()
