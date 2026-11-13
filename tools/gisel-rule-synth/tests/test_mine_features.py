"""Scope, split isolation and first-run multi-output scheduling regressions."""
import copy
import json
from pathlib import Path
import tempfile
import time
import types
import unittest
from unittest import mock

from test_agenda import ADD_CMP, SIMPLE, cli
from test_sibling import SUB, ULT
from girs import discover, known, mine, parallel, targets


class MineFeaturesTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def search(self, records, name='run', **kwargs):
        d = self.root / name
        d.mkdir(exist_ok=True)
        src = d / 'corpus.jsonl'
        src.write_text(''.join(json.dumps(r) + '\n' for r in records))
        options = dict(corpus=[str(src)], o=str(d / 'rules.json'),
                       proofs=str(d / 'proofs'), cache=str(self.root / 'cache'),
                       known='', search_jobs=0, grammar='registry',
                       max_rhs_cost=1, max_terms=5000, max_evals=100000)
        options.update(kwargs)
        cli.cmd_synth(cli.default_args('synth', **options))
        return (json.loads((d / 'rules.json').read_text()),
                json.loads((d / 'rules.stats.json').read_text()))

    def test_defaults_and_explicit_opt_out(self):
        args = cli.default_args('synth', corpus=[])
        self.assertTrue(args.regions and args.siblings)
        self.assertTrue(mine.DEFAULTS['search']['regions'])
        self.assertTrue(mine.DEFAULTS['search']['siblings'])
        args = cli.build_parser().parse_args(['synth', '--no-regions', '--no-siblings', 'x'])
        self.assertFalse(args.regions or args.siblings)

    def test_vector_only_does_not_search_scalar_siblings(self):
        vector = copy.deepcopy(SUB)
        vector['root'] = vector['expr']['reg'] = '%vector'
        vector['expr'].update(op='G_BUILD_VECTOR', lanes=2, type='<2 x s32>')
        db, stats = self.search([SUB, ULT, vector], only_vectors=True)
        self.assertEqual(stats['siblings']['pairs'], 0)
        self.assertGreater(stats['siblings']['corpus']['outside_vector_scope'], 0)
        self.assertFalse(db['rules'])

    def test_semantics_only_reuses_hybrid_knowledge_with_its_provenance(self):
        db, _ = self.search(SIMPLE[:1], regions=False, siblings=False)
        self.assertTrue(db['rules'])
        cached = self.root / 'cache' / 'learned.json'
        learned = json.loads(cached.read_text())
        for rule in learned['rules']:
            rule['provenance']['sources'] = ['egraph']
        cached.write_text(json.dumps(learned))
        r = mine.Run.__new__(mine.Run)
        r.dir = str(self.root / 'mine')
        r.cfg = copy.deepcopy(mine.DEFAULTS)
        r.cfg['joint']['enabled'] = False
        r.cfg['cache_dir'] = str(self.root / 'cache')
        r.cfg['search'].update(search_jobs=0, max_terms=100, max_evals=1000,
                               max_rhs_cost=1, regions=False, siblings=False)
        r.cli, r.target = cli, targets.get('AMDGPU')
        Path(r.p('frozen-baseline')).mkdir(parents=True)
        known.write(known.stamp({'format': db['format'], 'rules': []}),
                    r.p('frozen-baseline', 'rules.json'))
        Path(r.p('corpus')).mkdir()
        Path(r.p('corpus', 'input.jsonl')).write_text(json.dumps(SIMPLE[1]) + '\n')
        r.stage_discover()
        result = r.library()
        reused = set(result['incremental']['reused_from_cache'])
        self.assertTrue(reused)
        self.assertTrue(all(x['provenance']['sources'] == ['egraph']
                            for x in result['rules'] if x['id'] in reused))
        self.assertEqual(result['discovery_mode'], 'semantics-only')

    def manifest_run(self, heldout):
        a = self.root / 'a.ll'
        a.write_text('define i32 @a(i32 %x) { ret i32 %x }\n')
        b = self.root / 'b.ll'
        if heldout == 'alias':
            b.symlink_to(a)
        else:
            b.write_text(a.read_text() if heldout == 'copy' else 'different IR')
        manifests = {}
        for role, src in [('discovery', a), ('heldout', b)]:
            p = self.root / (role + '.txt')
            p.write_text(str(src) + '\n')
            manifests[role] = str(p)
        r = mine.Run.__new__(mine.Run)
        r.cfg = {'manifests': manifests}
        return r

    def test_identical_content_in_different_splits_is_rejected(self):
        r = self.manifest_run('copy')
        with self.assertRaisesRegex(SystemExit, 'overlap.*content'):
            r.validate_manifests()

    def test_path_alias_in_different_splits_is_rejected(self):
        r = self.manifest_run('alias')
        with self.assertRaisesRegex(SystemExit, 'overlap.*path'):
            r.validate_manifests()

    def test_content_change_invalidates_identity_and_detects_leakage(self):
        r = self.manifest_run('distinct')
        r.validate_manifests()
        before = r.source_identity()
        (self.root / 'b.ll').write_text((self.root / 'a.ll').read_text())
        self.assertNotEqual(before, r.source_identity())
        with self.assertRaisesRegex(SystemExit, 'overlap'):
            r.validate_manifests()

    def test_cold_run_reserves_region_work_after_single_deadline(self):
        now = [time.monotonic()]
        real = discover.discover
        calls = []

        def consume(inst, backend, *a, **kw):
            calls.append(backend.deadline)
            if len(calls) > 1:
                now[0] = backend.deadline
            return real(inst, backend, *a, **kw)

        clock = types.SimpleNamespace(monotonic=lambda: now[0], time=time.time)
        with mock.patch.object(cli, 'time', clock), \
                mock.patch.object(discover, 'discover', side_effect=consume):
            db, stats = self.search([ADD_CMP] + SIMPLE, time_budget_s=30, multi_share=.5)
        self.assertGreater(stats['queue']['single']['not_searched'], 0)
        self.assertGreater(stats['queue']['region']['complete'], 0)
        self.assertTrue(any(r.get('region') for r in db['rules']))

    def test_cold_process_run_restores_deadline_before_region_proofs(self):
        now = [time.monotonic()]
        original = parallel.Session.search
        deadlines = []

        def search(session, insts, sy, single=True, alternatives=None):
            if single:
                deadlines.append(session.deadline)
                rows = original(session, insts[:1], sy, single=True,
                                alternatives=alternatives[:1])
                now[0] = session.deadline
                return rows
            deadlines.append(session.deadline)
            return original(session, insts, sy, single, alternatives)

        clock = types.SimpleNamespace(monotonic=lambda: now[0], time=time.time)
        with mock.patch.object(cli, 'time', clock), \
                mock.patch.object(parallel.Session, 'search', search):
            db, stats = self.search([ADD_CMP] + SIMPLE, time_budget_s=30,
                                    multi_share=.5, search_jobs=1)
        self.assertGreater(stats['queue']['single']['not_searched'], 0)
        self.assertGreater(stats['queue']['region']['complete'], 0)
        self.assertTrue(any(r.get('region') for r in db['rules']))


if __name__ == '__main__':
    unittest.main()
