"""Kill the actual coordinator at publication boundaries, then resume it.

The driver patches only its parent process. Search/proof workers use spawn,
the production scheduler, and its default sixteen processes.
"""
import copy
import hashlib
import json
import os
from pathlib import Path
import signal
import sqlite3
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

from test_agenda import ADD_CMP, SIMPLE, DEPTH, ROOT, cli
from girs import agenda, emit, known, parallel
from test_sibling import SUB, ULT


DRIVER = r'''
import importlib.util
import os
from pathlib import Path
import sys
import time

if __name__ == '__main__':
    root, boundary, marker, *args = sys.argv[1:]
    sys.path.insert(0, root)
    from girs import agenda, known, parallel
    spec = importlib.util.spec_from_file_location('recovery_cli',
                                                  Path(root) / 'gi-rule-synth.py')
    cli = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cli)

    def stop():
        Path(marker).write_text('ready')
        while True:
            time.sleep(0.05)

    if boundary == 'finalize':
        parallel.Session.finalize = lambda *a, **k: stop()
    elif boundary in ('before_catalog', 'after_catalog', 'write_failure'):
        original = known.write
        def write(obj, path):
            if str(path).endswith('learned.json'):
                if boundary == 'write_failure':
                    raise OSError('injected catalog write failure')
                if boundary == 'before_catalog':
                    stop()
            original(obj, path)
            if str(path).endswith('learned.json') and boundary == 'after_catalog':
                stop()
        known.write = write
    elif boundary in ('during_commit', 'after_commit'):
        original = agenda.Agenda.commit
        def commit(self):
            n = 0
            def trace(sql):
                nonlocal n
                if sql.startswith('INSERT OR REPLACE INTO tasks'):
                    n += 1
                    if n == 2:
                        stop()
            if boundary == 'during_commit':
                self.db.set_trace_callback(trace)
            original(self)
            if boundary == 'after_commit':
                stop()
        agenda.Agenda.commit = commit
    sys.argv = [str(Path(root) / 'gi-rule-synth.py'), *args]
    cli.main()
'''


@unittest.skipUnless(os.name == 'posix', 'requires POSIX process-group termination')
class RecoveryTest(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name)
        self.driver = self.path / 'driver.py'
        self.driver.write_text(DRIVER)

    def source(self, records, name='corpus'):
        p = self.path / (name + '.jsonl')
        p.write_text(''.join(json.dumps(r) + '\n' for r in records))
        return p

    def run_search(self, source, directory, *options, boundary=None):
        d = self.path / directory
        d.mkdir(exist_ok=True)
        args = ['synth', str(source), '--known', '', '--cache', str(d/'cache'),
                '--proofs', str(d/'proofs'), '-o', str(d/'rules.json'), *options]
        marker = d / 'paused'
        cmd = [sys.executable, str(self.driver), str(ROOT), boundary or '',
               str(marker), *args]
        with (d/'run.log').open('w') as log:
            p = subprocess.Popen(cmd, stdout=log, stderr=log, start_new_session=True)
            try:
                if boundary and boundary != 'write_failure':
                    until = time.monotonic() + 60
                    while not marker.exists() and p.poll() is None and time.monotonic() < until:
                        time.sleep(0.02)
                    self.assertTrue(marker.exists(), (d/'run.log').read_text())
                    os.killpg(p.pid, signal.SIGKILL)
                    self.assertEqual(p.wait(timeout=10), -signal.SIGKILL)
                else:
                    code = p.wait(timeout=90)
                    if boundary == 'write_failure':
                        self.assertNotEqual(code, 0)
                        self.assertIn('injected catalog write failure', (d/'run.log').read_text())
                    else:
                        self.assertEqual(code, 0, (d/'run.log').read_text())
            finally:
                # Also reap spawned workers if an assertion or timeout fails.
                try:
                    os.killpg(p.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                p.wait(timeout=10)
        if boundary:
            return d
        db = json.loads((d/'rules.json').read_text())
        st = json.loads((d/'rules.stats.json').read_text())
        self.assertEqual(st['parallel']['search_jobs'],
                         int(options[options.index('--search-jobs') + 1])
                         if '--search-jobs' in options else 16)
        self.check_proofs(db, d/'proofs')
        self.check_proofs(known.load(d/'cache/learned.json'), d/'cache/verified-proofs')
        return db, st

    def check_proofs(self, db, directory):
        for r in db['rules']:
            proofs = list(r['semantic_status'].get('dnf_proofs', []))
            for d in r['disjuncts'] + r.get('unselected_disjuncts', []):
                proofs += d['proofs']
            for proof in proofs:
                h = proof['smt2_sha256']
                content = (directory / (h + '.smt2')).read_bytes()
                self.assertTrue(hashlib.sha256(content).hexdigest().startswith(h))

    def same_rules(self, a, b):
        self.assertEqual(sorted(known.revision(r) for r in a['rules']),
                         sorted(known.revision(r) for r in b['rules']))
        self.assertEqual(emit.emit(a, {}, True)[:2], emit.emit(b, {}, True)[:2])

    def test_killed_publication_recovers_without_lost_rules(self):
        source = self.source(SIMPLE[:2])
        reference, _ = self.run_search(source, 'reference')
        self.assertEqual(len(reference['rules']), 2)
        for boundary in ('finalize', 'before_catalog', 'after_catalog',
                         'during_commit', 'after_commit', 'write_failure'):
            with self.subTest(boundary=boundary):
                d = self.run_search(source, boundary, boundary=boundary)
                with sqlite3.connect(d/'cache/agenda.sqlite3') as db:
                    count = db.execute('SELECT count(*) FROM tasks').fetchone()[0]
                self.assertEqual(count, 2 if boundary == 'after_commit' else 0)
                recovered, st = self.run_search(source, boundary)
                self.same_rules(reference, recovered)
                self.assertEqual(st['queue']['left'], 0)
                self.assertEqual(st['discovery']['instances'],
                                 0 if boundary == 'after_commit' else 2)
                if boundary == 'after_commit':
                    self.assertEqual(st['solver_calls'], 0)

    def test_capped_parallel_runs_match_one_worker(self):
        source = self.source(SIMPLE)
        full, _ = self.run_search(source, 'one', '--search-jobs', '1')
        for completed in (2, 4, 6):
            db, st = self.run_search(source, 'capped', '--max-instances', '2')
            self.assertEqual(st['discovery']['instances'], 2)
            self.assertEqual(st['queue']['single']['complete'], completed)
        self.same_rules(full, db)
        resumed, st = self.run_search(source, 'capped', '--max-instances', '2')
        self.same_rules(full, resumed)
        self.assertEqual((st['solver_calls'], st['enumeration']['banks'],
                          st['queue']['left']), (0, 0, 0))

    def test_enabling_cross_block_regions_uses_cached_roots(self):
        record = copy.deepcopy(ADD_CMP)
        record['straight_line'] = [0, 1]
        record['bb'] = record['expr']['bb'] = 1
        record['expr']['args'][0]['bb'] = 0
        source = self.source([record])
        flags = ['--grammar', 'registry']
        self.run_search(source, 'resume', *flags)
        resumed, st = self.run_search(source, 'resume', *flags, '--regions')
        self.assertEqual(st['discovery']['instances'], 0)
        self.assertTrue(any(r.get('region') for r in resumed['rules']))
        full, _ = self.run_search(source, 'one', *flags, '--regions', '--search-jobs', '1')
        self.same_rules(full, resumed)
        again, st = self.run_search(source, 'resume', *flags, '--regions')
        self.same_rules(resumed, again)
        self.assertEqual((st['solver_calls'], st['enumeration']['banks'],
                          st['queue']['left']), (0, 0, 0))

    def test_growing_sibling_corpus_keeps_both_phases(self):
        def widen(value):
            if isinstance(value, list):
                return [widen(v) for v in value]
            if isinstance(value, dict):
                return {k: (64 if k == 'w' and v == 32 else
                            'i64' if k == 'type' and v == 'i32' else
                            'wider' if k == 'fn' else widen(v))
                        for k, v in value.items()}
            return value
        source = self.source([SUB, ULT])
        flags = ['--grammar', 'registry']
        self.run_search(source, 'resume', *flags)
        larger = self.source([SUB, ULT, widen(SUB), widen(ULT)], 'larger')
        result, st = self.run_search(larger, 'resume', *flags, '--siblings')
        self.assertGreater(st['discovery']['instances'], 0)
        self.assertTrue(any(r.get('region', {}).get('siblings') for r in result['rules']))
        again, st = self.run_search(larger, 'resume', *flags, '--siblings')
        self.same_rules(result, again)
        self.assertEqual(st['queue']['left'], 0)

    def test_unfinished_final_guard_does_not_complete_its_root(self):
        source = self.source(SIMPLE[:1])
        d = self.path / 'resume'
        d.mkdir()
        def unfinished(session, sy, insts, preserve):
            count = len(sy.rules)
            sy.rules.clear()
            return {'final_guard_unknown': count}
        args = cli.default_args('synth', corpus=[str(source)], known='',
                                cache=str(d/'cache'), proofs=str(d/'proofs'),
                                o=str(d/'rules.json'), timeout_ms=1000)
        with mock.patch.object(parallel.Session, 'finalize', unfinished):
            cli.cmd_synth(args)
        st = json.loads((d/'rules.stats.json').read_text())
        self.assertEqual(st['queue']['single']['complete'], 0)
        self.assertGreater(st['queue']['single']['reasons']['unknown'], 0)
        recovered, st = self.run_search(source, 'resume', '--timeout-ms', '2000')
        self.assertEqual(len(recovered['rules']), 1)
        self.assertEqual(st['queue']['single']['complete'], 1)

    def test_views_enablement_reopens_completed_roots(self):
        from test_views import _input, _node
        record = {'fn': 'fold', 'bb': 0, 'root': '%5',
                  'expr': _node('G_ADD', 32, '%5', [
                      _node('G_ADD', 32, '%4', [{'in': 0}, {'in': 1}]),
                      {'in': 2}]),
                  'inputs': [_input('%0'), _input('%1', const=3),
                             _input('%2', const=5)]}
        source = self.source([record])
        self.run_search(source, 'resume', '--no-views')
        resumed, st = self.run_search(source, 'resume')
        self.assertEqual(st['discovery']['instances'], 1)
        self.assertTrue(any(r['provenance']['discovery'] == 'views-linear+smt'
                            for r in resumed['rules']))
        full, _ = self.run_search(source, 'one', '--search-jobs', '1')
        self.same_rules(full, resumed)
        # Expanding the view domain recognizes its known candidate without
        # generalizing it again, and retains that candidate as a seed.
        replay, st = self.run_search(source, 'resume', '--views-max-proposals', '9')
        self.same_rules(resumed, replay)
        self.assertEqual(st['synthesis']['generalized'], 0)
        again, st = self.run_search(source, 'resume', '--views-max-proposals', '9')
        self.same_rules(resumed, again)
        self.assertEqual((st['solver_calls'], st['queue']['left']), (0, 0))


class TransactionTest(unittest.TestCase):
    def test_close_discards_unpublished_tasks(self):
        with tempfile.TemporaryDirectory() as d:
            a = agenda.Agenda(d, 'domain', DEPTH)
            a.record('single', 'root', result={'targets': []})
            self.assertIsNone(a.pending('single', 'root'))
            a.close()
            b = agenda.Agenda(d, 'domain', DEPTH)
            try:
                self.assertEqual(b.pending('single', 'root'), agenda.NEW)
                self.assertIsNone(b.result('single', 'root'))
            finally:
                b.close()


if __name__ == '__main__':
    unittest.main()
