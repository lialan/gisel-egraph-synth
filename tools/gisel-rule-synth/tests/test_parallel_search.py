"""Process scheduling, proof retry isolation and semantic result parity."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import types
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import z3
from girs import corpus, discover, emit, known, parallel, smt, synth
from test_sibling import IN, SUB, ULT, inp, node, rec


def queue_probe(task, slow=False, budget=0):
    _, idx = task
    start = time.monotonic()
    if idx == 'failure':
        raise RuntimeError('worker failed')
    time.sleep(0.25 if slow else 0.06 if idx == 0 else 0.005)
    return {'index': idx, 'lane': 'slow' if slow else 'fast',
            'start': start, 'end': time.monotonic(),
            'retry': not slow and idx % 2 == 0, 'deadline': False,
            'enumeration': {}, 'metrics': {'tasks': 1}}


def options(directory, jobs=1):
    return types.SimpleNamespace(
        cache='', proofs=str(Path(directory) / 'proofs'), timeout_ms=100,
        search_jobs=jobs, slow_jobs=1, search_batch=2, regions=True,
        slow_timeout_ms=1000, slow_budget_s=2, slow_total_s=4)


class QueueTest(unittest.TestCase):
    def run_queue(self, jobs, items):
        with tempfile.TemporaryDirectory() as d:
            with parallel.Session(options(d, jobs)) as session:
                session.configure(discover.Limits(), synth.SynthLimits(),
                                  known.stamp({'rules': []}), False, None)
                with mock.patch.object(parallel, '_execute', queue_probe):
                    result = session.map('probe', items)
                return result, session.metrics

    def test_stable_admission_and_separate_slow_lane(self):
        one, a = self.run_queue(1, range(6))
        many, b = self.run_queue(3, range(6))
        shape = lambda rows: [(r['index'], r['lane']) for r in rows]
        self.assertEqual(shape(one), shape(many))
        self.assertEqual(shape(one), [(0, 'slow'), (1, 'fast'), (2, 'slow'),
                                     (3, 'fast'), (4, 'fast'), (5, 'fast')])
        self.assertEqual(a['slow_admitted'], 2)
        self.assertEqual(b['slow_not_admitted'], 1)
        self.assertTrue(a['incomplete'])
        # Even with one fast process, later cheap work finishes while the
        # first slow proof is still running in a different process.
        self.assertLess(one[3]['end'], one[0]['end'])

    def test_worker_failure_propagates(self):
        with self.assertRaisesRegex(RuntimeError, 'worker failed'):
            self.run_queue(2, [1, 'failure'])

    def test_expired_global_deadline_submits_no_work(self):
        with tempfile.TemporaryDirectory() as d:
            with parallel.Session(options(d, 2)) as session:
                session.configure(discover.Limits(), synth.SynthLimits(),
                                  known.stamp({'rules': []}), False,
                                  time.monotonic() - 1)
                self.assertEqual(session.map('discover', [[None]]), [])
                self.assertTrue(session.metrics['incomplete'])
                self.assertEqual(session.metrics['stages']['discover']
                                 ['returned_tasks'], 0)

    def test_family_collision_is_not_silently_dropped(self):
        sy = synth.Synthesizer(smt.Z3Backend())
        sy.rules['duplicate'] = {}
        with self.assertRaisesRegex(ValueError, 'partition collision'):
            parallel.merge_state(sy, {'rules': {'duplicate': {}}})


class AttemptTest(unittest.TestCase):
    def test_unknown_is_an_attempt_and_larger_budget_retries(self):
        with tempfile.TemporaryDirectory() as d:
            cfg = {'timeout_ms': 100, 'deadline': None, 'cache': d + '/proofs',
                   'attempts': d + '/attempts', 'semantics': 'test'}
            b = parallel.TaskBackend(cfg, False, 0)
            try:
                f = z3.Bool('pending')
                with mock.patch.object(b, '_check', return_value=smt.Result('unknown')) as check:
                    self.assertEqual(b.check(f).status, 'unknown')
                    self.assertEqual(b.check(f).status, 'unknown')
                    self.assertEqual(check.call_count, 1)
                self.assertEqual(b.history.stored, 0)
                b.timeout_ms = 1000
                with mock.patch.object(b, '_check', return_value=smt.Result('sat')) as check:
                    self.assertEqual(b.check(f).status, 'sat')
                    self.assertEqual(check.call_count, 1)
                self.assertFalse(b.pending)
                self.assertEqual(b.history.stored, 1)
                self.assertEqual(b.calls, 3)
            finally:
                b.close()

    def test_slow_replay_retries_unknown_later_widths(self):
        # A valid first width can hide UNKNOWN at later widths from the
        # legacy inline retry hook. The whole slow task needs the long limit.
        with tempfile.TemporaryDirectory() as d:
            with parallel.Session(options(d)) as session:
                session.configure(discover.Limits(), synth.SynthLimits(),
                                  known.stamp({'rules': []}), False, None)
                inst = corpus.parse_record(records()[0])
                task = ('generalize', [((0, False, 0), inst, ('var', 0), None)])
                original = smt.Z3Backend._check

                def limited(b, formula, want_model_of=None):
                    if b.timeout_ms < 1000 and b.calls > 1:
                        return smt.Result('unknown')
                    return original(b, formula, want_model_of)

                with mock.patch.object(parallel, '_CONFIG', session.config), \
                        mock.patch.object(smt.Z3Backend, '_check', limited):
                    fast = parallel._execute(task)
                    slow = parallel._execute(task, True, 2)
                self.assertTrue(fast['retry'])
                self.assertFalse(slow['retry'])
                a = next(iter(fast['rules'].values()))
                b = next(iter(slow['rules'].values()))
                self.assertEqual(a['id'], b['id'])
                self.assertGreater(len(b['disjuncts'][0]['width_maps']),
                                   len(a['disjuncts'][0]['width_maps']))

    def test_deadline_exhaustion_does_not_poison_normal_budget(self):
        with tempfile.TemporaryDirectory() as d:
            cfg = {'timeout_ms': 100, 'deadline': time.monotonic() - 1,
                   'cache': d + '/proofs', 'attempts': d + '/attempts',
                   'semantics': 'test'}
            b = parallel.TaskBackend(cfg, False, 0)
            try:
                f = z3.BoolVal(False)
                self.assertEqual(b.check(f).status, 'unknown')
                b.deadline = None
                self.assertEqual(b.check(f).status, 'unsat')
                self.assertFalse(b.pending)
            finally:
                b.close()


def records():
    out = []
    for w in (8, 16, 32, 64):
        for op in ('G_AND', 'G_OR', 'G_XOR', 'G_SUB'):
            out.append(rec(node(op, w, '%r', [IN(0), IN(0)]),
                           [inp('%x', w)], fn=op + str(w)))
    # Multiple occurrences must merge support without adding duplicate rules.
    out.append(dict(out[0], fn='another_use'))
    out += [dict(SUB, straight_line=[0, 1]),
            dict(ULT, bb=1, straight_line=[0, 1])]
    add = node('G_ADD', 32, '%sum', [IN(0), IN(1)], uses=2, bb=0)
    joint = rec(node('G_ICMP', 1, '%carry', [add, IN(0)], pred='ult', bb=1),
                [inp('%x', 32), inp('%y', 32)], bb=1, fn='joint')
    out.append(dict(joint, straight_line=[0, 1], interior=2))
    x = dict(inp('%fp', 32), type='f32')
    out.append(rec(node('G_FNEG', 32, '%f', [
        node('G_FNEG', 32, '%n', [IN(0)], type='f32')], type='f32'),
        [x], fn='fp_negate_twice'))
    out.append(rec(node('G_AND', 32, '%v', [IN(0), IN(0)],
                        type='<2 x s32>', lanes=2),
                   [dict(inp('%x', 32), type='<2 x s32>', lanes=2)], fn='vector'))
    build = node('G_BUILD_VECTOR', 32, '%built', [IN(0), IN(1)],
                 type='<2 x s32>', lanes=2)
    out.append(rec(node('G_EXTRACT_VECTOR_ELT', 32, '%elt', [build, IN(2)]),
                   [inp('%x', 32), inp('%y', 32),
                    dict(inp('%idx', 32), const='0x0', zero='0xffffffff')],
                   fn='vector_extract'))
    return out


class CLITest(unittest.TestCase):
    def test_cold_serial_parallel_and_warm_cache_agree(self):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            source = d / 'corpus.jsonl'
            source.write_text(''.join(json.dumps(r) + '\n' for r in records()))
            results = []
            for name, jobs, cache in [('one', 1, ''), ('many', 3, str(d/'cache')),
                                      ('warm', 2, str(d/'cache')),
                                      ('slow', 3, ''), ('default', None, '')]:
                out = d / (name + '.json')
                workers = [] if jobs is None else ['--search-jobs', str(jobs)]
                retry = ['--timeout-ms', '0', '--slow-timeout-ms', '10000',
                         '--slow-budget-s', '10', '--slow-total-s', '1000'] \
                    if name == 'slow' else []
                p = subprocess.run([
                    sys.executable, str(ROOT/'gi-rule-synth.py'), 'synth',
                    str(source), *workers, '--search-batch', '2',
                    '--known', '', '--cache', cache, '--refresh-search',
                    '--grammar', 'registry', '--regions', '--siblings',
                    '-o', str(out), '--proofs', str(d/(name+'-proofs')), *retry],
                    text=True, capture_output=True, timeout=120)
                self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
                db = json.loads(out.read_text())
                st = json.loads(out.with_suffix('.stats.json').read_text())
                self.assertFalse(st['parallel']['incomplete'])
                self.assertEqual(st['parallel']['search_jobs'],
                                 16 if jobs is None else jobs)
                if name == 'slow':
                    self.assertGreater(st['parallel']['slow_admitted'], 0)
                self.assertGreater(st['discovery']['vector_instances'], 0)
                self.assertTrue(any('G_FNEG' in r['source']
                                    for r in db['rules']))
                results.append(db)
            # Compare all rule contents, support, guards and proof hashes,
            # not just the number or names of rules.
            self.assertEqual(results[0]['rules'], results[1]['rules'])
            self.assertEqual(results[0]['rules'], results[3]['rules'])
            self.assertEqual(results[0]['rules'], results[4]['rules'])
            # A learned catalog can retain the first equivalent revision;
            # compare semantic revisions and emitted code for a warm run.
            self.assertEqual([known.revision(r) for r in results[0]['rules']],
                             [known.revision(r) for r in results[2]['rules']])
            for db in results[1:]:
                self.assertEqual(emit.emit(results[0], {}, True)[:2],
                                 emit.emit(db, {}, True)[:2])
            self.assertTrue(any(r.get('region') for r in results[0]['rules']))


if __name__ == '__main__':
    unittest.main()
