"""The joint search as tasks of the agenda (girs/joint_tasks.py): runs that
stop and continue, budgets that reopen only what they blocked, the order
of publication and the independence of the number of processes."""

import os
import sqlite3
import sys
import json
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
sys.path.insert(0, os.path.dirname(__file__))

from girs import joint  # noqa: E402
from girs import joint_tasks  # noqa: E402
from test_joint import dsq, helper_region  # noqa: E402


def instances(*wins):
    out = {}
    for w in wins:
        key, c = joint.canonical(w)
        out[key] = (c, list(w.prov))
    return out


def limits(**kw):
    # No time budget ends a search here: the results are deterministic.
    # A few helpers keep the tests short (the helpers come cheapest first).
    base = dict(time_s=600, cost_slack=0, semantic_variants=3,
                max_helpers=16)
    base.update(kw)
    return joint.Limits(**base)


class JointTasksTest(unittest.TestCase):

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.cache = os.path.join(self.tmp.name, 'cache')
        self.inst = instances(dsq(), helper_region())

    def tearDown(self):
        self.tmp.cleanup()

    def run_tasks(self, lim, **kw):
        return joint_tasks.run(self.inst, lim, cache=self.cache, **kw)

    def test_a_stopped_run_continues(self):
        """A run that searched one window; the next one searches the other
        window only, and keeps the rules of the first; a third one searches
        nothing and returns the same rules."""
        lim = limits()
        r1, rec1, st1 = self.run_tasks(lim, max_tasks=1)
        self.assertEqual(st1['searched_in_this_run'], 1)
        self.assertEqual(st1['queue']['not_searched'], 1)
        r2, rec2, st2 = self.run_tasks(lim)
        self.assertEqual(st2['searched_in_this_run'], 1)
        self.assertTrue({r['id'] for r in r1} <= {r['id'] for r in r2})
        r3, rec3, st3 = self.run_tasks(lim)
        self.assertEqual(st3['searched_in_this_run'], 0)
        self.assertEqual(sorted(r['id'] for r in r3),
                         sorted(r['id'] for r in r2))
        self.assertEqual(st3['metrics'], {})

    def test_a_budget_reopens_only_what_it_blocked(self):
        """Banks of a few terms: the windows are partial for 'terms'. The
        same budgets do not search them again; more terms do, as a search
        (not only proofs). The domain is the same: the rules stay."""
        small = limits(max_terms=60)
        r1, rec1, st1 = self.run_tasks(small)
        blocked = {r['key'] for r in rec1 if 'terms' in r['reasons']}
        self.assertTrue(blocked)
        # Only a window that its proofs left partial is taken again.
        again = {r['key'] for r in rec1
                 if set(r['reasons']) & {'proofs', 'time', 'unknown'}}
        _, rec2, st2 = self.run_tasks(small)
        self.assertEqual({r['key'] for r in rec2 if 'mode' in r}, again)
        r3, rec3, st3 = self.run_tasks(limits())
        self.assertEqual(st3['domain'], st1['domain'])
        modes = {r['key']: r.get('mode') for r in rec3}
        self.assertTrue(all(modes[k] == 'full' for k in blocked))
        self.assertTrue({r['id'] for r in r1} <= {r['id'] for r in r3})

    def test_proofs_continue_in_later_runs(self):
        """One proof per run: each run proves the next candidates of the
        windows (without searching them again) until the quota is full.
        (All helpers: the shared helper window then has two
        implementations.)"""
        lim = limits(max_proofs=1, semantic_variants=2, max_helpers=256)
        r1, rec1, st1 = self.run_tasks(lim)
        self.assertIn('proofs', st1['reasons'])
        r2, rec2, st2 = self.run_tasks(lim)
        modes = {r['mode'] for r in rec2 if 'mode' in r}
        self.assertEqual(st2['searched_in_this_run'],
                         st1['reasons']['proofs'])
        self.assertTrue(modes <= {'prove', 'full'})
        self.assertIn('prove', modes)
        self.assertGreater(len(r2), len(r1))

    def test_rules_are_published_before_the_task(self):
        """The second publication of rules fails: the tasks committed
        before it have their rules in the store, and the task whose rule
        failed has no row (a later run searches it again)."""
        lim = limits()
        real = joint_tasks.Store.put
        calls = [0]

        def put(store, rule):
            calls[0] += 1
            if calls[0] == 2:
                raise OSError('disk full')
            return real(store, rule)
        with mock.patch.object(joint_tasks.Store, 'put', put):
            with self.assertRaises(OSError):
                self.run_tasks(lim)
        db = sqlite3.connect(os.path.join(self.cache, 'agenda.sqlite3'))
        rows = db.execute('SELECT key, result FROM tasks').fetchall()
        dom = joint_tasks.domain(lim)
        store = joint_tasks.Store(os.path.join(self.cache, 'joint', dom[:16]))
        for key, result in rows:
            for rid, state in json.loads(result)['decided'].items():
                if state == 'verified':
                    self.assertIsNotNone(store.get(rid), rid)
        self.assertLess(len(rows), len(self.inst))
        _, _, st = self.run_tasks(lim)
        self.assertEqual(st['queue']['complete'] + st['queue']['open'] +
                         st['queue']['closed_at_this_depth'], len(self.inst))

    def test_processes_do_not_change_the_rules(self):
        lim = limits()
        a = joint_tasks.run(self.inst, lim, jobs=1)
        b = joint_tasks.run(self.inst, lim, jobs=2)
        self.assertEqual([r['id'] for r in a[0]], [r['id'] for r in b[0]])
        strip = lambda rs: [(r['key'], r['status'], r['candidate_states'],
                             r['verified']) for r in rs]  # noqa: E731
        self.assertEqual(strip(a[1]), strip(b[1]))

    def test_identity_of_the_rows(self):
        """The cost policy and the window limits make another domain; the
        budgets are the depth of one domain."""
        d = joint_tasks.domain(limits())
        self.assertNotEqual(d, joint_tasks.domain(limits(cost_slack=1)))
        self.assertNotEqual(d, joint_tasks.domain(limits(max_window=4)))
        self.assertEqual(d, joint_tasks.domain(limits(max_proofs=12,
                                                      time_s=5,
                                                      semantic_variants=8)))


if __name__ == '__main__':
    unittest.main()
