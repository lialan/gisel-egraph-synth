"""The tasks of the search across runs (girs/agenda.py): a run searches
what was not searched, a known rule is a seed and is not found again, and
the tasks with several outputs have a part of the time of a run."""

import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from girs import agenda, corpus, discover, known, region, smt, synth  # noqa

spec = importlib.util.spec_from_file_location('agenda_cli',
                                              ROOT / 'gi-rule-synth.py')
cli = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = cli
spec.loader.exec_module(cli)

DEPTH = {'max_terms': 100, 'max_evals': 1000, 'max_proofs': 8,
         'max_candidates': 2, 'timeout_ms': 1000}


def V(i):
    return ('var', i)


class AgendaTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)

    def open(self, domain='d', **depth):
        a = agenda.Agenda(self.tmp.name, domain, dict(DEPTH, **depth))
        self.addCleanup(a.close)
        return a

    def publish(self, a, *args, **kwargs):
        a.record(*args, **kwargs)
        a.commit()

    def test_a_complete_task_is_not_searched_again(self):
        a = self.open()
        self.assertEqual(a.pending('single', 'k'), agenda.NEW)
        self.publish(a, 'single', 'k', result={'targets': [[1, []]]})
        # Not again in this run, and not in the next one.
        self.assertIsNone(a.pending('single', 'k'))
        b = self.open()
        self.assertIsNone(b.pending('single', 'k'))
        self.assertEqual(b.result('single', 'k'), {'targets': [[1, []]]})
        # A higher budget does not open it: the search was complete.
        self.assertIsNone(self.open(max_terms=10 ** 6).pending('single',
                                                               'k'))

    def test_another_domain_has_its_own_tasks(self):
        self.publish(self.open(), 'single', 'k')
        self.assertEqual(self.open('other').pending('single', 'k'),
                         agenda.NEW)

    def test_a_limit_opens_a_task_only_when_it_is_higher(self):
        for reason, budget in (('terms', 'max_terms'),
                               ('terms', 'max_evals'),
                               ('candidates', 'max_candidates'),
                               ('unknown', 'timeout_ms')):
            key = reason + budget
            self.publish(self.open(), 'single', key, [reason])
            self.assertIsNone(self.open().pending('single', key), key)
            higher = self.open(**{budget: DEPTH[budget] + 1})
            self.assertEqual(higher.pending('single', key), agenda.RETRY)
            # Another budget is not the limit of this task.
            other = 'max_proofs' if budget != 'max_proofs' else 'max_terms'
            self.assertIsNone(self.open(**{other: 10 ** 9}).pending(
                'single', key), key)

    def test_the_deadline_leaves_a_task_open(self):
        self.publish(self.open(), 'single', 'k', ['time'], progress=3,
                           result={'targets': []})
        b = self.open()
        self.assertEqual(b.pending('single', 'k'), agenda.RETRY)
        self.publish(b, 'single', 'k')
        self.assertIsNone(self.open().pending('single', 'k'))

    def test_the_proof_budget_continues_until_it_makes_no_progress(self):
        # A decided proof is in the proof history: the next search of the
        # task decides other candidates with the same budget.
        self.publish(self.open(), 'single', 'k', ['proofs'], progress=4)
        b = self.open()
        self.assertEqual(b.pending('single', 'k'), agenda.RETRY)
        self.publish(b, 'single', 'k', ['proofs'], progress=7)
        c = self.open()
        self.assertEqual(c.pending('single', 'k'), agenda.RETRY)
        # No more candidates decided: the solver does not decide them.
        self.publish(c, 'single', 'k', ['proofs'], progress=7)
        self.assertIsNone(self.open().pending('single', 'k'))
        self.assertEqual(self.open(max_proofs=9).pending('single', 'k'),
                         agenda.RETRY)
        self.assertEqual(self.open(timeout_ms=2000).pending('single', 'k'),
                         agenda.RETRY)

    def test_new_tasks_first_then_the_least_searched(self):
        a = self.open()
        self.publish(a, 'single', 'twice', ['time'])
        self.publish(a, 'single', 'done')
        b = self.open()
        self.publish(b, 'single', 'twice', ['time'])
        self.publish(b, 'single', 'once', ['time'])
        c = self.open()
        new, retry = c.order('single', ['once', 'x', 'done', 'twice', 'y'],
                             lambda k: k)
        self.assertEqual(new, ['x', 'y'])
        self.assertEqual(retry, ['once', 'twice'])

    def test_reopen_searches_every_task_once(self):
        self.publish(self.open(), 'single', 'k')
        a = agenda.Agenda(self.tmp.name, 'd', DEPTH, reopen=True)
        self.addCleanup(a.close)
        self.assertEqual(a.pending('single', 'k'), agenda.RETRY)
        self.publish(a, 'single', 'k')
        self.assertIsNone(a.pending('single', 'k'))

    def test_summary(self):
        a = self.open()
        self.publish(a, 'single', 'c')
        self.publish(a, 'single', 't', ['time'])
        self.publish(a, 'single', 'b', ['terms', 'unknown'])
        s = a.summary('single', ['c', 't', 'b', 'n', 'n'])
        self.assertEqual(
            {k: s[k] for k in ('tasks', 'complete', 'not_searched', 'open',
                               'closed_at_this_depth',
                               'searched_in_this_run',
                               'completed_in_this_run')},
            {'tasks': 4, 'complete': 1, 'not_searched': 1, 'open': 1,
             'closed_at_this_depth': 1, 'searched_in_this_run': 3,
             'completed_in_this_run': 1})
        self.assertEqual(s['reasons'],
                         {'terms': 1, 'time': 1, 'unknown': 1})

    def test_without_a_directory_the_tasks_are_of_this_process(self):
        a = agenda.Agenda(None, 'd', DEPTH)
        self.publish(a, 'single', 'k')
        self.assertIsNone(a.pending('single', 'k'))
        a.close()
        b = agenda.Agenda(None, 'd', DEPTH)
        self.assertEqual(b.pending('single', 'k'), agenda.NEW)
        b.close()

    def test_domain_and_depth_of_limits(self):
        lim = discover.Limits().identity()
        deeper = discover.Limits(max_terms=7, max_evals=7, max_proofs=7,
                                 max_candidates=7).identity()
        sl = vars(synth.SynthLimits())
        # A budget is the depth of a search, not its domain.
        self.assertEqual(agenda.domain(lim, sl), agenda.domain(deeper, sl))
        self.assertEqual(agenda.depth(deeper, 5), {
            'max_terms': 7, 'max_evals': 7, 'max_proofs': 7,
            'max_candidates': 7, 'timeout_ms': 5})
        for other in (discover.Limits(grammar='registry'),
                      discover.Limits(seed=1), discover.Limits(cost_slack=0)):
            self.assertNotEqual(agenda.domain(lim, sl),
                                agenda.domain(other.identity(), sl))
        self.assertNotEqual(agenda.domain(lim, sl), agenda.domain(
            lim, vars(synth.SynthLimits(max_atoms=3))))


def inst(expr, vw, uses=(), facts=None):
    n = len(vw)
    return corpus.Instance(expr, vw, facts or [(0, 0)] * n, [None] * n,
                           list(uses), [], [('f.ll', 'fn', '%0')])


def library(i, tgt):
    sy = synth.Synthesizer(smt.Z3Backend())
    rid = sy.add(i, tgt)
    sy.finalize([i])
    return known.stamp({'format': 'gi-rule-synth-library-v2',
                        'rules': [synth.strip_private(sy.rules[rid])]}), rid


class KnownCandidateTest(unittest.TestCase):
    """A candidate that a known rule covers is a result of the search."""

    def setUp(self):
        self.be = smt.Z3Backend()
        self.i = inst(('G_AND', 32, V(0), V(0)), (32,))
        self.db, self.rid = library(self.i, V(0))

    def ctx(self, **kw):
        lim = discover.Limits(**kw)
        ctx = discover.Context(lim)
        ctx.known = known.Index(self.db)
        return lim, ctx

    def test_it_is_in_the_result_with_the_id_of_its_rule(self):
        lim, ctx = self.ctx()
        cands, st = discover.discover(self.i, self.be, lim, ctx)
        self.assertEqual([(c['tgt'], c.get('known')) for c in cands],
                         [(V(0), self.rid)])
        self.assertNotIn('proof', cands[0])
        self.assertEqual((st['known_candidates'], st['smt_checks']), (1, 0))
        self.assertEqual((st['stop'], st['limits']), ('complete', []))

    def test_the_result_does_not_depend_on_what_is_known(self):
        # x & x: the candidates of a search without knowledge and of a
        # search that knows the rule are the same replacements.
        lim, ctx = self.ctx()
        with_k, _ = discover.discover(self.i, self.be, lim, ctx)
        without, _ = discover.discover(self.i, self.be, discover.Limits())
        self.assertEqual([c['tgt'] for c in with_k],
                         [c['tgt'] for c in without])

    def test_a_rule_that_needs_one_use_is_a_seed_only(self):
        # The value below the root has another user: the rule does not
        # apply, but a rule with several outputs can stand on it.
        src = ('G_AND', 32, ('G_OR', 32, V(0), V(0)), V(0))
        one = inst(src, (32,), uses=[1])
        db, rid = library(one, V(0))
        db['rules'][0]['needs_one_use'] = True
        idx = known.Index(known.stamp(db))
        shared = inst(src, (32,), uses=[2])
        self.assertEqual(idx.covers(one, V(0)), rid)
        self.assertIsNone(idx.covers(shared, V(0)))
        self.assertEqual(idx.covers(shared, V(0), count=False, seed=True),
                         rid)
        self.assertEqual(idx.hits, 1)

    def test_it_counts_for_the_limit_of_candidates(self):
        lim, ctx = self.ctx(max_candidates=1)
        st = discover.new_stats()
        out = discover.prove_candidates(
            self.i, [V(0), ('G_OR', 32, V(0), V(0))], self.be, lim, ctx, st)
        self.assertEqual([c['tgt'] for c in out], [V(0)])
        self.assertEqual((st['stop'], st['not_tried'], st['smt_checks']),
                         ('candidate_limit', 1, 0))

    def test_it_makes_a_worse_candidate_pointless(self):
        lim, ctx = self.ctx()
        st = discover.new_stats()
        envs = discover.instance_envs(self.i, lim, ctx)
        out = discover.prove_candidates(
            self.i, [V(0), ('G_OR', 32, V(0), V(0))], self.be, lim, ctx, st,
            envs)
        self.assertEqual([c['tgt'] for c in out], [V(0)])
        self.assertEqual((st['dominated'], st['smt_checks']), (1, 0))

    def test_every_limit_of_a_search_is_recorded(self):
        class Unknown:
            calls = 0

            def check(self, formula, want_model_of=None):
                self.calls += 1
                return smt.Result('unknown')
        i = inst(('G_AND', 32, V(0), V(0)), (32,))
        _, st = discover.discover(i, Unknown(), discover.Limits())
        self.assertEqual((st['stop'], st['limits']),
                         ('smt_unknown', ['unknown']))
        _, st = discover.discover(i, self.be, discover.Limits(max_proofs=0))
        self.assertEqual((st['stop'], st['limits']),
                         ('proof_budget', ['proofs']))
        lim = discover.Limits(max_terms=3)
        _, st = discover.discover(
            inst(('G_ADD', 32, ('G_SUB', 32, V(0), V(1)), V(1)), (32, 32)),
            self.be, lim)
        self.assertEqual(st['stop'], 'bank_truncated')
        self.assertIn('terms', st['limits'])


def node(op, w, reg, args, uses=1, **kw):
    return dict({'op': op, 'w': w, 'reg': reg, 'zero': '0x0', 'one': '0x0',
                 'uses': uses, 'flags': [], 'args': args}, **kw)


def record(expr, widths, fn='f', interior=1):
    return {'fn': fn, 'bb': 0, 'root': expr['reg'], 'interior': interior,
            'expr': expr,
            'inputs': [{'reg': '%%%d' % k, 'w': w, 'zero': '0x0',
                        'one': '0x0', 'def': 'COPY'}
                       for k, w in enumerate(widths)]}


IN0, IN1 = {'in': 0}, {'in': 1}
# x + y < x, and the sum has another user: G_UADDO gives both.
ADD_CMP = record(node('G_ICMP', 1, '%3', [
    node('G_ADD', 32, '%2', [IN0, IN1], uses=2), IN0], pred='ult'),
    (32, 32), interior=2)
SIMPLE = [record(node(op, 32, '%2', [IN0, IN0]), (32,), fn=op)
          for op in ('G_AND', 'G_OR', 'G_XOR', 'G_SUB', 'G_UMIN', 'G_UMAX')]


def extract(reg, index):
    """Lane ``index`` of the vector %v, in one block with the others."""
    return {'fn': 'v', 'bb': 0, 'root': reg, 'interior': 0, 'inputs': [
        {'reg': '%v', 'w': 32, 'lanes': 4, 'type': '<4 x s32>',
         'zero': '0x0', 'one': '0x0'},
        {'reg': '%i' + reg[1:], 'w': 32, 'type': 's32', 'zero': '0x0',
         'one': '0x0', 'const': hex(index)}],
        'expr': {'op': 'G_EXTRACT_VECTOR_ELT', 'w': 32, 'type': 's32',
                 'reg': reg, 'zero': '0x0', 'one': '0x0', 'uses': 1,
                 'flags': [], 'args': [{'in': 0}, {'in': 1}]}}


class RunsTest(unittest.TestCase):
    """synth, run after run with one cache directory."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.n = 0

    def path(self, *parts):
        return os.path.join(self.tmp.name, *parts)

    def corpus(self, records, name='c.jsonl'):
        with open(self.path(name), 'w') as f:
            for r in records:
                f.write(json.dumps(r) + '\n')
        return self.path(name)

    def synth(self, corpus_file, cache='cache', known_db='', **over):
        self.n += 1
        out = self.path('run%d.json' % self.n)
        over = dict(dict(regions=False, siblings=False), **over)
        cli.cmd_synth(cli.default_args(
            'synth', corpus=[corpus_file], o=out,
            proofs=self.path('proofs%d' % self.n), known=known_db,
            cache=self.path(cache) if cache else '', search_jobs=0, **over))
        with open(out) as f:
            db = json.load(f)
        with open(os.path.splitext(out)[0] + '.stats.json') as f:
            return db, json.load(f)

    def test_a_capped_run_searches_what_was_not_searched(self):
        c = self.corpus(SIMPLE)
        done, ids = [], []
        for _ in range(3):
            db, st = self.synth(c, max_instances=2)
            self.assertEqual(st['discovery']['instances'], 2)
            done.append(st['queue']['single']['complete'])
            ids.append({r['id'] for r in db['rules']})
        # The limit of instances is of the tasks that a run searches: a
        # task that is complete does not use it.
        self.assertEqual(done, [2, 4, 6])
        self.assertTrue(ids[0] < ids[1] < ids[2])
        self.assertEqual(st['queue']['left'], 0)
        # Nothing is left: no search, no check of the solver.
        db, st = self.synth(c, max_instances=2)
        self.assertEqual((st['discovery']['instances'], st['solver_calls'],
                          st['enumeration']['banks']), (0, 0, 0))
        self.assertEqual({r['id'] for r in db['rules']}, ids[2])
        # The same rules as one run without a limit and without a cache.
        full, st = self.synth(c, cache=None)
        self.assertEqual({r['id'] for r in full['rules']}, ids[2])
        self.assertEqual(st['queue']['left'], 0)

    def test_a_higher_budget_opens_only_the_tasks_that_it_limits(self):
        c = self.corpus(SIMPLE)
        _, st = self.synth(c, max_proofs=0)
        q = st['queue']['single']
        self.assertEqual(q['complete'] + q['open'], 6)
        self.assertGreater(q['reasons'].get('proofs', 0), 0)
        opened = q['open']
        _, st = self.synth(c)
        self.assertEqual(st['discovery']['instances'], opened)
        self.assertEqual(st['queue']['left'], 0)

    def test_a_known_rule_is_the_seed_of_a_rule_with_several_outputs(self):
        c = self.corpus([ADD_CMP])
        # The rules with one output, as a shared catalog.
        base, st = self.synth(c, cache=None, grammar='registry',
                              regions=True)
        single = [r for r in base['rules'] if not r.get('region')]
        joint = [r for r in base['rules'] if r.get('region')]
        self.assertTrue(single and joint)
        catalog = self.path('catalog')
        os.makedirs(catalog)
        k = known.stamp({'format': base['format'], 'rules': single})
        known.copy_proofs(k, os.path.join(catalog, 'proofs'),
                          [self.path('proofs%d' % self.n)])
        known.write(k, os.path.join(catalog, 'rules.json'))
        # A run that knows them finds the rule with two outputs on the
        # known rule, without a proof of a rule that it knows.
        with mock.patch.object(synth.Synthesizer, '_add',
                               side_effect=AssertionError('found again')):
            db, st = self.synth(c, known_db=os.path.join(catalog,
                                                         'rules.json'),
                                grammar='registry', regions=True)
        self.assertEqual(st['synthesis']['generalized'], 0)
        self.assertGreater(st['discovery']['known_candidates'], 0)
        delta = [r for r in db['rules']
                 if r['id'] in st['incremental']['delta']]
        self.assertEqual([r['id'] for r in delta], [r['id'] for r in joint])
        self.assertIn(delta[0]['region']['base_rule'],
                      {r['id'] for r in single})
        self.assertEqual(st['queue']['region']['complete'], 1)
        # The next run has no task.
        db2, st = self.synth(c, known_db=os.path.join(catalog,
                                                      'rules.json'),
                             grammar='registry', regions=True)
        self.assertEqual((st['solver_calls'], st['enumeration']['banks'],
                          st['queue']['left']), (0, 0, 0))
        self.assertEqual({r['id'] for r in db2['rules']},
                         {r['id'] for r in db['rules']})

    def test_a_group_with_a_vector_is_not_a_task(self):
        # Two instructions that read one vector: a group of the corpus,
        # but the search of a group is for scalar values.
        c = self.corpus([extract('%a', 0), extract('%b', 1)])
        _, st = self.synth(c, siblings=True)
        self.assertGreater(st['siblings']['corpus']['with_a_vector'], 0)
        self.assertEqual(st['queue']['sibling']['tasks'], 0)
        self.assertEqual(st['queue']['left'], 0)

    def test_several_outputs_have_a_part_of_the_time(self):
        c = self.corpus([ADD_CMP])
        # Run 1: the root of the region, without the search for several
        # outputs.
        _, st = self.synth(c, grammar='registry')
        self.assertEqual(st['queue']['left'], 0)
        # Run 2: more instances than its time has, and the region task
        # on the rules of run 1.
        c2 = self.corpus([ADD_CMP] + SIMPLE, 'c2.jsonl')
        real = discover.discover

        def slow(inst, *a, **k):
            time.sleep(2)
            return real(inst, *a, **k)
        with mock.patch.object(discover, 'discover', side_effect=slow):
            db, st = self.synth(c2, grammar='registry', regions=True,
                                time_budget_s=5)
        self.assertTrue(st['incremental']['deadline_reached'])
        self.assertGreater(st['queue']['single']['not_searched'], 0)
        self.assertEqual(st['queue']['region']['complete'], 1)
        self.assertTrue([r for r in db['rules'] if r.get('region')])


if __name__ == '__main__':
    unittest.main()
