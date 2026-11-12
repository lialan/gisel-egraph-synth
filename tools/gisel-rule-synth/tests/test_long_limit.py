"""The long time limit of the solver: a candidate that the solver does not
decide in the usual limit gets one more attempt (synth.Synthesizer._slow).
An UNKNOWN result is never a proof, so the long limit only adds rules."""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from girs import corpus, ir, ops, smt, synth  # noqa: E402

W = 32
LONG = 2 * smt.DEFAULT_TIMEOUT_MS


def V(i):
    return ('var', i)


def instance(src, vw):
    return corpus.Instance(src, tuple(vw), [(0, 0)] * len(vw),
                           [None] * len(vw),
                           [1] * len(ir.interior_nodes(src)), [],
                           [('f', 'fn', '%0')])


class OnlyWithTheLongLimit(smt.Z3Backend):
    """A solver that decides a formula only with the long limit."""

    def check(self, formula, want_model_of=None):
        if self.deadline is None:
            self.calls += 1
            return smt.Result('unknown')
        return super().check(formula, want_model_of)


class NeverDecides(smt.Z3Backend):
    def check(self, formula, want_model_of=None):
        self.calls += 1
        return smt.Result('unknown')


# (x + y) - y -> x.
SRC = ('G_SUB', W, ('G_ADD', W, V(0), V(1)), V(1))
TGT = V(0)


def limits(**kw):
    return synth.SynthLimits(slow_timeout_ms=LONG, **kw)


class LongLimitTest(unittest.TestCase):
    def test_usual_limit_has_no_long_attempt(self):
        s = synth.Synthesizer(smt.Z3Backend(), limits())
        self.assertIsNotNone(s.add(instance(SRC, (W, W)), TGT))
        self.assertNotIn('slow_attempts', s.stats)
        (r,) = s.rules.values()
        for d in r['disjuncts']:
            for p in d['proofs']:
                self.assertNotIn('timeout_ms', p)

    def test_long_limit_proves_the_rule(self):
        s = synth.Synthesizer(OnlyWithTheLongLimit(), limits())
        inst = instance(SRC, (W, W))
        self.assertIsNotNone(s.add(inst, TGT))
        self.assertEqual(s.stats['slow_attempts'], 1)
        s.finalize([inst])
        (r,) = s.rules.values()
        # Each proof has its limit, and the guard as a whole has a proof.
        self.assertEqual(r['semantic_status']['kind'], 'verified_refinement')
        proofs = [p for d in r['disjuncts'] for p in d['proofs']]
        self.assertTrue(proofs)
        for p in proofs + r['semantic_status']['dnf_proofs']:
            self.assertEqual(p['timeout_ms'], LONG)
        # The usual limit is back.
        self.assertEqual(s.backend.timeout_ms, smt.DEFAULT_TIMEOUT_MS)
        self.assertIsNone(s.backend.deadline)

    def test_new_widths_of_a_rule(self):
        # The rule has its proof for 32 bits; the instance with 64 bits
        # needs the long limit.
        b = OnlyWithTheLongLimit()
        s = synth.Synthesizer(b, limits(max_schedules=1))
        with b.limit(LONG, 60):
            rid = s.add(instance(SRC, (W, W)), TGT)
        self.assertIsNotNone(rid)
        src64 = ir.map_widths(SRC, {W: 64})
        self.assertEqual(s.add(instance(src64, (64, 64)), TGT), rid)
        self.assertEqual(s.stats['slow_attempts'], 1)
        self.assertEqual(s.stats['schedules_added'], 1)
        maps = [m for d in s.rules[rid]['disjuncts']
                for m in d['width_maps']]
        self.assertIn([[W, 64]], [sorted(map(list, m)) for m in maps])

    def test_unknown_is_not_a_proof(self):
        s = synth.Synthesizer(NeverDecides(), limits())
        self.assertIsNone(s.add(instance(SRC, (W, W)), TGT))
        self.assertEqual(s.stats['slow_attempts'], 1)
        self.assertFalse(s.rules)
        (rej,) = s.rejected.values()
        self.assertEqual(rej['reason'], 'solver_unknown')

    def test_one_attempt_for_a_candidate(self):
        s = synth.Synthesizer(NeverDecides(), limits())
        for _ in range(3):
            self.assertIsNone(s.add(instance(SRC, (W, W)), TGT))
        self.assertEqual(s.stats['slow_attempts'], 1)

    def test_no_time_left_of_the_run(self):
        s = synth.Synthesizer(OnlyWithTheLongLimit(),
                              limits(slow_total_s=0))
        self.assertIsNone(s.add(instance(SRC, (W, W)), TGT))
        self.assertNotIn('slow_attempts', s.stats)

    def test_limit_that_is_not_longer(self):
        s = synth.Synthesizer(
            OnlyWithTheLongLimit(),
            synth.SynthLimits(slow_timeout_ms=smt.DEFAULT_TIMEOUT_MS))
        self.assertIsNone(s.add(instance(SRC, (W, W)), TGT))
        self.assertNotIn('slow_attempts', s.stats)

    def test_check_after_the_deadline_is_unknown(self):
        b = smt.Z3Backend()
        enc = smt.Encoder((W, W), W)
        f = smt.refinement_violation(enc, SRC, TGT, True)
        with b.limit(LONG, 0):
            r = b.check(f)
        self.assertEqual(r.status, 'unknown')
        self.assertEqual(b.calls, 0)
        self.assertEqual(b.check(f).status, 'unsat')

    def test_result_has_only_a_long_limit(self):
        b = smt.Z3Backend()
        enc = smt.Encoder((W, W), W)
        f = smt.refinement_violation(enc, SRC, TGT, True)
        self.assertIsNone(b.check(f).timeout_ms)
        with b.limit(LONG, 60):
            self.assertEqual(b.check(f).timeout_ms, LONG)


if __name__ == '__main__':
    unittest.main()
