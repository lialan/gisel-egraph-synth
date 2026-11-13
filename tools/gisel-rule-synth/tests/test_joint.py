"""Tests of the joint region search (girs/joint.py) and its emission.

The regions are built here; the search has no template of any of them.
"""

import os
import sys
import unittest

import z3

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from girs import discover  # noqa: E402
from girs import ir  # noqa: E402
from girs import joint  # noqa: E402
from girs import joint_emit  # noqa: E402
from girs import ops  # noqa: E402
from girs import smt  # noqa: E402


def region(inputs, instrs):
    """inputs: (w, defined[, const]); instrs: (op, attr, widths, args,
    users of each result[, flags]). The outputs are the results with a
    user outside of the region."""
    ins = [joint.Input(i[0], defined=i[1],
                       const=i[2] if len(i) > 2 else None) for i in inputs]
    out = [joint.Instr(i[0], i[1], i[5] if len(i) > 5 else (), i[2],
                       [tuple(a) for a in i[3]], i[4],
                       defined=[True] * len(i[2])) for i in instrs]
    return joint.Region(ins, out, prov=[('test', 'f', 0, 0, ())])


X, Y, Z = ('in', 0), ('in', 1), ('in', 2)


def n(k, r=0):
    return ('n', k, r)


def dsq(defined=True, flags=(), a_users=1):
    """s = x*x; d = (x - y) * (y + x); s and d have a user outside."""
    return region([(32, defined), (32, defined)], [
        ('G_MUL', None, (32,), [X, X], [1], flags),
        ('G_SUB', None, (32,), [X, Y], [a_users]),
        ('G_ADD', None, (32,), [Y, X], [1]),
        ('G_MUL', None, (32,), [n(1), n(2)], [1])])


def helper_region():
    """o1 = (y + 1) * x; o2 = o1 - (x << 1): what opt -O2 makes of
    x * (y + 1) and x * (y - 1) for gfx1100."""
    return region([(32, True, 1), (32, True), (32, True)], [
        ('G_ADD', None, (32,), [Y, X], [1]),
        ('G_MUL', None, (32,), [n(0), Z], [2]),
        ('G_SHL', None, (32,), [Z, X], [1]),
        ('G_SUB', None, (32,), [n(1), n(2)], [1])])


class JointTest(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.limits = joint.Limits(time_s=120)
        cls.ctx = discover.Context(discover.Limits(
            max_terms=cls.limits.max_terms, max_evals=cls.limits.max_evals))
        cls.backend = smt.Z3Backend()

    def search(self, win, limits=None):
        key, c = joint.canonical(win)
        s = joint.Search(c, limits or self.limits, self.ctx, self.backend, {})
        status, cands, indep = s.run()
        return c, s, status, cands, indep

    def rules(self, win, limits=None):
        key, c = joint.canonical(win)
        rules, recs, stats = joint.search_windows(
            {key: (c, list(win.prov))}, limits or self.limits, self.backend)
        return rules, recs, stats

    # -- Phase 1: the difference of squares --

    def test_difference_of_squares_is_found(self):
        c, s, status, cands, indep = self.search(dsq())
        self.assertTrue(cands)
        best = cands[0]
        # Keep x*x, build y*y and the difference: one instruction fewer.
        self.assertEqual(best.cost_after(), s.cost_before - 1)
        sq = next(k for k, i in enumerate(c.instrs)
                  if i.name == 'G_MUL' and i.args == (X, X))
        self.assertEqual(best.kept, {sq})
        self.assertEqual(sorted(x[0] for x in best.new), ['G_MUL', 'G_SUB'])
        self.assertIn(('G_MUL', None, (32,), (Y, Y)), best.new)
        # Both inputs are read twice: defined(x), defined(y).
        self.assertEqual(joint.guards(best)['defined'], [0, 1])
        st, proofs, refuted = joint.prove(best, self.limits, self.backend)
        self.assertEqual(st, 'valid')
        self.assertEqual(sorted(dict(p['width_map'])[32] for p in proofs),
                         [8, 16, 32, 64])
        # Each output alone, charged with the instructions it reads, does
        # not get cheaper.
        self.assertTrue(indep is None or
                        indep.cost_after() >= s.cost_before)
        p = joint.plan(best)
        self.assertEqual(p['actions'][sq], 'relax')
        self.assertEqual(sorted(p['actions']).count('erase'), 2)
        self.assertEqual(c.instrs[p['anchor']].name, 'G_MUL')

    def test_rule_record_emits_and_checks(self):
        rules, recs, stats = self.rules(dsq())
        self.assertEqual(len(rules), 1)
        r = rules[0]
        self.assertEqual(joint.check_rule(r), [])
        td, inc, info = joint_emit.emit([r])
        self.assertEqual(info['rules'], 1)
        self.assertIn('(G_MUL $d0, $o0, $o1):$root', td)
        self.assertIn('Action::Relax', inc)
        self.assertIn('0x3, 0x0', inc)   # defined x, y; no distinct input
        # A guard removed by hand: the rule is refused.
        r['plan']['guards']['defined'] = []
        self.assertTrue(joint.check_rule(r))
        td, inc, info = joint_emit.emit([r])
        self.assertEqual(info['rules'], 0)
        self.assertIn(r['id'], info['skipped'])

    def test_proofs_replay(self):
        """A stored proof is an SMT-LIB2 query that z3 decides again."""
        c, s, status, cands, indep = self.search(dsq())
        st, proofs, refuted = joint.prove(cands[0], self.limits, self.backend)
        for p in proofs:
            solver = z3.Solver()
            solver.from_string(p['smt2'])
            self.assertEqual(solver.check(), z3.unsat)

    def test_undefined_inputs_reject(self):
        """The candidates read x and y twice; if they are not defined in
        the instance, the rule would never apply to it."""
        rules, recs, stats = self.rules(dsq(defined=False))
        self.assertEqual(rules, [])

    # -- Phase 3: a shared helper that the region does not have --

    def test_new_shared_helper(self):
        c, s, status, cands, indep = self.search(helper_region())
        self.assertTrue(cands)
        best = cands[0]
        self.assertEqual(best.cost_after(), s.cost_before - 1)
        shared = joint.shared_new(best)
        self.assertTrue(shared)
        h = best.new[shared[0]]
        self.assertEqual(h[0], 'G_MUL')
        # The helper is no value of the region.
        win_vals = {(i.name, tuple(sorted(i.args))) for i in c.instrs}
        self.assertNotIn((h[0], tuple(sorted(h[3]))), win_vals)
        # Both outputs change.
        self.assertTrue(all(v[0] == 't' for v in best.outputs.values()))
        self.assertEqual(best.kept, frozenset())
        # Independent selection: each output alone is no cheaper.
        self.assertTrue(indep is None or
                        indep.cost_after() >= s.cost_before)
        st, proofs, refuted = joint.prove(best, self.limits, self.backend)
        self.assertEqual(st, 'valid')
        g = joint.guards(best)
        self.assertEqual(len(g['constant']), 1)

    # -- semantic counterexamples --

    def _dsq_best(self, win=None):
        c, s, status, cands, indep = self.search(win or dsq())
        return cands[0]

    def test_wrong_second_output_is_refuted(self):
        best = self._dsq_best()
        new = list(best.new)
        j = next(i for i, x in enumerate(new) if x[0] == 'G_SUB')
        new[j] = ('G_ADD',) + new[j][1:]
        bad = joint.Candidate(best.win, best.kept, best.outputs, new, {})
        st, _, refuted = joint.prove(bad, self.limits, self.backend)
        self.assertEqual(st, 'invalid')

    def test_poison_output_does_not_excuse_another(self):
        """o1 = x << y is poison for y >= 32. The new o2 is poison exactly
        then, while the source o2 = x + y is defined: refuted, although
        all outputs of the source are not defined at that input."""
        win = region([(32, True), (32, True)], [
            ('G_SHL', None, (32,), [X, Y], [1]),
            ('G_ADD', None, (32,), [X, Y], [1])])
        _, c = joint.canonical(win)
        shl = next(k for k, i in enumerate(c.instrs) if i.name == 'G_SHL')
        add = 1 - shl
        cand = joint.Candidate(c, {shl}, {
            (shl, 0): n(shl), (add, 0): ('t', 2, 0)}, [
            ('G_ADD', None, (32,), (X, Y)),
            ('G_XOR', None, (32,), (n(shl), n(shl))),
            ('G_ADD', None, (32,), (('t', 0, 0), ('t', 1, 0)))], {})
        st, _, refuted = joint.prove(cand, self.limits, self.backend)
        self.assertEqual(st, 'invalid')
        # The model: an amount that makes the shift poison.
        vals = refuted[0]['model']
        self.assertGreaterEqual(vals[1], 32)

    def test_freezes_are_not_merged(self):
        win = region([(32, False)], [
            ('G_FREEZE', None, (32,), [X], [1]),
            ('G_FREEZE', None, (32,), [X], [1]),
            ('G_SUB', None, (32,), [n(0), n(1)], [1])])
        key, c = joint.canonical(win)
        self.assertEqual(sum(i.name == 'G_FREEZE' for i in c.instrs), 2)
        sub = next(k for k, i in enumerate(c.instrs) if i.name == 'G_SUB')
        zero = joint.Candidate(c, set(), {(sub, 0): ('lit', '0', 32)}, [], {})
        st, _, _ = joint.prove(zero, self.limits, self.backend)
        self.assertEqual(st, 'invalid')
        rules, _, _ = self.rules(win)
        self.assertEqual(rules, [])
        # One G_FREEZE read twice is one value: x - x is 0.
        one = region([(32, False)], [
            ('G_FREEZE', None, (32,), [X], [2]),
            ('G_SUB', None, (32,), [n(0), n(0)], [1])])
        _, c1 = joint.canonical(one)
        sub = next(k for k, i in enumerate(c1.instrs) if i.name == 'G_SUB')
        zero = joint.Candidate(c1, set(), {(sub, 0): ('lit', '0', 32)}, [],
                               {})
        self.assertEqual(joint.prove(zero, self.limits, self.backend)[0],
                         'valid')

    def test_flags_of_a_reused_value(self):
        """The square keeps nsw. Read by the new difference without
        dropping its flags, it can be poison where the source difference
        is not: refuted. The rule drops them (relax), and that is proved."""
        best = self._dsq_best(dsq(flags=('nsw',)))
        self.assertTrue(joint.relaxed(best))
        m = joint.width_maps(best, self.limits)[0]
        f, enc = joint.formula(best, m, flags=True, relax=False)
        self.assertEqual(self.backend.check(f).status, 'sat')
        f, enc = joint.formula(best, m, flags=True, relax=True)
        self.assertEqual(self.backend.check(f).status, 'unsat')

    def test_inner_value_with_an_outside_user(self):
        """x - y has a user outside: it is an output, it stays, and its
        cost counts. Then no rewrite of d is cheaper than the region."""
        win = dsq(a_users=2)
        key, c = joint.canonical(win)
        self.assertEqual(len(c.outputs), 3)
        rules, _, _ = self.rules(win)
        self.assertEqual(rules, [])
        c, s, status, cands, indep = self.search(win)
        sub = next(k for k, i in enumerate(c.instrs) if i.name == 'G_SUB')
        for cand in cands:
            self.assertIn((sub, 0), cand.outputs)
            if cand.outputs[(sub, 0)] == n(sub):
                self.assertIn(sub, cand.kept)
            self.assertLess(cand.cost_after(), s.cost_before)
            self.assertNotIn(sub, [k for k, a in enumerate(
                joint.plan(cand)['actions']) if a == 'erase'])

    # -- region DAG: identity, results, boundary --

    def test_multi_result_instruction(self):
        """x + y and (x + y) <u x as two outputs: one G_UADDO computes both
        (its two results are one instruction, of one cost)."""
        win = region([(32, False), (32, False)], [
            ('G_ADD', None, (32,), [X, Y], [2]),
            ('G_ICMP', 'ult', (1,), [n(0), X], [1])])
        lim = joint.Limits(time_s=120, grammar=list(ops.ENUMERATED) +
                           ['G_UADDO', 'G_ICMP'])
        c, s, status, cands, indep = self.search(win, lim)
        best = next(c_ for c_ in cands if any(x[0] == 'G_UADDO'
                                             for x in c_.new))
        self.assertEqual(len(best.new), 1)
        self.assertEqual(best.new[0][2], (32, 1))
        self.assertEqual(sorted(v[2] for v in best.outputs.values()), [0, 1])
        self.assertEqual(best.cost_after(), ops.cost('G_UADDO'))
        # Each input is read once: no guard.
        self.assertEqual(joint.guards(best)['defined'], [])
        self.assertEqual(joint.prove(best, lim, self.backend)[0], 'valid')

    def test_one_value_for_two_outputs(self):
        win = region([(32, True), (32, True)], [
            ('G_ADD', None, (32,), [X, Y], [1]),
            ('G_ADD', None, (32,), [Y, X], [1])])
        key, c = joint.canonical(win)
        self.assertEqual(len(c.instrs), 2)
        c, s, status, cands, indep = self.search(win)
        best = cands[0]
        self.assertEqual(best.cost_after(), 1)
        vals = set(best.outputs.values())
        self.assertEqual(len(vals), 1)
        # The kept value is read by two outputs: its inputs are guarded.
        self.assertEqual(joint.guards(best)['defined'], [0, 1])

    def test_canonical_renaming(self):
        a = dsq()
        # The same region with other input and instruction orders.
        b = region([(32, True), (32, True)], [
            ('G_ADD', None, (32,), [X, Y], [1]),
            ('G_SUB', None, (32,), [Y, X], [1]),
            ('G_MUL', None, (32,), [n(1), n(0)], [1]),
            ('G_MUL', None, (32,), [Y, Y], [1])])
        ka, ca = joint.canonical(a)
        kb, cb = joint.canonical(b)
        self.assertEqual(ka, kb)
        # Another boundary (a second user of x - y) is another key.
        kc, _ = joint.canonical(dsq(a_users=2))
        self.assertNotEqual(ka, kc)
        # Another fact is another key.
        kd, _ = joint.canonical(dsq(defined=False))
        self.assertNotEqual(ka, kd)
        # The renamed regions compute the same outputs.
        env = (7, 3)
        va = sorted(joint.evaluate(ca, env)[o] for o in ca.outputs)
        vb = sorted(joint.evaluate(cb, env)[o] for o in cb.outputs)
        self.assertEqual(va, vb)

    def test_windows_connect_through_shared_inputs(self):
        blk = dsq()
        wins = joint.windows(blk, 4, 1000)
        self.assertIn([0, 1, 2, 3], wins)
        # A value with too many users does not connect.
        many = region([(32, False)], [
            ('G_ADD', None, (32,), [X, X], [1]),
            ('G_MUL', None, (32,), [X, X], [1])])
        many.inputs[0].uses = joint.MAX_USERS + 1
        self.assertNotIn([0, 1], joint.windows(many, 4, 1000))

    def test_budget_is_not_no_optimization(self):
        lim = joint.Limits(time_s=0.0)
        c, s, status, cands, indep = self.search(dsq(), lim)
        self.assertTrue(status.startswith('budget'))

    # -- the bank --

    def test_nonlinear_bank(self):
        lim = discover.Limits(max_terms=20000)
        lin = discover.Bank((0, 0), ((32, 'i'),), lim,
                            discover.grammar_keys(['G_MUL'], None))
        lin.ensure(2)
        non = discover.Bank((0, 0), ((32, 'i'),), lim,
                            discover.grammar_keys(['G_MUL'], None),
                            nonlinear=True)
        non.ensure(2)
        sq = ('G_MUL', 32, ('var', 1), ('var', 1))
        exprs = [non.expr(i, ((32, 'i'),)) for i in range(len(non.op))]
        self.assertIn(sq, exprs)
        exprs = [lin.expr(i, ((32, 'i'),)) for i in range(len(lin.op))]
        self.assertNotIn(sq, exprs)
        self.assertTrue(all(ir.is_linear(e) for e in exprs))


if __name__ == '__main__':
    unittest.main()
