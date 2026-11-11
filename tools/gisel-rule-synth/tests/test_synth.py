"""Unit tests for llvm/utils/gisel-rule-synth.

Run:  python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests
(needs the z3 and numpy Python modules; no llc).
"""

import json
import os
import random
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import z3  # noqa: E402

from girs import (compose, corpus, discover, emit, ir, match,  # noqa
                  ops, precond, select, smt, synth, targets)


def V(i):
    return ('var', i)


def L(w, k):
    return ('lit', w, k)


def inst(expr, vw, facts, consts=None):
    consts = consts or [None] * len(vw)
    return corpus.Instance(expr, vw, facts, consts, [], [],
                           [('test', 'f', '%0')])


M32 = ir.mask(32)


class SemanticsTest(unittest.TestCase):
    """The concrete evaluator and the z3 encoding agree."""

    def test_eval_matches_z3(self):
        rng = random.Random(1)
        exprs = []
        for op in ir.BINOPS:
            exprs.append(((op, 8, V(0), V(1)), (8, 8)))
        exprs.append((('G_ZEXT', 16, V(0)), (8,)))
        exprs.append((('G_SEXT', 16, V(0)), (8,)))
        exprs.append((('G_TRUNC', 8, V(0)), (16,)))
        exprs.append((('G_SHL', 16, V(0), V(1)), (16, 8)))  # amount width
        for e, vw in exprs:
            enc = smt.Encoder(vw)
            ze, zp = enc.enc(e)
            for _ in range(40):
                env = [rng.getrandbits(w) if rng.random() < .7 else
                       rng.randrange(0, 20) for w in vw]
                sub = [(x, z3.BitVecVal(v, w))
                       for x, v, w in zip(enc.x, env, vw)]
                cv = ir.evaluate(e, vw, env)
                zpv = z3.is_true(z3.simplify(z3.substitute(zp, *sub)))
                self.assertEqual(cv is None, zpv, (e, env))
                if cv is not None:
                    self.assertEqual(
                        cv, z3.simplify(z3.substitute(ze, *sub)).as_long())

    def test_shift_out_of_range_is_poison(self):
        e = ('G_SHL', 32, V(0), V(1))
        self.assertIsNone(ir.evaluate(e, (32, 32), [1, 32]))
        self.assertEqual(ir.evaluate(e, (32, 32), [1, 31]), 1 << 31)

    def test_well_typed(self):
        self.assertTrue(ir.well_typed(('G_ZEXT', 32, V(0)), (8,)))
        self.assertFalse(ir.well_typed(('G_ZEXT', 8, V(0)), (32,)))
        self.assertFalse(ir.well_typed(('G_AND', 32, V(0), V(1)), (32, 64)))
        self.assertTrue(ir.well_typed(('G_LSHR', 64, V(0), V(1)), (64, 32)))


class DiscoveryTest(unittest.TestCase):
    def setUp(self):
        self.be = smt.Z3Backend()
        self.lim = discover.Limits()

    def test_and_mask_discovers_operand(self):
        # %x has its high 24 bits known zero; (x & 255) -> x is *found* by
        # the enumerative search, not looked up.
        i = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                 [(0xffffff00, 0), (0xffffff00, 0xff)], [None, 0xff])
        cands, st = discover.discover(i, self.be, self.lim)
        self.assertIn(V(0), [c['tgt'] for c in cands])
        self.assertGreater(st['terms'], 10)

    def test_and_mask_without_facts_finds_nothing(self):
        i = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                 [(0, 0), (0xffffff00, 0xff)], [None, 0xff])
        cands, _ = discover.discover(i, self.be, self.lim)
        self.assertEqual(cands, [])

    def test_unconditional_identity(self):
        # or(x, and(x, y)) -> x needs no facts at all.
        i = inst(('G_OR', 32, V(0), ('G_AND', 32, V(0), V(1))), (32, 32),
                 [(0, 0), (0, 0)])
        cands, _ = discover.discover(i, self.be, self.lim)
        self.assertEqual(cands[0]['tgt'], V(0))

    def test_terms_are_linear(self):
        ctx = discover.Context(self.lim)
        bank = ctx.bank((0, 0), 1, 2)
        n = bank.size(2)
        self.assertGreater(n, 20)
        for k in range(n):
            e = bank.expr(k, (32,))
            self.assertTrue(ir.is_linear(e), ir.to_sexpr(e))

    def test_bank_is_shared_across_shapes_and_widths(self):
        # Two sources of different shape and width, same signature (two
        # variables of one width class): one enumeration serves both.
        ctx = discover.Context(self.lim)
        a = inst(('G_OR', 32, V(0), ('G_AND', 32, V(0), V(1))), (32, 32),
                 [(0, 0), (0, 0)])
        b = inst(('G_AND', 16, V(0), ('G_OR', 16, V(0), V(1))), (16, 16),
                 [(0, 0), (0, 0)])
        for i in (a, b):
            cands, _ = discover.discover(i, self.be, self.lim, ctx)
            self.assertEqual(cands[0]['tgt'], V(0))
        st = ctx.stats()
        self.assertEqual(st['banks'], 1)
        self.assertEqual(st['bank_reuses'], 1)

    def test_refuting_model_becomes_a_sample(self):
        # A refuted candidate leaves its counterexample in the pool, and a
        # later instance with compatible facts is filtered by it.
        ctx = discover.Context(self.lim)
        i = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                 [(0, 0), (0x80000000, 0x7fffffff)], [None, 0x7fffffff])
        st = discover.new_stats()
        out = discover.prove_candidates(i, [V(0)], self.be, self.lim, ctx,
                                        st)
        self.assertEqual(out, [])
        self.assertEqual(st['smt_refuted'], 1)
        self.assertEqual(len(ctx.cex[(32, 32)]), 1)
        env = ctx.cex[(32, 32)][0]
        self.assertIn(env, discover.instance_envs(i, self.lim, ctx))
        self.assertFalse(discover.refines_on(i, V(0), env))

    def test_sampled_match_refuted_by_smt(self):
        # With 2 samples, x and (x & 0x7fffffff) can agree on the samples;
        # the concrete SMT proof must still reject the candidate.
        i = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                 [(0, 0), (0x80000000, 0x7fffffff)], [None, 0x7fffffff])
        r = discover.prove_concrete(i, V(0), self.be)
        self.assertEqual(r.status, 'sat')


class GrammarTest(unittest.TestCase):
    """The operators next to the base grammar of the enumerative search."""

    def test_kernels_match_the_evaluator(self):
        rng = random.Random(1)
        U64 = discover.U64
        for op in ops.ENUMERATED + ops.ENUMERATED_EXTRA:
            info = ops.parse(op)[0]
            unary = op in ir.CASTS or (op in ops.ENUMERATED_EXTRA and
                                       op not in ops.ENUMERATED_BINARY)
            checked = 0
            for w in (1, 8, 16, 32, 33, 64):
                for wa in (1, 8, 16, 32, 33, 64):
                    for wb in ((None,) if unary else (wa, 8)):
                        ws = [wa] if unary else [wa, wb]
                        if not info.typecheck(w, ws, None, 0):
                            continue
                        a = discover._special(wa) + \
                            [rng.getrandbits(wa) for _ in range(40)]
                        a = [x & ir.mask(wa) for x in a]
                        b = None if unary else \
                            [discover._draw(wb, rng) & ir.mask(wb)
                             for _ in a]
                        v, bad = discover.kernel(
                            op, w, wa, discover.np.array(a, U64),
                            None if unary else discover.np.array(b, U64))
                        for i, x in enumerate(a):
                            ref = ir.apply_op(op, w, ws,
                                              [x] if unary else [x, b[i]])
                            got = None if bad is not None and bad[i] \
                                else int(v[i])
                            self.assertEqual(got, ref, (op, w, ws, x, b))
                            checked += 1
            self.assertGreater(checked, 0, op)

    def test_base_bank_does_not_change_with_the_default_grammar(self):
        lim = discover.Limits()
        i = inst(('G_AND', 32, V(0), V(1)), (32, 32), [(0, 0), (0, 0)])
        self.assertEqual(discover.grammar_extras(i, lim), ())

    def test_source_operator_is_in_the_grammar(self):
        # umin(zext x, zext y) -> zext(umin(x, y)): the replacement needs
        # G_UMIN.
        be = smt.Z3Backend()
        lim = discover.Limits()
        src = ('G_UMIN', 32, ('G_ZEXT', 32, V(0)), ('G_ZEXT', 32, V(1)))
        i = inst(src, (8, 8), [(0, 0), (0, 0)])
        self.assertEqual(discover.grammar_extras(i, lim), ('G_UMIN',))
        cands, _ = discover.discover(i, be, lim)
        self.assertIn(('G_ZEXT', 32, ('G_UMIN', 8, V(0), V(1))),
                      [t for c in cands
                       for t in ir.commuted_variants(c['tgt'])])
        # The base grammar does not have the operator.
        cands, _ = discover.discover(i, be, discover.Limits(grammar='base'))
        self.assertEqual(cands, [])

    def test_all_grammar_finds_another_operator(self):
        # select(x ult y, x, y) -> umin(x, y): G_UMIN is not in the source.
        be = smt.Z3Backend()
        src = ('G_SELECT', 32, ('G_ICMP:ult', 1, V(0), V(1)), V(0), V(1))
        i = inst(src, (32, 32), [(0, 0), (0, 0)])
        cands, _ = discover.discover(i, be, discover.Limits())
        self.assertEqual(cands, [])
        cands, _ = discover.discover(i, be, discover.Limits(grammar='all'))
        self.assertIn(('G_UMIN', 32, V(0), V(1)),
                      [t for c in cands
                       for t in ir.commuted_variants(c['tgt'])])

    def test_corpus_record_with_attribute_and_result_index(self):
        def leaf(i):
            return {'in': i}

        def node(op, w, args, **kw):
            return dict({'op': op, 'w': w, 'reg': '%%%d' % id(args),
                         'zero': '0x0', 'one': '0x0', 'uses': 1,
                         'flags': [], 'args': args}, **kw)
        inp = [{'reg': '%0', 'w': 32, 'zero': '0x0', 'one': '0x0',
                'def': 'COPY'},
               {'reg': '%1', 'w': 32, 'zero': '0x0', 'one': '0x0',
                'def': 'COPY'}]
        rec = {'fn': 'f', 'bb': 0, 'root': '%9', 'interior': 2,
               'inputs': inp,
               'expr': node('G_SELECT', 32, [
                   node('G_ICMP', 1, [leaf(0), leaf(1)], pred='ult'),
                   leaf(0), leaf(1)])}
        i = corpus.parse_record(rec)
        self.assertEqual(i.expr, ('G_SELECT', 32,
                                  ('G_ICMP:ult', 1, V(0), V(1)), V(0),
                                  V(1)))
        rec['expr'] = node('G_UADDO', 1, [leaf(0), leaf(1)], res=1)
        self.assertEqual(corpus.parse_record(rec).expr,
                         ('G_UADDO#1', 1, V(0), V(1)))
        rec['expr'] = node('G_SEXT_INREG', 32, [leaf(0)], imm=8)
        self.assertEqual(corpus.parse_record(rec).expr,
                         ('G_SEXT_INREG:8', 32, V(0)))
        # An operator without a model is rejected with the reason.
        why = []
        rec['expr'] = node('G_CLMUL', 32, [leaf(0), leaf(1)])
        self.assertIsNone(corpus.parse_record(rec, why=why))
        self.assertIn('G_CLMUL', why[0])


class PreconditionTest(unittest.TestCase):
    def setUp(self):
        self.be = smt.Z3Backend()
        self.lim = synth.SynthLimits()

    def synth(self, src, tgt, vw, facts):
        sched = synth.schedules(src, tgt, vw, self.lim)
        valid, st = synth.synthesize_precondition(src, tgt, vw, facts, sched,
                                                  self.be, self.lim)
        best = synth.weakest(valid, vw, self.be, src[1]) if valid else []
        return [p for p, _ in best], st

    def test_and_mask_guard(self):
        # Primary milestone: G_AND(x, M) -> x if KZ(x) | KO(M) == all ones.
        ps, st = self.synth(('G_AND', 32, V(0), V(1)), V(0), (32, 32),
                            ((0xffffff00, 0), (0xffffff00, 0xff)))
        self.assertEqual(ps[0], (('all2', ('Z', 0), ('O', 1)),))
        self.assertGreater(st['counterexamples'], 0)  # CEGIS did refine

    def test_or_guard(self):
        ps, _ = self.synth(('G_OR', 32, V(0), V(1)), V(0), (32, 32),
                           ((0, 0xff), (0xffffff00, 0xf)))
        self.assertEqual(ps[0], (('all2', ('O', 0), ('Z', 1)),))

    def test_add_to_or_no_carry_guard(self):
        ps, _ = self.synth(('G_ADD', 32, V(0), V(1)),
                           ('G_OR', 32, V(0), V(1)), (32, 32),
                           ((0xf, 0), (0xfffffff8, 0x7)))
        self.assertEqual(ps[0], (('all2', ('Z', 0), ('Z', 1)),))

    def test_guard_generalizes_to_unseen_masks_and_widths(self):
        p = (('all2', ('Z', 0), ('O', 1)),)
        self.assertTrue(precond.eval_pred(
            p, ((0xffff0000, 0), (0xffff0000, 0xffff)), (32, 32)))
        self.assertTrue(precond.eval_pred(
            p, ((0xffffffff00000000, 0), (0xffffffff00000000, M32)),
            (64, 64)))
        self.assertFalse(precond.eval_pred(  # insufficient known bits
            p, ((0xffff0000, 0), (0xffffff00, 0xff)), (32, 32)))

    def test_insufficient_training_facts_reject(self):
        # x & 255 -> x is false when x's high bits are unknown: no
        # precondition that holds on these facts can be proved.
        src, tgt, vw = ('G_AND', 32, V(0), V(1)), V(0), (32, 32)
        facts = ((0, 0), (0xffffff00, 0xff))
        ps, st = self.synth(src, tgt, vw, facts)
        self.assertEqual(ps, [])

    def test_target_poison_is_rejected(self):
        # ((x + y) & 0) -> (0 >> y): equal values, but the replacement is
        # poison for y >= width. Rejected unconditionally, valid if
        # y < width.
        src = ('G_AND', 32, ('G_ADD', 32, V(0), V(1)), L(32, '0'))
        tgt = ('G_LSHR', 32, L(32, '0'), V(1))
        sched = synth.schedules(src, tgt, (32, 32), self.lim)
        st, _ = synth.verify(sched, [()], self.be)
        self.assertEqual(st, 'invalid')
        st, _ = synth.verify(sched, [(('ltw', 1, 0),)], self.be)
        self.assertEqual(st, 'valid')

    def test_poison_input_of_the_replacement_only_is_rejected(self):
        # (x & 0) -> (0 >> y): y can be poison, and the source does not
        # use it.
        src = ('G_AND', 32, V(0), L(32, '0'))
        tgt = ('G_LSHR', 32, L(32, '0'), V(1))
        sched = synth.schedules(src, tgt, (32, 32), self.lim)
        st, _ = synth.verify(sched, [(('ltw', 1, 0),)], self.be)
        self.assertEqual(st, 'invalid')
        # With a value that is not poison, the rule holds.
        st, _ = synth.verify(sched, [(('ltw', 1, 0), ('def', 1))], self.be)
        self.assertEqual(st, 'valid')

    def test_empty_disjunction_is_not_a_proof(self):
        src, tgt = ('G_AND', 32, V(0), V(1)), V(0)
        sched = synth.schedules(src, tgt, (32, 32), self.lim)
        with self.assertRaises(AssertionError):
            synth.verify(sched, [], self.be)

    def test_disjunction_is_proved_as_a_whole(self):
        # x & y -> x holds if y is all ones OR x is zero; neither disjunct
        # alone covers the other's facts, and a wrong disjunct breaks the
        # proof of the whole.
        src, tgt = ('G_AND', 32, V(0), V(1)), V(0)
        sched = synth.schedules(src, tgt, (32, 32), self.lim)
        ones = (('all', ('O', 1)),)
        zero = (('all', ('Z', 0)),)
        self.assertEqual(synth.verify(sched, [ones, zero], self.be)[0],
                         'valid')
        wrong = (('all', ('Z', 1)),)
        self.assertEqual(synth.verify(sched, [ones, wrong], self.be)[0],
                         'invalid')

    def test_solver_calls_do_not_depend_on_history(self):
        # Each check runs in a fresh solver context: the SMT-LIB text of a
        # proof and the model of a refutation are functions of the formula,
        # not of what was built before.
        src, tgt = ('G_AND', 32, V(0), V(1)), V(0)
        sched = synth.schedules(src, tgt, (32, 32), self.lim)[:1]
        ones = (('all', ('O', 1)),)
        _, p1 = synth.verify(sched, [ones], self.be)
        _, c1 = synth.verify(sched, [()], self.be)
        junk = [z3.BitVec('junk%d' % k, 32) + k for k in range(500)]
        _, p2 = synth.verify(sched, [ones], self.be)
        _, c2 = synth.verify(sched, [()], self.be)
        self.assertEqual(p1[0]['smt2'], p2[0]['smt2'])
        self.assertEqual(c1, c2)
        del junk

    def test_width_mismatch_schedules(self):
        src = ('G_AND', 32, ('G_ZEXT', 32, V(0)), V(1))
        tgt = ('G_ZEXT', 32, V(0))
        scheds = synth.schedules(src, tgt, (8, 32), self.lim)
        for s, t, v, _ in scheds:
            self.assertLess(v[0], v[1])  # zext stays widening
        self.assertIn((8, 64), [s[2] for s in scheds])

    def test_unknown_never_accepted(self):
        class Unknown(smt.Z3Backend):
            def check(self, formula, want_model_of=None):
                self.calls += 1
                return smt.Result('unknown')
        sy = synth.Synthesizer(Unknown())
        i = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                 [(0xffffff00, 0), (0xffffff00, 0xff)], [None, 0xff])
        self.assertIsNone(sy.add(i, V(0)))
        rej = list(sy.rejected.values())[0]
        self.assertEqual(rej['reason'], 'solver_unknown')
        self.assertEqual(sy.rules, {})

    def test_cross_width_guard(self):
        # and(zext x, m) -> zext x needs the low bits of m known one.
        ps, _ = self.synth(('G_AND', 32, ('G_ZEXT', 32, V(0)), V(1)),
                           ('G_ZEXT', 32, V(0)), (8, 32),
                           ((0, 0), (0xffffff00, 0xff)))
        self.assertEqual(ps[0], (('lowones', ('O', 1), 0),))

    def test_atoms_agree_with_z3(self):
        rng = random.Random(3)
        vw, rw = (8, 16), 8
        for a in precond.enumerate_atoms(vw, rw):
            enc = smt.Encoder(vw, rw)
            za = precond.z3_atom(a, enc)
            for _ in range(30):
                facts = []
                for w in vw:
                    z = rng.getrandbits(w) & rng.getrandbits(w)
                    o = rng.getrandbits(w) & ~z & ir.mask(w)
                    facts.append((z, o))
                sub = []
                for i, (z, o) in enumerate(facts):
                    sub += [(enc.kz[i], z3.BitVecVal(z, vw[i])),
                            (enc.ko[i], z3.BitVecVal(o, vw[i]))]
                zv = z3.is_true(z3.simplify(z3.substitute(za, *sub)))
                self.assertEqual(precond.eval_atom(a, facts, vw, rw), zv,
                                 (a, facts))


class GeneralizationTest(unittest.TestCase):
    def test_commuted_and_renamed_rules_share_key(self):
        a = synth.canonicalize(('G_AND', 32, V(0), V(1)), V(0), (32, 32),
                               ((1, 0), (2, 0)))
        b = synth.canonicalize(('G_AND', 32, V(1), V(0)), V(1), (32, 32),
                               ((2, 0), (1, 0)))
        self.assertEqual(synth.class_key(*a[:3]), synth.class_key(*b[:3]))
        self.assertEqual(a[3], b[3])  # facts follow the renaming

    def test_width_independent_key(self):
        k32 = synth.class_key(('G_AND', 32, V(0), V(1)), V(0), (32, 32))
        k64 = synth.class_key(('G_AND', 64, V(0), V(1)), V(0), (64, 64))
        self.assertEqual(k32, k64)

    def test_one_rule_for_many_masks(self):
        sy = synth.Synthesizer(smt.Z3Backend())
        ids = set()
        for m, w in ((0xff, 32), (0xffff, 32), (0xf, 32), (M32, 64)):
            hi = ir.mask(w) & ~m
            i = inst(('G_AND', w, V(0), V(1)), (w, w),
                     [(hi, 0), (hi, m)], [None, m])
            ids.add(sy.add(i, V(0)))
        self.assertEqual(len(ids), 1)
        r = sy.rules[ids.pop()]
        self.assertEqual(r['support']['instances'], 4)
        self.assertEqual(r['semantic_status']['kind'], 'verified_refinement')

    def test_flags_recorded_not_required(self):
        rec = {'fn': 'f', 'root': '%3', 'expr': {
            'op': 'G_ADD', 'w': 32, 'reg': '%3', 'uses': 1,
            'flags': ['nuw', 'nsw'], 'args': [{'in': 0}, {'in': 1}]},
            'inputs': [{'reg': '%1', 'w': 32, 'zero': '0xf', 'one': '0x0'},
                       {'reg': '%2', 'w': 32, 'zero': '0xfffffff8',
                        'one': '0x7', 'const': '0x7'}]}
        i = corpus.parse_record(rec)
        self.assertEqual(i.flags, ('nsw', 'nuw'))
        sy = synth.Synthesizer(smt.Z3Backend())
        rid = sy.add(i, ('G_OR', 32, V(0), V(1)))
        self.assertIn('nuw', sy.rules[rid]['support']['source_flags'])


class DisjunctionTest(unittest.TestCase):
    """One rule per (source, replacement); independently proved sufficient
    conditions are OR-ed."""

    def setUp(self):
        self.sy = synth.Synthesizer(smt.Z3Backend())
        # add -> xor: no common bits at 32 bits; always at 1 bit.
        self.a = inst(('G_ADD', 32, V(0), V(1)), (32, 32),
                      [(0xfffffffe, 0), (0xfffffff9, 0x6)])
        self.b = inst(('G_ADD', 1, V(0), V(1)), (1, 1), [(0, 0), (0, 0)])
        self.rid = self.sy.add(self.a, ('G_XOR', 32, V(0), V(1)))
        rid2 = self.sy.add(self.b, ('G_XOR', 1, V(0), V(1)))
        self.assertEqual(self.rid, rid2)

    def test_two_disjuncts_one_rule(self):
        self.sy.finalize([self.a, self.b])
        r = self.sy.rules[self.rid]
        self.assertEqual(sorted(d['pred'] for d in r['disjuncts']),
                         ['all(KZ(x0) | KZ(x1))', 'true'])
        self.assertIn(' || ', r['precondition'])
        self.assertTrue(r['semantic_status']['dnf_proofs'])
        # The unconditional disjunct is only proved at width 1.
        true = [d for d in r['disjuncts'] if d['pred'] == 'true'][0]
        self.assertEqual(true['width_maps'], [[[32, 1]]])

    def test_disjunct_without_coverage_is_not_emitted(self):
        # Only the 32-bit instance is in the corpus: the width-1 disjunct
        # covers nothing more and is left out of the guard (it stays in
        # the library).
        self.sy.finalize([self.a])
        r = self.sy.rules[self.rid]
        self.assertEqual([d['pred'] for d in r['disjuncts']],
                         ['all(KZ(x0) | KZ(x1))'])
        self.assertEqual([d['pred'] for d in r['unselected_disjuncts']],
                         ['true'])

    def test_guard_evaluates_disjuncts_lazily(self):
        self.sy.finalize([self.a, self.b])
        r = synth.strip_private(self.sy.rules[self.rid])
        cpp = emit._cpp_guard(r)
        # The disjunct without known-bits atoms is tried first and known
        # bits are only queried if it fails.
        self.assertLess(cpp.index('bool Pass = S'), cpp.index('getKnownBits'))
        self.assertIn('if (!Pass) {', cpp)

    def test_weaker_guard_replaces_stronger(self):
        # x & m -> x. First seen with a constant mask of all ones (which
        # also satisfies the stronger "m is all ones"), the rule must end
        # with the guard that covers partial masks too.
        sy = synth.Synthesizer(smt.Z3Backend())
        i = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                 [(0, 0), (0, M32)], [None, M32])
        j = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                 [(0xffffff00, 0), (0xffffff00, 0xff)], [None, 0xff])
        rid = sy.add(i, V(0))
        self.assertEqual(rid, sy.add(j, V(0)))
        sy.finalize([i, j])
        r = sy.rules[rid]
        self.assertEqual([d['pred'] for d in r['disjuncts']],
                         ['all(KZ(x0) | KO(x1))'])
        self.assertEqual(r['coverage']['pass_instances'], 2)


class DominanceTest(unittest.TestCase):
    def test_same_source_keeps_the_better_rule(self):
        # or(add(x, y), x) with no common bits: -> or(x, y) and -> xor(x, y)
        # cost the same under the same guard; exactly one stays a
        # candidate.
        sy = synth.Synthesizer(smt.Z3Backend())
        i = inst(('G_OR', 32, ('G_ADD', 32, V(0), V(1)), V(0)), (32, 32),
                 [(0xffff0000, 0), (0x0000ffff, 0)])
        a = sy.add(i, ('G_OR', 32, V(0), V(1)))
        b = sy.add(i, ('G_XOR', 32, V(0), V(1)))
        self.assertNotEqual(a, b)
        st = sy.finalize([i])
        self.assertEqual(st['dominated_rules'], 1)
        dom = [r for r in (a, b) if 'dominated_by' in sy.rules[r]]
        self.assertEqual(len(dom), 1)
        self.assertIn(sy.rules[dom[0]]['dominated_by'], (a, b))

    def test_cheaper_replacement_under_weaker_guard_dominates(self):
        # x & y: -> 0 needs "no common bits"; -> x needs "y covers x".
        # Neither guard implies the other, so both rules stay.
        sy = synth.Synthesizer(smt.Z3Backend())
        i = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                 [(0xffffff00, 0), (0xffffff00, 0xff)], [None, 0xff])
        j = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                 [(0xffffff00, 0), (0x000000ff, 0)])
        a = sy.add(i, V(0))
        b = sy.add(j, L(32, '0'))
        sy.finalize([i, j])
        self.assertNotIn('dominated_by', sy.rules[a])
        self.assertNotIn('dominated_by', sy.rules[b])

    def test_library_invariants(self):
        with open(os.path.join(ROOT, 'rules.json')) as f:
            db = json.load(f)
        by_id = {r['id']: r for r in db['rules']}
        n = 0
        for r in db['rules']:
            if 'dominated_by' not in r:
                continue
            n += 1
            d = by_id[r['dominated_by']]
            self.assertNotIn('dominated_by', d)
            self.assertLessEqual(d['cost']['replacement'],
                                 r['cost']['replacement'])
            self.assertNotIn(r['id'], [c['id'] for c in emit.candidates(db)])
        self.assertGreater(n, 0)


class MatchTest(unittest.TestCase):
    def test_commutative_and_nested(self):
        pat = ('G_SUB', 32, ('G_ADD', 32, V(0), V(1)), V(0))
        e = ('G_SUB', 32, ('G_ADD', 32, ('G_AND', 32, V(2), V(3)), V(5)),
             V(5))
        ms = match.match(pat, (32, 32), e, (0, 0, 32, 32, 0, 32))
        self.assertEqual(len(ms), 1)
        bind, wmap = ms[0]
        self.assertEqual(bind[0], V(5))
        self.assertEqual(bind[1], ('G_AND', 32, V(2), V(3)))
        self.assertEqual(wmap, {32: 32})

    def test_width_classes_must_agree(self):
        # Pattern (trunc:8 x:32): one class for the source, one for the
        # result; (trunc:16 x:16) is not an instance.
        pat = ('G_TRUNC', 8, V(0))
        self.assertTrue(match.match(pat, (32,), ('G_TRUNC', 16, V(0)),
                                    (64,)))
        self.assertFalse(match.match(pat, (32,), ('G_ZEXT', 16, V(0)),
                                     (8,)))

    def test_coverage_counts_guard_passes(self):
        sy = synth.Synthesizer(smt.Z3Backend())
        ok = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                  [(0xffffff00, 0), (0xffffff00, 0xff)], [None, 0xff])
        no = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                  [(0, 0), (0xffffff00, 0xff)], [None, 0xff])
        rid = sy.add(ok, V(0))
        sy.finalize([ok, no])
        cov = match.coverage([sy.rules[rid]], [ok, no])[rid]
        self.assertEqual(cov['match_instances'], 2)
        self.assertEqual(cov['pass_instances'], 1)


class ComposeTest(unittest.TestCase):
    """R1: (a & b) + (a | b) -> a + b and R2: (a + b) - a -> b compose
    into ((a & b) + (a | b)) - a -> b."""

    def setUp(self):
        self.be = smt.Z3Backend()
        self.lim = discover.Limits()
        self.ctx = discover.Context(self.lim)
        self.sy = synth.Synthesizer(self.be)
        nofacts = [(0, 0), (0, 0)]
        self.i1 = inst(('G_ADD', 32, ('G_AND', 32, V(0), V(1)),
                        ('G_OR', 32, V(0), V(1))), (32, 32), nofacts)
        self.i2 = inst(('G_SUB', 32, ('G_ADD', 32, V(0), V(1)), V(0)),
                       (32, 32), nofacts)
        self.r1 = self.sy.add(self.i1, ('G_ADD', 32, V(0), V(1)))
        self.r2 = self.sy.add(self.i2, V(1))
        self.deep = inst(('G_SUB', 32, self.i1.expr, V(0)), (32, 32),
                         nofacts)

    def propose(self, i):
        index = compose.Index(self.sy.rules.values())
        envs = discover.instance_envs(i, self.lim, self.ctx)
        return compose.propose(i, index, envs), envs

    def test_two_rules_compose(self):
        props, _ = self.propose(self.deep)
        self.assertEqual(props[0][0], V(1))
        self.assertEqual(sorted(props[0][1]), sorted([self.r1, self.r2]))

    def test_macro_rule_is_proved_and_recorded(self):
        props, envs = self.propose(self.deep)
        st = discover.new_stats()
        proved = discover.prove_candidates(
            self.deep, [e for e, _ in props], self.be, self.lim, self.ctx,
            st, envs)
        self.assertEqual(proved[0]['tgt'], V(1))
        rid = self.sy.add(self.deep, V(1), provenance={
            'discovery': 'composition', 'composed_from': props[0][1]})
        self.sy.finalize([self.i1, self.i2, self.deep])
        r = self.sy.rules[rid]
        self.assertEqual(r['semantic_status']['kind'],
                         'verified_refinement')
        self.assertEqual(r['provenance']['discovery'], 'composition')
        self.assertEqual(r['precondition'], 'true')
        self.assertEqual(r['cost'], {'source': 4, 'replacement': 0})

    def test_single_step_is_not_a_macro_rule(self):
        # What one rule does at the root is left to that rule.
        props, _ = self.propose(self.i1)
        self.assertEqual(props, [])
        props, _ = self.propose(self.i2)
        self.assertEqual(props, [])

    def test_guarded_step_needs_its_facts(self):
        # (x & m) + y - y... a step whose guard fails on the instance's
        # facts is refuted by the samples: and(x, m) -> x is no step when
        # x's high bits are unknown.
        sy = synth.Synthesizer(self.be)
        ok = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                  [(0xffffff00, 0), (0xffffff00, 0xff)], [None, 0xff])
        ra = sy.add(ok, V(0))
        rb = sy.add(self.i2, V(1))
        self.assertTrue(ra and rb)
        e = ('G_SUB', 32, ('G_ADD', 32, ('G_AND', 32, V(0), V(1)), V(2)),
             ('G_AND', 32, V(0), V(1)))
        index = compose.Index(sy.rules.values())
        bad = inst(e, (32, 32, 32), [(0, 0), (0xffffff00, 0xff), (0, 0)],
                   [None, 0xff, None])
        envs = discover.instance_envs(bad, self.lim, self.ctx)
        for tgt, steps in compose.propose(bad, index, envs):
            self.assertNotIn(ra, steps)


class SelectTest(unittest.TestCase):
    """Selection logic with a fake compiler: no llc needed."""

    def setUp(self):
        self.target = targets.get('AMDGPU')
        self.names = {'A': ['A'], 'B': ['B', 'B_c1'], 'C': ['C'], 'D': ['D']}
        # Instructions a rule adds (+) or removes (-) where it fires.
        self.effect = {'A': -3, 'B': +2, 'C': 0, 'D': 0}
        self.guard = {'A': 9, 'B': 0, 'C': 5, 'D': 0}
        self.compare = {'f.ll': {'base': {'rc': 0, 'insns': 100},
                                 'synth': {'rc': 0, 'insns': 99,
                                           'matched': {'A': 1}}}}
        self._real = select.measure.compile_ll

        def fake(llc, target, path, flags=(), synth=False, disabled=(),
                 count_rules=True):
            on = [r for r, ns in self.names.items()
                  if not set(ns) & set(disabled)]
            return {'rc': 0, 'insns': 100 + sum(self.effect[r] for r in on),
                    'matched': {r: 4 for r in on},
                    'passed': {r: 1 for r in on}}
        select.measure.compile_ll = fake

    def tearDown(self):
        select.measure.compile_ll = self._real

    def refine(self, keep_unmeasured=False):
        return select.refine(None, self.target, self.compare, self.names,
                             set(self.names), self.guard, keep_unmeasured, 2,
                             log=lambda *_: None)

    def test_regression_and_unmeasured_rules_are_dropped(self):
        sel, loo, dropped, summary = self.refine()
        # B adds instructions; C queries known bits for nothing; D is free.
        self.assertEqual(sel, {'A', 'D'})
        self.assertEqual(dropped['B'][0], 'measured_regression')
        self.assertEqual(dropped['C'][0], 'no_measured_gain')
        self.assertEqual(loo['A']['insns'], -3)
        self.assertEqual(summary['insns_delta'], -3)
        self.assertEqual(summary['files_worse'], 0)

    def test_keep_unmeasured(self):
        sel, _, dropped, _ = self.refine(keep_unmeasured=True)
        self.assertEqual(sel, {'A', 'C', 'D'})
        self.assertEqual(list(dropped), ['B'])

    def test_example_function_realizes_known_bits(self):
        with open(os.path.join(ROOT, 'rules.json')) as f:
            db = json.load(f)
        r = [r for r in emit.candidates(db)
             if r['precondition'] != 'true'][0]
        name, ex = select.examples(r)[0]
        mir = select.build_mir(r, ex, name, self.target)
        self.assertIn('name: ' + name, mir)
        self.assertIn(r['source_json']['op'], mir)
        self.assertEqual(select.count(mir)[name] > 0, True)


class EmitTest(unittest.TestCase):
    def setUp(self):
        with open(os.path.join(ROOT, 'rules.json')) as f:
            self.db = json.load(f)
        self.profiles = emit.load_profiles()

    def test_deterministic(self):
        self.assertEqual(emit.emit(self.db, self.profiles),
                         emit.emit(self.db, self.profiles))

    def test_in_tree_files_up_to_date(self):
        td, inc, _ = emit.emit(self.db, self.profiles)
        llvm = os.path.dirname(os.path.dirname(ROOT))
        with open(os.path.join(llvm, 'include/llvm/Target/GlobalISel/'
                               'GISynthCombines.td')) as f:
            self.assertEqual(f.read(), td, 'run gi-rule-synth.py emit')
        with open(os.path.join(llvm, 'include/llvm/CodeGen/GlobalISel/'
                               'GISynthGeneratedPredicates.inc')) as f:
            self.assertEqual(f.read(), inc, 'run gi-rule-synth.py emit')

    def test_only_verified_cheaper_rules_emitted(self):
        td, _, _ = emit.emit(self.db, all_candidates=True)
        for r in self.db['rules']:
            self.assertEqual(r['semantic_status']['kind'],
                             'verified_refinement')
            # A rule that moves an operation to a wider type is emitted
            # only if that type fits in a register of a target.
            widens = r['class'] == 'widens_operation' and \
                emit.widened_bits(r) <= targets.NATIVE_BITS and \
                r['cost']['replacement'] < r['cost']['source']
            if (r['class'] != 'reduces_cost' and not widens) or \
                    'dominated_by' in r:
                self.assertNotIn('def %s ' % r['id'], td)
        for r in emit.candidates(self.db):
            self.assertLess(r['cost']['replacement'], r['cost']['source'])

    def test_one_use_variants(self):
        cands = emit.candidates(self.db)
        by_id = {r['id']: r for r in cands}
        variants = [r for r in cands if 'variant_of' in r]
        self.assertTrue(variants)
        for v in variants:
            base = by_id[v['variant_of']]
            # The variant follows its rule, guards every interior value of
            # the source, and exists only if the rule can fire without
            # removing an instruction.
            self.assertEqual(cands.index(v), cands.index(base) + 1)
            self.assertEqual(v['id'], base['id'] + emit.ONE_USE_SUFFIX)
            self.assertTrue(v['needs_one_use'])
            self.assertFalse(base['needs_one_use'])
            self.assertGreater(base['cost']['replacement'], 0)
            self.assertIsNone(emit.one_use_variant(v))
        td, _, _ = emit.emit(self.db, all_candidates=True)
        v = variants[0]
        body = td.split('def %s ' % v['id'])[1].split('def ')[0]
        self.assertIn('GIHasOneUse', body)

    def test_widening_candidates_fit_the_target(self):
        narrow = targets.Target('T16', [], 'x-combiner', '-x', None, None,
                                None, None, '', native_bits=16)
        wide = {r['id'] for r in emit.candidates(self.db, targets.get(
            'AMDGPU')) if r['class'] == 'widens_operation'}
        self.assertTrue(wide)
        self.assertFalse([r for r in emit.candidates(self.db, narrow)
                          if r['class'] == 'widens_operation'])
        for r in self.db['rules']:
            if r['id'] in wide:
                self.assertLessEqual(emit.widened_bits(r), 32)

    def test_symmetric_commuted_forms_are_not_repeated(self):
        by = {(r['source'], r['replacement']): r
              for r in emit.candidates(self.db)}
        # x & y -> 0 if no common bits: swapping x and y gives the same
        # rule, one record. x & y -> x if y covers x: two records.
        sym = by[('(G_AND:s32 x0 x1)', '0:s32')]
        asym = by[('(G_AND:s32 x0 x1)', 'x0')]
        self.assertEqual(emit.record_names(sym), [sym['id']])
        self.assertEqual(emit.record_names(asym),
                         [asym['id'], asym['id'] + '_c1'])
        _, _, info = emit.emit(self.db, all_candidates=True)
        self.assertLess(info['records'], info['forms_before_dedup'])

    def test_one_group_per_target_from_its_profile(self):
        td, inc, info = emit.emit(self.db, self.profiles)
        for name, prof in self.profiles.items():
            t = targets.get(name)
            self.assertIn('def %s : GICombineGroup<[' % t.group, td)
            self.assertIn('*%s[] = {' % t.names_array, inc)
            want = sum(p.get('selection') == 'emitted'
                       for p in prof['rules'].values())
            self.assertEqual(info['targets'][name]['rules'], want)
        # A rule record is emitted once even if two targets select it.
        defs = [l for l in td.splitlines() if l.startswith('def synth_')]
        self.assertEqual(len(defs), len(set(defs)))

    def test_profiles_only_select_candidates(self):
        cands = {r['id'] for r in emit.candidates(self.db)}
        for prof in self.profiles.values():
            for rid, p in prof['rules'].items():
                self.assertIn(rid, cands)
                self.assertIn(p['selection'].split(':')[0],
                              [x.split(':')[0] for x in prof['policy']] +
                              ['emitted'])


class RegenerationTest(unittest.TestCase):
    def test_synth_twice_identical(self):
        seed = os.path.join(ROOT, 'corpus', 'seed.jsonl')
        insts, _ = corpus.load([seed])
        out = []
        for _ in range(2):
            be = smt.Z3Backend()
            sy = synth.Synthesizer(be)
            ctx = discover.Context(discover.Limits())
            for i in insts:
                for c in discover.discover(i, be, ctx.limits, ctx)[0]:
                    sy.add(i, c['tgt'])
            sy.finalize(insts)
            out.append(json.dumps([synth.strip_private(sy.rules[k])
                                   for k in sorted(sy.rules)],
                                  sort_keys=True))
        self.assertEqual(out[0], out[1])
        self.assertGreater(len(json.loads(out[0])), 10)


if __name__ == '__main__':
    unittest.main()
