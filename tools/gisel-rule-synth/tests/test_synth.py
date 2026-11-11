"""Unit tests for llvm/utils/gisel-rule-synth.

Run:  python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests
(needs the z3 Python module).
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

from girs import corpus, discover, emit, ir, precond, smt, synth  # noqa


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
        i = inst(('G_ADD', 32, V(0), V(1)), (32, 32), [(0, 0), (0, 0)])
        envs = discover.sample_envs(i, 8, random.Random(0))
        by_cost = discover.enumerate_terms(i, envs, 1, self.lim)
        for ts in by_cost.values():
            for t in ts:
                self.assertTrue(ir.is_linear(t.expr), ir.to_sexpr(t.expr))

    def test_sampled_match_refuted_by_smt(self):
        # With 2 samples, x and (x & 0x7fffffff) can agree on the samples;
        # the concrete SMT proof must still reject the candidate.
        i = inst(('G_AND', 32, V(0), V(1)), (32, 32),
                 [(0, 0), (0x80000000, 0x7fffffff)], [None, 0x7fffffff])
        r = discover.prove_concrete(i, V(0), self.be)
        self.assertEqual(r.status, 'sat')


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
        # (x & 0) -> (0 >> y): equal values, but the replacement is poison
        # for y >= width. Rejected unconditionally, valid if y < width.
        src = ('G_AND', 32, V(0), L(32, '0'))
        tgt = ('G_LSHR', 32, L(32, '0'), V(1))
        sched = synth.schedules(src, tgt, (32, 32), self.lim)
        st, _ = synth.verify(sched, (), self.be)
        self.assertEqual(st, 'invalid')
        st, _ = synth.verify(sched, (('ltw', 1, 0),), self.be)
        self.assertEqual(st, 'valid')

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


class EmitTest(unittest.TestCase):
    def setUp(self):
        with open(os.path.join(ROOT, 'rules.json')) as f:
            self.db = json.load(f)

    def test_deterministic(self):
        self.assertEqual(emit.emit(self.db), emit.emit(self.db))

    def test_in_tree_files_up_to_date(self):
        td, inc = emit.emit(self.db)
        llvm = os.path.dirname(os.path.dirname(ROOT))
        with open(os.path.join(llvm, 'include/llvm/Target/GlobalISel/'
                               'GISynthCombines.td')) as f:
            self.assertEqual(f.read(), td, 'run gi-rule-synth.py emit')
        with open(os.path.join(llvm, 'include/llvm/CodeGen/GlobalISel/'
                               'GISynthGeneratedPredicates.inc')) as f:
            self.assertEqual(f.read(), inc, 'run gi-rule-synth.py emit')

    def test_only_verified_cheaper_rules_emitted(self):
        td, _ = emit.emit(self.db)
        for r in self.db['rules']:
            self.assertEqual(r['semantic_status']['kind'],
                             'verified_refinement')
        for r in self.db['equal_cost']:
            self.assertNotIn('def %s ' % r['id'], td)

    def test_commuted_variants_emitted(self):
        td, _ = emit.emit(self.db)
        and_rules = [r for r in emit.emitted_rules(self.db)
                     if r['source'].startswith('(G_AND:s32 x0 x1)')]
        self.assertTrue(and_rules)
        self.assertIn('def %s_c1 ' % and_rules[0]['id'], td)


class RegenerationTest(unittest.TestCase):
    def test_synth_twice_identical(self):
        seed = os.path.join(ROOT, 'corpus', 'seed.jsonl')
        insts, _ = corpus.load([seed])
        out = []
        for _ in range(2):
            be = smt.Z3Backend()
            sy = synth.Synthesizer(be)
            for i in insts:
                for c in discover.discover(i, be, discover.Limits())[0]:
                    sy.add(i, c['tgt'])
            sy.finalize()
            rules = {k: (v['source'], v['replacement'], v['precondition'],
                         v['semantic_status']['schedules'])
                     for k, v in sy.rules.items()}
            out.append(rules)
        self.assertEqual(out[0], out[1])
        self.assertGreater(len(out[0]), 10)


if __name__ == '__main__':
    unittest.main()
