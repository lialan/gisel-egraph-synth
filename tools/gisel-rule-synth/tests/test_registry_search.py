"""The enumerative search is driven by the operator registry: operand
count, type rule, attribute values, result index and evaluator come from
the registry, and the search has no code for one operator."""

import os
import sys
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from girs import corpus, discover, ir, kernels, ops, smt  # noqa


def V(i):
    return ('var', i)


def inst(expr, vw, kinds=None, facts=None, consts=None):
    n = len(vw)
    return corpus.Instance(expr, vw, facts or [(0, 0)] * n,
                           consts or [None] * n, [], [],
                           [('test', 'f', '%0')], kinds=kinds)


def targets_of(cands):
    return [t for c in cands for t in ir.commuted_variants(c['tgt'])]


class ContractTest(unittest.TestCase):
    def test_every_generic_operator_has_an_answer(self):
        # Each operator says if it can be in a source and in a
        # replacement, with a reason if not.
        for info in ops.REGISTRY.values():
            self.assertTrue(info.lhs() == 'yes' or len(info.lhs()) > 8)
            self.assertTrue(info.rhs() == 'yes' or len(info.rhs()) > 8)
            if info.rhs() == 'yes':
                self.assertEqual(info.lhs(), 'yes')

    def test_a_model_is_not_enough_for_a_replacement(self):
        self.assertEqual(ops.REGISTRY['G_FREEZE'].lhs(), 'yes')
        self.assertIn('G_FREEZE', ops.REGISTRY['G_FREEZE'].rhs())
        self.assertEqual(ops.REGISTRY['G_UDIV'].lhs(), 'yes')
        self.assertIn('trap', ops.REGISTRY['G_UDIV'].rhs())
        rhs = ops.rhs_operators()
        self.assertNotIn('G_FREEZE', rhs)
        self.assertNotIn('G_UDIV', rhs)
        self.assertNotIn('G_PHI', rhs)
        for name in ('G_ICMP', 'G_SELECT', 'G_UADDO', 'G_FSHL', 'G_SITOFP',
                     'G_SEXT_INREG', 'G_UMIN'):
            self.assertIn(name, rhs)

    def test_signatures(self):
        ok = ops.signature_ok
        i1, i8, i32, f32, f64 = (1, 'i'), (8, 'i'), (32, 'i'), (32, 'f'), \
            (64, 'f')
        self.assertTrue(ok('G_ICMP:ult', i1, [i32, i32]))
        self.assertFalse(ok('G_ICMP:ult', i32, [i32, i32]))
        self.assertFalse(ok('G_ICMP:ult', i1, [i32, i8]))
        self.assertTrue(ok('G_SELECT', f32, [i1, f32, f32]))
        self.assertFalse(ok('G_SELECT', f32, [i1, f32, i32]))
        self.assertFalse(ok('G_SELECT', i32, [i1, f32, f32]))
        # A type is a width and a kind: an integer of 32 bits is not an
        # operand of a conversion from a floating-point value.
        self.assertTrue(ok('G_SITOFP', f32, [i32]))
        self.assertFalse(ok('G_SITOFP', i32, [i32]))
        self.assertFalse(ok('G_SITOFP', f32, [f32]))
        self.assertTrue(ok('G_FPTOSI', i8, [f32]))
        self.assertFalse(ok('G_FPTOSI', i8, [i32]))
        self.assertTrue(ok('G_FPEXT', f64, [f32]))
        self.assertFalse(ok('G_FPEXT', f32, [f64]))
        self.assertFalse(ok('G_ADD', f32, [f32, f32]))
        self.assertTrue(ok('G_UADDO#1', i1, [i32, i32]))
        self.assertFalse(ok('G_UADDO#2', i1, [i32, i32]))
        self.assertTrue(ok('G_SEXT_INREG:8', i32, [i32]))
        self.assertFalse(ok('G_SEXT_INREG:8', i8, [i8]))

    def test_attribute_and_result_domains(self):
        self.assertEqual(len(ops.search_keys('G_ICMP')), len(ops.PREDS))
        self.assertEqual(ops.search_keys('G_UADDO'),
                         ['G_UADDO', 'G_UADDO#1'])
        self.assertIn('G_SEXT_INREG:24', ops.search_keys('G_SEXT_INREG',
                                                         [24]))
        self.assertNotIn('G_SEXT_INREG:24', ops.search_keys('G_SEXT_INREG'))


class TypedBankTest(unittest.TestCase):
    def test_types_of_one_width_are_two_classes(self):
        # sitofp(x): the integer of 32 bits and the floating-point value
        # of 32 bits are not one search domain.
        i = inst(('G_SITOFP', 32, V(0)), (32,))
        var_cls, types, canon = discover.signature(i)
        self.assertEqual(sorted(types), [(32, 'f'), (32, 'i')])
        self.assertEqual(len(set(canon)), 2)
        ctx = discover.Context(discover.Limits())
        bank = ctx.bank(var_cls, canon, 2, discover.grammar_keys(
            ops.ENUMERATED + ('G_SITOFP', 'G_UITOFP', 'G_FPTOSI')))
        fcls = types.index((32, 'f'))
        for k in range(bank.size(2)):
            e = bank.expr(k, types)
            if not ir.is_op(e):
                continue
            # Arithmetic has integer operands, and the results of the
            # conversions to floating point are in the other class.
            info = ops.parse(e[0])[0]
            self.assertEqual(bank.cls[k] == fcls, info.fp_result,
                             ir.to_sexpr(e))
            self.assertIsNotNone(ir.type_of(e, i.vw, i.vk), ir.to_sexpr(e))

    def test_kind_from_the_type_of_the_register(self):
        # A select of floating-point values: the operators do not say the
        # kind, the type names of the corpus do.
        src = ('G_SELECT', 32, V(0), V(1), V(2))
        i = inst(src, (1, 32, 32), kinds=[None, 'f', 'f'])
        self.assertEqual(i.vk, ('i', 'f', 'f'))
        self.assertEqual(ir.type_of(src, i.vw, i.vk), (32, 'f'))
        self.assertEqual(inst(src, (1, 32, 32)).vk, ('i', 'i', 'i'))

    def test_samples_fit_the_width(self):
        import random
        rng = random.Random(3)
        for w, kind in ((1, 'i'), (8, 'i'), (16, 'f'), (32, 'f')):
            for env in discover.draw_envs([(w, kind)] * 3, 200, rng):
                self.assertTrue(all(0 <= v <= ir.mask(w) for v in env))
        # No term of a bank is a second form of a leaf.
        ctx = discover.Context(discover.Limits())
        types = ((1, 'i'), (64, 'i'))
        bank = ctx.bank((0, 1, 1), types, 1,
                        discover.grammar_keys(ops.ENUMERATED))
        forms = [ir.to_sexpr(bank.expr(k, types))
                 for k in range(bank.size(1))]
        self.assertNotIn('(G_ADD:s1 x0 0:s1)', forms)
        self.assertNotIn('(G_AND:s64 x1 -1:s64)', forms)

    def test_one_bit_class_is_exact(self):
        i = inst(('G_AND', 32, ('G_ZEXT', 32, V(0)), V(1)), (1, 32))
        self.assertEqual(discover.signature(i)[2], ((1, 'i'), (64, 'i')))


class RegistrySearchTest(unittest.TestCase):
    def setUp(self):
        self.be = smt.Z3Backend()

    def search(self, i, **kw):
        log = {}
        cands, st = discover.discover(i, self.be, discover.Limits(**kw),
                                      log=log)
        return targets_of(cands), st, log

    def test_comparison_in_a_replacement(self):
        # not(x ult y) -> x uge y: the predicate is an attribute that the
        # search enumerates.
        src = ('G_XOR', 1, ('G_ICMP:ult', 1, V(0), V(1)), ('lit', 1, '1'))
        tg, _, _ = self.search(inst(src, (32, 32)))
        self.assertIn(('G_ICMP:uge', 1, V(0), V(1)), tg)

    def test_select_in_a_replacement(self):
        # select(not c, x, y) -> select(c, y, x): an operator with three
        # operands.
        src = ('G_SELECT', 32, ('G_XOR', 1, V(0), ('lit', 1, '1')), V(1),
               V(2))
        tg, _, _ = self.search(inst(src, (1, 32, 32)))
        self.assertIn(('G_SELECT', 32, V(0), V(2), V(1)), tg)

    def test_second_result_in_a_replacement(self):
        # (x + y) ult x -> the carry of uaddo(x, y); the operator is not
        # in the source.
        src = ('G_ICMP:ult', 1, ('G_ADD', 32, V(0), V(1)), V(2))
        i = corpus.Instance(('G_ICMP:ult', 1, ('G_ADD', 32, V(0), V(1)),
                             V(0)), (32, 32), [(0, 0)] * 2, [None] * 2, [],
                            [], [('test', 'f', '%0')])
        del src
        self.assertEqual(self.search(i)[0], [])
        tg, _, _ = self.search(i, grammar='registry')
        self.assertIn(('G_UADDO#1', 1, V(0), V(1)), tg)

    def test_immediate_attribute_in_a_replacement(self):
        # ashr(shl(x, 24), 24) -> sext_inreg(x, 8): the immediate is one
        # of the values of the attribute domain.
        src = ('G_ASHR', 32, ('G_SHL', 32, V(0), V(1)), V(2))
        i = inst(src, (32, 32, 32), facts=[(0, 0), (M32 ^ 24, 24)] * 1 +
                 [(M32 ^ 24, 24)], consts=[None, 24, 24])
        tg, _, _ = self.search(i, grammar='registry')
        self.assertIn(('G_SEXT_INREG:8', 32, V(0)), tg)

    def test_float_conversion_in_a_replacement(self):
        # sitofp(sext x) -> sitofp(x): the operand type of the conversion
        # is any integer type of the instance.
        src = ('G_SITOFP', 32, ('G_SEXT', 32, V(0)))
        # The conversions have no kernel: the bank evaluates them with
        # the evaluator of the registry.
        self.assertNotIn('G_SITOFP', kernels.KERNELS)
        ctx = discover.Context(discover.Limits())
        cands, _ = discover.discover(inst(src, (16,)), self.be, ctx=ctx)
        self.assertIn(('G_SITOFP', 32, V(0)), targets_of(cands))
        self.assertGreater(ctx.stats()['generic_terms_built'], 0)
        self.assertGreater(ctx.stats()['generic_terms_evaluated'], 0)

    def test_operator_with_three_operands(self):
        src = ('G_OR', 32, ('G_SHL', 32, V(0), V(1)),
               ('G_LSHR', 32, V(2), V(3)))
        i = inst(src, (32, 32, 32, 32),
                 facts=[(0, 0), (M32 ^ 8, 8), (0, 0), (M32 ^ 24, 24)],
                 consts=[None, 8, None, 24])
        tg, _, _ = self.search(i, grammar='registry')
        self.assertIn(('G_FSHL', 32, V(0), V(2), V(1)), tg)

    def test_new_operator_needs_no_search_code(self):
        # An operator of a provider: a type rule, an evaluator and an SMT
        # encoding. No kernel and no change of the search.
        class TestOps(ops.Provider):
            namespace = 'TEST2'

            def operators(self):
                info = ops.OpInfo('G_TEST2_ANDN', 'binary', 2,
                                  namespace='TEST2')
                info.typecheck = lambda w, ws, at, r: ws == [w, w]
                info.eval = lambda w, ws, at, r, v: v[0] & ~v[1] & \
                    ops.mask(w)
                info.smt = lambda w, ws, at, r, x: (x[0] & ~x[1], None,
                                                    None)
                return [info]
        TestOps().install()
        try:
            self.assertEqual(ops.REGISTRY['G_TEST2_ANDN'].rhs(), 'yes')
            self.assertNotIn('G_TEST2_ANDN', kernels.KERNELS)
            src = ('G_AND', 32, V(0), ('G_XOR', 32, V(1),
                                       ('lit', 32, '-1')))
            i = inst(src, (32, 32))
            tg, _, _ = self.search(i, grammar='registry')
            self.assertNotIn(('G_TEST2_ANDN', 32, V(0), V(1)), tg)
            ctx = discover.Context(discover.Limits(
                grammar='registry', namespaces=('generic', 'TEST2')))
            log = {}
            cands, _ = discover.discover(i, self.be, ctx=ctx, log=log)
            self.assertIn(('G_TEST2_ANDN', 32, V(0), V(1)),
                          targets_of(cands))
            self.assertIn('G_TEST2_ANDN', log['stages'][0]['operators'])
            self.assertGreater(ctx.stats()['generic_terms_built'], 0)
        finally:
            del ops.REGISTRY['G_TEST2_ANDN']
            ops.parse.cache_clear()


class AutoGrammarTest(unittest.TestCase):
    SRC = ('G_SELECT', 32, ('G_ICMP:ult', 1, V(0), V(1)), V(0), V(1))

    def test_stages_grow(self):
        i = inst(self.SRC, (32, 32))
        st = discover.grammar_stages(i, discover.Limits(grammar='auto'))
        self.assertEqual([s[0] for s in st], ['source', 'registry'])
        self.assertLess(set(st[0][1]), set(st[1][1]))
        self.assertIn('G_SELECT', st[0][1])
        self.assertNotIn('G_UMIN', st[0][1])
        self.assertIn('G_UMIN', st[1][1])

    def test_target_stage(self):
        class Cap:
            def capable(self, name, types):
                return name in ('G_UMIN', 'G_UMAX')
        i = inst(self.SRC, (32, 32))
        lim = discover.Limits(grammar='auto', capability=Cap())
        st = discover.grammar_stages(i, lim, ((1, 'i'), (32, 'i')))
        self.assertEqual([s[0] for s in st],
                         ['source', 'target', 'registry'])
        self.assertEqual(set(st[1][1]) - set(st[0][1]),
                         {'G_UMIN', 'G_UMAX'})

    def test_auto_finds_an_operator_outside_the_source(self):
        be = smt.Z3Backend()
        i = inst(self.SRC, (32, 32))
        log = {}
        cands, st = discover.discover(
            i, be, discover.Limits(grammar='auto'), log=log)
        self.assertIn(('G_UMIN', 32, V(0), V(1)), targets_of(cands))
        # The record says what each stage searched and why it ended.
        self.assertEqual([s['stage'] for s in log['stages']],
                         ['source', 'registry'])
        self.assertEqual(log['stages'][0]['new_matches'], 0)
        self.assertGreater(log['stages'][1]['new_matches'], 0)
        for s in log['stages']:
            self.assertIn('stop', s)
            self.assertIn('operators', s)

    def test_no_candidate_in_the_source_grammar_is_not_the_end(self):
        be = smt.Z3Backend()
        i = inst(self.SRC, (32, 32))
        self.assertEqual(discover.discover(
            i, be, discover.Limits(grammar='source'))[0], [])


class BudgetTest(unittest.TestCase):
    def bank(self, cost=2, **kw):
        lim = discover.Limits(grammar='registry', **kw)
        ctx = discover.Context(lim)
        types = ((1, 'i'), (32, 'i'))
        names = discover.grammar_stages(
            inst(('G_ADD', 32, V(0), V(1)), (32, 32)), lim)[0][1]
        return ctx.bank((1, 1, 0), discover.canonical_types(types), cost,
                        discover.grammar_keys(names)), ctx

    def test_term_budget_is_shared_between_operators(self):
        # The room that is left at the level that reaches the limit goes
        # to the operators in turns, not to the first ones of the grammar.
        bank, ctx = self.bank(max_terms=1500)
        self.assertTrue(bank.truncated)
        self.assertEqual(bank.truncated_at[0], 2)
        self.assertEqual(bank.truncated_at[2], 'terms')
        self.assertLessEqual(len(bank.op), 1500)
        level = {ops.base(s[0]) for s in bank.segs if s[3] == 2}
        last = [n for n in bank.grammar][-1]
        self.assertIn(ops.base(last), level)
        self.assertGreater(len(level), 30)
        # The terms of the lower levels are as they were.
        full, _ = self.bank(cost=1)
        n = full.size(1)
        self.assertEqual(bank.op[:n], full.op)
        self.assertEqual(bank.opnds[:n], full.opnds)
        types = ((1, 'i'), (32, 'i'))
        for k in range(len(bank.op)):
            e = bank.expr(k, types)
            self.assertEqual(ir.cost(e), bank.cost[k])
            self.assertTrue(ir.is_linear(e))
        self.assertIn('terms', ctx.stats()['banks_truncated_at'][0])

    def test_samples_tell_ugt_from_uge(self):
        # Independent samples of a wide type are never equal. The samples
        # of a bank also have related values, so that it keeps both
        # comparisons.
        bank, _ = self.bank(cost=1)
        kept = {bank.op[k] for k in range(bank.size(1))}
        # `x ult y` is `y ugt x`: one of the two is in the bank.
        for a, b in (('ugt', 'ult'), ('uge', 'ule'), ('sgt', 'slt'),
                     ('sge', 'sle'), ('eq', 'eq'), ('ne', 'ne')):
            self.assertTrue({'G_ICMP:' + a, 'G_ICMP:' + b} & kept, (a, b))

    def test_evaluation_budget(self):
        bank, _ = self.bank(max_evals=20000)
        self.assertTrue(bank.truncated)
        self.assertEqual(bank.truncated_at[2], 'evaluations')

    def test_no_budget_reached(self):
        bank, _ = self.bank(cost=1)
        self.assertFalse(bank.truncated)
        self.assertEqual(bank.starved, [])

    def test_search_reports_the_budget(self):
        be = smt.Z3Backend()
        src = ('G_ADD', 32, ('G_ADD', 32, ('G_ADD', 32, V(0), V(1)), V(2)),
               V(3))
        log = {}
        _, st = discover.discover(
            inst(src, (32,) * 4), be,
            discover.Limits(grammar='registry', max_terms=3000), log=log)
        self.assertEqual(st['stop'], 'bank_truncated')
        self.assertIn('bank_truncated: terms', log['stages'][0]['stop'])


M32 = ir.mask(32)

if __name__ == '__main__':
    unittest.main()
