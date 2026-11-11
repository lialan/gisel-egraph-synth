"""Rules for two roots (girs/sibling.py): the root of a tree and a second
instruction of the block that reads inputs of the tree. The pairs come
from the registers of the corpus records, the search builds the
replacements from the operators, and the proof has both roots in one
query."""

import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from girs import corpus, discover, emit, ir, precond, region, sibling  # noqa
from girs import smt, synth  # noqa


def V(i):
    return ('var', i)


def node(op, w, reg, args, uses=1, **kw):
    return dict({'op': op, 'w': w, 'type': 'i%d' % w, 'reg': reg,
                 'zero': '0x0', 'one': '0x0', 'noundef': False,
                 'uses': uses, 'flags': [], 'args': args}, **kw)


def inp(reg, w, const=None):
    d = {'reg': reg, 'w': w, 'type': 'i%d' % w, 'zero': '0x0',
         'one': '0x0', 'noundef': const is not None, 'def': 'COPY'}
    if const is not None:
        d.update(const=hex(const), zero=hex(~const & ((1 << w) - 1)),
                 one=hex(const), **{'def': 'G_CONSTANT'})
    return d


def rec(expr, inputs, bb=0, fn='f'):
    return {'fn': fn, 'bb': bb, 'root': expr['reg'], 'interior': 1,
            'expr': expr, 'inputs': inputs}


def IN(i):
    return {'in': i}


def write(records):
    f = tempfile.NamedTemporaryFile('w', suffix='.jsonl', delete=False)
    for r in records:
        f.write(json.dumps(r) + '\n')
    f.close()
    return f.name


def pairs_of(records):
    path = write(records)
    try:
        stats = {}
        return sibling.load_pairs([path], stats), stats
    finally:
        os.unlink(path)


XY = [inp('%x', 32), inp('%y', 32)]
SUB = rec(node('G_SUB', 32, '%d', [IN(0), IN(1)]), XY)
ULT = rec(node('G_ICMP', 1, '%c', [IN(0), IN(1)], pred='ult'), XY)
# select (icmp uge x, y), a, b
SEL_IN = XY + [inp('%a', 32), inp('%b', 32)]
SEL = rec(node('G_SELECT', 32, '%s', [
    node('G_ICMP', 1, '%c', [IN(0), IN(1)], pred='uge'), IN(2), IN(3)]),
    SEL_IN)


def env():
    backend = smt.Z3Backend()
    lim = discover.Limits(grammar='registry')
    return backend, lim, discover.Context(lim), synth.Synthesizer(
        backend, synth.SynthLimits())


def run(records, found=None):
    backend, lim, ctx, sy = env()
    pairs, _ = pairs_of(records)
    stats = sibling.extend(sy, pairs, found or {}, backend, lim, ctx)
    return [synth.strip_private(r) for r in sy.rules.values()], stats


class PairsTest(unittest.TestCase):
    def test_two_roots_of_one_block_with_the_same_inputs(self):
        pairs, stats = pairs_of([SUB, ULT])
        # Each of the two is the primary root of one pair.
        self.assertEqual(stats['pairs'], 2)
        self.assertEqual(sorted(ir.to_sexpr(p.sib) for p in pairs),
                         ['(G_ICMP:ult:s1 x0 x1)', '(G_SUB:s32 x0 x1)'])

    def test_the_sibling_has_the_variables_of_the_primary_tree(self):
        # The comparison reads (y, x): its variables are numbered by the
        # registers of the tree of the subtraction.
        ugt = rec(node('G_ICMP', 1, '%c', [IN(0), IN(1)], pred='ugt'),
                  [inp('%y', 32), inp('%x', 32)])
        pairs, _ = pairs_of([SUB, ugt])
        p = [p for p in pairs if p.inst.expr[0] == 'G_SUB'][0]
        self.assertEqual(p.sib, ('G_ICMP:ugt', 1, V(1), V(0)))

    def test_another_block_is_not_a_pair(self):
        other = dict(ULT, bb=1)
        self.assertEqual(pairs_of([SUB, other])[0], [])

    def test_another_function_is_not_a_pair(self):
        other = dict(ULT, fn='g')
        self.assertEqual(pairs_of([SUB, other])[0], [])

    def test_a_sibling_reads_only_inputs_of_the_tree(self):
        other = rec(node('G_ICMP', 1, '%c', [IN(0), IN(1)], pred='ult'),
                    [inp('%x', 32), inp('%z', 32)])
        self.assertEqual(pairs_of([SUB, other])[0], [])

    def test_a_sibling_is_one_instruction(self):
        deep = rec(node('G_ZEXT', 64, '%z', [
            node('G_ICMP', 1, '%c', [IN(0), IN(1)], pred='ult')]), XY)
        pairs, _ = pairs_of([SUB, deep])
        # The deep tree is a primary root; it is not a sibling.
        self.assertEqual([ir.to_sexpr(p.sib) for p in pairs],
                         ['(G_SUB:s32 x0 x1)'])

    def test_an_instruction_of_the_tree_is_not_a_sibling(self):
        cmp_ = rec(node('G_ICMP', 1, '%c', [IN(0), IN(1)], pred='uge'), XY)
        pairs, _ = pairs_of([SEL, cmp_])
        self.assertFalse([p for p in pairs if p.inst.expr[0] == 'G_SELECT'])

    def test_two_results_of_one_instruction_are_not_a_pair(self):
        r0 = rec(node('G_USUBO', 32, '%d', [IN(0), IN(1)], res=0,
                      mi='%d'), XY)
        r1 = rec(node('G_USUBO', 1, '%o', [IN(0), IN(1)], res=1,
                      mi='%d'), XY)
        self.assertEqual(pairs_of([r0, r1])[0], [])

    def test_a_definition_of_an_input_is_not_a_sibling(self):
        # %y = G_ZEXT %w is an input of the tree, not a second root.
        tree = rec(node('G_ADD', 32, '%s', [IN(0), IN(1)]),
                   [inp('%y', 32), inp('%w', 32)])
        zext = rec(node('G_TRUNC', 32, '%y', [IN(0)]), [inp('%w', 64)])
        tree['inputs'][1] = inp('%w', 64)
        tree['expr'] = node('G_ADD', 32, '%s', [
            IN(0), node('G_TRUNC', 32, '%t', [IN(1)])])
        pairs, _ = pairs_of([tree, zext])
        self.assertFalse([p for p in pairs if p.inst.expr[0] == 'G_ADD'])

    def test_users_of_a_value_below_the_root_make_another_pair(self):
        # The comparison of the second select has another user: it stays,
        # so the pair has another cost and is searched on its own.
        shared = json.loads(json.dumps(SEL))
        shared['fn'] = 'g'
        shared['expr']['args'][0]['uses'] = 2
        pairs, _ = pairs_of([SEL, SUB, shared, dict(SUB, fn='g')])
        sel = [p for p in pairs if p.inst.expr[0] == 'G_SELECT']
        self.assertEqual(sorted(p.inst.interior_uses for p in sel),
                         [(1,), (2,)])
        rules, stats = run([SEL, SUB, shared, dict(SUB, fn='g')])
        r = [r for r in rules if r['source'].startswith('(G_SELECT')]
        # One rule, from the pair whose comparison has one user.
        self.assertEqual(len(r), 1)
        self.assertEqual(r[0]['support']['occurrences'], 1)
        self.assertFalse(r[0]['needs_one_use'])

    def test_occurrences(self):
        again = [dict(SUB, fn='g'), dict(ULT, fn='g')]
        pairs, stats = pairs_of([SUB, ULT] + again)
        self.assertEqual(stats['distinct'], 2)
        self.assertEqual([len(p.prov) for p in pairs], [2, 2])


class SearchTest(unittest.TestCase):
    def test_one_instruction_for_two_roots(self):
        rules, stats = run([SUB, ULT])
        r = [r for r in rules if r['source'].startswith('(G_SUB')]
        self.assertEqual(len(r), 1, rules)
        r = r[0]
        self.assertEqual(r['replacement'],
                         '(G_USUBO:s32 x0 x1); (G_ICMP:ult:s1 x0 x1) = '
                         '(G_USUBO#1:s1 x0 x1)')
        self.assertEqual(r['cost'], {'source': 2, 'replacement': 1})
        self.assertEqual(r['precondition'], 'true')
        self.assertEqual(r['provenance']['discovery'], 'joint-sibling+smt')
        # Every width of the schedule, in one joint proof each.
        self.assertGreater(len(r['disjuncts'][0]['width_maps']), 1)
        self.assertTrue(all(p['outputs'] == 2
                            for p in r['disjuncts'][0]['proofs']))

    def test_the_other_result_feeds_the_replacement_of_the_root(self):
        # select (x uge y), a, b and x - y: the borrow of one G_USUBO is
        # the negated condition, so the select exchanges its values.
        rules, _ = run([SEL, SUB])
        r = [r for r in rules if r['source'].startswith('(G_SELECT')]
        self.assertEqual(len(r), 1, rules)
        self.assertEqual(
            r[0]['replacement'],
            '(G_SELECT:s32 (G_USUBO#1:s1 x0 x1) x3 x2); (G_SUB:s32 x0 x1) '
            '= (G_USUBO:s32 x0 x1)')
        self.assertEqual(r[0]['cost'], {'source': 3, 'replacement': 2})

    def test_a_sibling_that_stays_gives_its_results(self):
        # x + y next to the overflow result of G_UADDO x, y: the sum is
        # the other result of the instruction that is there.
        add = rec(node('G_ADD', 32, '%s', [IN(0), IN(1)]), XY)
        ov = rec(node('G_UADDO', 1, '%o', [IN(0), IN(1)], res=1,
                      mi='%u'), XY)
        rules, _ = run([add, ov])
        r = [r for r in rules if r['source'].startswith('(G_ADD')]
        self.assertEqual(len(r), 1, rules)
        self.assertEqual(r[0]['replacement'],
                         '(G_UADDO:s32 x0 x1); (G_UADDO#1:s1 x0 x1) stays')
        self.assertTrue(r[0]['region']['siblings'][0]['stays'])
        self.assertEqual(r[0]['cost'], {'source': 2, 'replacement': 1})

    def test_no_rule_without_a_shared_instruction(self):
        # Two roots with no cheaper joint form.
        xor = rec(node('G_XOR', 32, '%e', [IN(0), IN(1)]), XY)
        rules, stats = run([SUB, xor])
        self.assertEqual(rules, [])
        self.assertEqual(stats['pairs'], 2)

    def test_a_rule_of_the_root_alone_is_the_limit(self):
        # With a rule of the root alone that is as cheap, the pair gives
        # nothing new.
        backend, lim, ctx, sy = env()
        pairs, _ = pairs_of([SEL, SUB])
        pair = [p for p in pairs if p.inst.expr[0] == 'G_SELECT'][0]
        free = {pair.inst.key(): [V(2)]}    # a (wrong) free replacement
        stats = sibling.extend(sy, [pair], free, backend, lim, ctx)
        self.assertEqual(stats['rules'], 0)

    def test_a_precondition_on_a_constant(self):
        # select (x uge y), a + 1, a and x - y: a - (-1) - borrow. The
        # rule needs the constant 1.
        ins = XY + [inp('%a', 32), inp('%one', 32, 1)]
        sel = rec(node('G_SELECT', 32, '%s', [
            node('G_ICMP', 1, '%c', [IN(0), IN(1)], pred='uge'),
            node('G_ADD', 32, '%p', [IN(2), IN(3)]), IN(2)]), ins)
        rules, _ = run([sel, SUB])
        r = [r for r in rules if r['source'].startswith('(G_SELECT')]
        self.assertEqual(len(r), 1, rules)
        self.assertEqual(r[0]['precondition'], 'x3 == 1')
        self.assertIn('G_USUBE', r[0]['replacement'])
        self.assertEqual(r[0]['support']['training_constants'],
                         {'x3': ['0x1']})

    def test_support_counts_the_occurrences(self):
        rules, stats = run([SUB, ULT, dict(SUB, fn='g'), dict(ULT, fn='g')])
        r = [r for r in rules if r['source'].startswith('(G_SUB')][0]
        self.assertEqual(r['support']['occurrences'], 2)
        self.assertEqual(r['support']['examples'][0]['sibling'], '%c')


class ProofTest(unittest.TestCase):
    def rule(self):
        rules, _ = run([SEL, SUB])
        return [r for r in rules if r['source'].startswith('(G_SELECT')][0]

    def check(self, rule):
        backend = smt.Z3Backend()
        d = rule['disjuncts'][0]
        pred = tuple(precond.atom_from_json(a) for a in d['pred_json'])
        sched = region.schedules(rule, d['width_maps'])
        if None in sched:
            return 'structural'
        return region.verify(sched, [pred], backend)[0]

    def test_a_stored_rule_is_proved_again(self):
        r = self.rule()
        self.assertTrue(sibling.structural(r))
        self.assertEqual(self.check(r), 'valid')

    def test_a_wrong_replacement_of_the_root_is_refuted(self):
        r = self.rule()
        # The values of the select not exchanged.
        t = ir.from_json(r['replacement_json'])
        r['replacement_json'] = ir.to_json(t[:3] + (t[4], t[3]))
        self.assertEqual(self.check(r), 'invalid')

    def test_a_wrong_replacement_of_the_sibling_is_refuted(self):
        r = self.rule()
        s = r['region']['siblings'][0]
        b = ir.from_json(s['replacement_json'])
        s['replacement_json'] = ir.to_json(b[:2] + (b[3], b[2]))
        self.assertEqual(self.check(r), 'invalid')

    def test_structural_conditions(self):
        r = self.rule()
        s = r['region']['siblings'][0]
        # A replacement that reads an input twice.
        bad = dict(r, replacement_json=ir.to_json(
            ('G_ADD', 32, ir.from_json(r['replacement_json']), V(0))))
        self.assertFalse(sibling.structural(bad))
        # A sibling that is not one instruction over inputs.
        deep = dict(r, region=dict(r['region'], siblings=[dict(
            s, source_json=ir.to_json(
                ('G_SUB', 32, ('G_ADD', 32, V(0), V(1)), V(1))))]))
        self.assertFalse(sibling.structural(deep))
        # A sibling with several results that is replaced.
        multi = dict(r, region=dict(r['region'], siblings=[dict(
            s, source_json=ir.to_json(('G_USUBO#1', 1, V(0), V(1))))]))
        self.assertFalse(sibling.structural(multi))

    def test_undefined_behaviour_of_a_root_is_of_the_source(self):
        # The source of the joint formula has undefined behaviour if one
        # of its roots has: a division next to the root excuses the
        # replacement for a zero divisor.
        enc = smt.Encoder((32, 32), 32)
        div = ('G_UDIV', 32, V(0), V(1))
        pairs = [(('G_ADD', 32, V(0), V(1)), ('G_ADD', 32, V(0), V(1))),
                 (div, div)]
        import z3
        f = smt.joint_violation(enc, pairs, z3.BoolVal(True))
        self.assertEqual(smt.Z3Backend().check(f).status, 'unsat')


class AtomTest(unittest.TestCase):
    def test_the_constant_one(self):
        a = ('one', 0)
        self.assertIn(a, precond.enumerate_atoms((32,), 32))
        self.assertTrue(precond.eval_atom(a, [(0xfffffffe, 1)], (32,)))
        self.assertFalse(precond.eval_atom(a, [(0xfffffffc, 1)], (32,)))
        self.assertFalse(precond.eval_atom(a, [(0xfffffffd, 2)], (32,)))
        # One bit: the constant 1 has no known zero.
        self.assertTrue(precond.eval_atom(a, [(0, 1)], (1,)))
        self.assertEqual(precond.atom_from_json(precond.atom_to_json(a)), a)
        self.assertEqual(precond.rename_atom(a, {0: 3}), ('one', 3))
        self.assertEqual(precond.atom_vars(a), [0])
        self.assertEqual(precond.atom_str(a), 'x0 == 1')
        self.assertIn('getConstant().isOne()', precond.cpp_atom(a))

    def test_the_formula_says_that_the_value_is_one(self):
        import z3
        enc = smt.Encoder((8,), 8)
        f = z3.And(enc.well_formed(), precond.z3_atom(('one', 0), enc),
                   enc.x[0] != 1)
        self.assertEqual(smt.Z3Backend().check(f).status, 'unsat')


class EmitTest(unittest.TestCase):
    def rules(self):
        add = rec(node('G_ADD', 32, '%s', [IN(0), IN(1)]), XY)
        ov = rec(node('G_UADDO', 1, '%o', [IN(0), IN(1)], res=1,
                      mi='%u'), XY)
        rules, _ = run([SEL, SUB, add, ov])
        both = [r for r in rules if r['source'].startswith('(G_SELECT')][0]
        stays = [r for r in rules if r['source'].startswith('(G_ADD')][0]
        return both, stays

    def test_emittable(self):
        for r in self.rules():
            self.assertIsNone(emit.why_not_emittable(r), r['id'])

    def test_the_finder_matches_the_sibling(self):
        both, stays = self.rules()
        f = emit._cpp_sibling(both)
        self.assertIn('findSiblingRoot(MRI, Root, X0,', f)
        self.assertIn('MI.getOpcode() == TargetOpcode::G_SUB', f)
        self.assertIn('MI.getOperand(1).getReg() == X0 && '
                      'MI.getOperand(1 + 1).getReg() == X1', f)
        # Not the comparison of the tree of the root.
        self.assertIn('!is_contained({T0}, MI.getOperand(0).getReg())', f)
        # G_UADDO is commutative and has two results before its operands.
        f = emit._cpp_sibling(stays)
        self.assertIn('MI.getOperand(2).getReg() == X0 && '
                      'MI.getOperand(2 + 1).getReg() == X1', f)
        self.assertIn('MI.getOperand(2).getReg() == X1 && '
                      'MI.getOperand(2 + 1).getReg() == X0', f)

    def test_the_finder_of_a_comparison_has_the_swapped_form(self):
        rules, _ = run([SUB, ULT])
        r = [r for r in rules if r['source'].startswith('(G_SUB')][0]
        f = emit._cpp_sibling(r)
        self.assertIn('getPredicate() == CmpInst::ICMP_ULT && '
                      'MI.getOperand(2).getReg() == X0', f)
        self.assertIn('getPredicate() == CmpInst::ICMP_UGT && '
                      'MI.getOperand(2).getReg() == X1', f)

    def test_guard(self):
        both, stays = self.rules()
        g = emit._cpp_guard(both)
        self.assertIn('MachineInstr *Sib = Root ? sibling_%s(MRI, *Root, '
                      'X0, X1, X2, X3, T0) : nullptr;' % both['id'], g)
        # The width of the sibling is a column of the proved widths.
        self.assertIn('getScalarWidths(MRI, {X0, X1, X2, X3, T0, Dst, SR0}'
                      ', W)', g)
        self.assertIn('{32, 32, 32, 32, 1, 32, 32}', g)
        self.assertIn('siblingInsertPoint(*Root, *Sib, {X0, X1, X2, X3}, '
                      '/*SibStays=*/false)', g)
        g = emit._cpp_guard(stays)
        # The overflow result of the sibling has one bit at every width.
        self.assertIn('getScalarWidths(MRI, {X0, X1, Dst, SR0, SR1}, W)', g)
        self.assertIn('{32, 32, 32, 32, 1}', g)
        self.assertIn('{64, 64, 64, 64, 1}', g)
        self.assertIn('/*SibStays=*/true)', g)

    def test_apply_replaces_both_roots(self):
        both, _ = self.rules()
        a = emit._cpp_apply(both)
        self.assertIn('B.buildInstr(TargetOpcode::G_USUBO, {SR0, '
                      'MRI.getType(T0)}, {X0, X1})', a)
        self.assertIn('/*SibStays=*/false, /*Move=*/true)', a)
        self.assertIn('Sib->eraseFromParent();', a)
        self.assertIn('Root.eraseFromParent();', a)
        # The select takes the borrow of the new instruction.
        self.assertRegex(a, r'buildInstr\(TargetOpcode::G_SELECT, \{Dst\}, '
                            r'\{N\d+\.getReg\(1\), X3, X2\}\)')

    def test_apply_reads_a_sibling_that_stays(self):
        _, stays = self.rules()
        a = emit._cpp_apply(stays)
        self.assertIn('MachineInstrBuilder NSib(B.getMF(), Sib);', a)
        self.assertIn('B.buildCopy(Dst, NSib.getReg(0));', a)
        self.assertNotIn('Sib->eraseFromParent', a)
        self.assertNotIn('G_UADDO, {', a)

    def test_inc_has_the_finder_before_the_guard(self):
        both, stays = self.rules()
        db = {'rules': [both, stays]}
        _, inc, info = emit.emit(db, all_candidates=True)
        self.assertEqual(info['rules'], 2)
        for r in (both, stays):
            self.assertLess(inc.index('inline MachineInstr *sibling_' +
                                      r['id']),
                            inc.index('inline bool guard_' + r['id']))

    def test_single_root_rules_are_unchanged(self):
        with open(os.path.join(os.path.dirname(__file__), '..',
                               'rules.json')) as f:
            db = json.load(f)
        _, inc, _ = emit.emit(db, all_candidates=True)
        self.assertNotIn('findSiblingRoot', inc)
        self.assertNotIn('Sib', inc)


if __name__ == '__main__':
    unittest.main()
