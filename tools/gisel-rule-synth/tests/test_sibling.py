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
        # One rule, from the pair whose comparison has one user. Two new
        # instructions replace the select and the subtract: the rule does
        # not need to remove the comparison.
        self.assertEqual(len(r), 1)
        self.assertEqual(r[0]['support']['occurrences'], 1)
        self.assertEqual(r[0]['region']['dead_nodes'], [])
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
        # The literal -1 of the replacement has the width of the matched
        # type, not the width of the stored pattern: the rule is proved
        # at other widths too.
        self.assertIn('-1:s32', r[0]['replacement'])
        self.assertGreater(len(r[0]['disjuncts'][0]['width_maps']), 1)
        a = emit._cpp_apply(r[0])
        self.assertRegex(a, r'B\.buildConstant\(MRI\.getType\((\w+)\), '
                            r'APInt::getAllOnes\(MRI\.getType\(\1\)\.'
                            r'getScalarSizeInBits\(\)\)\)')
        self.assertNotIn('APInt(32', a)

    def test_support_counts_the_occurrences(self):
        rules, stats = run([SUB, ULT, dict(SUB, fn='g'), dict(ULT, fn='g')])
        r = [r for r in rules if r['source'].startswith('(G_SUB')][0]
        self.assertEqual(r['support']['occurrences'], 2)
        self.assertEqual(r['support']['examples'][0]['siblings'], ['%c'])


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

    def test_the_guard_finds_the_sibling(self):
        both, stays = self.rules()
        g = emit._cpp_guard(both)
        self.assertIn('MachineInstr *Sib0 = findSiblingRoot(\n'
                      '      MRI, *Root, X0,', g)
        self.assertIn('MI.getOpcode() != TargetOpcode::G_SUB', g)
        self.assertIn('MI.getOperand(1).getReg() == X0 &&\n'
                      '            MI.getOperand(1 + 1).getReg() == X1', g)
        # Not the comparison of the tree of the root, and not a sibling
        # that the plan has.
        self.assertIn('/*MaxUsers=*/8, {T0}, Plan.Sibs);', g)
        self.assertIn('Plan.Sibs.push_back(Sib0);', g)
        # G_UADDO is commutative and has two results before its operands.
        g = emit._cpp_guard(stays)
        self.assertIn('MI.getOperand(2).getReg() == X0 &&\n'
                      '            MI.getOperand(2 + 1).getReg() == X1', g)
        self.assertIn('MI.getOperand(2).getReg() == X1 &&\n'
                      '            MI.getOperand(2 + 1).getReg() == X0', g)

    def test_the_sibling_that_is_a_comparison_has_the_swapped_form(self):
        rules, _ = run([SUB, ULT])
        r = [r for r in rules if r['source'].startswith('(G_SUB')][0]
        g = emit._cpp_guard(r)
        self.assertIn('getPredicate() == CmpInst::ICMP_ULT &&\n'
                      '            MI.getOperand(2).getReg() == X0', g)
        self.assertIn('getPredicate() == CmpInst::ICMP_UGT &&\n'
                      '            MI.getOperand(2).getReg() == X1', g)

    def test_guard(self):
        both, stays = self.rules()
        g = emit._cpp_guard(both)
        # The match step fills the plan.
        self.assertIn('RegionPlan &Plan, Register Dst, Register X0, '
                      'Register X1, Register X2, Register X3, Register T0)',
                      g)
        self.assertIn('Plan = RegionPlan();', g)
        # The width of the sibling is a column of the proved widths.
        self.assertIn('getScalarWidths(MRI, {X0, X1, X2, X3, T0, Dst, S0R0}'
                      ', W)', g)
        self.assertIn('{32, 32, 32, 32, 1, 32, 32}', g)
        self.assertIn('planRegion(*Root, Plan, /*Stays=*/0, '
                      '{X0, X1, X2, X3})', g)
        # Two new instructions replace the two roots: the rule does not
        # need to remove the comparison below the root.
        self.assertEqual(both['region']['dead_nodes'], [])
        self.assertNotIn('hasNUses', g)
        g = emit._cpp_guard(stays)
        # The overflow result of the sibling has one bit at every width.
        self.assertIn('getScalarWidths(MRI, {X0, X1, Dst, S0R0, S0R1}, W)',
                      g)
        self.assertIn('{32, 32, 32, 32, 1}', g)
        self.assertIn('{64, 64, 64, 64, 1}', g)
        # The sibling stays: bit 0. Its operands are defined before the
        # position, because the apply step can move it.
        self.assertIn('planRegion(*Root, Plan, /*Stays=*/1, {X0, X1})', g)
        self.assertNotIn('hasNUses', g)

    def test_apply_replaces_both_roots(self):
        both, _ = self.rules()
        a = emit._cpp_apply(both)
        self.assertIn('const RegionPlan &Plan', a)
        self.assertIn('B.setInstrAndDebugLoc(applyRegionPlan(Plan));', a)
        self.assertIn('MachineInstr *Sib0 = Plan.Sibs[0];', a)
        self.assertIn('B.buildInstr(TargetOpcode::G_USUBO, {S0R0, '
                      'MRI.getType(T0)}, {X0, X1})', a)
        self.assertIn('Sib0->eraseFromParent();', a)
        self.assertIn('Root.eraseFromParent();', a)
        # The replacements read the comparison of the tree of the root
        # (T0), which stays: the proof has it without flags.
        self.assertIn('dropFlags(B, *MRI.getVRegDef(T0));', a)
        self.assertNotIn('dropFlags(B, *Sib0)', a)
        # The apply step does not search: the match step did.
        self.assertNotIn('findSiblingRoot', a)
        self.assertNotIn('planRegion', a)
        # The select takes the borrow of the new instruction.
        self.assertRegex(a, r'buildInstr\(TargetOpcode::G_SELECT, \{Dst\}, '
                            r'\{N\d+\.getReg\(1\), X3, X2\}\)')

    def test_the_example_function_has_every_root(self):
        # The probe of a rule runs it on its own example: the function
        # has the sibling and a user of each output, else the rule never
        # applies there.
        from girs import select, targets
        both, stays = self.rules()
        t = targets.get('AMDGPU')
        name, ex = select.examples(both)[0]
        mir = select.build_mir(both, ex, name, t)
        lines = [ln.strip() for ln in mir.splitlines()]
        sub = [ln for ln in lines if '= G_SUB ' in ln]
        cmp_ = [ln for ln in lines if '= G_ICMP intpred(uge), ' in ln]
        self.assertEqual(len(sub), 1)
        self.assertEqual(len(cmp_), 1)
        # The two roots read the same two registers.
        self.assertEqual(sub[0].split('G_SUB ')[1],
                         cmp_[0].split('intpred(uge), ')[1])
        reg = sub[0].split(':')[0]
        self.assertIn('$vgpr1 = COPY ' + reg, lines)
        self.assertIn('SI_RETURN implicit $vgpr0, implicit $vgpr1', lines)
        # A sibling that stays has several results: one instruction.
        name, ex = select.examples(stays)[0]
        mir = select.build_mir(stays, ex, name, t)
        self.assertEqual(mir.count('= G_UADDO '), 1)
        self.assertEqual(mir.count('= G_ADD '), 1)
        # The 1-bit output goes through a G_ANYEXT to its register.
        self.assertEqual(mir.count('= G_ANYEXT '), 1)
        self.assertEqual(select.count(mir)[name], 3)

    def test_apply_reads_a_sibling_that_stays(self):
        _, stays = self.rules()
        a = emit._cpp_apply(stays)
        self.assertIn('MachineInstrBuilder NSib0(B.getMF(), Sib0);', a)
        self.assertIn('B.buildCopy(Dst, NSib0.getReg(0));', a)
        self.assertNotIn('Sib0->eraseFromParent', a)
        self.assertNotIn('releaseResults(MRI, *Sib0)', a)
        self.assertIn('releaseResults(MRI, Root);', a)
        self.assertNotIn('G_UADDO, {', a)
        # The replacement reads the sibling that stays: the proof has it
        # without flags (an addition with nuw is poison where the proof
        # has a value).
        self.assertIn('dropFlags(B, *Sib0);', a)

    def test_the_rule_record_has_the_plan(self):
        both, stays = self.rules()
        db = {'rules': [both, stays]}
        td, inc, info = emit.emit(db, all_candidates=True)
        self.assertEqual(info['rules'], 2)
        self.assertEqual(td.count('def gisynth_region_plan : '
                                  'GIDefMatchData<"gisynth::RegionPlan">;'),
                         1)
        self.assertIn('(defs root:$dst, gisynth_region_plan:$plan),', td)
        for r in (both, stays):
            self.assertIn('gisynth::guard_%s(MRI, Helper.getValueTracking(), '
                          '${plan}, ${dst}.getReg(),' % r['id'], td)
            self.assertIn('gisynth::apply_%s(B, *${dst}.getParent(), '
                          '${plan}, ${dst}.getReg(),' % r['id'], td)
        # The guard counts the users: a sibling is a user too.
        self.assertNotIn('GIHasOneUse', td)

    def test_single_root_rules_are_unchanged(self):
        with open(os.path.join(os.path.dirname(__file__), '..',
                               'rules.json')) as f:
            db = json.load(f)
        td, inc, _ = emit.emit(db, all_candidates=True)
        self.assertNotIn('findSiblingRoot', inc)
        self.assertNotIn('Sib', inc)
        self.assertNotIn('RegionPlan', inc)
        self.assertNotIn('gisynth_region_plan', td)


class WiderRegionTest(unittest.TestCase):
    """Regions with more than two roots, with a sibling that reads a value
    below the root, and with an input that only a sibling reads."""

    # and (add x, y), m; icmp ult (add x, y), x: the sum has two users.
    AND = rec(node('G_AND', 32, '%r', [
        node('G_ADD', 32, '%t', [IN(0), IN(1)], uses=2), IN(2)]),
        XY + [inp('%m', 32)])
    CARRY = rec(node('G_ICMP', 1, '%c', [
        node('G_ADD', 32, '%t', [IN(0), IN(1)], uses=2), IN(0)],
        pred='ult'), XY)

    def test_two_siblings(self):
        ult = rec(node('G_ICMP', 1, '%c2', [IN(0), IN(1)], pred='ult'), XY)
        rules, stats = run([SEL, SUB, ult])
        self.assertEqual(stats['rules_with_two_siblings'], 1)
        r = [r for r in rules if len(r['region']['siblings']) == 2][0]
        # The siblings are in the order of their expressions.
        text = ('(G_SELECT:s32 (G_USUBO#1:s1 x0 x1) x3 x2); '
                '(G_ICMP:ult:s1 x0 x1) = (G_USUBO#1:s1 x0 x1); '
                '(G_SUB:s32 x0 x1) = (G_USUBO:s32 x0 x1)')
        self.assertEqual(r['replacement'], text)
        # The same roots in another order in the block are the same rule.
        other, stats = run([SEL, ult, SUB])
        self.assertEqual(stats['rules_with_two_siblings'], 1)
        o = [o for o in other if len(o['region']['siblings']) == 2][0]
        self.assertEqual(o['replacement'], text)
        self.assertEqual(o['id'], r['id'])
        self.assertEqual(r['semantic_status']['joint_outputs'], 3)
        # Four instructions become two, with or without the comparison
        # below the root.
        self.assertEqual(r['cost'], {'source': 4, 'replacement': 2})
        self.assertEqual(r['region']['dead_nodes'], [])
        self.assertTrue(sibling.structural(r))
        self.assertIsNone(emit.why_not_emittable(r))
        g = emit._cpp_guard(r)
        self.assertIn('MachineInstr *Sib1 = findSiblingRoot(', g)
        self.assertIn('getScalarWidths(MRI, {X0, X1, X2, X3, T0, Dst, S0R0, '
                      'S1R0}, W)', g)
        self.assertIn('planRegion(*Root, Plan, /*Stays=*/0, ', g)
        a = emit._cpp_apply(r)
        # One new instruction defines the registers of both siblings.
        self.assertIn('B.buildInstr(TargetOpcode::G_USUBO, {S1R0, S0R0}, '
                      '{X0, X1})', a)
        self.assertIn('Sib0->eraseFromParent();', a)
        self.assertIn('Sib1->eraseFromParent();', a)
        # A later new instruction can read a register of a replaced
        # sibling (the builder reads its definition to fold constants), so
        # the old instructions release their registers before the build.
        for read, rel in (('S0R0 = Sib0->getOperand',
                           'releaseResults(MRI, *Sib0);'),
                          ('S1R0 = Sib1->getOperand',
                           'releaseResults(MRI, *Sib1);'),
                          ('S1R0 = Sib1->getOperand',
                           'releaseResults(MRI, Root);')):
            self.assertLess(a.index(read), a.index(rel))
            self.assertLess(a.index(rel), a.index('B.buildInstr'))

    def test_the_results_of_one_instruction_are_one_sibling(self):
        add = rec(node('G_ADD', 32, '%s', [IN(0), IN(1)]), XY)
        sum_ = rec(node('G_UADDO', 32, '%v', [IN(0), IN(1)], res=0,
                        mi='%u'), XY)
        ov = rec(node('G_UADDO', 1, '%o', [IN(0), IN(1)], res=1,
                      mi='%u'), XY)
        pairs, stats = pairs_of([add, sum_, ov])
        self.assertEqual(stats['with_two_siblings'], 0)
        self.assertTrue(all(len(p.sibs) == 1 for p in pairs))

    def test_a_sibling_reads_a_value_below_the_root(self):
        pairs, stats = pairs_of([self.AND, self.CARRY])
        self.assertEqual(stats['with_a_value_below_the_root'], 1)
        p = [p for p in pairs if ir.to_sexpr(p.inst.expr).startswith(
            '(G_AND')][0]
        self.assertEqual(sibling.operand_refs(p.inst.expr, p.sibs),
                         [(('node', 1), ('var', 0))])

    def test_a_value_that_occurs_twice_is_not_a_value_of_the_region(self):
        # (x + y) & (x + y) with two G_ADD instructions: the comparison
        # reads one of them, and the model has one term for both.
        two = rec(node('G_AND', 32, '%r', [
            node('G_ADD', 32, '%t', [IN(0), IN(1)], uses=2),
            node('G_ADD', 32, '%t2', [IN(0), IN(1)])]), XY)
        pairs, _ = pairs_of([two, self.CARRY])
        self.assertFalse([p for p in pairs if ir.to_sexpr(
            p.inst.expr).startswith('(G_AND')])

    def test_a_replaced_sibling_is_not_a_user_that_keeps_a_value(self):
        rules, _ = run([self.AND, self.CARRY])
        r = [r for r in rules if r['source'].startswith('(G_AND')]
        self.assertEqual(len(r), 1, rules)
        r = r[0]
        self.assertEqual(r['replacement'],
                         '(G_AND:s32 (G_UADDO:s32 x0 x1) x2); '
                         '(G_ICMP:ult:s1 (G_ADD:s32 x0 x1) x0) = '
                         '(G_UADDO#1:s1 x0 x1)')
        self.assertEqual(r['region']['siblings'][0]['operands'],
                         [{'node': 1}, {'var': 0}])
        # Two instructions replace two. In the corpus the sum goes with
        # them (its users are the root and the sibling), but the rule does
        # not need that.
        self.assertEqual(r['cost'], {'source': 3, 'replacement': 2})
        self.assertEqual(r['region']['dead_nodes'], [])
        self.assertTrue(sibling.structural(r))
        self.assertIsNone(emit.why_not_emittable(r))
        g = emit._cpp_guard(r)
        self.assertIn('MRI, *Root, T0,', g)
        self.assertIn('MI.getOperand(2).getReg() == T0 &&\n'
                      '            MI.getOperand(2 + 1).getReg() == X0', g)

    def test_a_rule_with_more_new_instructions_needs_to_remove_values(self):
        # and (add x, y), m with icmp ult (add x, y), x: a replacement of
        # the root with two new instructions (three in all for the two
        # roots) removes an instruction only if the sum goes. Its users
        # are the root and the sibling, which the rule replaces.
        a = ('G_AND', 32, ('G_ADD', 32, V(0), V(1)), V(2))
        b = ('G_ICMP:ult', 1, a[2], V(0))
        ra = ('G_AND', 32, ('G_XOR', 32, ('G_UADDO', 32, V(0), V(1)),
                            ('lit', 32, '0')), V(2))
        rb = ('G_UADDO#1', 1, V(0), V(1))
        self.assertEqual(sibling.dead_nodes(a, ra, b, rb, [2]), [1])
        # A third user: in that instance the rule did not need it.
        self.assertEqual(sibling.dead_nodes(a, ra, b, rb, [3]), [])
        # The replacement of the corpus has two new instructions.
        self.assertEqual(sibling.dead_nodes(
            a, ('G_AND', 32, ra[2][2], V(2)), b, rb, [2]), [])
        rules, _ = run([self.AND, self.CARRY])
        r = [r for r in rules if r['source'].startswith('(G_AND')][0]
        r = dict(r, needs_one_use=True,
                 region=dict(r['region'], dead_nodes=[1]))
        self.assertIn('if (!hasNUses(MRI, T0, 2))', emit._cpp_guard(r))
        td, _, _ = emit.emit({'rules': [r]}, all_candidates=True)
        self.assertNotIn('GIHasOneUse', td)

    def test_a_result_of_an_instruction_with_several_results_stays(self):
        # zext (the borrow of G_USUBO x, y) with icmp uge x, y next to it.
        # The corpus has the users of the borrow only, and the difference
        # can have a user: the G_USUBO stays, so nothing is cheaper.
        ins = [inp('%x', 32), inp('%y', 32)]
        zext = rec(node('G_ZEXT', 32, '%z', [
            node('G_USUBO', 1, '%b', [IN(0), IN(1)], res=1, mi='%u')]), ins)
        uge = rec(node('G_ICMP', 1, '%c', [IN(0), IN(1)], pred='uge'), ins)
        rules, _ = run([zext, uge])
        self.assertFalse([r for r in rules
                          if r['source'].startswith('(G_ZEXT')])

    def test_a_third_user_keeps_the_value(self):
        # The sum has a user outside the region: it stays, so the group
        # has no cheaper form.
        three = dict(self.AND, expr=dict(self.AND['expr'], args=[
            dict(self.AND['expr']['args'][0], uses=3), IN(2)]))
        carry = dict(self.CARRY, expr=dict(self.CARRY['expr'], args=[
            dict(self.CARRY['expr']['args'][0], uses=3), IN(0)]))
        rules, _ = run([three, carry])
        self.assertFalse([r for r in rules
                          if r['source'].startswith('(G_AND')])

    def test_a_replacement_reads_a_sibling_that_stays(self):
        a = emit._cpp_apply(self.stays_rule())
        self.assertIn('buildInstr(TargetOpcode::G_SELECT, {Dst}, '
                      '{NSib0.getReg(0), X3, X2})', a)
        self.assertNotIn('buildICmp', a)

    def test_a_replacement_reads_a_value_below_the_root(self):
        # The apply step does not build an instruction that the pattern
        # matched: it reads the register of that instruction, which is
        # then an input of the plan.
        r = self.stays_rule()
        src = ir.from_json(r['source_json'])
        sib = ir.from_json(r['region']['siblings'][0]['source_json'])
        tgt = ('G_SELECT', 32, ('G_AND', 1, src[2], sib), V(3), V(2))
        r = dict(r, replacement_json=ir.to_json(tgt))
        a = emit._cpp_apply(r)
        self.assertIn('buildInstr(TargetOpcode::G_AND, {MRI.getType(T0)}, '
                      '{T0, NSib0.getReg(0)})', a)
        self.assertNotIn('buildICmp', a)
        self.assertIn('/*Stays=*/1, {X0, X1, X2, X3, T0}))',
                      emit._cpp_guard(r))

    def stays_rule(self):
        ult = rec(node('G_ICMP', 1, '%c2', [IN(0), IN(1)], pred='ult'), XY)
        rules, _ = run([SEL, ult])
        return [r for r in rules if r['source'].startswith('(G_SELECT')][0]

    def test_an_input_of_the_sibling_only(self):
        add = rec(node('G_ADD', 32, '%s', [IN(0), IN(1)]), XY)
        xyz = XY + [inp('%z', 1, 0)]
        adde = rec(node('G_UADDE', 32, '%e', [IN(0), IN(1), IN(2)], res=0,
                        mi='%u'), xyz)
        pairs, stats = pairs_of([add, adde])
        self.assertEqual(stats['with_an_input_of_the_sibling'], 1)
        rules, _ = run([add, adde])
        r = [r for r in rules if r['source'].startswith('(G_ADD')][0]
        # The carry input is zero in the corpus: the precondition says so.
        self.assertEqual(r['region']['sibling_vars'], [2])
        self.assertEqual(r['precondition'], 'all(KZ(x2)) && defined(x2)')
        self.assertTrue(sibling.structural(r))
        self.assertIsNone(emit.why_not_emittable(r))
        g = emit._cpp_guard(r)
        # The pattern of the root does not have x2: the guard takes it
        # from the sibling and gives it to the apply step.
        self.assertIn('Register Dst, Register X0, Register X1) {', g)
        self.assertIn('  Register X2;', g)
        self.assertIn('X2 = MI.getOperand(2 + 2).getReg();', g)
        self.assertIn('Plan.Extra = {X2};', g)
        self.assertIn('KnownBits K2 = VT->getKnownBits(X2);', g)
        self.assertIn('planRegion(*Root, Plan, /*Stays=*/1, {X0, X1, X2})',
                      g)
        a = emit._cpp_apply(r)
        self.assertIn('Register X2 = Plan.Extra[0];', a)
        td, _, _ = emit.emit({'rules': [r]}, all_candidates=True)
        self.assertNotIn('${x2}', td)

    def test_an_input_of_the_sibling_is_a_constant_in_the_corpus(self):
        add = rec(node('G_ADD', 32, '%s', [IN(0), IN(1)]), XY)
        adde = rec(node('G_UADDE', 32, '%e', [IN(0), IN(1), IN(2)], res=0,
                        mi='%u'), XY + [inp('%z', 1)])
        pairs, _ = pairs_of([add, adde])
        self.assertFalse([p for p in pairs if ir.to_sexpr(
            p.inst.expr).startswith('(G_ADD')])

    def test_a_sibling_reads_an_earlier_sibling(self):
        # d = x - y; and d, x: the second reads the first.
        and_ = rec(node('G_AND', 32, '%n', [IN(0), IN(1)]),
                   [inp('%d', 32), inp('%x', 32)])
        pairs, stats = pairs_of([SEL, SUB, and_])
        two = [p for p in pairs if len(p.sibs) == 2]
        self.assertEqual(len(two), 1)
        refs = sibling.operand_refs(two[0].inst.expr, two[0].sibs)
        self.assertEqual(refs[1], (('sib', 0), ('var', 0)))

    def test_the_guard_matches_an_operand_that_is_an_earlier_sibling(self):
        rules, _ = run([SEL, SUB])
        r = [r for r in rules if r['source'].startswith('(G_SELECT')][0]
        # A second sibling that stays and that reads the first.
        sub = ir.from_json(r['region']['siblings'][0]['source_json'])
        b = ('G_AND', 32, sub, V(0))
        r = dict(r, region=dict(r['region'], siblings=[
            dict(r['region']['siblings'][0], stays=True),
            {'source': ir.to_sexpr(b), 'source_json': ir.to_json(b),
             'operands': [{'sibling': 0}, {'var': 0}], 'result': 0,
             'stays': True}]))
        g = emit._cpp_guard(r)
        self.assertIn('MRI, *Root, S0R0,', g)
        self.assertIn('MI.getOperand(1).getReg() == S0R0 &&\n'
                      '            MI.getOperand(1 + 1).getReg() == X0', g)
        # The results of the siblings that stay are not inputs of the
        # plan; the operands of the siblings are.
        self.assertIn('/*Stays=*/3, {X0, X1, X2, X3}))', g)
        # A sibling that stays does not read one that the rule replaces.
        bad = dict(r, region=dict(r['region'], siblings=[
            dict(r['region']['siblings'][0], stays=False),
            r['region']['siblings'][1]]))
        self.assertEqual(emit.why_not_emittable(bad),
                         'a root that stays reads a root that is replaced')
        self.assertFalse(sibling.structural(bad))


if __name__ == '__main__':
    unittest.main()
