#!/usr/bin/env python3
"""Tests of the synthesis of rules with fixed vectors: the search of
vector_search.py (its families and budgets), rules that keep vectors with a
precondition (CEGIS with the facts of the lanes), the width schedules of a
rule with vectors, the lifting of a G_SELECT of vectors with one scalar
condition, and the replacements that a rule must not create.

Run:  python3 -m unittest discover -s tools/gisel-rule-synth/tests
"""

import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

from girs import (corpus, discover, emit, ir, known, ops, precond,  # noqa
                  smt, synth, vector, vector_search)

VEC = ops.vec
V2, V4, V2_16, V4_16 = VEC(2, 32), VEC(4, 32), VEC(2, 16), VEC(4, 16)


def X(i):
    return ('var', i)


def instance(src, vw, facts=None, consts=None, lifted=False, shared=()):
    n = len(vw)
    inst = corpus.Instance(src, vw, facts or [(0, 0)] * n,
                           consts or [None] * n,
                           [1] * len(ir.interior_nodes(src)), [],
                           [('f.jsonl', 'fn', '%0')])
    inst.lifted = lifted
    inst.lift_scalars = tuple(shared)
    return inst


def sexprs(cands):
    return [(ir.to_sexpr(t), f) for t, f in cands]


class Roles(unittest.TestCase):
    def test_roles(self):
        R = ops.operand_roles
        self.assertEqual(R('G_ADD', V4, [V4, V4]), ['elementwise'] * 2)
        self.assertEqual(R('G_SELECT', V4, [1, V4, V4]),
                         ['shared_scalar', 'elementwise', 'elementwise'])
        self.assertEqual(R('G_SELECT', V4, [VEC(4, 1), V4, V4]),
                         ['elementwise'] * 3)
        self.assertEqual(R('G_BUILD_VECTOR', V2, [32, 32]),
                         ['scalar_element'] * 2)
        self.assertEqual(R('G_EXTRACT_VECTOR_ELT', 32, [V4, 32]),
                         ['lane_mapping', 'index'])
        self.assertEqual(R('G_INSERT_VECTOR_ELT', V4, [V4, 32, 32]),
                         ['lane_mapping', 'scalar_element', 'index'])
        self.assertEqual(R('G_SHUFFLE_VECTOR:1.0', V2, [V2, V2]),
                         ['lane_mapping'] * 2)
        self.assertEqual(R('G_BITCAST:r', 64, [V2]), ['lane_mapping'])
        self.assertIsNone(R('G_MERGE_VALUES', 64, [32, 32]))

    def test_creatable(self):
        self.assertTrue(ops.creatable('G_INSERT_VECTOR_ELT:1'))
        # A variable index can be outside of the vector.
        self.assertFalse(ops.creatable('G_INSERT_VECTOR_ELT'))
        self.assertTrue(ops.creatable('G_EXTRACT_VECTOR_ELT:0'))
        self.assertFalse(ops.creatable('G_EXTRACT_VECTOR_ELT'))
        self.assertTrue(ops.creatable('G_CONCAT_VECTORS'))
        self.assertFalse(ops.creatable('G_VECREDUCE_ADD'))


class SharedScalarLift(unittest.TestCase):
    """A G_SELECT of vectors with one scalar condition: each lane reads
    the same value of the condition."""

    REC = {
        'fn': 'f', 'root': '%4',
        'inputs': [
            {'reg': '%0', 'w': 1, 'type': 's1', 'zero': '0x0', 'one': '0x0'},
            {'reg': '%1', 'w': 32, 'lanes': 4, 'type': '<4 x s32>',
             'zero': '0x0', 'one': '0x0'},
            {'reg': '%2', 'w': 32, 'lanes': 4, 'type': '<4 x s32>',
             'zero': '0x0', 'one': '0x0'}],
        'expr': {'op': 'G_SELECT', 'w': 32, 'lanes': 4, 'type': '<4 x s32>',
                 'reg': '%4', 'zero': '0x0', 'one': '0x0', 'args': [
                     {'in': 0},
                     {'op': 'G_SELECT', 'w': 32, 'lanes': 4,
                      'type': '<4 x s32>', 'reg': '%3', 'zero': '0x0',
                      'one': '0x0', 'uses': 1,
                      'args': [{'in': 0}, {'in': 1}, {'in': 2}]},
                     {'in': 2}]}}

    def test_reader_lifts_a_scalar_condition(self):
        inst = corpus.parse_record(self.REC)
        self.assertTrue(inst.lifted)
        self.assertEqual(inst.lift_scalars, (0,))
        self.assertEqual(inst.vw, (1, 32, 32))

    def test_rule_accepts_a_scalar_condition(self):
        inst = corpus.parse_record(self.REC)
        sy = synth.Synthesizer(smt.Z3Backend())
        # select(c, select(c, a, b), b) -> select(c, a, b)
        rid = sy.add(inst, ('G_SELECT', 32, X(0), X(1), X(2)))
        self.assertIsNotNone(rid)
        sy.finalize([inst])
        r = sy.rules[rid]
        self.assertEqual(r['lift_scalars'], [0])
        self.assertEqual(emit.shared_scalars(r), [0])
        self.assertIn('/*SharedScalars=*/UINT64_C(0x1)', emit._cpp_guard(r))
        # A new applicability is a new revision of the same rule.
        plain = dict(r)
        plain.pop('lift_scalars')
        self.assertNotEqual(known.revision(r), known.revision(plain))

    def test_condition_read_otherwise_is_not_shared(self):
        # The replacement reads the condition as a value: with vectors of
        # the other operands that is not an operator of LLVM.
        inst = corpus.parse_record(self.REC)
        r = {'lift': True, 'lift_scalars': [0],
             'source_json': ir.to_json(inst.expr),
             'replacement_json': ir.to_json(
                 ('G_SELECT', 32, ('G_XOR', 1, X(0), ('lit', 1, '-1')),
                  X(2), X(1)))}
        self.assertEqual(emit.shared_scalars(r), [])

    def test_known_scalar_rule_does_not_cover(self):
        inst = corpus.parse_record(self.REC)
        sy = synth.Synthesizer(smt.Z3Backend())
        scalar = corpus.parse_record(self.REC)
        scalar.lifted, scalar.lift_scalars = False, ()
        rid = sy.add(scalar, ('G_SELECT', 32, X(0), X(1), X(2)))
        sy.finalize([scalar])
        db = known.stamp({'rules': [synth.strip_private(sy.rules[rid])]})
        idx = known.Index(db)
        self.assertIsNone(idx.covers(inst, ('G_SELECT', 32, X(0), X(1),
                                            X(2))))
        self.assertIsNotNone(idx.covers(scalar, ('G_SELECT', 32, X(0), X(1),
                                                 X(2))))


class Preconditions(unittest.TestCase):
    """A rule that keeps vectors and needs a fact of every lane."""

    SRC = ('G_EXTRACT_VECTOR_ELT:1', 32, ('G_AND', V2, X(0), X(1)))

    def test_cegis_finds_the_lane_fact(self):
        # x1 has all bits one in each lane (a splat of -1, or known bits).
        inst = instance(self.SRC, (V2, V2),
                        facts=[(0, 0), (0, 0xffffffff)])
        sy = synth.Synthesizer(smt.Z3Backend())
        rid = sy.add(inst, ('G_EXTRACT_VECTOR_ELT:1', 32, X(0)))
        self.assertIsNotNone(rid)
        sy.finalize([inst])
        r = sy.rules[rid]
        # The weakest condition that CEGIS finds: each bit of a lane is
        # known zero in x0 or known one in x1 (all ones in x1 is one case).
        self.assertEqual(r['precondition'], 'all(KZ(x0) | KO(x1))')
        pred = r['disjuncts'][0]['_pred']
        self.assertTrue(precond.eval_pred(pred, [(0, 0), (0, 0xffffffff)],
                                          (V2, V2), 32))
        self.assertFalse(precond.eval_pred(pred, [(0, 0), (0, 0xfffffffe)],
                                           (V2, V2), 32))
        maps = r['disjuncts'][0]['width_maps']
        # The lanes keep their number; their width varies.
        self.assertIn([[32, 32], [V2, V2]], [sorted(m) for m in maps])
        self.assertIn([[32, 8], [V2, VEC(2, 8)]], [sorted(m) for m in maps])
        guard = emit._cpp_guard(r)
        self.assertIn('KnownBits K1 = VT->getKnownBits(X1);', guard)
        self.assertIn('(K0.Zero | K1.One).isAllOnes()', guard)

    def test_without_the_fact_no_rule(self):
        inst = instance(self.SRC, (V2, V2))
        sy = synth.Synthesizer(smt.Z3Backend())
        self.assertIsNone(sy.add(inst, ('G_EXTRACT_VECTOR_ELT:1', 32, X(0))))

    def test_counterexample_has_lane_widths(self):
        s = synth.rule_schedules(
            {'source_json': ir.to_json(self.SRC),
             'replacement_json': ir.to_json(
                 ('G_EXTRACT_VECTOR_ELT:1', 32, X(0))), 'vw': [V2, V2]},
            [[[32, 32], [V2, V2]]])
        st, cex = synth.verify(s, [()], smt.Z3Backend())
        self.assertEqual(st, 'invalid')
        vw, facts, rw = cex
        self.assertEqual((vw, rw), ((32, 32), 32))
        self.assertTrue(precond.eval_pred((), facts, vw, rw))

    def test_def_means_every_lane(self):
        # freeze(v) -> v needs every lane defined.
        src = ('G_FREEZE', V2, X(0))
        sch = synth.rule_schedules(
            {'source_json': ir.to_json(src), 'replacement_json':
             ir.to_json(X(0)), 'vw': [V2]}, [[[V2, V2]]])
        self.assertEqual(synth.verify(sch, [()], smt.Z3Backend())[0],
                         'invalid')
        self.assertEqual(synth.verify(sch, [(('def', 0),)],
                                      smt.Z3Backend())[0], 'valid')

    def test_same_bits_other_shape(self):
        # <2 x s32>, <4 x s16> and s64 have 64 bits each; a rule for one
        # shape has no schedule of another.
        src = ('G_EXTRACT_VECTOR_ELT:0', 32, ('G_BUILD_VECTOR', V2, X(0),
                                              X(1)))
        lim = synth.SynthLimits()
        for _, _, v, m in synth.schedules(src, X(0), (32, 32), lim):
            self.assertTrue(all(ops.lanes(w) in (0, 2) for w in m.values()))
        add = ('G_ADD', V2, X(0), ('G_SUB', V2, X(1), X(0)))
        for _, _, v, m in synth.schedules(add, X(1), (V2, V2), lim):
            self.assertEqual({ops.lanes(w) for w in m.values()}, {2})
            self.assertNotIn(64, m.values())
            self.assertNotIn(V4_16, m.values())


class Search(unittest.TestCase):
    def test_extract_through_shuffle(self):
        src = ('G_EXTRACT_VECTOR_ELT:1', 32,
               ('G_SHUFFLE_VECTOR:3.0', V2, X(0), X(1)))
        self.assertEqual(sexprs(vector_search.candidates(src, (V2, V2))),
                         [('(G_EXTRACT_VECTOR_ELT:0:s32 x0)', 'lanes')])

    def test_index_bounds(self):
        # The last lane is an index; a constant index outside of the
        # vector has no model.
        self.assertTrue(ir.well_typed(('G_EXTRACT_VECTOR_ELT:3', 32, X(0)),
                                      (V4,)))
        self.assertFalse(ir.well_typed(('G_EXTRACT_VECTOR_ELT:4', 32, X(0)),
                                       (V4,)))

    def test_shuffle_composition_and_repeated_lanes(self):
        s = ('G_SHUFFLE_VECTOR:1.0', V2, X(0), X(1))
        src = ('G_SHUFFLE_VECTOR:3.0', V2, s, X(1))
        self.assertEqual(sexprs(vector_search.candidates(src, (V2, V2))),
                         [('(G_SHUFFLE_VECTOR:1.3:v2s32 x1 x0)', 'lanes')])
        # A composition that reads one lane twice: an undef lane has a
        # value per read (vector.linear), so it is not a replacement.
        src = ('G_SHUFFLE_VECTOR:1.1', V2, s, X(1))
        self.assertEqual(vector_search.candidates(src, (V2, V2)), [])

    def test_undefined_lane_is_not_created(self):
        src = ('G_SHUFFLE_VECTOR:u.0', V2,
               ('G_SHUFFLE_VECTOR:1.0', V2, X(0), X(1)), X(1))
        for t, _ in vector_search.candidates(src, (V2, V2)):
            self.assertFalse(vector.undefined_lane(t, (V2, V2)))
        self.assertTrue(vector.undefined_lane(src, (V2, V2)))

    def test_concat_and_insert(self):
        b = ('G_BUILD_VECTOR', V4,
             ('G_EXTRACT_VECTOR_ELT:0', 32, X(0)),
             ('G_EXTRACT_VECTOR_ELT:1', 32, X(0)),
             ('G_EXTRACT_VECTOR_ELT:0', 32, X(1)),
             ('G_EXTRACT_VECTOR_ELT:1', 32, X(1)))
        got = sexprs(vector_search.candidates(b, (V2, V2)))
        self.assertIn(('(G_CONCAT_VECTORS:v4s32 x0 x1)', 'lanes'), got)
        ins = ('G_BUILD_VECTOR', V2, ('G_EXTRACT_VECTOR_ELT:0', 32, X(0)),
               X(1))
        got = sexprs(vector_search.candidates(ins, (V2, 32)))
        self.assertIn(('(G_INSERT_VECTOR_ELT:1:v2s32 x0 x1)', 'lanes'), got)

    def test_permutation_factoring(self):
        # add(shuffle(a), shuffle(b)) with one permutation: the operation
        # on the whole vectors, then one shuffle.
        src = ('G_ADD', V2, ('G_SHUFFLE_VECTOR:1.0', V2, X(0), X(0)),
               ('G_SHUFFLE_VECTOR:1.0', V2, X(1), X(1)))
        got = sexprs(vector_search.candidates(src, (V2, V2)))
        self.assertEqual(got[0], ('(G_SHUFFLE_VECTOR:1.0:v2s32 '
                                  '(G_ADD:v2s32 x0 x1) x0)', 'permute'))
        tgt = vector_search.candidates(src, (V2, V2))[0][0]
        f, _, _ = vector.violation(src, tgt, (V2, V2))
        self.assertEqual(smt.Z3Backend().check(f).status, 'unsat')

    def test_permutation_needs_one_mask(self):
        src = ('G_ADD', V2, ('G_SHUFFLE_VECTOR:1.0', V2, X(0), X(0)),
               ('G_SHUFFLE_VECTOR:0.1', V2, X(1), X(1)))
        self.assertNotIn('permute', [f for _, f in vector_search.candidates(
            src, (V2, V2), limits=vector_search.Limits(cost_slack=4))])

    def test_template_search(self):
        # The lanes are sub(p, p) of the same column: the scalar search
        # finds 0 for each lane.
        sh = ('G_SHUFFLE_VECTOR:1.0', V2, X(0), X(1))
        src = ('G_SUB', V2, sh, sh)
        inst = instance(src, (V2, V2))
        dlim = discover.Limits()
        ctx = discover.Context(dlim)
        cands, st = vector_search.search(
            inst, smt.Z3Backend(), vector_search.Limits.of(dlim), dlim, ctx)
        got = [(ir.to_sexpr(c['tgt']), c['family']) for c in cands]
        self.assertIn(('0:v2s32', 'template'), got)
        self.assertEqual(st['vector_template_searches'], 1)
        sy = synth.Synthesizer(smt.Z3Backend())
        self.assertIsNotNone(sy.add(inst, ('lit', V2, '0')))

    def test_shared_scalar_is_kept(self):
        # The condition of a G_SELECT of vectors is one scalar: the
        # template keeps it as a scalar.
        sh = ('G_SHUFFLE_VECTOR:1.0', V2, X(1), X(2))
        src = ('G_SELECT', V2, X(0), sh, sh)
        inst = instance(src, (1, V2, V2))
        L = vector.Lanes((1, V2, V2))
        T = vector_search.lane_template(L, L.of(src))
        self.assertEqual(T.shared.count(True), 1)
        v = vector_search.vectorize(T.expr, L, T, [None, sh], 2)
        self.assertEqual(v[2], X(0))

    def test_cost_budgets(self):
        src = ('G_EXTRACT_VECTOR_ELT:1', 32, ('G_ADD', V4, X(0), X(1)))
        self.assertEqual(vector_search.candidates(src, (V4, V4)), [])
        lim = vector_search.Limits(cost_slack=1)
        got = sexprs(vector_search.candidates(src, (V4, V4), limits=lim))
        self.assertIn(('(G_ADD:s32 (G_EXTRACT_VECTOR_ELT:1:s32 x0) '
                       '(G_EXTRACT_VECTOR_ELT:1:s32 x1))', 'lanes'), got)
        lim = vector_search.Limits(cost_slack=1, max_rhs_cost=2)
        self.assertEqual(vector_search.candidates(src, (V4, V4),
                                                  limits=lim), [])

    def test_search_is_not_semantics(self):
        # A change of the search is not a change of the semantics: it
        # does not invalidate the catalog.
        import inspect
        self.assertNotIn('vector_search', inspect.getsource(
            known.semantics_sha))
        self.assertIn('vector_search.py', inspect.getsource(
            known.search_sha))
        self.assertIn("'vector.py'", inspect.getsource(known.semantics_sha))


class Legality(unittest.TestCase):
    """The legality table with types of fixed vectors (version 2)."""

    TABLE = {
        'version': 2, 'target': 'amdgcn-amd-amdhsa', 'cpu': 'gfx1100',
        'operators': {'G_ADD': {'32': 'Legal', '16': 'Legal'}},
        'type_operands': {'G_ADD': [0], 'G_EXTRACT_SUBVECTOR': [0, 1],
                          'G_INSERT_VECTOR_ELT': [0, 2, 3],
                          'G_SHUFFLE_VECTOR': [0, 1]},
        'typed': {
            'G_ADD': {'<2 x s16>': 'Legal', '<2 x s32>': 'FewerElements'},
            'G_EXTRACT_SUBVECTOR': {'<2 x s32>,<4 x s32>': 'Unsupported'},
            'G_INSERT_VECTOR_ELT': {'<2 x s32>,s32,s32': 'Custom'},
            'G_SHUFFLE_VECTOR': {'<4 x s32>,<8 x s32>': 'Lower'}}}

    def cap(self):
        from girs import targets
        return targets.Capability(self.TABLE, 'digest')

    def test_actions_by_stage(self):
        c = self.cap()
        add16 = ('G_ADD', V2_16, X(0), X(1))
        add32 = ('G_ADD', V2, X(0), X(1))
        self.assertEqual(c.node_types(add16, (V2_16, V2_16)), ['<2 x s16>'])
        self.assertTrue(c.can_create(add16, (V2_16,) * 2))
        self.assertTrue(c.can_create(add16, (V2_16,) * 2, 'post-legalizer'))
        # The legalizer splits it: acceptable before the legalizer only.
        self.assertTrue(c.can_create(add32, (V2, V2)))
        self.assertFalse(c.can_create(add32, (V2, V2), 'post-legalizer'))
        # A constant index is a register of the index type of the target.
        ins = ('G_INSERT_VECTOR_ELT:1', V2, X(0), X(1))
        self.assertEqual(c.node_types(ins, (V2, 32)),
                         ['<2 x s32>', 's32', 's32'])
        self.assertTrue(c.can_create(ins, (V2, 32)))
        self.assertIsNone(c.can_create(('G_ADD', V4, X(0), X(1)), (V4, V4)))
        # Scalars: the table of version 1.
        self.assertTrue(c.can_create(('G_ADD', 32, X(0), X(1)), (32, 32)))

    def test_search_does_not_create_unsupported(self):
        V8 = VEC(8, 32)
        src = ('G_SHUFFLE_VECTOR:0.1.2.3', V4, X(0), X(0))
        ext = ('G_EXTRACT_SUBVECTOR:0', V4, X(0))
        free = sexprs(vector_search.candidates(
            ('G_BUILD_VECTOR', V4) + tuple(
                ('G_EXTRACT_VECTOR_ELT:%d' % j, 32, X(0)) for j in range(4)),
            (V8,)))
        self.assertIn((ir.to_sexpr(ext), 'lanes'), free)
        c = self.cap()
        c.typed['G_EXTRACT_SUBVECTOR'] = {'<4 x s32>,<8 x s32>':
                                          'Unsupported'}
        st = {}
        got = sexprs(vector_search.candidates(
            ('G_BUILD_VECTOR', V4) + tuple(
                ('G_EXTRACT_VECTOR_ELT:%d' % j, 32, X(0)) for j in range(4)),
            (V8,), limits=vector_search.Limits(capability=c), stats=st))
        self.assertNotIn((ir.to_sexpr(ext), 'lanes'), got)
        self.assertIn((ir.to_sexpr(src), 'lanes'), got)
        self.assertEqual(st['not_legalizable'], 1)

    def test_index_bits(self):
        self.assertEqual(vector_search.index_bits(self.cap()), 32)
        self.assertEqual(vector_search.index_bits(None), 32)


LLC = os.environ.get('GIRS_LLC') or __import__('girs.paths').paths.llc()
MIR = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(HERE))),
                   'test', 'AMDGPU', 'egraph-combiner-vector.mir')


class EGraphBridge(unittest.TestCase):
    """Vector MIR -> GIEGraph -> export -> import -> the proof of the
    synthesizer -> a rule. The e-graph is not trusted: each candidate is
    proved again."""

    def records(self):
        import json
        import subprocess
        import tempfile
        if not os.path.exists(LLC) or not os.path.exists(MIR):
            self.skipTest('needs llc and test/AMDGPU/egraph-combiner-vector.mir')
        with tempfile.TemporaryDirectory() as d:
            out = os.path.join(d, 'e.jsonl')
            subprocess.run([LLC, '-mtriple=amdgcn-amd-amdhsa',
                            '-run-pass=gisel-egraph-combiner',
                            '-gisel-egraph-export=' + out, '-o', os.devnull,
                            MIR], check=True, stderr=subprocess.DEVNULL)
            with open(out) as f:
                return [json.loads(x) for x in f if x.strip()]

    def test_types_of_the_export(self):
        from girs import egraph
        self.assertEqual(egraph.parse_type('<2 x s16>'), V2_16)
        self.assertEqual(egraph.parse_type('<4 x i32>'), V4)
        self.assertEqual(egraph.parse_type('s32'), 32)
        self.assertIsNone(egraph.parse_type('<2 x p0>'))
        self.assertIsNone(egraph.parse_type('<32 x s8>'))
        lim = egraph.Limits(max_width=16)
        self.assertIsNone(lim.type_error(V4_16))
        self.assertEqual(lim.type_error(V2), 'wider than 16 bits')
        self.assertEqual(egraph.Limits(max_bits=32).type_error(V4_16),
                         'more than 32 bits in all lanes')

    def test_candidates_are_proved_rules(self):
        from girs import egraph
        recs = self.records()
        self.assertTrue(recs)
        imp = egraph.Importer(smt.Z3Backend())
        for r in recs:
            imp.add_record(r, 'vector.jsonl')
        cands = imp.candidates()
        got = {(ir.to_sexpr(c.inst.expr), ir.to_sexpr(c.tgt)) for c in cands}
        self.assertIn(('(G_EXTRACT_VECTOR_ELT:0:s32 '
                       '(G_SHUFFLE_VECTOR:3.0:v2s32 x0 x1))',
                       '(G_EXTRACT_VECTOR_ELT:1:s32 x1)'), got)
        sy = synth.Synthesizer(smt.Z3Backend())
        rids = []
        for c in cands:
            rid = sy.add(c.inst, c.tgt, provenance={
                'discovery': 'egraph', 'egraph_rules': c.rules})
            if rid:
                rids.append(rid)
        sy.finalize([c.inst for c in cands])
        rules = [sy.rules[r] for r in set(rids)]
        shuffle = [r for r in rules if 'SHUFFLE' in r['source']]
        self.assertTrue(shuffle)
        r = shuffle[0]
        self.assertEqual(r['provenance']['sources'], ['egraph'])
        self.assertIn('vector-extract-of-shuffle',
                      r['provenance']['egraph_rules'])
        self.assertIsNone(emit.why_not_emittable(r))
        self.assertIn('buildExtractVectorElementConstant(Dst, X1, 1)',
                      emit._cpp_apply(r))
        # The rule is proved for other widths of the lanes too.
        self.assertGreater(len(r['disjuncts'][0]['width_maps']), 1)


class RuleConstruction(unittest.TestCase):
    def rule(self, src, tgt, vw):
        sy = synth.Synthesizer(smt.Z3Backend())
        inst = instance(src, vw)
        rid = sy.add(inst, tgt)
        self.assertIsNotNone(rid)
        sy.finalize([inst])
        return sy.rules[rid]

    def test_insert_and_concat_are_built(self):
        ins = ('G_BUILD_VECTOR', V2, ('G_EXTRACT_VECTOR_ELT:0', 32, X(0)),
               X(1))
        r = self.rule(ins, ('G_INSERT_VECTOR_ELT:1', V2, X(0), X(1)),
                      (V2, 32))
        self.assertIn('buildInsertVectorElementConstant(B, Dst, X0, X1, 1)',
                      emit._cpp_apply(r))
        b = ('G_BUILD_VECTOR', V4,
             ('G_EXTRACT_VECTOR_ELT:0', 32, X(0)),
             ('G_EXTRACT_VECTOR_ELT:1', 32, X(0)),
             ('G_EXTRACT_VECTOR_ELT:0', 32, X(1)),
             ('G_EXTRACT_VECTOR_ELT:1', 32, X(1)))
        r = self.rule(b, ('G_CONCAT_VECTORS', V4, X(0), X(1)), (V2, V2))
        self.assertIn('B.buildConcatVectors(Dst, {X0, X1})',
                      emit._cpp_apply(r))

    def test_variable_index_is_not_a_replacement(self):
        src = ('G_EXTRACT_VECTOR_ELT', 32, ('G_BUILD_VECTOR', V2, X(0),
                                            X(0)), X(1))
        inst = instance(src, (32, 32))
        sy = synth.Synthesizer(smt.Z3Backend())
        self.assertIsNone(sy.add(inst, ('G_EXTRACT_VECTOR_ELT', 32,
                                        ('G_BUILD_VECTOR', V2, X(0), X(0)),
                                        X(1))))


if __name__ == '__main__':
    unittest.main()
