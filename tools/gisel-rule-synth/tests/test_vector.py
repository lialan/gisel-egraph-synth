#!/usr/bin/env python3
"""Tests of the model of fixed vectors (girs/vector.py): the lanes of each
operator, the joint proof of the lanes, the replacements that the lanes
give, rules for scalars that also accept vectors lane by lane, and the
generated code of a rule with vectors.

Run:  python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests
"""

import json
import os
import random
import re
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

from girs import (corpus, emit, ir, ops, select, smt, synth,  # noqa: E402
                  targets, vector)

BIN = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(ROOT))),
                   'build', 'bin')
LLC = os.environ.get('GIRS_LLC') or os.path.join(BIN, 'llc')
OPT = os.path.join(os.path.dirname(LLC), 'opt')
HAVE_LLC = os.path.exists(LLC)
HAVE_OPT = os.path.exists(OPT)
TRIPLE = ['-mtriple=amdgcn-amd-amdhsa', '-mcpu=gfx1100']

VEC = ops.vec
V4, V2, V8 = VEC(4, 32), VEC(2, 32), VEC(8, 32)


def X(i):
    return ('var', i)


def status(src, tgt, vw):
    f, _, _ = vector.violation(src, tgt, vw)
    return smt.Z3Backend().check(f).status


def instance(src, vw, lifted=False):
    n = len(vw)
    inst = corpus.Instance(src, vw, [(0, 0)] * n, [None] * n,
                           [1] * len(ir.interior_nodes(src)), [],
                           [('f.jsonl', 'fn', '%0')])
    inst.lifted = lifted
    return inst


def rule_of(src, vw, tgt=None):
    """The finalized rule of the replacement that the lanes of ``src``
    give (or of ``tgt``)."""
    sy = synth.Synthesizer(smt.Z3Backend())
    if tgt is None:
        (tgt,) = vector.candidates(src, vw)
    rid = sy.add(instance(src, vw), tgt)
    sy.finalize([])
    return sy.rules[rid] if rid else None


class TypeCodes(unittest.TestCase):
    def test_codes(self):
        self.assertEqual((ops.lanes(V4), ops.elem(V4), ops.bits(V4)),
                         (4, 32, 128))
        self.assertEqual((ops.lanes(32), ops.elem(32), ops.bits(32)),
                         (0, 32, 32))
        self.assertEqual(ir.type_str(V4), 'v4s32')
        # The code that gisynth::getScalarWidths writes.
        self.assertEqual(V4, (4 << 16) | 32)

    def test_lane_wise_operators(self):
        ok = ir.well_typed
        self.assertTrue(ok(('G_ADD', V4, X(0), X(1)), (V4, V4)))
        self.assertFalse(ok(('G_ADD', V4, X(0), X(1)), (V4, V2)))
        self.assertFalse(ok(('G_ADD', V4, X(0), X(1)), (V4, 32)))
        self.assertTrue(ok(('G_ICMP:ult', VEC(4, 1), X(0), X(1)), (V4, V4)))
        self.assertFalse(ok(('G_ICMP:ult', 1, X(0), X(1)), (V4, V4)))
        self.assertTrue(ok(('G_ZEXT', VEC(4, 64), X(0)), (V4,)))
        # The condition of a G_SELECT: a vector, or one scalar.
        for c in (VEC(4, 1), 1):
            self.assertTrue(ok(('G_SELECT', V4, X(0), X(1), X(2)),
                               (c, V4, V4)))
        self.assertFalse(ok(('G_SELECT', V4, X(0), X(1), X(2)),
                            (VEC(2, 1), V4, V4)))

    def test_vector_operators(self):
        ok = ir.well_typed
        self.assertTrue(ok(('G_BUILD_VECTOR', V2, X(0), X(1)), (32, 32)))
        self.assertFalse(ok(('G_BUILD_VECTOR', V2, X(0), X(1)), (32, 16)))
        self.assertFalse(ok(('G_BUILD_VECTOR', V4, X(0), X(1)), (32, 32)))
        self.assertTrue(ok(('G_CONCAT_VECTORS', V4, X(0), X(1)), (V2, V2)))
        self.assertTrue(ok(('G_EXTRACT_VECTOR_ELT:3', 32, X(0)), (V4,)))
        self.assertFalse(ok(('G_EXTRACT_VECTOR_ELT:4', 32, X(0)), (V4,)))
        self.assertTrue(ok(('G_EXTRACT_VECTOR_ELT', 32, X(0), X(1)),
                           (V4, 64)))
        self.assertTrue(ok(('G_SHUFFLE_VECTOR:0.7.u.1', V4, X(0), X(1)),
                           (V4, V4)))
        self.assertFalse(ok(('G_SHUFFLE_VECTOR:0.8.u.1', V4, X(0), X(1)),
                            (V4, V4)))
        self.assertTrue(ok(('G_VECREDUCE_ADD', 32, X(0)), (V4,)))
        self.assertFalse(ok(('G_VECREDUCE_FADD', 32, X(0)), (VEC(4, 8),)))

    def test_bits_with_another_number_of_lanes(self):
        ok = ir.well_typed
        self.assertTrue(ok(('G_BITCAST:r', 64, X(0)), (V2,)))
        self.assertFalse(ok(('G_BITCAST', 64, X(0)), (V2,)))
        self.assertTrue(ok(('G_BITCAST:r', VEC(4, 16), X(0)), (V2,)))
        self.assertFalse(ok(('G_BITCAST:r', VEC(3, 16), X(0)), (V2,)))
        # Lanes, vectors of lanes, and parts of a lane.
        self.assertTrue(ok(('G_UNMERGE_VALUES#3', 32, X(0)), (V4,)))
        self.assertFalse(ok(('G_UNMERGE_VALUES#4', 32, X(0)), (V4,)))
        self.assertTrue(ok(('G_UNMERGE_VALUES#1', V2, X(0)), (V4,)))
        self.assertTrue(ok(('G_UNMERGE_VALUES#7', 16, X(0)), (V4,)))
        self.assertFalse(ok(('G_UNMERGE_VALUES#8', 16, X(0)), (V4,)))

    def test_vectors_too_large(self):
        big = VEC(ops.MAX_LANES + 1, 8)
        self.assertFalse(ir.well_typed(
            ('G_BUILD_VECTOR', big) + tuple(X(i) for i in range(17)),
            (8,) * 17))


class Lanes(unittest.TestCase):
    """The value of each operator, lane by lane."""

    def ev(self, e, vw, env):
        return vector.evaluate(e, vw, env)

    def test_build_extract_insert(self):
        b = ('G_BUILD_VECTOR', V4, X(0), X(1), X(2), X(3))
        self.assertEqual(self.ev(b, (32,) * 4, [1, 2, 3, 4]), (1, 2, 3, 4))
        v = (10, 11, 12, 13)
        self.assertEqual(self.ev(('G_EXTRACT_VECTOR_ELT:2', 32, X(0)),
                                 (V4,), [v]), 12)
        self.assertEqual(self.ev(('G_EXTRACT_VECTOR_ELT', 32, X(0), X(1)),
                                 (V4, 32), [v, 3]), 13)
        self.assertEqual(self.ev(('G_INSERT_VECTOR_ELT:1', V4, X(0), X(1)),
                                 (V4, 32), [v, 99]), (10, 99, 12, 13))
        self.assertEqual(
            self.ev(('G_INSERT_VECTOR_ELT', V4, X(0), X(1), X(2)),
                    (V4, 32, 32), [v, 99, 3]), (10, 11, 12, 99))

    def test_poison_is_per_lane(self):
        v = (10, None, 12, 13)
        ex = lambda k: self.ev(('G_EXTRACT_VECTOR_ELT:%d' % k, 32, X(0)),
                               (V4,), [v])
        self.assertEqual(ex(0), 10)
        self.assertIsNone(ex(1))
        # A lane-wise operator: only the lane with poison is poison.
        self.assertEqual(self.ev(('G_ADD', V4, X(0), X(0)), (V4,), [v]),
                         (20, None, 24, 26))
        # A poison index is poison in each lane that it can select.
        self.assertIsNone(self.ev(('G_EXTRACT_VECTOR_ELT', 32, X(0), X(1)),
                                  (V4, 32), [(1, 2, 3, 4), None]))

    def test_shuffle_concat_subvector(self):
        a, b = (1, 2, 3, 4), (5, 6, 7, 8)
        self.assertEqual(
            self.ev(('G_SHUFFLE_VECTOR:7.0.5.2', V4, X(0), X(1)), (V4, V4),
                    [a, b]), (8, 1, 6, 3))
        # A shuffle to another number of lanes.
        self.assertEqual(
            self.ev(('G_SHUFFLE_VECTOR:6.1', V2, X(0), X(1)), (V4, V4),
                    [a, b]), (7, 2))
        self.assertEqual(self.ev(('G_CONCAT_VECTORS', V8, X(0), X(1)),
                                 (V4, V4), [a, b]), a + b)
        self.assertEqual(self.ev(('G_EXTRACT_SUBVECTOR:2', V2, X(0)), (V4,),
                                 [a]), (3, 4))
        self.assertEqual(
            self.ev(('G_INSERT_SUBVECTOR:2', V4, X(0), X(1)), (V4, V2),
                    [a, (9, 10)]), (1, 2, 9, 10))

    def test_reductions(self):
        v = (7, 0xffffffff, 3, 12)
        want = {'ADD': 21, 'MUL': (7 * 0xffffffff * 3 * 12) & 0xffffffff,
                'AND': 0, 'OR': 0xffffffff, 'XOR': 7 ^ 0xffffffff ^ 3 ^ 12,
                'SMAX': 12, 'SMIN': 0xffffffff, 'UMAX': 0xffffffff,
                'UMIN': 3}
        for name, r in want.items():
            self.assertEqual(self.ev(('G_VECREDUCE_' + name, 32, X(0)),
                                     (V4,), [v]), r, name)

    def test_compress(self):
        m = VEC(4, 1)
        e = ('G_VECTOR_COMPRESS', V4, X(0), X(1), X(2))
        self.assertEqual(
            self.ev(e, (V4, m, V4), [(1, 2, 3, 4), (0, 1, 0, 1),
                                     (9, 9, 9, 9)]), (2, 4, 9, 9))

    def test_bitcast_and_parts_of_a_lane(self):
        # The first lane has the least significant bits.
        self.assertEqual(self.ev(('G_BITCAST:r', 32, X(0)), (VEC(2, 16),),
                                 [(0x1234, 0xabcd)]), 0xabcd1234)
        self.assertEqual(self.ev(('G_BITCAST:r', VEC(4, 8), X(0)), (32,),
                                 [0xaabbccdd]), (0xdd, 0xcc, 0xbb, 0xaa))
        self.assertEqual(self.ev(('G_UNMERGE_VALUES#3', 16, X(0)),
                                 (V2,), [(0x11112222, 0x33334444)]), 0x3333)


@unittest.skipUnless(HAVE_OPT, 'needs opt')
class AgainstLLVM(unittest.TestCase):
    """The model against the constant folder of LLVM IR."""

    def fold(self, body, ret_ty):
        ir_text = 'define %s @f() {\n%s\n}\n' % (ret_ty, body)
        out = subprocess.run([OPT, '-S', '-passes=instsimplify'],
                             input=ir_text, capture_output=True, text=True,
                             check=True).stdout
        m = re.search(r'ret %s (.*)' % re.escape(ret_ty), out)
        vals = re.findall(r'i32 (-?\d+|poison|undef)', m.group(1)) or \
            [m.group(1).strip()]
        if m.group(1).strip() == 'zeroinitializer':
            return None
        return [None if v in ('poison', 'undef') else int(v) & 0xffffffff
                for v in vals]

    @staticmethod
    def const(v):
        return '<%s>' % ', '.join('i32 %d' % x for x in v)

    def test_shuffle_extract_insert_reduce(self):
        rnd = random.Random(7)
        for _ in range(12):
            a = tuple(rnd.getrandbits(32) for _ in range(4))
            b = tuple(rnd.getrandbits(32) for _ in range(4))
            mask = [rnd.randrange(8) for _ in range(4)]
            k = rnd.randrange(4)
            x = rnd.getrandbits(32)
            got = self.fold(
                '  %%r = shufflevector <4 x i32> %s, <4 x i32> %s, '
                '<4 x i32> %s\n  ret <4 x i32> %%r' % (
                    self.const(a), self.const(b), self.const(mask)),
                '<4 x i32>')
            e = (ops.make_key('G_SHUFFLE_VECTOR', ops.mask_attr(mask)), V4,
                 X(0), X(1))
            if got is not None:
                self.assertEqual(list(vector.evaluate(e, (V4, V4), [a, b])),
                                 got)
            got = self.fold(
                '  %%v = insertelement <4 x i32> %s, i32 %d, i32 %d\n'
                '  %%r = extractelement <4 x i32> %%v, i32 %d\n'
                '  ret i32 %%r' % (self.const(a), x, k, mask[0] % 4), 'i32')
            e = ('G_EXTRACT_VECTOR_ELT:%d' % (mask[0] % 4), 32,
                 ('G_INSERT_VECTOR_ELT:%d' % k, V4, X(0), X(1)))
            self.assertEqual([vector.evaluate(e, (V4, 32), [a, x])], got)
            for name in ('add', 'mul', 'and', 'or', 'xor', 'smax', 'smin',
                         'umax', 'umin'):
                got = self.fold(
                    '  %%r = call i32 @llvm.vector.reduce.%s.v4i32('
                    '<4 x i32> %s)\n  ret i32 %%r' % (name, self.const(a)),
                    'i32')
                e = ('G_VECREDUCE_' + name.upper(), 32, X(0))
                self.assertEqual([vector.evaluate(e, (V4,), [a])], got,
                                 name)


class Proofs(unittest.TestCase):
    def test_lanes_move(self):
        b = ('G_BUILD_VECTOR', V4, X(0), X(1), X(2), X(3))
        src = ('G_EXTRACT_VECTOR_ELT:2', 32, b)
        self.assertEqual(status(src, X(2), (32,) * 4), 'unsat')
        self.assertEqual(status(src, X(1), (32,) * 4), 'sat')

    def test_poison_of_another_lane(self):
        # The replacement must not read a lane that the source does not
        # read: that lane can be poison.
        src = ('G_EXTRACT_VECTOR_ELT:0', 32,
               ('G_BUILD_VECTOR', V2, X(0), X(1)))
        tgt = ('G_ADD', 32, X(0), ('G_XOR', 32, X(1), X(1)))
        self.assertEqual(status(src, tgt, (32, 32)), 'sat')
        # A lane-wise operator on a whole vector.
        src = ('G_EXTRACT_VECTOR_ELT:1', 32, ('G_AND', V2, X(0), X(1)))
        tgt = ('G_AND', 32, ('G_EXTRACT_VECTOR_ELT:1', 32, X(0)),
               ('G_EXTRACT_VECTOR_ELT:1', 32, X(1)))
        self.assertEqual(status(src, tgt, (V2, V2)), 'unsat')

    def test_insert_then_extract(self):
        ins = ('G_INSERT_VECTOR_ELT:0', V4, X(0), X(1))
        self.assertEqual(status(('G_EXTRACT_VECTOR_ELT:0', 32, ins), X(1),
                                (V4, 32)), 'unsat')
        self.assertEqual(
            status(('G_EXTRACT_VECTOR_ELT:1', 32, ins),
                   ('G_EXTRACT_VECTOR_ELT:1', 32, X(0)), (V4, 32)), 'unsat')
        self.assertEqual(
            status(('G_EXTRACT_VECTOR_ELT:1', 32, ins), X(1), (V4, 32)),
            'sat')

    def test_variable_index(self):
        # A lane that the index selects.
        src = ('G_EXTRACT_VECTOR_ELT', 32,
               ('G_INSERT_VECTOR_ELT', V4, X(0), X(1), X(2)), X(2))
        # Not valid: the index can be outside of the vector, and the
        # source then has some value that is not poison.
        self.assertEqual(status(src, X(1), (V4, 32, 32)), 'sat')
        # Each lane is the same value that is not poison.
        splat = ('G_BUILD_VECTOR', V2, X(0), X(0))
        self.assertEqual(status(('G_EXTRACT_VECTOR_ELT:1', 32, splat), X(0),
                                (32,)), 'unsat')
        self.assertEqual(status(('G_EXTRACT_VECTOR_ELT', 32, splat, X(1)),
                                X(0), (32, 32)), 'sat')

    def test_shuffle(self):
        s = ('G_SHUFFLE_VECTOR:0.5.2.7', V4, X(0), X(1))
        src = ('G_SHUFFLE_VECTOR:3.2.1.0', V4, s, s)
        tgt = ('G_SHUFFLE_VECTOR:3.6.1.4', V4, X(1), X(0))
        self.assertEqual(status(src, tgt, (V4, V4)), 'unsat')
        bad = ('G_SHUFFLE_VECTOR:3.6.1.5', V4, X(1), X(0))
        self.assertEqual(status(src, bad, (V4, V4)), 'sat')
        # A lane without a value in the source is some value that is not
        # poison: a constant refines it, a lane of an input does not.
        src = ('G_SHUFFLE_VECTOR:0.u', V2, X(0), X(1))
        lane0 = ('G_EXTRACT_VECTOR_ELT:0', 32, X(0))
        self.assertEqual(status(src, ('G_BUILD_VECTOR', V2, lane0,
                                      ('const', 32, 5)), (V2, V2)), 'unsat')
        self.assertEqual(status(src, ('G_SHUFFLE_VECTOR:0.3', V2, X(0),
                                      X(1)), (V2, V2)), 'sat')

    def test_reduction(self):
        src = ('G_VECREDUCE_ADD', 32, ('G_BUILD_VECTOR', V2, X(0), X(1)))
        self.assertEqual(status(src, ('G_ADD', 32, X(0), X(1)), (32, 32)),
                         'unsat')
        self.assertEqual(status(src, ('G_SUB', 32, X(0), X(1)), (32, 32)),
                         'sat')

    def test_bits_of_lanes(self):
        vw = (VEC(2, 16),)
        src = ('G_TRUNC', 16, ('G_BITCAST:r', 32, X(0)))
        self.assertEqual(status(src, ('G_EXTRACT_VECTOR_ELT:0', 16, X(0)),
                                vw), 'unsat')
        self.assertEqual(status(src, ('G_EXTRACT_VECTOR_ELT:1', 16, X(0)),
                                vw), 'sat')
        src = ('G_UNMERGE_VALUES#3', 32,
               ('G_BUILD_VECTOR', VEC(2, 64), X(0), X(1)))
        self.assertEqual(status(src, ('G_UNMERGE_VALUES#1', 32, X(1)),
                                (64, 64)), 'unsat')
        self.assertTrue(vector.little_endian_only((64, 64), src))
        self.assertFalse(vector.little_endian_only(
            (V4,), ('G_UNMERGE_VALUES#1', 32, X(0))))
        # Scalars with the bits of two lanes each: the second s64 of a
        # <4 x s32> has the lanes 2 and 3, the lane 2 least significant.
        src = ('G_UNMERGE_VALUES#1', 64, X(0))
        self.assertTrue(ops.typecheck('G_UNMERGE_VALUES#1', 64, [V4]))
        self.assertFalse(ops.typecheck('G_UNMERGE_VALUES#2', 64, [V4]))
        for w in (48, 96):
            self.assertFalse(ops.typecheck('G_UNMERGE_VALUES', w,
                                           [VEC(3, 32)]))
        tgt = ('G_MERGE_VALUES', 64, ('G_EXTRACT_VECTOR_ELT:2', 32, X(0)),
               ('G_EXTRACT_VECTOR_ELT:3', 32, X(0)))
        self.assertEqual(status(src, tgt, (V4,)), 'unsat')
        self.assertEqual(status(
            src, ('G_MERGE_VALUES', 64, ('G_EXTRACT_VECTOR_ELT:3', 32, X(0)),
                  ('G_EXTRACT_VECTOR_ELT:2', 32, X(0))), (V4,)), 'sat')
        self.assertTrue(vector.little_endian_only((V4,), src))

    def test_freeze_of_a_vector(self):
        # Each lane is frozen: a lane without poison keeps its value, and
        # a lane with poison gets a value.
        fr = ('G_FREEZE', V2, X(0))
        got = vector.evaluate(fr, (V2,), [(7, None)])
        self.assertEqual(got[0], 7)
        self.assertIsNotNone(got[1])
        src = ('G_EXTRACT_VECTOR_ELT:1', 32, fr)
        # Not the lane itself: it can be poison.
        self.assertEqual(status(src, ('G_EXTRACT_VECTOR_ELT:1', 32, X(0)),
                                (V2,)), 'sat')
        # A G_FREEZE of the replacement is another instruction, with a
        # value of its own for poison.
        tgt = ('G_FREEZE', 32, ('G_EXTRACT_VECTOR_ELT:1', 32, X(0)))
        self.assertEqual(status(src, tgt, (V2,)), 'sat')


class Search(unittest.TestCase):
    def cands(self, src, vw):
        return [ir.to_sexpr(t) for t in vector.candidates(src, vw)]

    def test_replacements(self):
        b = ('G_BUILD_VECTOR', V4, X(0), X(1), X(2), X(3))
        self.assertEqual(self.cands(('G_EXTRACT_VECTOR_ELT:2', 32, b),
                                    (32,) * 4), ['x2'])
        s = ('G_SHUFFLE_VECTOR:0.5.2.7', V4, X(0), X(1))
        self.assertEqual(
            self.cands(('G_SHUFFLE_VECTOR:3.2.1.0', V4, s, s), (V4, V4)),
            ['(G_SHUFFLE_VECTOR:3.6.1.4:v4s32 x1 x0)'])
        re_b = ('G_BUILD_VECTOR', V4) + tuple(
            ('G_EXTRACT_VECTOR_ELT:%d' % j, 32, X(0)) for j in range(4))
        self.assertEqual(self.cands(re_b, (V4,)), ['x0'])
        self.assertEqual(
            self.cands(('G_VECREDUCE_ADD', 32,
                        ('G_BUILD_VECTOR', V2, X(0), X(1))), (32, 32)),
            ['(G_ADD:s32 x0 x1)'])

    def test_no_replacement(self):
        # Not cheaper, or an operator that a rule does not create.
        self.assertEqual(self.cands(
            ('G_EXTRACT_VECTOR_ELT:1', 32, ('G_ADD', V4, X(0), X(1))),
            (V4, V4)), [])
        self.assertEqual(self.cands(
            ('G_UNMERGE_VALUES#3', 32,
             ('G_BUILD_VECTOR', VEC(2, 64), X(0), X(1))), (64, 64)), [])

    def test_each_lane_is_read_once(self):
        b = ('G_BUILD_VECTOR', V2, ('G_EXTRACT_VECTOR_ELT:0', 32, X(0)),
             ('G_EXTRACT_VECTOR_ELT:0', 32, X(0)))
        self.assertFalse(vector.linear(b, (V2,)))
        self.assertFalse(vector.linear(
            ('G_SHUFFLE_VECTOR:0.0', V2, X(0), X(0)), (V2,)))
        self.assertTrue(vector.linear(
            ('G_SHUFFLE_VECTOR:0.3', V2, X(0), X(0)), (V2,)))
        ok = ('G_BUILD_VECTOR', V2, ('G_EXTRACT_VECTOR_ELT:1', 32, X(0)),
              ('G_EXTRACT_VECTOR_ELT:0', 32, X(0)))
        self.assertTrue(vector.linear(ok, (V2,)))


class Rules(unittest.TestCase):
    def test_rule_with_vectors(self):
        b = ('G_BUILD_VECTOR', V4, X(0), X(1), X(2), X(3))
        r = rule_of(('G_EXTRACT_VECTOR_ELT:2', 32, b), (32,) * 4)
        self.assertEqual(r['replacement'], 'x2')
        self.assertEqual(r['precondition'], 'true')
        self.assertFalse(r['needs_one_use'])
        self.assertIsNone(emit.why_not_emittable(r))
        pats = emit.variants(r)[0]
        self.assertIn('(G_BUILD_VECTOR $t0, $x0, $x1, $x2, $x3)', pats)
        self.assertIn('gisynth::isConstantIndex(${dst_i}.getReg(), MRI, 2)',
                      pats[-1])
        guard = emit._cpp_guard(r)
        self.assertIn('uint32_t V0[][6] = {{32, 32, 32, 32, %d, 32}}' % V4,
                      guard)
        self.assertNotIn('Lift', guard)

    def test_a_wrong_replacement_is_no_rule(self):
        b = ('G_BUILD_VECTOR', V4, X(0), X(1), X(2), X(3))
        self.assertIsNone(rule_of(('G_EXTRACT_VECTOR_ELT:2', 32, b),
                                  (32,) * 4, X(1)))

    def test_shuffle_rule_builds_a_shuffle(self):
        s = ('G_SHUFFLE_VECTOR:0.5.2.7', V4, X(0), X(1))
        r = rule_of(('G_SHUFFLE_VECTOR:3.2.1.0', V4, s, s), (V4, V4))
        self.assertIsNone(emit.why_not_emittable(r))
        self.assertIn('gisynth::isShuffleMask(${t0_m}, {0, 5, 2, 7})',
                      emit.variants(r)[0][-1])
        self.assertIn('B.buildShuffleVector(Dst, X1, X0, '
                      'ArrayRef<int>({3, 6, 1, 4}))', emit._cpp_apply(r))

    def test_lane_without_a_value_below_the_root(self):
        # The value below the root has lanes that are not specified: the
        # rule applies only if that value has no other user.
        src = ('G_EXTRACT_VECTOR_ELT:0', 32,
               ('G_SHUFFLE_VECTOR:2.u.u.u', V4, X(0), X(1)))
        r = rule_of(src, (V4, V4))
        self.assertEqual(r['replacement'],
                         '(G_EXTRACT_VECTOR_ELT:2:s32 x0)')
        self.assertTrue(r['needs_one_use'])
        self.assertIn('buildExtractVectorElementConstant(Dst, X0, 2)',
                      emit._cpp_apply(r))

    def test_little_endian_guard(self):
        src = ('G_TRUNC', 16, ('G_BITCAST:r', 32, X(0)))
        r = rule_of(src, (VEC(2, 16),),
                    ('G_EXTRACT_VECTOR_ELT:0', 16, X(0)))
        self.assertIn('isLittleEndian()', emit._cpp_guard(r))

    def test_recheck_proves_the_lanes(self):
        b = ('G_BUILD_VECTOR', V2, X(0), X(1))
        r = rule_of(('G_VECREDUCE_ADD', 32, b), (32, 32))
        d = r['disjuncts'][0]
        st, _ = synth.verify(synth.rule_schedules(r, d['width_maps']), [()],
                             smt.Z3Backend())
        self.assertEqual(st, 'valid')
        # A rule with vectors has no proof with a precondition and no
        # proof for each value of the bits that are not specified.
        st, _ = synth.verify(synth.rule_schedules(r, d['width_maps']), [()],
                             smt.Z3Backend(), strong=True)
        self.assertEqual(st, 'unknown')


class Lift(unittest.TestCase):
    """A rule for scalars whose source is in the corpus with vectors."""

    REC = {
        'fn': 'f', 'root': '%3',
        'inputs': [
            {'reg': '%0', 'w': 32, 'lanes': 4, 'type': '<4 x s32>',
             'zero': '0x0', 'one': '0x0'},
            {'reg': '%1', 'w': 32, 'lanes': 4, 'type': '<4 x s32>',
             'zero': '0x0', 'one': '0x0'}],
        'expr': {'op': 'G_SUB', 'w': 32, 'lanes': 4, 'type': '<4 x s32>',
                 'reg': '%3', 'zero': '0x0', 'one': '0x0', 'args': [
                     {'op': 'G_ADD', 'w': 32, 'lanes': 4,
                      'type': '<4 x s32>', 'reg': '%2', 'zero': '0x0',
                      'one': '0x0', 'uses': 1,
                      'args': [{'in': 0}, {'in': 1}]},
                     {'in': 1}]}}

    def test_reader_gives_the_scalar_source(self):
        inst = corpus.parse_record(self.REC)
        self.assertTrue(inst.lifted)
        self.assertEqual(inst.vw, (32, 32))
        self.assertEqual(ir.to_sexpr(inst.expr),
                         '(G_SUB:s32 (G_ADD:s32 x0 x1) x1)')

    def test_guard_accepts_vectors(self):
        inst = corpus.parse_record(self.REC)
        sy = synth.Synthesizer(smt.Z3Backend())
        rid = sy.add(inst, X(0))
        sy.finalize([inst])
        r = sy.rules[rid]
        self.assertTrue(r['lift'] and emit.lifts(r))
        self.assertIn('/*Lift=*/true', emit._cpp_guard(r))
        # The same rule from a source with scalars only.
        sy = synth.Synthesizer(smt.Z3Backend())
        inst.lifted = False
        rid = sy.add(inst, X(0))
        sy.finalize([inst])
        self.assertNotIn('Lift', emit._cpp_guard(sy.rules[rid]))

    def test_constant_is_built_by_the_builder(self):
        # x - x -> 0: a G_CONSTANT has no vector type.
        rec = json.loads(json.dumps(self.REC))
        rec['expr'] = {'op': 'G_SUB', 'w': 32, 'lanes': 4,
                       'type': '<4 x s32>', 'reg': '%3', 'zero': '0x0',
                       'one': '0x0', 'args': [{'in': 0}, {'in': 0}]}
        rec['inputs'] = rec['inputs'][:1]
        inst = corpus.parse_record(rec)
        sy = synth.Synthesizer(smt.Z3Backend())
        rid = sy.add(inst, ('lit', 32, '0'))
        sy.finalize([inst])
        r = sy.rules[rid]
        self.assertTrue(emit._rule_needs_cpp_apply(r))
        self.assertIn('B.buildConstant(Dst, ', emit._cpp_apply(r))

    def test_not_lane_wise_is_not_lifted(self):
        rec = json.loads(json.dumps(self.REC))
        rec['expr']['args'][1] = {
            'op': 'G_BUILD_VECTOR', 'w': 32, 'lanes': 4,
            'type': '<4 x s32>', 'reg': '%9', 'zero': '0x0', 'one': '0x0',
            'uses': 1, 'args': [{'in': 2}] * 4}
        rec['inputs'].append({'reg': '%8', 'w': 32, 'type': 's32',
                              'zero': '0x0', 'one': '0x0'})
        inst = corpus.parse_record(rec)
        self.assertFalse(inst.lifted)
        self.assertTrue(vector.has_vector(inst.vw, inst.expr))

    def test_scalar_only_operator_is_not_lifted(self):
        # LLVM has no G_UADDE, G_SBFX or G_UBFX of vectors (the builder
        # and the machine verifier refuse them): a rule that makes one
        # stays a rule for scalars.
        for name in ('G_UADDE', 'G_USUBE', 'G_SADDE', 'G_SSUBE',
                     'G_SBFX', 'G_UBFX'):
            self.assertFalse(ops.REGISTRY[name].lanewise, name)
        self.assertFalse(ops.typecheck('G_UADDE', ops.vec(4, 32),
                                       [ops.vec(4, 32), ops.vec(4, 32),
                                        ops.vec(4, 1)]))
        rec = json.loads(json.dumps(self.REC))
        rec['inputs'] = [
            {'reg': '%0', 'w': 1, 'lanes': 4, 'type': '<4 x s1>',
             'zero': '0x0', 'one': '0x0'},
            {'reg': '%1', 'w': 32, 'lanes': 4, 'type': '<4 x s32>',
             'zero': '0x0', 'one': '0x0'},
            {'reg': '%2', 'w': 32, 'lanes': 4, 'type': '<4 x s32>',
             'zero': '0xfffffffe', 'one': '0x1'}]
        rec['expr'] = {
            'op': 'G_SELECT', 'w': 32, 'lanes': 4, 'type': '<4 x s32>',
            'reg': '%4', 'zero': '0x0', 'one': '0x0', 'args': [
                {'in': 0},
                {'op': 'G_ADD', 'w': 32, 'lanes': 4, 'type': '<4 x s32>',
                 'reg': '%3', 'zero': '0x0', 'one': '0x0', 'uses': 1,
                 'args': [{'in': 1}, {'in': 2}]},
                {'in': 1}]}
        inst = corpus.parse_record(rec)
        self.assertTrue(inst.lifted)
        sy = synth.Synthesizer(smt.Z3Backend())
        rid = sy.add(inst, ('G_UADDE', 32, X(1), ('lit', 32, '0'), X(0)))
        self.assertIsNotNone(rid)
        sy.finalize([inst])
        r = sy.rules[rid]
        self.assertFalse(emit.lifts(r))
        self.assertNotIn('Lift', emit._cpp_guard(r))

    def test_reader_attributes(self):
        rec = {'fn': 'f', 'root': '%3', 'inputs': [
            {'reg': '%0', 'w': 32, 'lanes': 4, 'type': '<4 x s32>',
             'zero': '0x0', 'one': '0x0'},
            {'reg': '%1', 'w': 32, 'type': 's32', 'zero': '0x0',
             'one': '0x0', 'const': '0x2'}],
            'expr': {'op': 'G_EXTRACT_VECTOR_ELT', 'w': 32, 'type': 's32',
                     'reg': '%3', 'zero': '0x0', 'one': '0x0', 'args': [
                         {'op': 'G_SHUFFLE_VECTOR', 'w': 32, 'lanes': 4,
                          'type': '<4 x s32>', 'mask': [3, -1, 0, 1],
                          'reg': '%2', 'zero': '0x0', 'one': '0x0',
                          'uses': 1, 'args': [{'in': 0}, {'in': 0}]},
                         {'in': 1}]}}
        inst = corpus.parse_record(rec)
        self.assertEqual(
            ir.to_sexpr(inst.expr),
            '(G_EXTRACT_VECTOR_ELT:2:s32 (G_SHUFFLE_VECTOR:3.u.0.1:v4s32 '
            'x0 x0))')


@unittest.skipUnless(HAVE_LLC, 'needs llc')
class WithLLC(unittest.TestCase):
    def test_probe_functions_pass_the_verifier(self):
        t = targets.get('AMDGPU')
        s = ('G_SHUFFLE_VECTOR:0.5.2.7', V4, X(0), X(1))
        cases = [
            (('G_EXTRACT_VECTOR_ELT:2', 32,
              ('G_BUILD_VECTOR', V4, X(0), X(1), X(2), X(3))), (32,) * 4),
            (('G_SHUFFLE_VECTOR:3.2.1.0', V4, s, s), (V4, V4)),
            (('G_VECREDUCE_ADD', 32, ('G_BUILD_VECTOR', V2, X(0), X(1))),
             (32, 32)),
            (('G_EXTRACT_VECTOR_ELT:0', 32,
              ('G_SHUFFLE_VECTOR:2.u.u.u', V4, X(0), X(1))), (V4, V4)),
        ]
        fns = []
        for k, (src, vw) in enumerate(cases):
            r = rule_of(src, vw)
            fns.append(select.build_mir(r, r['disjuncts'][0]['example'],
                                        'f%d' % k, t))
        p = subprocess.run(
            [LLC] + TRIPLE + ['-x', 'mir', '-run-pass=none',
                              '-verify-machineinstrs', '-o', '/dev/null',
                              '-'],
            input='\n'.join(fns), capture_output=True, text=True)
        self.assertEqual(p.returncode, 0, p.stderr[-2000:])

    def test_extraction_from_ir(self):
        text = '''
define <4 x i32> @lane(<4 x i32> %x, <4 x i32> %y, <4 x i32> %z) {
  %c = icmp ult <4 x i32> %y, %z
  %i = add <4 x i32> %x, <i32 1, i32 1, i32 1, i32 1>
  %s = select <4 x i1> %c, <4 x i32> %i, <4 x i32> %x
  ret <4 x i32> %s
}
define i32 @reduce(i32 %a, i32 %b) {
  %v0 = insertelement <2 x i32> poison, i32 %a, i32 0
  %v1 = insertelement <2 x i32> %v0, i32 %b, i32 1
  %r = call i32 @llvm.vector.reduce.add.v2i32(<2 x i32> %v1)
  ret i32 %r
}
declare i32 @llvm.vector.reduce.add.v2i32(<2 x i32>)
'''
        with tempfile.TemporaryDirectory() as d:
            out = os.path.join(d, 'c.jsonl')
            subprocess.run(
                [LLC] + TRIPLE + ['-O2', '-global-isel',
                                  '-amdgpu-gisel-synth-corpus',
                                  '-gisel-synth-corpus-out=' + out, '-o',
                                  '/dev/null', '-'],
                input=text, capture_output=True, text=True, check=True)
            insts, stats = corpus.load([out])
        self.assertEqual(stats['unsupported'], 0)
        srcs = {ir.to_sexpr(i.expr): i for i in insts}
        lane = srcs['(G_SELECT:s32 (G_ICMP:ult:s1 x0 x1) (G_ADD:s32 x2 x3) '
                    'x2)']
        self.assertTrue(lane.lifted)
        # The constant with one value in each lane is the value of a lane.
        self.assertEqual(lane.consts[3], 1)
        # The target expands the reduction before the translation. The
        # constant index of the lane is an attribute.
        self.assertIn('(G_EXTRACT_VECTOR_ELT:0:s32 (G_ADD:v2s32 x0 x1))',
                      srcs)


if __name__ == '__main__':
    unittest.main()
