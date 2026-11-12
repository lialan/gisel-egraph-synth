#!/usr/bin/env python3
"""Tests of constants: the bits of G_CONSTANT and G_FCONSTANT (also of a
pointer), addresses as defined inputs, floating-point literals in a
replacement, conditions on a floating-point constant, constants that the
compiler computes, and the kernels of the floating-point operators.

Run:  python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests
"""

import importlib.util
import json
import os
import random
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

import numpy as np  # noqa: E402
import z3  # noqa: E402

from girs import corpus, discover, emit, fp, ir, kernels  # noqa: E402
from girs import ops, precond, smt, synth, targets  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    'gi_rule_synth_cli', os.path.join(ROOT, 'gi-rule-synth.py'))
cli = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cli)

LLC = os.environ.get('GIRS_LLC') or os.path.join(
    os.path.dirname(os.path.dirname(os.path.dirname(ROOT))), 'build', 'bin',
    'llc')
HAVE_LLC = os.path.exists(LLC)
F = fp.Fraction
W = 32
ENV = fp.ENV_BITS


def V(i):
    return ('var', i)


def L(k, w=W):
    return ('lit', w, k)


def op(name, w, *args):
    return (name, w) + args


def fbits(x, w=W):
    """The bit pattern of the number x (a Fraction or an int)."""
    x = F(x)
    return fp.encode(int(x < 0), abs(x), w)


def instance(src, vw, consts=None, nofpe=False):
    """An instance of the corpus: a constant has its bits as facts, and
    the environment says if the program reads the exceptions."""
    consts = consts or [None] * len(vw)
    env = ir.env_vars(src)
    facts = [((0, fp.ENV_IGNORE, True) if nofpe else
              (fp.ENV_IGNORE, 0, True)) if i in env else
             (0, 0) if c is None else (~c & ops.mask(w), c, True)
             for i, (c, w) in enumerate(zip(consts, vw))]
    return corpus.Instance(src, tuple(vw), facts, consts,
                           [1] * len(ir.interior_nodes(src)), [],
                           [('f', 'fn', '%0')])


def rule_of(src, tgt, vw, consts=None, nofpe=False, cv=None):
    """The rule that the synthesizer makes of a candidate, or None."""
    s = synth.Synthesizer(smt.Z3Backend())
    inst = instance(src, vw, consts, nofpe)
    if cv is not None:
        inst.const_vars = cv
    if s.add(inst, tgt) is None:
        return None
    s.finalize([inst])
    (rule,) = s.rules.values()
    return rule


def cpp(rule):
    out = emit._cpp_guard(rule)
    if emit._rule_needs_cpp_apply(rule):
        out += emit._cpp_apply(rule)
    return out


def targets_of(inst, **limits):
    lim = discover.Limits(grammar='auto', **limits)
    cands, _ = discover.discover(inst, smt.Z3Backend(), lim,
                                 discover.Context(lim), {})
    return [c['tgt'] for c in cands]


class LiteralTest(unittest.TestCase):
    def test_bits_of_the_literals(self):
        self.assertEqual(fp.literal_bits('f1', 32), 0x3F800000)
        self.assertEqual(fp.literal_bits('f-1', 32), 0xBF800000)
        self.assertEqual(fp.literal_bits('f-0', 16), 0x8000)
        self.assertEqual(fp.literal_bits('f2', 16), 0x4000)
        self.assertEqual(fp.literal_bits('f0.5', 64), 0x3FE0000000000000)
        self.assertEqual(fp.literal_bits('f0', 64), 0)
        for k in ir.FP_LITERALS:
            self.assertIn(k, fp.LITERAL_CPP)

    def test_a_literal_is_a_value_of_each_format(self):
        # The evaluator and the solver give a literal the bits of its
        # format.
        for w in (16, 32, 64):
            for k in ir.FP_LITERALS:
                e = ('G_FNEG', w, ('lit', w, k))
                want = fp.literal_bits(k, w) ^ fp.sign_bit(w)
                self.assertEqual(ir.evaluate(e, (), {}), want)
                enc = smt.Encoder((), w)
                self.assertEqual(
                    z3.simplify(enc.enc_full(e)[0]).as_long(), want)

    def test_exact_inverse(self):
        yes = [2, F(1, 8), 1, -4, F(-1, 2)]
        no = [3, 0, F(1, 3), 10]
        for w in (16, 32, 64):
            for x in yes:
                self.assertTrue(fp.has_exact_inverse(fbits(x, w), w), (x, w))
            for x in no:
                self.assertFalse(fp.has_exact_inverse(fbits(x, w), w),
                                 (x, w))
            self.assertFalse(fp.has_exact_inverse(fp.inf(w), w))
            self.assertFalse(fp.has_exact_inverse(fp.qnan(w), w))
            # The reciprocal of the smallest normal number is a number;
            # that of the largest power of 2 is a subnormal number.
            self.assertTrue(fp.has_exact_inverse(fp.min_normal(w), w))
            top = fp.inf(w) - (1 << (fp.FORMATS[w][1] - 1))
            self.assertFalse(fp.has_exact_inverse(top, w))
            self.assertFalse(fp.has_exact_inverse(1, w))

    def test_exact_inverse_of_the_solver(self):
        rng = random.Random(2)
        for w in (16, 32):
            eb, p = fp.FORMATS[w]
            x = z3.BitVec('x', w)
            f = fp.z3_has_exact_inverse(x)
            vals = [0, 1, fp.inf(w), fp.qnan(w), fp.min_normal(w),
                    fp.max_finite(w)]
            vals += [rng.getrandbits(eb + 1) << (p - 1) for _ in range(60)]
            vals += [rng.getrandbits(w) for _ in range(60)]
            for v in vals:
                got = z3.simplify(z3.substitute(f, (x, z3.BitVecVal(v, w))))
                self.assertEqual(z3.is_true(got),
                                 fp.has_exact_inverse(v, w), (hex(v), w))

    def test_an_exact_inverse_is_exact(self):
        # 1 / c is exact, and x / c is x * (1 / c) for each x.
        rng = random.Random(3)
        for w in (16, 32):
            eb, p = fp.FORMATS[w]
            for _ in range(200):
                c = rng.getrandbits(eb + 1) << (p - 1)
                if not fp.has_exact_inverse(c, w):
                    continue
                r = fp.div(fp.literal_bits('f1', w), c, w)
                self.assertEqual(fp.div(r, fp.literal_bits('f1', w), w), r)
                for _ in range(20):
                    x = rng.getrandbits(w)
                    self.assertTrue(fp.same_bits(fp.div(x, c, w),
                                                 fp.mul(x, r, w), w))


class ConstantRuleTest(unittest.TestCase):
    """Rules with a floating-point constant: a literal in the
    replacement, a condition on the constant, and a constant that the
    compiler computes when the rule applies."""

    def test_divide_by_a_constant_with_an_exact_inverse(self):
        src = op('G_FDIV', W, V(0), V(1))
        tgt = op('G_FMUL', W, V(0), op('G_FDIV', W, L('f1'), V(1)))
        r = rule_of(src, tgt, (W, W), [None, fbits(4)], cv=(1,))
        self.assertIsNotNone(r)
        self.assertIn('exact_inverse(x1)', r['precondition'])
        self.assertEqual(list(r['const_vars']), [1])
        self.assertIsNone(emit.why_not_emittable(r))
        text = cpp(r)
        self.assertIn('hasExactInverse(K1.getConstant())', text)
        self.assertIn('fpDivBits(', text)
        self.assertIn('/*IsFP=*/true', text)

    def test_divide_by_another_constant_is_refuted(self):
        # x / 3 is not x * (1 / 3): the reciprocal is rounded.
        src = op('G_FDIV', W, V(0), V(1))
        tgt = op('G_FMUL', W, V(0), op('G_FDIV', W, L('f1'), V(1)))
        i = instance(src, (W, W), [None, fbits(3)])
        res = discover.prove_concrete(i, tgt, smt.Z3Backend(),
                                      const_vars=(1,))
        self.assertEqual(res.status, 'sat')
        i = instance(src, (W, W), [None, fbits(4)])
        res = discover.prove_concrete(i, tgt, smt.Z3Backend(),
                                      const_vars=(1,))
        self.assertEqual(res.status, 'unsat')

    def test_negated_constant(self):
        # x - c -> x + (-c) for each constant: the compiler negates it.
        src = op('G_FSUB', W, V(0), V(1))
        tgt = op('G_FADD', W, V(0), op('G_FNEG', W, V(1)))
        r = rule_of(src, tgt, (W, W), [None, fbits(3)], cv=(1,))
        self.assertIsNotNone(r)
        self.assertEqual(r['precondition'], 'true')
        self.assertIn('fpNegBits(C1)', cpp(r))

    def test_condition_on_one_constant(self):
        # (x * c) * c -> x only for c == -1.0 (and 1.0, another rule).
        src = op('G_FMUL', W, op('G_FMUL', W, V(0), V(1)), V(1))
        r = rule_of(src, V(0), (W, W), [None, fbits(-1)])
        self.assertIsNotNone(r)
        self.assertIn('-1.0', r['precondition'])
        self.assertIn('getFPLiteralBits(FPLiteral::NegOne', cpp(r))

    def test_wrong_literal_is_refuted(self):
        # x - x is not +0.0: x can be an infinity or a NaN.
        src = op('G_FSUB', W, V(0), V(0))
        self.assertIsNone(rule_of(src, L('f0'), (W,)))

    def test_search_finds_a_rule_for_a_constant(self):
        # x / -1.0 -> -x.
        i = instance(op('G_FDIV', W, V(0), V(1)), (W, W),
                     [None, fbits(-1)])
        self.assertIn(op('G_FNEG', W, V(0)), targets_of(i))

    def test_search_finds_a_literal(self):
        # (-x) < -0.0 -> x > 0.0: the replacement has a constant that the
        # source does not have.
        src = op('G_FCMP:olt', 1, op('G_FNEG', W, V(0)), V(1))
        i = instance(src, (W, W), [None, fp.literal_bits('f-0', W)])
        tg = targets_of(i)
        self.assertIn(op('G_FCMP:ogt', 1, V(0), L('f0')), tg)
        r = rule_of(src, op('G_FCMP:ogt', 1, V(0), L('f0')), (W, W),
                    [None, fp.literal_bits('f-0', W)])
        self.assertIsNotNone(r)
        self.assertIn('getFPLiteralBits(FPLiteral::Zero', cpp(r))

    def test_literal_only_for_a_float_value(self):
        # A literal of a floating-point value is not an operand of an
        # operator on integers, and it has a format.
        self.assertIsNone(
            ir.type_of(op('G_ADD', W, V(0), L('f1')), (W,), ('i',)))
        self.assertEqual(
            ir.type_of(op('G_FADD', W, V(0), L('f1')), (W,), ('f',)),
            (W, 'f'))
        self.assertFalse(ir.well_typed(L('f1', 8), ()))


class FloatKernelTest(unittest.TestCase):
    """A kernel of a floating-point operator gives the bits of the exact
    evaluator."""

    def _values(self, w, rng, n):
        eb, p = fp.FORMATS[w]
        bias = fp._bias(w)
        sp = [0, 1, 2, fp.inf(w), fp.qnan(w), fp.inf(w) + 1, fp.inf(w) - 1,
              1 << (p - 1), (1 << (p - 1)) - 1]
        sp += [fp.literal_bits(k, w) for k in ir.FP_LITERALS]
        for num, den in ((1, 2), (3, 2), (5, 2), (7, 2), (1, 4), (3, 4),
                         (1, 3), (1 << (p - 1), 1), ((1 << p) - 1, 2),
                         ((1 << p) + 1, 2)):
            sp.append(fp.encode(0, F(num, den), w))
        sp += [v ^ fp.sign_bit(w) for v in sp]
        for _ in range(n):
            e = rng.choice([0, 1, 2, bias - 1, bias, bias + 1, bias + p - 2,
                            bias + p - 1, bias + p, (1 << eb) - 2,
                            rng.randrange(1 << eb)])
            sp.append((rng.getrandbits(1) << (w - 1)) | (e << (p - 1)) |
                      rng.getrandbits(p - 1))
        return sp

    def test_kernels_match_the_evaluator(self):
        rng = random.Random(7)
        U64 = np.uint64
        for name in kernels.FP_KERNELS:
            info = ops.REGISTRY[name]
            for key in ops.search_keys(name, [3]):
                _, attr, res = ops.parse(key)
                for w in (16, 32, 64):
                    rw = 1 if name == 'G_FCMP' else w
                    ws = [w] * info.operands
                    if not info.typecheck(rw, ws, attr, res):
                        continue
                    vs = self._values(w, rng, 30)
                    cols = [np.array([[rng.choice(vs) for _ in vs]
                                      for _ in range(6)], U64) for _ in ws]
                    oks = [np.ones(c.shape, bool) for c in cols]
                    v, _ = kernels.apply(key, rw, ws, cols, oks)
                    g, _ = kernels.generic(key, rw, ws, cols, oks)
                    self.assertTrue(np.array_equal(v, g), (key, w))

    def test_fused_multiply_add_at_a_tie(self):
        # a * b is the middle of two numbers of the format, and c moves
        # it: one rounding, not two.
        U64 = np.uint64
        for w in (16, 32):
            eb, p = fp.FORMATS[w]
            a, b, c = [], [], []
            for k in range(1, p):
                for sign in (0, 1):
                    for cv in (0, fp.sign_bit(w), 1, 1 | fp.sign_bit(w),
                               fbits(F(1, 2), w), fbits(F(-1, 2), w),
                               fbits(2 ** (p + 1), w), fp.inf(w),
                               fp.max_finite(w, 1)):
                        a.append(fp.encode(sign, F(2 ** k + 1), w))
                        b.append(fp.encode(0, F(2 ** (p - k) + 1), w))
                        c.append(cv)
            cols = [np.array([x], U64) for x in (a, b, c)]
            oks = [np.ones(x.shape, bool) for x in cols]
            for key in ('G_FMA', 'G_FMAD'):
                v, _ = kernels.apply(key, w, [w] * 3, cols, oks)
                g, _ = kernels.generic(key, w, [w] * 3, cols, oks)
                self.assertTrue(np.array_equal(v, g), (key, w))

    def test_no_kernel_for_another_format(self):
        # binary64 has no kernel for the fused operation: the evaluator
        # of the registry gives the value.
        U64 = np.uint64
        cols = [np.array([[fbits(3, 64)]], U64) for _ in range(3)]
        oks = [np.ones(c.shape, bool) for c in cols]
        counters = {}
        v, _ = kernels.apply('G_FMA', 64, [64] * 3, cols, oks, counters)
        self.assertEqual(int(v[0, 0]), fbits(12, 64))
        self.assertEqual(counters['generic_terms'], 1)


CS_MIR = '''
--- |
  @g = external global i32
  define void @fconst() { ret void }
  define void @pconst() { ret void }
  define void @addr() { ret void }
  define void @frame() { ret void }
...
---
name: fconst
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = G_FCONSTANT float 2.000000e+00
    %2:_(s32) = G_FMUL %0, %1
    $vgpr0 = COPY %2
    SI_RETURN implicit $vgpr0
...
---
name: pconst
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0
    %0:_(p0) = G_CONSTANT i64 16
    %1:_(s64) = G_PTRTOINT %0
    %2:_(s32) = G_TRUNC %1
    $vgpr0 = COPY %2
    SI_RETURN implicit $vgpr0
...
---
name: addr
tracksRegLiveness: true
body: |
  bb.0:
    %0:_(p0) = G_GLOBAL_VALUE @g
    %1:_(p0) = G_FREEZE %0
    %2:_(s64) = G_PTRTOINT %1
    %3:_(s32) = G_TRUNC %2
    $vgpr0 = COPY %3
    SI_RETURN implicit $vgpr0
...
---
name: frame
tracksRegLiveness: true
stack:
  - { id: 0, size: 4, alignment: 4 }
body: |
  bb.0:
    %0:_(p5) = G_FRAME_INDEX %stack.0
    %1:_(p5) = G_FREEZE %0
    %2:_(s32) = G_PTRTOINT %1
    $vgpr0 = COPY %2
    SI_RETURN implicit $vgpr0
...
'''


@unittest.skipUnless(HAVE_LLC, 'no llc (set GIRS_LLC)')
class RealExtractionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        mir = os.path.join(cls.tmp.name, 'cs.mir')
        with open(mir, 'w') as f:
            f.write(CS_MIR)
        _, out = cli._extract_one(LLC, mir, cls.tmp.name, 'mir',
                                  targets.get('AMDGPU'))
        assert out, 'the extractor failed'
        with open(out) as f:
            cls.records = [json.loads(l) for l in f if l.strip()]
        cls.insts, cls.stats = corpus.load([out])

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _inst(self, sexpr, consts=None):
        (i,) = [i for i in self.insts if ir.to_sexpr(i.expr) == sexpr and
                (consts is None or list(i.consts) == consts)]
        return i

    def _inputs(self, fn, opcode):
        return [i for r in self.records if r['fn'] == fn
                for i in r['inputs'] if i.get('def') == opcode]

    def test_every_record_is_read(self):
        self.assertEqual(self.stats['unsupported'], 0)

    def test_float_constant_has_its_bits(self):
        (c,) = self._inputs('fconst', 'G_FCONSTANT')
        self.assertEqual(c['const'], '0x40000000')
        self.assertTrue(c['noundef'])
        i = self._inst('(G_FMUL:s32 x0 x1)')
        self.assertEqual(list(i.consts), [None, 0x40000000])
        self.assertEqual(tuple(i.facts[1]),
                         (0xBFFFFFFF, 0x40000000, True))

    def test_pointer_constant_has_its_bits(self):
        i = self._inst('(G_TRUNC:s32 (G_PTRTOINT:s64 x0))', [16])
        self.assertEqual(tuple(i.facts[0]), (ir.mask(64) ^ 16, 16, True))

    def test_address_is_a_defined_input(self):
        # The bits of an address are not known; it is neither undef nor
        # poison.
        for fn, opcode in (('addr', 'G_GLOBAL_VALUE'),
                           ('frame', 'G_FRAME_INDEX')):
            ins = self._inputs(fn, opcode)
            self.assertTrue(ins, fn)
            for c in ins:
                self.assertTrue(c['address'] and c['noundef'], c)
                self.assertNotIn('const', c)

    def test_freeze_of_an_address_is_removed(self):
        i = self._inst('(G_FREEZE:s64 x0)')
        self.assertIs(i.facts[0][2], True)
        s = synth.Synthesizer(smt.Z3Backend())
        self.assertIsNotNone(s.add(i, V(0)))
        s.finalize([i])
        (r,) = s.rules.values()
        self.assertIn('defined(x0)', r['precondition'])


if __name__ == '__main__':
    unittest.main()
