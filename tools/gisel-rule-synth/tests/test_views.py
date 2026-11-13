#!/usr/bin/env python3
"""Tests of the analysis views of the synthesizer (girs/views.py): the AC,
linear and slice signatures, and the proposals of the views, which only
the proofs accept.

Run:  python3 -m unittest discover -s tools/gisel-rule-synth/tests
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

import z3  # noqa: E402

from girs import corpus, discover, ir, precond, smt, synth, views  # noqa

M32 = ir.mask(32)


def V(i):
    return ('var', i)


def L(w, k):
    return ('lit', w, k)


X, Y, Z, C1, C2 = V(0), V(1), V(2), V(3), V(4)
VW = (32,) * 5


def exact(w, c):
    return (~c & ir.mask(w), c)


def inst(expr, vw, consts=None, facts=None):
    n = len(vw)
    consts = list(consts or [None] * n)
    facts = list(facts or [exact(w, c) if c is not None else (0, 0)
                           for w, c in zip(vw, consts)])
    return corpus.Instance(expr, vw, facts, consts,
                           [1] * len(ir.interior_nodes(expr)), [],
                           [('test', 'f', '%0')])


def refines(src, tgt, vw, const_vars=(), facts=None):
    """True if ``tgt`` refines ``src`` for every input (poison included),
    the variables ``const_vars`` matched as constants of any value; with
    ``facts``, for the inputs with these known bits."""
    i = inst(src, vw, facts=facts or [(0, 0)] * len(vw))
    return discover.prove_concrete(i, tgt, smt.Z3Backend(),
                                   const_vars).status == 'unsat'


def ac(e, vw=VW, consts=None, flagged=()):
    return views.ac_signature(e, vw, consts, flagged)


def lin(e, vw=VW, consts=None):
    return views.linear_signature(e, vw, consts)


def sl(e, vw=VW, consts=None):
    return views.slice_signature(e, vw, consts)


def add(a, b, w=32):
    return ('G_ADD', w, a, b)


def xor(a, b, w=32):
    return ('G_XOR', w, a, b)


def and_(a, b, w=32):
    return ('G_AND', w, a, b)


class ACSignatureTest(unittest.TestCase):
    def test_operators_come_from_the_table(self):
        # The traits are read from gmir_ops.json: G_SUB is not AC, G_ADD
        # and G_XOR are; an operator without a multiplicity rule is not
        # flattened.
        self.assertIsNotNone(views.ac_operator('G_ADD'))
        self.assertIsNotNone(views.ac_operator('G_XOR'))
        self.assertIsNone(views.ac_operator('G_SUB'))
        self.assertIsNone(views.ac_operator('G_UADDO'))

    def test_add_keeps_the_count(self):
        twice = add(add(X, X), Y)
        self.assertNotEqual(ac(twice), ac(add(X, Y)))
        self.assertEqual(ac(twice), ac(add(X, add(Y, X))))
        self.assertEqual(ac(twice), ('ac', 'G_ADD', 32, (X, X, Y), None))

    def test_xor_keeps_the_parity(self):
        self.assertEqual(ac(xor(xor(X, Y), X)), Y)
        self.assertEqual(ac(xor(X, X)), ('const', 32, 0))
        self.assertEqual(ac(xor(xor(X, X), X)), X)
        self.assertEqual(ac(xor(xor(X, Y), xor(Y, Z))), ac(xor(Z, X)))

    def test_and_or_min_max_keep_one(self):
        self.assertEqual(ac(and_(and_(X, Y), X)), ac(and_(Y, X)))
        self.assertEqual(ac(('G_OR', 32, X, X)), X)
        self.assertEqual(ac(('G_UMIN', 32, X, ('G_UMIN', 32, Y, X))),
                         ac(('G_UMIN', 32, Y, X)))
        # Operands in another order are one leaf.
        self.assertEqual(ac(xor(and_(X, Y), and_(Y, X))), ('const', 32, 0))

    def test_constants_fold_modulo_the_width(self):
        consts = (None, None, None, M32, 1)
        e = add(add(X, C1), C2)
        # 0xffffffff + 1 is 0 in 32 bits: the term is x.
        self.assertEqual(ac(e, consts=consts), X)
        # In 64 bits it is 0x100000000.
        self.assertEqual(ac(add(add(X, C1, 64), C2, 64), (64,) * 5, consts),
                         ('ac', 'G_ADD', 64, (X,), 1 << 32))

    def test_absorbing_constants(self):
        consts = (None, None, None, 0xf0, 0x0f)
        self.assertEqual(ac(and_(and_(X, C1), C2), consts=consts),
                         ('const', 32, 0))
        consts = (None, None, None, 0xffff0000, 0x0000ffff)
        self.assertEqual(ac(('G_OR', 32, ('G_OR', 32, X, C1), C2),
                            consts=consts), ('const', 32, M32))
        # Without the values of the constants nothing folds.
        self.assertEqual(ac(and_(and_(X, C1), C2)),
                         ('ac', 'G_AND', 32, (X, C1, C2), None))

    def test_a_flagged_node_is_a_leaf(self):
        # GIEGraph flattens only unflagged nodes: a flagged node (nsw) is
        # a leaf, as an AC term with it would only be a refinement. It is
        # not an AC term of its own either (canonicalizeAC merges only
        # unflagged nodes).
        inner = add(X, Y)
        e = add(inner, Z)
        self.assertEqual(ac(e), ('ac', 'G_ADD', 32, (X, Y, Z), None))
        self.assertEqual(ac(e, flagged={inner}),
                         ('ac', 'G_ADD', 32,
                          tuple(sorted((inner, Z), key=repr)), None))
        self.assertEqual(ac(add(Y, X), flagged={add(Y, X)}), inner)

    def test_vectors_and_other_types_are_not_flattened(self):
        from girs import ops
        v4 = ops.vec(4, 32)
        e = ('G_ADD', v4, ('G_ADD', v4, X, Y), Z)
        self.assertEqual(ac(e, (v4,) * 3), ('G_ADD', v4, ('G_ADD', v4, X, Y),
                                            Z))


class LinearSignatureTest(unittest.TestCase):
    def test_coefficients(self):
        two_x = ('lin', 32, 0, ((X, 2),))
        consts = (None, 2, None, 1)
        self.assertEqual(lin(add(X, X)), two_x)
        self.assertEqual(lin(('G_SHL', 32, X, C1), consts=consts), two_x)
        self.assertEqual(lin(('G_MUL', 32, X, Y), consts=consts), two_x)
        three = (None, 3)
        self.assertEqual(lin(('G_SUB', 32, ('G_MUL', 32, Y, X), X),
                             consts=three), two_x)

    def test_coefficients_wrap_around(self):
        consts = (None, 1 << 31)
        e = add(('G_MUL', 32, X, Y), ('G_MUL', 32, Y, X))
        # 2^31 + 2^31 is 0 modulo 2^32, but not modulo 2^64.
        self.assertEqual(lin(e, consts=consts), ('const', 32, 0))
        e64 = add(('G_MUL', 64, X, Y), ('G_MUL', 64, Y, X), 64)
        self.assertEqual(lin(e64, (64, 64), consts),
                         ('lin', 64, 0, ((X, 1 << 32),)))
        shl = ('G_SHL', 32, ('G_SHL', 32, X, C1), C2)
        self.assertEqual(lin(shl, consts=(None, None, None, 31, 1)),
                         ('const', 32, 0))

    def test_negation_and_subtraction(self):
        self.assertEqual(lin(('G_SUB', 32, L(32, '0'), X)),
                         ('lin', 32, 0, ((X, M32),)))
        self.assertEqual(lin(('G_SUB', 32, X, X)), ('const', 32, 0))
        self.assertEqual(lin(('G_SUB', 32, add(X, Y), X)), Y)
        self.assertEqual(lin(add(add(X, C1), ('G_SUB', 32, Y, C1)),
                             consts=(None, None, None, 7)),
                         lin(add(Y, X)))

    def test_non_linear_leaves(self):
        # A leaf in another operand order is the same leaf.
        e = add(and_(X, Y), and_(Y, X))
        self.assertEqual(lin(e), ('lin', 32, 0, ((ac(and_(X, Y)), 2),)))
        # A product of two values and a shift by a value are leaves.
        self.assertEqual(lin(('G_MUL', 32, X, Y)), ac(('G_MUL', 32, Y, X)))
        self.assertEqual(lin(add(('G_SHL', 32, X, Y), X)),
                         ('lin', 32, 0, tuple(sorted(
                             ((X, 1), (('G_SHL', 32, X, Y), 1)), key=repr))))
        # A shift by the width or more is poison, not a multiplication.
        big = ('G_SHL', 32, X, C1)
        self.assertEqual(lin(big, consts=(None, None, None, 32)),
                         ('G_SHL', 32, X, ('const', 32, 32)))


class SliceSignatureTest(unittest.TestCase):
    def test_one_slice_many_forms(self):
        consts = (None, 8, 0xff, 0xff00, 8)
        want = ('slice', 32, X, 8, 8, 0)
        forms = [and_(('G_LSHR', 32, X, Y), Z),
                 ('G_UBFX', 32, X, Y, C2),
                 ('G_LSHR', 32, and_(X, C1), Y),
                 ('G_ZEXT', 32, ('G_TRUNC', 8, ('G_LSHR', 32, X, Y)))]
        for e in forms:
            self.assertEqual(sl(e, consts=consts), want, ir.to_sexpr(e))

    def test_other_slices(self):
        consts = (None, 8, 0x7f, 0xff)
        self.assertEqual(sl(and_(('G_LSHR', 32, X, Y), Z), consts=consts),
                         ('slice', 32, X, 8, 7, 0))
        # The bits [0, 8) shifted right by 8: no bit is left.
        self.assertEqual(sl(('G_LSHR', 32, and_(X, C1), Y), consts=consts),
                         ('const', 32, 0))

    def test_not_slices(self):
        # A mask that is not contiguous, and a field outside the value
        # (poison), are not slices.
        e = and_(('G_LSHR', 32, X, Y), Z)
        self.assertNotEqual(sl(e, consts=(None, 8, 0xf0f))[0], 'slice')
        self.assertNotEqual(sl(('G_UBFX', 32, X, Y, Z),
                               consts=(None, 28, 8))[0], 'slice')


class SignatureSoundnessTest(unittest.TestCase):
    """Expressions with one signature have one value on defined inputs
    (each read of an input the same value). Random expressions, grouped
    by signature, are compared on random inputs."""

    def test_equal_signatures_have_equal_values(self):
        rng = random.Random(7)
        w = 8
        leaves = [V(0), V(1), V(2), V(3)]
        consts = (None, None, None, 0x35)
        ops_ = ['G_ADD', 'G_SUB', 'G_XOR', 'G_AND', 'G_OR', 'G_MUL',
                'G_UMIN', 'G_SMAX', 'G_SHL']

        def gen(d):
            if d == 0 or rng.random() < 0.25:
                return rng.choice(leaves + [L(w, '1'), L(w, '-1')])
            op = rng.choice(ops_)
            if op == 'G_SHL':
                return (op, w, gen(d - 1), rng.choice([L(w, '1'), V(3)]))
            return (op, w, gen(d - 1), gen(d - 1))
        exprs = {gen(3) for _ in range(1500)}
        vw = (w,) * 4
        envs = [(rng.randrange(256), rng.randrange(256), rng.randrange(256),
                 0x35) for _ in range(64)]
        pairs = 0
        for kind in ('ac', 'linear'):
            groups = views.group(
                sorted(exprs, key=repr),
                lambda e: views.signature(e, vw, consts, kind))
            for sig, es in groups.items():
                vals = [[ir.evaluate(e, vw, env) for env in envs]
                        for e in es]
                for v in vals[1:]:
                    pairs += 1
                    for a, b in zip(vals[0], v):
                        if a is not None and b is not None:
                            self.assertEqual(a, b, (kind, sig, es))
        # Not a vacuous test: many expressions share a signature.
        self.assertGreater(pairs, 200)

    def test_slices_have_equal_values(self):
        rng = random.Random(3)
        vw = (32, 32, 32, 32)
        for lo in (0, 3, 8):
            for n in (1, 5, 8):
                c = (None, lo, ir.mask(n), ir.mask(n) << lo, n)
                forms = [and_(('G_LSHR', 32, X, Y), Z),
                         ('G_LSHR', 32, and_(X, C1), Y),
                         ('G_UBFX', 32, X, Y, ('var', 4))]
                vw5 = (32,) * 5
                sigs = {sl(e, vw5, c) for e in forms}
                self.assertEqual(len(sigs), 1)
                for _ in range(32):
                    env = (rng.getrandbits(32),) + tuple(c[1:])
                    vals = {ir.evaluate(e, vw5, env) for e in forms}
                    self.assertEqual(len(vals), 1)
        del vw


class ProposalTest(unittest.TestCase):
    def setUp(self):
        self.backend = smt.Z3Backend()
        self.dlim = discover.Limits()

    def props(self, i, kinds=views.KINDS):
        st = {}
        out = views.propose(i, self.dlim, views.Limits(kinds), st)
        return {ir.to_sexpr(p['tgt']): p for p in out}, st

    def rule(self, i, tgt, cv=()):
        sy = synth.Synthesizer(self.backend)
        i.const_vars = tuple(cv)
        rid = sy.add(i, tgt, provenance={'discovery': 'views-test+smt'})
        if rid is None:
            return None
        sy.finalize([i])
        return synth.strip_private(sy.rules[rid])

    def test_folded_constant_is_computed(self):
        # (x + c1) + c2 -> x + (c1 + c2): one operation less, for every
        # pair of constants (the proof covers each value of them).
        vw = (32, 32, 32)
        i = inst(add(add(X, Y), Z), vw, [None, 3, 5])
        got, _ = self.props(i)
        p = got['(G_ADD:s32 x0 (G_ADD:s32 x1 x2))']
        self.assertEqual(p['const_vars'], (1, 2))
        self.assertTrue(refines(i.expr, p['tgt'], vw, (1, 2)))
        r = self.rule(i, p['tgt'], p['const_vars'])
        self.assertEqual(r['precondition'], 'true')
        # Two constants of the rule (in its own numbering) are computed
        # with; the third variable is the matched value.
        self.assertEqual(len(r['const_vars']), 2)
        self.assertEqual(r['cost'], {'source': 2, 'replacement': 1})
        self.assertEqual(r['class'], 'reduces_cost')

    def test_wrap_around_of_a_folded_constant(self):
        # The constant is computed modulo 2^W when the rule applies: the
        # rule holds at every width of its schedules.
        vw = (8, 8, 8)
        i = inst(add(add(X, Y, 8), Z, 8), vw, [None, 0xff, 1])
        got, _ = self.props(i)
        p = got['(G_ADD:s8 x0 (G_ADD:s8 x1 x2))']
        r = self.rule(i, p['tgt'], p['const_vars'])
        self.assertEqual(r['precondition'], 'true')
        self.assertGreater(len({tuple(map(tuple, m)) for d in r['disjuncts']
                                for m in d['width_maps']}), 1)

    def test_a_value_of_the_instance_needs_a_guard(self):
        # (x & c1) & c2 is 0 for these constants only. The proposal is
        # proved under the facts of the instance, refuted without them,
        # and its rule has a guard that fails for other constants.
        vw = (32, 32, 32)
        i = inst(and_(and_(X, Y), Z), vw, [None, 0xf0, 0x0f])
        got, _ = self.props(i)
        self.assertIn('0:s32', got)
        zero = got['0:s32']['tgt']
        self.assertEqual(discover.prove_concrete(i, zero,
                                                 self.backend).status,
                         'unsat')
        self.assertFalse(refines(i.expr, zero, vw))
        r = self.rule(i, zero)
        self.assertIsNotNone(r)
        self.assertNotEqual(r['precondition'], 'true')
        self.assertIn('KZ', r['precondition'])
        pred = tuple(precond.atom_from_json(a)
                     for a in r['disjuncts'][0]['pred_json'])
        # The constants of the rule are in the order of the source.
        ok = inst(and_(and_(X, Y), Z), vw, [None, 0xf0, 0x0f])
        bad = inst(and_(and_(X, Y), Z), vw, [None, 0xf0, 0x1f])
        self.assertTrue(precond.eval_pred(pred, ok.facts, vw, 32))
        self.assertFalse(precond.eval_pred(pred, bad.facts, vw, 32))

    def test_parity_drops_an_undef_leaf(self):
        # (x ^ y) ^ y -> x: the source reads y twice, the replacement not
        # at all; for an undef or poison y the source has every value.
        vw = (32, 32)
        i = inst(xor(xor(X, Y), Y), vw)
        got, _ = self.props(i)
        self.assertIn('x0', got)
        self.assertTrue(refines(i.expr, X, vw))
        # The other direction reads y twice: not a refinement for poison.
        self.assertFalse(refines(X, xor(xor(X, Y), Y), vw))

    def test_an_input_read_twice_is_not_proposed(self):
        # The kept leaves of the parity both read x and y.
        vw = (32, 32, 32)
        e = xor(xor(and_(X, Y), Z), xor(('G_OR', 32, X, Y), Z))
        i = inst(e, vw)
        got, st = self.props(i, ('ac',))
        self.assertEqual(got, {})
        self.assertEqual(st.get('reads_an_input_twice'), 1)

    def test_linear_forms(self):
        vw = (32, 32)
        # (x + y) + (x - y) -> x << 1: y is dropped, x read once.
        i = inst(add(add(X, Y), ('G_SUB', 32, X, Y)), vw)
        got, _ = self.props(i, ('linear',))
        self.assertIn('(G_SHL:s32 x0 1:s32)', got)
        self.assertTrue(refines(i.expr, ('G_SHL', 32, X, L(32, '1')), vw))
        # (a << c) + (b << c) -> (a + b) << c, for every amount c.
        vw = (32, 32, 32)
        i = inst(add(('G_SHL', 32, X, Y), ('G_SHL', 32, Z, Y)), vw,
                 [None, 3, None])
        got, _ = self.props(i, ('linear',))
        t = ('G_SHL', 32, add(X, Z), Y)
        self.assertIn(ir.to_sexpr(t), got)
        self.assertTrue(refines(i.expr, t, vw))

    def test_slices(self):
        vw = (32, 32)
        # (x << c) >> c -> x & (-1 >> c), for every c: the amount is a
        # constant input that the rule computes with.
        i = inst(('G_LSHR', 32, ('G_SHL', 32, X, Y), Y), vw, [None, 8])
        got, _ = self.props(i)
        p = got['(G_AND:s32 x0 (G_LSHR:s32 -1:s32 x1))']
        self.assertEqual(p['const_vars'], (1,))
        self.assertTrue(refines(i.expr, p['tgt'], vw, (1,)))
        r = self.rule(i, p['tgt'], p['const_vars'])
        self.assertEqual(r['precondition'], 'true')
        # (x >> c) & 1 -> G_UBFX x, c, 1, if the mask is 1.
        vw = (32, 32, 32)
        i = inst(and_(('G_LSHR', 32, X, Y), Z), vw, [None, 5, 1])
        got, _ = self.props(i)
        t = ('G_UBFX', 32, X, Y, L(32, '1'))
        self.assertIn(ir.to_sexpr(t), got)
        r = self.rule(i, t)
        self.assertNotEqual(r['precondition'], 'true')
        three = inst(and_(('G_LSHR', 32, X, Y), Z), vw, [None, 5, 3])
        pred = tuple(precond.atom_from_json(a)
                     for a in r['disjuncts'][0]['pred_json'])
        self.assertFalse(precond.eval_pred(pred, three.facts, vw, 32))

    def test_a_field_at_the_top_is_not_a_bit_field_extract(self):
        # (x >> 28) & 0xff has 4 bits: the slice is x >> 28. A G_UBFX of 8
        # bits from bit 28 would be poison where the source is not; the
        # view does not propose it, and the proof would refute it.
        vw = (32, 32, 32, 32)
        i = inst(and_(('G_LSHR', 32, X, Y), Z), vw, [None, 28, 0xff, 8])
        got, _ = self.props(i)
        self.assertNotIn('(G_UBFX:s32 x0 x1 x3)', got)
        bad = ('G_UBFX', 32, X, Y, C1)
        self.assertEqual(discover.prove_concrete(i, bad,
                                                 self.backend).status, 'sat')

    def test_search_proves_and_names_the_family(self):
        vw = (32, 32)
        i = inst(('G_LSHR', 32, ('G_SHL', 32, X, Y), Y), vw, [None, 8])
        ctx = discover.Context(self.dlim)
        log = {}
        out, st = views.search(i, self.backend, views.Limits(), self.dlim,
                               ctx, log)
        self.assertEqual([c['family'] for c in out], ['views-slice'])
        self.assertEqual(st['views_proved_slice'], 1)
        self.assertEqual(st['views_stop'], 'complete')
        self.assertIn('views', log)
        # A replacement that another search has is not proved again.
        again, st = views.search(i, self.backend, views.Limits(), self.dlim,
                                 ctx, have=[out[0]['tgt']])
        self.assertEqual(again, [])
        self.assertEqual(st['views_smt_checks'], 0)


class DedupeTest(unittest.TestCase):
    def test_identical_implementations_only(self):
        consts = (None, 2)
        shl = ('G_SHL', 32, X, L(32, '1'))
        mul = ('G_MUL', 32, X, Y)
        # One signature, two implementations: both are kept.
        self.assertEqual(views.linear_signature(shl, (32, 32), consts),
                         views.linear_signature(mul, (32, 32), consts))
        cands = [{'tgt': shl, 'const_vars': ()},
                 {'tgt': mul, 'const_vars': ()},
                 {'tgt': add(X, Y), 'const_vars': ()},
                 {'tgt': add(Y, X), 'const_vars': ()},
                 {'tgt': add(Y, X), 'const_vars': (1,)}]
        out = views.dedupe(cands)
        self.assertEqual([c['tgt'] for c in out],
                         [shl, mul, add(X, Y), add(Y, X)])

    def test_group_statistics(self):
        a = inst(xor(xor(X, Y), X), (32, 32))
        b = inst(Y, (32, 32))
        b.expr = ('G_OR', 32, Y, Y)
        c = inst(add(X, Y), (32, 32))
        st = views.group_stats([a, b, c])
        self.assertEqual(st['ac']['signatures'], 2)
        self.assertEqual(st['ac']['instances_in_shared_groups'], 2)


spec = importlib.util.spec_from_file_location(
    'gi_rule_synth', os.path.join(ROOT, 'gi-rule-synth.py'))
cli = importlib.util.module_from_spec(spec)
sys.modules.setdefault('gi_rule_synth', cli)
spec.loader.exec_module(cli)


def _node(op, w, reg, args, **kw):
    n = {'op': op, 'w': w, 'reg': reg, 'zero': '0x0', 'one': '0x0',
         'uses': 1, 'flags': [], 'args': args}
    n.update(kw)
    return n


def _input(reg, w=32, const=None):
    d = {'reg': reg, 'w': w, 'zero': '0x0', 'one': '0x0', 'def': 'COPY'}
    if const is not None:
        d.update(const=hex(const), zero=hex(~const & ir.mask(w)),
                 one=hex(const), noundef=True, **{'def': 'G_CONSTANT'})
    return d


class SynthIntegrationTest(unittest.TestCase):
    """synth with and without the views: the rules of the views have the
    provenance of their family, and the statistics their time."""

    def run_synth(self, *extra):
        recs = [
            # (x << c) >> c
            {'fn': 'f', 'bb': 0, 'root': '%3',
             'expr': _node('G_LSHR', 32, '%3', [
                 _node('G_SHL', 32, '%2', [{'in': 0}, {'in': 1}]),
                 {'in': 1}]),
             'inputs': [_input('%0'), _input('%1', const=8)]},
            # (x + 3) + 5
            {'fn': 'g', 'bb': 0, 'root': '%5',
             'expr': _node('G_ADD', 32, '%5', [
                 _node('G_ADD', 32, '%4', [{'in': 0}, {'in': 1}]),
                 {'in': 2}]),
             'inputs': [_input('%0'), _input('%1', const=3),
                        _input('%2', const=5)]}]
        d = tempfile.mkdtemp(prefix='girs-views-')
        with open(os.path.join(d, 'c.jsonl'), 'w') as f:
            for r in recs:
                f.write(json.dumps(r) + '\n')
        out = os.path.join(d, 'rules.json')
        args = cli.default_args(
            'synth', corpus=[os.path.join(d, 'c.jsonl')], o=out,
            proofs=os.path.join(d, 'proofs'), known='', cache='',
            **dict(extra))
        cli.cmd_synth(args)
        with open(out) as f:
            db = json.load(f)
        with open(os.path.join(d, 'rules.stats.json')) as f:
            st = json.load(f)
        return db, st

    def test_views_on_and_off(self):
        db, st = self.run_synth()
        by = {r['provenance']['discovery']: r for r in db['rules']}
        self.assertIn('views-slice+smt', by)
        self.assertIn('views-linear+smt', by)
        lin_rule = by['views-linear+smt']
        self.assertEqual(lin_rule['cost'], {'source': 2, 'replacement': 1})
        self.assertEqual(len(lin_rule['const_vars']), 2)
        for r in by.values():
            self.assertEqual(r['provenance']['sources'], ['enumerative'])
            self.assertEqual(r['precondition_source'], 'lhs')
        self.assertTrue(st['views']['enabled'])
        self.assertEqual(st['views']['instances'], 2)
        self.assertGreaterEqual(st['views']['rules'], 2)
        self.assertIn('seconds', st['views'])
        # The default search runs in worker processes (parallel.py); the
        # serial search finds the same rules of the views.
        serial, sst = self.run_synth(('search_jobs', 0))
        self.assertEqual(
            sorted((r['id'], r['provenance']['discovery'])
                   for r in serial['rules']),
            sorted((r['id'], r['provenance']['discovery'])
                   for r in db['rules']))
        self.assertEqual(sst['views']['rules'], st['views']['rules'])
        db, st = self.run_synth(('views', False))
        self.assertFalse(any(r['provenance']['discovery'].startswith(
            'views') for r in db['rules']))
        self.assertFalse(st['views']['enabled'])


if __name__ == '__main__':
    unittest.main()
