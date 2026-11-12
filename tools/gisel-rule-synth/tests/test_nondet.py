"""Tests of sources and replacements with two equal terms that have a value
of their own (ir.repeated_nondet): two G_FMINNUM of +0 and -0 can give
zeros of different signs, two G_ANYEXT different high bits, and two
G_FREEZE of poison different values."""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(
    __file__))))

from girs import corpus, emit, ir, smt, synth  # noqa: E402


def _node(op, w, reg, args, ty, uses=1):
    return {'op': op, 'w': w, 'type': ty, 'reg': reg, 'zero': '0x0',
            'one': '0x0', 'noundef': False, 'uses': uses, 'flags': [],
            'args': args}


def _record(src):
    """xor(f(x, y), f(x, y)) with two instructions for f, each with
    another user: the corpus record of the extractor."""
    in_w = 8 if src == 'G_ANYEXT' else 16
    in_ty = {'G_ANYEXT': 'i8', 'G_FREEZE': 'i16'}.get(src, 'f16')
    inputs = [{'reg': '%x', 'w': in_w, 'type': in_ty, 'zero': '0x0',
               'one': '0x0', 'def': 'COPY'},
              {'reg': '%y', 'w': 16, 'type': in_ty, 'zero': '0x0',
               'one': '0x0', 'def': 'COPY'}]

    def side(m, b):
        if src in ('G_ANYEXT', 'G_FREEZE'):
            return _node(src, 16, m, [{'in': 0}], 'i16', uses=2)
        inner = _node(src, 16, m, [{'in': 0}, {'in': 1}], 'f16')
        return _node('G_BITCAST', 16, b, [inner], 'i16', uses=2)

    return {'fn': 'f', 'bb': 0, 'root': '%r', 'interior': 4,
            'expr': _node('G_XOR', 16, '%r',
                          [side('%m1', '%b1'), side('%m2', '%b2')], 'i16'),
            'inputs': inputs}


class RepeatedNondetTest(unittest.TestCase):
    def test_corpus_refuses_the_source(self):
        for src in ('G_FMINNUM', 'G_FMAXNUM', 'G_FADD', 'G_ANYEXT',
                    'G_FREEZE'):
            with self.subTest(src=src):
                why = []
                self.assertIsNone(corpus.parse_record(_record(src),
                                                      why=why))
                self.assertEqual(why, ['two equal instructions with a '
                                       'value of their own'])

    def test_deterministic_terms_twice_are_kept(self):
        # Two G_ADD instructions with equal operands have equal values.
        rec = _record('G_FMINNUM')
        for side in rec['expr']['args']:
            side['args'][0]['op'] = 'G_ADD'
            side['args'][0]['type'] = 'i16'
        for inp in rec['inputs']:
            inp['type'] = 'i16'
        inst = corpus.parse_record(rec)
        self.assertIsNotNone(inst)
        self.assertFalse(ir.repeated_nondet(inst.expr))

    def test_synthesizer_refuses_the_source(self):
        # An instance that does not come from the corpus reader (the
        # e-graph and the composition give instances too).
        m = ('G_FMINNUM', 16, ('var', 0), ('var', 1))
        src = ('G_XOR', 16, ('G_BITCAST', 16, m), ('G_BITCAST', 16, m))
        self.assertTrue(ir.repeated_nondet(src))
        inst = corpus.Instance(src, (16, 16), ((0, 0), (0, 0)),
                               (None, None), (2, 1, 2, 1), (), [],
                               kinds=('f', 'f'))
        sy = synth.Synthesizer(smt.Z3Backend())
        self.assertIsNone(sy.add(inst, ('const', 16, 0)))
        self.assertEqual(sy.stats.get('nondet_rejected'), 1)

    def test_apply_pattern_builds_equal_terms_once(self):
        # The proof gives two equal terms of a replacement one value, so
        # the replacement has one instruction for them.
        x = ('var', 0)
        a = ('G_ANYEXT', 32, x)
        pats = emit._apply_patterns(('G_XOR', 32, a, a), (16,), 32)
        self.assertEqual(sum('G_ANYEXT' in p for p in pats), 1)
        self.assertIn('$n0, $n0', pats[-1])


if __name__ == '__main__':
    unittest.main()
