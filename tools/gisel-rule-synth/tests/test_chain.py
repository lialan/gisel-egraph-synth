#!/usr/bin/env python3
"""A conditional rule from a corpus to its generated guard:

    tests/data/chain/corpus.mir -> extract -> synth (no catalog) -> rule
        with a precondition on known bits -> emit (scratch profile)

The corpus has x + 1 with the low bit of x known zero (x defined in
another block). The search has the corpus only; the test checks what it
finds: x + y -> x | y with the guard "no bit is one in both", the source
of that precondition, and the guard that the emitter writes. That the
rule fires in a compiler with it (and not where the guard fails) is shown
by eval/rule_chain.py with the lit tests of test/SynthChain, which need a
build of their own.

The chain needs llc (GIRS_LLC, or build/plugin/bin/llc).
"""

import importlib.util
import json
import os
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

from girs import emit, ir, precond  # noqa: E402

spec = importlib.util.spec_from_file_location(
    'gi_rule_synth', os.path.join(ROOT, 'gi-rule-synth.py'))
cli = importlib.util.module_from_spec(spec)
sys.modules.setdefault('gi_rule_synth', cli)
spec.loader.exec_module(cli)

spec = importlib.util.spec_from_file_location(
    'rule_chain', os.path.join(ROOT, 'eval', 'rule_chain.py'))
chain = importlib.util.module_from_spec(spec)
spec.loader.exec_module(chain)

LLC = os.environ.get('GIRS_LLC') or cli.paths.llc()
HAVE_LLC = os.path.exists(LLC)
ADD = '(G_ADD:s32 x0 x1)'
CARRY = '(G_ICMP:ult:s1 (G_ADD:s32 x0 x1) x0)'


@unittest.skipUnless(HAVE_LLC, 'needs build/plugin/bin/llc or GIRS_LLC')
class ChainTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        d = tempfile.mkdtemp(prefix='girs-chain-')
        cls.dir = d
        cli.cmd_extract(cli.default_args(
            'extract', llc=LLC, o=os.path.join(d, 'corpus'),
            mir=[chain.CORPUS], j=1))
        cli.cmd_synth(cli.default_args(
            'synth', corpus=[os.path.join(d, 'corpus')],
            o=os.path.join(d, 'rules.json'),
            proofs=os.path.join(d, 'proofs'), known='', cache='',
            cost_slack=0, regions=True, grammar='registry'))
        with open(os.path.join(d, 'rules.json')) as f:
            cls.db = json.load(f)
        cls.found = chain.find_rules(cls.db)

    def test_the_corpus_has_the_known_bits(self):
        recs = []
        corpus = os.path.join(self.dir, 'corpus')
        for name in os.listdir(corpus):
            if name.endswith('.jsonl'):
                with open(os.path.join(corpus, name)) as f:
                    recs += [json.loads(line) for line in f if line.strip()]
        adds = [r for r in recs if r['fn'].startswith('add_one') and
                r['expr']['op'] == 'G_ADD']
        # Each function also has a straight-line record that looks through
        # the block boundary (the definition of the value is part of the
        # tree, so it has more inputs); the facts are on the records of the
        # block itself.
        single = [r for r in adds if len(r['inputs']) == 2]
        self.assertEqual(len(single), 2)
        self.assertEqual(len(adds) - len(single), 2)
        for r in single:
            # The value is an input (defined in another block) with its
            # low bit known zero; the other input is the constant 1.
            self.assertEqual([i['zero'] for i in r['inputs']],
                             ['0x1', '0xFFFFFFFE'])
            self.assertEqual(r['inputs'][1]['const'], '0x1')

    def test_conditional_rule(self):
        r = self.found[ADD]
        self.assertEqual(r['id'], 'synth_add_ae52fe29')
        self.assertEqual(r['replacement'], '(G_OR:s32 x0 x1)')
        self.assertEqual(r['precondition'], 'all(KZ(x0) | KZ(x1))')
        self.assertEqual(r['precondition_source'], 'guard')
        self.assertEqual(r['semantic_status']['kind'], 'verified_refinement')
        # An equal-cost rule: a candidate of a target-cost search only.
        self.assertEqual(r['class'], 'equal_cost')
        self.assertTrue(r['target_cost_candidate'])
        # Proved for more widths than the corpus has.
        widths = {m[0][1] for d in r['disjuncts'] for m in d['width_maps']}
        self.assertTrue({8, 16, 32, 64} <= widths)
        # The guard holds for the facts of the corpus and fails where a
        # bit may be one in both operands.
        pred = tuple(precond.atom_from_json(a)
                     for a in r['disjuncts'][0]['pred_json'])
        one = (0xFFFFFFFE, 1)
        self.assertTrue(precond.eval_pred(pred, [(1, 0), one], (32, 32), 32))
        self.assertFalse(precond.eval_pred(pred, [(0, 0), one], (32, 32),
                                           32))
        three = (0xFFFFFFFC, 3)
        self.assertFalse(precond.eval_pred(pred, [(1, 0), three], (32, 32),
                                           32))
        self.assertTrue(precond.eval_pred(pred, [(3, 0), three], (32, 32),
                                          32))

    def test_rule_with_two_outputs(self):
        r = self.found[CARRY]
        self.assertEqual(r['precondition'], 'true')
        self.assertEqual(r['precondition_source'], 'lhs')
        self.assertEqual([o['replacement'] for o in r['region']['outputs']],
                         ['(G_UADDO#1:s1 x0 x1)', '(G_UADDO:s32 x0 x1)'])

    def test_scratch_emission(self):
        ids = [r['id'] for r in self.found.values()]
        td, inc, info = emit.emit(self.db, chain.scratch_profiles(
            self.db, ids))
        self.assertEqual(info['targets']['AMDGPU']['rules'], 2)
        self.assertEqual(info['targets']['AArch64']['rules'], 0)
        self.assertIn('def synth_add_ae52fe29 : GICombineRule<', td)
        self.assertIn('bool Pass = (K0.Zero | K1.Zero).isAllOnes();', inc)
        region = self.found[CARRY]['id']
        self.assertIn('def %s : GICombineRule<' % region, td)
        self.assertIn('B.buildInstr(TargetOpcode::G_UADDO', inc)
        # The group of the scratch profile has exactly these rules.
        group = td[td.index('def gi_synth_combines_amdgpu'):]
        for name in ('synth_add_ae52fe29', region):
            self.assertIn(name, group)
        self.assertNotIn('synth_add_24a228fd', td)


if __name__ == '__main__':
    unittest.main()
