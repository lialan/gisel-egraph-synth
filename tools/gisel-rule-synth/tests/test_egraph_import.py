#!/usr/bin/env python3
"""Tests of the import of the e-graph export (girs/egraph.py), format
version 3: the fields "features", "views" and "context_facts", where the
precondition of a candidate comes from, the cross-check of the records
whose rewrites needed context facts, and the records whose roots are the
results of one instruction with several results.

The synthetic records have the form of the export of
lib/GIEGraphCombiner.cpp (one is also written by llc, if it is there).

Run:  python3 -m unittest discover -s tools/gisel-rule-synth/tests
"""

import importlib.util
import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, ROOT)

from girs import discover, egraph, ir, precond, region, smt, synth  # noqa

spec = importlib.util.spec_from_file_location(
    'gi_rule_synth', os.path.join(ROOT, 'gi-rule-synth.py'))
cli = importlib.util.module_from_spec(spec)
sys.modules.setdefault('gi_rule_synth', cli)
spec.loader.exec_module(cli)

LLC = os.environ.get('GIRS_LLC') or cli.paths.llc()
HAVE_LLC = os.path.exists(LLC)

FEATURES = ['facts', 'linear', 'slice', 'tuples', 'patterns', 'banks', 'dag']
VIEW_KEYS = ('views', 'candidates', 'merges', 'refinements', 'unsafe',
             'budget', 'unsupported', 'context_facts')


def V(i):
    return ('var', i)


def inp(i, reg, zero='0x0', one='0x0', d='COPY', id_=None):
    return {'id': i if id_ is None else id_, 'in': i, 'reg': reg,
            'type': 's32', 'zero': zero, 'one': one, 'def': d,
            'not_undef': False, 'not_poison': False}


def node(id_, op, reg, args, best, ty='s32', uses=1, **kw):
    n = {'id': id_, 'op': op, 'best': best, 'instr': id_, 'reg': reg,
         'type': ty, 'uses': uses, 'zero': '0x0', 'one': '0x0',
         'not_undef': False, 'not_poison': False, 'args': args}
    n.update(kw)
    return n


def record(fn, inputs, original, optimized, roots, rules, constants=(),
           context_facts=None, version=3):
    r = {'version': version, 'fn': fn, 'bb': 0, 'stage': 'pre-legalizer',
         'triple': 'amdgcn-amd-amdhsa', 'profitable': True,
         'refinement': False, 'blocker': '', 'saturated': True,
         'cost': {'original': 2, 'optimized': 1},
         'inputs': inputs, 'constants': list(constants),
         'original': original, 'optimized': optimized, 'roots': roots,
         'rules': rules}
    if version >= 3:
        r['features'] = FEATURES
        r['views'] = {'facts': dict.fromkeys(VIEW_KEYS, 0),
                      'linear': dict(dict.fromkeys(VIEW_KEYS, 0), views=2)}
        r['context_facts'] = context_facts or {}
    return r


# x & 0xff where x = lshr y, 24 is in another block: the e-graph removes
# the mask with the known bits of the input (and-mask-of-known-zeros needs
# context facts).
MASK = record(
    'mask', [inp(0, '%2', zero='0xFFFFFF00', d='G_LSHR')],
    [node(2, 'G_AND', '%4', [0, 1], best=0, zero='0xFFFFFF00')],
    [{'id': 0, 'in': 0}],
    [{'reg': '%4', 'original': 2, 'optimized': 0}],
    {'and-mask-of-known-zeros': 1},
    constants=[{'id': 1, 'type': 's32', 'value': '0xFF'}],
    context_facts={'and-mask-of-known-zeros': 1})

# x * y where y is known to be 2 (all its bits): x << 1. The guard would
# have to say y == 2, which the precondition grammar has no atom for.
TIMES_TWO = record(
    'times_two', [inp(0, '%0'), inp(1, '%1', zero='0xFFFFFFFD', one='0x2',
                                    d='G_LOAD')],
    [node(2, 'G_MUL', '%2', [0, 1], best=4, zero='0x1')],
    [{'id': 0, 'in': 0}, {'id': 3, 'type': 's32', 'value': '0x1'},
     {'id': 4, 'op': 'G_SHL', 'type': 's32', 'args': [0, 3]}],
    [{'reg': '%2', 'original': 2, 'optimized': 4}],
    {'known-constant': 1}, context_facts={'known-constant': 1})

# (x ^ y) ^ y -> x needs no fact; the record says that another rewrite of
# the region needed context facts.
XOR = record(
    'xor_self', [inp(0, '%0'), inp(1, '%1')],
    [node(2, 'G_XOR', '%2', [0, 1], best=2),
     node(3, 'G_XOR', '%3', [2, 1], best=0)],
    [{'id': 0, 'in': 0}, {'id': 1, 'in': 1},
     {'id': 2, 'op': 'G_XOR', 'type': 's32', 'args': [0, 1]}],
    [{'reg': '%3', 'original': 3, 'optimized': 0}],
    {'xor-self': 1, 'add-disjoint-to-or': 1},
    context_facts={'add-disjoint-to-or': 1})

# s = a + b (another user) and c = icmp ult s, a: one G_UADDO computes both
# (the tuple rules of GIEGraph; the selected DAG has the two results).
UADDO = record(
    'uaddo', [inp(0, '%0'), inp(1, '%1')],
    [node(2, 'G_ADD', '%2', [0, 1], best=10, uses=2),
     node(3, 'G_ICMP', '%3', [2, 0], best=11, ty='s1', pred='ult')],
    [{'id': 0, 'in': 0}, {'id': 1, 'in': 1},
     {'id': 10, 'op': 'G_UADDO', 'res': 0, 'type': 's32', 'args': [0, 1]},
     {'id': 11, 'op': 'G_UADDO', 'res': 1, 'type': 's1', 'args': [0, 1]}],
    [{'reg': '%2', 'original': 2, 'optimized': 10},
     {'reg': '%3', 'original': 3, 'optimized': 11}],
    {'tuple-uaddo': 2})

# d = x - y and l = icmp ult x, y: roots that do not read each other.
USUBO = record(
    'usubo', [inp(0, '%0'), inp(1, '%1')],
    [node(2, 'G_SUB', '%2', [0, 1], best=10),
     node(3, 'G_ICMP', '%3', [0, 1], best=11, ty='s1', pred='ult')],
    [{'id': 0, 'in': 0}, {'id': 1, 'in': 1},
     {'id': 10, 'op': 'G_USUBO', 'res': 0, 'type': 's32', 'args': [0, 1]},
     {'id': 11, 'op': 'G_USUBO', 'res': 1, 'type': 's1', 'args': [0, 1]}],
    [{'reg': '%2', 'original': 2, 'optimized': 10},
     {'reg': '%3', 'original': 3, 'optimized': 11}],
    {'tuple-usubo': 2})


# The source has the G_USUBO already, and both results are roots: no
# rewrite of several roots.
USUBO_KEPT = record(
    'usubo_kept', [inp(0, '%0'), inp(1, '%1')],
    [node(2, 'G_USUBO', '%2', [0, 1], best=10, res=0),
     node(3, 'G_USUBO', '%3', [0, 1], best=11, ty='s1', res=1)],
    [{'id': 0, 'in': 0}, {'id': 1, 'in': 1},
     {'id': 10, 'op': 'G_USUBO', 'res': 0, 'type': 's32', 'args': [0, 1]},
     {'id': 11, 'op': 'G_USUBO', 'res': 1, 'type': 's1', 'args': [0, 1]}],
    [{'reg': '%2', 'original': 2, 'optimized': 10},
     {'reg': '%3', 'original': 3, 'optimized': 11}],
    {})


def by_sexpr(imp):
    return {(ir.to_sexpr(c.inst.expr), ir.to_sexpr(c.tgt)): c
            for c in imp.candidates()}


class VersionTest(unittest.TestCase):
    def test_versions_one_to_three(self):
        imp = egraph.Importer(smt.Z3Backend())
        imp.add_file(os.path.join(HERE, 'data', 'egraph-umin.jsonl'))
        v2 = {k: x for k, x in XOR.items()
              if k not in ('features', 'views', 'context_facts')}
        imp.add_record(dict(v2, version=2))
        imp.add_record(XOR)
        self.assertEqual(imp.stats['versions'], {1: 1, 2: 1, 3: 1})
        # Version 3 only: the features and the views are summed.
        self.assertEqual(imp.stats['features']['linear'], 1)
        self.assertEqual(imp.stats['views']['linear']['views'], 2)
        self.assertEqual(imp.stats['context_facts']['records'], 1)
        with self.assertRaises(ValueError):
            imp.add_record(dict(XOR, version=4))


class PreconditionSourceTest(unittest.TestCase):
    def setUp(self):
        self.backend = smt.Z3Backend()
        self.imp = egraph.Importer(self.backend)
        for r in (MASK, TIMES_TWO, XOR):
            self.imp.add_record(r, 'test')
        self.sy = synth.Synthesizer(self.backend)
        self.rids = {}
        for c in self.imp.candidates():
            self.rids[(ir.to_sexpr(c.inst.expr), ir.to_sexpr(c.tgt))] = \
                self.imp.synthesize(c, self.sy)

    def test_guard_from_the_known_bits_of_an_input(self):
        (key, c), = [(k, c) for k, c in by_sexpr(self.imp).items()
                     if k[0] == '(G_AND:s32 x0 x1)']
        self.assertEqual(c.precondition_source, 'guard')
        self.assertEqual(c.context_facts, {'and-mask-of-known-zeros'})
        r = self.sy.rules[self.rids[key]]
        self.assertTrue(all(d['_pred'] for d in r['disjuncts']))
        self.assertEqual(r['provenance']['precondition_source'], 'guard')
        self.assertEqual(r['provenance']['egraph_context_facts'],
                         ['and-mask-of-known-zeros'])
        # Without the facts the rule is wrong: the guard must test them,
        # and it fails where a bit outside of the mask may be one.
        self.assertEqual(discover.prove_concrete(
            _free(c.inst), c.tgt, self.backend).status, 'sat')
        d = r['disjuncts'][0]
        vw = tuple(r['vw'])
        ok = [(int(z, 16), int(o, 16)) for z, o in
              (f[:2] for f in d['example']['facts'])]
        # The value (not the constant) loses a known zero bit.
        v = [i for i, (z, o) in enumerate(ok) if (z | o) != 0xFFFFFFFF]
        self.assertEqual(len(v), 1)
        bad = list(ok)
        bad[v[0]] = (0xFFFFFE00, 0)
        self.assertTrue(precond.eval_pred(d['_pred'], ok, vw, 32))
        self.assertFalse(precond.eval_pred(d['_pred'], bad, vw, 32))

    def test_unconditional_candidate(self):
        key = ('(G_XOR:s32 (G_XOR:s32 x0 x1) x1)', 'x0')
        c = by_sexpr(self.imp)[key]
        self.assertEqual(c.precondition_source, 'lhs')
        rid = self.rids[key]
        self.assertEqual(synth.precondition_text(self.sy.rules[rid]),
                         'true')

    def test_facts_without_a_guard_are_counted(self):
        # The candidate is proved with y == 2, but no guard says y == 2:
        # no rule, and the rejection is counted, not dropped.
        key = ('(G_MUL:s32 x0 x1)', '(G_SHL:s32 x0 1:s32)')
        c = by_sexpr(self.imp)[key]
        self.assertEqual(c.precondition_source, 'guard')
        self.assertIsNone(self.rids[key])
        p = self.imp.stats['precondition']
        self.assertEqual(p['guard']['rejected'],
                         {'no_precondition_in_grammar': 1})
        self.assertEqual(p['guard']['rules'], 1)
        self.assertEqual(p['lhs']['rules'], 1)

    def test_records_with_context_facts(self):
        out = self.imp.cross_check()
        # Each record with context facts is in one bucket.
        self.assertEqual(out, {'guarded': 1, 'rejected': 1,
                               'proved_without_facts': 1,
                               'not_synthesized': 0, 'no_candidate': 0})
        st = self.imp.stats['context_facts']
        self.assertEqual(st['records'], 3)
        self.assertEqual(sum(out.values()), st['records'])
        self.assertEqual(st['rules'], {'and-mask-of-known-zeros': 1,
                                       'known-constant': 1,
                                       'add-disjoint-to-or': 1})
        self.assertEqual([e['fn'] for e in
                          st['examples']['proved_without_facts']],
                         ['xor_self'])

    def test_a_record_that_was_not_synthesized(self):
        imp = egraph.Importer(self.backend)
        imp.add_record(MASK, 'test')
        self.assertEqual(imp.cross_check()['not_synthesized'], 1)


def _free(inst):
    import copy
    i = copy.copy(inst)
    i.facts = tuple((0, 0) for _ in inst.vw)
    return i


class MultiRootTest(unittest.TestCase):
    def setUp(self):
        self.backend = smt.Z3Backend()

    def test_carry_and_sum_seed_a_rule_with_two_outputs(self):
        imp = egraph.Importer(self.backend)
        imp.add_record(UADDO, 'test')
        st = imp.stats['multi_root']
        self.assertEqual((st['records'], st['groups'], st['region_seeds'],
                          st['parts']), (1, 1, 1, 1))
        seeds = [c for c in imp.candidates() if c.joint]
        self.assertEqual(len(seeds), 1)
        c = seeds[0]
        self.assertEqual(ir.to_sexpr(c.inst.expr),
                         '(G_ICMP:ult:s1 (G_ADD:s32 x0 x1) x0)')
        self.assertEqual(ir.to_sexpr(c.tgt), '(G_UADDO#1:s1 x0 x1)')
        self.assertEqual(c.inst.interior_uses, (2,))
        # The root of the sum alone (one result of the G_UADDO) is not a
        # candidate: it is a part of the rewrite of the two roots.
        self.assertNotIn('(G_UADDO:s32 x0 x1)',
                         {ir.to_sexpr(x.tgt) for x in imp.candidates()
                          if not ir.interior_nodes(x.inst.expr)})
        # The region step proves the rule with both outputs.
        sy = synth.Synthesizer(self.backend)
        rid = imp.synthesize(c, sy)
        self.assertIsNotNone(rid)
        sy.finalize([c.inst])
        lim = discover.Limits(grammar='registry')
        region.extend(sy, [(c.inst, c.tgt, rid)], self.backend, lim,
                      discover.Context(lim))
        joint = [r for r in sy.rules.values() if r.get('region')]
        self.assertEqual(len(joint), 1)
        outs = joint[0]['region']['outputs']
        self.assertEqual([o['replacement'] for o in outs],
                         ['(G_UADDO#1:s1 x0 x1)', '(G_UADDO:s32 x0 x1)'])
        self.assertEqual(joint[0]['provenance']['sources'], ['egraph'])

    def test_independent_roots_are_counted(self):
        imp = egraph.Importer(self.backend)
        imp.add_record(USUBO, 'test')
        st = imp.stats['multi_root']
        self.assertEqual((st['groups'], st['region_seeds'], st['parts']),
                         (1, 0, 2))
        self.assertEqual(sum(imp.stats['rejected']['multi-root'].values()),
                         1)
        self.assertEqual([c for c in imp.candidates()
                          if not ir.interior_nodes(c.inst.expr)], [])

    def test_roots_that_do_not_change_are_not_a_rewrite(self):
        imp = egraph.Importer(self.backend)
        imp.add_record(USUBO_KEPT, 'test')
        st = imp.stats['multi_root']
        self.assertEqual((st['records'], st['groups']), (0, 0))
        self.assertNotIn('multi-root', imp.stats['rejected'])
        self.assertEqual(imp.stats['roots_unchanged'], 2)

    def test_synth_command_with_regions(self):
        d = tempfile.mkdtemp(prefix='girs-egraph-')
        with open(os.path.join(d, 'e.jsonl'), 'w') as f:
            f.write(json.dumps(UADDO) + '\n')
        open(os.path.join(d, 'empty.jsonl'), 'w').close()
        out = os.path.join(d, 'rules.json')
        cli.cmd_synth(cli.default_args(
            'synth', corpus=[os.path.join(d, 'empty.jsonl')], o=out,
            proofs=os.path.join(d, 'proofs'), known='', cache='',
            egraph=[os.path.join(d, 'e.jsonl')], regions=True,
            grammar='registry'))
        with open(out) as f:
            rules = json.load(f)['rules']
        joint = [r for r in rules if r.get('region')]
        self.assertEqual(len(joint), 1)
        self.assertEqual(joint[0]['replacement'],
                         '(G_UADDO#1:s1 x0 x1); $t0 = (G_UADDO:s32 x0 x1)')
        self.assertEqual(joint[0]['precondition_source'], 'lhs')
        with open(os.path.join(d, 'rules.stats.json')) as f:
            st = json.load(f)['egraph']
        self.assertEqual(st['multi_root']['region_seeds_searched'], 1)


MIR = '''---
name: mask_ctx
tracksRegLiveness: true
body: |
  bb.0:
    successors: %bb.1
    liveins: $vgpr0
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = G_CONSTANT i32 24
    %2:_(s32) = G_LSHR %0, %1
    G_BR %bb.1
  bb.1:
    %3:_(s32) = G_CONSTANT i32 255
    %4:_(s32) = G_AND %2, %3
    $vgpr0 = COPY %4
    SI_RETURN implicit $vgpr0
...
'''


@unittest.skipUnless(HAVE_LLC, 'needs build/plugin/bin/llc or GIRS_LLC')
class RealExportTest(unittest.TestCase):
    """A record that llc writes: the mask is removed with the facts of an
    input from another block (context facts)."""

    def test_export_of_llc(self):
        d = tempfile.mkdtemp(prefix='girs-egraph-')
        mir = os.path.join(d, 'm.mir')
        out = os.path.join(d, 'm.jsonl')
        with open(mir, 'w') as f:
            f.write(MIR)
        subprocess.run([LLC, '-mtriple=amdgcn-amd-amdhsa',
                        '-run-pass=gisel-egraph-combiner',
                        '-gisel-egraph-export=' + out, '-o', os.devnull,
                        mir], check=True)
        with open(out) as f:
            recs = [json.loads(line) for line in f if line.strip()]
        self.assertEqual(len(recs), 1)
        rec = recs[0]
        self.assertEqual(rec['version'], 3)
        self.assertIn('and-mask-of-known-zeros', rec['context_facts'])
        imp = egraph.Importer(smt.Z3Backend())
        imp.add_file(out)
        sy = synth.Synthesizer(smt.Z3Backend())
        cands = imp.candidates()
        self.assertTrue(cands)
        for c in cands:
            self.assertEqual(c.precondition_source, 'guard')
            self.assertIsNotNone(imp.synthesize(c, sy))
        self.assertEqual(imp.cross_check()['guarded'], 1)
        for r in sy.rules.values():
            self.assertNotEqual(synth.precondition_text(r), 'true')


if __name__ == '__main__':
    unittest.main()
