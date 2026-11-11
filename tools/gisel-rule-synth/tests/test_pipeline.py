"""Tests of the command line and of the real extraction chain

    MIR -> the extractor pass of llc -> JSON -> corpus reader -> instance

The tests of the chain need llc: the environment variable GIRS_LLC, or
build/bin/llc of the repository. They are skipped without it.
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

from girs import corpus, discover, ir, ops, smt, targets  # noqa: E402

spec = importlib.util.spec_from_file_location(
    'gi_rule_synth', os.path.join(ROOT, 'gi-rule-synth.py'))
cli = importlib.util.module_from_spec(spec)
sys.modules['gi_rule_synth'] = cli
spec.loader.exec_module(cli)

LLC = os.environ.get('GIRS_LLC') or os.path.join(
    os.path.dirname(cli.LLVM), 'build', 'bin', 'llc')
HAVE_LLC = os.path.exists(LLC)

CHAIN_MIR = '''---
name: chain
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0, $vgpr1
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s1) = G_ICMP intpred(ult), %0, %1
    %3:_(s32) = G_SELECT %2, %0, %1
    %4:_(s32) = G_SEXT_INREG %3, 8
    %5:_(s32), %6:_(s1) = G_UADDO %4, %1
    %7:_(s32) = G_ZEXT %6
    %8:_(f32) = G_FCONSTANT float 1.500000e+00
    %9:_(f64) = G_FPEXT %8
    %10:_(s64) = G_FPTOSI %9
    %11:_(s32) = G_TRUNC %10
    %12:_(s32) = G_ADD %5, %7
    %13:_(s32) = G_ADD %12, %11
    %14:_(s32) = G_FREEZE %0
    %15:_(s32) = G_AND %14, %14
    %16:_(s32) = G_XOR %13, %15
    ; Shapes and types that a tree must not have.
    %19:_(s64) = G_SEXT %1
    %20:_(p0) = G_INTTOPTR %19
    %21:_(p0) = G_PTR_ADD %20, %19
    %28:_(s64) = G_PTRTOINT %21
    %22:_(s32) = G_TRUNC %28
    %23:_(<2 x s32>) = G_BUILD_VECTOR %0, %1
    %24:_(<2 x s32>) = G_ADD %23, %23
    %25:_(s128) = G_ZEXT %0
    %26:_(s128) = G_ADD %25, %25
    %27:_(s32) = G_TRUNC %26
    ; Types and operators that the reader refuses, with the reason.
    %30:_(bf16) = G_FPTRUNC %8
    %31:_(s16) = G_FPTOSI %30
    %32:_(s64) = G_ANYEXT %0
    %33:_(s32) = G_TRUNC %32
    %34:_(s32) = G_OR %22, %27
    %35:_(s16) = G_TRUNC %33
    %36:_(s16) = G_OR %35, %31
    %37:_(s32) = G_ZEXT %36
    %38:_(s32) = G_OR %34, %37
    %39:_(s32) = G_OR %38, %16
    $vgpr0 = COPY %39
    SI_RETURN implicit $vgpr0
...
---
name: phi
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0, $vgpr1
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s1) = G_ICMP intpred(eq), %0, %1
    G_BRCOND %2, %bb.2
  bb.1:
    %3:_(s32) = G_ADD %0, %1
  bb.2:
    %4:_(s32) = G_PHI %0, %bb.0, %3, %bb.1
    %5:_(s32) = G_SUB %4, %1
    $vgpr0 = COPY %5
    SI_RETURN implicit $vgpr0
...
'''


def _trees(node, out=None):
    out = [] if out is None else out
    if 'op' in node:
        out.append(node)
        for a in node['args']:
            _trees(a, out)
    return out


class DefaultArgsTest(unittest.TestCase):
    def test_defaults_of_the_parser(self):
        a = cli.default_args('synth', corpus=['x'])
        self.assertEqual(a.grammar, 'source')
        self.assertEqual(a.egraph, [])
        self.assertEqual(a.egraph_max_cost, 8)
        # A list default is not shared between two callers.
        a.egraph.append('y')
        self.assertEqual(cli.default_args('synth', corpus=['x']).egraph, [])

    def test_unknown_and_missing_arguments(self):
        with self.assertRaises(TypeError):
            cli.default_args('synth', corpus=['x'], gramar='all')
        with self.assertRaises(TypeError):
            cli.default_args('synth')
        with self.assertRaises(TypeError):
            cli.default_args('extract', o='d')   # --llc is required

    def test_every_command_runs_with_its_defaults(self):
        """A command function reads only arguments that its parser has:
        each attribute that the source of a command reads from ``args``
        is a default of the subcommand."""
        import inspect
        import re
        for name, sub in cli._SUBPARSERS.items() or \
                (cli.build_parser() and cli._SUBPARSERS).items():
            fn = sub.get_default('fn')
            have = {a.dest for a in sub._actions}
            used = set(re.findall(r'\bargs\.(\w+)', inspect.getsource(fn)))
            self.assertEqual(used - have, set(), name)


class ScheduleTest(unittest.TestCase):
    def _insts(self):
        out = []
        for k in range(40):
            op = 'G_ADD' if k < 36 else ('G_UMIN' if k < 39 else 'G_CTPOP')
            e = (op, 32, ('var', 0)) if op == 'G_CTPOP' else \
                (op, 32, ('var', 0), ('var', 1))
            n = len(ir.variables(e))
            out.append(corpus.Instance(e, (32,) * n, [(k, 0)] * n,
                                       [None] * n, [], [],
                                       [('f', 'fn', '%0')]))
        return out

    def test_rare_operators_get_a_place_before_the_budget_ends(self):
        insts = self._insts()
        order = cli._schedule(insts, 0.2)
        self.assertEqual(sorted(map(id, order)), sorted(map(id, insts)))
        first = [ops.base(i.expr[0]) for i in order[:10]]
        self.assertIn('G_UMIN', first)
        self.assertIn('G_CTPOP', first)
        # Four of five places are in the order of value.
        self.assertEqual(order[0], insts[0])
        self.assertGreaterEqual(first.count('G_ADD'), 8)
        # No share: the order of value.
        self.assertEqual(cli._schedule(insts, 0), insts)


class SearchRecordTest(unittest.TestCase):
    """The record of a search says why it ended."""

    def _inst(self, src, vw):
        n = len(vw)
        return corpus.Instance(src, vw, [(0, 0)] * n, [None] * n, [], [],
                               [('f', 'fn', '%0')])

    def test_complete_and_budget(self):
        src = ('G_AND', 32, ('G_OR', 32, ('var', 0), ('var', 1)),
               ('var', 0))
        inst = self._inst(src, (32, 32))
        backend = smt.Z3Backend()
        log = {}
        cands, st = discover.discover(inst, backend, discover.Limits(),
                                      log=log)
        self.assertEqual(st['stop'], 'complete')
        self.assertEqual(log['stop'], 'complete')
        self.assertIn('x0', [c['tgt'] for c in log['candidates']
                             if c['status'] == 'proved'])
        # No proof budget: the search has no result, and it says that a
        # budget ended it.
        lim = discover.Limits(max_proofs=0)
        cands, st = discover.discover(inst, backend, lim)
        self.assertEqual(cands, [])
        self.assertEqual(st['stop'], 'proof_budget')
        self.assertGreater(st['not_tried'], 0)
        # A term budget that the bank reaches.
        lim = discover.Limits(max_terms=12)
        src2 = ('G_ADD', 32, ('G_SUB', 32, ('G_XOR', 32, ('var', 0),
                                            ('var', 1)), ('var', 1)),
                ('var', 2))
        cands, st = discover.discover(self._inst(src2, (32, 32, 32)),
                                      backend, lim)
        self.assertEqual(st['stop'], 'bank_truncated')

    def test_unknown_is_not_a_proof(self):
        class Unknown(smt.Z3Backend):
            def check(self, formula, want_model_of=None):
                self.calls += 1
                return smt.Result('unknown')
        src = ('G_AND', 32, ('G_OR', 32, ('var', 0), ('var', 1)),
               ('var', 0))
        cands, st = discover.discover(self._inst(src, (32, 32)), Unknown(),
                                      discover.Limits())
        self.assertEqual(cands, [])
        self.assertEqual(st['stop'], 'smt_unknown')
        self.assertGreater(st['smt_unknown'], 0)


@unittest.skipUnless(HAVE_LLC, 'no llc (set GIRS_LLC)')
class RealExtractionTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.TemporaryDirectory()
        mir = os.path.join(cls.tmp.name, 'chain.mir')
        with open(mir, 'w') as f:
            f.write(CHAIN_MIR)
        _, out = cli._extract_one(LLC, mir, cls.tmp.name, 'mir',
                                  targets.get('AMDGPU'))
        assert out, 'the extractor failed'
        cls.out = out
        with open(out) as f:
            cls.records = [json.loads(l) for l in f if l.strip()]
        cls.insts, cls.stats = corpus.load([out])

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def _roots(self, fn='chain'):
        return {r['root']: r for r in self.records
                if r['fn'] == fn and r['interior'] == 1}

    def test_attributes_and_result_index(self):
        roots = self._roots()
        self.assertEqual(roots['%2']['expr']['pred'], 'ult')
        self.assertEqual(roots['%4']['expr']['imm'], 8)
        self.assertEqual(roots['%5']['expr']['res'], 0)
        self.assertEqual(roots['%6']['expr']['res'], 1)
        self.assertEqual(roots['%6']['expr']['w'], 1)
        # The two results are results of one instruction.
        self.assertEqual(roots['%5']['expr']['mi'], '%5')
        self.assertEqual(roots['%6']['expr']['mi'], '%5')
        self.assertNotIn('mi', roots['%2']['expr'])
        keys = {n[0] for i in self.insts for n in ir.nodes(i.expr)}
        for k in ('G_ICMP:ult', 'G_SEXT_INREG:8', 'G_UADDO', 'G_UADDO#1',
                  'G_SELECT', 'G_FPEXT', 'G_FPTOSI', 'G_FREEZE'):
            self.assertIn(k, keys)

    def test_types_and_fp_constant(self):
        roots = self._roots()
        r = roots['%9']
        self.assertEqual(r['expr']['type'], 'f64')
        self.assertEqual(r['inputs'][0]['type'], 'f32')
        # 1.5 as an IEEE single: the bit pattern, not the number.
        self.assertEqual(int(r['inputs'][0]['const'], 16), 0x3fc00000)
        inst = next(i for i in self.insts
                    if i.expr == ('G_FPEXT', 64, ('var', 0)))
        self.assertEqual(inst.consts, (0x3fc00000,))
        # The compiler reports no known bits for the floating-point
        # constant; the instance has all of them.
        self.assertEqual(r['inputs'][0]['zero'], '0x0')
        # A constant is never undef or poison.
        self.assertEqual(inst.facts, ((0xc03fffff, 0x3fc00000, True),))
        self.assertEqual(ir.evaluate(inst.expr, inst.vw, inst.consts),
                         0x3ff8000000000000)

    def test_definedness_of_an_input(self):
        """The extractor says which inputs are neither undef nor poison,
        and the fact reaches the instance: a search without the e-graph
        combiner can find a rule that needs it."""
        roots = self._roots()
        # %15 = G_AND %14, %14 with %14 = G_FREEZE %0.
        self.assertIs(roots['%15']['inputs'][0]['noundef'], True)
        # %2 = G_ICMP %0, %1: copies of physical registers.
        self.assertIs(roots['%2']['inputs'][0]['noundef'], False)
        inst = next(i for i in self.insts
                    if i.expr == ('G_AND', 32, ('var', 0), ('var', 0)))
        self.assertEqual(inst.facts[0][2:], (True,))
        inst = next(i for i in self.insts if i.expr == (
            'G_ICMP:ult', 1, ('var', 0), ('var', 1)))
        self.assertEqual(len(inst.facts[0]), 2)

    def test_legality_table(self):
        t = targets.get('AMDGPU')
        mir = os.path.join(self.tmp.name, 'one.ll')
        with open(mir, 'w') as f:
            f.write('define i32 @f(i32 %a, i32 %b) {\n'
                    '  %c = add i32 %a, %b\n  ret i32 %c\n}\n')
        out = cli._legality(LLC, t, mir,
                            os.path.join(self.tmp.name, 'legality.json'))
        self.assertTrue(out)
        cap = targets.Capability.load(out)
        self.assertEqual(cap.action('G_ADD', [32]), 'Legal')
        self.assertTrue(cap.capable('G_ADD', [(32, 'i')]))
        # Two type indices: the result and the operand.
        self.assertIn(cap.action('G_ZEXT', [64, 32]), ('Legal', 'Custom'))
        self.assertEqual(cap.action('G_NO_SUCH_OP', [32]), 'Unsupported')
        self.assertFalse(cap.capable('G_NO_SUCH_OP', [(32, 'i')]))
        # The digest is a part of the identity of a search.
        lim = discover.Limits(grammar='auto', capability=cap)
        self.assertEqual(lim.identity()['capability'], cap.digest)

    def test_the_instance_is_searched(self):
        """The search reads the extracted tree: the conversion of the
        constant is the constant 1."""
        inst = next(i for i in self.insts if i.expr == (
            'G_FPTOSI', 64, ('G_FPEXT', 64, ('var', 0))))
        cands, st = discover.discover(inst, smt.Z3Backend(),
                                      discover.Limits())
        self.assertIn(('lit', 64, '1'), [c['tgt'] for c in cands])

    def test_shapes_that_are_not_extracted(self):
        """No tree has a pointer, a vector, a value wider than 64 bits or
        a G_PHI, as a node or as an input."""
        ops_seen = set()
        for r in self.records:
            for n in _trees(r['expr']) + r['inputs']:
                self.assertLessEqual(n['w'], 64)
                self.assertFalse(n['type'].startswith(('p', '<')), n)
            ops_seen |= {n['op'] for n in _trees(r['expr'])}
        self.assertEqual(ops_seen & {
            'G_PHI', 'G_PTR_ADD', 'G_BUILD_VECTOR', 'G_INTTOPTR',
            'G_PTRTOINT', 'G_BRCOND'}, set())
        # The s128 addition and the vector addition are not roots, and the
        # truncation of the s128 value has no tree: its operand is not a
        # supported scalar.
        adds = [r for r in self.records if r['fn'] == 'chain' and
                r['interior'] == 1 and r['expr']['op'] == 'G_ADD']
        self.assertEqual(len(adds), 2)
        # The value of a G_PHI is an input of the tree of its user.
        sub = next(r for r in self.records
                   if r['fn'] == 'phi' and r['expr']['op'] == 'G_SUB')
        self.assertEqual(sub['inputs'][0]['def'], 'G_PHI')

    def test_reader_refuses_with_a_reason(self):
        reasons = self.stats['unsupported_reasons']
        self.assertIn('type bf16 has no model', reasons)
        self.assertTrue(any('G_ANYEXT' in r for r in reasons), reasons)
        self.assertEqual(self.stats['unsupported'], sum(reasons.values()))
        for i in self.insts:
            for n in ir.nodes(i.expr):
                self.assertNotIn(ops.base(n[0]), ('G_ANYEXT', 'G_PTRTOINT',
                                                  'G_INTTOPTR'))

    def test_all_command(self):
        """`all` gives its subcommands every argument they read."""
        d = self.tmp.name
        args = cli.build_parser().parse_args([
            'all', '--llc', LLC, '--corpus-dir', os.path.join(d, 'corpus'),
            '--db', os.path.join(d, 'rules.json'),
            '--proofs', os.path.join(d, 'proofs'),
            '--td', os.path.join(d, 'out.td'),
            '--inc', os.path.join(d, 'out.inc'),
            '--max-instances', '30', '--grammar', 'all'])
        self.assertFalse(args.fn(args))
        with open(os.path.join(d, 'rules.json')) as f:
            db = json.load(f)
        self.assertEqual(db['limits']['discovery']['grammar'], 'all')
        self.assertEqual(db['discovery_mode'], 'semantics-only')
        self.assertTrue(os.path.getsize(os.path.join(d, 'out.td')))


class ProbeLoopTest(unittest.TestCase):
    """A rule that loops with an existing combine: the probe ends, and the
    rule is not a new rule."""

    def test_the_probe_has_a_time_limit(self):
        from girs import measure
        with tempfile.TemporaryDirectory() as d:
            fake = os.path.join(d, 'llc')
            with open(fake, 'w') as f:
                f.write('#!/bin/sh\nexec sleep 60\n')
            os.chmod(fake, 0o755)
            with self.assertRaises(measure.CombinerLoop):
                measure.run_combiner(fake, targets.get('AMDGPU'), '',
                                     timeout=1)

    def test_a_failure_is_not_a_loop(self):
        from girs import measure
        with tempfile.TemporaryDirectory() as d:
            fake = os.path.join(d, 'llc')
            with open(fake, 'w') as f:
                f.write('#!/bin/sh\nexit 1\n')
            os.chmod(fake, 0o755)
            with self.assertRaises(RuntimeError) as cm:
                measure.run_combiner(fake, targets.get('AMDGPU'), '')
            self.assertNotIsInstance(cm.exception, measure.CombinerLoop)

    def test_classes_of_the_probe(self):
        from unittest import mock
        from girs import measure, select
        rules = [{'id': 'loops'}, {'id': 'fails'}]

        def run(llc, target, mir, synth=False, disabled=()):
            if synth and 'loops' not in disabled:
                raise measure.CombinerLoop('llc did not end')
            if synth:
                raise RuntimeError('llc failed')
            return ''
        with mock.patch.object(select.emit, 'record_names',
                               lambda r: [r['id']]), \
                mock.patch.object(select, 'examples', lambda r: []), \
                mock.patch.object(measure, 'run_combiner', run):
            nov = select.novelty('llc', targets.get('AMDGPU'), rules)
        self.assertEqual(nov['loops']['class'], 'loop')
        self.assertEqual(nov['fails']['class'], 'error')


class SearchPipelineTest(unittest.TestCase):
    def test_changed_window_invalidates_extracted_files(self):
        from girs import mine
        from pathlib import Path
        with tempfile.TemporaryDirectory() as root:
            d = os.path.join(root, 'corpus')
            key = {'depth': 2, 'compiler': 'a'}
            mine._stage_cache(d, key)
            p = Path(d) / 'old.jsonl'
            p.write_text('old depth')
            mine._stage_cache(d, key)
            self.assertTrue(p.exists())
            mine._stage_cache(d, dict(key, depth=4))
            self.assertFalse(p.exists())

    def test_equal_and_growing_rules_reach_target_measurement(self):
        from girs import emit, synth
        src = ('G_SUB', 32, ('var', 0), ('var', 1))
        tgt = ('G_ADD', 32, ('var', 0),
               ('G_SUB', 32, ('lit', 32, '0'), ('var', 1)))
        inst = corpus.Instance(src, (32, 32), [(0, 0)] * 2,
                               [None] * 2, [], [], [('f', 'fn', '%0')])
        sy = synth.Synthesizer(smt.Z3Backend())
        rid = sy.add(inst, tgt)
        self.assertIsNotNone(rid)
        sy.finalize([inst], preserve_alternatives=True)
        rule = synth.strip_private(sy.rules[rid])
        self.assertEqual(rule['class'], 'increases_cost')
        self.assertEqual(emit.candidates({'rules': [rule]}), [])
        rule['target_cost_candidate'] = True
        self.assertIn(rid, [r['id'] for r in emit.candidates(
            {'rules': [rule]}, targets.get('AMDGPU'))])
        # Expanding the grammar does not bypass semantic eligibility.
        rule['semantic_status']['kind'] = 'unknown'
        self.assertEqual(emit.candidates({'rules': [rule]}), [])


if __name__ == '__main__':
    unittest.main()
