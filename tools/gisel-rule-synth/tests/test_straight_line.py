"""Straight-line regions, including extraction -> discovery -> joint proof
-> generated TableGen/C++ -> a real combiner -> MachineVerifier.

GIRS_LLC enables extraction tests. GIRS_TEST_REGION_BUILD=1 additionally
builds an isolated compiler with the discovered rules, using GIRS_LLVM_BUILD.
GIRS_REGION_EVIDENCE optionally saves its corpus, rules, and before/after MIR.
It never edits the checked-in generated rules or their target profiles.
"""

import copy
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from girs import corpus, discover, emit, ir, paths, region, sibling, smt, synth
from test_sibling import SUB, ULT, pairs_of

LLC = os.environ.get('GIRS_LLC', paths.llc())
HAVE_LLC = os.path.isfile(LLC)

JOINT = '''---
name: joint
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0, $vgpr1
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s32) = G_ADD %0, %1
    G_BR %bb.2
  bb.1:
    %3:_(s1) = G_ICMP intpred(ult), %2(s32), %0
    %4:_(s32) = G_ZEXT %3
    $vgpr0 = COPY %4
    $vgpr1 = COPY %2
    SI_RETURN implicit $vgpr0, implicit $vgpr1
  bb.2:
    G_BR %bb.1
...
'''

SIBLINGS = '''---
name: siblings
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0, $vgpr1
    %0:_(s32) = COPY $vgpr0
    %1:_(s32) = COPY $vgpr1
    %2:_(s32) = G_SUB %0, %1
    G_BR %bb.1
  bb.1:
    %3:_(s1) = G_ICMP intpred(ult), %0(s32), %1
    %4:_(s32) = G_ZEXT %3
    $vgpr0 = COPY %4
    $vgpr1 = COPY %2
    SI_RETURN implicit $vgpr0, implicit $vgpr1
...
'''

# Same arithmetic but the sum's block has two successors; this must not
# acquire the straight-line scope, even though it dominates the comparison.
BRANCH = JOINT.replace('name: joint', 'name: branch').replace(
    '    G_BR %bb.2',
    '    %6:_(s1) = G_ICMP intpred(eq), %0(s32), %1\n'
    '    G_BRCOND %6, %bb.1\n    G_BR %bb.2', 1)

PHI_USER = JOINT.replace('name: joint', 'name: phi_user').replace(
    '    $vgpr0 = COPY %4\n    $vgpr1 = COPY %2\n'
    '    SI_RETURN implicit $vgpr0, implicit $vgpr1', '    G_BR %bb.3').replace(
    '...\n', '  bb.3:\n'
    '    %5:_(s32) = G_PHI %2(s32), %bb.1\n'
    '    $vgpr0 = COPY %4\n    $vgpr1 = COPY %5\n'
    '    SI_RETURN implicit $vgpr0, implicit $vgpr1\n...\n')


def run_llc(llc, mir, *args, target='AMDGPU'):
    target_args = ['-mtriple=amdgcn-amd-amdhsa', '-mcpu=gfx900'] \
        if target == 'AMDGPU' else ['-mtriple=aarch64-linux-gnu']
    p = subprocess.run([llc, *target_args,
                        '-x', 'mir', '-verify-machineinstrs', *args,
                        '-o', '-', '-'], input=mir, text=True,
                       capture_output=True, timeout=60)
    if p.returncode:
        raise AssertionError(p.stderr + '\n' + mir)
    return p.stdout


def extract(mir, directory):
    path = Path(directory) / 'corpus.jsonl'
    run_llc(LLC, mir, '-run-pass=gisel-synth-corpus',
            '-gisel-synth-corpus-out=' + str(path))
    return path, [json.loads(s) for s in path.read_text().splitlines()]


def discover_joint(inst):
    backend = smt.Z3Backend()
    limits = discover.Limits(grammar='registry')
    ctx = discover.Context(limits)
    sy = synth.Synthesizer(backend, synth.SynthLimits())
    candidates, _ = discover.discover(inst, backend, limits, ctx)
    tgts = [c['tgt'] for c in candidates]
    for t in region.root_alternatives(inst, limits, ctx):
        if t not in tgts and discover.prove_concrete(
                inst, t, backend).status == 'unsat':
            tgts.append(t)
    pending = []
    for tgt in tgts:
        rid = sy.add(inst, tgt)
        if rid:
            pending.append((inst, tgt, rid))
    sy.finalize([inst])
    region.extend(sy, pending, backend, limits, ctx)
    return [synth.strip_private(r) for r in sy.rules.values()
            if r.get('region')]


class ScopeTest(unittest.TestCase):
    def test_old_corpus_stays_local(self):
        self.assertEqual(pairs_of([SUB, dict(ULT, bb=1)])[0], [])

    def test_certified_chain_groups_siblings(self):
        records = [dict(SUB, straight_line=[0, 1]),
                   dict(ULT, bb=1, straight_line=[0, 1])]
        pairs, stats = pairs_of(records)
        self.assertEqual(len(pairs), 2)
        self.assertEqual(stats['cross_block_pairs'], 2)
        # Adding the scope does not count local occurrences twice.
        records[1]['bb'] = 0
        _, stats = pairs_of(records)
        self.assertEqual(stats['pairs'], 2)
        self.assertEqual(stats['cross_block_pairs'], 0)

    def test_inconsistent_and_cyclic_scopes_are_not_joined(self):
        for other in ([1, 2], [0, 1, 0], [0], ['0', 1]):
            pairs, _ = pairs_of([dict(SUB, straight_line=[0, 1]),
                                 dict(ULT, bb=1, straight_line=other)])
            self.assertEqual(pairs, [])

    def test_non_pure_replacements_cannot_cross(self):
        x, y = ('var', 0), ('var', 1)
        self.assertTrue(region.straight_line_expr(('G_UADDO', 32, x, y)))
        for name in ('G_UDIV', 'G_SDIV', 'G_FREEZE', 'G_ANYEXT', 'G_FNEG'):
            e = (name, 32, x, y) if name.endswith('DIV') else (name, 32, x)
            self.assertFalse(region.straight_line_expr(e), name)


@unittest.skipUnless(HAVE_LLC, 'no llc (set GIRS_LLC)')
class ExtractionTest(unittest.TestCase):
    def test_chain_and_joint_proof(self):
        with tempfile.TemporaryDirectory() as d:
            path, records = extract(JOINT, d)
            rec = next(r for r in records if r['root'] == '%3' and
                       r['interior'] == 2)
            self.assertEqual(rec['straight_line'], [0, 2, 1])
            self.assertEqual(rec['expr']['bb'], 1)
            self.assertEqual(rec['expr']['args'][0]['bb'], 0)
            inst = corpus.parse_record(rec, str(path))
            rules = discover_joint(inst)
            self.assertTrue(rules)
            rule = rules[0]
            self.assertEqual(len(rule['region']['outputs']), 2)
            self.assertIn('G_UADDO', rule['replacement'])
            self.assertTrue(all(p['outputs'] == 2 and p['result'] == 'unsat'
                                for c in rule['disjuncts'] for p in c['proofs']))
            # A wrong live-out is rejected even when the primary output is
            # unchanged. The proof is joint, not one query per root.
            bad = copy.deepcopy(rule)
            bad['region']['outputs'][1]['replacement_json'] = ir.to_json(
                ('lit', 32, '0'))
            maps = rule['disjuncts'][0]['width_maps'][:1]
            status, _ = region.verify(region.schedules(bad, maps), [()],
                                      smt.Z3Backend())
            self.assertEqual(status, 'invalid')

    def test_branch_is_a_boundary(self):
        with tempfile.TemporaryDirectory() as d:
            _, records = extract(BRANCH, d)
            for r in records:
                if r['root'] == '%3':
                    self.assertEqual(r['interior'], 1)
                    self.assertNotIn('straight_line', r)

    def test_freeze_and_division_are_boundary_inputs(self):
        for opcode in ('G_UDIV %0, %1', 'G_FREEZE %0'):
            mir = JOINT.replace('G_ADD %0, %1', opcode)
            with tempfile.TemporaryDirectory() as d:
                _, records = extract(mir, d)
                self.assertTrue(any(r['root'] == '%3' for r in records))
                for r in records:
                    if r['root'] == '%3':
                        self.assertEqual(r['interior'], 1)

    def test_conditional_branch_with_one_successor_is_a_boundary(self):
        mir = JOINT.replace('    G_BR %bb.2',
                            '    %6:_(s1) = G_ICMP intpred(eq), %0(s32), %1\n'
                            '    G_BRCOND %6, %bb.2\n    G_BR %bb.2', 1)
        with tempfile.TemporaryDirectory() as d:
            _, records = extract(mir, d)
            roots = [r for r in records if r['root'] == '%3']
            self.assertTrue(roots)
            self.assertTrue(all(r['interior'] == 1 for r in roots))

    def test_boundary_load_keeps_its_extension_fact(self):
        mir = '''---
name: load_fact
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0_vgpr1
    %0:_(p1) = COPY $vgpr0_vgpr1
    %1:_(s32) = G_ZEXTLOAD %0(p1) :: (load (s8), addrspace 1)
    G_BR %bb.1
  bb.1:
    %2:_(s32) = G_CONSTANT i32 255
    %3:_(s32) = G_AND %1, %2
    $vgpr0 = COPY %3
    SI_RETURN implicit $vgpr0
...
'''
        with tempfile.TemporaryDirectory() as d:
            _, records = extract(mir, d)
            hints = [r for r in records if r['expr']['args'][0].get('load')]
            self.assertTrue(hints)
            self.assertEqual(hints[0]['expr']['args'][0]['op'], 'G_ASSERT_ZEXT')
            self.assertNotIn('straight_line', hints[0])

    def test_real_cross_block_siblings(self):
        with tempfile.TemporaryDirectory() as d:
            path, _ = extract(SIBLINGS, d)
            stats = {}
            pairs = sibling.load_pairs([str(path)], stats)
            self.assertGreater(stats['cross_block_pairs'], 0)
            self.assertTrue(any(p.inst.expr[0] == 'G_SUB' and
                                p.sib[0] == 'G_ICMP:ult' for p in pairs))


@unittest.skipUnless(HAVE_LLC and os.environ.get('GIRS_TEST_REGION_BUILD') == '1',
                     'set GIRS_TEST_REGION_BUILD=1 to build discovered rules')
class GeneratedCombinerTest(unittest.TestCase):
    def test_discovered_rules_rewrite_real_cross_block_mir(self):
        with tempfile.TemporaryDirectory(prefix='girs-straight-line-') as d:
            path, records = extract(JOINT + SIBLINGS, d)
            # Keep three real extracted records to bound the CLI search.
            # The candidates and their replacements are not prescribed.
            records = [r for r in records if
                       (r['fn'] == 'joint' and r['root'] == '%3' and
                        r['interior'] == 2) or
                       (r['fn'] == 'siblings' and r['root'] in ('%2', '%3')
                        and r['interior'] == 1)]
            self.assertEqual(len(records), 3)
            path.write_text(''.join(json.dumps(r) + '\n' for r in records))
            cli = str(Path(paths.TOOL) / 'gi-rule-synth.py')
            database = Path(d) / 'rules.json'
            command = [sys.executable, cli, 'synth', str(path),
                       '-o', str(database), '--proofs', str(Path(d) / 'proofs'),
                       '--grammar', 'registry', '--regions', '--siblings',
                       '--known', '', '--cache', '']
            p = subprocess.run(command, text=True, capture_output=True,
                               timeout=120)
            self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
            db = json.loads(database.read_text())
            rules = [r for r in db['rules'] if r.get('region')]
            self.assertTrue(any(not r['region'].get('siblings') for r in rules))
            self.assertTrue(any(r.get('region', {}).get('siblings')
                                for r in rules))
            db['rules'] = rules
            database.write_text(json.dumps(db))
            source = Path(d) / 'source'
            shutil.copytree(paths.REPO, source,
                            ignore=shutil.ignore_patterns('.git', 'build',
                                                         'third_party',
                                                         '__pycache__'))
            command = [sys.executable, cli, 'emit', str(database),
                       '--all-candidates', '--td',
                       str(source / 'td/GISynthCombines.td'), '--inc',
                       str(source / 'include/GISelEGraphSynth/'
                           'GISynthGeneratedPredicates.inc')]
            p = subprocess.run(command, text=True, capture_output=True, timeout=30)
            self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
            build = Path(d) / 'build'
            commands = [
                ['cmake', '-G', 'Ninja', '-S', str(source), '-B', str(build),
                 '-DCMAKE_BUILD_TYPE=Release',
                 '-DLLVM_DIR=' + paths.LLVM_BUILD + '/lib/cmake/llvm',
                 '-DGISELEGRAPHSYNTH_INCLUDE_TESTS=OFF'],
                ['cmake', '--build', str(build), '--target',
                 paths.LLC_TARGET, '-j', '8']]
            for command in commands:
                p = subprocess.run(command, text=True, capture_output=True,
                                   timeout=600)
                self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
            compiler = str(build / 'bin/llc')
            evidence = os.environ.get('GIRS_REGION_EVIDENCE')
            if evidence:
                evidence = Path(evidence)
                evidence.mkdir(parents=True, exist_ok=True)
                shutil.copy2(path, evidence / 'corpus.jsonl')
                shutil.copy2(database, evidence / 'rules.json')
                shutil.copytree(Path(d) / 'proofs', evidence / 'proofs',
                                dirs_exist_ok=True)
            cases = [(JOINT, 'G_UADDO', 'AMDGPU'),
                     (SIBLINGS, 'G_USUBO', 'AMDGPU'),
                     (PHI_USER, 'G_UADDO', 'AMDGPU')]
            cases += [(mir.replace('$vgpr', '$x').replace('(s32)', '(i64)')
                       .replace('(s1)', '(i1)').replace('SI_RETURN',
                                                       'RET_ReallyLR'),
                       opcode, 'AArch64') for mir, opcode, _ in list(cases)]
            for mir, opcode, target in cases:
                before = run_llc(compiler, mir, '-run-pass=none', target=target)
                after = run_llc(compiler, mir,
                                '-run-pass=gisynth-' + target.lower() +
                                '-combiner', target=target)
                if evidence:
                    name = re.search(r'name: (\w+)', mir)[1] + '-' + target
                    (evidence / (name + '.before.mir')).write_text(before)
                    (evidence / (name + '.after.mir')).write_text(after)
                self.assertEqual(after.count(' = ' + opcode + ' '), 1, after)
                self.assertNotIn(' = G_ICMP ', after)
                # The replacement is before the first crossing. Branches,
                # successor lists and block layout are preserved exactly.
                self.assertLess(after.index(opcode), after.index('G_BR '))
                cfg = lambda text: [ln.strip() for ln in text.splitlines()
                                    if re.match(r'\s*(bb\.\d|successors:|G_BR)',
                                                ln)]
                self.assertEqual(cfg(before), cfg(after))
            rejected = run_llc(compiler, BRANCH,
                               '-run-pass=gisynth-amdgpu-combiner')
            self.assertNotIn('G_UADDO', rejected)
            self.assertIn('G_ADD', rejected)


if __name__ == '__main__':
    unittest.main()
