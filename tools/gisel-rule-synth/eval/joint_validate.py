#!/usr/bin/env python3
"""Validation of a generated joint rule in real LLVM pipelines.

For one source function (default: the difference of squares of the joint
region search) and each target (gfx1100, AArch64):

  * `opt -O2`, then the llc of this project with and without
    -gisel-synth-joint-combines (one binary; -global-isel-abort=1, so a
    SelectionDAG fallback is a failure; -verify-machineinstrs), and the
    stock llc of the LLVM build, which must give the same code as the run
    without the flag;
  * the MIR after the pre-legalizer combiner, and mutations of it: commuted
    operands, wrong instructions, flags, inputs that are not defined, a
    second user of an inner value, an instruction in another block or after
    the user of an output, frozen and computed-undef inputs, other widths.
    Each runs -run-pass=gisynth-joint-combiner with the verifier, and the
    result must be the expected one (rewritten or not, flags dropped).

Writes results.json, commands.json and provenance.json to --out.
"""

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--llvm-build', required=True, type=Path)
p.add_argument('--llc', required=True, type=Path)
p.add_argument('--out', required=True, type=Path)
p.add_argument('--rule', default=None, help='expected rule id (debug line)')
args = p.parse_args()
args.out.mkdir(parents=True, exist_ok=True)
commands = []


def run(cmd, log, check=True, inp=None):
    cmd = list(map(str, cmd))
    r = subprocess.run(cmd, text=True, capture_output=True, input=inp)
    commands.append({'command': cmd, 'returncode': r.returncode})
    (args.out / (log + '.log')).write_text(r.stdout + r.stderr)
    if check and r.returncode:
        raise RuntimeError(f'{log}: {r.stderr[-3000:]}')
    return r


SOURCE = '''define {i32, i32} @difference_squares(i32 noundef %x, i32 noundef %y) {
entry:
  %s = mul i32 %x, %x
  %a = sub i32 %x, %y
  %b = add i32 %x, %y
  %d = mul i32 %a, %b
  %r0 = insertvalue {i32, i32} poison, i32 %s, 0
  %r1 = insertvalue {i32, i32} %r0, i32 %d, 1
  ret {i32, i32} %r1
}
'''
src = args.out / 'input.ll'
src.write_text(SOURCE)
results = {'pipeline': {}, 'mir': []}
INSN = re.compile(r'^\t[a-zA-Z][a-zA-Z0-9_.]*(?:\s|$)')
TARGETS = [('amdgpu', ['-mtriple=amdgpu11.00-amd-amdhsa', '-mcpu=gfx1100']),
           ('aarch64', ['-mtriple=aarch64-linux-gnu'])]


def asm_ops(path):
    return [s.strip() for s in path.read_text().splitlines()
            if INSN.match(s)]


def body(text):
    return text.split('body:', 1)[1]


def debug_counts(text):
    c = {}
    for m in re.finditer(r'gisel-synth-joint: ([a-z ]+): (\w+)', text):
        c[m.group(1)] = c.get(m.group(1), 0) + 1
    return c


for target, flags in TARGETS:
    ir = args.out / (target + '-O2.ll')
    run([args.llvm_build / 'bin/opt', '-passes=default<O2>', '-S', *flags,
         src, '-o', ir], target + '-opt')
    base = [args.llc, '-O2', '-global-isel=1', '-global-isel-abort=1',
            '-verify-machineinstrs', *flags, ir]
    counts = {}
    for enable in (False, True):
        tag = target + ('-after' if enable else '-before')
        extra = ['-gisel-synth-joint-combines',
                 '-debug-only=gisel-synth-joint'] if enable else []
        r = run([*base, *extra, '-o', args.out / (tag + '.s')], tag + '-asm')
        if enable:
            counts = debug_counts(r.stderr)
        stop = ('gisynth-joint-combiner' if enable
                else target + '-prelegalizer-combiner')
        run([*base, *extra, '-stop-after=' + stop, '-o',
             args.out / (tag + '.mir')], tag + '-mir')
    before = asm_ops(args.out / (target + '-before.s'))
    after = asm_ops(args.out / (target + '-after.s'))
    run([args.llvm_build / 'bin/llc', *base[1:], '-o',
         args.out / (target + '-stock.s')], target + '-stock')
    stock = asm_ops(args.out / (target + '-stock.s'))
    results['pipeline'][target] = {
        'before': before, 'after': after, 'before_count': len(before),
        'after_count': len(after), 'stock_matches_baseline': stock == before,
        'joint_debug_counts': counts}
    assert stock == before, (target, stock, before)
    assert len(after) < len(before), (target, before, after)

    template = (args.out / (target + '-before.mir')).read_text()
    b = body(template)
    for pat in ['%2:_(i32) = G_MUL %0, %0', '%3:_(i32) = G_SUB %0, %1',
                '%4:_(i32) = G_ADD %1, %0', '%5:_(i32) = G_MUL %3, %4']:
        assert pat in b, (target, pat, b)
    ret_copy = '$vgpr1 = COPY %5(i32)' if target == 'amdgpu' else \
        '$w1 = COPY %5(i32)'
    assert ret_copy in b, (target, b)

    # (name, mir, expectation): 'rewrite', 'rewrite-relax' (the square
    # loses its flags) or 'keep'.
    cases = [('positive', template, 'rewrite')]

    def add(name, old, new, expect='keep', text=None):
        t = text if text is not None else template
        assert old in t, (name, old)
        cases.append((name, t.replace(old, new), expect))
    add('commuted_mul', 'G_MUL %3, %4', 'G_MUL %4, %3', 'rewrite')
    add('commuted_add', 'G_ADD %1, %0', 'G_ADD %0, %1', 'rewrite')
    add('wrong_square', 'G_MUL %0, %0', 'G_MUL %0, %1')
    add('wrong_add', 'G_ADD %1, %0', 'G_ADD %1, %1')
    add('reversed_sub', 'G_SUB %0, %1', 'G_SUB %1, %0')
    add('xor_not_add', 'G_ADD %1, %0', 'G_XOR %1, %0')
    # Flags of the square, which stays and which a new instruction reads:
    # the rule drops them (relax). Flags of the instructions that die do not
    # matter: the proof is for the source without flags.
    for flag in ['nsw', 'nuw']:
        add('square_' + flag, '= G_MUL %0, %0', '= ' + flag + ' G_MUL %0, %0',
            'rewrite-relax')
        add('root_' + flag, '= G_MUL %3, %4', '= ' + flag + ' G_MUL %3, %4',
            'rewrite')
    add('sub_nsw', '= G_SUB %0, %1', '= nsw G_SUB %0, %1', 'rewrite')
    add('add_nuw', '= G_ADD %1, %0', '= nuw G_ADD %1, %0', 'rewrite')
    # Not noundef: the guard defined(x), defined(y) fails.
    cases.append(('unproven_inputs', template.replace('noundef ', ''),
                  'keep'))
    square = '    %2:_(i32) = G_MUL %0, %0\n'
    root = '    %5:_(i32) = G_MUL %3, %4\n'
    # The square after the root, before its user: the new instructions are
    # placed after the square.
    cases.append(('square_after_root', template.replace(square, '').replace(
        root, root + square), 'rewrite'))
    # The square after the user of the root: no position dominates the
    # user and follows the square.
    t2 = template.replace(square, '')
    t2 = t2.replace('    ' + ret_copy + '\n', '    ' + ret_copy + '\n' +
                    square)
    cases.append(('square_after_use', t2, 'keep'))
    # A second user of an inner value: it does not die, so it is not a
    # region of this rule.
    for operand in ['%3', '%4']:
        mutated = template.replace(root, root +
                                   f'    %8:_(i32) = G_XOR %5, {operand}\n')
        mutated = mutated.replace(ret_copy, ret_copy.replace('%5', '%8'))
        cases.append(('multiuse_' + operand[1:], mutated, 'keep'))
    # A second user of the square: it stays anyway.
    mutated = template.replace(root, root + '    %8:_(i32) = G_XOR %5, %2\n')
    mutated = mutated.replace(ret_copy, ret_copy.replace('%5', '%8'))
    cases.append(('square_two_users', mutated, 'rewrite'))
    # One block only.
    cases.append(('square_other_block', template.replace(
        '  bb.1.entry:\n', '  bb.1.entry:\n    successors: %bb.2\n').replace(
        '    %3:_(i32)', '    G_BR %bb.2\n  \n  bb.2:\n    %3:_(i32)'),
        'keep'))
    # Frozen inputs are defined for LLVM's own analysis, without noundef.
    frozen = template.replace('noundef ', '').replace(
        '    %2:_(i32)', '    %8:_(i32) = G_FREEZE %0\n'
        '    %9:_(i32) = G_FREEZE %1\n    %2:_(i32)')
    frozen = frozen.replace('G_MUL %0, %0', 'G_MUL %8, %8').replace(
        'G_SUB %0, %1', 'G_SUB %8, %9').replace('G_ADD %1, %0', 'G_ADD %9, %8')
    cases.append(('frozen_inputs', frozen, 'rewrite'))
    # Two different G_FREEZE of one input are two values: not the pattern.
    twofreeze = frozen.replace('    %9:_(i32) = G_FREEZE %1\n',
                               '    %9:_(i32) = G_FREEZE %1\n'
                               '    %10:_(i32) = G_FREEZE %0\n').replace(
        'G_SUB %8, %9', 'G_SUB %10, %9')
    cases.append(('two_freezes', twofreeze, 'keep'))
    undef = template.replace('    %2:_(i32)',
                             '    %8:_(i32) = G_IMPLICIT_DEF\n'
                             '    %9:_(i32) = G_CONSTANT i32 1\n'
                             '    %10:_(i32) = G_OR %8, %9\n    %2:_(i32)')
    undef = undef.replace('G_MUL %0, %0', 'G_MUL %10, %10').replace(
        'G_SUB %0, %1', 'G_SUB %10, %1').replace('G_ADD %1, %0', 'G_ADD %1, %10')
    cases.append(('computed_undef', undef, 'keep'))
    # Other widths: each has its own proof.
    for w in (16, 64):
        srcw = args.out / f'{target}-i{w}.ll'
        srcw.write_text(SOURCE.replace('i32', f'i{w}'))
        mirw = args.out / f'{target}-i{w}.mir'
        run([args.llc, '-O2', *flags, '-global-isel=1', '-global-isel-abort=1',
             '-verify-machineinstrs',
             '-stop-after=' + target + '-prelegalizer-combiner', srcw, '-o',
             mirw], f'{target}-i{w}-generate')
        cases.append((f'i{w}', mirw.read_text(), 'rewrite-width'))

    for name, text, expect in cases:
        tag = target + '-' + name
        inp = args.out / (tag + '-input.mir')
        out = args.out / (tag + '-output.mir')
        inp.write_text(text)
        r = run([args.llc, '-O2', *flags, '-verify-machineinstrs',
                 '-run-pass=gisynth-joint-combiner',
                 '-debug-only=gisel-synth-joint', inp, '-o', out], tag,
                check=False)
        ok = r.returncode == 0
        ob = body(out.read_text()) if ok else ''
        dbg = debug_counts(r.stderr)
        # Applied by the matcher's own count; a rewrite has the shape of
        # the new DAG (two products, one subtraction, no addition).
        rewritten = ok and dbg.get('applied', 0) > 0
        if rewritten:
            assert 'G_ADD' not in ob and ob.count('G_MUL') == 2 and \
                ob.count('G_SUB') == 1, (tag, ob)
        if expect == 'keep':
            passed = ok and not rewritten
        else:
            passed = rewritten
            if expect == 'rewrite-relax':
                passed &= not re.search(r'= n[su]w G_MUL %0, %0', ob)
        results['mir'].append({'target': target, 'case': name,
                               'expected': expect, 'rewritten': rewritten,
                               'llc_ok': ok, 'passed': bool(passed),
                               'debug': dbg})

llvm_rev = subprocess.run(['git', '-C', str(args.llvm_build.parent.parent /
                                            'third_party' / 'llvm-project'),
                           'rev-parse', 'HEAD'], capture_output=True,
                          text=True).stdout.strip()
prov = {'llvm_revision': llvm_rev, 'files': {}}
for f in [args.llc, args.llvm_build / 'bin/llc', args.llvm_build / 'bin/opt']:
    prov['files'][str(f)] = hashlib.sha256(Path(f).read_bytes()).hexdigest()
(args.out / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
(args.out / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
(args.out / 'provenance.json').write_text(json.dumps(prov, indent=2) + '\n')
failed = [m for m in results['mir'] if not m['passed']]
print(json.dumps({'pipeline': {t: (v['before_count'], v['after_count'])
                               for t, v in results['pipeline'].items()},
                  'mir_cases': len(results['mir']),
                  'mir_failed': [(m['target'], m['case'], m['expected'],
                                  m['rewritten'], m['llc_ok'])
                                 for m in failed]}, indent=1))
raise SystemExit(1 if failed else 0)
