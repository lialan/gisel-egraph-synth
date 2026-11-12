#!/usr/bin/env python3
"""A rule from a corpus to the compiler, in a scratch build.

    corpus MIR --extract--> trees --synth (cold)--> proved rules
        --emit (scratch profile)--> td + guards --build--> llc
        --lit (test/SynthChain)--> the rules fire, and their guards fail
                                   where the facts are missing

The corpus is tests/data/chain/corpus.mir: functions with x + 1 where the
low bit of x is known zero, and a sum with its carry. The search runs
without the catalog (``synth --known '' --cache ''``) and with
``--cost-slack 0 --regions --grammar registry``: the rule x + y -> x | y
is an equal-cost rule, which only a search for target-cost candidates
admits, and the sum with its carry is a rule with two outputs, whose
G_UADDO is an operator of the registry grammar. The search gets the corpus and
nothing else; this script checks what it found.

The script then writes a scratch profile that selects the given rules
(``--rules``, default: the rules of CHAIN_RULES that the search found),
emits the TableGen records and guards into a copy of the source tree, builds
that copy in a build directory of its own, and runs the lit tests of
test/SynthChain with the llc of that build (lit parameter synth_chain). The
generated files of the repository, its build and its target profiles are
not changed.

    python3 tools/gisel-rule-synth/eval/rule_chain.py --run-dir /tmp/chain \\
        --llvm-build build/llvm
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
TOOL = os.path.dirname(HERE)
sys.path.insert(0, TOOL)

from girs import emit, known, paths, targets  # noqa: E402

CORPUS = os.path.join(TOOL, 'tests', 'data', 'chain', 'corpus.mir')
# What the chain demonstrates, by the source and the replacement of a rule
# (the ids are content hashes; the script reports the ids it finds).
CHAIN_RULES = {
    '(G_ADD:s32 x0 x1)': '(G_OR:s32 x0 x1)',
    '(G_ICMP:ult:s1 (G_ADD:s32 x0 x1) x0)':
        '(G_UADDO#1:s1 x0 x1); $t0 = (G_UADDO:s32 x0 x1)',
}


def run(cmd, log, **kw):
    print('+ ' + ' '.join(cmd), flush=True)
    with open(log, 'a') as f:
        f.write('+ ' + ' '.join(cmd) + '\n')
        f.flush()
        rc = subprocess.run(cmd, stdout=f, stderr=subprocess.STDOUT,
                            **kw).returncode
    if rc:
        sys.exit('rule_chain: failed (%d), see %s' % (rc, log))


def find_rules(db):
    """The rules of the search that are the rules of CHAIN_RULES."""
    out = {}
    for r in db['rules']:
        want = CHAIN_RULES.get(r['source'])
        if want == r['replacement'] and \
                r['semantic_status']['kind'] == 'verified_refinement':
            out[r['source']] = r
    return out


def scratch_profiles(db, ids):
    """The profile of each target: AMDGPU selects ``ids`` (in the order of
    emit.candidates), AArch64 nothing."""
    cands = [r['id'] for r in emit.candidates(db, targets.get('AMDGPU'))
             if r['id'] in ids]
    missing = sorted(set(ids) - set(cands))
    if missing:
        sys.exit('rule_chain: not emission candidates: %s' % missing)
    return {'AMDGPU': {'rules': {i: {'selection': 'emitted'} for i in cands},
                       'baseline': {'order': cands}},
            'AArch64': {'rules': {}, 'baseline': {'order': []}}}


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--run-dir', required=True)
    ap.add_argument('--llc', default=paths.llc(),
                    help='llc of this project for the extraction')
    ap.add_argument('--llvm-build', default=paths.LLVM_BUILD,
                    help='the stock LLVM build (cmake, llvm-lit, FileCheck)')
    ap.add_argument('--rules', nargs='*',
                    help='rule ids to build (default: the rules of '
                    'CHAIN_RULES that the search found)')
    ap.add_argument('--skip-build', action='store_true',
                    help='only extract, search and emit')
    ap.add_argument('-j', '--jobs', type=int, default=os.cpu_count())
    args = ap.parse_args()
    d = os.path.abspath(args.run_dir)
    os.makedirs(d, exist_ok=True)
    log = os.path.join(d, 'chain.log')
    py = sys.executable
    cli = os.path.join(TOOL, 'gi-rule-synth.py')
    seconds = {}
    report = {'corpus': os.path.relpath(CORPUS, paths.REPO)}

    t = time.monotonic()
    shutil.rmtree(os.path.join(d, 'corpus'), ignore_errors=True)
    run([py, cli, 'extract', '--llc', args.llc, '-o',
         os.path.join(d, 'corpus'), '--mir', CORPUS], log)
    seconds['extract'] = round(time.monotonic() - t, 2)

    t = time.monotonic()
    lib = os.path.join(d, 'library')
    shutil.rmtree(lib, ignore_errors=True)
    run([py, cli, 'synth', os.path.join(d, 'corpus'), '--known', '',
         '--cache', '', '--cost-slack', '0', '--regions', '--grammar',
         'registry', '-o', os.path.join(lib, 'rules.json'), '--proofs',
         os.path.join(lib, 'proofs')], log)
    seconds['synth'] = round(time.monotonic() - t, 2)
    with open(os.path.join(lib, 'rules.json')) as f:
        db = json.load(f)
    known.require_current(db)
    found = find_rules(db)
    report['rules'] = {s: {'id': r['id'], 'replacement': r['replacement'],
                           'precondition': r['precondition'],
                           'precondition_source': r['precondition_source'],
                           'class': r['class'],
                           'discovery': r['provenance']['discovery'],
                           'width_maps': sorted({tuple(map(tuple, m))
                                                 for dj in r['disjuncts']
                                                 for m in dj['width_maps']})}
                       for s, r in found.items()}
    print(json.dumps(report['rules'], indent=1))
    if set(found) != set(CHAIN_RULES) and not args.rules:
        sys.exit('rule_chain: the search did not find %s' %
                 sorted(set(CHAIN_RULES) - set(found)))
    ids = args.rules or [r['id'] for r in found.values()]

    t = time.monotonic()
    src = os.path.join(d, 'src')
    run(['rsync', '-a', '--delete', '--exclude', '.git', '--exclude',
         'build', '--exclude', 'third_party', '--exclude', '.cache',
         '--exclude', '__pycache__', paths.REPO + '/', src + '/'], log)
    td, inc, info = emit.emit(db, scratch_profiles(db, ids))
    for path, text in ((paths.GEN_TD, td), (paths.GEN_INC, inc)):
        with open(os.path.join(src, os.path.relpath(path, paths.REPO)),
                  'w') as f:
            f.write(text)
    report['emit'] = info
    seconds['emit'] = round(time.monotonic() - t, 2)
    if args.skip_build:
        print(json.dumps(report, indent=1))
        return 0

    t = time.monotonic()
    build = os.path.join(d, 'build')
    cmake = ['cmake', '-G', 'Ninja', '-S', src, '-B', build,
             '-DCMAKE_BUILD_TYPE=Release',
             '-DLLVM_DIR=' + os.path.join(args.llvm_build, 'lib', 'cmake',
                                          'llvm')]
    if shutil.which('clang'):
        cmake += ['-DCMAKE_C_COMPILER=clang', '-DCMAKE_CXX_COMPILER=clang++']
    if shutil.which('ld.lld'):
        cmake += ['-DLLVM_USE_LINKER=lld']
    run(cmake, log)
    run(['ninja', '-C', build, '-j', str(args.jobs), paths.LLC_TARGET], log)
    seconds['build'] = round(time.monotonic() - t, 2)

    t = time.monotonic()
    lit = os.path.join(args.llvm_build, 'bin', 'llvm-lit')
    res = subprocess.run([lit, '-v', '--param', 'synth_chain=1',
                          os.path.join(build, 'test', 'SynthChain')],
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True)
    with open(log, 'a') as f:
        f.write(res.stdout)
    print(res.stdout)
    seconds['lit'] = round(time.monotonic() - t, 2)
    report.update(llc=os.path.join(build, 'bin', 'llc'), seconds=seconds,
                  lit_returncode=res.returncode,
                  lit=[line for line in res.stdout.splitlines()
                       if line.startswith(('PASS', 'FAIL', 'UNSUPPORTED',
                                           'XFAIL', 'XPASS'))])
    with open(os.path.join(d, 'chain.json'), 'w') as f:
        json.dump(report, f, indent=1, sort_keys=True)
        f.write('\n')
    print(json.dumps({k: report[k] for k in ('seconds', 'lit')}, indent=1))
    return res.returncode


if __name__ == '__main__':
    sys.exit(main())
