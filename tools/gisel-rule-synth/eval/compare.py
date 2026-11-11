#!/usr/bin/env python3
"""Compiles a list of .ll files for one target several ways and compares
the output:

  base    plain GlobalISel (-global-isel)
  synth   + the target's -*-gisel-synth-combines flag (the generated rules)
  egraph  AMDGPU only: + -amdgpu-gisel-egraph -gisel-egraph-mode=rewrite
          (the run-time equality-saturation combiner, used here as an oracle
          for how much a dynamic search finds on the same code)

All runs use -verify-machineinstrs. Per file it records the instruction
count of the assembly, the .s size in bytes, per-mode user CPU time, the
functions that fell back to SelectionDAG (-global-isel-abort=2) and, for
the synth mode of an assertions build, how often each rule matched and how
often it fired. The JSON is the input of `gi-rule-synth.py select --compare`.

  compare.py --llc BUILD/bin/llc --list FILES.txt -o OUT.json [-j N]
             [--target AMDGPU|AArch64] [--modes base,synth]
"""

import argparse
import concurrent.futures
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

from girs import measure, targets  # noqa: E402

EGRAPH = ['-amdgpu-gisel-egraph', '-gisel-egraph-mode=rewrite']


def run(llc, target, path, mode, extra, count_rules):
    if mode == 'synth':
        return measure.compile_ll(llc, target, path, extra, synth=True,
                                  count_rules=count_rules)
    flags = list(extra) + (EGRAPH if mode == 'egraph' else [])
    return measure.compile_ll(llc, target, path, flags)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--llc', required=True)
    ap.add_argument('--list', required=True)
    ap.add_argument('-o', required=True)
    ap.add_argument('-j', type=int, default=os.cpu_count())
    ap.add_argument('--target', default='AMDGPU')
    ap.add_argument('--modes', default='base,synth,egraph')
    ap.add_argument('--extra', default='')
    ap.add_argument('--no-rule-counters', action='store_true',
                    help='do not pass -debug-only=gisel-synth (for timing, '
                    'or for a build without assertions)')
    a = ap.parse_args()
    target = targets.get(a.target)
    files = [l.strip() for l in open(a.list) if l.strip()]
    modes = a.modes.split(',')
    extra = a.extra.split() if a.extra else []
    res = {}

    def one(path):
        return path, {m: run(a.llc, target, path, m, extra,
                             not a.no_rule_counters) for m in modes}
    with concurrent.futures.ThreadPoolExecutor(a.j) as ex:
        for path, r in ex.map(one, files):
            res[path] = r
    with open(a.o, 'w') as f:
        json.dump(res, f, indent=0, sort_keys=True)
    summarize(res, modes)


def summarize(res, modes):
    ok = [p for p, r in res.items() if r['base']['rc'] == 0]
    print('files: %d (%d compile with base)' % (len(res), len(ok)))
    for m in modes:
        if m == 'base':
            continue
        crash = [p for p in ok if res[p][m]['rc'] != 0]
        both = [p for p in ok if res[p][m]['rc'] == 0]
        b = sum(res[p]['base']['insns'] for p in both)
        n = sum(res[p][m]['insns'] for p in both)
        better = sum(res[p][m]['insns'] < res[p]['base']['insns']
                     for p in both)
        worse = sum(res[p][m]['insns'] > res[p]['base']['insns']
                    for p in both)
        bb = sum(res[p]['base']['bytes'] for p in both)
        nb = sum(res[p][m]['bytes'] for p in both)
        print('%-7s crash=%d insns %d -> %d (%+d), files better=%d worse=%d,'
              ' asm bytes %+d' % (m, len(crash), b, n, n - b, better, worse,
                                  nb - bb))
        # A function that falls back to SelectionDAG in only one of the two
        # runs is compiled by different instruction selectors.
        same = [p for p in both if res[p][m].get('fallback', []) ==
                res[p]['base'].get('fallback', [])]
        if len(same) != len(both):
            d = sum(res[p][m]['insns'] - res[p]['base']['insns']
                    for p in same)
            fb = sum(len(res[p]['base'].get('fallback', [])) for p in both)
            fm = sum(len(res[p][m].get('fallback', [])) for p in both)
            print('        SelectionDAG fallbacks %d -> %d; %d files with the'
                  ' same fallbacks: insns %+d, better=%d worse=%d' %
                  (fb, fm, len(same), d,
                   sum(res[p][m]['insns'] < res[p]['base']['insns']
                       for p in same),
                   sum(res[p][m]['insns'] > res[p]['base']['insns']
                       for p in same)))
        if m == 'synth':
            fired = {}
            for p in both:
                for rid, k in res[p][m].get('passed', {}).items():
                    fired[rid] = fired.get(rid, 0) + k
            print('        rules fired: %d distinct, %d applications' %
                  (len(fired), sum(fired.values())))


if __name__ == '__main__':
    main()
