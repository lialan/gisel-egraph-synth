#!/usr/bin/env python3
"""Compiles a list of .ll files for AMDGPU three ways and compares ISA:

  base    plain GlobalISel (-global-isel)
  synth   + -amdgpu-gisel-synth-combines (the generated rules)
  egraph  + -amdgpu-gisel-egraph -gisel-egraph-mode=rewrite (the run-time
          equality-saturation combiner, used here as an oracle for how much
          a dynamic search finds on the same code)

All runs use -verify-machineinstrs. Per file it records the ISA instruction
count (lines starting with s_/v_ in the assembly), the .s size in bytes, and
SGPR/VGPR counts from the kernel metadata, plus per-mode user CPU time.

  compare.py --llc BUILD/bin/llc --list FILES.txt -o OUT.json [-j N]
"""

import argparse
import concurrent.futures
import json
import os
import re
import resource
import subprocess
import tempfile

BASE = ['-mtriple=amdgcn-amd-amdhsa', '-mcpu=gfx1100', '-O2', '-global-isel',
        '-global-isel-abort=2', '-verify-machineinstrs']
MODES = {
    'base': [],
    # -debug-only needs an assertions build; it lists the rules that fired.
    'synth': ['-amdgpu-gisel-synth-combines', '-debug-only=gisel-synth'],
    'egraph': ['-amdgpu-gisel-egraph', '-gisel-egraph-mode=rewrite'],
}
INSN = re.compile(r'^\s+[sv]_[a-z0-9_]+', re.M)
SGPR = re.compile(r'^\s+\.sgpr_count:\s+(\d+)', re.M)
VGPR = re.compile(r'^\s+\.vgpr_count:\s+(\d+)', re.M)


def run(llc, path, mode, extra):
    with tempfile.NamedTemporaryFile(suffix='.s', delete=False) as tf:
        out = tf.name
    cmd = [llc] + BASE + MODES[mode] + extra + [path, '-o', out]
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    p = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                       text=True)
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    res = {'rc': p.returncode}
    fired = re.findall(r'gisel-synth: guard passed: (\w+)', p.stderr)
    if fired:
        res['fired'] = sorted(set(fired))
    if p.returncode == 0:
        s = open(out).read()
        res.update(insns=len(INSN.findall(s)), bytes=len(s),
                   sgpr=sum(map(int, SGPR.findall(s))),
                   vgpr=sum(map(int, VGPR.findall(s))))
    else:
        res['err'] = p.stderr[-400:]
    os.remove(out)
    res['user'] = r1.ru_utime - r0.ru_utime  # approximate under threads
    return res


def one(llc, path, modes, extra):
    return path, {m: run(llc, path, m, extra) for m in modes}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--llc', required=True)
    ap.add_argument('--list', required=True)
    ap.add_argument('-o', required=True)
    ap.add_argument('-j', type=int, default=os.cpu_count())
    ap.add_argument('--modes', default='base,synth,egraph')
    ap.add_argument('--extra', default='')
    a = ap.parse_args()
    files = [l.strip() for l in open(a.list) if l.strip()]
    modes = a.modes.split(',')
    extra = a.extra.split() if a.extra else []
    res = {}
    with concurrent.futures.ThreadPoolExecutor(a.j) as ex:
        for path, r in ex.map(lambda f: one(a.llc, f, modes, extra), files):
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


if __name__ == '__main__':
    main()
