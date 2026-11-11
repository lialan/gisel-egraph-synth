#!/usr/bin/env python3
"""Writes a corpus manifest: the .ll files of some directories that the
baseline pipeline of a target compiles, and in which GlobalISel itself
compiled at least one function.

The filter uses only the compiler without the synthesized rules, so a
manifest does not depend on a rule and can be a held-out set.

  make_manifest.py --llc BUILD/bin/llc -o OUT.txt [--target AMDGPU]
                   [--exclude MANIFEST...] DIR...

Paths are relative to the root of the repository (the working directory).
"""

import argparse
import concurrent.futures
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

from girs import measure, targets  # noqa: E402

DEFINE = re.compile(r'^define\b', re.M)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--llc', required=True)
    ap.add_argument('-o', required=True)
    ap.add_argument('--target', default='AMDGPU')
    ap.add_argument('--exclude', nargs='*', default=[])
    ap.add_argument('-j', type=int, default=os.cpu_count())
    ap.add_argument('dirs', nargs='+')
    a = ap.parse_args()
    target = targets.get(a.target)
    skip = set()
    for m in a.exclude:
        skip |= {l.strip() for l in open(m) if l.strip()}
    files = sorted(os.path.join(d, f) for d in a.dirs
                   for f in os.listdir(d) if f.endswith('.ll'))
    files = [f for f in files if f not in skip]

    def one(path):
        with open(path, errors='replace') as f:
            defs = len(DEFINE.findall(f.read()))
        if not defs:
            return path, 'no function'
        res = measure.compile_ll(a.llc, target, path)
        if res['rc']:
            return path, 'does not compile'
        if len(res['fallback']) >= defs or not res['insns']:
            return path, 'no function compiled by GlobalISel'
        return path, None
    keep, why = [], {}
    with concurrent.futures.ThreadPoolExecutor(a.j) as ex:
        for path, r in ex.map(one, files):
            if r is None:
                keep.append(path)
            else:
                why[r] = why.get(r, 0) + 1
    with open(a.o, 'w') as f:
        f.write(''.join(p + '\n' for p in keep))
    print('%d of %d files; left out: %s' % (len(keep), len(files), why))


if __name__ == '__main__':
    main()
