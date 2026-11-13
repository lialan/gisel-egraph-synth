#!/usr/bin/env python3
"""Compares two configurations of views_eval.py results, from one run or
from two (for example the same configuration with two builds of llc).

  views_diff.py A.json[:CONFIG] B.json[:CONFIG] [--top N]

CONFIG defaults to `all`. Only the files that compiled in every
configuration of both runs, with the same SelectionDAG fallbacks, are
compared (the set that views_eval.py compares); with --pairwise, the files
that compiled in A and B with the same fallbacks. It prints the totals of A and B
(instructions, code bytes, registers), the number of files where B is
better or worse, the largest changes per file and the change of each
counted mnemonic.
"""

import argparse
import collections
import json
import sys

KEYS = ('insns', 'code_bytes', 'sgpr', 'vgpr')


def load(spec):
    """The results of one configuration per file, and the files whose
    configurations of that run all compiled with the same fallbacks."""
    path, _, config = spec.partition(':')
    with open(path) as f:
        data = json.load(f)
    config = config or 'all'
    files, uniform = {}, {}
    for rel, by_config in data['files'].items():
        if config not in by_config:
            raise SystemExit('%s has no configuration %s (it has %s)' %
                             (path, config, ', '.join(sorted(by_config))))
        files[rel] = by_config[config]
        rs = by_config.values()
        if all(r['rc'] == 0 for r in rs) and \
                len({tuple(r['fallback']) for r in rs}) == 1:
            uniform[rel] = tuple(files[rel]['fallback'])
    return files, uniform


def compare(a, b, pairwise=False):
    """The comparable files and their per-file and total changes. a
    and b are results of load()."""
    (a, ua), (b, ub) = a, b
    if pairwise:
        common = [p for p in sorted(set(a) & set(b))
                  if a[p]['rc'] == 0 and b[p]['rc'] == 0 and
                  a[p]['fallback'] == b[p]['fallback']]
    else:
        common = [p for p in sorted(set(ua) & set(ub)) if ua[p] == ub[p]]
    tot = {'a': collections.Counter(), 'b': collections.Counter()}
    mn = {'a': collections.Counter(), 'b': collections.Counter()}
    delta = {}
    for p in common:
        for side, r in (('a', a[p]), ('b', b[p])):
            for k in KEYS:
                tot[side][k] += r[k]
            mn[side].update(r.get('mnemonics', {}))
        delta[p] = (b[p]['insns'] - a[p]['insns'],
                    b[p]['code_bytes'] - a[p]['code_bytes'])
    return {'files': common, 'totals': tot, 'mnemonics': mn,
            'delta': delta,
            'better': sum(1 for d in delta.values() if d[0] < 0),
            'worse': sum(1 for d in delta.values() if d[0] > 0)}


def report(c, a_name, b_name, top, out=sys.stdout):
    ta, tb = c['totals']['a'], c['totals']['b']
    print('A = %s, B = %s; comparable files: %d' %
          (a_name, b_name, len(c['files'])), file=out)
    print('%-6s' % '' + ''.join('%14s' % k for k in KEYS), file=out)
    for name, t in (('A', ta), ('B', tb)):
        print('%-6s' % name + ''.join('%14d' % t[k] for k in KEYS), file=out)
    print('%-6s' % 'B - A' + ''.join('%+14d' % (tb[k] - ta[k])
                                     for k in KEYS), file=out)
    print('B better in %d files, worse in %d' % (c['better'], c['worse']),
          file=out)
    ranked = sorted(c['delta'].items(), key=lambda kv: (kv[1][0], kv[0]))
    gains = [kv for kv in ranked if kv[1][0] < 0][:top]
    losses = [kv for kv in reversed(ranked) if kv[1][0] > 0][:top]
    for title, rows in (('largest gains', gains), ('largest losses', losses)):
        if rows:
            print('%s (instructions, bytes):' % title, file=out)
            for p, (di, db) in rows:
                print('  %+6d %+7d  %s' % (di, db, p), file=out)
    ma, mb = c['mnemonics']['a'], c['mnemonics']['b']
    changed = {m: mb[m] - ma[m] for m in sorted(set(ma) | set(mb))
               if mb[m] != ma[m]}
    if changed:
        print('mnemonics B - A: %s' % json.dumps(changed), file=out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('a', help='A.json[:CONFIG]')
    ap.add_argument('b', help='B.json[:CONFIG]')
    ap.add_argument('--top', type=int, default=10)
    ap.add_argument('--pairwise', action='store_true',
                    help='compare every file that A and B both compiled')
    args = ap.parse_args()
    report(compare(load(args.a), load(args.b), args.pairwise), args.a,
           args.b, args.top)


if __name__ == '__main__':
    main()
