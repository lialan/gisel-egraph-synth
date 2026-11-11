#!/usr/bin/env python3
"""Classifies each emitted rule against the existing AMDGPU pre-legalizer
combiner.

For every rule, a MIR function is built from the rule's source pattern and
the known bits of its first training example. Each input's facts are
realized with real instructions that GISelValueTracking reads back exactly:

    x = G_OR (G_AND arg, ~KnownZero), KnownOne

(inputs whose bits are all known become a G_CONSTANT). The function is run
through -run-pass=amdgpu-prelegalizer-combiner with and without
-amdgpu-gisel-synth-combines and the remaining generic instructions are
counted. Classification:

    covered     the existing combiner reaches the same count
    new         only the synthesized rules reduce the count
    not_fired   neither changes the source (the rule did not apply here)
    worse       the synthesized rules leave more instructions

  baseline.py --llc BUILD/bin/llc --db rules.json [-o out.json]
"""

import argparse
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

from girs import emit, ir  # noqa: E402

LLC = ['-mtriple=amdgcn-amd-amdhsa', '-mcpu=gfx1100',
       '-run-pass=amdgpu-prelegalizer-combiner', '-verify-machineinstrs']


class Fn:
    def __init__(self):
        self.lines = []
        self.n = 0
        self.vgpr = 0

    def reg(self):
        self.n += 1
        return '%%%d' % (self.n - 1)

    def emit(self, w, rhs):
        r = self.reg()
        self.lines.append('    %s:_(s%d) = %s' % (r, w, rhs))
        return r

    def arg(self, w):
        if w > 32:
            phys = '$vgpr%d_vgpr%d' % (self.vgpr, self.vgpr + 1)
            self.vgpr += 2
            return self.emit(w, 'COPY ' + phys), phys
        phys = '$vgpr%d' % self.vgpr
        self.vgpr += 1
        r = self.emit(32, 'COPY ' + phys)
        if w < 32:
            r = self.emit(w, 'G_TRUNC %s' % r)
        return r, phys


def build(rule, name):
    src = ir.from_json(rule['source_json'])
    vw = rule['support']['example_vw']
    facts = [(int(z, 16), int(o, 16))
             for z, o in rule['support']['example_facts']]
    fn = Fn()
    xs, live = [], []
    for w, (z, o) in zip(vw, facts):
        m = ir.mask(w)
        if (z | o) == m:
            xs.append(fn.emit(w, 'G_CONSTANT i%d %d' % (w, o)))
            continue
        r, phys = fn.arg(w)
        live.append(phys)
        if z:
            c = fn.emit(w, 'G_CONSTANT i%d %d' % (w, ~z & m))
            r = fn.emit(w, 'G_AND %s, %s' % (r, c))
        if o:
            c = fn.emit(w, 'G_CONSTANT i%d %d' % (w, o))
            r = fn.emit(w, 'G_OR %s, %s' % (r, c))
        xs.append(r)
    marker = fn.n

    def walk(e):
        if ir.is_var(e):
            return xs[e[1]]
        args = [walk(a) for a in e[2:]]
        return fn.emit(e[1], '%s %s' % (e[0], ', '.join(args)))
    root = walk(src)
    w = src[1]
    if w < 32:
        root = fn.emit(32, 'G_ANYEXT %s' % root)
        w = 32
    out = '$vgpr0' if w == 32 else '$vgpr0_vgpr1'
    body = ['---', 'name: %s' % name, 'tracksRegLiveness: true', 'body: |',
            '  bb.0:']
    if live:
        body.append('    liveins: ' + ', '.join(live))
    body += fn.lines + ['    %s = COPY %s' % (out, root),
                        '    SI_RETURN implicit %s' % out, '...']
    return '\n'.join(body), marker


def count(mir_out):
    """Generic instructions other than copies / constants / extensions of
    the result, per function."""
    res, name = {}, None
    for l in mir_out.splitlines():
        if l.startswith('name:'):
            name = l.split()[1]
            res[name] = 0
        m = re.match(r'\s+%\d+:_\(\S+\) = (G_\w+)', l)
        if m and name and m.group(1) not in ('G_CONSTANT', 'G_ANYEXT',
                                             'G_TRUNC', 'G_IMPLICIT_DEF'):
            res[name] += 1
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--llc', required=True)
    ap.add_argument('--db', required=True)
    ap.add_argument('-o')
    ap.add_argument('--keep', help='write the generated MIR here')
    a = ap.parse_args()
    db = json.load(open(a.db))
    rules = emit.emitted_rules(db)
    fns = []
    for r in rules:
        text, _ = build(r, r['id'])
        fns.append(text)
    mir = '\n'.join(fns) + '\n'
    path = a.keep or '/dev/stdin'
    if a.keep:
        open(a.keep, 'w').write(mir)
    outs = {}
    for mode, extra in (('base', []), ('synth',
                                       ['-amdgpu-gisel-synth-combines'])):
        p = subprocess.run([a.llc] + LLC + extra + ['-x', 'mir', '-', '-o',
                                                    '-'],
                           input=mir, capture_output=True, text=True)
        if p.returncode:
            sys.exit('llc failed (%s):\n%s' % (mode, p.stderr[-2000:]))
        outs[mode] = count(p.stdout)
    src = count(mir)
    result = {}
    tally = {}
    for r in rules:
        s, b, n = src[r['id']], outs['base'][r['id']], outs['synth'][r['id']]
        if n < b:
            c = 'new'
        elif n > b:
            c = 'worse'
        elif b < s:
            c = 'covered'
        else:
            c = 'not_fired'
        tally[c] = tally.get(c, 0) + 1
        result[r['id']] = {'class': c, 'source_insns': s, 'base': b,
                           'synth': n, 'rule': '%s -> %s if %s' % (
                               r['source'], r['replacement'],
                               r['precondition'])}
        print('%-10s %d->%d/%d  %s' % (c, s, b, n, result[r['id']]['rule']))
    print(tally)
    if a.o:
        json.dump(result, open(a.o, 'w'), indent=1, sort_keys=True)


if __name__ == '__main__':
    main()
