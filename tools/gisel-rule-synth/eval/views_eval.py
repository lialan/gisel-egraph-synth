#!/usr/bin/env python3
"""Compares the e-graph combiner with and without its target-aware
features (docs/TargetAwareViews.md) on a fixed list of .ll files, and both
with the stock GlobalISel pipeline.

Configurations (all with -global-isel -verify-machineinstrs and the
target's flags of girs/targets.py, AMDGPU gfx1100 by default):

  stock    the stock pipeline (no e-graph pass)
  none     + -amdgpu-gisel-egraph -gisel-egraph-mode=rewrite
             -gisel-egraph-features=none (the engine without the features)
  all      + the e-graph pass with all features (the default)
  no-X     all features but X (facts, linear, slice, tuples, patterns,
           banks, dag), for ablations

Per file and configuration it records: the instruction count of the
assembly, the encoded code size (sum of `; codeLenInByte`), SGPRs and
VGPRs, the counts of a few instructions (moves and copies between banks,
v_add3_u32, bit-field extracts, carry adds), the CPU time, the functions
that fell back to SelectionDAG, and the -stats counters of the e-graph pass
(an assertions build has them). A file whose fallback set differs between
configurations is not comparable and is reported separately.

The instruction count and the code size are static measures of the
generated code; nothing here runs the code.

  views_eval.py --llc build/plugin/bin/llc --list FILES -o OUT.json
                [--root DIR] [--configs stock,none,all] [--mcpu gfx1100]
                [-j N]
"""

import argparse
import collections
import concurrent.futures
import json
import os
import re
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

from girs import measure, paths, targets  # noqa: E402

EGRAPH = ['-amdgpu-gisel-egraph', '-gisel-egraph-mode=rewrite']
FEATURES = ('facts', 'linear', 'slice', 'tuples', 'patterns', 'banks', 'dag')
CODE_LEN = re.compile(r';\s*codeLenInByte\s*=\s*(\d+)')
# Instructions counted by mnemonic: moves (a COPY between banks or of a
# constant), the fused add, bit-field extracts, adds with a carry.
MNEMONICS = ('v_mov_b32', 's_mov_b32', 'v_readfirstlane_b32', 'v_add3_u32',
             'v_bfe_u32', 'v_bfe_i32', 's_bfe_u32', 's_bfe_i32',
             'v_add_co_u32', 'v_add_nc_u32', 'v_add_u32', 's_add_i32',
             's_add_u32', 'v_lshl_add_u32', 'v_mad_u32_u24', 'v_mul_lo_u32',
             's_mul_i32', 'v_lshlrev_b32', 'v_and_b32', 'v_or_b32',
             'v_cndmask_b32', 'v_cmp_gt_u32', 'v_cmp_lt_u32')
STAT = re.compile(r'^\s*(\d+)\s+(\S+)\s+-\s+(.*)$', re.M)


def flags_of(config):
    if config == 'stock':
        return []
    if config == 'none':
        return EGRAPH + ['-gisel-egraph-features=none']
    if config == 'all':
        return list(EGRAPH)
    if config.startswith('no-') and config[3:] in FEATURES:
        return EGRAPH + ['-gisel-egraph-features=all,' + config]
    raise SystemExit('unknown configuration ' + config)


def compile_one(llc, target, mcpu, path, config, timeout):
    with tempfile.NamedTemporaryFile(suffix='.s', delete=False) as tf:
        out = tf.name
    ll_flags = [f for f in target.ll_flags if not f.startswith('-mcpu=')]
    if mcpu:
        ll_flags.append('-mcpu=' + mcpu)
    cmd = ([llc] + ll_flags + ['-verify-machineinstrs', '-stats'] +
           flags_of(config) + [path, '-o', out])
    rc, stderr, cpu = measure.run_timed(cmd, timeout)
    res = {'rc': rc, 'user': cpu,
           'fallback': sorted(set(measure.FALLBACK.findall(stderr)))}
    if rc == 0:
        with open(out) as f:
            s = f.read()
        code = [l.split(';')[0] for l in s.splitlines()]
        # Mnemonics without the encoding suffix (v_add_nc_u32_e32).
        words = collections.Counter(
            re.sub(r'_(e32|e64|vop3|sdwa|dpp)$', '', l.split()[0])
            for l in code if l.strip() and l.startswith('\t'))
        res.update(
            insns=len(re.findall(target.insn_regex, s, re.M)),
            code_bytes=sum(map(int, CODE_LEN.findall(s))),
            sgpr=sum(map(int, measure.SGPR.findall(s))),
            vgpr=sum(map(int, measure.VGPR.findall(s))),
            mnemonics={m: words[m] for m in MNEMONICS if words[m]})
        stats = {}
        for n, group, desc in STAT.findall(stderr):
            if group == 'gisel-egraph':
                stats[desc.strip()] = stats.get(desc.strip(), 0) + int(n)
        if stats:
            res['stats'] = stats
    else:
        res['err'] = stderr[-400:]
    if os.path.exists(out):
        os.remove(out)
    return res


def summarize(res, configs, out=sys.stdout):
    comparable = [p for p, r in res.items()
                  if all(r[c]['rc'] == 0 for c in configs) and
                  len({tuple(r[c]['fallback']) for c in configs}) == 1]
    failed = {c: sorted(p for p, r in res.items() if r[c]['rc'] != 0)
              for c in configs}
    print('files: %d, comparable: %d' % (len(res), len(comparable)),
          file=out)
    for c in configs:
        if failed[c]:
            print('  %s: %d failed compilations' % (c, len(failed[c])),
                  file=out)
    base = configs[0]
    tot = {c: collections.Counter() for c in configs}
    for p in comparable:
        for c in configs:
            r = res[p][c]
            for k in ('insns', 'code_bytes', 'sgpr', 'vgpr'):
                tot[c][k] += r[k]
            tot[c]['user'] += r['user']
            for m, n in r.get('mnemonics', {}).items():
                tot[c]['#' + m] += n
    keys = ['insns', 'code_bytes', 'sgpr', 'vgpr', 'user']
    print('%-10s' % 'config' + ''.join('%14s' % k for k in keys), file=out)
    for c in configs:
        print('%-10s' % c + ''.join(
            ('%14.1f' if k == 'user' else '%14d') % tot[c][k] for k in keys),
            file=out)
    for c in configs[1:]:
        better = sum(1 for p in comparable
                     if res[p][c]['insns'] < res[p][base]['insns'])
        worse = sum(1 for p in comparable
                    if res[p][c]['insns'] > res[p][base]['insns'])
        print('%s vs %s: %+d instructions, %+d code bytes; %d files better, '
              '%d worse' % (c, base, tot[c]['insns'] - tot[base]['insns'],
                            tot[c]['code_bytes'] - tot[base]['code_bytes'],
                            better, worse), file=out)
    for c in configs:
        mn = {k[1:]: v for k, v in sorted(tot[c].items()) if k[0] == '#'}
        print('%s mnemonics: %s' % (c, json.dumps(mn)), file=out)
    for c in configs:
        st = collections.Counter()
        for p in comparable:
            st.update(res[p][c].get('stats', {}))
        if st:
            print('%s e-graph stats: %s' % (c, json.dumps(dict(sorted(
                st.items())))), file=out)
    return comparable


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--llc', required=True)
    ap.add_argument('--list', required=True)
    ap.add_argument('-o', required=True)
    ap.add_argument('--root', default=paths.LLVM_ROOT,
                    help='directory of the relative paths of the list')
    ap.add_argument('--configs', default='stock,none,all')
    ap.add_argument('--target', default='AMDGPU')
    ap.add_argument('--mcpu', default='')
    ap.add_argument('--timeout', type=int, default=measure.TIMEOUT)
    ap.add_argument('-j', type=int, default=os.cpu_count())
    a = ap.parse_args()
    target = targets.get(a.target)
    files = [l.strip() for l in open(a.list)
             if l.strip() and not l.startswith('#')]
    configs = a.configs.split(',')
    llc = os.path.abspath(a.llc)

    def one(rel):
        path = rel if os.path.isabs(rel) else os.path.join(a.root, rel)
        return rel, {c: compile_one(llc, target, a.mcpu, path, c, a.timeout)
                     for c in configs}
    res = {}
    with concurrent.futures.ThreadPoolExecutor(a.j) as ex:
        for rel, r in ex.map(one, files):
            res[rel] = r
    with open(a.o, 'w') as f:
        json.dump({'llc': llc, 'mcpu': a.mcpu, 'configs': configs,
                   'files': res}, f, indent=0, sort_keys=True)
    summarize(res, configs)


if __name__ == '__main__':
    main()
