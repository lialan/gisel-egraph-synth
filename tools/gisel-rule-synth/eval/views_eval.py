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
  f:X+Y    exactly the features X and Y (f: alone is the same as none), to
           measure combinations directly: an ablation hides features that
           only pay off together

`--define 'NAME=BASE FLAG...'` (repeatable) names a configuration that is
BASE (one of the above) with extra llc flags, e.g. an experimental switch:
`--define 'ordis=all -gisel-egraph-or-disjoint-to-add' --configs all,ordis`.

Per file and configuration it records: the instruction count of the
assembly (and how many of them are scheduling and wait hints: s_delay_alu,
s_waitcnt*, s_nop, s_clause, s_set_inst_prefetch_distance), the encoded
code size (sum of `; codeLenInByte`), SGPRs and
VGPRs, the counts of a few instructions (moves and copies between banks,
v_add3_u32, bit-field extracts, carry adds), the CPU time and the peak
resident set size of llc, the functions
that fell back to SelectionDAG, and the -stats counters of the e-graph pass
(an assertions build has them). A file whose fallback set differs between
configurations is not comparable and is reported separately.

With --time-passes it also records the timers of the e-graph pass
(-time-passes: building, saturating, extracting and rewriting, the
uniformity analysis computed again after a rewrite) and the time of the
pass itself, in seconds per file.

The instruction count and the code size are static measures of the
generated code; nothing here runs the code.

  views_eval.py --llc build/plugin/bin/llc --list FILES -o OUT.json
                [--root DIR] [--configs stock,none,all] [--mcpu gfx1100]
                [--define 'NAME=BASE FLAG...'] [--time-passes] [-j N]
"""

import argparse
import collections
import concurrent.futures
import json
import os
import re
import shlex
import subprocess
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
# Scheduling and wait hints: counted in insns (the target's instruction
# pattern), and also on their own (hints), since they come from the
# scheduler and the hazard recognizer rather than the selected code.
HINTS = ('s_delay_alu', 's_nop', 's_clause', 's_set_inst_prefetch_distance')
STAT = re.compile(r'^\s*(\d+)\s+(\S+)\s+-\s+(.*)$', re.M)
# -time-passes: the title of a timer group, and a row of times
# ("0.0123 ( 45.6%)" per column) followed by the name of the timer.
TIMER_TITLE = re.compile(r'^\s{2,}(\S.*\S)\s*\n=+-+=+\s*$', re.M)
TIMER_COLUMN = re.compile(r'(\d+\.\d+)\s+\(\s*[\d.]+%\)')
EGRAPH_TIMERS = ('GlobalISel e-graph combiner',
                 'GlobalISel e-graph combiner analyses')
# The pass in the report of the legacy pass manager: one row per instance
# (before and after the legalizer), 'GIEGraphCombiner #2' for the second.
EGRAPH_PASS = re.compile(r'^GIEGraphCombiner(?: #\d+)?$')


def flags_of(config, defines=None):
    if defines and config in defines:
        base, extra = defines[config]
        return flags_of(base) + extra
    if config == 'stock':
        return []
    if config == 'none':
        return EGRAPH + ['-gisel-egraph-features=none']
    if config == 'all':
        return list(EGRAPH)
    if config.startswith('no-') and config[3:] in FEATURES:
        return EGRAPH + ['-gisel-egraph-features=all,' + config]
    if config.startswith('f:'):
        feats = [f for f in config[2:].split('+') if f]
        bad = [f for f in feats if f not in FEATURES]
        if bad:
            raise SystemExit('unknown feature %s in %s' % (bad[0], config))
        return EGRAPH + ['-gisel-egraph-features=' + ','.join(['none'] +
                                                              feats)]
    raise SystemExit('unknown configuration ' + config)


def parse_defines(specs):
    """--define 'NAME=BASE FLAG...' -> {NAME: (BASE, [FLAG...])}."""
    defines = {}
    for spec in specs:
        name, _, rest = spec.partition('=')
        words = shlex.split(rest)
        if not name or not words:
            raise SystemExit('--define: expected NAME=BASE FLAG..., got ' +
                             spec)
        flags_of(words[0])  # The base must be a known configuration.
        defines[name] = (words[0], words[1:])
    return defines


def parse_timers(stderr):
    """The e-graph timers of -time-passes output, in seconds of process
    time (user + system; wall time if that is all there is): the phases
    of the pass (build, saturate, extract and rewrite), the uniformity
    analysis (computed again after each rewrite; it runs inside those
    phases) and the pass itself from the report of the legacy pass manager
    ('pass')."""
    timers = {}
    titles = list(TIMER_TITLE.finditer(stderr))
    for i, m in enumerate(titles):
        end = titles[i + 1].start() if i + 1 < len(titles) else len(stderr)
        body = stderr[m.end():end]
        header = next((l for l in body.splitlines() if '--- Name ---' in l),
                      None)
        if header is None:
            continue
        cols = re.findall(r'-+\s*([A-Za-z+ ]+?)\s*-+', header)
        cols = [c.replace(' Time', '') for c in cols if c != 'Name']
        pick = (cols.index('User+System') if 'User+System' in cols else
                cols.index('Wall') if 'Wall' in cols else 0)
        for line in body.splitlines():
            times = TIMER_COLUMN.findall(line)
            if len(times) != len(cols):
                continue
            name = TIMER_COLUMN.sub('', line).strip()
            secs = float(times[pick])
            if m.group(1) in EGRAPH_TIMERS and name != 'Total':
                timers[name] = timers.get(name, 0.0) + secs
            elif EGRAPH_PASS.match(name):
                timers['pass'] = timers.get('pass', 0.0) + secs
    return timers


def run(cmd, timeout):
    """measure.run_timed, with the peak resident set size (KiB) of the
    compilation: wait4 reports the largest of the processes it waited for,
    i.e. llc under `timeout`."""
    with tempfile.TemporaryFile() as err:
        p = subprocess.Popen(['timeout', '-k', '5', str(timeout)] + cmd,
                             stdout=subprocess.DEVNULL, stderr=err)
        _, status, ru = os.wait4(p.pid, 0)
        rc = os.waitstatus_to_exitcode(status)
        p.returncode = rc
        err.seek(0)
        text = err.read().decode(errors='replace')
    if rc in (124, 137):
        rc = -1
    return rc, text, ru.ru_utime + ru.ru_stime, ru.ru_maxrss


def compile_one(llc, target, mcpu, path, config, timeout, defines=None,
                time_passes=False):
    with tempfile.NamedTemporaryFile(suffix='.s', delete=False) as tf:
        out = tf.name
    # The CPU of the target (gfx1100 for AMDGPU) unless --mcpu is given.
    ll_flags = list(target.ll_flags)
    if mcpu:
        ll_flags = [f for f in ll_flags if not f.startswith('-mcpu=')]
        ll_flags.append('-mcpu=' + mcpu)
    cmd = ([llc] + ll_flags + ['-verify-machineinstrs', '-stats'] +
           (['-time-passes'] if time_passes else []) +
           flags_of(config, defines) + [path, '-o', out])
    rc, stderr, cpu, rss = run(cmd, timeout)
    res = {'rc': rc, 'user': cpu, 'rss_kib': rss,
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
            hints=sum(n for m, n in words.items()
                      if m in HINTS or m.startswith('s_waitcnt')),
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
        if time_passes:
            res['timers'] = parse_timers(stderr)
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
            tot[c]['max_rss_mib'] = max(tot[c]['max_rss_mib'],
                                        r.get('rss_kib', 0) // 1024)
            for m, n in r.get('mnemonics', {}).items():
                tot[c]['#' + m] += n
    for p in comparable:
        for c in configs:
            tot[c]['hints'] += res[p][c].get('hints', 0)
    keys = ['insns', 'hints', 'code_bytes', 'sgpr', 'vgpr', 'user',
            'max_rss_mib']
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
        def real(p, cfg):
            return res[p][cfg]['insns'] - res[p][cfg].get('hints', 0)
        rbetter = sum(1 for p in comparable if real(p, c) < real(p, base))
        rworse = sum(1 for p in comparable if real(p, c) > real(p, base))
        print('%s vs %s: %+d instructions, %+d code bytes; %d files better, '
              '%d worse; without hints %+d, %d files better, %d worse' % (
                  c, base, tot[c]['insns'] - tot[base]['insns'],
                  tot[c]['code_bytes'] - tot[base]['code_bytes'],
                  better, worse,
                  (tot[c]['insns'] - tot[c]['hints']) -
                  (tot[base]['insns'] - tot[base]['hints']),
                  rbetter, rworse), file=out)
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
    for c in configs:
        tm = collections.Counter()
        for p in comparable:
            tm.update(res[p][c].get('timers', {}))
        if tm:
            print('%s e-graph timers (s): %s' % (c, json.dumps(
                {k: round(v, 3) for k, v in sorted(tm.items())})), file=out)
    return comparable


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--llc', required=True)
    ap.add_argument('--list', required=True)
    ap.add_argument('-o', required=True)
    ap.add_argument('--root', default=paths.LLVM_ROOT,
                    help='directory of the relative paths of the list')
    ap.add_argument('--configs', default='stock,none,all')
    ap.add_argument('--define', action='append', default=[],
                    metavar='NAME=BASE FLAG...',
                    help='a configuration BASE with extra llc flags')
    ap.add_argument('--time-passes', action='store_true',
                    help='record the timers of the e-graph pass')
    ap.add_argument('--target', default='AMDGPU')
    ap.add_argument('--mcpu', default='')
    ap.add_argument('--timeout', type=int, default=measure.TIMEOUT)
    ap.add_argument('-j', type=int, default=os.cpu_count())
    a = ap.parse_args()
    target = targets.get(a.target)
    files = [l.strip() for l in open(a.list)
             if l.strip() and not l.startswith('#')]
    configs = a.configs.split(',')
    defines = parse_defines(a.define)
    for c in configs:
        flags_of(c, defines)  # Fail before compiling anything.
    llc = os.path.abspath(a.llc)

    def one(rel):
        path = rel if os.path.isabs(rel) else os.path.join(a.root, rel)
        return rel, {c: compile_one(llc, target, a.mcpu, path, c, a.timeout,
                                    defines, a.time_passes)
                     for c in configs}
    res = {}
    with concurrent.futures.ThreadPoolExecutor(a.j) as ex:
        for rel, r in ex.map(one, files):
            res[rel] = r
    with open(a.o, 'w') as f:
        json.dump({'llc': llc, 'mcpu': a.mcpu, 'configs': configs,
                   'defines': {k: [b] + e for k, (b, e) in defines.items()},
                   'files': res}, f, indent=0, sort_keys=True)
    summarize(res, configs)


if __name__ == '__main__':
    main()
