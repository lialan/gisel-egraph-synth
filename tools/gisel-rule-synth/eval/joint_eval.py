#!/usr/bin/env python3
"""A/B measurement of the joint region rules on a corpus.

Each .ll file of a manifest is compiled twice by the same llc (this
project's): without and with -gisel-synth-joint-combines, with the flags
of the target (-O2 -global-isel -global-isel-abort=2) and
-verify-machineinstrs. The second run also has -debug-only=gisel-synth-joint,
so the matcher reports, per rule, each anchor it looked at, each rejection
(by stage: pattern, boundary, defined, width, placement, fanout, trials,
types, distance) and each application.

Files are deduplicated by content; a file whose content is also in one of
the --exclude manifests (the training and validation sets) is not measured.

Writes <out>/files.jsonl (one record per file) and <out>/summary.json: the
files that compile in both runs, new failures, fallback changes, the
instruction counts, the files that get smaller or larger, the rules that
applied, the rejection counts (the match rate) and the CPU time of the
compilations with and without the rules. Static instruction counts are
not a run-time measurement.

  joint_eval.py --llc build/plugin/bin/llc --manifest M --root R --out D
      [--exclude M2 ...] [--disable rule,...] [-j N]
"""

import argparse
import collections
import concurrent.futures
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

from girs import measure  # noqa: E402
from girs import targets  # noqa: E402

DEBUG = re.compile(r'gisel-synth-joint: ([a-z ]+): (\w+)')
FALLBACK = re.compile(r'Instruction selection used fallback path for (\S+)')


def compile_one(llc, target, path, joint, disable=(), timeout=180,
                debug=False):
    with tempfile.NamedTemporaryFile(suffix='.s', delete=False) as tf:
        out = tf.name
    cmd = [llc] + target.ll_flags + ['-verify-machineinstrs']
    if joint:
        cmd += ['-gisel-synth-joint-combines']
        if debug:
            cmd.append('-debug-only=gisel-synth-joint')
        if disable:
            cmd.append('--gisynthjointcombiner-disable-rule=' +
                       ','.join(disable))
    cmd += [path, '-o', out]
    rc, err, cpu = measure.run_timed(cmd, timeout)
    res = {'rc': rc, 'cpu': round(cpu, 4),
           'fallback': sorted(set(FALLBACK.findall(err)))}
    if debug:
        c = collections.Counter('%s|%s' % m for m in DEBUG.findall(err))
        res['joint'] = dict(sorted(c.items()))
    if rc == 0:
        with open(out) as f:
            s = f.read()
        res['insns'] = len(re.findall(target.insn_regex, s, re.M))
    else:
        res['err'] = err[-300:]
    if os.path.exists(out):
        os.remove(out)
    return res


def read_manifest(path, root):
    with open(path) as f:
        return [os.path.join(root, l.strip()) for l in f if l.strip()]


def digest(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--llc', required=True)
    ap.add_argument('--target', default='AMDGPU')
    ap.add_argument('--manifest', action='append', required=True)
    ap.add_argument('--root', required=True)
    ap.add_argument('--exclude', action='append', default=[],
                    help='manifests whose file contents are not measured')
    ap.add_argument('--disable', default='', help='rules to disable')
    ap.add_argument('--out', required=True)
    ap.add_argument('-j', type=int, default=os.cpu_count())
    ap.add_argument('--limit', type=int, default=0)
    args = ap.parse_args()
    target = targets.get(args.target)
    os.makedirs(args.out, exist_ok=True)
    files = []
    for m in args.manifest:
        files += read_manifest(m, args.root)
    excluded = set()
    for m in args.exclude:
        for p in read_manifest(m, args.root):
            if os.path.exists(p):
                excluded.add(digest(p))
    seen, todo, dup, overlap = set(), [], 0, 0
    for p in files:
        if not os.path.exists(p):
            continue
        d = digest(p)
        if d in excluded:
            overlap += 1
            continue
        if d in seen:
            dup += 1
            continue
        seen.add(d)
        todo.append(p)
    if args.limit:
        todo = todo[:args.limit]
    disable = [x for x in args.disable.split(',') if x]

    def job(p):
        off = compile_one(args.llc, target, p, False)
        on = compile_one(args.llc, target, p, True, disable)
        dbg = compile_one(args.llc, target, p, True, disable, debug=True)
        # The counters of the matcher come from a run with debug output; it
        # must give the same code.
        on['joint'] = dbg.get('joint', {})
        on['debug_run_same_insns'] = dbg.get('insns') == on.get('insns')
        return p, off, on
    recs = []
    with concurrent.futures.ThreadPoolExecutor(args.j) as ex:
        for p, off, on in ex.map(job, todo):
            recs.append({'file': os.path.relpath(p, args.root),
                         'off': off, 'on': on})
    with open(os.path.join(args.out, 'files.jsonl'), 'w') as f:
        for r in recs:
            f.write(json.dumps(r) + '\n')
    both = [r for r in recs if r['off']['rc'] == 0 and r['on']['rc'] == 0]
    new_fail = [r['file'] for r in recs
                if r['off']['rc'] == 0 and r['on']['rc'] != 0]
    fb = [r['file'] for r in both
          if r['off']['fallback'] != r['on']['fallback']]
    smaller = [r for r in both if r['on']['insns'] < r['off']['insns']]
    larger = [r for r in both if r['on']['insns'] > r['off']['insns']]
    per_rule = collections.defaultdict(collections.Counter)
    files_of_rule = collections.defaultdict(list)
    for r in recs:
        for k, v in r['on'].get('joint', {}).items():
            stage, rule = k.split('|')
            per_rule[rule][stage] += v
            if stage == 'applied':
                files_of_rule[rule].append(r['file'])
    gain_of_rule = {}
    for rule, fs in files_of_rule.items():
        fs = set(fs)
        d = [r['off']['insns'] - r['on']['insns'] for r in both
             if r['file'] in fs]
        gain_of_rule[rule] = {'files': len(fs), 'insns_saved': sum(d),
                              'files_smaller': sum(x > 0 for x in d),
                              'files_larger': sum(x < 0 for x in d)}
    total = collections.Counter()
    for c in per_rule.values():
        total.update(c)
    summary = {
        'manifests': args.manifest, 'excluded_manifests': args.exclude,
        'files_listed': len(files), 'duplicate_content': dup,
        'content_in_excluded_sets': overlap, 'measured': len(todo),
        'compiled_both': len(both),
        'failed_without_rules': sum(r['off']['rc'] != 0 for r in recs),
        'new_failures': new_fail, 'fallback_changes': fb,
        'insns_without': sum(r['off']['insns'] for r in both),
        'insns_with': sum(r['on']['insns'] for r in both),
        'files_smaller': len(smaller), 'files_larger': len(larger),
        'larger': [(r['file'], r['off']['insns'], r['on']['insns'])
                   for r in larger],
        'smaller': [(r['file'], r['off']['insns'], r['on']['insns'])
                    for r in smaller],
        'matcher': dict(total),
        'per_rule': {k: dict(v) for k, v in sorted(per_rule.items())},
        'applied_rules': gain_of_rule,
        'cpu_without_s': round(sum(r['off']['cpu'] for r in both), 2),
        'cpu_with_s': round(sum(r['on']['cpu'] for r in both), 2),
        'disabled': disable,
        'llc_sha256': digest(args.llc),
    }
    summary['debug_run_differs'] = [r['file'] for r in both
                                    if not r['on']['debug_run_same_insns']]
    summary['note'] = ('cpu: the runs without debug output; static '
                       'instruction counts, not run time')
    with open(os.path.join(args.out, 'summary.json'), 'w') as f:
        json.dump(summary, f, indent=1)
    print(json.dumps({k: summary[k] for k in (
        'measured', 'compiled_both', 'new_failures', 'fallback_changes',
        'insns_without', 'insns_with', 'files_smaller', 'files_larger',
        'matcher', 'cpu_without_s', 'cpu_with_s')}, indent=1))


if __name__ == '__main__':
    main()
