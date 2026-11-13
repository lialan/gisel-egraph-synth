#!/usr/bin/env python3
"""Measured selection of joint rules on top of a frozen baseline.

The llc must have every rule of --baseline and of --rules emitted
(`gi-rule-synth.py joint-emit --rules ALL.json`, the baseline rules first).
Every measurement compiles with the same llc, the same flags and
-verify-machineinstrs; a rule is switched off with
--gisynthjointcombiner-disable-rule, so that a configuration is exactly a
set of enabled rules:

  control    no joint combiner (-gisel-synth-joint-combines absent)
  baseline   the frozen rules of --baseline only (the existing selection)
  screen     read-only matches, plus a screen that allows only baseline
             rules to apply: candidates on their results are counted too,
             without candidates hiding each other or changing the MIR
  solo X     baseline + X, on the files where X screened: the marginal
             effect of X alone over the frozen baseline (no other candidate
             can take its place, and the gains of the baseline are not
             counted again)

Then, per window (one source pattern), the candidates are compared by
their solo effect, and a set is built greedily (largest solo gain first):
X joins the set S if baseline + S + X is better than baseline + S on the
files of X and on no file worse, and if S + X has no rewrite cycle
(joint.rewrite_cycles). The set is then refined with the leave-one-out of
girs/select.py inside the set, and validated with select.enforce: no file
of the corpus may be worse, fail or change its fallbacks against the
baseline.

The primary metric is the number of machine instructions; the encoded
bytes (codeLenInByte), SGPRs/VGPRs, spills, scratch and the CPU time of
the compilations are recorded too. These are static counts, not run time.

Each candidate gets a proof status (from its rule record) and a
profitability status:
  never_matched      no screened match in the corpus
  no_application     screened, but never applied over the baseline
  no_gain            applied; no instruction fewer in total
  regression         a file with more instructions, a new failure or a
                     changed fallback with the rule
  profitable         fewer instructions, no file worse
and, for the profitable ones, a selection status: selected,
dominated_in_window (another candidate of its window is better),
no_gain_in_set, cycle, final_set_violation.

  joint_measure.py --llc LLC --rules R.json --baseline B.json \\
      --manifest M --root ROOT [--exclude M2] --out DIR [-j N]
  joint_measure.py --llc LLC --evaluate ids --baseline B.json \\
      --manifest M --root ROOT --out DIR      (frozen set: held-out)

--evaluate measures control, baseline and baseline + ids on every file,
and selects nothing. Use it, once, on held-out data.
"""

import argparse
import collections
import copy
import json
import os
import re
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

from girs import joint, measure, select, targets  # noqa: E402

from girs.joint_measure import (  # noqa: E402
    METRIC_VERSION, METRICS, Measurer, sha_file, delta, solo_info, per_window,
    greedy, measure_candidates)


def joint_target(name):
    """The target with the combiner of the joint rules alone
    (measure.synth_flags, joint_only): measure.compile_ll and the functions
    of girs/select.py then enable, disable and count joint rules only. The
    flags are also here for eval/joint_case.py."""
    t = copy.copy(targets.get(name))
    t.joint_only = True
    t.enable_flag = '-gisel-synth-joint-combines'
    t.disable_rule_flag = '--gisynthjointcombiner-disable-rule='
    return t


def emitted_ids(td):
    with open(td) as f:
        return re.findall(r'^def (joint_\w+) : GICombineRule', f.read(), re.M)


def read_files(args):
    files = []
    for m in args.manifest:
        with open(m) as f:
            files += [os.path.join(args.root, l.strip()) for l in f
                      if l.strip()]
    excluded = set()
    for m in args.exclude:
        with open(m) as f:
            for l in f:
                p = os.path.join(args.root, l.strip())
                if l.strip() and os.path.exists(p):
                    excluded.add(sha_file(p))
    seen, out, info = set(), [], collections.Counter()
    for p in files:
        if not os.path.exists(p):
            info['missing'] += 1
            continue
        d = sha_file(p)
        if d in excluded:
            info['in_excluded_sets'] += 1
            continue
        if d in seen:
            info['duplicate_content'] += 1
            continue
        seen.add(d)
        out.append(p)
    if args.limit:
        out = out[:args.limit]
    info['measured'] = len(out)
    return out, dict(info)


def totals(results):
    t = collections.Counter()
    for r in results:
        if r.get('rc') == 0:
            for m in METRICS:
                t[m] += r.get(m, 0)
        t['cpu'] += r.get('user', 0)
    t['cpu'] = round(t['cpu'], 2)
    return dict(t)


def compare(a, b, files):
    """Totals over the files that compile in both, and the files that are
    smaller, larger, failing or with other fallbacks in b."""
    both = [p for p in files if a[p].get('rc') == 0 and b[p].get('rc') == 0]
    out = {'files': len(files), 'compiled_both': len(both),
           'a': totals(a[p] for p in both), 'b': totals(b[p] for p in both),
           'cpu_a': round(sum(a[p].get('user', 0) for p in files), 2),
           'cpu_b': round(sum(b[p].get('user', 0) for p in files), 2)}
    out['smaller'] = sorted((os.path.basename(p), a[p]['insns'],
                             b[p]['insns']) for p in both
                            if b[p]['insns'] < a[p]['insns'])
    out['larger'] = sorted((os.path.basename(p), a[p]['insns'],
                            b[p]['insns']) for p in both
                           if b[p]['insns'] > a[p]['insns'])
    out['new_failures'] = sorted(os.path.basename(p) for p in files
                                 if a[p].get('rc') == 0 and b[p].get('rc'))
    out['fallback_changes'] = sorted(
        os.path.basename(p) for p in both
        if a[p].get('fallback', []) != b[p].get('fallback', []))
    out['insns_delta'] = out['b'].get('insns', 0) - out['a'].get('insns', 0)
    out['code_bytes_delta'] = out['b'].get('code_bytes', 0) - \
        out['a'].get('code_bytes', 0)
    return out


def config_record(args, target, base_ids, extra):
    return dict({
        'llc': os.path.abspath(args.llc), 'llc_sha256': sha_file(args.llc),
        'target': target.name, 'llc_flags': target.ll_flags +
        ['-verify-machineinstrs'],
        'subtarget': [f for f in target.ll_flags if f.startswith('-mcpu')],
        'joint_flag': target.enable_flag,
        'pass_position': 'after the pre-legalizer combiner '
                         '(-gisel-synth-joint-combines)',
        'baseline_ids': base_ids, 'metric_version': METRIC_VERSION,
        'primary_metric': 'insns (static machine instructions)'}, **extra)


def evaluate(args, target, base_ids):
    """Control, baseline and baseline + ids on every file: the frozen
    evaluation of a selected set."""
    ids = [x for x in args.evaluate.split(',') if x]
    all_ids = emitted_ids(args.td)
    missing = [i for i in base_ids + ids if i not in all_ids]
    if missing:
        raise SystemExit('not in the llc (%s): %s' % (args.td, missing))
    files, finfo = read_files(args)
    M = Measurer(args.llc, target, all_ids, args.cache, args.j)
    ctl = dict(zip(files, M.many([(p, None, False, False) for p in files])))
    base = dict(zip(files, M.many([(p, base_ids, False, True)
                                   for p in files])))
    cur = dict(zip(files, M.many([(p, base_ids + ids, False, True)
                                  for p in files])))
    applied = collections.Counter()
    files_of = collections.defaultdict(list)
    for p in files:
        for rid, n in cur[p].get('passed', {}).items():
            applied[rid] += n
            files_of[rid].append(p)
    per_rule = {}
    for rid in ids:
        fs = files_of.get(rid, [])
        ds = [delta(base[p], cur[p]) for p in fs]
        ds = [d for d in ds if d]
        per_rule[rid] = {'files': len(fs), 'applied': applied[rid],
                         'insns_saved_in_files': -sum(d['insns'] for d in ds)}
    out = {'config': config_record(args, target, base_ids,
                                   {'evaluated_ids': ids}),
           'files': finfo,
           'baseline_vs_control': compare(ctl, base, files),
           'set_vs_baseline': compare(base, cur, files),
           'set_vs_control': compare(ctl, cur, files),
           'applied': dict(applied), 'per_rule': per_rule,
           'compiles': M.compiles, 'cache_hits': M.hits}
    with open(os.path.join(args.out, 'evaluation.json'), 'w') as f:
        json.dump(out, f, indent=1)
    s = out['set_vs_baseline']
    print('evaluate: %d files; set vs baseline: insns %+d, code bytes %+d, '
          '%d smaller, %d larger, %d new failures, %d fallback changes; '
          'cpu %.1f -> %.1f s' % (
              len(files), s['insns_delta'], s['code_bytes_delta'],
              len(s['smaller']), len(s['larger']), len(s['new_failures']),
              len(s['fallback_changes']), s['cpu_a'], s['cpu_b']))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument('--llc', required=True)
    ap.add_argument('--target', default='AMDGPU')
    ap.add_argument('--td', default=os.path.join(
        HERE, '..', '..', '..', 'td', 'GISynthJointCombines.td'),
        help='the generated rules that the llc was built with')
    ap.add_argument('--rules', help='rules.json of joint-search: the '
                    'candidates')
    ap.add_argument('--baseline', required=True,
                    help='rules.json of the frozen baseline rules')
    ap.add_argument('--evaluate', help='ids: evaluate baseline + ids only')
    ap.add_argument('--manifest', action='append', required=True)
    ap.add_argument('--root', required=True)
    ap.add_argument('--exclude', action='append', default=[])
    ap.add_argument('--out', required=True)
    ap.add_argument('--cache', help='JSON lines of compilations')
    ap.add_argument('--limit', type=int, default=0)
    ap.add_argument('-j', type=int, default=os.cpu_count())
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    args.cache = args.cache or os.path.join(args.out, 'compile-cache.jsonl')
    target = joint_target(args.target)
    with open(args.baseline) as f:
        base_rules = json.load(f)['rules']
    base_ids = [r['id'] for r in base_rules]
    if args.evaluate:
        return evaluate(args, target, base_ids)
    t0 = time.monotonic()
    with open(args.rules) as f:
        cand_rules = [r for r in json.load(f)['rules']
                      if r['id'] not in base_ids]
    by_id = {r['id']: r for r in base_rules + cand_rules}
    all_ids = emitted_ids(args.td)
    missing = [i for i in base_ids if i not in all_ids]
    if missing:
        raise SystemExit('baseline rules not in the llc (%s): %s' % (
            args.td, missing))
    # A candidate that joint-emit refused is not in the llc.
    not_emitted = [r['id'] for r in cand_rules if r['id'] not in all_ids]
    cand_rules = [r for r in cand_rules if r['id'] in all_ids]
    cids = [r['id'] for r in cand_rules]
    files, finfo = read_files(args)
    M = Measurer(args.llc, target, all_ids, args.cache, args.j)
    log = lambda m: print(m, flush=True)  # noqa: E731

    # 1. control and baseline.
    log('measure: %d files, %d baseline rules, %d candidates' % (
        len(files), len(base_ids), len(cids)))
    ctl = dict(zip(files, M.many([(p, None, False, False) for p in files])))
    base = dict(zip(files, M.many([(p, base_ids, False, True)
                                   for p in files])))
    # 2. Both screens, then baseline + X for each candidate independently.
    eligible = [p for p in files if not base[p].get('rc')]
    info, screened, screening = measure_candidates(
        M, eligible, cand_rules, base_ids, base)
    log('measure: solo done (%d compiles, %d cache hits)' % (M.compiles,
                                                            M.hits))
    best, window_report = per_window(cids, info)
    S = greedy(M, base, base_ids, best, screened, info,
               lambda ids: joint.rewrite_cycles([by_id[x] for x in base_ids + ids]))
    log('measure: greedy set of %d rules' % len(S))

    # 5. leave-one-out inside the set (select.py), then the whole set on
    # every file against the baseline (select.enforce).
    names = {i: [i] for i in all_ids}
    pinned = set(base_ids)
    loo = {}
    for _ in range(3):
        sel = set(base_ids) | set(S)
        cur, off, _ = select.check_set(args.llc, target, files, base, names,
                                       sel, args.j)
        loo = select._loo_in_set(args.llc, target, cur, off, names,
                                 set(S), args.j)
        drop = [r for r in S if loo[r]['insns'] >= 0]
        if not drop:
            break
        for r in drop:
            S.remove(r)
            info[r]['selection'] = 'no_gain_in_set'
            info[r]['loo'] = select._public(loo[r])
    sel, dropped, final, unexplained = select.enforce(
        args.llc, target, files, base, names, set(base_ids) | set(S),
        args.j, log=log, pinned=pinned)
    for r in list(S):
        if r not in sel:
            S.remove(r)
            info[r]['selection'] = 'final_set_violation'
            info[r]['final_set_violation'] = dropped.get(r)
        else:
            info[r]['loo'] = select._public(loo.get(r, {}))
    for rid in not_emitted:
        info[rid] = {'window': by_id[rid].get('window'),
                     'proof_status': by_id[rid]['semantic_status']['kind'],
                     'profitability_status': 'not_emittable'}
    status_counts = collections.Counter(i['profitability_status']
                                        for i in info.values())
    sel_counts = collections.Counter(i.get('selection') for i in info.values()
                                     if i.get('selection'))
    nondec = [r for r in S if info[r]['original_only']]
    out = {
        'config': config_record(args, target, base_ids,
                                {'candidates': len(cids)}),
        'files': finfo,
        'baseline_vs_control': compare(ctl, base, files),
        'final_vs_baseline': compare(base, final, files),
        'final_vs_control': compare(ctl, final, files),
        'selected': base_ids + S, 'new_selected': S,
        'new_selected_non_decreasing': nondec,
        'profitability': dict(status_counts), 'selection': dict(sel_counts),
        'unexplained_violations': unexplained,
        'windows': window_report,
        'multi_candidate_windows': {
            w: r for w, r in window_report.items()
            if sum(1 for s in r['status'].values()
                   if s not in ('never_matched',)) >= 2},
        'candidates': info,
        'screening': screening,
        'compiles': M.compiles, 'cache_hits': M.hits,
        'seconds': round(time.monotonic() - t0, 1),
    }
    with open(os.path.join(args.out, 'selection.json'), 'w') as f:
        json.dump(out, f, indent=1)
    fb = out['final_vs_baseline']
    print('measure: %d candidates: %s; selected %d (%s); final set vs '
          'baseline: insns %+d, code bytes %+d, %d smaller, %d larger' % (
              len(cids), dict(status_counts), len(S), dict(sel_counts),
              fb['insns_delta'], fb['code_bytes_delta'], len(fb['smaller']),
              len(fb['larger'])))


if __name__ == '__main__':
    main()
