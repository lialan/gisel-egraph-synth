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
  screen     every rule, with -gisel-synth-joint-screen: each rule reports
             where it would match and none applies, so no rule hides
             another (a rule that the baseline enables after it applied is
             not seen here)
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
import concurrent.futures
import copy
import hashlib
import json
import os
import re
import sys
import threading
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))

from girs import joint, measure, select, targets  # noqa: E402

METRIC_VERSION = 1
SCREEN_FLAG = '-gisel-synth-joint-screen'
METRICS = ('insns', 'code_bytes', 'sgpr', 'vgpr', 'spills', 'scratch')


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


def sha_file(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


def emitted_ids(td):
    with open(td) as f:
        return re.findall(r'^def (joint_\w+) : GICombineRule', f.read(), re.M)


class Measurer:
    """Compilations of files with sets of enabled rules, with a cache: the
    key is the compiler, its flags, the content of the file, the enabled
    rules (or control / screen) and METRIC_VERSION."""

    def __init__(self, llc, target, all_ids, cache, jobs):
        self.llc, self.target = llc, target
        self.all_ids = sorted(all_ids)
        self.jobs = jobs
        self.llc_sha = sha_file(llc)
        self.file_sha = {}
        self.lock = threading.Lock()
        self.cache_path = cache
        self.memo = {}
        self.hits = self.compiles = 0
        if cache and os.path.exists(cache):
            with open(cache) as f:
                for line in f:
                    k, v = json.loads(line)
                    self.memo[k] = v

    def key(self, path, enabled, screen, count):
        if path not in self.file_sha:
            self.file_sha[path] = sha_file(path)
        return hashlib.sha256(json.dumps([
            METRIC_VERSION, self.llc_sha, self.target.ll_flags,
            self.file_sha[path], None if enabled is None else
            sorted(enabled), screen, count]).encode()).hexdigest()

    def one(self, path, enabled=None, screen=False, count=True):
        k = self.key(path, enabled, screen, count)
        with self.lock:
            if k in self.memo:
                self.hits += 1
                return self.memo[k]
        if enabled is None:
            res = measure.compile_ll(self.llc, self.target, path)
        else:
            off = sorted(set(self.all_ids) - set(enabled))
            res = measure.compile_ll(
                self.llc, self.target, path,
                flags=[SCREEN_FLAG] if screen else [], synth=True,
                disabled=off, count_rules=count)
        with self.lock:
            self.compiles += 1
            self.memo[k] = res
            if self.cache_path:
                with open(self.cache_path, 'a') as f:
                    f.write(json.dumps([k, res]) + '\n')
        return res

    def many(self, jobs):
        """[(path, enabled, screen, count)] -> results in order."""
        with concurrent.futures.ThreadPoolExecutor(self.jobs) as ex:
            return list(ex.map(lambda j: self.one(*j), jobs))


def delta(a, b):
    """Metrics of b - a (negative: b is smaller), or None if one of them
    did not compile."""
    if a.get('rc') or b.get('rc'):
        return None
    return {m: b.get(m, 0) - a.get(m, 0) for m in METRICS}


def worse(base, cur):
    """Why ``cur`` is worse than ``base`` (select._violations), or None."""
    return select._violations({'f': cur}, {'f': base}).get('f')


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


def solo_info(cand_rules, screened, solo, base):
    """The solo measurement of each candidate (baseline + it, on the files
    where it screened) and its profitability status."""
    info = {}
    for rule in cand_rules:
        rid = rule['id']
        est = rule['candidate']['estimated_cost']
        i = {'window': rule.get('window'),
             'proof_status': rule['semantic_status']['kind'],
             'generic_cost': [est['before'], est['after']],
             'original_only': rule['plan'].get('original_only', False),
             'text': rule['candidate']['text'],
             'screened_files': len(screened.get(rid, []))}
        info[rid] = i
        if not screened.get(rid):
            i['profitability_status'] = 'never_matched'
            continue
        applied = sum(r.get('passed', {}).get(rid, 0)
                      for r in solo[rid].values())
        tot = collections.Counter()
        bad, gains = [], []
        for p, r in solo[rid].items():
            why = worse(base[p], r)
            if why:
                bad.append((os.path.basename(p), why))
            d = delta(base[p], r)
            if d:
                tot.update(d)
                if d['insns']:
                    gains.append((os.path.basename(p), -d['insns']))
        i['solo'] = {'files': len(solo[rid]), 'applied': applied,
                     'insns_saved': -tot['insns'],
                     'code_bytes_saved': -tot['code_bytes'],
                     'vgpr_delta': tot['vgpr'], 'sgpr_delta': tot['sgpr'],
                     'spills_delta': tot['spills'],
                     'worse_files': bad[:10], 'per_file': sorted(gains)[:20]}
        if not applied:
            i['profitability_status'] = 'no_application'
        elif bad:
            i['profitability_status'] = 'regression'
        elif -tot['insns'] > 0:
            i['profitability_status'] = 'profitable'
        else:
            i['profitability_status'] = 'no_gain'
        i['marginal'] = {'insns_saved': -tot['insns']}
    return info


def solo_key(info, rid):
    s = info[rid].get('solo', {})
    return (-s.get('insns_saved', 0), -s.get('code_bytes_saved', 0),
            info[rid]['generic_cost'][1], rid)


def per_window(cids, info):
    """The candidates of one source pattern (window) side by side: the
    profitable one with the largest solo gain is the candidate of the
    window, the others are dominated. Returns (the candidate of each
    window, largest solo gain first; the report of each window)."""
    groups = collections.defaultdict(list)
    for rid in cids:
        groups[info[rid]['window']].append(rid)
    best = []
    report = {}
    for w, ids in groups.items():
        prof = sorted((r for r in ids
                       if info[r]['profitability_status'] == 'profitable'),
                      key=lambda r: solo_key(info, r))
        report[w] = {
            'candidates': sorted(ids, key=lambda r: solo_key(info, r)),
            'solo_insns_saved': {r: info[r].get('solo', {}).get(
                'insns_saved') for r in ids},
            'status': {r: info[r]['profitability_status'] for r in ids}}
        if prof:
            best.append(prof[0])
            info[prof[0]]['selection'] = 'candidate'
            for r in prof[1:]:
                info[r]['selection'] = 'dominated_in_window'
                info[r]['dominated_by'] = prof[0]
    best.sort(key=lambda r: solo_key(info, r))
    return best, report


def greedy(M, base, base_ids, best, screened, info, cycles):
    """The set S, built in the order of ``best``: X joins if baseline + S
    + X has fewer instructions than baseline + S on the files of X, no
    file is worse (than the baseline or than baseline + S), and S + X has
    no rewrite cycle (``cycles``). Records the interaction of X with the
    set: its gain in the set against its solo gain."""
    S = []
    for rid in best:
        fs = screened[rid]
        prev = M.many([(p, base_ids + S, False, True) for p in fs])
        cur = M.many([(p, base_ids + S + [rid], False, True) for p in fs])
        tot = collections.Counter()
        bad = []
        for p, a, b in zip(fs, prev, cur):
            why = worse(base[p], b) or worse(a, b)
            if why:
                bad.append((os.path.basename(p), why))
            d = delta(a, b)
            if d:
                tot.update(d)
        gain = -tot['insns']
        i = info[rid]
        i['in_set'] = {'insns_saved': gain,
                       'code_bytes_saved': -tot['code_bytes'],
                       'set_before': list(S), 'worse_files': bad[:10]}
        solo_gain = i['solo']['insns_saved']
        if gain < solo_gain:
            i['interaction'] = 'overlaps the set: %d of its solo %d' % (
                gain, solo_gain)
        elif gain > solo_gain:
            i['interaction'] = 'enabled by the set: %d, solo %d' % (
                gain, solo_gain)
        if bad:
            i['selection'] = 'worse_in_set'
            continue
        if gain <= 0:
            i['selection'] = 'no_gain_in_set'
            continue
        cyc = cycles(S + [rid])
        if cyc:
            i['selection'] = 'cycle'
            i['cycle'] = cyc
            continue
        S.append(rid)
        i['selection'] = 'selected'
    return S



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

    # 1. control, baseline, screen.
    log('measure: %d files, %d baseline rules, %d candidates' % (
        len(files), len(base_ids), len(cids)))
    ctl = dict(zip(files, M.many([(p, None, False, False) for p in files])))
    base = dict(zip(files, M.many([(p, base_ids, False, True)
                                   for p in files])))
    scr = dict(zip(files, M.many([(p, base_ids + cids, True, True)
                                  for p in files])))
    screened = collections.defaultdict(list)
    for p in files:
        if base[p].get('rc') or ctl[p].get('rc'):
            continue
        for rid in scr[p].get('matched', {}):
            if rid in cids:
                screened[rid].append(p)
    log('measure: control/baseline/screen done (%d compiles); %d '
        'candidates screened' % (M.compiles, len(screened)))

    # 2. solo: baseline + X on the files where X screened.
    jobs = [(rid, p) for rid in cids for p in screened.get(rid, [])]
    res = M.many([(p, base_ids + [rid], False, True) for rid, p in jobs])
    solo = collections.defaultdict(dict)
    for (rid, p), r in zip(jobs, res):
        solo[rid][p] = r
    info = solo_info(cand_rules, screened, solo, base)
    log('measure: solo done (%d compiles, %d cache hits)' % (M.compiles,
                                                            M.hits))
    best, window_report = per_window(cids, info)
    S = greedy(M, base, base_ids, best, screened, info,
               lambda ids: joint.rewrite_cycles([by_id[x] for x in ids]))
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
