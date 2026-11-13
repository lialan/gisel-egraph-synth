"""Shared joint-candidate measurement and selection for mine and the CLI."""

import collections
import concurrent.futures
import hashlib
import json
import os
import threading

from . import measure, select

METRIC_VERSION = 2
SCREEN_FLAG = '-gisel-synth-joint-screen'
SCREEN_APPLY_FLAG = '-gisel-synth-joint-screen-apply='
METRICS = ('insns', 'code_bytes', 'sgpr', 'vgpr', 'spills', 'scratch')


def sha_file(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


class Measurer:
    """Compilations of files with sets of enabled rules, with a cache: the
    key is the compiler, its flags, the content of the file, the enabled
    rules (or control / screen) and METRIC_VERSION."""

    def __init__(self, llc, target, all_ids, cache, jobs, names=None):
        self.llc, self.target = llc, target
        self.all_ids = sorted(all_ids)
        self.names = names or {i: [i] for i in self.all_ids}
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
            measure.synth_flags(self.target, count_rules=count), self.names,
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
            off = [n for i in self.all_ids if i not in enabled
                   for n in self.names[i]]
            res = measure.compile_ll(
                self.llc, self.target, path,
                flags=screen_flags(screen), synth=True,
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


def screen_flags(screen):
    """False: ordinary compilation; True: read-only screen; a sequence:
    screen candidates while allowing these baseline joint rules to apply.
    An empty sequence is still a screen, with no allowed rewrites."""
    if screen is False:
        return []
    flags = [SCREEN_FLAG]
    if screen is not True and screen:
        flags.append(SCREEN_APPLY_FLAG + ','.join(sorted(screen)))
    return flags


def measure_candidates(M, files, cand_rules, base_ids, base):
    """Screen the original MIR and the baseline's rewriting worklist,
    then measure each candidate alone over the same baseline. A failed
    screen falls back to solo measurement, never to 'no match'."""
    cids = [r['id'] for r in cand_rules]
    if not cids:
        return {}, {}, {'baseline_only': {}, 'failed': []}
    joint_base = tuple(i for i in base_ids if i.startswith('joint_'))
    modes = [True] + ([joint_base] if joint_base else [])
    jobs = [(p, base_ids + cids, mode, True)
            for mode in modes for p in files]
    results = M.many(jobs)
    hits, baseline_only, failed = {}, {}, []
    for mode, batch in zip(modes, range(0, len(results), len(files) or 1)):
        for p, res in zip(files, results[batch:batch + len(files)]):
            before = hits.setdefault(p, set())
            matched = set(res.get('matched', {})) & set(cids)
            if mode is not True and matched - before:
                baseline_only[p] = sorted(matched - before)
            if res.get('rc'):
                failed.append({'file': p, 'baseline_applied': mode is not True})
                matched = set(cids)
            before.update(matched)
    screened = {rid: [p for p in files if rid in hits[p]] for rid in cids}
    jobs = [(rid, p) for rid in cids for p in screened[rid]]
    results = M.many([(p, base_ids + [rid], False, True) for rid, p in jobs])
    solo = {rid: {} for rid in cids}
    for (rid, p), res in zip(jobs, results):
        solo[rid][p] = res
    return (solo_info(cand_rules, screened, solo, base), screened,
            {'baseline_only': baseline_only, 'failed': failed})


def solo_info(cand_rules, screened, solo, base):
    """The solo measurement of each candidate (baseline + it, on the files
    where it screened) and its profitability status."""
    info = {}
    for rule in cand_rules:
        rid = rule['id']
        est = rule['candidate']['estimated_cost']
        window = rule.get('window') or hashlib.sha256(json.dumps(
            rule['source'], sort_keys=True).encode()).hexdigest()
        i = {'window': window,
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
        if bad:
            i['profitability_status'] = 'regression'
        elif not applied:
            i['profitability_status'] = 'no_application'
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
