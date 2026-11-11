#!/usr/bin/env python3
"""Measure candidates independently on their real corpus occurrences.

This is an inexpensive screen before joint selection, particularly for
equal-cost/growing candidates which may undo existing combines or cycle.
All other synthesized rules in the candidate binary are disabled. Results
are discovery-set evidence only: they do not replace frozen held-out or
final-set acceptance, and do not modify a target profile.
"""

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
from girs import emit, measure, report, targets  # noqa: E402


def screen(run, llc, target, timeout=5, jobs=4, max_rules=0, examples=2):
    db = json.loads((run / 'library/rules.json').read_text())
    candidates = [r for r in emit.candidates(db, target) if emit.emittable(r)]
    names = {r['id']: emit.record_names(r) for r in candidates}
    # Width/one-use variants do not establish a new family.
    old = json.loads((run / 'frozen-baseline/rules.json').read_text())
    frozen = {report.family_key(r) for r in old['rules']}
    index = json.loads((run / 'corpus/index.json').read_text())
    files = {v['out']: (k, v) for k, v in index.items() if v['out']}
    candidates.sort(key=lambda r: (
        report.family_key(r) in frozen,
        hashlib.sha256(r['id'].encode()).hexdigest()))
    total = len(candidates)
    if max_rules:
        candidates = candidates[:max_rules]
    pairs = []
    for r in candidates:
        seen = set()
        for ex in r['support']['examples']:
            if ex['file'] not in files:
                continue
            path, provenance = files[ex['file']]
            if path in seen:
                continue
            seen.add(path)
            pairs.append((r, path, provenance))
            if len(seen) >= examples:
                break
    paths = sorted({p for _, p, _ in pairs})
    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        baseline = dict(zip(paths, pool.map(
            lambda p: measure.compile_ll(llc, target, p, timeout=timeout),
            paths)))

    def one(pair):
        r, path, provenance = pair
        off = [n for rid, ns in names.items() if rid != r['id'] for n in ns]
        base = baseline[path]
        cur = measure.compile_ll(llc, target, path, synth=True,
                                 disabled=off, timeout=timeout) if \
            base['rc'] == 0 else None
        status = 'baseline_failed'
        delta = None
        fired = 0
        if cur is not None:
            if cur['rc']:
                status = 'compile_failed_or_timeout'
            elif cur.get('fallback', []) != base.get('fallback', []):
                status = 'fallback_changed'
            else:
                fired = cur.get('passed', {}).get(r['id'], 0)
                delta = cur['insns'] - base['insns']
                status = 'not_fired' if not fired else (
                    'better' if delta < 0 else 'worse' if delta > 0 else 'same')
        return {'id': r['id'], 'source': provenance['source'],
                'pipeline': provenance['pipeline'], 'input': path,
                'family': report.family_key(r),
                'family_in_frozen': report.family_key(r) in frozen,
                'class': r['class'], 'status': status, 'fired': fired,
                'insns_delta': delta, 'baseline': base, 'candidate': cur}

    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        results = list(pool.map(one, pairs))
    out = {
        'scope': 'Independent candidates on discovery examples only; '
                 'neither final-set gain nor held-out acceptance.',
        'llc': str(llc), 'llc_sha256': hashlib.sha256(
            Path(llc).read_bytes()).hexdigest(),
        'library_sha256': hashlib.sha256(
            (run / 'library/rules.json').read_bytes()).hexdigest(),
        'candidate_rules': total, 'screened_rules': len(candidates),
        'rules_with_examples': len({r['id'] for r in results}),
        'timeout_seconds': timeout, 'results': results,
    }
    (run / 'candidate-screen.json').write_text(
        json.dumps(out, indent=2, sort_keys=True) + '\n')
    from collections import Counter
    print(dict(Counter(r['status'] for r in results)), flush=True)
    for r in results:
        if r['status'] == 'better':
            print(r['id'], r['insns_delta'], r['source'], flush=True)
    return out


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run-dir', type=Path, required=True)
    p.add_argument('--llc', required=True,
                   help='candidate binary built from this run library')
    p.add_argument('--target', default='AMDGPU')
    p.add_argument('--timeout', type=int, default=5)
    p.add_argument('--jobs', type=int, default=4)
    p.add_argument('--max-rules', type=int, default=0)
    p.add_argument('--examples', type=int, default=2)
    a = p.parse_args()
    run = a.run_dir.resolve()
    llc = str(Path(a.llc).resolve())
    os.chdir(HERE.parents[2])
    screen(run, llc, targets.get(a.target), a.timeout, a.jobs,
           a.max_rules, a.examples)


if __name__ == '__main__':
    main()
