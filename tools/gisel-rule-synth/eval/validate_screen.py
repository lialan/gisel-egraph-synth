#!/usr/bin/env python3
"""Bounded joint validation of an independent candidate screen.

Rank from discovery examples, greedily require a net instruction reduction
and no per-file regressions on the entire discovery+validation manifest,
freeze, then evaluate the untouched held-out manifest once. Never sums
individual candidate gains. This writes experiment evidence, not a profile.
"""

import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
from girs import emit, measure, mine, report  # noqa: E402


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--run-dir', type=Path, required=True)
    ap.add_argument('--top-per-class', type=int, default=2)
    ap.add_argument('--timeout', type=int, default=5)
    ap.add_argument('--jobs', type=int, default=8)
    a = ap.parse_args()
    spec = importlib.util.spec_from_file_location('gi_rule_synth',
                                                HERE / 'gi-rule-synth.py')
    cli = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cli)
    root = a.run_dir.resolve()
    out = root / 'screen-validation'
    if (out / 'frozen.json').exists():
        raise SystemExit('This screen is already frozen; do not tune on held-out.')
    out.mkdir(exist_ok=True)
    run = mine.Run(str(root / 'config.json'), str(root), cli)
    db = run.library()
    rules = {r['id']: r for r in emit.candidates(db, run.target)
             if emit.emittable(r)}
    names = {rid: emit.record_names(r) for rid, r in rules.items()}
    screen = json.loads((root / 'candidate-screen.json').read_text())
    llc = run.candidate_llc()
    if hashlib.sha256(Path(llc).read_bytes()).hexdigest() != \
            screen['llc_sha256'] or hashlib.sha256(
                (root / 'library/rules.json').read_bytes()).hexdigest() != \
            screen['library_sha256']:
        raise SystemExit('Screen, compiler and library do not match.')
    by_id = {}
    for row in screen['results']:
        by_id.setdefault(row['id'], []).append(row)
    eligible = [rid for rid, rows in by_id.items() if
                any(r['status'] == 'better' for r in rows) and
                all(r['status'] in ('better', 'same', 'not_fired') and
                    r['insns_delta'] <= 0 for r in rows)]
    eligible.sort(key=lambda rid: (
        sum(r['insns_delta'] for r in by_id[rid]),
        not rules[rid]['needs_one_use'], rid))
    seen, counts, trials = set(), {}, []
    for rid in eligible:
        family = report.family_key(rules[rid])
        cls = rules[rid]['class']
        if family in seen or counts.get(cls, 0) >= a.top_per_class:
            continue
        seen.add(family)
        counts[cls] = counts.get(cls, 0) + 1
        trials.append(rid)

    def compile_set(units, selected=None):
        paths = sorted({u.path for u in units})
        off = [n for rid, ns in names.items()
               if rid not in (selected or ()) for n in ns]

        def one(path):
            return measure.compile_ll(llc, run.target, path,
                                      synth=selected is not None,
                                      disabled=off, timeout=a.timeout)
        with concurrent.futures.ThreadPoolExecutor(a.jobs) as pool:
            return dict(zip(paths, pool.map(one, paths)))

    units = run.units('selection')
    base = compile_set(units)
    mine._dump(base, str(out / 'selection-base.json'))
    selected, delta, records = [], 0, []
    for rid in trials:
        trial = selected + [rid]
        result = compile_set(units, trial)
        summary = mine.summarize(units, base, result)
        safe = all(not s['compile_failures'] and not s['fallback_changed']
                   and s['files_worse'] == 0 for s in summary.values())
        new_delta = sum(s['insns_delta'] for s in summary.values())
        accepted = safe and new_delta < delta
        records.append({'id': rid, 'accepted': accepted,
                        'joint_insns_delta': new_delta, 'summary': summary})
        mine._dump(result, str(out / (rid + '.json')))
        if accepted:
            selected, delta = trial, new_delta
        print(rid, 'accepted' if accepted else 'rejected', new_delta, flush=True)
    frozen = {
        'selected': selected, 'selection_insns_delta': delta,
        'trial_policy': {'top_per_class': a.top_per_class,
                         'timeout_seconds': a.timeout},
        'trials': records, 'library_sha256': screen['library_sha256'],
        'llc_sha256': screen['llc_sha256'],
        'manifests': {r: mine._sha_file(p)
                      for r, p in run.cfg['manifests'].items()},
        'statement': 'Frozen before any candidate evaluation on held-out.',
    }
    mine._dump(frozen, str(out / 'frozen.json'))
    heldout = run.units('heldout')
    hb, hc = compile_set(heldout), compile_set(heldout, selected)
    mine._dump(hb, str(out / 'heldout-base.json'))
    mine._dump(hc, str(out / 'heldout-final.json'))
    hs = mine.summarize(heldout, hb, hc)
    mine._dump(hs, str(out / 'heldout-summary.json'))
    print('heldout', {k: {f: v[f] for f in (
        'compared', 'insns_delta', 'files_better', 'files_worse',
        'compile_failures', 'fallback_changed')} for k, v in hs.items()}, flush=True)


if __name__ == '__main__':
    main()
