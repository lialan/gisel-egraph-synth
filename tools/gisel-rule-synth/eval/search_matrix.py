#!/usr/bin/env python3
"""Controlled, semantics-only search experiments on real LLVM test files.

All arms use the same deterministic manifest subsets and budgets. Only the
named pipeline/grammar/cost/window settings differ. A family absent from
rules.json is NOT evidence that InstCombine or SelectionDAG lacks it.
Run directories are private to this experiment; no maintained rules or
target profiles are overwritten. Use `mine` afterwards for final-code
measurement, selection and held-out acceptance of a chosen arm.
"""

import argparse
import collections
import concurrent.futures
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
from girs import emit, report, targets  # noqa: E402

ARMS = (
    ('direct-source-d2', 'direct', 'source', None, 1, 2),
    ('o2-source-d2', 'opt-O2', 'source', None, 1, 2),
    ('o2-registry-d2', 'opt-O2', 'registry', None, 1, 2),
    ('o2-forms-d2', 'opt-O2', 'registry', None, 3, 2),
    ('o2-equal-d2', 'opt-O2', 'registry', 0, 3, 2),
    ('o2-growth-d2', 'opt-O2', 'registry', 1, 3, 2),
    ('o2-growth-d3', 'opt-O2', 'registry', 1, 3, 3),
    ('o2-growth-d4', 'opt-O2', 'registry', 1, 3, 4),
)


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def summarize(directory):
    frozen = json.loads((HERE / 'rules.json').read_text())['rules']
    old = {report.family_key(r) for r in frozen}
    rows = []
    for name, *_ in ARMS:
        run = directory / name
        db_path = run / 'library/rules.json'
        if not db_path.exists():
            rows.append({'run': name, 'state': 'no completed discovery'})
            continue
        db = json.loads(db_path.read_text())
        st = json.loads((run / 'library/rules.stats.json').read_text())
        families = {report.family_key(r) for r in db['rules']}
        depth, sizes = collections.Counter(), collections.Counter()

        def height(e):
            return 0 if 'op' not in e else 1 + max(
                (height(a) for a in e.get('args', [])), default=0)

        for p in (run / 'corpus').glob('*.jsonl'):
            for line in p.read_text().splitlines():
                rec = json.loads(line)
                if 'expr' in rec:
                    depth[height(rec['expr'])] += 1
                    sizes[rec.get('interior', 0)] += 1
        rows.append({
            'run': name, 'state': 'discovery complete',
            'rules': len(db['rules']), 'families': len(families),
            'families_in_frozen': len(families & old),
            'families_outside_frozen': len(families - old),
            'measurement_candidates': len(emit.candidates(
                db, targets.get('AMDGPU'))),
            'classes': st['rules_by_class'],
            'discovery': st['discovery'], 'seconds': st['seconds'],
            'peak_rss_mb': st['peak_rss_mb'],
            'extracted_depths': dict(depth),
            'extracted_operations': dict(sizes),
            'corpus': db['corpus'],
            'new_families': sorted(families - old),
        })
    dump(directory / 'search-comparison.json', {
        'scope': 'Discovery only; no final-code benefit or LLVM-wide '
                 'novelty is implied by these counts.', 'runs': rows})
    for r in rows:
        print(r['run'], {k: r[k] for k in (
            'rules', 'families', 'families_in_frozen',
            'measurement_candidates') if k in r}, flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run-dir', type=Path, required=True)
    p.add_argument('--llc', required=True)
    p.add_argument('--opt', required=True)
    p.add_argument('--build-dir', required=True)
    p.add_argument('--limit-files', type=int, default=0,
                   help='deterministic files per role, 0 for full manifests')
    p.add_argument('--max-instances', type=int, default=0)
    p.add_argument('--seconds', type=float, default=120)
    p.add_argument('--jobs', type=int, default=8)
    p.add_argument('--parallel', type=int, default=2)
    p.add_argument('--arms', nargs='*', choices=[a[0] for a in ARMS])
    p.add_argument('--summarize-only', action='store_true')
    a = p.parse_args()
    root = a.run_dir.resolve()
    root.mkdir(parents=True, exist_ok=True)
    if a.summarize_only:
        summarize(root)
        return
    manifests = {}
    for role, filename in (
            ('discovery', 'amdgpu-discovery.txt'),
            ('validation', 'amdgpu-validation.txt'),
            ('heldout', 'amdgpu-heldout-codegen.txt')):
        lines = (HERE / 'manifests' / filename).read_text().splitlines()
        lines = sorted((l for l in lines if l.strip()),
                       key=lambda l: hashlib.sha256(l.encode()).hexdigest())
        if a.limit_files:
            lines = lines[:a.limit_files]
        path = root / (role + '.txt')
        path.write_text('\n'.join(lines) + '\n')
        manifests[role] = str(path)
    tasks = []
    for name, pipeline, grammar, slack, variants, depth in ARMS:
        if a.arms is not None and name not in a.arms:
            continue
        cfg = {
            'name': name, 'mode': 'semantics-only', 'target': 'AMDGPU',
            'llc': str(Path(a.llc).resolve()),
            'opt': str(Path(a.opt).resolve()),
            'build_dir': str(Path(a.build_dir).resolve()),
            'jobs': a.jobs, 'manifests': manifests,
            'pipelines': ['direct', 'opt-O2'],
            'discovery_pipelines': [pipeline],
            'extract': {'depth': depth, 'max_trees': 64},
            'search': {
                'grammar': grammar, 'cost_slack': slack,
                'semantic_variants': variants, 'max_rhs_cost': 3,
                'max_terms': 20000, 'max_evals': 2000000,
                'max_candidates': 6, 'max_proofs': 24, 'timeout_ms': 1000,
                'max_instances': a.max_instances,
                'time_budget_s': a.seconds,
            },
        }
        path = root / (name + '.json')
        dump(path, cfg)
        tasks.append((name, path))

    def run(task):
        name, config = task
        with (root / (name + '.log')).open('w') as log:
            rc = subprocess.run([
                sys.executable, str(HERE / 'gi-rule-synth.py'), 'mine',
                '--config', str(config), '--run-dir', str(root / name),
                '--until', 'discover'], stdout=log,
                stderr=subprocess.STDOUT).returncode
        print(name, 'exit', rc, flush=True)
        return rc

    with concurrent.futures.ThreadPoolExecutor(a.parallel) as pool:
        codes = list(pool.map(run, tasks))
    summarize(root)
    if any(codes):
        raise SystemExit('Some arms failed; inspect their logs.')


if __name__ == '__main__':
    main()
