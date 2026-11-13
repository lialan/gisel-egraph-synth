#!/usr/bin/env python3
"""Paired, cold-search-cache comparison of single-round and iterative mine.

All arms finish selection before any arm reads held-out measurements.
The same corpus, target, workers, seed and total search allowance are used.
Compilation and selection time are outside that allowance and reported.
No gain is required: a null/negative result is still a completed experiment.
"""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
from girs import mine


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--config', required=True)
    ap.add_argument('--local')
    ap.add_argument('--out', required=True)
    ap.add_argument('--budget-s', type=float, default=300)
    ap.add_argument('--seeds', type=int, nargs='+', default=[17, 29])
    ap.add_argument('--rounds', type=int, default=3)
    ap.add_argument('--jobs', type=int, default=16)
    args = ap.parse_args()
    if args.budget_s <= 0 or args.rounds < 2 or args.jobs < 1:
        ap.error('positive budget/jobs and at least two treatment rounds are required')
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    spec = importlib.util.spec_from_file_location('experiment_cli', HERE / 'gi-rule-synth.py')
    cli = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = cli
    spec.loader.exec_module(cli)
    root = mine.Run(args.config, str(out / 'inputs'), cli, local=args.local)
    config = root.cfg
    # The build can be left at the most recently built candidate. Keep the
    # initial compiler image immutable across arms and resume.
    import shutil
    reference = out / 'reference-llc'
    if not reference.exists():
        shutil.copy2(config['llc'], reference)
    config['llc'] = str(reference)
    config['restore_build'] = False
    config['jobs'] = args.jobs
    config['search'].update(search_jobs=args.jobs, slow_total_s=0)
    config['joint'].update(jobs=args.jobs)
    arms = []
    for seed in args.seeds:
        for name, rounds, metric in (('single-insns', 1, 'insns'),
                                     ('loop-insns', args.rounds, 'insns'),
                                     ('loop-bytes', args.rounds, 'code_bytes')):
            c = copy.deepcopy(config)
            label = '%s-seed%d' % (name, seed)
            folder = out / label
            folder.mkdir(exist_ok=True)
            c['name'] = label
            c['cache_dir'] = str(folder / 'cache')
            c['search']['seed'] = c['joint']['seed'] = seed
            c['loop'].update(rounds=rounds, search_budget_s=args.budget_s)
            c['select'].update(strategy='measured', metric=metric)
            path = folder / 'input.json'
            if path.exists() and json.loads(path.read_text()) != c:
                raise ValueError('experiment configuration changed: ' + label)
            path.write_text(json.dumps(c, indent=2) + '\n')
            arms.append((label, folder, path))
    protocol = {'budget_s': args.budget_s, 'seeds': args.seeds, 'jobs': args.jobs,
                'harness_sha256': mine._sha_file(__file__),
                'arms': [a[0] for a in arms], 'source': root.inputs_identity(),
                'comparison': 'same engine and candidate policy; single round vs feedback rounds',
                'heldout_policy': 'all selections frozen before any heldout evaluation'}
    protocol_path = out / 'protocol.json'
    if protocol_path.exists() and json.loads(protocol_path.read_text()) != protocol:
        raise ValueError('experiment source or protocol changed; use a new directory')
    protocol_path.write_text(json.dumps(protocol, indent=2) + '\n')
    for phase, until in (('selection', 'verify'), ('evaluation', None)):
        for label, folder, path in arms:
            command = [sys.executable, '-u', str(HERE / 'gi-rule-synth.py'), 'mine',
                       '--config', str(path), '--run-dir', str(folder / 'run')]
            if until:
                command += ['--until', until]
            marker = folder / (phase + '.json')
            if marker.exists() and json.loads(marker.read_text()).get('rc') == 0:
                continue
            started = time.monotonic()
            print(phase, label, flush=True)
            with (folder / (phase + '.log')).open('a') as log:
                rc = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT).returncode
            marker.write_text(json.dumps({'rc': rc, 'wall_s': time.monotonic() - started}) + '\n')
            if rc:
                raise SystemExit('%s failed: %s' % (label, folder / (phase + '.log')))
    summary = {}
    for label, folder, _ in arms:
        report = json.loads((folder / 'run' / 'report.json').read_text())
        summary[label] = {'objective': report['objective'],
            'search_elapsed_s': report['campaign']['search_elapsed_s'],
            'new_selected': report['campaign']['new_selected'],
            'newly_discovered_selected': report['campaign']['newly_discovered_selected'],
            'known_rules_newly_selected': report['campaign']['known_rules_newly_selected'],
            'rounds': [{k: r.get(k) for k in ('search_elapsed_s', 'new_selected', 'selection')}
                       for r in report['campaign']['rounds']],
            'evaluation': report['evaluation'],
            'selection_wall_s': json.loads((folder / 'selection.json').read_text())['wall_s']}
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
