#!/usr/bin/env python3
"""Replay a frozen corpus with fresh caches and compare process counts."""
import argparse
import hashlib
import json
import platform
import z3
from pathlib import Path
import statistics
import subprocess
import sys
import time

from girs import emit, known


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('corpus')
    ap.add_argument('--out', required=True)
    ap.add_argument('--jobs', nargs='+', type=int, default=[1, 8])
    ap.add_argument('--repeats', type=int, default=2)
    ap.add_argument('--max-evals', type=int, default=1000000)
    ap.add_argument('--max-terms', type=int, default=10000)
    ap.add_argument('--max-rhs-cost', type=int, default=2)
    ap.add_argument('--search-batch', type=int, default=16)
    ap.add_argument('--grammar', default='auto')
    ap.add_argument('--timeout-ms', type=int, default=10000)
    ap.add_argument('--slow-timeout-ms', type=int, default=120000)
    ap.add_argument('--slow-total-s', type=float, default=3600)
    ap.add_argument('--regions', action='store_true')
    ap.add_argument('--siblings', action='store_true')
    ap.add_argument('--max-pairs', type=int, default=0)
    a = ap.parse_args()
    if a.repeats < 1 or not a.jobs or min(a.jobs) < 0 or 1 not in a.jobs:
        ap.error('positive repeats and nonnegative jobs including 1 are required')
    source = Path(a.corpus).resolve()
    out = Path(a.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    report = {'corpus': str(source),
              'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'parameters': vars(a), 'runs': [],
              'host': platform.node(), 'python': platform.python_version(),
              'z3': z3.get_version_string(),
              'search_sha': known.search_sha(),
              'semantics_sha': known.semantics_sha()}
    for repeat in range(a.repeats):
        # Alternate order to reduce a systematic warm-machine advantage.
        order = a.jobs if repeat % 2 == 0 else list(reversed(a.jobs))
        for jobs in order:
            run = out / ('j%d-r%d' % (jobs, repeat))
            run.mkdir(exist_ok=True)
            command = [sys.executable, str(Path(__file__).with_name('gi-rule-synth.py')),
                       'synth', str(source), '--known', '', '--cache', '',
                       '--search-jobs', str(jobs), '--search-batch', str(a.search_batch),
                       '--grammar', a.grammar, '--max-evals', str(a.max_evals),
                       '--max-terms', str(a.max_terms), '--max-rhs-cost', str(a.max_rhs_cost),
                       '--timeout-ms', str(a.timeout_ms),
                       '--slow-timeout-ms', str(a.slow_timeout_ms),
                       '--slow-total-s', str(a.slow_total_s),
                       '--max-pairs', str(a.max_pairs),
                       '--proofs', str(run/'proofs'), '-o', str(run/'rules.json')]
            command += ['--regions'] if a.regions else []
            command += ['--siblings'] if a.siblings else []
            start = time.monotonic()
            with (run/'run.log').open('w') as log:
                result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
            wall = time.monotonic() - start
            if result.returncode:
                raise RuntimeError('failed run: ' + str(run/'run.log'))
            db = json.loads((run/'rules.json').read_text())
            st = json.loads((run/'rules.stats.json').read_text())
            td, inc, _ = emit.emit(db, {}, True)
            (run/'rules.td').write_text(td)
            (run/'rules.inc').write_text(inc)
            row = {'jobs': jobs, 'repeat': repeat, 'wall_s': wall,
                   'rules': len(db['rules']), 'rules_sha': digest(db['rules']),
                   'revisions_sha': digest(sorted(known.revision(r) for r in db['rules'])),
                   'generated_sha': digest([td, inc]),
                   'phases': st['seconds'], 'stops': st['discovery']['stop'],
                   'parallel': st.get('parallel'), 'command': command}
            report['runs'].append(row)
            print(json.dumps({k:row[k] for k in ['jobs','repeat','wall_s','rules','revisions_sha']}), flush=True)
            (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    process_runs = [r for r in report['runs'] if r['jobs'] > 0]
    report['semantic_parity'] = len({r['revisions_sha'] for r in process_runs}) == 1
    report['full_rule_parity'] = len({r['rules_sha'] for r in process_runs}) == 1
    report['generated_parity'] = len({r['generated_sha'] for r in process_runs}) == 1
    if 0 in a.jobs:
        for label, field in [('semantic', 'revisions_sha'),
                             ('full_rule', 'rules_sha'),
                             ('generated', 'generated_sha')]:
            report['legacy_' + label + '_parity'] = len(
                {r[field] for r in report['runs']}) == 1
    report['unresolved'] = any(r['parallel']['incomplete'] for r in process_runs)
    report['median_wall_s'] = {str(j): statistics.median(
        r['wall_s'] for r in report['runs'] if r['jobs'] == j) for j in a.jobs}
    if '1' in report['median_wall_s']:
        report['speedup_vs_one'] = {j: report['median_wall_s']['1']/t
                                   for j,t in report['median_wall_s'].items()}
    (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['runs','parameters']}, indent=2))
    return 0 if all(report[k] for k in (
        'semantic_parity', 'full_rule_parity', 'generated_parity')) else 1


if __name__ == '__main__':
    sys.exit(main())
