#!/usr/bin/env python3
"""Fixed-budget discovery rounds on one `mine` configuration.

Runs the discovery stage of a run directory `--rounds` times with the time
budget of the configuration (`search.time_budget_s`) and records, after
each round, the state of the search queue, the verified new rules and the
time by kind. To compare one long run with several short runs, give each
arm its own `cache_dir` and run directory, and the same total budget:

  budget_rounds.py --config long.json  --run-dir runs/long  --rounds 1
  budget_rounds.py --config short.json --run-dir runs/short --rounds 4

The rounds report discovery only. `mine` on the run directory continues
with build, selection and held-out evaluation; `--local` with
{"search": {"time_budget_s": 1}} does so without more search.
"""

import argparse
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parents[1]


def row(n, stats, rules):
    queue = stats['queue']
    by_id = {r['id']: r for r in rules['rules']}
    delta = stats['incremental']['delta']
    stages = {k: v for k, v in queue.items() if k != 'left'}
    return {
        'round': n,
        'seconds': stats['seconds']['total'],
        'cost_seconds': stats['cost_seconds'],
        'searched': {k: v['searched_in_this_run'] for k, v in stages.items()},
        'complete': {k: v['complete'] for k, v in stages.items()},
        'closed_at_this_depth': {k: v['closed_at_this_depth']
                                 for k, v in stages.items()},
        'left': queue['left'],
        'new_rules': sorted(delta),
        'new_rules_emittable': sum(
            1 for i in delta if by_id[i].get('emission') == 'yes'),
        'new_rules_with_several_outputs': sum(
            1 for i in delta if by_id[i].get('region')),
        'known_candidates': stats['discovery']['known_candidates'],
        'candidate_fate': stats['candidate_fate'],
        'term_banks': stats['enumeration']['banks'],
        'solver_calls': stats['solver_calls'],
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--config', required=True)
    ap.add_argument('--run-dir', required=True)
    ap.add_argument('--rounds', type=int, default=4)
    ap.add_argument('-o', help='JSON output (default: '
                    '<run-dir>/budget-rounds.json)')
    args = ap.parse_args()
    run = Path(args.run_dir)
    out = Path(args.o) if args.o else run / 'budget-rounds.json'
    rows = json.loads(out.read_text()) if out.exists() else []
    for _ in range(args.rounds):
        subprocess.run([sys.executable, str(HERE / 'gi-rule-synth.py'),
                        'mine', '--config', args.config, '--run-dir',
                        str(run), '--until', 'discover'], check=True,
                       stdout=subprocess.DEVNULL)
        lib = run / 'library'
        rows.append(row(len(rows) + 1,
                        json.loads((lib / 'rules.stats.json').read_text()),
                        json.loads((lib / 'rules.json').read_text())))
        run.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(rows, indent=1, sort_keys=True) + '\n')
        r, prev = rows[-1], rows[-2]['new_rules'] if len(rows) > 1 else []
        print('round %d: %.0f s, left %d, complete %s, new rules %d '
              '(+%d, -%d), emittable %d, several outputs %d' % (
                  r['round'], r['seconds'], r['left'],
                  json.dumps(r['complete'], sort_keys=True),
                  len(r['new_rules']),
                  len(set(r['new_rules']) - set(prev)),
                  len(set(prev) - set(r['new_rules'])),
                  r['new_rules_emittable'],
                  r['new_rules_with_several_outputs']), flush=True)
        if not r['left']:
            print('no task is left at these budgets')
            break


if __name__ == '__main__':
    main()
