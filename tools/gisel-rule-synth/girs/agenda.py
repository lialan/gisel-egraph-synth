"""The search tasks of a cache directory, across runs.

A task is one unit of search: an instance of the corpus ('single'), a
discovery whose instance has an output below the root ('region'), or a
group of roots ('sibling'). The row of a task says whether its search is
complete, which limits ended it, and which budgets it had. A run takes
the tasks without a row first, then the tasks that it can take further,
least searched first. A complete task does not use the budget of a run
again, and neither does a task whose limit is not higher than before.

A row belongs to a search domain: the semantic model, the search method
and the limits that decide which terms and candidates exist. Another
domain has its own rows. The budgets (terms, evaluations, proofs,
candidates, solver time) are the depth of a search inside one domain.
"""

import json
import os
import sqlite3
import time

from . import known

# The budgets of a search: its depth.
BUDGETS = ('max_terms', 'max_evals', 'max_proofs', 'max_candidates',
           'timeout_ms')

# Why a search is not complete -> the budgets that take it further when
# they are higher than they were. () is "the same budgets are enough":
#   time    the deadline of the run ended the search.
#   proofs  the proof budget of one instance ended it. A decided proof is
#           in the proof history and does not use the budget again, so the
#           next search continues after it.
REASONS = {
    'time': (),
    'proofs': (),
    'terms': ('max_terms', 'max_evals'),
    'candidates': ('max_candidates',),
    'unknown': ('timeout_ms',),
}

# A search with the reason 'proofs' that decided no more candidates than
# the search before it: the solver does not decide the next candidates.
STALLED = ('max_proofs', 'timeout_ms')

NEW, RETRY = 'new', 'retry'


def domain(limits, synth_limits, extra=None):
    """The search domain of the limits ``limits`` (discover.Limits
    .identity()) and ``synth_limits`` (the values of synth.SynthLimits)."""
    d = {k: v for k, v in limits.items() if k not in BUDGETS}
    return known.digest([known.semantics_sha(), known.search_sha(), d,
                         synth_limits, extra])


def depth(limits, timeout_ms):
    d = {k: limits[k] for k in BUDGETS if k in limits}
    d['timeout_ms'] = timeout_ms
    return d


def task_key(*parts):
    return known.digest(repr(parts))[:32]


class Agenda:
    """``directory`` None: the tasks of this process only."""

    def __init__(self, directory, domain, depth, reopen=False):
        self.domain, self.depth = domain, dict(depth)
        # Every task is searched again (synth --refresh-search).
        self.reopen = reopen
        if directory:
            os.makedirs(directory, exist_ok=True)
        self.db = sqlite3.connect(
            os.path.join(directory, 'agenda.sqlite3') if directory
            else ':memory:', timeout=30)
        if directory:
            self.db.execute('PRAGMA journal_mode=WAL')
        with self.db:
            self.db.execute(
                'CREATE TABLE IF NOT EXISTS tasks (domain TEXT NOT NULL, '
                'stage TEXT NOT NULL, key TEXT NOT NULL, state TEXT NOT '
                'NULL, reasons TEXT NOT NULL, depth TEXT NOT NULL, '
                'progress INTEGER NOT NULL, stalled INTEGER NOT NULL, '
                'runs INTEGER NOT NULL, last_run INTEGER NOT NULL, '
                'result TEXT, PRIMARY KEY (domain, stage, key))')
            self.db.execute(
                'CREATE TABLE IF NOT EXISTS runs (id INTEGER PRIMARY KEY '
                'AUTOINCREMENT, domain TEXT NOT NULL, started REAL NOT '
                'NULL)')
            self.run = self.db.execute(
                'INSERT INTO runs (domain, started) VALUES (?, ?)',
                (domain, time.time())).lastrowid
        self.rows = {}
        for stage, key, state, reasons, dep, progress, stalled, runs, last \
                in self.db.execute(
                    'SELECT stage, key, state, reasons, depth, progress, '
                    'stalled, runs, last_run FROM tasks WHERE domain=?',
                    (domain,)):
            self.rows[stage, key] = {
                'state': state, 'reasons': json.loads(reasons),
                'depth': json.loads(dep), 'progress': progress,
                'stalled': bool(stalled), 'runs': runs, 'last_run': last}
        self.searched = {}
        self.staged = {}

    def row(self, stage, key):
        return self.rows.get((stage, key))

    def _higher(self, row, budgets):
        return any(self.depth.get(b, 0) > row['depth'].get(b, 0)
                   for b in budgets)

    def pending(self, stage, key):
        """NEW: the task was not searched. RETRY: this run can take it
        further. None: it is complete, or its limits are not higher."""
        row = self.rows.get((stage, key))
        if row is None:
            return NEW
        if (stage, key) in self.searched:
            return None
        if self.reopen:
            return RETRY
        if row['state'] == 'complete':
            return None
        # A known replacement is a reusable seed, not a newly proved
        # candidate. New coverage can free slots or cover a previously
        # undecided proof even at the same quota and solver timeout.
        # Do not put knowledge in the domain: that would discard completed
        # searches and unrelated term/solver checkpoints as it grows.
        if set(row['reasons']) & {'candidates', 'proofs', 'unknown'} and \
                row['depth'].get('knowledge_sha') != self.depth.get('knowledge_sha'):
            return RETRY
        for r in row['reasons']:
            if r == 'proofs' and row['stalled']:
                if self._higher(row, STALLED):
                    return RETRY
            elif not REASONS[r] or self._higher(row, REASONS[r]):
                return RETRY
        return None

    def order(self, stage, tasks, key_of):
        """The tasks of ``tasks`` that this run searches, in the order of
        the search: the new tasks in the order that they have, then the
        other tasks, least searched first."""
        new, retry = [], []
        for t in tasks:
            p = self.pending(stage, key_of(t))
            if p == NEW:
                new.append(t)
            elif p == RETRY:
                row = self.rows[stage, key_of(t)]
                retry.append((row['runs'], row['last_run'], len(retry), t))
        return new, [t for *_, t in sorted(retry, key=lambda r: r[:3])]

    def record(self, stage, key, reasons=(), progress=0, result=None):
        """The search of a task in this run. ``reasons`` (keys of REASONS)
        say why it is not complete; ``progress`` counts what the search
        decided; ``result`` (JSON) is what later stages read."""
        reasons = sorted(set(reasons))
        assert all(r in REASONS for r in reasons), reasons
        old = self.rows.get((stage, key))
        stalled = bool(
            'proofs' in reasons and old is not None and
            'proofs' in old['reasons'] and not self.reopen and
            progress <= old['progress'] and
            not self._higher(old, STALLED))
        row = {'state': 'partial' if reasons else 'complete',
               'reasons': reasons, 'depth': dict(self.depth),
               'progress': progress, 'stalled': stalled,
               'runs': (old['runs'] if old else 0) + 1,
               'last_run': self.run}
        self.rows[stage, key] = row
        self.searched[stage, key] = row['state']
        self.staged[stage, key] = result

    def defer(self, stage, key, reason):
        """A task whose final proof/publication is still pending."""
        row = self.rows[stage, key]
        row['state'] = self.searched[stage, key] = 'partial'
        row['reasons'] = sorted(set(row['reasons']) | {reason})

    def commit(self):
        """Publish checkpoints only after the coordinator saved the rules.

        A failed process before this transaction leaves the old agenda intact.
        If rule publication succeeded but this transaction did not, replay is
        harmless: the catalog and proof cache already contain the results.
        close() never commits staged state.
        """
        with self.db:
            for (stage, key), result in self.staged.items():
                row = self.rows[stage, key]
                self.db.execute(
                    'INSERT OR REPLACE INTO tasks VALUES '
                    '(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)',
                    (self.domain, stage, key, row['state'],
                     json.dumps(row['reasons']), json.dumps(row['depth'], sort_keys=True),
                     row['progress'], int(row['stalled']), row['runs'], self.run,
                     None if result is None else json.dumps(result)))
        self.staged.clear()

    def result(self, stage, key):
        if (stage, key) in self.staged:
            return self.staged[stage, key]
        r = self.db.execute(
            'SELECT result FROM tasks WHERE domain=? AND stage=? AND key=?',
            (self.domain, stage, key)).fetchone()
        return None if r is None or r[0] is None else json.loads(r[0])

    def summary(self, stage, keys):
        """The state of the tasks ``keys`` of a stage after this run."""
        out = {'tasks': 0, 'complete': 0, 'not_searched': 0,
               'open': 0, 'closed_at_this_depth': 0,
               'searched_in_this_run': 0, 'completed_in_this_run': 0,
               'reasons': {}}
        for key in set(keys):
            out['tasks'] += 1
            row = self.rows.get((stage, key))
            if row is None:
                out['not_searched'] += 1
                continue
            if (stage, key) in self.searched:
                out['searched_in_this_run'] += 1
                out['completed_in_this_run'] += row['state'] == 'complete'
            if row['state'] == 'complete':
                out['complete'] += 1
                continue
            for r in row['reasons']:
                out['reasons'][r] = out['reasons'].get(r, 0) + 1
            # Open: a later run with the same budgets searches it again.
            searched, self.searched = self.searched, {}
            again = self.pending(stage, key) is not None and \
                not self.reopen
            self.searched = searched
            out['open' if again else 'closed_at_this_depth'] += 1
        out['reasons'] = dict(sorted(out['reasons'].items()))
        return out

    def close(self):
        self.db.close()
