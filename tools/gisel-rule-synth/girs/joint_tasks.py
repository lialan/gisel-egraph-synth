"""The joint region search (girs/joint.py) as tasks of the agenda.

Each canonical window is one task of the agenda of the single-output search
(girs/agenda.py), in a stage of its own, with the proof history
(girs/history.py) and the process backend (girs/parallel.TaskBackend) of
that search. There is no other database and no other recovery protocol:

  agenda      <cache>/agenda.sqlite3, stage 'joint': per window its state
              (complete / partial), why it is partial (joint.REASONS), the
              budgets it had, and its result (the decided and the pending
              candidates, joint.search_window)
  proofs      <cache>/proofs.sqlite3: SAT and UNSAT of each query, shared
              by every process; UNKNOWN is only an attempt of this run
  rule store  <cache>/joint/<domain>/rules/<id>.json and proofs/*.smt2:
              the verified rules of a domain

A run takes the windows that have no row first, then the windows that it
can take further: the reason of a partial window says which budget it
needs (more time per window, more terms, more proofs, ...). A window whose
search is complete and that only has pending candidates is not searched
again: its candidates are proved ('prove' mode). Decided candidates are
never proved again, and do not use the proof budget of a later run.

Commit order (as cmd_synth): the rules of a result are written to the
rule store first (each file atomically), then the agenda records the task;
the agenda is committed at checkpoints and at the end. A run that stops
(an interrupt, a failed worker) commits what it published; a task without
a committed row is searched again, and its proofs come from the history.

Identity. The domain of the rows is the semantic model of the joint proofs
(semantics_sha: the operator model of known.semantics_sha, the record
schema and the functions of joint.py that make formulas, guards and plans),
the search code (known.search_sha and JOINT_SEARCH_VERSION) and the limits
that decide which candidates exist (window size, outputs, costs, grammar,
samples, seed, the cost policy). The budgets (BUDGETS) are the depth of a
search inside one domain. A new domain has no rows: every window is new,
and proofs whose query did not change come from the history.

Time budgets (time_s per window, the deadline of a run) depend on the
load of the machine: a run with them is not reproducible bit for bit.
With budgets that never end the search (time_s large), the rules do not
depend on the number of processes: each window is searched alone, and a
term bank depends only on its key and on max_terms / max_evals.
"""

import concurrent.futures as futures
import inspect
import json
import multiprocessing
import os
import resource
import signal
import tempfile
import time

from . import agenda, history, joint, known, parallel

STAGE = 'joint'
# Raised when the search proposes other candidates for the same limits
# (a change of joint.Search that is not a change of the proof model).
JOINT_SEARCH_VERSION = 1
# The budgets of the search of a window: its depth in the agenda.
BUDGETS = ('time_s', 'max_terms', 'max_evals', 'max_helpers', 'max_combos',
           'max_cands', 'max_proofs', 'timeout_ms', 'semantic_variants')
# Neither domain nor depth: the memory of a process.
NOT_LIMITS = ('max_banks',)
# A partial window with the reason 'proofs' that decided no more candidates
# than before needs one of these higher.
STALLED = ('max_proofs', 'timeout_ms')


def semantics_sha():
    """The proof model of the joint rules: if it changes, no row and no
    stored rule of the old model is reused (the history keeps the queries
    that did not change)."""
    fns = (joint.evaluate, joint.guards, joint.support, joint.target_reads,
           joint.relaxed, joint.classes, joint.literal, joint.width_maps,
           joint.formula, joint.prove, joint.flag_poison,
           joint.ssa_definitions, joint.joint_violation, joint.plan,
           joint.non_decreasing, joint.plan_json, joint.candidate_json,
           joint.check_rule, joint.max_after_of)
    return known.digest([known.semantics_sha(), joint.SCHEMA,
                         [inspect.getsource(f) for f in fns]])


def domain(limits):
    d = {k: v for k, v in limits.identity().items()
         if k not in BUDGETS + NOT_LIMITS}
    return known.digest(['joint', semantics_sha(), known.search_sha(),
                         JOINT_SEARCH_VERSION, d])


def depth(limits):
    return {k: getattr(limits, k) for k in BUDGETS}


class JointAgenda(agenda.Agenda):
    """The agenda with the reasons of the joint search (joint.REASONS).
    agenda.py itself is not changed: it is part of known.search_sha, which
    keys the rows of the single-output search."""

    def pending(self, stage, key):
        row = self.rows.get((stage, key))
        if row is None:
            return agenda.NEW
        if (stage, key) in self.searched:
            return None
        if self.reopen:
            return agenda.RETRY
        if row['state'] == 'complete':
            return None
        for r in row['reasons']:
            if r == 'proofs' and row['stalled']:
                if self._higher(row, STALLED):
                    return agenda.RETRY
            elif not joint.REASONS[r] or self._higher(row, joint.REASONS[r]):
                return agenda.RETRY
        return None

    def searchable(self, stage, key):
        """True if the search of the window (not only its proofs) can go
        further in this run."""
        row = self.rows.get((stage, key))
        if row is None or self.reopen:
            return True
        return any(not joint.REASONS[r] or self._higher(row, joint.REASONS[r])
                   for r in row['reasons'] if r in joint.SEARCH_REASONS)

    def record(self, stage, key, reasons=(), progress=0, result=None):
        reasons = sorted(set(reasons))
        assert all(r in joint.REASONS for r in reasons), reasons
        old = self.rows.get((stage, key))
        stalled = bool(
            'proofs' in reasons and old is not None and
            'proofs' in old['reasons'] and not self.reopen and
            progress <= old['progress'] and not self._higher(old, STALLED))
        row = {'state': 'partial' if reasons else 'complete',
               'reasons': reasons, 'depth': dict(self.depth),
               'progress': progress, 'stalled': stalled,
               'runs': (old['runs'] if old else 0) + 1,
               'last_run': self.run}
        self.rows[stage, key] = row
        self.searched[stage, key] = row['state']
        self.staged[stage, key] = result


class Store:
    """The verified joint rules of a domain. A rule is published (its proof
    files, then its record, each written atomically) before the agenda
    commits its task."""

    def __init__(self, directory):
        self.dir = directory
        os.makedirs(os.path.join(directory, 'rules'), exist_ok=True)
        os.makedirs(os.path.join(directory, 'proofs'), exist_ok=True)
        self.written = 0

    def _atomic(self, path, text):
        fd, tmp = tempfile.mkstemp(dir=os.path.dirname(path), prefix='.tmp-')
        try:
            with os.fdopen(fd, 'w') as f:
                f.write(text)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp, path)
        finally:
            if os.path.exists(tmp):
                os.remove(tmp)

    def put(self, rule):
        rule = json.loads(json.dumps(rule))
        rule.pop('_key', None)
        for pr in rule['proofs']:
            text = pr.pop('smt2', None)
            if text is not None:
                h = known.digest(text)[:16]
                path = os.path.join(self.dir, 'proofs', h + '.smt2')
                if not os.path.exists(path):
                    self._atomic(path, text)
                pr['smt2_file'] = 'proofs/%s.smt2' % h
        self._atomic(os.path.join(self.dir, 'rules', rule['id'] + '.json'),
                     json.dumps(rule, indent=1, sort_keys=True) + '\n')
        self.written += 1

    def get(self, rid):
        path = os.path.join(self.dir, 'rules', rid + '.json')
        if not os.path.exists(path):
            return None
        with open(path) as f:
            return json.load(f)


# ------------------------------------------------------------- workers ---

_W = {}


def _initialize(config):
    _W.clear()
    _W['config'] = config
    _W['ctx'] = joint.new_context(config['limits'])
    # A worker stops between windows on an interrupt; the coordinator
    # decides what to commit.
    signal.signal(signal.SIGINT, signal.SIG_IGN)


def _execute(task):
    """One window: (index, key, window, provenance, prior, mode, released)."""
    idx, key, win, prov, prior, mode, released = task
    c = _W['config']
    backend = parallel.TaskBackend(c, slow=False, budget=0)
    start = time.monotonic()
    try:
        out = joint.search_window(key, win, prov, c['limits'], _W['ctx'],
                                  backend, prior=prior, mode=mode,
                                  deadline=c['deadline'],
                                  released=set(released))
        out.pop('indep', None)
        out['reasons'] = sorted(out['reasons'])
        out['metrics'] = {
            'solver_calls': backend.calls,
            'physical_solver_calls': backend.actual_calls,
            'solver_seconds': backend.seconds,
            'proof_cache_hits': backend.history.hits,
            'unknown': backend.unknown,
            'unknown_replays_avoided': backend.skipped_unknown,
            'task_seconds': time.monotonic() - start,
            'peak_rss_mb': resource.getrusage(
                resource.RUSAGE_SELF).ru_maxrss // 1024}
        out['index'] = idx
        return out
    finally:
        backend.close()


def _prepare_history(cache, attempts, semantics):
    """The proof history and the attempts of this run (as
    parallel.Session.configure): the proofs before this run are free."""
    for path in (cache, attempts):
        history.Proofs(path, semantics).close()
    h = history.Proofs(attempts, semantics)
    h.db.execute('CREATE TABLE IF NOT EXISTS prior_proofs '
                 '(key TEXT PRIMARY KEY)')
    h.db.execute('ATTACH DATABASE ? AS previous',
                 (os.path.join(cache, 'proofs.sqlite3'),))
    with h.db:
        h.db.execute('INSERT OR IGNORE INTO prior_proofs '
                     'SELECT key FROM previous.proofs')
    h.close()


# --------------------------------------------------------- scheduling ---

def load_feedback(path):
    """The measured profitability of rules (eval/joint_measure.py
    selection): (rule id -> status, window -> measured gain)."""
    if not path:
        return {}, {}
    with open(path) as f:
        sel = json.load(f)
    status, gain = {}, {}
    for rid, info in sel.get('candidates', {}).items():
        status[rid] = info.get('profitability_status', 'unmeasured')
        w = info.get('window')
        if w is not None:
            g = info.get('marginal', {}).get('insns_saved', 0) or 0
            gain[w] = max(gain.get(w, 0), g)
    return status, gain


# Measured without a gain: a later run does not count them in the quota of
# their window, so that it proves other shapes there.
RELEASED = ('no_gain', 'regression')


def schedule(new, retry, gain, explore=0.25):
    """The order of the tasks: without feedback, the new windows first (in
    their order: the most frequent first), then the others, least searched
    first (agenda.order). With feedback, the windows whose rules have a
    measured gain come first, largest gain first; one place of every
    1/explore goes to a window without a measurement, so that the
    measurement does not decide everything."""
    if not gain:
        return new + retry
    rest = [t for t in new + retry if gain.get(t[2], 0) <= 0]
    best = sorted((t for t in new + retry if gain.get(t[2], 0) > 0),
                  key=lambda t: -gain[t[2]])
    period = max(2, round(1 / explore)) if explore > 0 else 0
    out = []
    while best or rest:
        if rest and (not best or (period and len(out) % period ==
                                  period - 1)):
            out.append(rest.pop(0))
        else:
            out.append(best.pop(0))
    return out


# --------------------------------------------------------- coordinator ---

def run(instances, limits, cache=None, jobs=1, time_budget_s=None,
        reopen=False, feedback=None, checkpoint_s=60.0, log=None,
        max_tasks=None):
    """Searches the windows ``instances`` (key -> (window, provenance), in
    the order of the search) as tasks. Returns (rules, records, stats):
    the verified rules of these windows (also of earlier runs), a record
    per window, and the statistics of the run with the agenda summary."""
    t0 = time.monotonic()
    tmp = tempfile.TemporaryDirectory(prefix='girs-joint-')
    cache = cache or os.path.join(tmp.name, 'cache')
    dom = domain(limits)
    sem = semantics_sha()
    ag = JointAgenda(cache, dom, depth(limits), reopen=reopen)
    store = Store(os.path.join(cache, 'joint', dom[:16]))
    attempts = os.path.join(tmp.name, 'attempts')
    _prepare_history(cache, attempts, sem)
    deadline = t0 + time_budget_s if time_budget_s else None
    status_of, gain = load_feedback(feedback)
    released_ids = {rid for rid, s in status_of.items() if s in RELEASED}
    tasks = []
    for idx, (key, (win, prov)) in enumerate(instances.items()):
        tasks.append((idx, key, joint.window_key(key), win, prov))
    tkey = {t[2]: agenda.task_key(STAGE, t[1]) for t in tasks}
    new, retry = ag.order(STAGE, tasks, lambda t: tkey[t[2]])
    # Refill any slots released by measurement, including a window that
    # still has profitable rules. The old proofs stay in the store.
    queued = {t[2] for t in new + retry}
    for t in tasks:
        if t[2] in queued:
            continue
        row = ag.row(STAGE, tkey[t[2]])
        if row and 'variants' in row['reasons'] and released_ids:
            res = ag.result(STAGE, tkey[t[2]]) or {}
            ver = [i for i, s in res.get('decided', {}).items()
                   if s == 'verified']
            if (set(ver) & released_ids and
                    len(set(ver) - released_ids) < limits.semantic_variants and
                    res.get('pending')):
                retry.append(t)
    order = schedule(new, retry, gain)
    if max_tasks is not None:
        order = order[:max_tasks]
    todo = []
    for idx, key, wk, win, prov in order:
        prior = ag.result(STAGE, tkey[wk])
        mode = 'full' if ag.searchable(STAGE, tkey[wk]) or prior is None \
            else 'prove'
        rel = sorted(i for i in (prior or {}).get('decided', {})
                     if i in released_ids)
        todo.append((idx, key, win, prov, prior, mode, rel))
    stats = joint.new_stats()
    stats.pop('seconds')
    metrics = {}
    records = {}
    done = 0
    last_commit = time.monotonic()
    stop = {'signal': None}

    def on_signal(sig, frame):
        stop['signal'] = sig
    old_handlers = {s: signal.signal(s, on_signal)
                    for s in (signal.SIGINT, signal.SIGTERM)}

    def publish(out):
        nonlocal done
        for r in out['rules']:
            store.put(r)
        wk = out['record']['key']
        ag.record(STAGE, tkey[wk], out['reasons'], out['progress'],
                  out['result'])
        out['record'].pop('_key', None)
        records[wk] = out['record']
        joint.add_window_stats(stats, out)
        # A peak is a maximum, not a sum.
        rss = out['metrics'].pop('peak_rss_mb', 0)
        metrics['peak_rss_mb_worker'] = max(
            metrics.get('peak_rss_mb_worker', 0), rss)
        parallel.add_stats(metrics, out['metrics'])
        done += 1
        if log:
            log('%s %s -> %s' % (out['record']['status'],
                                 out['record']['window'],
                                 ','.join(out['record'].get('verified', []))
                                 or '-'))

    config = {'limits': limits, 'deadline': deadline,
              'timeout_ms': limits.timeout_ms, 'cache': cache,
              'attempts': attempts, 'semantics': sem}
    failed = []
    interrupted = False
    try:
        if jobs <= 1:
            _initialize(config)
            signal.signal(signal.SIGINT, on_signal)
            for t in todo:
                if stop['signal'] or (deadline and time.monotonic() >=
                                      deadline):
                    break
                publish(_execute(t))
                if time.monotonic() - last_commit >= checkpoint_s:
                    ag.commit()
                    last_commit = time.monotonic()
        else:
            mp = multiprocessing.get_context('spawn')
            with futures.ProcessPoolExecutor(
                    jobs, mp_context=mp, initializer=_initialize,
                    initargs=(config,)) as pool:
                pending, submitted = {}, 0
                while submitted < len(todo) or pending:
                    late = deadline and time.monotonic() >= deadline
                    while not stop['signal'] and not late and \
                            submitted < len(todo) and \
                            len(pending) < 2 * jobs:
                        f = pool.submit(_execute, todo[submitted])
                        pending[f] = todo[submitted]
                        submitted += 1
                    if not pending:
                        break
                    if stop['signal']:
                        for f in list(pending):
                            if f.cancel():
                                del pending[f]
                    ready, _ = futures.wait(
                        pending, timeout=5,
                        return_when=futures.FIRST_COMPLETED)
                    for f in ready:
                        t = pending.pop(f)
                        try:
                            out = f.result()
                        except futures.process.BrokenProcessPool:
                            raise
                        except Exception as e:   # the task stays new
                            failed.append((joint.window_key(t[1]),
                                           repr(e)[:300]))
                            continue
                        publish(out)
                    if time.monotonic() - last_commit >= checkpoint_s:
                        ag.commit()
                        last_commit = time.monotonic()
    except futures.process.BrokenProcessPool as e:
        failed.append(('pool', repr(e)[:300]))
    finally:
        # Everything that was published is committed; nothing else.
        ag.commit()
        for s, h in old_handlers.items():
            signal.signal(s, h)
    interrupted = stop['signal'] is not None
    # The rules of all windows of this run, also of the windows that an
    # earlier run decided; a record for each window.
    rules, out_records = [], []
    missing = []
    for idx, key, wk, win, prov in tasks:
        res = ag.result(STAGE, tkey[wk])
        rec = records.get(wk)
        if rec is None:
            row = ag.row(STAGE, tkey[wk])
            rec = {'key': wk, 'window': win.text(),
                   'occurrences': len(prov),
                   'status': 'not searched' if row is None else
                   'earlier run: %s' % row['state'],
                   'reasons': row['reasons'] if row else [],
                   'verified': [i for i, s in (res or {}).get(
                       'decided', {}).items() if s == 'verified']}
        out_records.append(rec)
        ids = [i for i, s in (res or {}).get('decided', {}).items()
               if s == 'verified']
        got = []
        for rid in ids:
            r = store.get(rid)
            if r is None:
                missing.append(rid)
                continue
            if rid in status_of:
                r['profitability_status'] = status_of[rid]
            got.append(r)
        # Cheapest first in each window, the windows in the search order.
        got.sort(key=lambda r: (r['candidate']['estimated_cost']['after'],
                                r['id']))
        rules += got
    # The text of each proof travels with its rule (the store may be a
    # temporary directory).
    for r in rules:
        for pr in r['proofs']:
            if 'smt2_file' in pr:
                with open(os.path.join(store.dir, pr['smt2_file'])) as f:
                    pr['smt2'] = f.read()
    summary = ag.summary(STAGE, tkey.values())
    ag.close()
    tmp.cleanup()
    stats.update(
        tasks=len(tasks), queued=len(todo), searched_in_this_run=done,
        prove_only=sum(1 for r in records.values()
                       if r.get('mode') == 'prove'),
        failed_tasks=failed, interrupted=interrupted,
        deadline_reached=bool(deadline and time.monotonic() >= deadline),
        queue=summary, metrics=metrics, rules_published=store.written,
        rules_total=len(rules), missing_rules=missing,
        domain=dom, semantics_sha=sem, depth=depth(limits),
        wall_seconds=round(time.monotonic() - t0, 2),
        peak_rss_mb_children=resource.getrusage(
            resource.RUSAGE_CHILDREN).ru_maxrss // 1024,
        peak_rss_mb_self=resource.getrusage(
            resource.RUSAGE_SELF).ru_maxrss // 1024)
    return rules, out_records, stats
