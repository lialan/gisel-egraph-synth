"""Deterministic process tasks for discovery and proof generalization.

Workers never publish a library. Task boundaries, input order, and slow-lane
admission do not depend on the number or completion order of workers. SAT and
UNSAT history is shared; UNKNOWN is only a run-local attempt, never a proof.
The coordinator alone merges rule families and publishes the result.
"""

import collections
import contextlib
import concurrent.futures as futures
import copy
import multiprocessing
import os
import tempfile
import time

from . import discover, history, ir, known, region, sibling, smt, synth, vector
from . import vector_search


def add_stats(dst, src):
    for k, v in src.items():
        if isinstance(v, dict):
            add_stats(dst.setdefault(k, {}), v)
        elif isinstance(v, list):
            dst.setdefault(k, []).extend(v)
        elif isinstance(v, (int, float)):
            dst[k] = dst.get(k, 0) + v


def batches(insts, size):
    """Fixed signature batches, including their original corpus positions."""
    groups = collections.OrderedDict()
    for n, inst in enumerate(insts):
        key = repr(discover.signature(inst))
        groups.setdefault(key, []).append((n, inst))
    out = [g[i:i + size] for g in groups.values()
           for i in range(0, len(g), size)]
    return sorted(out, key=lambda g: g[0][0])


def candidate_key(inst, tgt):
    src, tgt, vw, _, perm = synth.canonicalize(
        inst.expr, tgt, inst.vw, inst.facts)
    cv = tuple(n for n, old in enumerate(perm) if old in inst.const_vars)
    return synth.class_key(src, tgt, vw, cv)


def sibling_key(pair):
    # A deliberately coarse source-only partition: widths, commutation,
    # variable names and sibling ordering cannot split a rule family.
    return tuple(sorted(n[0] for e in [pair.inst.expr] + list(pair.sibs)
                        for n in ir.nodes(e)))


def merge_state(sy, state):
    """Families are owned by one task; never silently overwrite a collision."""
    for attr in ('rules', 'by_key', 'rejected'):
        dest = getattr(sy, attr)
        for k, v in state.get(attr, {}).items():
            if k in dest:
                raise ValueError('parallel family partition collision: %s' % k)
            dest[k] = v
    add_stats(sy.stats, state.get('synthesis', {}))


_CONFIG = None


def _initialize(config):
    global _CONFIG
    _CONFIG = config


class TaskBackend(smt.Z3Backend):
    def __init__(self, config, slow, budget):
        super().__init__(config['timeout_ms'])
        self.slow = slow
        self.fast_timeout_ms = config['timeout_ms']
        self.unknown = 0
        self.pending = set()
        self.actual_calls = 0
        self.skipped_unknown = 0
        self.deadline = config['deadline']
        if slow:
            end = time.monotonic() + budget
            self.deadline = min(self.deadline, end) if self.deadline else end
        self.history = history.Proofs(config['cache'], config['semantics'])
        # Only this invocation uses these attempts. They are not conclusions
        # and cannot leak across solver versions or independent CLI runs.
        self.attempts = history.Proofs(config['attempts'], config['semantics'])
        self.attempts.db.execute(
            'CREATE TABLE IF NOT EXISTS unknown_attempts '
            '(key TEXT PRIMARY KEY, timeout_ms INTEGER NOT NULL)')

    @contextlib.contextmanager
    def limit(self, timeout_ms, budget_s):
        # Final guard verification must also leave long checks to the slow lane.
        if not self.slow:
            timeout_ms = min(timeout_ms, self.fast_timeout_ms)
        with super().limit(timeout_ms, budget_s):
            yield

    def check(self, formula, want_model_of=None):
        # Logical query budgets must not depend on which other process won
        # a cache race. Keep physical solver calls as a separate metric.
        self.calls += 1
        key = self.history.key(formula, want_model_of)
        hit = self.history.get(key)
        if hit is not None:
            self.pending.discard(key)
            return hit
        row = self.attempts.db.execute(
            'SELECT timeout_ms FROM unknown_attempts WHERE key=?',
            (key,)).fetchone()
        if row and row[0] >= self.timeout_ms:
            self.unknown += 1
            self.pending.add(key)
            self.skipped_unknown += 1
            return smt.Result('unknown')
        allowance = self._time_left_ms()
        logical = self.calls
        result = self._check(formula, want_model_of)
        self.actual_calls += self.calls - logical
        self.calls = logical
        self.history.put(key, result)
        if result.status == 'unknown':
            self.unknown += 1
            self.pending.add(key)
            with self.attempts.db:
                self.attempts.db.execute(
                    'INSERT INTO unknown_attempts VALUES (?, ?) '
                    'ON CONFLICT(key) DO UPDATE SET timeout_ms='
                    'MAX(timeout_ms, excluded.timeout_ms)',
                    (key, allowance))
        else:
            self.pending.discard(key)
        return result

    def close(self):
        self.history.close()
        self.attempts.close()


class FastSynthesizer(synth.Synthesizer):
    def _slow(self, key, fn):
        # Leave the ordinary proof pending. The entire canonical family is
        # replayed in the slow lane, using its already decided proof history.
        # Lambdas and live Z3 contexts never cross a process boundary.
        return None


def _discover(data, config, backend, ctx):
    rows = []
    for idx, inst in data:
        if backend.deadline and time.monotonic() >= backend.deadline:
            break
        log = {}
        if vector.has_vector(inst.vw, inst.expr):
            cands, st = vector_search.search(
                inst, backend, vector_search.Limits.of(ctx.limits),
                ctx.limits, ctx, log)
        else:
            cands, st = discover.discover(inst, backend, ctx.limits, ctx, log)
        # Only plain expressions and records cross the process boundary.
        cands = [{k: v for k, v in c.items() if k != 'proof'} for c in cands]
        alternatives = []
        if config['regions'] and not vector.has_vector(inst.vw, inst.expr):
            have = {c['tgt'] for c in cands}
            for alt in region.root_alternatives(inst, ctx.limits, ctx):
                if alt not in have and discover.prove_concrete(
                        inst, alt, backend).status == 'unsat':
                    alternatives.append(alt)
        rows.append((idx, {'cands': cands, 'stats': st, 'log': log,
                           'alternatives': alternatives}))
    return {'rows': rows}


def _execute(task, slow=False, budget=0):
    kind, data = task
    c = _CONFIG
    start = time.monotonic()
    backend = TaskBackend(c, slow, budget)
    if slow:
        # Later widths can be UNKNOWN even when the first width is valid;
        # that does not trigger Synthesizer._slow. Retry every query here.
        backend.timeout_ms = c['slim'].slow_timeout_ms
    try:
        limits = copy.copy(c['dlim'])
        limits.deadline = backend.deadline
        ctx = discover.Context(limits)
        ctx.known = known.Index(c['knowledge']) if c['use_known'] else None
        slim = copy.copy(c['slim'])
        slim.slow_total_s = budget if slow else 0
        sy = (synth.Synthesizer if slow else FastSynthesizer)(
            backend, slim, proof_dir=c['proofs'])
        sy.known = ctx.known
        if kind == 'discover':
            out = _discover(data, c, backend, ctx)
        elif kind == 'generalize':
            ids = []
            for token, inst, tgt, provenance in data:
                ids.append((token, sy.add(inst, tgt, provenance)))
            out = {'ids': ids}
        elif kind == 'finalize':
            rules, insts, preserve = data
            sy.rules = {r['id']: r for r in rules}
            out = {'stats': sy.finalize(insts, preserve_alternatives=preserve)}
        elif kind == 'region':
            base, pending = data
            sy.rules[base['id']] = base
            out = {'stats': region.extend(sy, pending, backend, limits, ctx)}
            del sy.rules[base['id']]
        elif kind == 'sibling':
            pairs, found = data
            out = {'stats': sibling.extend(sy, pairs, found, backend,
                                           limits, ctx)}
        else:
            raise ValueError('unknown search task: ' + kind)
        out.update(rules=sy.rules, by_key=sy.by_key, rejected=sy.rejected,
                   synthesis=sy.stats, enumeration=ctx.stats(),
                   retry=bool(backend.pending),
                   deadline=bool(backend.deadline and
                                 time.monotonic() >= backend.deadline),
                   metrics={'solver_calls': backend.calls,
                            'physical_solver_calls': backend.actual_calls,
                            'solver_seconds': backend.seconds,
                            'proof_cache_hits': backend.history.hits,
                            'proof_cache_stored': backend.history.stored,
                            'unknown': backend.unknown,
                            'unknown_replays_avoided': backend.skipped_unknown,
                            'task_seconds': time.monotonic() - start,
                            'tasks': 1})
        return out
    finally:
        backend.close()


class Session:
    """A bounded fast queue and an independent slow-proof process pool."""
    def __init__(self, args):
        self.args = args
        self.fast = self.slow = None
        self.temp = tempfile.TemporaryDirectory(prefix='girs-search-')
        self.metrics = {'stages': {}, 'slow_admitted': 0,
                        'slow_not_admitted': 0, 'incomplete': False}
        self.enumeration = {}
        self.seconds = {}

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        for pool in (self.fast, self.slow):
            if pool is not None:
                pool.shutdown(wait=True, cancel_futures=bool(exc[0]))
        self.temp.cleanup()

    def configure(self, dlim, slim, knowledge, use_known, deadline):
        a = self.args
        cache = a.cache or os.path.join(self.temp.name, 'proofs')
        attempts = os.path.join(self.temp.name, 'attempts')
        semantics = known.semantics_sha()
        # Initialize WAL before workers open connections concurrently.
        for path in (cache, attempts):
            h = history.Proofs(path, semantics)
            h.close()
        slim = copy.copy(slim)
        slim.slow_timeout_ms = a.slow_timeout_ms
        slim.slow_budget_s = a.slow_budget_s
        self.slow_left = a.slow_total_s
        self.config = dict(dlim=dlim, slim=slim, knowledge=knowledge,
                           use_known=use_known, deadline=deadline,
                           timeout_ms=a.timeout_ms, semantics=semantics,
                           cache=cache, attempts=attempts, proofs=a.proofs,
                           regions=a.regions)
        # spawn never inherits a live solver or SQLite connection.
        mp = multiprocessing.get_context('spawn')
        self.fast = futures.ProcessPoolExecutor(
            a.search_jobs, mp_context=mp, initializer=_initialize,
            initargs=(self.config,))
        self.slow = futures.ProcessPoolExecutor(
            a.slow_jobs, mp_context=mp, initializer=_initialize,
            initargs=(self.config,))

    def map(self, kind, items):
        items = list(items)
        if not items:
            return []
        start = time.monotonic()
        out, pending, ready = {}, {}, {}
        submitted = release = 0
        metrics = self.metrics['stages'].setdefault(kind, {})
        deadline = self.config['deadline']
        # A fixed per-task slow allowance is charged at admission, not in
        # completion order. Worker speed/count cannot decide who gets a retry.
        while submitted < len(items) or pending:
            expired = deadline is not None and time.monotonic() >= deadline
            while not expired and submitted < len(items) and sum(
                    lane == 'fast' for _, lane in pending.values()) < \
                    2 * self.args.search_jobs:
                f = self.fast.submit(_execute, (kind, items[submitted]))
                pending[f] = (submitted, 'fast')
                submitted += 1
            if expired:
                self.metrics['incomplete'] = True
                submitted = len(items)
            if not pending:
                break
            done, _ = futures.wait(pending, return_when=futures.FIRST_COMPLETED)
            for f in done:
                idx, lane = pending.pop(f)
                result = f.result()  # Worker errors fail the run, not a rule.
                add_stats(metrics.setdefault(lane, {}), result['metrics'])
                if lane == 'fast':
                    ready[idx] = result
                    out[idx] = result
                else:
                    # A partial retry must not discard a completed fast result.
                    if not result['deadline']:
                        out[idx] = result
                    self.metrics['incomplete'] |= result['deadline']
            # Stable admission even when fast tasks finish out of order.
            expired = deadline is not None and time.monotonic() >= deadline
            while release in ready:
                result = ready.pop(release)
                if result['retry']:
                    budget = min(self.args.slow_budget_s, self.slow_left)
                    if budget > 0 and not expired and \
                            self.args.slow_timeout_ms > self.args.timeout_ms:
                        self.slow_left -= budget
                        f = self.slow.submit(_execute, (kind, items[release]),
                                             True, budget)
                        pending[f] = (release, 'slow')
                        self.metrics['slow_admitted'] += 1
                    else:
                        self.metrics['slow_not_admitted'] += 1
                        self.metrics['incomplete'] = True
                release += 1
        results = [out[i] for i in sorted(out)]
        self.metrics['incomplete'] |= any(r['retry'] or r['deadline']
                                           for r in results)
        for result in results:
            add_stats(self.enumeration, result['enumeration'])
        self.seconds[kind] = time.monotonic() - start
        metrics['input_tasks'] = len(items)
        metrics['returned_tasks'] = len(results)
        return results

    def search(self, insts, sy):
        rows = {}
        for result in self.map('discover', batches(insts, self.args.search_batch)):
            rows.update(result['rows'])
        groups = collections.OrderedDict()
        for idx in sorted(rows):
            row = rows[idx]
            row['rids'] = [None] * len(row['cands'])
            row['alt_ids'] = [None] * len(row['alternatives'])
            for alt, candidates in ((False, row['cands']),
                                    (True, [{'tgt': t} for t in row['alternatives']])):
                for j, c in enumerate(candidates):
                    inst = copy.copy(insts[idx])
                    if c.get('const_vars'):
                        inst.const_vars = tuple(c['const_vars'])
                    provenance = ({'discovery': 'joint-region-alternative+smt'}
                                  if alt else
                                  {'discovery': 'vector-search-%s+smt' % c['family']}
                                  if c.get('family') else None)
                    key = candidate_key(inst, c['tgt'])
                    groups.setdefault(key, []).append(
                        ((idx, alt, j), inst, c['tgt'], provenance))
        for result in self.map('generalize', groups.values()):
            merge_state(sy, result)
            for (idx, alt, j), rid in result['ids']:
                rows[idx]['alt_ids' if alt else 'rids'][j] = rid
        return rows

    def finalize(self, sy, insts, preserve):
        # Candidates that can dominate each other have identical source
        # opcode multisets. Coverage still sees every corpus instance.
        groups = collections.OrderedDict()
        for rule in sy.rules.values():
            key = tuple(sorted(n[0] for n in ir.nodes(
                ir.from_json(rule['source_json']))))
            groups.setdefault(key, []).append(rule)
        stats, rules = {}, {}
        for result in self.map('finalize', [(g, insts, preserve)
                                           for g in groups.values()]):
            add_stats(stats, result['stats'])
            for rid, rule in result['rules'].items():
                if rid in rules:
                    raise ValueError('finalization family collision: ' + rid)
                rules[rid] = rule
        # A task that never reached final proof cannot publish its rules.
        sy.rules = rules
        return stats

    def regions(self, sy, pending):
        groups = collections.OrderedDict()
        for inst, tgt, rid in pending:
            if rid in sy.rules:
                groups.setdefault(rid, []).append((inst, tgt, rid))
        stats = {}
        for result in self.map('region', [(sy.rules[rid], group)
                                         for rid, group in groups.items()]):
            merge_state(sy, result)
            add_stats(stats, result['stats'])
        return stats

    def siblings(self, sy, pairs, found, max_pairs):
        groups = collections.OrderedDict()
        chosen = pairs[:max_pairs] if max_pairs else pairs
        for pair in chosen:
            groups.setdefault(sibling_key(pair), []).append(pair)
        stats = {'not_searched': len(pairs) - len(chosen)}
        tasks = [(g, {p.base_key: found.get(p.base_key, ()) for p in g})
                 for g in groups.values()]
        for result in self.map('sibling', tasks):
            merge_state(sy, result)
            add_stats(stats, result['stats'])
        return stats
