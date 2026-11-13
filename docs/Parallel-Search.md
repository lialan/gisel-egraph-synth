# Multiprocess rule search

`synth` and `mine` default to 16 search processes plus one additional slow
proof process. `--search-jobs N` controls process tasks for enumeration and concrete proofs,
rule generalization, final guard proofs, joint regions and sibling regions.
The coordinator alone deduplicates rule families and publishes the library.
The generated rules still require the existing proofs and emission checks.

```sh
python tools/gisel-rule-synth/gi-rule-synth.py synth corpus.jsonl \
  --search-jobs 16 --slow-jobs 1 --search-batch 32 \
  --regions --siblings -o rules.json
```

For `mine`, these defaults can be overridden in the `search` configuration:

```json
{"search": {"search_jobs": 16, "slow_jobs": 1, "search_batch": 32}}
```

The top-level `mine.jobs` continues to control compiler processes. It does
not control the core search. Hybrid e-graph candidate ingestion and rule
composition still run in the coordinator; this change parallelizes the
semantics-driven search and its region pipeline.

## Scheduling and merging

Discovery uses fixed batches of instances with the same search signature.
A batch reuses its term banks and counterexamples. Its size and order do
not depend on the worker count. Generalization assigns every occurrence
of a canonical source/replacement class to the same task, retaining the
original occurrence order and support accounting. Final guard selection
keeps potentially dominating source patterns together. Region and sibling
families also have one task owner. A duplicate family at merge is an error,
not an arbitrary overwrite. Results merge in task order, regardless of
completion order.

Workers use `spawn`, independent solver contexts and independent SQLite
connections. A WAL proof store shares only SAT/UNSAT conclusions. Logical
query budgets count same-run cache hits too, so another worker winning a
cache race does not grant extra queries. A snapshot of proof keys at run
start makes previous-run proofs free, letting bounded searches advance
across runs. Physical solver calls and cache hits are
reported separately for each lane and stage.

## Slow proofs

There are `N` fast processes plus `--slow-jobs` additional processes. A
fast task that encounters UNKNOWN is replayed in the separate slow queue
with its completed proofs reused. Fast tasks never perform the long inline
retry. A replay repeats the task, not a live solver continuation; enumeration
may therefore repeat. Slow retries can overlap later fast work in the same
stage. Stages have barriers before their dependent work begins.

The defaults are 10 seconds per fast query, 120 seconds per slow query,
300 seconds per slow task and 3600 seconds of reserved slow-task allowances.
Use `--timeout-ms`, `--slow-timeout-ms`, `--slow-budget-s`, and
`--slow-total-s` to change these limits. Admission reserves the task's entire
allowance in stable task order; unused reservations are not reclaimed.
This is conservative but prevents completion order from choosing which
families receive the limited retries. `--slow-total-s 0` disables retries.

UNKNOWN attempts are recorded only for this invocation. Repeating the
same obligation at the same or a smaller timeout is avoided; a larger
allowance can retry it. UNKNOWN is never stored as a proof. A global wall
deadline also bounds worker solver deadlines. If the deadline interrupts a
slow replay, the coordinator retains its fast result. A final guard that
cannot be proved remains ineligible for emission. Worker exceptions fail
the run before the new library is published.

## Reproducibility and limits

`--search-jobs 0` explicitly selects the original serial scheduler.
`--search-jobs 1` is the single-process reference for the new task plan.
Compare 1 and N with identical corpus, knowledge, seed, batch size, and
budgets. Fixed batches have task-local counterexamples; the old scheduler
shares state for longer, so changing from 0 to 1 is also a search-scheduling
change and need not preserve every bounded heuristic decision.

Worker count does not change task boundaries, query budgets or merge order.
Wall-clock timeouts can still vary with machine load. Inspect
`parallel.incomplete` and the per-stage fast/slow metrics in `rules.stats.json`
before interpreting a run as a completed comparison. The persistent queue
distinguishes work still open at the same budget from work closed until a
limiting budget increases. `mine` uses this queue and final-guard failures
to decide whether a search remains incomplete. The overall enumeration remains
bounded; completion does not mean exhaustive search.

Persistent SAT/UNSAT history, learned rules and the task queue are reused
in both serial and process mode. `max_instances`/`max_pairs` count pending
tasks. Known root rules seed multi-output discovery; `--multi-share 0.3`
reserves an initial portion of a timed run for those earlier tasks, with
stage deadlines passed to both worker pools.

Only the coordinator writes checkpoints. It first stages completed tasks in
memory, publishes the output catalog, learned catalog and referenced proofs,
then commits all task rows in one SQLite transaction. An interrupted run
before commit replays work; after commit it can reuse the published rules.
Publication errors and worker exceptions cannot leave completed tasks without
their rules. A cache-directory lock serializes coordinators sharing that
cache, while all search workers remain parallel. Partial term banks are
rebuilt on restart. Process interruption tests cover termination before/after
catalog publication, mid-transaction rollback and post-commit restart.

Default generated files and target selections are unchanged by this queue.

## Replay a timing experiment

```sh
python tools/gisel-rule-synth/eval_parallel.py corpus.jsonl \
  --out build/validation/parallel-benchmark --jobs 1 8 --repeats 2 \
  --regions --siblings
```

Each measured invocation starts with an empty proof cache and empty known
catalog. Runs execute sequentially, alternating their order between repeats.
The report saves commands, corpus hash, external wall time, phase timings,
full rule hashes, semantic revision hashes and hashes of emitted TableGen/C++.
`--jobs 0 1 8` also records the legacy scheduler for a separate comparison.

See [Parallel-Search-Validation.md](Parallel-Search-Validation.md) for the
measured speedup and result-equivalence checks on nod.
