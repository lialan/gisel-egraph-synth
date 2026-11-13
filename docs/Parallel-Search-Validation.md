# Multiprocess search validation

Validated on nod (hostname `Shark19`) on 2026-11-12, in
`/home/nod/gisel-parallel-search-20261112`, branch `codex/parallel-search`,
based on latest `origin/main` at task start, `cb362c18d28e2e1c06aa559ac963991a25edec21`.
LLVM remains pinned at `37a1706d0eac1774701a0a44d9fb4fa542f56fde`.
The host has 32 logical CPUs; Python is 3.12.14, Z3 is 5.4.1.

## Timings and equality

The frozen corpus has 515 distinct instances: 512 deterministically sampled
scalar integer instances from the existing discovery corpus and three real
cross-block regression records. No held-out corpus was used. The source
extraction predates this change; the same frozen bytes feed every run.
The corpus SHA256 is `dd7bd09659cbdfbd78bebebaa84c30df58bf71dd40f189c2d3b81ccb547a5141`.

Each run starts with empty knowledge and an empty proof cache. Runs execute
sequentially; the second repeat reverses their order. Search budgets are
identical: RHS cost at most 2, 10,000 bank terms, 1,000,000 evaluations, auto
grammar, and regions/siblings enabled. The process task plan uses batch
size 16. Full commands, input provenance, phase metrics and hashes are in
[Parallel-Search-Validation.json](Parallel-Search-Validation.json).

| Scheduler | First run | Second run | Median |
|---|---:|---:|---:|
| Legacy serial (`--search-jobs 0`) | 42.55 s | 41.49 s | 42.02 s |
| One search process (`--search-jobs 1`) | 74.57 s | 74.58 s | 74.57 s |
| Eight search processes (`--search-jobs 8`) | 21.53 s | 21.25 s | 21.39 s |

Eight processes are **1.96x faster than the original
serial scheduler**, and **3.49x faster than one
process running the same new task plan**. The new one-process plan costs
more than legacy serial: fixed task-local banks repeat some work, and proof
history, serialization and process coordination add overhead. The larger
number is not the speedup over the original implementation.

All six runs produced the same **93 complete rule records**, including
support counts, conditions, width schedules and proof hashes. Semantic
revisions and emitted TableGen/C++ were also identical. No parallel task
was left unresolved. All 534 referenced proof files exist and their content
hashes match.

This is a bounded, shallow integer-search workload. Its stop counts are
488 complete, 24 bank-truncated and 3 candidate-limit instances. These
budgets apply equally to each run; this is not an exhaustive search or a
benchmark of heavy floating-point timeouts. No new target optimization
benefit is claimed by these timing results.

## Correctness checks

- Full Python suite: **632 passed**, including an isolated build of the
  parallel-search-generated cross-block rules and execution on AMDGPU and
  AArch64 with MachineVerifier and unchanged CFG checks.
- The eight focused parallel tests passed again after extending their
  fixtures with a structural vector and forced slow-lane replay. They
  compare cold 1/3-process runs, warm 2-process reuse, and a run with zero
  fast proof allowance. Full rule records and generated code agree.
- Scheduler tests cover stable slow-budget admission under reordered task
  completion, fast work continuing during a slow task, worker failure,
  expired global deadlines, and duplicate-family rejection.
- A regression test catches UNKNOWN at later widths after the first width
  has already proved valid; the slow task now grants the longer limit to
  those queries too. Unknown attempts cannot become proof-cache entries.
- An independent real cross-block run with zero fast proof allowance
  admitted five slow tasks and returned the same five rules as the normal
  run, without unresolved work.
- All **93 rules independently re-proved**, with 918 solver queries and no
  proof cache. Every semantic revision stayed unchanged.
- Default `emit --check` passed. Semantic models, default generated files,
  rule catalog and selected target profiles are unchanged.
- `git diff --check` passed.

The standard `recheck` CLI currently refers to the removed
`synth.repeated_choice` function, including on the base commit. Independent
revalidation therefore uses the existing `known.refresh` API with a fresh
backend and no proof cache; see the accompanying JSON validation result.
This change does not modify that unrelated CLI path.

Evidence and the frozen input are retained under
`/home/nod/gisel-parallel-search-20261112/build/validation/`.
[Parallel-Search.md](Parallel-Search.md) documents activation, slow-budget
allocation, task-local sharing, and the remaining serial hybrid phases.
