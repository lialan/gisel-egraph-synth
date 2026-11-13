# Incremental queue integration and recovery validation

Validated on nod (`Shark19`) on 2026-11-12, with Python 3.12.14 and Z3
5.4.1. Tested source: `fd5912f83ad124e226432de2065b279846e887f8`, integrating
PR #2 with main at `da9a471c93431aaf50afecab84a8e4b2bfc55b4c`.
The default remains sixteen search processes plus one separate slow-proof
process. No maintained rules, target profiles, or generated combines change.

## Publication and recovery

Task completion is staged in the coordinator. It is committed in one SQLite
transaction only after output rules, learned rules and referenced proof files
have been published successfully. Closing the agenda discards staged rows.
A cache-directory lock prevents simultaneous coordinators from publishing
incompatible checkpoints; workers retain independent processes and connections.

`tests/test_agenda_recovery.py` launches the production scheduler with its
default sixteen processes and kills the entire process group with SIGKILL:

- Before final guard verification.
- Before and after publication of `learned.json`.
- During the second task insert in the SQLite transaction.
- Immediately after transaction commit.

Before commit, no task rows survive; after commit, all rows do. Every restarted
run reproduces the uninterrupted rule revisions and emitted TableGen/C++, and
every referenced proof file has the expected hash. Restart after commit does
no search or solver work. An injected catalog-write error also leaves no
completed task rows. These checks concern process interruption, not recovery
from disk loss or manual file deletion.

Additional cases cover capped runs advancing without spending quotas on
completed work, enabling cross-block regions on saved single-root rules,
growing a sibling corpus, unfinished final guards, and enabling/expanding
the latest analysis views. Known view candidates retain their rule IDs and
seeds. Views configuration participates in the queue domain; their proof/time
limits cannot be hidden by a different enumeration stop reason.

Proofs present before a run do not consume its logical proof quota. Proofs
first obtained during the run still count on cache hits, keeping quotas
independent of worker completion order. Tests cover both cases and the
existing separate slow-proof queue, worker failures, and serial/process parity.

## Regression checks

- Full Python suite: **706 passed**, with `GIRS_LLC` pointing to the newly
  built integration compiler, `GIRS_LLVM_BUILD` pointing to the shared pinned
  LLVM build, and `GIRS_TEST_REGION_BUILD=1`.
- One subsequently added views enablement/recovery regression: **passed**.
- `check-gisel-egraph-synth`: **267 C++ unit tests and 19 lit tests passed**;
  2 lit tests unsupported under their platform requirements.
- The cross-block test extracts real MIR, discovers joint/sibling rules,
  emits them, builds an isolated compiler and verifies actual rewrites and
  unchanged CFG on AMDGPU and AArch64.
- `emit --check` and `git diff --check`: passed.

The first pre-views integration also passed its 661-test suite. An earlier
run exposed a missing vector-composition filter in conflict resolution and
an absent LLVM source checkout; both were corrected before final validation.

## Fixed-corpus timing and equality

Replayed the same frozen 515-record corpus, starting with an empty catalog
and proof cache for each invocation. Runs were sequential, reversing order
on the second repeat, with no other validation jobs running during timing.
At the user's suggestion, two additional 32-process runs then used the exact
same command and budgets. The recorded order is 0, 1, 16, 16, 1, 0, 32, 32.

```sh
python tools/gisel-rule-synth/eval_parallel.py \
  /home/nod/gisel-parallel-search-20261112/build/validation/benchmark-corpus.jsonl \
  --out build/validation/parallel-benchmark \
  --jobs 0 1 16 --repeats 2 --regions --siblings
```

| Scheduler | Median wall time, two runs |
| --- | ---: |
| Original serial (`--search-jobs 0`) | 46.51 s |
| Single process with task scheduling (`--search-jobs 1`) | 80.31 s |
| Sixteen search processes | 19.77 s |
| Thirty-two search processes | 20.77 s |

Sixteen processes are **2.35× faster than the original serial scheduler** and
**4.06× faster than one process using the same task plan** on this corpus.
All eight runs produce the same **93 complete rule records**, semantic
revisions and emitted code hashes. No unresolved slow-proof work remains.
Of the 515 searches, 24 hit term-bank limits and 3 hit candidate limits;
they are closed at the tested depth, not claimed to be exhaustively searched.
Increasing the relevant budget reopens them.

Thirty-two processes are supported (`--search-jobs 32`), but are about 5%
slower than sixteen here. The default therefore remains sixteen. This small
fixed-corpus comparison does not establish the best count for every workload.

Machine-readable configuration, times and hashes are in
[Incremental-Queue-Validation.json](Incremental-Queue-Validation.json).
Raw logs, per-run rules/proofs/generated code and cross-block evidence remain
under `/home/nod/gisel-pr2-integration-20261112/build/validation/`.
This measures search throughput and recovery correctness, not an additional
target-code profitability result.
