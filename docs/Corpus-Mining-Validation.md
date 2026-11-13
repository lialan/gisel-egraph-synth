# Corpus mining validation (2026-11-13)

This validates the measured `mine` campaign, its configurable static
objective, and the real-program preparation recipe. The machine-code
metrics are instruction count and encoded executable-section size;
the experiments do not measure hardware execution time.

## Source and environment

- Main baseline: `d842e366366d0ead9c0ac7fc9aa57741684ce4b4`.
- Experiment implementation: `58c65c2`. Subsequent commit `6306724` adds
  stage-cache invalidation for changed measurement/selection/report code
  and a regression test. It does not change fresh-run search, selection
  or measurement logic; the experiment stays on its frozen source.
- LLVM backend: `37a1706d0eac1774701a0a44d9fb4fa542f56fde`.
- Clang frontend: 23.0.0git, `0721d8e7768c011b8cf2d4d223ca6eca3392b1f9`.
- Validation host: nod, 32 logical CPUs, 16 search workers. Work was
  isolated in `/home/nod/gisel-mine-loop-20261113`; the existing LLVM build
  supplied backend libraries, with a separate build of this project.
- AArch64 Linux sysroot: `libc6-arm64-cross` and `libc6-dev-arm64-cross`
  `2.35-0ubuntu1cross3`, `linux-libc-dev-arm64-cross`
  `5.15.0-22.22cross3`, extracted locally without a global install.

## Corpus and protocol

The checked-in recipe pins LLVM test-suite to
`19b349c5aa391729e688f9b4b53ded177e1531cb`. All C translation units from the
nine listed MiBench programs compiled unchanged at O2: 13 discovery,
13 validation, and 7 held-out units. No failed frontend inputs were
silently discarded. Programs are disjoint between roles; this is a split
within one collection, not evidence across unrelated ecosystems.

Selection uses validation programs only. Each arm starts with a cold
search cache and the same pinned maintained profile. The two seeds are
17 and 29. For each seed, the arms are one round with an instruction
objective, three feedback rounds with an instruction objective, and three
feedback rounds with an encoded-size objective. The first two compare
the feedback policy as a whole; they do not separately ablate cache
continuation, reallocation, candidate retention or limit growth.

Every arm receives a 180-second search/proof allowance and 16 workers.
Compilation, measurement and selection are outside that allowance. Other
search limits can stop an arm early; in-flight work can overrun deadlines.
Both actual search time and selection wall time are retained. All six
arms finish selection before any arm evaluates held-out machine code.

```sh
python tools/gisel-rule-synth/eval/mine_experiment.py \
  --config tools/gisel-rule-synth/configs/real-corpus.json \
  --out build/experiment-final-180 --budget-s 180 --seeds 17 29 --jobs 16
```

Development smoke runs and an interrupted earlier implementation run
are excluded from the formal comparison. They did not evaluate held-out
machine code. A review caught missing retention of unselected ordinary
candidates across local promotions; the formal run starts from the
corrected implementation and new caches.

## Results

**No arm selected an additional combine.** The maintained baseline of 13
ordinary rules and no joint rules remains unchanged. No experiment was
exported into the maintained catalogs or target profiles.

| Seed | Policy | Rounds | Actual search s | Selection wall s | Added rules | Validation instruction / code-byte delta | Held-out instruction / code-byte delta |
|---|---|---:|---:|---:|---:|---|---|
| 17 | single, instructions | 1 | 133.2 | 211.0 | 0 | 0 / 0 | 0 / 0 |
| 17 | feedback, instructions | 3 | 163.3 | 316.9 | 0 | 0 / 0 | 0 / 0 |
| 17 | feedback, code bytes | 3 | 166.0 | 320.8 | 0 | 0 / 0 | 0 / 0 |
| 29 | single, instructions | 1 | 137.8 | 217.7 | 0 | 0 / 0 | 0 / 0 |
| 29 | feedback, instructions | 3 | 163.5 | 298.2 | 0 | 0 / 0 | 0 / 0 |
| 29 | feedback, code bytes | 3 | 162.8 | 291.4 | 0 | 0 / 0 | 0 / 0 |

Selection wall time includes search, builds, measurements and verification;
it excludes the final evaluation phase. Each arm receives the same
180-second allowance, but uses a different amount of it. These timings
do not establish an equal-actual-work comparison or a speedup.

The final comparison covers all 13 validation units (3,384 baseline
instructions) and all 7 held-out units (3,088 baseline instructions).
Every unit compiled, all encoded-size measurements were present, and
there were no changed fallback sets or per-unit regressions. The two
string-search initializers `bmhi_init` and `bmh_init` already used
SelectionDAG fallback in the baseline; this was unchanged in every arm.
No held-out function used fallback. The 13 discovery units supplied the
search inputs and are not part of this final evaluation total.

In the seed-17 single-round arm, 289 joint candidates were measured:
272 did not apply to validation programs, 12 applied without a gain,
and 5 regressed. The feedback arms continued their queues and tested
retained and additional candidates, but none passed selection either.
Candidate counts and truncated-queue reasons for every round are in
[the machine-readable evidence](Corpus-Mining-Validation.json).

The harness completed all six selections before the first held-out
evaluation, and each frozen report records zero previous held-out
evaluations. An independent check recomputed the instruction and encoded
size deltas from every per-file baseline/final measurement and matched
the reports. The evidence records the ordering, exact configuration,
source/IR/compiler hashes, artifact hashes and the unchanged fallback sets.

This is a completed negative result for this corpus, grammar and budget.
It validates the workflow, but does not show that feedback rounds find
better combines than the single-round policy. It also does not establish
which of corpus coverage, search limits or candidate forms is the main
bottleneck. Further tuning must use fresh held-out programs for another
independent acceptance claim.

## Regression checks

On the experiment implementation, the full Python suite ran 802 tests
and passed with 2 skips. The C++ suite passed 275 tests. The MIR suite
passed 26 tests with 2 unsupported cases. `emit --check` found the
maintained generated files current.

The new coverage checks objective conflicts, per-file regressions,
guardrails, missing metrics, changed fallback sets, candidate overlap,
baseline-enabled matches, cycles, feedback quotas, encoded ELF sections,
corpus grouping and hashes, budget splitting, CLI status, local promotion,
candidate retention, final-only evaluation, original-baseline comparison,
completed resume, export baseline identity and artifact tampering.

A real completed three-round campaign was invoked again after evaluation:
its campaign/report, per-round states, catalogs, profiles, joint search
statistics and final freeze record were byte-for-byte unchanged (21
artifacts, 0.57 seconds). No completed search or held-out measurement ran
again. The resume artifact hashes are included in the evidence.
