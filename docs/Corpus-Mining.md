# Corpus-driven mining campaigns

`mine` accepts a corpus, target, objective and search allowance. It searches
ordinary and joint rules, proves them, measures them over a fixed baseline,
and selects a set. A campaign repeats this with local promotions and
measurement feedback. The repository's catalogs and target profiles are
unchanged until `mine --export` passes its final evaluation checks.

## Objectives and selection

```json
"select": {
  "strategy": "measured",
  "metric": "insns",
  "guardrails": {"code_bytes": 0}
}
```

The primary metric is `insns` or `code_bytes`. Both are static metrics;
neither is a runtime speed estimate. `code_bytes` is the AMDGPU backend's
encoded function length, or the sum of executable ELF sections for AArch64.
The latter requires a second compilation to an object; its extra CPU time
is recorded as `metric_user`. The historical `bytes` field is assembly text
length and is never a selection metric.

Guardrails are maximum absolute increases per compilation unit, not
percentages. Supported fields are `insns`, `code_bytes`, `sgpr`, `vgpr`,
`spills`, and `scratch`. Register/spill/scratch fields currently come from
AMDGPU. A missing metric is an error, never an assumed zero. Compilation
failure or a changed SelectionDAG fallback set always rejects a candidate.
The selected primary metric may not regress on any selection unit.

The measured selector is shared by ordinary and joint rules:

1. Compile every candidate **alone over the pinned baseline**, on every
   selection unit, using one binary and fixed emitted rule order. This sees
   matches enabled by the baseline and does not credit a candidate with
   another candidate's gain.
2. In decreasing solo-gain order, test each profitable candidate inside the
   growing set. Require positive marginal gain, per-unit non-regression,
   configured guardrails, and no joint rewrite cycle.
3. Recheck leave-one-out marginal value and verify the final set on every
   selection unit. Store solo and in-set evidence separately.

Measurements are cached per compiler, target, file contents, enabled rules
and measurement implementation. The selector evaluates all candidates;
there is no single best-per-window filter before set measurement. It is
still greedy: this does not search arbitrary combinations of individually
unprofitable rules, or prove global optimality. The legacy selector remains
available as `strategy: "legacy"` for instruction-count-only comparisons.

## Cache identity and residual reuse

Mining retains three different kinds of evidence. Their reuse has different
requirements:

| Evidence | Reuse requirement |
|---|---|
| Exact SMT conclusion | The same complete query, declarations and requested model values in the same proof trust namespace. SAT/UNSAT may be reused independently of search budgets and ordinary compiler-tool source edits. |
| Verified rule | Current semantic, typing, precondition and runtime matcher/emitter contracts, with the rule's proved guards and width schedules. The catalog and selected profile remain subject to `refresh-known` and reselection checks. |
| Codegen result | The actual compiler, target, flags, input bytes, selected rules and measurement implementation. It must be remeasured when that identity changes. |

An exact-query hit establishes a result about its encoded formula. Runtime
applicability, legality and profitability still need their own current
checks. A corrected encoding normally creates a different query. If a
model or solver/backend bug invalidates trust in an unchanged query,
maintainers must bump `PROOF_MODEL_EPOCH` or `PROOF_SOLVER_EPOCH` in
`girs/known.py` before revalidation. Catalog trust changes with those epochs
as well. Old catalog-keyed proof-cache entries conservatively miss under
the new namespace and are not automatically migrated. UNKNOWN is never
published as a decided proof.

A changed LLVM/compiler build triggers a fresh extraction. The discovery
stage then compares residual content rather than inheriting the compiler's
producer hash as its search identity. The fingerprint for current tree and
joint-region JSON retains types, flags, known bits, definedness, constants,
use counts, sharing, multi-result identity and region boundaries. Register
and block numbers are normalized within their function scope, including
relationships across records. Unknown/older schemas, new unrecognized fields
and e-graph exports use a full-content hash. The fingerprint only describes
the context recorded by the extractor.

Residual identities also retain the binding between source/pipeline and
captured file, successful and failed captures, target legality and the
pinned baseline. Source and raw capture provenance are tracked separately
from the semantic task key. If those records change, the discovery wrapper
refreshes current corpus metadata and source-to-capture mappings; the agenda
can still reuse unchanged semantic tasks. Previously learned rule examples
remain historical evidence, and original proof provenance stays with its
proof. Current applicability comes from compiler checks. A matching residual
fingerprint never substitutes for measurements made with the new compiler.

### Known candidates and bounded continuation

An exact catalog match skips repeated proof work only if the source/RHS,
proved widths, constants, vector domain, guard and use requirements cover
the current instance. Such a result remains a seed for composition and
multi-output discovery, and does not consume `search.max_candidates` /
`--max-candidates` slots for new candidates, including whole-vector searches.
The shared term bank keeps its intermediate expressions. Other RHS forms
and uncovered domains remain eligible.

After sample matching, a different RHS is no longer discarded solely
because another candidate agrees on samples or has a lower generic cost.
Exact duplicate and counterexample filters remain. Existing bank heuristics,
grammar and term/evaluation/time limits still bound which forms are reached;
the counters do not establish an exhaustive search of equivalent programs.
View proposal and joint-window limits retain their separate meanings.

When usable catalog coverage grows, partial ordinary tasks blocked by
candidate, proof or UNKNOWN limits can reopen at the same numerical budget.
Completed tasks and tasks blocked only by term limits retain their state.
The discovery stage keeps continuation available when newly learned rules
can release candidate slots. Increasing a recorded limiting budget remains
another way to continue. A cached search result is reusable work, not a
claim that the current compiler applies its candidate or benefits from it.

## Feedback rounds and budgets

```json
"loop": {
  "rounds": 3,
  "search_budget_s": 300,
  "joint_share": 0.5,
  "growth": 2,
  "max_growth": 4
}
```

The allowance covers search and proof, excluding corpus extraction, builds,
selection and evaluation. The remaining allowance is divided over the
remaining rounds and then between ordinary and joint search. Active workers
and proof publication can overrun a deadline; actual discovery-stage elapsed
time is recorded and deducted before allocating another round. This is not
a hard process-time quota. Compare runs with the same worker counts and
report both requested allowance and actual search/total time.

Each round has its own directory and immutable baseline. Accepted rules
become the next round's baseline; the next extraction therefore sees the
residual after those rules. Earlier unselected ordinary and joint candidates
remain eligible for measurement against the new baseline. The ordinary
proof/search cache and joint agenda persist across rounds. Joint feedback
supplies the measured in-set gain (retaining solo evidence separately) and
releases failed implementations from their window's quota. Limits grow
only for recorded blocked categories (terms, time per window, helpers,
candidate lists, combinations, variants), up to `max_growth` times the
original limits. Window size and the grammar do not silently change.

All joint CLI budgets, including `cost_slack`, `semantic_variants`,
`max_evals`, `helper_cost`, `samples`, proof limits and checkpoint interval,
are available in `mine`'s `joint` configuration. Defaults retain equal-cost
candidates and up to six proved shapes. `joint.priority` accepts earlier
measured feedback; campaigns populate it automatically.

`campaign.json` publishes a round only after its rules, proofs and profile
exist. Resume verifies the completed configuration/artifact hashes and
skips completed rounds. An interrupted round uses the existing task and
per-file caches. Changed inputs require a new campaign directory.

Only the final round freezes and evaluates held-out inputs. Its evaluation
disables all additions to recover the **original** campaign baseline in
the same final compiler. Intermediate rules are never credited twice.
`--until verify` finishes all requested selection rounds without evaluating
held-out. A later invocation without that option finishes evaluation.
`--export` uses the original baseline for compare-and-swap and refuses
missing measurements, regressions or guardrail failures. A finished run
that finds no additional rule remains a valid baseline evaluation.

## Real source corpus

`tools/gisel-rule-synth/corpora/mibench-aarch64.json` pins LLVM test-suite
revision `19b349c5aa391729e688f9b4b53ded177e1531cb`. It contains nine MiBench
program families, with every C translation unit in each selected program:

| Role | Programs |
|---|---|
| discovery | bitcount, SHA, Patricia trie |
| validation | string search, Blowfish, ADPCM |
| held-out | Rijndael, CRC32, basic math |

These are program-family splits within one benchmark collection, not a
claim of independence between unrelated software ecosystems. Source code
is not modified to create combine opportunities. Clang compiles it at O2
for AArch64 with a real target sysroot; the recipe explicitly enables the
older C dialect required by these programs. The corpus measures codegen;
the benchmark executables are not run by preparation or mining.

Provide a checkout of that revision (the MiBench directory may be sparse),
an LLVM-compatible Clang, and an AArch64 Linux sysroot. Preparation does
not download dependencies or install anything globally:

```sh
python3 tools/gisel-rule-synth/eval/prepare_corpus.py \
  --recipe tools/gisel-rule-synth/corpora/mibench-aarch64.json \
  --source /path/to/llvm-test-suite --clang /path/to/clang \
  --sysroot /path/to/aarch64-sysroot --out build/real-corpus
python3 tools/gisel-rule-synth/gi-rule-synth.py mine \
  --config tools/gisel-rule-synth/configs/real-corpus.json \
  --run-dir build/runs/real
```

Preparation records the source revision, compiler hash/version, recipe,
commands, source hashes, header dependency hashes and IR hashes in
`metadata.json`. A frontend failure aborts manifest publication. `mine`
checks IR hashes and program-group isolation, in addition to existing
path/content overlap checks. Held-out roles cannot be selection or
discovery roles. The sample configuration selects on validation programs
only. The manifests remain ordinary `.ll` lists, so other corpora can use
the same workflow; `corpus_metadata` is optional for existing manifests.

## Fixed-allowance experiment

```sh
python3 tools/gisel-rule-synth/eval/mine_experiment.py \
  --config tools/gisel-rule-synth/configs/real-corpus.json \
  --out build/experiments/real --budget-s 300 --seeds 17 29 --jobs 16
```

For each seed, the harness runs a single-round instruction objective,
a three-round instruction objective, and a three-round code-size objective.
The first two use the same engine, candidate policy, corpus and worker
counts. They compare the whole feedback policy (round allocation, cache
continuation and targeted limit growth); they do not isolate each of those
features. The allowance is a maximum: an arm can stop earlier at its other
limits, so actual search time must also be compared. Each arm has a cold
search cache. The initial
compiler image is copied once; builds may then reuse their intermediate
objects without changing this reference. All arms complete selection
before any evaluates held-out. The protocol and per-arm configurations
are frozen; a changed protocol requires a new output directory.

`summary.json` reports selected additions, each round's selection result,
actual search time, total selection wall time, and final corpus deltas.
Keep null results and per-file regressions visible. Once held-out results
have influenced development, use a new held-out set for the next independent
acceptance claim. The tool does not make previously inspected tests unseen.

The two-seed MiBench runs, including the repeat after integrating newer
main, and their negative results are recorded in
[Corpus-Mining-Validation.md](Corpus-Mining-Validation.md), with per-round
measurements and provenance in the accompanying JSON evidence.
