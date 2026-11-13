# Joint region rules: several inputs, several outputs, shared instructions

The single-root search (`synth.py`) and its extensions (`region.py`,
`sibling.py`) start from an expression tree. This document describes the
joint region path, which starts from a region of real gMIR with all of its
inputs and outputs. It searches a cheaper DAG for all outputs at once and
generates an ordinary single-root `GICombineRule` with a C++ matcher and
applier.

```
real gMIR (after the pre-legalizer combiner)
  -> region DAG of each block            -gisel-synth-joint-regions (C++)
  -> windows, canonical keys             girs/joint.py  collect
  -> joint candidates, shared cost       girs/joint.py  Search
  -> joint proof of all outputs          smt.joint_violation(defs=...)
  -> rewrite plan                        girs/joint.py  plan
  -> GICombineRule + C++ description     girs/joint_emit.py
  -> matcher / applier                   GISelEGraphSynth/GISynthJoint.h
  -> combiner of its own                 -gisel-synth-joint-combines
```

| Command | What it does |
|---|---|
| `gi-rule-synth.py joint-extract` | runs llc with `-gisel-synth-joint-regions -gisel-synth-region-out=FILE` |
| `gi-rule-synth.py joint-search` | windows, search, selection, proofs, plans: `rules.json`, `search.jsonl`, `stats.json`, `proofs/`; with `--cache`, an incremental run (see [Runs that continue](#runs-that-continue)) |
| `gi-rule-synth.py joint-recheck` | checks stored rules again, replays and redoes each proof |
| `gi-rule-synth.py joint-emit` | writes `td/GISynthJointCombines.td` and `include/GISelEGraphSynth/GISynthJointRules.inc` |
| `eval/joint_validate.py` | full `opt -O2 -> llc` A/B and MIR cases for the difference of squares |
| `eval/joint_eval.py` | corpus A/B (held-out), per-rule application and matcher counters |
| `eval/joint_measure.py` | marginal effect of each candidate over a frozen baseline, per-window comparison, measured set (see [Measured selection](#measured-selection)); `--evaluate` for a frozen set |

The existing search paths, `rules.json`, the target profiles and the
generated `td/GISynthCombines.td` are not changed. The joint rules run in
a combiner that contains only them, so the same `llc` with and without
`-gisel-synth-joint-combines` measures exactly these rules.

## Region DAG (extractor record)

`-gisel-synth-joint-regions -gisel-synth-region-out=FILE` (the pass
`lib/GISynthRegionExtractor.cpp`, after the pre-legalizer combiner of AMDGPU
and AArch64; the corpus extractor and its records are not changed) writes
one JSON line per basic block (at most `-gisel-synth-region-max-instrs`
instructions per record). It contains the pure scalar integer instructions
of the block: integer binary operators, shifts, `G_TRUNC`/`G_ZEXT`/`G_SEXT`/
`G_SEXT_INREG`, `G_ICMP`, `G_SELECT`, `G_FREEZE`, min/max, `G_ABS`,
`G_[US]MULH` and the overflow operators, on types of at most 64 bits.

```json
{"kind": "region", "fn": "f", "bb": 1, "chunk": 0, "args_noundef": true,
 "inputs": [{"reg": "%0", "w": 32, "type": "i32", "zero": "0x0",
             "one": "0x0", "defined": true, "noundef": false,
             "def": "COPY", "pos": 0, "uses": 3, "const": "0x1"}],
 "instrs": [{"op": "G_MUL", "pred": "ult", "imm": 8, "pos": 2,
             "flags": ["nsw"],
             "defs": [{"reg": "%2", "w": 32, "type": "i32", "zero": "0x0",
                       "one": "0x0", "defined": true, "noundef": false,
                       "uses": 1}],
             "args": [{"in": 0}, {"node": 3, "res": 1}]}]}
```

* A value is either an input (`{"in": i}`) or an `(instruction, result)`
  pair (`{"node": k, "res": r}`). Its identity is never the text of an
  expression: two `G_FREEZE` of one register are two values.
* `uses` is the number of operands that read the value in the whole
  function. The users outside of any part of the region follow from it.
* `pos` is the position in the block, and `-1` for an input of another
  block.
* `defined` is the result of `gisynth::joint::isStableValue`, the same
  function that the guard `defined(x)` of a generated rule calls.
  `noundef` is what LLVM's `isGuaranteedNotToBeUndefOrPoison` alone says.
  It is false for every argument copy.
* `const` is the value of a `G_CONSTANT` input.

In `girs/joint.py`, a `Region` has `inputs`, `instrs` (topological),
`outputs` (the results with a user outside), the input facts, the positions
and the provenance. `window(block, members)` takes a part of a block and
recomputes its inputs and outputs from the uses of the whole block.

### Windows and identity

`windows` enumerates the connected sets of at most `max_window`
instructions (ESU enumeration, a budget per block). Two instructions are
connected if one reads the other, or if both read a value with at most 16
users; that is the bound of the matcher's `UserOf` step. So roots that are
not in one tree, siblings with inputs of their own, belong to one window.
A window must be convex.

`canonical` renames the inputs, the instructions and the outputs of a
window together. The order is a depth-first walk from the outputs, which
are ordered by a structural hash, and commutative operands are ordered by
hash. Result indices, sharing and aliases are kept. The key contains the
boundary: input widths, `defined`, constant values, flags, result widths
and, for each result, its users outside of the window (0, 1 or more).
Equal windows of different files are one search instance, and their
occurrences are its provenance.

## Joint candidate

```json
{"reused_source_instructions": [0], "relax_flags": [0],
 "new_instruction_dag": [{"op": "G_MUL", "ws": [32], "args": [["in", 1], ["in", 1]]},
                         {"op": "G_SUB", "ws": [32], "args": [["n", 0, 0], ["t", 0, 0]]}],
 "output_mapping": [{"output": [0, 0], "value": ["n", 0, 0]},
                    {"output": [3, 0], "value": ["t", 1, 0]}],
 "required_guards": {"defined": [0, 1], "distinct": [], "constant": []},
 "estimated_cost": {"before": 6, "after": 5, "gain": 1, "independent_after": 6}}
```

The value of an output is a kept source value `["n", k, r]`, a new value
`["t", j, r]`, an input or a literal. An output whose instruction stays
maps to itself.

For the difference of squares, `reuse(s)` has the two meanings that the
task asks for. In the proof, `s` is the variable of its source instruction,
defined as `mul(x, x)`; it is not a free input. In the generated rule, `s`
is the register of the matched instruction.

## Search

The search reuses the term bank of the single-root search
(`discover.Bank`) with two opt-in options. Both are part of the bank
cache key, and the defaults keep the old banks unchanged.

* `nonlinear`: a term can read a variable more than once, for example
  `mul(y, y)`. `_products` no longer requires disjoint variables, and the
  symmetric case `idx[0] <= idx[1]` admits `op(t, t)`. The guards then
  cover such reads, as described below.
* `variant_mask`: of each sampled value, the bank keeps the cheapest term
  *for each set of context variables it reads*. So a term that reads a
  value another output keeps is not dropped in favor of a cheaper term
  that does not read it. The retention key is the dependency set, not a
  count of variants.

For one window:

1. The variables are the inputs, then the outputs of the window (reuse
   leaves). A constant input has its value in every sample.
2. For each output, the candidates are the bank terms that agree with it on
   the samples (a filter only), excluding terms that read the output
   itself or a value computed from it. The other results of a
   multi-result instruction in a candidate are added as candidates of the
   other outputs.
3. Helper round. Helpers are terms of cost <= `helper_cost` over the
   inputs and literals whose value is not a value of the window. Each one
   is one more variable of a small bank, and only combinations in which at
   least two outputs read the helper are kept. A helper is never one of
   the window's values, so it is a *new* shared instruction.
4. Joint selection. For each output: the output itself (keep) or one of its
   candidates. Over all combinations (bounded by `max_combos`), the cost
   is the union of the kept instructions (the instructions the read values
   need, each once) and the new instructions. Equal new instructions are
   merged, the results of one instruction are one instruction, and a new
   instruction equal to a kept one (not a `G_FREEZE`) is that instruction.
   A replaced output whose instruction is kept is rejected, because the
   new value would read the old one.
5. `independent` is a baseline for comparison only: the cheapest candidate
   of each output on its own, charged with what it reads, then shared
   instructions.
6. A candidate whose guards fail on its own instance is dropped, since the
   rule would not fire there.
7. The candidates are proved, cheapest first (see [Several
   implementations](#several-implementations-of-a-window)).

The status is `complete`, or `budget: <what>` when the time, the bank
(`bank_truncated`), the helpers, the combinations or the candidate lists
(`cands_truncated`, `max_cands`) reach their budget. `budget` is never
reported as "no optimization". A budget never discards what was found
before it ended: `Search.run` returns the candidates made so far, with
`stats['incomplete']` and the reason (`stop`).

## Several implementations of a window

Two options, with the meaning that they have for the single-output search
(`discover.Limits`), decide which candidates the search may look at:

| Option | Default | Meaning |
|---|---|---|
| `--cost-slack k` | none | none: a candidate DAG costs less than the window (the historical policy). `k >= -1`: it costs at most the window plus `k` (`0`: equal cost). |
| `--semantic-variants n` | 1 | proved implementations of different shapes that a window keeps (1: the first proved one). |

The cost bound `max_after` replaces each place where the search assumed a
cheaper DAG: the cost of the bank terms of an output (`_bank_rows`), the
room for a helper and the two instructions that read it, the selection,
`check_rule` (against the cost policy stored in the rule) and the cache
identity. Shared instructions, kept instructions and the results of one
instruction still count once, and the cost is that of the whole DAG: an
output that alone gets more expensive is not dropped.

A search cost is not a target cost. A candidate of equal or higher
generic cost exists to be measured: `eval/joint_measure.py` decides whether
it is profitable.

With a slack the window itself is a candidate of its own cost (operands
commuted, flags dropped): `is_identity` drops it. The proofs then take
the candidates cheapest first and keep at most one proved candidate of
each **shape** (the kept instructions, the multiset of new operators with
their attributes and widths, and the kind of value of each output), so
that `x+(y+z)` and `(x+y)+z` do not fill the quota. `variant_mask` of the
bank still keeps the terms that read different shared values. A window
stops proving when it has `semantic_variants` proved shapes or after
`max_proofs` proofs; there is no break at the first proof. Each candidate
gets a state:

| State | Meaning |
|---|---|
| `verified` | proved: a rule (stable id `joint_<hash of window and candidate>`) |
| `refuted` | the solver found a counterexample |
| `unknown` | the solver did not decide (never a proof) |
| `not_tried` | the quota, the proof budget or the end of the run came first |
| `same_shape` | a candidate of a proved shape |
| `no_plan`, `error` | no match order, or a model gap |

The record of a window (`search.jsonl`) has these counts, the proof
attempts, the solver calls, the time and the reasons why its work is not
done (`window_time`, `time`, `terms`, `helpers`, `combos`, `candidates`,
`proofs`, `unknown`, `variants`). A rule record has its `cost_policy`, its
`shape`, its `window` (the rules of one window share their source
pattern), `proof_status` in `semantic_status` and `profitability_status`
(`unmeasured` until a measurement).

## Termination

A rule that does not make the generic cost smaller can undo another one
(`x << 1 -> x + x`, `x + x -> x << 1`). The combiner of the joint rules
runs one iteration in `SinglePass` mode, which still puts the instructions
that a rule creates back on the worklist, so two such rules would rewrite
each other forever. Two measures:

* At run time (`GISynthJoint.h`), the plan of such a rule has
  `original_only` (`RuleDesc::OriginalOnly`): it erases and replaces only
  instructions whose results are older than the combiner
  (`MatchEnv::FirstNewVReg`, the number of virtual registers when the
  combiner started). Each application of such a rule removes one of the
  instructions that the function had, and every other rule makes the
  generic cost of the function smaller, so the combiner ends.
  `unittests/GISynthJointTest.cpp` checks both rules of the example: the
  second one matches the instruction that the first one created only
  without the guard.
* Before a set of rules is selected, `joint.rewrite_graph` looks for the
  source pattern of each rule in the result of each rule (structurally,
  without flags, facts and outside users: an over-approximation inside
  the result, which cannot see the instructions around a match), and
  `joint.rewrite_cycles` reports the cycles that contain a rule of
  `original_only`. A rule that closes such a cycle is not selected.

The existing combiners run before the joint combiner (the pre-legalizer
combiner) or after it (the legalizer and the post-legalizer combiner);
none of them runs again in this pass, so a joint rule that a later
combiner undoes costs time but cannot loop. Its measured effect shows it.

## Runs that continue

With `--cache DIR`, `joint-search` makes each canonical window a task of
the agenda of the single-output search (`girs/agenda.py`, stage `joint`),
with its proof history (`girs/history.py`) and its process backend
(`girs/parallel.TaskBackend`): no other database or recovery protocol
(`girs/joint_tasks.py`). `JointAgenda` only replaces the table of reasons
(`agenda.py` is part of `known.search_sha`, which keys the rows of the
single-output search, and is not changed).

| In the cache | What it holds |
|---|---|
| `agenda.sqlite3` | per window: complete or partial, the reasons, the budgets it had, and its result: the decided candidates (`verified`, `refuted`), the shapes, the pending candidates (`not_tried`, `unknown`, as records that a later run proves) |
| `proofs.sqlite3` | SAT and UNSAT of each query, shared by all processes; UNKNOWN is only an attempt of the run |
| `joint/<domain>/rules/*.json`, `proofs/*.smt2` | the verified rules of the domain |

* **Order.** New windows first (the most frequent first), then the windows
  that this run can take further, least searched first. With `--priority
  SELECTION` (the output of `joint_measure.py`), windows whose rules have a
  measured gain come first, and one place in four goes to a window
  without a measurement.
* **What reopens a window.** Each reason names the budgets that take it
  further (`joint.REASONS`): `window_time` needs a larger `--time-s`,
  `terms` larger `--max-terms`/`max_evals`, `helpers`, `combos` and
  `candidates` their limits, `unknown` a larger `--timeout-ms`, `variants`
  a larger `--semantic-variants`. `time` (the end of the run) and `proofs`
  (the proof budget of one run) need no larger budget; a window whose
  proofs decide nothing new twice needs a larger `max_proofs` or
  `timeout_ms` (the `stalled` rule of the agenda). Only the search reasons
  search the window again; a window with only proof reasons proves its
  pending candidates (`mode: prove`).
* **Decided work.** A decided candidate is never proved again and does not
  use the proof budget of a later run. A verified rule that a measurement
  found without a gain (`no_gain`, `regression`) leaves the quota of its
  window, and its shape stays taken, so that the next run proves another
  shape there.
* **Commit order.** As `cmd_synth`: the rules of a window (their proof
  files, then the rule, each written atomically) before its row; the agenda
  is committed at checkpoints (`--checkpoint-s`) and at the end. An
  interrupt (SIGINT/SIGTERM) stops the queue, waits for the running
  windows and commits what was published. A failed worker or a failed
  write leaves no row for its window, which a later run searches again
  (its proofs come from the history).
* **Identity.** The domain of the rows and of the rule store is the joint
  proof model (`joint_tasks.semantics_sha`: `known.semantics_sha`, the
  record schema and the source of the functions of `joint.py` that make
  formulas, guards and plans), the search (`known.search_sha`,
  `JOINT_SEARCH_VERSION`) and the limits that decide which candidates
  exist (window, outputs, `max_cost`, grammar, samples, seed, widths,
  `cost_slack`). The budgets (`time_s`, `max_terms`, `max_evals`,
  `max_helpers`, `max_combos`, `max_cands`, `max_proofs`, `timeout_ms`,
  `semantic_variants`) are the depth inside a domain. A window's key is its
  canonical form with the boundary (inputs, facts, flags, widths, outside
  users).
* **Determinism.** Each window is searched alone, and a term bank depends
  only on its key and on `max_terms`/`max_evals`, so with budgets that do
  not end a search the rules do not depend on the number of processes.
  The time budgets (`--time-s`, `--time-budget-s`) depend on the load of
  the machine: a run with them is not reproducible bit for bit.

```
# A first run of at most 20 minutes, then runs that continue it:
gi-rule-synth.py joint-search --regions R --out OUT1 --cache C --jobs 96 \
    --cost-slack 0 --semantic-variants 6 --time-budget-s 1200
gi-rule-synth.py joint-search --regions R --out OUT2 --cache C --jobs 96 \
    --cost-slack 0 --semantic-variants 6
# More terms for the windows whose banks were truncated:
gi-rule-synth.py joint-search ... --cache C --max-terms 400000
```

## Measured selection

`eval/joint_measure.py` decides which candidates are worth emitting, over
the frozen baseline (the rules already selected, `joint/rules.json`), on a
validation corpus. One `llc` has every rule (the baseline first); a
configuration is a set of enabled rules (`--gisynthjointcombiner-disable-
rule` for the others), compiled with the target's flags and
`-verify-machineinstrs`:

1. `control` (no joint combiner), `baseline`, and `screen`: every rule with
   `-gisel-synth-joint-screen`, where a match is reported and rejected, so
   no rule hides another and nothing changes.
2. `solo`: baseline + one candidate, on the files where it screened. This
   is its marginal effect: no other candidate takes its place, and the
   gains of the baseline are not counted again.
3. The candidates of one window are compared by their solo effect; the
   best one is the window's candidate, the others are
   `dominated_in_window`. Measuring them one at a time matters: enabled
   together, the first one in the combiner takes every instance.
4. A greedy set, largest solo gain first: a candidate joins if baseline +
   set + it is smaller than baseline + set on its files, no file gets
   worse, and no rewrite cycle appears. Its gain in the set is recorded
   next to its solo gain (`overlaps the set`, `enabled by the set`).
5. `select._loo_in_set` (leave-one-out inside the set) and
   `select.enforce` (no file of the corpus worse, failing or with other
   fallbacks than with the baseline) refine and validate the set.

Each candidate has a proof status and a profitability status:
`never_matched`, `no_application`, `no_gain`, `regression`, `profitable`
(`not_emittable` if `joint-emit` refused it), and, if profitable, a
selection status (`selected`, `dominated_in_window`, `no_gain_in_set`,
`worse_in_set`, `cycle`, `final_set_violation`). The primary metric is the
number of machine instructions; encoded bytes (`codeLenInByte`), SGPRs,
VGPRs, spills, scratch and the CPU time of the compilations are recorded.
These are static counts, not run time. Compilations are cached by
compiler, flags, file content, enabled rules and metric version.

The screen sees the MIR without joint rules: a candidate that would only
match after a baseline rule applied is not measured there. The held-out
corpus is for `--evaluate` of a frozen set only.

Completeness bounds: the search is exhaustive over the windows enumerated
for a block (at most `max_window` instructions, at most `max_outputs`
outputs), over the bank terms of cost <= `max_cost` (until the bank's
term or evaluation budget), over at most one helper of cost <=
`helper_cost`, and over the combinations of the `max_cands` cheapest
candidates of each output.

## Cost

`C_before` is the cost of all instructions of the window; each one
computes an output, or a value that an output needs. `C_after` is the
cost of the kept instructions plus the new ones, each counted once. The
gain is `C_before - C_after`, and no output has to be cheaper on its own.
This generic cost is a filter. Target gains come from the measured
pipeline.

## Guards, definedness, flags

* **defined(x).** The proof has one value per input. That covers an undef
  input if the candidate's DAG reads each input once and reads each value
  once (counting one read per output): it is then a tree. Otherwise every
  input that is read more than once, and every input of a value that is
  read more than once (not through a `G_FREEZE`), gets the guard
  `defined(x)`. The guard is part of the rule, of the SMT guard
  (`not poison`), and of the matcher (`isStableValue`). The other inputs
  must be distinct registers.
* **The fact source.** `isStableValue` accepts LLVM's own analysis, copies
  of defined virtual registers, `G_ASSERT_*`, `G_MERGE_VALUES` and
  `G_UNMERGE_VALUES` of defined parts, generic instructions that cannot
  create undef or poison with defined operands, and copies of argument
  registers (`isNoUndefArgumentCopy`). An argument copy qualifies when it
  is a COPY of a physical live-in in the entry block, not clobbered
  before it, in a non-variadic function whose arguments are *all*
  `noundef`. The lowering of arguments does not record which register
  holds which argument, so it asks for all of them.
* **Flags.** The source instructions are proved without their flags. That
  covers any flags of the instructions that die: flags only add poison to
  the source. An instruction that stays and that a new instruction (or a
  new output mapping) reads, transitively, gets the action `relax`: the
  applier drops its poison-generating flags (`dropFlags`, with observer
  notification). The other kept instructions are `keep`. The replaced ones
  are `replace`, the dead ones `erase`.
* **Constants.** A constant input is a value of the rule. The proof fixes
  it, and the matcher checks the operand as a literal. 0, 1 and -1 keep
  their meaning at each width; any other constant is proved at its own
  width only.
* **Widths.** Each width map has its own joint proof. The rule's
  `WidthMaps` holds only the proved maps, and the matcher checks that the
  matched types form one of them.

## Proof

`joint.joint_violation` calls `smt.joint_violation` with SSA
definitions. Each window instruction has one variable per result,
constrained by its definition (`joint.ssa_definitions`). The definitions,
and the condition that none of them has undefined behaviour, are
conjuncts of the environment (guard) of the unchanged
`smt.joint_violation`. That is the same formula as the definitions' UB
inside the source UB. `smt.py` and the corpus extractor are not changed,
so the semantic model hash of the rule catalog (`known.semantics_sha`) and
its existing proofs stay valid. A `G_FREEZE` variable is the instruction's
own choice. Every source instruction executes, so its undefined behaviour
is the source's. The query is

```
Guard and not UB(source) and OR_i ( source_i not poison and
                                    (target_i poison or target_i != source_i) )
```

over a single environment of inputs and instruction variables. A kept
instruction is the same variable on both sides, so outputs that share a
choice stay correlated. `formula(..., flags=True, relax=False)` models
flags; the flag test uses it to show why `relax` is needed. UNKNOWN is not
a proof.

## Plan and generated code

`plan` derives these from the candidate:

* an action per source instruction;
* the anchor: the last replaced instruction;
* the match order: anchor, `DefOf` (definition of an operand slot),
  `UserOf` (a user of a bound value, never a constant);
* the new DAG, the replaced outputs, the erase candidates and the guards.

`check_rule` derives all of these again from a stored rule. `joint-emit`
refuses a rule that differs, for example one whose guard was removed by
hand.

`GISynthJoint.h` implements the matcher and the applier.

* **match** binds the instructions in order, with commutative operands
  tried both ways (backtracking, at most 256 bindings) and at most 16
  users per `UserOf`. It then checks that:
  * every operand is consistent;
  * inputs are defined outside the region and distinct where required;
  * every width class has one integer LLT, and the widths form a proved
    map;
  * erased instructions, and the results of replaced instructions that
    are not outputs, have no user outside the match;
  * `defined(x)` holds;
  * placement works. The new instructions go before the first replaced
    instruction, or after the last value they read if that comes later,
    and never after a user of an output in the block. The scan is limited
    to 128 instructions around the anchor.
  * for a rule with `OriginalOnly`, no erased or replaced instruction was
    created by this run of the combiner (`reject created`; see
    [Termination](#termination)).

  The matcher changes nothing. With `-gisel-synth-joint-screen` it reports
  a match (`matched`) and returns false (measurement only).
* **apply** drops the flags of `relax` instructions, builds each new
  instruction once in order with the builder (CSE included), rewrites only
  the *uses* of each replaced output with observer notification, and
  erases the replaced or erased instructions that are dead, users first.

`-debug-only=gisel-synth-joint` prints `anchor`, `reject <stage>`,
`matched` and `applied` per rule: the match rate.

## Not changed

* The online C++ e-graph (`GIEGraph.h`, its `Extractor`, `getDagCost`) is
  not changed. Its tree-cost extraction still cannot recover a dropped
  sharing alternative; the joint selection exists only in the offline
  synthesizer.
* `region.py`, `sibling.py`, the single-root search, the existing rule
  library, the profiles and `td/GISynthCombines.td`.
* LLVM: no TableGen extension. Each rule is a single-root `GICombineRule`.
