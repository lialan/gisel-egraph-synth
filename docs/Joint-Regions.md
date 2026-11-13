# Joint region rules: several inputs, several outputs, shared instructions

The single-root search (`synth.py`) and its extensions (`region.py`,
`sibling.py`) start from an expression tree. This document describes the
joint region path, which starts from a region of real gMIR with all of its
inputs and outputs. It searches a cheaper DAG for all outputs at once and
generates an ordinary single-root `GICombineRule` with a C++ matcher and
applier.

```
real gMIR (after the pre-legalizer combiner)
  -> region DAG of each block            -gisel-synth-region-out   (C++)
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
| `gi-rule-synth.py joint-extract` | runs llc with the corpus pass and `-gisel-synth-region-out` |
| `gi-rule-synth.py joint-search` | windows, search, selection, proofs, plans: `rules.json`, `search.jsonl`, `stats.json`, `proofs/` |
| `gi-rule-synth.py joint-recheck` | checks stored rules again, replays and redoes each proof |
| `gi-rule-synth.py joint-emit` | writes `td/GISynthJointCombines.td` and `include/GISelEGraphSynth/GISynthJointRules.inc` |
| `eval/joint_validate.py` | full `opt -O2 -> llc` A/B and MIR cases for the difference of squares |
| `eval/joint_eval.py` | corpus A/B (held-out), per-rule application and matcher counters |

The existing search paths, `rules.json`, the target profiles and the
generated `td/GISynthCombines.td` are not changed. The joint rules run in
a combiner that contains only them, so the same `llc` with and without
`-gisel-synth-joint-combines` measures exactly these rules.

## Region DAG (extractor record)

`-gisel-synth-region-out=FILE` (in `lib/GISynthCorpusExtractor.cpp`) writes
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
7. The best candidates are proved; the first proved one becomes the rule.

The status is `complete`, or `budget: <what>` when the time, the bank
(`bank_truncated`), the helpers or the combinations reach their budget.
`budget` is never reported as "no optimization".

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

`smt.joint_violation(enc, pairs, guard, defs)` with SSA definitions.
Each window instruction has one variable per result, constrained by its
definition (`ssa_definitions`). A `G_FREEZE` variable is the instruction's
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

  The matcher changes nothing.
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
