# Joint region rules: validation (2026-11-12)

Design: [Joint-Regions.md](Joint-Regions.md). Artifacts:
`tools/gisel-rule-synth/joint/` (`provenance.json` has the LLVM revision,
the binary hashes, the code commits and the commands). Everything ran on
`nod` against the LLVM submodule `37a1706d0eac` (Release, assertions,
AMDGPU and AArch64). Instruction counts are static counts of the final
assembly, not run time.

## Answers

| Question | Answer and evidence |
|---|---|
| Was the difference of squares found by the generic search? | Yes. The search had the gMIR region of `difference_squares` (opt -O2, gfx1100) as one training input next to 1431 corpus files. The bank had the base grammar and the window's operators, with no template. It found `keep n0 = x*x; t0 = y*y; t1 = n0 - t0; n3 -> t1` (rule `joint_743e08a976`), proved jointly at widths 8/16/32/64 under `defined(x0, x1)`. The unit test `test_difference_of_squares_is_found` repeats the search on a built region. |
| Are all region inputs, outputs and SSA sharing kept? | Yes, within the subset. The extractor writes `(instruction, result)` identities, the users of each result and the facts. Windows recompute their inputs and outputs from the users of the block. `canonical` renames the whole DAG together, and its key holds the boundary. Two `G_FREEZE` stay two values. Tests: `test_canonical_renaming`, `test_freezes_are_not_merged`, `test_inner_value_with_an_outside_user`, `test_multi_result_instruction`, `test_one_value_for_two_outputs`. |
| Can it find a new shared helper that the region does not have? | Yes. On `shared_helper` (x*(y+1), x*(y-1); after opt -O2 the region is `o1 = (y+1)*x; o2 = o1 - (x << 1)`) it found `t0 = y*x; o1 = x + t0; o2 = t0 - x` (`joint_b421acca3c`). `x*y` is no value of the region; both outputs change; cost 5 -> 4. |
| What does joint selection add over independent selection? | Independent selection takes each output's cheapest candidate, charged with the instructions it reads, then shares instructions. For the helper region it gives cost 6, worse than the region (5): no output alone gets cheaper. For the difference of squares it keeps the product: `s - y*y` charged with `x*x` costs 5, more than keeping `(x-y)*(x+y)` (4). Joint selection finds 4 and 5. On the corpus, joint beat independent in 2 of 177 rules. The other 175 are mostly one-output local rewrites, where the two agree. |
| Do the generated rules really run? | Yes. One `llc` with and without `-gisel-synth-joint-combines` (abort on fallback, verifier). The matcher's debug counters show `matched`/`applied`. 50 MIR cases and 2 lit files check the generated rules. |
| How are definedness, poison, flags, outside users and placement handled? | See below. |
| Does the gain hold in the full LLVM pipeline? | Difference of squares: gfx1100 7 -> 6, AArch64 6 -> 3 (`mul`, `msub`, `ret`). Shared helper: gfx1100 8 -> 7 for the function; AArch64 has a different region after opt -O2 and no match. Held-out corpus: -43 instructions over 7813 files (13 smaller, 2 larger by one), no failures, no fallback changes. |
| Search budget and matcher cost? | Search: 7138 windows in 32 min wall time on 24 processes (41,136 process-seconds). 3732 complete, 2787 bank budget, 619 time budget. SMT: 1234 checks, 12.9 s. Matcher: held-out CPU 647.1 s -> 652.8 s (+0.9%) with 6 rules; 79,354 anchors, 52 applications. |
| Does the online C++ e-graph extractor have this? | No. `GIEGraph.h` and its tree-cost `Extractor` are unchanged. Only the offline synthesizer does joint selection. |

## Phase 1: the difference of squares

`eval/joint_validate.py` (results in `joint/pipeline/`): `opt -O2`, then the
same `llc` without and with the rules. The plugin `llc` without the flag
gives the same code as the stock `llc`.

| Target | Without | With |
|---|---:|---:|
| gfx1100 (`amdgpu11.00-amd-amdhsa`) | 7 | 6 |
| AArch64 (`aarch64-linux-gnu`) | 6 | 3 |

```
gfx1100 with the rule                  AArch64 with the rule
  s_waitcnt vmcnt(0) ...                 mul  w0, w0, w0
  v_mul_lo_u32 v0, v0, v0                msub w1, w1, w1, w0
  v_mul_lo_u32 v1, v1, v1                ret
  s_delay_alu instid0(VALU_DEP_1)
  v_sub_nc_u32_e32 v1, v0, v1
  s_setpc_b64 s[30:31]
```

The MIR cases (25 per target, all pass; the verifier is on in each run):

| Case | Expected | Why |
|---|---|---|
| positive, commuted mul, commuted add | rewrite | |
| `G_MUL x, y` square, `G_ADD y, y`, reversed sub, xor | keep | not the region |
| nsw / nuw on the square | rewrite, flags dropped | the square stays and a new instruction reads it (`relax`) |
| nsw / nuw on the product, nsw sub, nuw add | rewrite | instructions that die: the proof is for the source without flags |
| arguments not noundef | keep | `defined(x)`, `defined(y)` fail |
| square after the product | rewrite | the new instructions go after the square |
| square after a user of the product | keep | no position dominates that user and follows the square |
| second user of x-y or of x+y | keep | the inner value would not die |
| second user of the square | rewrite | it stays anyway |
| square in another block | keep | one block |
| frozen inputs | rewrite | LLVM's own analysis: defined |
| two `G_FREEZE` of x | keep | two values, not the region |
| computed undef | keep | not defined |
| i16, i64 | rewrite | each width has its proof; i64 arguments are `G_MERGE_VALUES` of two copies |

`test/Joint/joint-rules-{amdgpu,aarch64}.mir` (lit) checks the same
behaviour with `update_mir_test_checks.py` CHECK lines, plus the
shared-helper rule and its constant guard.

## Phase 2 and 3

| Requirement | Where |
|---|---|
| sibling input that the other root does not read | the difference of squares: `y` is not read by `x*x`; the windows connect roots through shared values (`test_windows_connect_through_shared_inputs`) |
| inner node with an outside user | an output with its cost (`test_inner_value_with_an_outside_user`); the matcher rejects a would-be-dead instruction with another user (`reject boundary`; MIR `multiuse_*`) |
| multi-result instruction | `(x + y, (x + y) <u x)` -> one `G_UADDO`, one cost (`test_multi_result_instruction`) |
| one SSA value for two outputs | `x + y`, `y + x` -> one kept value (`test_one_value_for_two_outputs`) |
| several outputs replaced | the shared helper rule; the plan keeps `output_replacements` for each |
| canonical renaming and cache key | `test_canonical_renaming` (other orders: same key; another boundary or fact: another key) |
| dominance failure | MIR `square_after_use`, lit `dsq_square_after_use` |
| new shared helper, joint vs independent | `test_new_shared_helper`, pipeline gfx1100 8 -> 7 |

## Semantic counterexamples (tests/test_joint.py)

| Case | Result |
|---|---|
| second output wrong (`n0 + t0` for `n0 - t0`) | refuted |
| a poison source output does not excuse another output (`x << y` poison, `x + y` defined; the new `x + y` is poison exactly then) | refuted, with a model `y >= 32` |
| two `G_FREEZE` of one undef value: `f1 - f2 -> 0` | refuted; no rule; one `G_FREEZE` read twice: `f - f -> 0` proved |
| a guard `defined(x)` removed from a stored rule | `check_rule` refuses it, `joint-emit` skips it |
| inputs not defined in the instance | the candidate is dropped (the rule would never apply to it) |
| the reused square keeps `nsw` | refuted without `relax`, proved with it |
| an inner value with an outside user | it is an output; its instruction stays and its cost counts; no rule |

## Corpus run

Training: `manifests/amdgpu-discovery.txt` (1431 files; 1418 with
regions) and the two examples.

| | |
|---|---:|
| blocks | 9,647 |
| windows (occurrences / distinct) | 32,918 / 7,138 |
| windows rejected: non-convex / too many outputs | 138,424 / 10,918 |
| search status: complete | 3,732 |
| budget: bank terms | 1,826 |
| budget: bank terms and helpers | 961 |
| budget: time (30 s per window) | 619 |
| candidates (sample filter) | 2,084 |
| refuted by SMT / unknown | 916 / 0 |
| proved rules (one output / two outputs) | 177 (173 / 4) |
| with `defined` guards | 6 |
| with a new instruction that two outputs share | 3 |
| joint cheaper than independent | 2 |

`joint-recheck` replayed the 318 stored proofs (all `unsat`) and proved
each emitted width map again from the stored source and candidate (318
valid). `check_rule` found no inconsistent rule.

Selection (`eval/joint_select.py`): all 177 rules in one `llc`, measured on
`manifests/amdgpu-validation.txt` (1469 files, no content overlap with the
training set). A rule is kept if it applied, the files where it applied
got smaller in total, and none got larger, failed or changed its fallbacks.
The two example rules are kept on their own pipeline measurement. Totals:
319,662 -> 319,652 instructions, 6 files smaller, 5 larger, CPU +1.0%
with 177 rules.

| Kept | Rule | Validation |
|---|---|---|
| `joint_743e08a976` | difference of squares | own pipeline |
| `joint_b421acca3c` | shared helper `x*y` | own pipeline |
| `joint_66f36e5034` | `c ^ (c ^ trunc x) -> trunc x` | 3 files, -9 |
| `joint_315c4a0ef9` | `zext(b ^ 1) -> 1 >> b` (i1 b) | 1 file, -8 |
| `joint_a27cbc14a2` | `trunc x + trunc y -> trunc(x + y)` (32 -> 16 only) | 4 files, -1 |
| `joint_f5cef5f7f4` | `select(c, zext(y + C), zext y) -> zext(y + select(c, C, 0))` (C constant) | 1 file, -1 |

Dropped: 152 never applied, 14 applied with no gain, 5 applied in a file
that got larger.

Held-out (`manifests/amdgpu-heldout-codegen.txt`, 7814 files; 1 duplicate
content, 0 in the training or validation sets; the frozen 6 rules):

| | |
|---|---:|
| files compiled with and without | 7,813 / 7,813 |
| new failures / fallback changes | 0 / 0 |
| instructions | 1,750,142 -> 1,750,099 (-43) |
| files smaller / larger | 13 / 2 (+1 each) |
| CPU of the compilations | 647.1 s -> 652.8 s (+0.9%) |
| matcher: anchors / applied | 79,354 / 52 |
| rejected: pattern / types / width / boundary / defined | 79,206 / 112 / 71 / 6 / 0 |

Per rule on held-out: `joint_315c4a0ef9` 11 files, -36 (1 larger);
`joint_a27cbc14a2` 21 files, -8; `joint_f5cef5f7f4` 1 file, +1. The two
example rules and `joint_66f36e5034` found no instance. The held-out gain
comes from small local rules; the two motivating joint rules have no
instance in these test files.

### The fact `defined` in the corpus

Of the 18,950 non-constant inputs of the training regions:

* 92 are `defined` under `isStableValue`;
* 59 are `defined` under LLVM's analysis alone;
* 6,344 are entry copies, and 3 of them are noundef argument copies.

Only 711 inputs are in functions whose arguments are all `noundef`. LLVM's
test IR rarely has `noundef`, so a rule with a `defined` guard seldom
applies to this corpus. This was not measured on frontend-generated code.

## Limits

* One basic block; scalar integers of at most 64 bits; no memory, calls,
  G_PHI, floating point, unspecified bits or immediate UB.
* Windows of at most 5 instructions and 3 outputs; new DAGs of generic cost
  <= 3; one helper of cost <= 2 over the inputs; a candidate list of 12 per
  output. The search reports when these budgets end (`budget: ...`).
* `defined(x)` is conservative: a value read twice requires its inputs to
  be defined, even where the source shares it the same way.
* Constants other than 0, 1, -1 are proved at their own width only.
* No moves of kept instructions: the new instructions go to a position
  that needs none, or the matcher rejects the match.
* The argument fact needs every IR argument `noundef`, because the lowered
  arguments do not record which register holds which argument.
* The online e-graph extractor is unchanged.
