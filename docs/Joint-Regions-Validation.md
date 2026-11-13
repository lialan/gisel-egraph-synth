# Joint region rules: validation

Design: [Joint-Regions.md](Joint-Regions.md). Instruction counts are
static counts of the final assembly, not run time.

# 2026-11-13: several implementations, runs that continue, measured selection

Everything ran on `mi350-bg` (128 cores) against the LLVM submodule
`37a1706d0eac` (Release, assertions), gfx1100, with the corpora of the
first run: training `manifests/amdgpu-discovery.txt` (1431 files, 1416
with regions, and the two examples), selection
`manifests/amdgpu-validation.txt` (1469 files), held-out
`manifests/amdgpu-heldout-codegen.txt` (7813 distinct files; read once,
after the selection was frozen). Artifacts: `tools/gisel-rule-synth/joint/`
(`rules.json` is the frozen set of 21 rules, `proofs/` its proofs) and
`joint/measured/` (all candidates, the search records and statistics, the
measurement of every candidate, the validation and held-out evaluations,
the proof replay, the ISA of the cases below, the statistics of the
subset runs (`subset-runs.json`), `provenance.json` with the commands and
the hashes of the two `llc`s).

## What changed

| Gap of the first run | Now | Where |
|---|---|---|
| a candidate had to be cheaper in generic cost | `--cost-slack k`: up to the window's cost + k (0 here) | `joint.Limits.max_after`, `_bank_rows`, helpers, `select`, `check_rule` |
| the first proved candidate ended a window | up to `--semantic-variants` proved shapes per window (6 here); one per shape; a state per candidate | `joint.search_window` |
| a time budget returned no candidate | the candidates made before the budget are proved or kept pending | `Search.run`, `search_window` |
| progress per window not kept | each window is a task of the agenda (stage `joint`), proofs in the history, rules in a store | `girs/joint_tasks.py` |
| a file's total credited to every rule in it | each candidate measured alone over the frozen rules; per-window comparison; set built and validated with `select.py` | `eval/joint_measure.py` |
| equal-cost rules could undo each other | `original_only` matcher guard; rewrite cycles kept out of the selection | `GISynthJoint.h`, `joint.rewrite_cycles` |

## Search on the training corpus

The same windows (7135 distinct of 32,914), the same budgets (30 s per
window, 200,000 terms, 256 helpers, 12 candidates per output, 6 proofs per
window), 96 processes, both runs on `mi350-bg`. The old run is the code of
`06e517f`.

| | old policy (`06e517f`) | slack 0, 6 shapes |
|---|---:|---:|
| windows with status `complete` | 3781 | 1840 |
| windows that hit the time budget | 1301 (no candidate kept) | 2122 (candidates kept) |
| candidates (sample filter) | 2060 | 7306 |
| proved / refuted / unknown | 175 / 898 / 0 | 1187 / 1386 / 0 |
| proved rules of equal cost / cheaper | 0 / 175 | 884 / 303 |
| windows with a rule / with two or more | 128 / 23 | 686 / 204 |
| rules with two or more outputs | 3 | 55 |
| with a new instruction that two outputs share | 3 | 23 |
| candidates left pending (proof budget, quota) | — | 2404 |
| candidates without a match order (`no_plan`) | not counted | 1964 |
| solver calls / solver time | 1211 / 31.7 s | 3752 / 71.7 s (368 from the history) |
| process time / wall time | 72,687 s / 14.7 min | 114,476 s / 20.3 min |

The time budget ends more windows with the slack: a helper may now cost
as much as the window minus the two instructions that read it, so the
banks of the helper round are larger. 2122 windows ended on time and
4941 on a truncated bank; their candidates are proved or pending, and the
agenda reopens them when `--time-s` or `--max-terms` grows (205 windows
stay open for the next run without a larger budget: their proof budget
ended). The 1964 `no_plan` candidates are reachable only through a
constant (the matcher's `UserOf` starts from bound registers only); the
first run dropped them silently.

The time budget of a window depends on the load of the machine: the old
run on `nod` with 24 processes had 619 windows on time, here 1301.

## Old and new policies on a fixed subset

The 1000 most frequent windows of the training corpus, the same budgets,
64 processes, a cold cache each, nothing else on the machine; the code
of each run was frozen before it started.

| Run | Rules (equal cost) | Windows with 2+ | Windows on time | Process time | Wall |
|---|---:|---:|---:|---:|---:|
| C0: code of `06e517f` | 6 (0) | 1 | 105 | 6,643 s | 155 s |
| C1: new code, historical policy | 6 (0) | 0 | 115 | 7,442 s | 137 s |
| C2: slack 0, 6 shapes | 101 (95) | 17 | 226 | 11,806 s | 206 s |
| C2 again, warm cache | 101 | | | 6.8 s | 1.3 s |
| C2b: slack 1, 6 shapes | 226 (220) | 51 | 357 | 16,743 s | 281 s |
| C3: historical policy, runs of 45 s until done (4 + 1 empty) | 6 | | | 9,574 s | 178 s |
| C4: slack 0, runs of 45 s until done (6 + 1 empty) | 101 (95) | 17 | | 15,623 s | 277 s |

* **The same rules.** C0, C1 and the last run of C3 have the same 6 rule
  ids; C2, the last run of C4, the resumed run below and the warm run have
  the same 101. This was observed, not guaranteed: with a time budget per
  window, the load of the machine decides which windows end on time.
* **Short runs cost more.** The end of each 45-s run cuts the 128 windows
  in flight (2 per process); the next run searches them again from the
  start (the candidates they had found are kept). Here that is +29%
  (historical policy) and +32% (slack 0) process time for the same
  result.
* **Warm.** The second C2 run searched only the 16 windows whose proof
  budget had ended (in `prove` mode, without a search), and nothing else.
* **Slack 1** more than doubles the rules (226, 25 with two outputs) and
  the time-budget hits; it was not measured further.

**Processes.** The 100 most frequent windows with a time budget that does
not end (`--time-s 100000`), slack 0, 1, 8 and 32 processes: the same 12
rules and the same record of every window (status, candidate states,
verified ids, reasons). The first comparison found 4 windows labeled
`bank_truncated` with some process counts and `complete` with others: a
term bank is shared by the windows of a process, and its truncation at a
higher cost (by another window) was charged to every window that used
it. `_bank_rows` now counts a truncation only at a cost that the window
reads, as the single-output search does; the rules were the same before
and after. (The full run above was made before this fix; some of its
`bank_truncated` labels are of this kind, its candidates are not.)


## Measured selection (validation)

One `llc` with the 6 rules of the first run (the frozen baseline) and the
1182 other proved rules of the full run as candidates (`joint-emit`
accepted all; the run found 5 of the 6 baseline rules again, with the
same ids; the sixth, the shared helper `x*y`, ended on its window's time
budget before the helper round reached it, kept its equal-cost candidate
`joint_7632ea4890`, and is reopened by a larger `--time-s`).
`eval/joint_measure.py` (control, baseline, screen, solo, set). 1469
files, 0 compile failures.

| Profitability of the candidates | |
|---|---:|
| never matched in the validation corpus | 871 |
| screened, but not applied over the baseline | 18 |
| applied, no instruction fewer | 160 |
| a file worse (more instructions) | 98 |
| fewer instructions, no file worse | 35 |

Of the 35: 15 selected; 10 rewrite cycles; 7 without a gain in the set
(their instances overlap rules already selected); 3 dominated in their
window. Of the 15, 14 have equal generic cost (`original_only`); one is
cheaper. 41 windows had two or more candidates that reached a compile.

| Configuration (1469 files) | Instructions | Encoded bytes | Smaller / larger files |
|---|---:|---:|---:|
| baseline (6 rules) vs control | −19 | −64 | 6 / 0 |
| baseline + 15 vs baseline | −190 | −512 | 23 / 0 |

The set was emitted in its final order (the baseline first), built and
measured again on the validation corpus: the same −190 / −512, 23 / 0, no
new failure, no fallback change. `joint-recheck` replays and redoes the
proofs of all 21 rules (21 valid).

### The 10 rewrite cycles

All ten are rules whose result contains their own source pattern:
reassociations of a chain of three `G_ADD` (solo −37 each, five
windows), `(a − b) + c -> a + (c − b)` (−6, two windows) and of an
`G_AND`/`G_OR` chain (−1, three windows). Without the matcher guard they
would rewrite their own result again; with it each original chain is
rewritten once, which is what the solo measurement saw. They are kept out
of the selection as the task requires; a direction (an order of the
operands that the result must respect) would make them acyclic.

## Held-out (once, frozen set)

7813 files (one duplicate removed), `--exclude` training and validation.

| | Instructions | Encoded bytes | Smaller / larger files | Failures / fallback changes |
|---|---:|---:|---:|---:|
| baseline (6 rules) vs control | 1,750,142 -> 1,750,099 (−43) | −256 | 13 / 2 | 0 / 0 |
| baseline + 15 vs baseline | 1,750,099 -> 1,749,644 (**−455**) | **+1,976** | 85 / 3 | 0 / 0 |

* The baseline row is the result of the first run, measured again.
* Per rule (applications, files, the change of the files where it
  applied): `select(c, y+1, y) -> y + zext(c)` 880 / 85 / −435. Of the
  other 14, 7 applied (2 to 9 instructions each in their files, 35
  together; their files overlap those of the first rule, so the numbers
  do not add up to the total) and 7 never applied on held-out.
* The three larger files: `divu_remu.ll` +3, `int-div-01.ll` +2,
  `ppc64-r2-alloc.ll` +5.
* **Encoded size grows** by 1976 bytes although instructions fall: the
  new forms use VOP3 encodings (`v_add3_u32`, `v_cndmask_b32_e64`, 8
  bytes) for VOP2 ones (4 bytes). On the validation corpus the bytes fell
  (−512). The selection's metric is the instruction count; a selection by
  encoded bytes would decide otherwise for this rule.
* CPU of the compilations: baseline 870.6 s, with the 15 rules 870.5 s
  (both with the matcher's debug counters on; the control runs without
  them and are not comparable for time).

## Cases

`joint/measured/cases.txt` has the assembly of both (`eval/joint_case.py`
on the measuring `llc`).

**One window, three implementations of equal cost.** The window
`n0 = x + (-1); n1 = n0 - z` (from `frem.ll`) has three proved
candidates, each measured alone over the baseline:

| Candidate | Generic cost | Solo (validation) |
|---|---:|---:|
| `x + (-1 - z)` (`joint_78a00c1e4d`) | 2 -> 2 | −19 instructions, selected |
| `(z - x) ^ -1` (`joint_3e25c8df5f`) | 2 -> 2 | +3, regression |
| `x + (-1 ^ z)` (`joint_f41648b70a`) | 2 -> 2 | +1 net, regression in `frem.ll` |

In `frem_f32` the baseline computes `s_add_i32 s5, s6, -1; s_add_i32 s4,
s7, -1; s_sub_i32 s5, s5, s4`; with the first candidate the later
combiners fold it to `s_add_i32 s4, s6, -1; s_sub_i32 s5, s7, s6` (107 ->
106); the two others keep the subtraction and add an `s_not_b32` (107).
`-1 - z` and `-1 ^ z` are one value; they select differently.

**Equal generic cost, fewer machine instructions.** `n0 = y + 1; n1 =
select(c, n0, y)` -> `t0 = zext(c); t1 = y + t0` (`joint_48f67f7f94`,
2 -> 2, proved at 8/16/32/64 bits, no `defined` guard): the quotient
correction of the integer division expansion. In `udiv.ll` (gfx1100):

```
baseline (udiv_i32, 34)                 with the rule (33)
v_add_nc_u32_e32 v2, 1, v3              v_sub_nc_u32_e32 v2, v0, v1
v_sub_nc_u32_e32 v4, v0, v1             v_cmp_ge_u32_e32 vcc_lo, v0, v1
v_cmp_ge_u32_e32 vcc_lo, v0, v1         v_cndmask_b32_e32 v0, v0, v2, vcc_lo
v_cndmask_b32_e32 v2, v3, v2, vcc_lo    v_cndmask_b32_e64 v4, 0, 1, vcc_lo
v_cndmask_b32_e32 v0, v0, v4, vcc_lo    v_cmp_ge_u32_e32 vcc_lo, v0, v1
v_add_nc_u32_e32 v3, 1, v2              v_mov_b32_e32 v1, 0
v_cmp_ge_u32_e32 vcc_lo, v0, v1         v_cndmask_b32_e64 v0, 0, 1, vcc_lo
v_dual_mov_b32 v1, 0 :: v_dual_cndmask_b32 v0, v2, v3
                                        v_add3_u32 v0, v3, v4, v0
```

The two corrections become one `v_add3_u32`; `s_udiv_i32` 37 -> 35
(`s_cselect_b32` of the compare and one `s_add_i32` instead of add,
compare and select), `udiv_v4i32` 100 -> 94. The generated rule
(`td/GISynthJointCombines.td`):

```
def joint_48f67f7f94 : GICombineRule<
  (defs root:$root, gisynth_joint_plan:$plan),
  (match (G_SELECT $d0, $o0, $o1, $o2):$root,
         [{ return gisynth::joint::rules::match_joint_48f67f7f94(*${root}, MRI, ${plan}, JointEnv); }]),
  (apply [{ gisynth::joint::rules::apply_joint_48f67f7f94(B, ${plan}); }])>;
```

`test/Joint/joint-rules-measured-amdgpu.mir` checks it at 32 and 16 bits,
twice in a row, with the arms swapped and with another constant (no
rewrite), and the other selected rules of these cases, among them the
two-output rule `m = x & 15; x - m -> x ^ m` with its guard `defined(x)`.

## Runs that continue

A run of the subset (slack 0) was interrupted with SIGINT after 40 s
(`--checkpoint-s 5`; exit status 130). Its agenda had 334 windows; the
running windows finished and were committed. The next run searched the
666 windows without a row and 4 that the first run left partial for
`proofs` (proved in `prove` mode, without a search); none of the 330
other windows was searched again. Together they have the 101 rules of the
uninterrupted run C2. The test `test_rules_are_published_before_the_task`
makes the publication of a rule fail: the agenda then has no row for
that window, and every committed row names rules that are in the store.

Budgets reopen only what they blocked (`test_a_budget_reopens_only_what_it_blocked`):
windows cut by a bank of 60 terms are not searched again with the same
budgets, and are searched again (as a search) with more terms; the domain,
and so the rules of the first run, stay.

Cache identity: the rows and the rule store of a domain are keyed by the
proof model (`joint_tasks.semantics_sha`), the search code
(`known.search_sha`, `JOINT_SEARCH_VERSION`) and the limits that decide
which candidates exist, among them the cost slack; the budgets are its
depth. Measurements are keyed by the `llc` binary, the flags, the content
of the file, the enabled rules and `METRIC_VERSION`. A time budget makes a
run depend on the load (the old run had 619 windows on time on `nod`, 1301
here); the results above do not claim bit-identical runs under time
budgets.


## Tests

| Test | Result |
|---|---|
| `tests/test_joint.py` (23, of which 7 new: implementations, identity, cost policy, partial results, pending proofs, quota release, cycles) | pass |
| `tests/test_joint_tasks.py` (6: resume, budget reopening, proofs across runs, publication order, process counts, identity) | pass |
| `tests/test_joint_measure.py` (3: solo status, window and set, cycle) | pass |
| `unittests/GISynthJointTest.cpp` (3: guard, rewrite back, screening) and the other unit tests | 275 pass |
| lit (`test/Joint` with the 21 rules, and the rest) | 26 pass, 2 unsupported (`SynthChain`, as before) |
| `joint-emit --check`, `joint-recheck` (21 rules) | clean, 21 valid |
| full Python suite (`unittest discover`) | 749 pass, 2 skipped |

## Limits

* The screen sees the MIR without joint rules: a candidate that matches
  only after a baseline rule applied is not measured.
* A rule of equal cost replaces only instructions that the combiner did
  not create: a chain of such rules (A, then B on A's result) is cut after
  the first.
* The cycle check is structural and inside the result of a rule; a match
  that the instructions around a result complete is covered only by the
  matcher guard.
* Static instruction counts are not run time, and fewer instructions came
  with more encoded bytes on the held-out corpus.
* Most measured gain comes from one rule; 871 of 1182 candidates have no
  instance in the validation corpus (LLVM CodeGen tests, not workloads).

# 2026-11-12: the first run

The rest of this document is the validation of the first run, on `nod`
against the same LLVM. Its artifacts are those of `joint/` other than
`rules.json` (now the frozen set of 21 rules, the 6 of that run first)
and `measured/`.

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
