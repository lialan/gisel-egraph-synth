# gisel-rule-synth

Offline tool that discovers, generalizes, proves and generates GlobalISel
combine rules (GIRuleSynthesizer). Normal compilation only runs the
generated `GICombineRule`s through the existing combiner. No solver, search
engine or e-graph runs inside LLVM.

## Requirements

- An LLVM build with the targets to generate for (AMDGPU, AArch64), for
  `llc`. An assertions build is needed by `select` (it counts rule matches
  with `-debug-only=gisel-synth`).
- Python 3 with the z3 and numpy modules (`pip install z3-solver numpy`), but
  only for `synth`, `mine` and `recheck`. `extract`, `select`, `report` and
  `emit` need no solver, so a normal LLVM build never needs z3.

## Two layers: the library and the target profiles

- **`rules.json`, the rule library**, is target independent. A rule is a
  proved refinement of generic MIR, `S -> T if P`, with its proof records. It
  holds every proved rule: the ones that reduce cost, equal-cost rewrites,
  rules dominated by a better rule with the same source, and the rejected
  candidates.
- **`targets/<Target>.json`, a target profile**, says which library rules
  that target runs and why: corpus coverage, novelty against the target's
  existing combiner, redundancy, measured effect on the final code, ranking.
  It contains no semantics; the same proofs serve every target.

`emit` writes each rule record once and one `GICombineGroup` per target
(`gi_synth_combines_amdgpu`, `gi_synth_combines_aarch64`). To add a target:
describe it in `girs/targets.py`, include the group in its pre-legalizer
combiner behind a flag, and run `select`.

## The complete run: `mine`

```sh
S=llvm/utils/gisel-rule-synth/gi-rule-synth.py
$S mine --config llvm/utils/gisel-rule-synth/configs/m3-auto.json \
        --run-dir runs/m3-auto
```

`mine` goes from a configuration and corpus manifests to a selected and
checked rule set and its report (`report.md`, `report.json`), without a
manual step between the stages:

| Stage | Result |
|---|---|
| `identity` | what the run is made from: source commit and dirty state, hashes of the tool, of the semantic model and of the registry, the compiler, the frozen library and profiles, the manifests, the budgets and the seed |
| `prepare` | the `opt -O2` form of every file (the second pipeline) |
| `extract` | the corpus of the discovery files, written by the baseline pipeline (the synthesized rules are off), and the legality table of the target |
| `discover` | candidates, preconditions and proofs: the rule library of the run |
| `build` | a compiler with every candidate of the library |
| `measure` | the selection files with and without every candidate |
| `select` | the target profile |
| `verify` | the selected set on every selection file: compile failures, machine verifier errors, changed SelectionDAG fallbacks, files with more instructions. A rule that makes a file worse is removed, and the check runs again |
| `freeze` | hashes of everything that decides the result. The held-out files are not read before this stage |
| `heldout` | the frozen set and the reference sets on every role and pipeline |
| `report` | the counts, the relation to the frozen library, the search record and the evaluation |

- **Resume.** Each run has a directory. A stage writes a record in
  `state.json` with a hash of its inputs; `mine` skips a stage whose record
  has the hash of the current inputs. An interrupted run continues, and a
  changed input (a manifest, a budget, the tool) runs the stages after it
  again. The stages with many compiler runs keep their results per file.
  `--until STAGE` stops after a stage; `--force STAGE...` runs stages again.
- **Configuration.** `configs/*.json`: `mode`, `target`, `manifests` (role ->
  file with one `.ll` path per line), `search` (grammar, budgets, seed,
  `regions`, `siblings`), `select`. `girs/mine.py` (`DEFAULTS`) has every key. `--local
  FILE` gives the values of one machine (compiler paths, reference
  compilers, jobs).
- **Roles.** `discovery` files give the corpus. `discovery` and `validation`
  files select the rules. `heldout` files are compiled only after the set is
  frozen; `frozen.json` counts the held-out evaluations of a run directory.
  A file must not be in two manifests. `eval/make_manifest.py` writes a
  manifest from directories with the baseline compiler alone.
- **Modes.** `semantics-only`: the candidates come from the enumerative
  search alone (operator semantics, types, costs, budgets). The rewrites of
  the e-graph combiner, the composition of rules and the frozen library are
  not inputs, and the run fails if a rule has another source. `hybrid` adds
  the e-graph candidates and the composition; each rule records its sources.
- **Pipelines.** Every measurement is made for `.ll -> llc` (`direct`) and
  for `.ll -> opt -O2 -> llc` (`opt-O2`), and reported separately.
- **Export.** A run does not write `rules.json` or `targets/`. `mine
  --export` copies the library and the profile of a finished run there.
  `compare-runs RUN...` compares finished runs.

## Commands

The steps of `mine` are also commands:

```sh
S=llvm/utils/gisel-rule-synth/gi-rule-synth.py
E=llvm/utils/gisel-rule-synth/eval/compare.py

# 1. Corpus: gMIR trees + GISelValueTracking known bits, as JSON lines.
#    Depth 2 is searched; depth 3 is used for rule composition and coverage.
$S extract --llc build/bin/llc -o corpus-d2 --ll-list train.txt
$S extract --llc build/bin/llc -o corpus-d3 --ll-list train.txt --depth 3
$S extract --llc build/bin/llc -o seed-d3 --depth 3 \
    --mir llvm/utils/gisel-rule-synth/corpus/seed.mir

# 1b. Second candidate source: the rewrites that the e-graph combiner
#     finds on the same files, as JSON lines (one record per region).
$S egraph-export --llc build/bin/llc -o egraph-train --ll-list train.txt

# 2. Discover, generalize, synthesize preconditions (CEGIS), prove (z3),
#    compose. Writes rules.json, proofs/*.smt2 and rules.stats.json.
$S synth corpus-d2 llvm/utils/gisel-rule-synth/corpus/seed.jsonl \
    --compose-corpus corpus-d3 seed-d3 --egraph egraph-train

# 3. Select per target. Needs an llc with every candidate compiled in:
$S emit --all-candidates && ninja -C build llc
$E --llc build/bin/llc --list train.txt -o cmp.json --modes base,synth
$S select --target AMDGPU --llc build/bin/llc --corpus corpus-d3 seed-d3 \
    --compare cmp.json
$S report --target AMDGPU      # ranked rules with the evidence

# 4. Generate TableGen + C++ (pure function of rules.json and the profiles).
$S emit && ninja -C build llc
$S emit --check         # fails if the generated files are stale

# Re-prove every rule in the library from its JSON form.
$S recheck

# The operators: what each stage supports, and the checks of the models.
$S capabilities                       # one row per operator
$S check-ops --llc build/bin/llc      # evaluator against SMT and against llc
```

Using the generated rules:

```sh
llc -global-isel -amdgpu-gisel-synth-combines ...    # off by default
llc -global-isel -aarch64-gisel-synth-combines ...   # off by default
llc ... -debug-only=gisel-synth     # each guard that is evaluated / passes
```

## How a rule gets into the library

0. **Corpus** (`GISynthCorpusExtractor`, `corpus.py`). The extractor pass
   has no list of opcodes: it writes a tree for each scalar instruction that
   is an operator of the operator table of the e-graph combiner (GIEGraph.h,
   `OpProperties`), except the pointer operators, `G_PHI` and the
   terminators. A node has the opcode (`op`), the predicate of a comparison
   (`pred`), a trailing immediate (`imm`), the index of the result if the
   instruction has several results (`res`), and the type name (`type`); a
   tree is written for each result. `corpus.py` accepts a tree if every
   operator has a model in the registry (`ops.py`) and counts the other
   trees by reason (`corpus.unsupported_reasons` in `rules.stats.json`,
   next to the occurrences of each operator, `corpus.operators`). A new
   operator of the table with a model needs no change in these two places.
   A node and an input also have `noundef` (the value is neither undef nor
   poison, `isGuaranteedNotToBeUndefOrPoison`): the search without the
   e-graph combiner can find a rule with the precondition `def(x)`. The two
   results of one instruction have the same `mi`. `llc
   -gisel-synth-legality=FILE` writes what the legalizer does with each
   operator at each combination of scalar widths (`targets.Capability`).
1. **Discovery** (`discover.py`). Enumerative search for a cheaper
   expression that agrees with the source on samples, then an SMT proof under
   the instance's concrete known bits. The source can have every operator
   with a model.

   *The registry decides what a term bank can build.* `OpInfo.rhs()` says if
   a rule can create an operator, or why not (an operation that can trap and
   `G_FREEZE` are matched and not created). `ops.signature_ok` is the one
   type check: the number of operands, the type rule and the kind of each
   value (integer or floating point; two types of one width are two type
   classes). `ops.search_keys` gives the keys of an operator: one for each
   predicate, each value of an immediate (`imm_domain` and the values of
   the source) and each result. An operator without a sample kernel
   (`kernels.py`) is evaluated with the evaluator of the registry. A new
   operator needs an entry in the registry and no change in `discover.py`.

   `synth --grammar` selects the operators of a bank:

   | Grammar | Operators |
   |---|---|
   | `base` | `ops.ENUMERATED`: nine arithmetic and bit operations, three integer casts |
   | `source` (default) | `base` and the operators of the source that a rule can create |
   | `all` | `base` and `ops.ENUMERATED_EXTRA` (32 operators with one result and no attribute) |
   | `registry` | every operator with `rhs() == 'yes'`: also comparisons, `G_SELECT`, the overflow and carry operators, the funnel shifts, the conversions with a floating-point value, the operators with an immediate |
   | `auto` | in steps: `source`, then the operators that the target has at the types of the source (`--legality`), then `registry`. Each step is a function of the operators and types of the source, of the registry and of the target, not of what the source computes |

   The enumeration is done once per *signature* (type class of every
   input), in a term bank pruned by observational equivalence, and reused by
   every instance with that signature whatever its shape or bit widths. A
   bank has one term per sample fingerprint: that is a filter, not a proof,
   and a term can hide another term with the same samples (the region step
   below has its own candidates for that reason).

   *Budgets.* `--max-terms` (terms of a bank), `--max-evals` (candidate
   terms that a bank evaluates per cost level; inside a level each operator
   gets a share, so the operators at the end of a grammar are also tried),
   `--max-proofs`, `--max-candidates`, `--time-budget-s`, `--timeout-ms`.
   The search of each instance ends with a reason (`discover.STOPS`):
   `complete`, or the budget that ended it. A budget is not "no result in
   the grammar"; `rules.stats.json` counts the reasons and `--search-log`
   has every candidate with its status.

   Instances are visited by corpus frequency times instructions at stake,
   with a share (`--explore-share`) for the rarest root operators. Refuting
   SMT models become samples for the rest of the run. The proved candidates
   of an instance are kept in `--cache` by the instance, the limits and the
   model hash; an UNKNOWN answer is not kept.
2. **Generalization** (`synth.py`, `precond.py`). One rule per (source,
   replacement), widths abstracted. CEGIS over a known-bits grammar finds
   *every* minimal sufficient conjunction, not just the first; strictly
   stronger ones are dropped. The precondition of a rule is the disjunction
   of conjunctions found from its different corpus instances, each proved on
   its own width schedules. `finalize` keeps the disjuncts that add corpus
   coverage (most coverage first, cheapest guard on ties), proves the kept
   disjunction as a whole, and marks a rule `dominated_by` another rule with
   the same source whose replacement is no more expensive and whose
   precondition it implies (proved).
3. **Composition** (`compose.py`). On deeper corpus trees, verified rules are
   applied as rewrite steps (bounded breadth-first search, at most
   `--compose-steps` steps). A result that is cheaper than the source, needs
   at least two steps, and is not what a single rule gives at the root is a
   proposal; it goes through the same proof and generalization as a
   discovered rule and becomes a direct *macro rule* (provenance
   `composition`, with the ids of the steps). The steps are only a search
   heuristic: the macro rule has its own proof. A step or a result can move
   an operation to a wider type of at most 32 bits (the register width of
   the targets in `girs/targets.py`); a wider operation is never proposed.

4. **E-graph candidates** (`egraph.py`). `llc -gisel-egraph-export=FILE`
   makes the e-graph combiner write, for each region with a cheaper form,
   the original expression DAG, the DAG that the extractor selected, the
   inputs with their known bits and the roots (format version 1, one JSON
   object per line; the function is not changed). The importer reads each
   record in three steps. (a) The maximal subterms that the two DAGs have in
   common become variables. (b) The pair is divided at the operators that
   did not change, until each part is proved with the known bits of the
   region. (c) Each subterm of a part becomes a variable if the part is
   still proved. A part is a *candidate*: it goes through `Synthesizer.add`
   as an enumerative discovery does (generalization, CEGIS, width schedules,
   proofs), with the provenance `egraph` and the names of the e-graph rules
   that fired. The e-graph is not trusted: a candidate that is not proved
   gives no rule. A rewrite that gives no candidate is counted with its
   reason in `rules.stats.json` (`egraph.rejected`).

5. **Regions with several outputs** (`region.py`, `synth --regions`). A
   rule of the search above replaces the root of a tree. A value below the
   root that has another user stays, so the rule removes the root only. Such
   a value is a second output of the region. The step searches a replacement
   of that value that shares instructions with the replacement of the root:

   ```
   %s = G_SUB %x, %y            ; %s has other users
   %c = G_ICMP ugt, %s, %x      ; the root
   ->
   %s, %c = G_USUBO %x, %y
   ```

   A rule with a region has `region.outputs`: `(node, result)` of each
   value that is replaced (node 0 is the root, node k the k-th value below
   it in pre-order) with its replacement. Equal instructions of the
   replacements are one instruction and their cost counts once; two results
   of one instruction are one instruction.
   - *Candidates*: the terms of the bank, the values that the instructions
     of the other replacements compute (the other result of an instruction
     with two results), and for the root a result of an instruction with
     several results of which another result is a value below the root.
   - *Proof*: one query per width map with every output
     (`smt.joint_violation`), under the precondition of the rule of the
     root. A width map without that proof is not a width of the new rule.
     The replacements read each input once in all.
   - *Generated code*: the guard also checks that each replaced value has
     another user, is in the block of the root, and that no input of the
     replacement is defined after the first of them (`isJointRegion`). The
     apply function builds the replacement before that first value and
     erases the old instructions.
   - *Limits*: one basic block; the other outputs are below the root (step
     6 has two roots that share only operands); a value that occurs twice
     in the source and a result of an instruction with several results are
     not replaced; no computed constants.

6. **Regions with two roots** (`sibling.py`, `synth --siblings`). The
   second root (the sibling) is not in the tree of the first: it is one
   instruction of the same block that reads only inputs of that tree.

   ```
   %d = G_SUB %x, %y                ; the sibling
   %c = G_ICMP uge, %x, %y
   %r = G_SELECT %c, %a, %b         ; the primary root
   ->
   %d, %o = G_USUBO %x, %y
   %r = G_SELECT %o, %b, %a
   ```

   - *Pairs*: the corpus has one tree per root. `sibling.load_pairs` pairs
     the records of one basic block by their registers: each tree with each
     record of one instruction whose inputs are inputs of the tree. An
     instruction of the tree, another result of such an instruction and the
     definition of an input are not siblings.
   - *Candidates*: no rewrite is given. The values of instructions that a
     replacement can read for no added cost are leaves of the term bank,
     next to the inputs: the results of the sibling if it stays, or the
     other results of a new instruction with several results of which one
     result has the samples of the sibling (the sibling is then replaced by
     that result). A term with the samples of the primary root that reads a
     leaf is a candidate; the leaf is replaced by its definition. A
     candidate must be cheaper than the two roots and than the rules of the
     primary root alone.
   - *Proof*: the joint query of step 5 with the two roots, with a
     precondition from the same grammar and the same width schedules. A
     sibling that stays is its own replacement. The source has undefined
     behaviour if one of the roots has.
   - *Rule*: `region.siblings` has the sibling, `stays` and its
     replacement. The combine rule matches the primary tree.
   - *Generated code*: `sibling_<id>` finds the sibling among the first
     users of its first operand (`findSiblingRoot`). The guard checks the
     widths of its results with the widths of the pattern, and that the two
     roots are near in one block (`siblingInsertPoint`). The apply function
     builds the replacement before the first of the two roots; a sibling
     that stays and that is after the root is moved before it (its operands
     are inputs of the tree).
   - *Limits*: one basic block and one sibling; the sibling is one
     instruction; a sibling that is replaced has one result; no `G_FREEZE`
     in a root; a sibling that can trap is not emitted.

A replacement can have a *computed constant*: a constant that the source
does not have. The importer looks for a recipe, an expression over the
constants of the source (`G_ADD`, `G_SUB`, `G_MUL`, `G_AND`, `G_OR`, `G_XOR`,
the shifts, min/max and the saturating addition and subtraction;
`ir.RECIPE_OPS`) or the mask of the low bits of a narrower type of the source
(`G_ZEXT` of the literal -1), and tries at most three recipes. The rule then
matches the variables of the recipe only as constants (`const_vars`), and
the proof holds for every value of them. The generated guard reads the
constants, and it rejects a recipe that is not defined or that gives a shift
amount that is not smaller than the width; the proof assumes exactly that
check (`smt.Encoder.recipe_guard`). The apply function computes the constant
with `APInt`.

Everything is deterministic: every solver check runs in a fresh solver
context, so `rules.json` and the proof files are byte-identical between runs
on the same corpus.

`rules.stats.json` and each target profile have a `provenance` record: the
version of the tool and a hash of its source files, the commit that was
checked out when the tool ran, and `llvm_dirty` (the `llvm` directory had
changes that were not committed). The commit is necessarily older than the
commit that contains the generated file; the hash identifies the tool
without a commit.

## How a target selects (`select.py`)

Candidates are the library rules that reduce cost and are not dominated. A
rule that moves an operation to a wider type is a candidate only if that
type is not wider than the registers of the target (`Target.native_bits`):
there the wider operation uses the same register. For each candidate the
profile records

- **coverage**: occurrences of the source pattern in the target's corpus and
  how many pass the guard (offline, no compiler);
- **novelty**: the rule alone against the target's existing combiner, on a
  MIR function built from its own training example (`new`, `covered`,
  `worse`, `not_fired`). The run has a time limit. If the combiner does
  not end (the rule loops with an existing combine), the class is `loop`
  and the rule is never selected (`probe_loop`). If llc fails, the class is
  `error`: the novelty is not known, and the rule is not a new rule;
- **redundancy**: other synthesized rules reach the same result;
- **measured effect**: matches and applications when the files are compiled
  with every candidate, and the change in instruction count of the final
  code when only that rule is disabled;
- **cost**: generated records, pattern nodes, guard cost (known-bits
  queries).

The selected set is then refined *inside the set* (with every candidate
enabled a second rule can take over when one is disabled and hide its
effect): rules that add instructions are dropped, and so are rules that
query known bits but remove nothing (`--keep-unmeasured` keeps those), one at
a time until the set is stable. The profile lists every candidate with its
selection and the evidence, and the measured totals of the final set.

**One-use variants.** A rule removes the interior operations of its source
only if they have no other user. If its replacement costs as much as the
root alone, the rule removes nothing from a source with a shared interior
value; it only changes the code, and the target can select worse code for
the result. Such a rule `R` has a variant `R_1u` with a one-use guard on
every interior value. With every candidate enabled, one of the two fires on
a source without a shared value and the other takes its place when the
first is disabled, so the measured effect of `R` is the effect of its
firings on shared values. If those remove no
instruction, the profile selects `R_1u` (`one_use_variant_selected`); if
`R` is dropped later because it adds instructions inside the set, `R_1u`
takes its place.

## Files

| Path | Contents |
|---|---|
| `girs/ops.py` | the operator registry: shape, typing, evaluator and SMT encoding of each generic opcode; `Provider` for target operators |
| `girs/gmir_ops.json` | typing metadata of the operators, written by `llc -gisel-egraph-print-ops` from the property table of the e-graph |
| `girs/opcheck.py` | checks of the operator models (evaluator against SMT, evaluator against the folds of llc) |
| `girs/ir.py` | typed expressions: operators with attributes and result indices, constants, computed constants |
| `girs/egraph.py` | import of the e-graph export: candidates, recipes of computed constants |
| `girs/corpus.py` | corpus reader, DAG-aware tree conversion |
| `girs/discover.py` | grammars, term banks, fingerprints, concrete SMT proof |
| `girs/kernels.py` | sample kernels of operators (speed only; the evaluator of the registry is the reference) |
| `girs/region.py` | rules with several outputs: candidates, joint proof |
| `girs/sibling.py` | rules for two roots: pairs from the corpus, candidates, rule creation |
| `girs/mine.py` | the complete run: stages, state, resume, export |
| `girs/report.py` | the report of a run and the comparison of runs |
| `girs/precond.py` | precondition grammar (eval / z3 / C++), implication |
| `girs/synth.py` | generalization, width schedules, CEGIS, disjunctions, dominance, rule library |
| `girs/compose.py` | rule composition into macro rules |
| `girs/match.py` | rule matching on corpus trees, coverage |
| `girs/smt.py` | z3 backend and gMIR bitvector/poison encoding |
| `girs/fp.py` | IEEE formats of the conversion operators: exact evaluator and z3 encoding |
| `girs/targets.py` | per-target compiler flags and names |
| `girs/measure.py` | running llc, instruction and rule counters |
| `girs/select.py` | per-target coverage, novelty, redundancy, ranking, selection |
| `girs/emit.py` | `GICombineRule`, guard and per-target group emission |
| `corpus/seed.mir`, `corpus/seed.jsonl` | seed inputs (not rules) and their extracted corpus |
| `rules.json` | the target-independent rule library with proof records |
| `targets/*.json` | target profiles |
| `proofs/` | SMT-LIB2 queries of the proofs, named by SHA-256 |
| `eval/compare.py` | compiles a file list as base / synthesized rules / e-graph and compares the final code |
| `eval/make_manifest.py` | writes a corpus manifest with the baseline compiler |
| `configs/*.json` | run configurations of `mine` |
| `manifests/*.txt` | corpus manifests: discovery, validation, held-out |
| `tests/*.py` | unit tests (`python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests`); the tests of the real extraction chain need `build/bin/llc` or `GIRS_LLC` |

Generated in-tree files:
`llvm/include/llvm/Target/GlobalISel/GISynthCombines.td` and
`llvm/include/llvm/CodeGen/GlobalISel/GISynthGeneratedPredicates.inc`.
The hand-written guard primitives are in
`llvm/include/llvm/CodeGen/GlobalISel/GISynthPredicates.h`. Lit tests:
`llvm/test/CodeGen/{AMDGPU,AArch64}/GlobalISel/synth-combines.mir`.

## Semantic model, in short

A rule `S -> T if P` is accepted only if, for every consistent known-bits
assignment satisfying `P` and every input that is poison or matches those
known bits, a non-poison `S` implies that `T` is also non-poison and
`T == S`. This is proved at every width schedule the guard accepts, for
every disjunct of `P` and for the emitted disjunction as a whole.

- Each input has a poison flag. Shift amounts at or above the bit width are
  poison.
- Every supported operation except `G_SELECT` and `G_FREEZE` propagates
  poison.
- `G_FREEZE` has the value of its operand, or a value of its own if the
  operand is poison, and it is never poison. Two `G_FREEZE` instructions
  have two values: a `G_FREEZE` of the replacement is not the `G_FREEZE` of
  the source, and one `G_FREEZE` term must not occur twice in a source. A
  rule can match a `G_FREEZE` but does not create one.
- The precondition atom `def(x)` says that an input is neither undef nor
  poison (`isGuaranteedNotToBeUndefOrPoison` in the guard). The corpus and
  the e-graph export give this fact for a value (`noundef`). `freeze(x) ->
  x` needs it.
- The precondition atom `x == 1` says that the known bits give the
  constant 1. With "all bits known zero" and "all bits known one" the
  grammar has the three literals of the search (0, 1, -1).
- A rule with several outputs is proved for all of them in one query: an
  output of the source that is not poison has the same value in the
  replacement, whatever the other outputs are. A node of the source that
  two outputs have is one value, and so is an instruction that two
  replacements have.
- A floating-point value is its bit pattern (`girs/fp.py`: half, single and
  double). `G_FPEXT` is exact. `G_FPTRUNC`, `G_SITOFP` and `G_UITOFP` round
  to nearest, ties to even. `G_FPTOSI` and `G_FPTOUI` round toward zero and
  are poison for a NaN and for a number outside of the range of the result;
  the `_SAT` forms give the nearest value of the range, and 0 for a NaN.
- LLVM does not specify the payload of a NaN that a conversion makes. The
  proof accepts each NaN of the replacement where the source value is such
  a NaN. Where the source gives the NaN of an input unchanged (through
  `G_SELECT` or `G_FREEZE`), the replacement must give the same bits.
- `T` uses only `S`'s inputs, and each of them at most once, so undef inputs
  are handled soundly. An input that the rule matches as a constant can
  occur more than once: a constant is not undef.
- An operation with undefined behaviour (a division by zero) is modeled as
  such: `T` must not have undefined behaviour if `S` has none.
- `G_SELECT` is poison only if its condition or the selected operand is.
- Source flags (`nsw`, `nuw`, `exact`, `disjoint`, `nneg`) only add poison,
  so a proof for the flag-free source also covers them. Replacements carry no
  flags.

An UNKNOWN solver result is never accepted.
