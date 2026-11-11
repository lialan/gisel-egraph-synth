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
  only for `synth` and `recheck`. `extract`, `select`, `report` and `emit`
  need no solver, so a normal LLVM build never needs z3.

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

## Commands

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

1. **Discovery** (`discover.py`). Enumerative search for a cheaper
   expression that agrees with the source on samples, then an SMT proof under
   the instance's concrete known bits. The enumeration is done once per
   *signature* (width class of every input), in a term bank pruned by
   observational equivalence, and reused by every instance with that
   signature whatever its shape or bit widths. Instances are visited by
   corpus frequency times instructions at stake. Refuting SMT models become
   samples for the rest of the run.
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

A replacement can have a *computed constant*: a constant that the source
does not have. The importer looks for a recipe, an expression over the
constants of the source (`G_ADD`, `G_SUB`, `G_MUL`, `G_AND`, `G_OR`, `G_XOR`
and the shifts) or the mask of the low bits of a narrower type of the source
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
  `worse`, `not_fired`);
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
| `girs/discover.py` | term banks, fingerprints, concrete SMT proof |
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
| `tests/test_synth.py`, `tests/test_unified.py`, `tests/test_fp.py` | unit tests (`python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests`) |

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
  poison (`isGuaranteedNotToBeUndefOrPoison` in the guard). The e-graph
  export gives this fact for a value; the known-bits corpus does not, so
  only an e-graph candidate can get this atom. `freeze(x) -> x` needs it.
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
