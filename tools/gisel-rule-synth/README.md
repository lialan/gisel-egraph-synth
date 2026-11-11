# gisel-rule-synth

Offline tool that discovers, generalizes, proves and generates GlobalISel
combine rules (GIRuleSynthesizer). Normal compilation only runs the
generated `GICombineRule`s through the existing combiner. No solver, search
engine or e-graph runs inside LLVM.

## Requirements

- An LLVM build that includes the AMDGPU target (for `llc`).
- Python 3 and the z3 Python module (`pip install z3-solver`), but only for
  `synth` and `recheck`. `extract` and `emit` need no solver, so a normal
  LLVM build never needs z3.

## Commands

```sh
S=llvm/utils/gisel-rule-synth/gi-rule-synth.py

# 1. Corpus: gMIR trees + GISelValueTracking known bits, as JSON lines.
#    MIR files run the extractor pass alone; .ll files are compiled for
#    AMDGPU and extracted after the pre-legalizer combiner.
$S extract --llc build/bin/llc -o corpus-dir --mir llvm/utils/gisel-rule-synth/corpus/seed.mir
$S extract --llc build/bin/llc -o corpus-dir --ll-list files.txt

# 2. Discover, generalize, synthesize preconditions (CEGIS), prove (z3).
#    Writes rules.json, proofs/*.smt2 and rules.stats.json (timings, commit).
$S synth corpus-dir -o llvm/utils/gisel-rule-synth/rules.json

# 3. Generate TableGen + C++ (pure function of rules.json).
$S emit                 # writes the in-tree generated files
$S emit --check         # fails if they are stale

# Re-prove every rule in the database from its JSON form.
$S recheck

# Seed corpus only, end to end:
$S all --llc build/bin/llc
```

Using the generated rules:

```sh
llc -global-isel -amdgpu-gisel-synth-combines ...   # off by default
llc ... -debug-only=gisel-synth                     # print each guard that passes
```

## Files

| Path | Contents |
|---|---|
| `girs/corpus.py` | corpus reader, DAG-aware tree conversion |
| `girs/discover.py` | bottom-up enumerative search, fingerprints, concrete SMT proof |
| `girs/precond.py` | precondition grammar (eval / z3 / C++), implication |
| `girs/synth.py` | generalization, width schedules, CEGIS, rule database |
| `girs/smt.py` | z3 backend and gMIR bitvector/poison encoding |
| `girs/emit.py` | `GICombineRule` and guard emission |
| `corpus/seed.mir`, `corpus/seed.jsonl` | seed inputs (not rules) and their extracted corpus |
| `rules.json` | rule database: emitted, verified-but-not-emitted and rejected candidates, with proof records |
| `proofs/` | SMT-LIB2 queries of the proofs, named by SHA-256 |
| `eval/compare.py` | AMDGPU ISA comparison: base, synthesized rules, e-graph |
| `eval/baseline.py` | classifies each rule against the existing combiner |
| `tests/test_synth.py` | unit tests (`python3 -m unittest discover -s llvm/utils/gisel-rule-synth/tests`) |

Generated in-tree files:
`llvm/include/llvm/Target/GlobalISel/GISynthCombines.td` and
`llvm/include/llvm/CodeGen/GlobalISel/GISynthGeneratedPredicates.inc`.
The hand-written guard primitives are in
`llvm/include/llvm/CodeGen/GlobalISel/GISynthPredicates.h`.

## Semantic model, in short

A rule `S -> T if P` is accepted only if, for every consistent known-bits
assignment satisfying `P` and every non-poison input matching those known
bits, a non-poison `S` implies that `T` is also non-poison and `T == S`.
This is proved at every width schedule the guard accepts.

- Shift amounts at or above the bit width are poison.
- Every supported operation propagates poison.
- `T` uses only `S`'s inputs, and each of them at most once, so undef inputs
  are handled soundly.
- Source flags (`nsw`, `nuw`, `exact`, `disjoint`, `nneg`) only add poison,
  so a proof for the flag-free source also covers them. Replacements carry no
  flags.

An UNKNOWN solver result is never accepted.
