# gisel-egraph-synth

This project finds new GlobalISel combine rules automatically, proves them
correct, and compiles them into LLVM as ordinary `GICombineRule`s.

It has two parts:

* **GIRuleSynthesizer** (`tools/gisel-rule-synth`). An offline Python tool.
  It reads real compiler output, searches for shorter equivalent code, proves
  each rewrite with the Z3 SMT solver, and measures which rules make the
  final machine code smaller. The selected rules become TableGen records.
* **The e-graph combiner** (`lib/GIEGraph*.cpp`). An experimental GlobalISel
  pass that optimizes a whole expression region at compile time with an
  e-graph. It is a reference for what the rules can reach, and a second
  source of rule candidates.

The project builds against an unpatched LLVM, which is a git submodule. The
normal compilation never runs a solver or a search: it runs only the
generated match, guard and apply code.

```
          offline (Python, Z3)                    compile time (C++)
  +----------------------------------+    +--------------------------------+
  |                                  |    |                                |
  |  .ll corpus --> llc --> records  |    |  GlobalISel pipeline           |
  |                          |       |    |    IRTranslator                |
  |                          v       |    |    pre-legalizer combiner      |
  |            search + SMT proof    |    |    synthesized rules  <--------+---+
  |                          |       |    |    e-graph combiner (opt-in)   |   |
  |                          v       |    |    Legalizer                   |   |
  |            measure + select      |    |    post-legalizer combiner     |   |
  |                          |       |    |    e-graph combiner (opt-in)   |   |
  |                          v       |    |    RegBankSelect, Select       |   |
  |            td/GISynthCombines.td-+----+--> generated C++ matcher ------+---+
  |                                  |    |                                |
  +----------------------------------+    +--------------------------------+
```

## How the synthesizer works

The `mine` command runs the complete loop. Each stage writes its result into
a run directory, so an interrupted run continues from the last stage that
completed.

```
  manifests (.ll files)
        |
        v
  +-------------+   compile each file with llc; the corpus pass writes
  |  extract    |   each expression tree that remains after the existing
  +-------------+   combines, with types, known bits and facts
        |
        v
  +-------------+   for each distinct tree: enumerate replacement programs
  |  discover   |   from the operator registry, filter them on sample
  +-------------+   values, then prove the survivors
        |
        v
  +-------------+   find the precondition (known bits, constant facts),
  | generalize  |   the bit widths, and the constants that the rule must
  +-------------+   compute; prove each case again
        |
        v
  +-------------+   generate TableGen and C++ guards; rebuild llc with
  |   build     |   all candidate rules (only this project recompiles)
  +-------------+
        |
        v
  +-------------+   compile the corpus with and without the candidates;
  |  measure    |   count the instructions of the final machine code
  +-------------+
        |
        v
  +-------------+   keep a rule only if it has a measured gain; reject
  |   select    |   rules that loop, crash, change a fallback, or make
  +-------------+   one file worse
        |
        v
  +-------------+   check the final set again on each file, then
  | verify,     |   evaluate it on held-out files that the search
  | heldout     |   never saw
  +-------------+
        |
        v
  report.json, targets/<Target>.json, td/GISynthCombines.td
```

### What one rule looks like

The search sees a tree of generic instructions. A rule replaces the tree
with a cheaper tree that gives the same value for each input:

```
  source (from the corpus)                 replacement (found by search)

  %c = G_ICMP intpred(uge), %x, %y
  %s = G_SUB  %x, %y                 -->   %s, %b = G_USUBO %x, %y
  %r = G_SELECT %c, %p, %q                 %r     = G_SELECT %b, %q, %p
```

The rule above has two outputs (`%s` and `%r`). The search also finds rules
with one output, rules with a precondition such as "bit 0 of `%x` is known
zero", and rules with a constant that the compiler computes when it applies
the rule.

### How a rule is proved

A rule is correct if the replacement **refines** the source: for each input,
each value that the replacement can give is a value that the source can
give. The proof uses the same semantics as LLVM:

```
   for all inputs x (each bit pattern, poison or not):
       precondition(x)  ==>  value(replacement, x)  is in  values(source, x)

   unsat  --> the rule is proved        sat     --> counterexample, rejected
                                        unknown --> retried with a longer limit
```

The model covers these cases:

| Area | What the proof models |
|---|---|
| Integers | Each integer operator, flags (`nuw`, `nsw`, `exact`), overflow and carry results |
| Undefined values | Poison per input, `G_FREEZE`, `G_IMPLICIT_DEF`, bits that `G_ANYEXT` leaves unspecified |
| Floating point | Bit-exact IEEE 754: conversions, min/max (each NaN and signed-zero rule), rounding, arithmetic, NaN payloads |
| Strict float | The ten `G_STRICT_*` operators in each rounding mode, with the exception flags |
| Other kinds | Pointers as integers, fixed vectors (lane by lane), `G_PHI`, a load after a store to the same address, some AMDGPU intrinsics |

Each operator model is compared with LLVM's own constant folding
(`gi-rule-synth.py check-ops`), so a model cannot drift from the compiler.

### Knowledge that persists

The repository holds the knowledge of earlier runs. A new run searches only
for what is not yet known:

```
   K  rules.json + proofs/      all proved rules, also rules that no
                                target selects
   B  targets/<Target>.json     the rules that a target uses now, pinned

   new run:   llc with B  -->  corpus  -->  search  -->  Delta = new rules
                                                           |
              measure Delta on top of B, never remove B <--+
                                                           |
              mine --export:  K := K + Delta,  B := B + selected Delta
```

A run that finds nothing new stops after discovery and reports
`no_new_rules`. The report never claims that a search was exhaustive.

## How the e-graph combiner works

The e-graph combiner takes a region of generic instructions, puts it into an
e-graph, and applies rewrite rules until no rule adds a new form. Then it
extracts the cheapest form that is legal for the target:

```
  MIR region                 e-graph (one class = one value)        extract

  %2 = G_XOR %0, %1          class A: { %0, G_XOR(B, %1) }
  %3 = G_XOR %2, %1    -->   class B: { G_XOR(%0, %1) }       -->   %5 = G_ADD %0, %0
  %4 = G_ADD %3, %0          class C: { G_ADD(A, %0) }
                             rules: xor-self, xor-zero              cost 3 -> 1
```

The class of `%3` merges with the class of `%0`, because `(x ^ y) ^ y` is
`x`. The cheapest member of the root class is then `G_ADD %0, %0`. This is
the real output of `-gisel-egraph-report` for this region.

* The rewrite rules come from a table of operator properties (identity,
  commutativity, absorbing values, inverses), not from hand-written cases.
* The cost model asks the target's legalizer which operations are legal.
* Instructions and constants that do not change stay in place.
* By default the pass only analyzes and reports (`-gisel-egraph-mode=shadow`).
  `-gisel-egraph-mode=rewrite` changes the MIR.
* `-gisel-egraph-report` prints each region, its cost and the rules used.
* `-gisel-egraph-export=FILE` writes each optimized region as a candidate
  for the synthesizer.

`docs/GIEGraphCombiner-Design.md` has the full design.

## Layout

| Path | Content |
|---|---|
| `third_party/llvm-project` | Upstream LLVM (submodule), not changed |
| `include/GISelEGraphSynth`, `lib` | E-graph combiner, corpus extractor, combiners of the synthesized rules, pass registration |
| `td/GISynthCombines.td` | Rule records that the tool generates |
| `test` | Lit tests (MIR) |
| `unittests` | Unit tests of the engine and of the rule guards |
| `tools/gisel-rule-synth` | The rule synthesizer (Python), its rule catalog, proofs and target profiles |
| `tools/gisel-egraph` | SMT verifier of the e-graph rules, evaluation scripts |
| `docs` | Design of the e-graph combiner |

## Build

```sh
git clone --recurse-submodules <url> gisel-egraph-synth
cd gisel-egraph-synth
scripts/build-llvm.sh   # stock LLVM into build/llvm (one time)
scripts/build.sh        # this project into build/plugin
```

`scripts/build.sh` builds `build/plugin/bin/llc`. This is the stock `llc`
driver of the submodule, with the passes of this project linked in. The
upstream `llc` of this LLVM version has no `-load` option, and it loads a
`-load-pass-plugin` only after it parses the command line, so it cannot
read the options of a plugin. The project therefore builds its own driver
from the upstream `llc` sources. The rebuild after a change of the rules
compiles only the files of this project.

```
  third_party/llvm-project ---> build/llvm         (stock LLVM, one time)
                                     |
  lib/ + td/ + llc.cpp ----------> build/plugin/bin/llc   (fast rebuild)
```

## Use

All passes are off by default.

| Option | Effect |
|---|---|
| `-amdgpu-gisel-synth-combines` | Synthesized rules, in their own combiner after the AMDGPU pre-legalizer combiner |
| `-aarch64-gisel-synth-combines` | The same for AArch64 |
| `-amdgpu-gisel-egraph` | E-graph combiner after the AMDGPU pre-legalizer and post-legalizer combiners. Add `-gisel-egraph-mode=rewrite`, or it only reports |
| `-amdgpu-gisel-synth-corpus` | Corpus extractor of the synthesizer, last after the AMDGPU pre-legalizer combiner |

```sh
build/plugin/bin/llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx1100 -O2 \
  -global-isel -amdgpu-gisel-synth-combines \
  -amdgpu-gisel-egraph -gisel-egraph-mode=rewrite in.ll
```

With `-run-pass`, the pass names are `gisel-egraph-combiner`,
`gisynth-amdgpu-combiner`, `gisynth-aarch64-combiner` and
`gisel-synth-corpus`.

A complete synthesizer run:

```sh
python3 tools/gisel-rule-synth/gi-rule-synth.py mine \
  --config tools/gisel-rule-synth/configs/m4-auto.json \
  --run-dir build/runs/incremental
```

## Tests

```sh
ninja -C build/plugin check-gisel-egraph-synth     # lit and unit tests
cd tools/gisel-rule-synth && python3 -m unittest discover -s tests
```

The Python tests need `z3-solver`, `numpy` and the build above.

## More detail

`tools/gisel-rule-synth/README.md` describes each command, the
configuration of a run, the search options and the knowledge catalog.
Corpus manifests list files relative to `third_party/llvm-project`.
