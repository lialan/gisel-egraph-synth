# gisel-egraph-synth

A GlobalISel e-graph combiner and GIRuleSynthesizer, an offline tool that
finds, proves and emits GlobalISel combine rules. The project builds against
an unpatched LLVM, which is a git submodule.

## Layout

| Path | Content |
|---|---|
| `third_party/llvm-project` | Upstream LLVM (submodule), not changed |
| `include/GISelEGraphSynth`, `lib` | E-graph combiner, corpus extractor, combiners of the synthesized rules, pass registration |
| `td/GISynthCombines.td` | Rule records that the tool generates |
| `test` | Lit tests (MIR) |
| `unittests` | Unit tests of the engine and of the rule guards |
| `tools/gisel-rule-synth` | The rule synthesizer (Python) |
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

## Use

All passes are off by default.

| Option | Effect |
|---|---|
| `-amdgpu-gisel-egraph` | E-graph combiner after the AMDGPU pre-legalizer and post-legalizer combiners |
| `-amdgpu-gisel-synth-combines` | Synthesized rules, in their own combiner after the AMDGPU pre-legalizer combiner |
| `-aarch64-gisel-synth-combines` | The same for AArch64 |
| `-amdgpu-gisel-synth-corpus` | Corpus extractor of the synthesizer after the AMDGPU pre-legalizer combiner |

```sh
build/plugin/bin/llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx1100 -O2 \
  -global-isel -amdgpu-gisel-synth-combines -amdgpu-gisel-egraph in.ll
```

With `-run-pass`, the pass names are `gisel-egraph-combiner`,
`gisynth-amdgpu-combiner`, `gisynth-aarch64-combiner` and
`gisel-synth-corpus`.

## Tests

```sh
ninja -C build/plugin check-gisel-egraph-synth     # lit and unit tests
cd tools/gisel-rule-synth && python3 -m unittest discover -s tests
```

The Python tests need `z3-solver`, `numpy` and the build above.

## The synthesizer

See `tools/gisel-rule-synth/README.md`. Corpus manifests list files relative
to `third_party/llvm-project`. The `mine` driver rebuilds `build/plugin/bin/llc`
with the candidate rules and keeps a copy for each run.
