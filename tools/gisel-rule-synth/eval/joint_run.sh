#!/usr/bin/env bash
# The complete joint region run: training corpus -> rules -> selection on a
# validation corpus -> frozen rules -> held-out evaluation and the full
# pipeline validation. Each step writes into $OUT; a step whose output
# exists is skipped. See docs/Joint-Regions.md.
#
#   LLVM_SRC=.../third_party/llvm-project LLVM_BUILD=.../build/llvm \
#   PY=python3 OUT=build/eval tools/gisel-rule-synth/eval/joint_run.sh
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
T="$ROOT/tools/gisel-rule-synth"
PY="${PY:-python3}"
OUT="${OUT:-$ROOT/build/eval}"
LLVM_SRC="${LLVM_SRC:-$ROOT/third_party/llvm-project}"
LLVM_BUILD="${LLVM_BUILD:-$ROOT/build/llvm}"
JOBS="${JOBS:-24}"
LLC="$ROOT/build/plugin/bin/llc"
M="$T/manifests"
mkdir -p "$OUT"
build() { ninja -C "$ROOT/build/plugin" bin/llc >/dev/null; }

# 1. Region DAGs of the training corpus and of the two examples.
[ -d "$OUT/train-regions" ] || $PY "$T/gi-rule-synth.py" joint-extract \
  --llc "$LLC" -o "$OUT/train-regions" --ll-list "$M/amdgpu-discovery.txt" \
  --root "$LLVM_SRC" -j "$JOBS"
EX="$OUT/examples"
if [ ! -d "$EX/regions" ]; then
  mkdir -p "$EX"
  for f in "$T"/eval/joint-examples/*.ll; do
    "$LLVM_BUILD/bin/opt" -passes='default<O2>' -S \
      -mtriple=amdgpu11.00-amd-amdhsa -mcpu=gfx1100 "$f" \
      -o "$EX/$(basename "$f" .ll)-O2.ll"
  done
  $PY "$T/gi-rule-synth.py" joint-extract --llc "$LLC" -o "$EX/regions" \
    --ll "$EX"/*-O2.ll
fi

# 2. Search, proofs, plans.
[ -f "$OUT/train-search/rules.json" ] || $PY "$T/gi-rule-synth.py" \
  joint-search --regions "$OUT/train-regions" "$EX/regions" \
  --out "$OUT/train-search" --jobs "$JOBS" --time-s 30

# 3. All candidates in one llc, measured on the validation corpus.
if [ ! -f "$OUT/validation/summary.json" ]; then
  $PY "$T/gi-rule-synth.py" joint-emit --rules "$OUT/train-search/rules.json"
  build
  $PY "$T/eval/joint_eval.py" --llc "$LLC" --manifest "$M/amdgpu-validation.txt" \
    --root "$LLVM_SRC" --exclude "$M/amdgpu-discovery.txt" \
    --out "$OUT/validation" -j "$JOBS"
fi

# 4. Selection, then the frozen rules.
EXAMPLES=$($PY - "$OUT/train-search/rules.json" <<'EOF'
import json, sys
rules = json.load(open(sys.argv[1]))['rules']
print(','.join(r['id'] for r in rules
               if any('joint-examples' in e[0] or '-O2.ll' in e[0]
                      for e in r['provenance']['examples'])))
EOF
)
$PY "$T/eval/joint_select.py" --rules "$OUT/train-search/rules.json" \
  --validation "$OUT/validation" --keep "$EXAMPLES" --out "$OUT/selection.json"
SEL=$($PY -c "import json;print(','.join(json.load(open('$OUT/selection.json'))['selected']))")
$PY "$T/gi-rule-synth.py" joint-emit --rules "$OUT/train-search/rules.json" --ids "$SEL"
build

# 5. The full pipeline of the difference of squares, and held-out files.
$PY "$T/eval/joint_validate.py" --llvm-build "$LLVM_BUILD" --llc "$LLC" \
  --out "$OUT/pipeline"
$PY "$T/eval/joint_eval.py" --llc "$LLC" --manifest "$M/amdgpu-heldout-codegen.txt" \
  --root "$LLVM_SRC" --exclude "$M/amdgpu-discovery.txt" \
  --exclude "$M/amdgpu-validation.txt" --out "$OUT/heldout" -j "$JOBS"
$PY "$T/gi-rule-synth.py" joint-recheck --rules "$OUT/train-search/rules.json" \
  > "$OUT/recheck.json"
