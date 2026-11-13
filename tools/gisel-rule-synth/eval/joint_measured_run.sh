#!/usr/bin/env bash
# The joint region run with several implementations per window and a
# measured selection over the frozen baseline (docs/Joint-Regions.md):
#
#   1. region DAGs of the training corpus and of the two examples
#   2. joint-search with a cost slack and several proved shapes per window,
#      incremental in $OUT/cache (a second invocation continues it)
#   3. one llc with the baseline rules (joint/rules.json) and every
#      candidate; eval/joint_measure.py on the validation corpus
#   4. the selected set (baseline first) emitted, built and measured again
#      on the validation corpus in its final order
#   5. the frozen set, once, on the held-out corpus; the proofs again
#
# Each step whose output exists is skipped. The held-out corpus is not read
# before step 5.
#
#   LLVM_SRC=.../third_party/llvm-project LLVM_BUILD=.../build/llvm \
#   PY=python3 OUT=build/eval-measured JOBS=96 \
#   tools/gisel-rule-synth/eval/joint_measured_run.sh
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
T="$ROOT/tools/gisel-rule-synth"
PY="${PY:-python3}"
OUT="${OUT:-$ROOT/build/eval-measured}"
LLVM_SRC="${LLVM_SRC:-$ROOT/third_party/llvm-project}"
LLVM_BUILD="${LLVM_BUILD:-$ROOT/build/llvm}"
JOBS="${JOBS:-24}"
SLACK="${SLACK:-0}"
VARIANTS="${VARIANTS:-6}"
LLC="$ROOT/build/plugin/bin/llc"
M="$T/manifests"
BASE="$T/joint/rules.json"
mkdir -p "$OUT"
build() { ninja -C "$ROOT/build/plugin" bin/llc >/dev/null; }

# 1. Region DAGs.
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

# 2. The search (incremental: the cache keeps the decided work).
[ -f "$OUT/search/rules.json" ] || $PY "$T/gi-rule-synth.py" joint-search \
  --regions "$OUT/train-regions" "$EX/regions" --out "$OUT/search" \
  --cache "$OUT/cache" --jobs "$JOBS" --time-s 30 \
  --cost-slack "$SLACK" --semantic-variants "$VARIANTS"

# 3. Baseline + every candidate in one llc, measured on validation.
if [ ! -f "$OUT/measure/selection.json" ]; then
  $PY - "$BASE" "$OUT/search/rules.json" "$OUT/all.json" <<'EOF'
import json, sys
base = json.load(open(sys.argv[1]))['rules']
cand = json.load(open(sys.argv[2]))['rules']
ids = {r['id'] for r in base}
json.dump({'schema': 'gisel-joint-region/1',
           'rules': base + [r for r in cand if r['id'] not in ids]},
          open(sys.argv[3], 'w'))
EOF
  $PY "$T/gi-rule-synth.py" joint-emit --rules "$OUT/all.json"
  build
  cp "$ROOT/td/GISynthJointCombines.td" "$OUT/all.td"
  cp "$LLC" "$OUT/llc-all"
  $PY "$T/eval/joint_measure.py" --llc "$OUT/llc-all" --td "$OUT/all.td" \
    --rules "$OUT/search/rules.json" --baseline "$BASE" \
    --manifest "$M/amdgpu-validation.txt" --root "$LLVM_SRC" \
    --exclude "$M/amdgpu-discovery.txt" --out "$OUT/measure" -j "$JOBS"
fi

# 4. The selected set, in its order, built and measured again.
SEL=$($PY -c "import json;print(','.join(json.load(open('$OUT/measure/selection.json'))['selected']))")
NEW=$($PY -c "import json;print(','.join(json.load(open('$OUT/measure/selection.json'))['new_selected']))")
$PY "$T/gi-rule-synth.py" joint-emit --rules "$OUT/all.json" --ids "$SEL"
build
$PY "$T/eval/joint_measure.py" --llc "$LLC" --baseline "$BASE" \
  --evaluate "$NEW" --manifest "$M/amdgpu-validation.txt" --root "$LLVM_SRC" \
  --exclude "$M/amdgpu-discovery.txt" --out "$OUT/validation-final" -j "$JOBS"

# 5. Held-out, once, and the proofs of the selected rules again.
$PY "$T/eval/joint_measure.py" --llc "$LLC" --baseline "$BASE" \
  --evaluate "$NEW" --manifest "$M/amdgpu-heldout-codegen.txt" \
  --root "$LLVM_SRC" --exclude "$M/amdgpu-discovery.txt" \
  --exclude "$M/amdgpu-validation.txt" --out "$OUT/heldout" -j "$JOBS"
# The proofs of a rule file are next to it: the selected rules go next to
# the proofs of the search, with the proofs of the baseline.
cp -n "$T"/joint/proofs/*.smt2 "$OUT/search/proofs/"
$PY - "$OUT/all.json" "$SEL" "$OUT/search/selected.json" <<'EOF'
import json, sys
rules = {r['id']: r for r in json.load(open(sys.argv[1]))['rules']}
json.dump({'schema': 'gisel-joint-region/1',
           'rules': [rules[i] for i in sys.argv[2].split(',')]},
          open(sys.argv[3], 'w'), indent=1)
EOF
$PY "$T/gi-rule-synth.py" joint-recheck --rules "$OUT/search/selected.json" \
  > "$OUT/recheck.json"
