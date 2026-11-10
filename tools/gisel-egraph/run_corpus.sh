#!/usr/bin/env bash
# Run the experimental e-graph combiner (rewrite mode, machine verifier on)
# over a corpus of .ll files and compare AMDGPU instruction counts against
# plain GlobalISel. Usage: run_corpus.sh <llvm-build-dir> <out-dir> <file>...
set -uo pipefail
BUILD=$1 OUT=$2; shift 2
mkdir -p "$OUT"
one() {
  f=$1 BUILD=$2 OUT=$3
  id=$(echo "$f" | md5sum | cut -c1-12)
  LLC="$BUILD/bin/llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx1100 -O2 -global-isel -global-isel-abort=2"
  cnt() { grep -cE '^[[:space:]]+[sv]_[a-z0-9_]+' "$1" 2>/dev/null || true; }
  # Files that plain GlobalISel cannot compile (or that fail the verifier
  # without the e-graph pass) are skipped, so CRASH means "fails only with
  # the e-graph combiner".
  if ! $LLC -verify-machineinstrs "$f" -o "$OUT/$id.base.s" 2>/dev/null; then
    echo "$f SKIP"; return
  fi
  if ! $LLC -amdgpu-gisel-egraph -gisel-egraph-mode=rewrite -verify-machineinstrs \
      -stats "$f" -o "$OUT/$id.eg.s" 2>"$OUT/$id.eg.err"; then
    echo "$f CRASH"; return
  fi
  applied=$(awk '/Number of regions rewritten/ {print $1}' "$OUT/$id.eg.err")
  prof=$(awk '/Number of regions with a cheaper candidate/ {print $1}' "$OUT/$id.eg.err")
  regions=$(awk '/Number of e-graph regions examined/ {print $1}' "$OUT/$id.eg.err")
  echo "$f OK $(cnt "$OUT/$id.base.s") $(cnt "$OUT/$id.eg.s") ${regions:-0} ${prof:-0} ${applied:-0}"
}
export -f one
printf '%s\n' "$@" | xargs -P "$(nproc)" -I{} bash -c 'one "$@"' _ {} "$BUILD" "$OUT"
