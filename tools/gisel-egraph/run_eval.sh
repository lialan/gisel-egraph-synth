#!/usr/bin/env bash
# Compare AMDGPU code for eval/kernels.ll with and without the experimental
# GlobalISel e-graph combiner. Usage: run_eval.sh <llvm-build-dir> [mcpu]
set -euo pipefail
BUILD=${1:?usage: run_eval.sh <llvm-build-dir> [mcpu]}
MCPU=${2:-gfx1100}
HERE=$(cd "$(dirname "$0")" && pwd)
IN=$HERE/eval/kernels.ll
LLC="$BUILD/bin/llc -mtriple=amdgcn-amd-amdhsa -mcpu=$MCPU -O2"
OPT="$BUILD/bin/opt -mtriple=amdgcn-amd-amdhsa -mcpu=$MCPU -O3"
EG="-amdgpu-gisel-egraph -gisel-egraph-mode=rewrite"

# Prints "<function> <instructions>" for an asm file. All instructions are
# counted, including s_waitcnt, s_delay_alu and the final s_setpc_b64/s_endpgm.
count() {
  awk '
    /^[A-Za-z_][A-Za-z0-9_.]*:/ && !/^\./ { fn = substr($1, 1, length($1) - 1); n = 0; next }
    /^\.Lfunc_end/ { if (fn != "") cnt[fn] = n; fn = ""; next }
    fn != "" && /^[ \t]+[a-z_][a-z0-9_]*/ && $1 !~ /^\./ { n++ }
    END { for (f in cnt) print f, cnt[f] }' "$1" | sort
}

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
$LLC -global-isel "$IN" -o "$TMP/gisel.s"
$LLC -global-isel $EG "$IN" -o "$TMP/egraph.s"
$LLC "$IN" -o "$TMP/sdag.s"
$OPT "$IN" -S -o "$TMP/o3.ll"
$LLC -global-isel "$TMP/o3.ll" -o "$TMP/o3-gisel.s"
$LLC -global-isel $EG "$TMP/o3.ll" -o "$TMP/o3-egraph.s"

printf "%-26s %6s %6s %6s | %8s %8s\n" function gisel egraph sdag O3+gisel O3+egraph
join <(count "$TMP/gisel.s") <(count "$TMP/egraph.s") |
  join - <(count "$TMP/sdag.s") |
  join - <(count "$TMP/o3-gisel.s") |
  join - <(count "$TMP/o3-egraph.s") |
  awk '{ printf "%-26s %6d %6d %6d | %8d %8d\n", $1, $2, $3, $4, $5, $6;
         g += $2; e += $3; s += $4; og += $5; oe += $6 }
       END { printf "%-26s %6d %6d %6d | %8d %8d\n", "TOTAL", g, e, s, og, oe }'
