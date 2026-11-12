#!/usr/bin/env bash
# Configure and build the plugin and its tests into build/plugin, against
# the LLVM build of scripts/build-llvm.sh.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LLVM_BUILD="${LLVM_BUILD_DIR:-$ROOT/build/llvm}"
BUILD="${PLUGIN_BUILD_DIR:-$ROOT/build/plugin}"
EXTRA=()
command -v clang >/dev/null && EXTRA+=(-DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++)
command -v ld.lld >/dev/null && EXTRA+=(-DLLVM_USE_LINKER=lld)
cmake -G Ninja -S "$ROOT" -B "$BUILD" \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_DIR="$LLVM_BUILD/lib/cmake/llvm" \
  "${EXTRA[@]}" "$@"
ninja -C "$BUILD"
