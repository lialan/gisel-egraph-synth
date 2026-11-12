#!/usr/bin/env bash
# Configure and build the stock LLVM of the submodule into build/llvm.
# Only the tools and libraries that the plugin, its tests and the rule
# synthesizer use are built.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
BUILD="${LLVM_BUILD_DIR:-$ROOT/build/llvm}"
EXTRA=()
command -v clang >/dev/null && EXTRA+=(-DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++)
command -v ld.lld >/dev/null && EXTRA+=(-DLLVM_USE_LINKER=lld)
command -v ccache >/dev/null && EXTRA+=(-DLLVM_CCACHE_BUILD=ON)
cmake -G Ninja -S "$ROOT/third_party/llvm-project/llvm" -B "$BUILD" \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_ENABLE_ASSERTIONS=ON \
  -DLLVM_TARGETS_TO_BUILD="AMDGPU;AArch64" \
  -DLLVM_PARALLEL_LINK_JOBS=4 \
  "${EXTRA[@]}" "$@"
ninja -C "$BUILD" llc opt llvm-tblgen FileCheck not count llvm-config \
  llvm_gtest llvm_gtest_main
