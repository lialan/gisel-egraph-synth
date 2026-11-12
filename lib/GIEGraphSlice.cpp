//===- GIEGraphSlice.cpp - Bit slices in the e-graph ----------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// The bit-slice view of an integer class (see applySliceViews in
/// GIEGraph.h).
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GIEGraph.h"

using namespace llvm;
using namespace llvm::egraph;

unsigned llvm::egraph::applySliceViews(EGraph &G,
                                       const SaturationLimits &Limits,
                                       ViewStats &Stats) {
  return 0;
}
