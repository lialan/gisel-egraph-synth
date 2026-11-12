//===- GIEGraphLinear.cpp - Linear forms modulo 2^W in the e-graph --------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// The linear view of an integer class (see applyLinearViews in GIEGraph.h).
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GIEGraph.h"

using namespace llvm;
using namespace llvm::egraph;

unsigned llvm::egraph::applyLinearViews(EGraph &G,
                                        const SaturationLimits &Limits,
                                        ViewStats &Stats) {
  return 0;
}
