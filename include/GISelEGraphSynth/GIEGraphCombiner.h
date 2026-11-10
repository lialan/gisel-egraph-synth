//===- llvm/CodeGen/GlobalISel/GIEGraphCombiner.h - E-graph combiner -*- C++
//-*-//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// Experimental equality-saturation based combiner for scalar integer gMIR.
///
/// The pass collects single-block regions of pure scalar integer operations
/// (G_ADD, G_SUB, G_MUL, G_AND, G_OR, G_XOR, G_SHL, G_LSHR, G_ASHR with
/// G_CONSTANT operands), translates each into an e-graph, runs bounded
/// equality saturation with a generic rule library, extracts the cheapest
/// equivalent (or refining) expression and, in rewrite mode, re-emits the
/// region if it is strictly cheaper. In shadow mode (the default) the MIR is
/// never modified; opportunities are only counted and optionally reported.
///
/// The pass is not part of any default pipeline.
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_GLOBALISEL_GIEGRAPHCOMBINER_H
#define LLVM_CODEGEN_GLOBALISEL_GIEGRAPHCOMBINER_H

#include "llvm/CodeGen/MachineFunctionPass.h"

namespace llvm {

class GIEGraphCombiner : public MachineFunctionPass {
public:
  static char ID;

  GIEGraphCombiner();

  StringRef getPassName() const override { return "GIEGraphCombiner"; }

  MachineFunctionProperties getRequiredProperties() const override {
    return MachineFunctionProperties().set(
        MachineFunctionProperties::Property::IsSSA);
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override;

  bool runOnMachineFunction(MachineFunction &MF) override;
};

} // end namespace llvm

#endif // LLVM_CODEGEN_GLOBALISEL_GIEGRAPHCOMBINER_H
