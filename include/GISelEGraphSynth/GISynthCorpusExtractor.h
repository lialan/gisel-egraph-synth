//===- llvm/CodeGen/GlobalISel/GISynthCorpusExtractor.h ---------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// Corpus extractor for the offline GlobalISel rule synthesizer
/// (llvm/utils/gisel-rule-synth).
///
/// The pass never modifies MIR. For every pure scalar integer instruction it
/// writes small single-block expression trees rooted at that instruction to a
/// JSON-lines file, together with the GISelValueTracking known bits of each
/// tree input. The offline synthesizer reads that file to discover, generalize
/// and verify combine rules.
///
/// The pass is not part of any default pipeline.
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_GLOBALISEL_GISYNTHCORPUSEXTRACTOR_H
#define LLVM_CODEGEN_GLOBALISEL_GISYNTHCORPUSEXTRACTOR_H

#include "llvm/CodeGen/MachineFunctionPass.h"

namespace llvm {

class GISynthCorpusExtractor : public MachineFunctionPass {
public:
  static char ID;

  GISynthCorpusExtractor();

  StringRef getPassName() const override { return "GISynthCorpusExtractor"; }

  MachineFunctionProperties getRequiredProperties() const override {
    return MachineFunctionProperties().set(
        MachineFunctionProperties::Property::IsSSA);
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override;

  bool runOnMachineFunction(MachineFunction &MF) override;
};

} // end namespace llvm

#endif // LLVM_CODEGEN_GLOBALISEL_GISYNTHCORPUSEXTRACTOR_H
