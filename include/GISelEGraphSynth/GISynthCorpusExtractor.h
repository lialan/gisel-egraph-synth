//===- GISelEGraphSynth/GISynthCorpusExtractor.h ---------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// Corpus extractor for the offline GlobalISel rule synthesizer
/// (tools/gisel-rule-synth).
///
/// The pass never modifies MIR. For every instruction that is a scalar
/// operator of the operator table of the e-graph combiner (GIEGraph.h,
/// OpProperties) it writes small expression trees rooted at each
/// result of that instruction to a JSON-lines file, together with the
/// GISelValueTracking known bits of each tree input. The offline synthesizer
/// reads that file to discover, generalize and verify combine rules.
/// Pure scalar integer trees can span a bounded straight-line chain of
/// blocks; other operations retain their block-local extraction contract.
/// The extractor has no opcode list of its own, so an operator that is added to
/// the table is extracted too.
///
/// The pass is not part of any default pipeline. lib/PassRegistration.cpp
/// adds it to the pipeline of a target when an llc option asks for it.
//===----------------------------------------------------------------------===//

#ifndef GISELEGRAPHSYNTH_GISYNTHCORPUSEXTRACTOR_H
#define GISELEGRAPHSYNTH_GISYNTHCORPUSEXTRACTOR_H

#include "llvm/CodeGen/MachineFunctionPass.h"

namespace llvm {

class PassRegistry;
void initializeGISynthCorpusExtractorPass(PassRegistry &);

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

#endif // GISELEGRAPHSYNTH_GISYNTHCORPUSEXTRACTOR_H
