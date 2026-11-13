//===- GISelEGraphSynth/GISynthRegionExtractor.h ----------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// The pass that writes the region DAGs of the joint region search
/// (-gisel-synth-joint-regions, -gisel-synth-region-out).
//===----------------------------------------------------------------------===//

#ifndef GISELEGRAPHSYNTH_GISYNTHREGIONEXTRACTOR_H
#define GISELEGRAPHSYNTH_GISYNTHREGIONEXTRACTOR_H

#include "llvm/CodeGen/MachineFunctionPass.h"

namespace llvm {

class PassRegistry;
void initializeGISynthRegionExtractorPass(PassRegistry &);

class GISynthRegionExtractor : public MachineFunctionPass {
public:
  static char ID;

  GISynthRegionExtractor();

  StringRef getPassName() const override { return "GISynthRegionExtractor"; }

  MachineFunctionProperties getRequiredProperties() const override {
    return MachineFunctionProperties().set(
        MachineFunctionProperties::Property::IsSSA);
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override;

  bool runOnMachineFunction(MachineFunction &MF) override;
};

} // end namespace llvm

#endif // GISELEGRAPHSYNTH_GISYNTHREGIONEXTRACTOR_H
