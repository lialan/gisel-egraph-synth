//===- SynthCombiners.h - Combiners of the synthesized rules ----*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
/// \file
/// The combiner passes that run the synthesized rules of a target
/// (lib/SynthCombiners.td). Each runs the generic combines and the rule group
/// of its target, after the pre-legalizer combiner of that target.
//
//===----------------------------------------------------------------------===//

#ifndef GISELEGRAPHSYNTH_SYNTHCOMBINERS_H
#define GISELEGRAPHSYNTH_SYNTHCOMBINERS_H

namespace llvm {

class PassRegistry;

void initializeGISynthAMDGPUCombinerLegacyPass(PassRegistry &);
void initializeGISynthAArch64CombinerLegacyPass(PassRegistry &);
void initializeGISynthJointCombinerLegacyPass(PassRegistry &);

/// The pass IDs, for TargetPassConfig::insertPass.
const void *getGISynthAMDGPUCombinerID();
const void *getGISynthAArch64CombinerID();
const void *getGISynthJointCombinerID();

} // end namespace llvm

#endif // GISELEGRAPHSYNTH_SYNTHCOMBINERS_H
