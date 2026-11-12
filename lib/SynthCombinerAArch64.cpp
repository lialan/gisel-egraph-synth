//===- SynthCombinerAArch64.cpp - Synthesized rules for AArch64 -----------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// The combiner pass of the synthesized rules that the AArch64 profile
// selects (gi_synth_combines_aarch64). lib/PassRegistration.cpp adds it after
// the AArch64 pre-legalizer combiner when -aarch64-gisel-synth-combines is set.
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/SynthCombiners.h"

#define DEBUG_TYPE "gisynth-aarch64-combiner"
#define SYNTH_GEN_INC "GISynthAArch64Combiner.inc"
#define SYNTH_IMPL GISynthAArch64CombinerImpl
#define SYNTH_RULE_CONFIG GISynthAArch64CombinerImplRuleConfig
#define SYNTH_PASS GISynthAArch64CombinerLegacy
#define SYNTH_PASS_DESC "GISynthAArch64Combiner"

#include "SynthCombiner.inc"

INITIALIZE_PASS_BEGIN(GISynthAArch64CombinerLegacy, DEBUG_TYPE,
                      "Combine with the synthesized rules of AArch64", false,
                      false)
INITIALIZE_PASS_DEPENDENCY(TargetPassConfig)
INITIALIZE_PASS_DEPENDENCY(GISelValueTrackingAnalysisLegacy)
INITIALIZE_PASS_DEPENDENCY(MachineDominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(GISelCSEAnalysisWrapperPass)
INITIALIZE_PASS_END(GISynthAArch64CombinerLegacy, DEBUG_TYPE,
                    "Combine with the synthesized rules of AArch64", false,
                    false)

const void *llvm::getGISynthAArch64CombinerID() {
  return &GISynthAArch64CombinerLegacy::ID;
}
