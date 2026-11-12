//===- SynthCombinerAMDGPU.cpp - Synthesized rules for AMDGPU -------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// The combiner pass of the synthesized rules that the AMDGPU profile
// selects (gi_synth_combines_amdgpu). lib/PassRegistration.cpp adds it after
// the AMDGPU pre-legalizer combiner when -amdgpu-gisel-synth-combines is set.
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/SynthCombiners.h"

#define DEBUG_TYPE "gisynth-amdgpu-combiner"
#define SYNTH_GEN_INC "GISynthAMDGPUCombiner.inc"
#define SYNTH_IMPL GISynthAMDGPUCombinerImpl
#define SYNTH_RULE_CONFIG GISynthAMDGPUCombinerImplRuleConfig
#define SYNTH_PASS GISynthAMDGPUCombinerLegacy
#define SYNTH_PASS_DESC "GISynthAMDGPUCombiner"

#include "SynthCombiner.inc"

INITIALIZE_PASS_BEGIN(GISynthAMDGPUCombinerLegacy, DEBUG_TYPE,
                      "Combine with the synthesized rules of AMDGPU", false,
                      false)
INITIALIZE_PASS_DEPENDENCY(TargetPassConfig)
INITIALIZE_PASS_DEPENDENCY(GISelValueTrackingAnalysisLegacy)
INITIALIZE_PASS_DEPENDENCY(MachineDominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(GISelCSEAnalysisWrapperPass)
INITIALIZE_PASS_END(GISynthAMDGPUCombinerLegacy, DEBUG_TYPE,
                    "Combine with the synthesized rules of AMDGPU", false,
                    false)

const void *llvm::getGISynthAMDGPUCombinerID() {
  return &GISynthAMDGPUCombinerLegacy::ID;
}
