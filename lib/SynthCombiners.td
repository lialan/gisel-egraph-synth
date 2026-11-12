//===- SynthCombiners.td - Combiners of the synthesized rules -*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// One combiner for each target that hosts synthesized rules. A combiner has
// the generic combines (all_combines) and the group of the target, in the
// same order as when the group was part of the target's pre-legalizer
// combiner, so that the generic combines can clean up after a rule.
//
// The combiner emitter needs a Target record. The rules are generic, so a
// target with no instructions of its own is sufficient.
//
//===----------------------------------------------------------------------===//

include "llvm/Target/Target.td"
include "llvm/Target/GlobalISel/Combine.td"
include "GISynthCombines.td"

def GISynthInstrInfo : InstrInfo;
def GISynth : Target {
  let InstructionSet = GISynthInstrInfo;
}

def GISynthAMDGPUCombiner : GICombiner<
  "GISynthAMDGPUCombinerImpl", [all_combines, gi_synth_combines_amdgpu]>;

def GISynthAArch64Combiner : GICombiner<
  "GISynthAArch64CombinerImpl", [all_combines, gi_synth_combines_aarch64]>;
