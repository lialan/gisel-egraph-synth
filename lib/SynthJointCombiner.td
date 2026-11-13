//===- SynthJointCombiner.td - Combiner of the joint region rules -*- tablegen -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// The combiner of the joint region rules (td/GISynthJointCombines.td, written
// by `gi-rule-synth.py joint-emit`). It has these rules only, so that one llc
// with and without -gisel-synth-joint-combines measures exactly them.
//
//===----------------------------------------------------------------------===//

include "llvm/Target/Target.td"
include "llvm/Target/GlobalISel/Combine.td"

def GISynthJointInstrInfo : InstrInfo;
def GISynthJoint : Target {
  let InstructionSet = GISynthJointInstrInfo;
}

// The plan of a joint rule: the match step fills it, the apply step
// executes it (GISelEGraphSynth/GISynthJoint.h).
def gisynth_joint_plan : GIDefMatchData<"gisynth::joint::JointPlan">;

include "GISynthJointCombines.td"

def GISynthJointCombiner : GICombiner<
  "GISynthJointCombinerImpl", [gi_synth_joint_combines]>;
