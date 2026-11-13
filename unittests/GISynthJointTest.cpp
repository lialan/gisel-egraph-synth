//===- GISynthJointTest.cpp -----------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// The matcher of the joint region rules (GISelEGraphSynth/GISynthJoint.h):
// a rule that does not make the generic cost smaller (OriginalOnly) never
// replaces an instruction that the combiner created, so that two such rules
// cannot rewrite each other's results forever; screening reports a match
// and changes nothing.
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GISynthJoint.h"
#include "GISelMITest.h"

using namespace llvm::gisynth::joint;

namespace {

MachineInstr *findOpcode(MachineFunction &MF, unsigned Opc) {
  for (MachineBasicBlock &MBB : MF)
    for (MachineInstr &MI : MBB)
      if (MI.getOpcode() == Opc)
        return &MI;
  return nullptr;
}

// x << 1 -> x + x and x + x -> x << 1: two rules of one generic cost that
// undo each other (a search with a cost slack can find both).
const NodeDesc ShlSrc[] = {{TargetOpcode::G_SHL, -1, 1, 2, false,
                            {{in(0), lit(1), Ref()}}, {{0, 0}}, {{0, 0, 0}}}};
const NodeDesc AddOfX[] = {{TargetOpcode::G_ADD, -1, 1, 2, true,
                            {{in(0), in(0), Ref()}}, {{0, 0}}, {{0, 0, 0}}}};
const MatchStep AnchorOnly[] = {{0, Find::Anchor, Ref()}};
const Action ReplaceIt[] = {Action::Replace};
const OutputDesc ToTgt0[] = {{0, 0, tgt(0, 0), 0}};
const uint8_t OneClass[] = {0};
const uint16_t Width64[] = {64};

RuleDesc rule(const char *Name, ArrayRef<NodeDesc> Src, ArrayRef<NodeDesc> Tgt,
              bool OriginalOnly) {
  return {Name,  Src,      AnchorOnly, ReplaceIt, Tgt, ToTgt0, 1,
          OneClass, 0,     0,          1,         Width64, OriginalOnly};
}

const char *ShlByOne = "  %3:_(s64) = G_CONSTANT i64 1\n"
                       "  %4:_(s64) = G_SHL %0, %3(s64)\n"
                       "  $x0 = COPY %4(s64)\n";

TEST_F(AArch64GISelMITest, OriginalOnlyMatchesOriginalInstructions) {
  setUp(ShlByOne);
  if (!TM)
    GTEST_SKIP();
  RuleDesc ShlToAdd = rule("shl_to_add", ShlSrc, AddOfX, true);
  MachineInstr *Shl = findOpcode(*MF, TargetOpcode::G_SHL);
  ASSERT_TRUE(Shl);
  JointPlan Plan;
  // Without a combiner state, and with every register of the function
  // older than the combiner.
  EXPECT_TRUE(match(ShlToAdd, *Shl, *MRI, Plan));
  MatchEnv Env;
  Env.FirstNewVReg = MRI->getNumVirtRegs();
  EXPECT_TRUE(match(ShlToAdd, *Shl, *MRI, Plan, Env));
  // The same instruction, created by the combiner.
  Env.FirstNewVReg = Shl->getOperand(0).getReg().virtRegIndex();
  EXPECT_FALSE(match(ShlToAdd, *Shl, *MRI, Plan, Env));
  // A rule that makes the cost smaller is not limited.
  RuleDesc Smaller = rule("smaller", ShlSrc, AddOfX, false);
  EXPECT_TRUE(match(Smaller, *Shl, *MRI, Plan, Env));
}

TEST_F(AArch64GISelMITest, OriginalOnlyStopsARewriteBack) {
  setUp(ShlByOne);
  if (!TM)
    GTEST_SKIP();
  RuleDesc ShlToAdd = rule("shl_to_add", ShlSrc, AddOfX, true);
  RuleDesc AddToShl = rule("add_to_shl", AddOfX, ShlSrc, true);
  MatchEnv Env;
  Env.FirstNewVReg = MRI->getNumVirtRegs();
  MachineInstr *Shl = findOpcode(*MF, TargetOpcode::G_SHL);
  JointPlan Plan;
  ASSERT_TRUE(match(ShlToAdd, *Shl, *MRI, Plan, Env));
  apply(ShlToAdd, B, Plan);
  EXPECT_FALSE(findOpcode(*MF, TargetOpcode::G_SHL));
  MachineInstr *Add = findOpcode(*MF, TargetOpcode::G_ADD);
  ASSERT_TRUE(Add);
  // The second rule would turn the new G_ADD back into a G_SHL, and the
  // first one would then apply again.
  EXPECT_TRUE(match(AddToShl, *Add, *MRI, Plan));
  EXPECT_FALSE(match(AddToShl, *Add, *MRI, Plan, Env));
}

TEST_F(AArch64GISelMITest, ScreeningChangesNothing) {
  setUp(ShlByOne);
  if (!TM)
    GTEST_SKIP();
  RuleDesc ShlToAdd = rule("shl_to_add", ShlSrc, AddOfX, false);
  MachineInstr *Shl = findOpcode(*MF, TargetOpcode::G_SHL);
  JointPlan Plan;
  MatchEnv Env;
  Env.ScreenOnly = true;
  EXPECT_FALSE(match(ShlToAdd, *Shl, *MRI, Plan, Env));
  EXPECT_EQ(findOpcode(*MF, TargetOpcode::G_SHL), Shl);
}

} // namespace
