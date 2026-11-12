//===- GISynthPredicatesTest.cpp ------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// The helpers of the synthesized combine rules that decide whether and where
// the replacement of a region with several outputs is built.
//
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/GlobalISel/GISynthPredicates.h"
#include "GISelMITest.h"

using namespace llvm::gisynth;

namespace {

/// The first instruction of the function with the opcode \p Opc, after
/// \p Skip earlier ones.
MachineInstr *findOpcode(MachineFunction &MF, unsigned Opc, unsigned Skip = 0) {
  for (MachineBasicBlock &MBB : MF)
    for (MachineInstr &MI : MBB)
      if (MI.getOpcode() == Opc && Skip-- == 0)
        return &MI;
  return nullptr;
}

bool isBefore(const MachineInstr &A, const MachineInstr &B) {
  for (const MachineInstr &MI : *A.getParent()) {
    if (&MI == &A)
      return true;
    if (&MI == &B)
      return false;
  }
  return false;
}

// The sibling (G_SUB) is before the tree of the root (G_SELECT of G_ICMP).
const char *SiblingFirst = "  %3:_(s64) = G_SUB %0, %1\n"
                           "  %4:_(s64) = G_ADD %0, %2\n"
                           "  %5:_(s1) = G_ICMP intpred(uge), %0(s64), %1\n"
                           "  %6:_(s64) = G_SELECT %5(s1), %2, %4\n";

// The root is before the sibling.
const char *RootFirst = "  %4:_(s64) = G_ADD %0, %2\n"
                        "  %5:_(s1) = G_ICMP intpred(uge), %0(s64), %1\n"
                        "  %6:_(s64) = G_SELECT %5(s1), %2, %4\n"
                        "  %7:_(s64) = G_MUL %6, %6\n"
                        "  %3:_(s64) = G_SUB %0, %1\n";

TEST_F(AArch64GISelMITest, FirstRegionOutput) {
  setUp(SiblingFirst);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Sub = findOpcode(*MF, TargetOpcode::G_SUB);
  MachineInstr *Add = findOpcode(*MF, TargetOpcode::G_ADD);
  MachineInstr *Select = findOpcode(*MF, TargetOpcode::G_SELECT);
  Register SubReg = Sub->getOperand(0).getReg();
  Register AddReg = Add->getOperand(0).getReg();

  EXPECT_EQ(firstRegionOutput(*Select, {SubReg}, {}), Sub);
  // Two outputs: the first of them.
  EXPECT_EQ(firstRegionOutput(*Select, {SubReg, AddReg}, {}), Sub);
  // The inputs are defined before the first output.
  EXPECT_EQ(firstRegionOutput(*Select, {SubReg}, {Copies[0], Copies[1]}), Sub);
  // An input that is defined after the first output.
  EXPECT_EQ(firstRegionOutput(*Select, {SubReg}, {AddReg}), nullptr);
  // An output that is not before the root.
  EXPECT_EQ(firstRegionOutput(*Sub, {AddReg}, {}), nullptr);
  // The limit of the distance.
  EXPECT_EQ(firstRegionOutput(*Select, {SubReg}, {}, /*MaxDistance=*/2),
            nullptr);
  EXPECT_EQ(firstRegionOutput(*Select, {SubReg}, {}, /*MaxDistance=*/3), Sub);
}

TEST_F(AArch64GISelMITest, FindSiblingRoot) {
  setUp(SiblingFirst);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Sub = findOpcode(*MF, TargetOpcode::G_SUB);
  MachineInstr *Select = findOpcode(*MF, TargetOpcode::G_SELECT);
  MachineInstr *ICmp = findOpcode(*MF, TargetOpcode::G_ICMP);
  auto IsSub = [](const MachineInstr &MI) {
    return MI.getOpcode() == TargetOpcode::G_SUB;
  };
  auto Any = [](const MachineInstr &MI) { return true; };

  EXPECT_EQ(findSiblingRoot(*MRI, *Select, Copies[0], IsSub), Sub);
  EXPECT_EQ(findSiblingRoot(*MRI, *Select, Copies[1], IsSub), Sub);
  // %2 has no user that is a G_SUB.
  EXPECT_EQ(findSiblingRoot(*MRI, *Select, Copies[2], IsSub), nullptr);
  // The root is not its own sibling: %5 has no other user.
  EXPECT_EQ(findSiblingRoot(*MRI, *Select, ICmp->getOperand(0).getReg(), Any),
            nullptr);
  // The limit of the users: %0 has three.
  unsigned Seen = 0;
  auto Count = [&](const MachineInstr &MI) {
    ++Seen;
    return false;
  };
  EXPECT_EQ(findSiblingRoot(*MRI, *Select, Copies[0], Count), nullptr);
  EXPECT_EQ(Seen, 3u);
  Seen = 0;
  EXPECT_EQ(findSiblingRoot(*MRI, *Select, Copies[0], Count, /*MaxUsers=*/2),
            nullptr);
  EXPECT_EQ(Seen, 2u);
}

TEST_F(AArch64GISelMITest, FindSiblingRootOtherBlock) {
  StringRef MIRString = "  %3:_(s64) = G_SUB %0, %1\n"
                        "  G_BR %bb.2\n"
                        "\n"
                        "  bb.2:\n"
                        "  %5:_(s1) = G_ICMP intpred(uge), %0(s64), %1\n"
                        "  %6:_(s64) = G_SELECT %5(s1), %2, %0\n";
  setUp(MIRString);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Select = findOpcode(*MF, TargetOpcode::G_SELECT);
  auto IsSub = [](const MachineInstr &MI) {
    return MI.getOpcode() == TargetOpcode::G_SUB;
  };
  EXPECT_EQ(findSiblingRoot(*MRI, *Select, Copies[0], IsSub), nullptr);
}

TEST_F(AArch64GISelMITest, FindSiblingRootNotTheTreeAndNotASibling) {
  StringRef MIRString = "  %3:_(s64) = G_SUB %0, %1\n"
                        "  %4:_(s64) = G_SUB %0, %1\n"
                        "  %5:_(s64) = G_SUB %0, %2\n"
                        "  %6:_(s64) = G_ADD %5, %1\n";
  setUp(MIRString);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Sub0 = findOpcode(*MF, TargetOpcode::G_SUB);
  MachineInstr *Sub1 = findOpcode(*MF, TargetOpcode::G_SUB, 1);
  MachineInstr *Sub2 = findOpcode(*MF, TargetOpcode::G_SUB, 2);
  MachineInstr *Add = findOpcode(*MF, TargetOpcode::G_ADD);
  auto IsSub = [](const MachineInstr &MI) {
    return MI.getOpcode() == TargetOpcode::G_SUB;
  };
  // An instruction of the tree of the root (%5) is not a sibling.
  Register Tree[] = {Sub2->getOperand(0).getReg()};
  EXPECT_EQ(findSiblingRoot(*MRI, *Add, Copies[2], IsSub), Sub2);
  EXPECT_EQ(findSiblingRoot(*MRI, *Add, Copies[2], IsSub, 8, Tree), nullptr);
  // A sibling that the plan has is not found again.
  EXPECT_EQ(findSiblingRoot(*MRI, *Add, Copies[1], IsSub, 8, Tree), Sub0);
  MachineInstr *Others[] = {Sub0};
  EXPECT_EQ(findSiblingRoot(*MRI, *Add, Copies[1], IsSub, 8, Tree, Others),
            Sub1);
}

TEST_F(AArch64GISelMITest, HasNUses) {
  setUp(SiblingFirst);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *ICmp = findOpcode(*MF, TargetOpcode::G_ICMP);
  // %0: G_SUB, G_ADD and G_ICMP.
  EXPECT_TRUE(hasNUses(*MRI, Copies[0], 3));
  EXPECT_FALSE(hasNUses(*MRI, Copies[0], 2));
  EXPECT_FALSE(hasNUses(*MRI, Copies[0], 4));
  EXPECT_TRUE(hasNUses(*MRI, ICmp->getOperand(0).getReg(), 1));
}

TEST_F(AArch64GISelMITest, PlanRegionSiblingFirst) {
  setUp(SiblingFirst);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Sub = findOpcode(*MF, TargetOpcode::G_SUB);
  MachineInstr *Add = findOpcode(*MF, TargetOpcode::G_ADD);
  MachineInstr *Select = findOpcode(*MF, TargetOpcode::G_SELECT);
  Register AddReg = Add->getOperand(0).getReg();
  RegionPlan Plan;
  Plan.Sibs.push_back(Sub);

  // The sibling stays: the replacement of the root is built before the
  // root, and the sibling is before that position.
  EXPECT_TRUE(
      planRegion(*Select, Plan, /*Stays=*/1, {Copies[0], Copies[1], AddReg}));
  EXPECT_EQ(Plan.InsertPt, Select);
  EXPECT_TRUE(Plan.Move.empty());
  // The two roots are replaced: before the sibling, which is the first.
  EXPECT_TRUE(planRegion(*Select, Plan, /*Stays=*/0, {Copies[0], Copies[1]}));
  EXPECT_EQ(Plan.InsertPt, Sub);
  EXPECT_TRUE(Plan.Move.empty());
  EXPECT_EQ(&applyRegionPlan(Plan), Sub);
  // An input of the replacement is defined after the sibling.
  EXPECT_FALSE(planRegion(*Select, Plan, /*Stays=*/0, {Copies[0], AddReg}));
}

TEST_F(AArch64GISelMITest, PlanRegionRootFirst) {
  setUp(RootFirst);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Sub = findOpcode(*MF, TargetOpcode::G_SUB);
  MachineInstr *Add = findOpcode(*MF, TargetOpcode::G_ADD);
  MachineInstr *Mul = findOpcode(*MF, TargetOpcode::G_MUL);
  MachineInstr *Select = findOpcode(*MF, TargetOpcode::G_SELECT);
  Register AddReg = Add->getOperand(0).getReg();
  RegionPlan Plan;
  Plan.Sibs.push_back(Sub);

  // The two roots are replaced: before the root, where every input of its
  // tree is defined.
  EXPECT_TRUE(
      planRegion(*Select, Plan, /*Stays=*/0, {Copies[0], Copies[1], AddReg}));
  EXPECT_EQ(Plan.InsertPt, Select);
  EXPECT_TRUE(Plan.Move.empty());
  // An input that is defined after the root, and one that the root defines.
  EXPECT_FALSE(planRegion(*Select, Plan, /*Stays=*/0,
                          {Copies[0], Mul->getOperand(0).getReg()}));
  EXPECT_FALSE(planRegion(*Select, Plan, /*Stays=*/0,
                          {Copies[0], Select->getOperand(0).getReg()}));
  // The sibling stays. The match step does not move it.
  EXPECT_TRUE(planRegion(*Select, Plan, /*Stays=*/1, {Copies[0], Copies[1]}));
  EXPECT_EQ(Plan.InsertPt, Select);
  ASSERT_EQ(Plan.Move.size(), 1u);
  EXPECT_EQ(Plan.Move[0], Sub);
  EXPECT_TRUE(isBefore(*Select, *Sub));
  // The apply step moves it before the root.
  EXPECT_EQ(&applyRegionPlan(Plan), Select);
  EXPECT_TRUE(isBefore(*Sub, *Select));
  EXPECT_EQ(Sub->getParent(), Select->getParent());
  EXPECT_EQ(std::next(Sub->getIterator()), Select->getIterator());
  EXPECT_TRUE(MF->verify(nullptr, "after the move", &errs(),
                         /*AbortOnError=*/false));
}

TEST_F(AArch64GISelMITest, PlanRegionSeveralSiblings) {
  // A sibling that the rule replaces is before the root. Two siblings
  // that stay are after the root, and the second reads the first.
  StringRef MIRString = "  %3:_(s64) = G_SUB %0, %1\n"
                        "  %5:_(s1) = G_ICMP intpred(uge), %0(s64), %1\n"
                        "  %6:_(s64) = G_SELECT %5(s1), %2, %0\n"
                        "  %7:_(s64) = G_MUL %6, %6\n"
                        "  %8:_(s64) = G_XOR %0, %1\n"
                        "  %9:_(s64) = G_AND %8, %1\n";
  setUp(MIRString);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Sub = findOpcode(*MF, TargetOpcode::G_SUB);
  MachineInstr *Select = findOpcode(*MF, TargetOpcode::G_SELECT);
  MachineInstr *Xor = findOpcode(*MF, TargetOpcode::G_XOR);
  MachineInstr *And = findOpcode(*MF, TargetOpcode::G_AND);
  RegionPlan Plan;
  // Not in the order of the block.
  Plan.Sibs.push_back(And);
  Plan.Sibs.push_back(Sub);
  Plan.Sibs.push_back(Xor);

  // The position is the sibling that the rule replaces. The siblings that
  // stay are moved before it, in the order of the block.
  EXPECT_TRUE(planRegion(*Select, Plan, /*Stays=*/0b101,
                         {Copies[0], Copies[1], Copies[2]}));
  EXPECT_EQ(Plan.InsertPt, Sub);
  ASSERT_EQ(Plan.Move.size(), 2u);
  EXPECT_EQ(Plan.Move[0], Xor);
  EXPECT_EQ(Plan.Move[1], And);
  EXPECT_EQ(&applyRegionPlan(Plan), Sub);
  EXPECT_EQ(std::next(Xor->getIterator()), And->getIterator());
  EXPECT_EQ(std::next(And->getIterator()), Sub->getIterator());
  EXPECT_TRUE(MF->verify(nullptr, "after the move", &errs(),
                         /*AbortOnError=*/false));

  // No sibling is replaced: the position is the root, and the sibling
  // that is before it does not move.
  setUp(MIRString);
  Sub = findOpcode(*MF, TargetOpcode::G_SUB);
  Select = findOpcode(*MF, TargetOpcode::G_SELECT);
  Xor = findOpcode(*MF, TargetOpcode::G_XOR);
  Plan = RegionPlan();
  Plan.Sibs.push_back(Sub);
  Plan.Sibs.push_back(Xor);
  EXPECT_TRUE(planRegion(*Select, Plan, /*Stays=*/0b11,
                         {Copies[0], Copies[1], Copies[2]}));
  EXPECT_EQ(Plan.InsertPt, Select);
  ASSERT_EQ(Plan.Move.size(), 1u);
  EXPECT_EQ(Plan.Move[0], Xor);
}

TEST_F(AArch64GISelMITest, PlanRegionTooFar) {
  // 70 instructions between the two roots: more than the limit of the
  // search.
  std::string MIR = "  %3:_(s64) = G_SUB %0, %1\n";
  for (unsigned I = 0; I != 70; ++I)
    MIR += "  %" + std::to_string(10 + I) + ":_(s64) = G_ADD %0, %2\n";
  MIR += "  %5:_(s1) = G_ICMP intpred(uge), %0(s64), %1\n"
         "  %6:_(s64) = G_SELECT %5(s1), %2, %0\n";
  setUp(MIR);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Sub = findOpcode(*MF, TargetOpcode::G_SUB);
  MachineInstr *Select = findOpcode(*MF, TargetOpcode::G_SELECT);
  RegionPlan Plan;
  Plan.Sibs.push_back(Sub);
  EXPECT_FALSE(planRegion(*Select, Plan, /*Stays=*/1, {}));
  EXPECT_FALSE(planRegion(*Select, Plan, /*Stays=*/0, {}));
  EXPECT_TRUE(planRegion(*Select, Plan, /*Stays=*/0, {},
                         /*MaxDistance=*/100));
}

TEST_F(AArch64GISelMITest, IsJointRegionFillsThePlan) {
  StringRef MIRString = "  %3:_(s64) = G_ADD %0, %1\n"
                        "  %4:_(s64) = G_MUL %3, %2\n"
                        "  %5:_(s1) = G_ICMP intpred(ult), %3(s64), %0\n"
                        "  %6:_(s64) = G_ZEXT %5\n";
  setUp(MIRString);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Add = findOpcode(*MF, TargetOpcode::G_ADD);
  MachineInstr *ICmp = findOpcode(*MF, TargetOpcode::G_ICMP);
  MachineInstr *ZExt = findOpcode(*MF, TargetOpcode::G_ZEXT);
  Register AddReg = Add->getOperand(0).getReg();
  Register CmpReg = ICmp->getOperand(0).getReg();
  RegionPlan Plan;
  // The sum has a user outside the tree of the comparison.
  EXPECT_TRUE(
      isJointRegion(*MRI, CmpReg, {AddReg}, {Copies[0], Copies[1]}, Plan));
  EXPECT_EQ(Plan.InsertPt, Add);
  EXPECT_TRUE(Plan.Sibs.empty());
  EXPECT_EQ(&applyRegionPlan(Plan), Add);
  // The comparison has one user: the rule for the root alone applies.
  EXPECT_FALSE(isJointRegion(*MRI, ZExt->getOperand(0).getReg(), {CmpReg},
                             {Copies[0]}, Plan));
}

TEST_F(AArch64GISelMITest, ReleaseResults) {
  // Three roots become one G_USUBO and one G_XOR that reads its borrow.
  StringRef MIRString = "  %3:_(s64) = G_SUB %0, %1\n"
                        "  %4:_(s1) = G_ICMP intpred(ult), %0(s64), %1\n"
                        "  %5:_(s1) = G_ICMP intpred(uge), %0(s64), %1\n"
                        "  %6:_(s64) = G_ZEXT %4\n"
                        "  %7:_(s64) = G_ZEXT %5\n"
                        "  %8:_(s64) = G_ADD %3, %6\n"
                        "  %9:_(s64) = G_ADD %8, %7\n"
                        "  $x0 = COPY %9\n";
  setUp(MIRString);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Sub = findOpcode(*MF, TargetOpcode::G_SUB);
  MachineInstr *ULT = findOpcode(*MF, TargetOpcode::G_ICMP);
  MachineInstr *UGE = &*std::next(ULT->getIterator());
  ASSERT_EQ(UGE->getOpcode(), TargetOpcode::G_ICMP);
  Register Diff = Sub->getOperand(0).getReg();
  Register Borrow = ULT->getOperand(0).getReg();
  Register Dst = UGE->getOperand(0).getReg();
  RegionPlan Plan;
  Plan.Sibs.push_back(Sub);
  Plan.Sibs.push_back(ULT);
  ASSERT_TRUE(planRegion(*UGE, Plan, /*Stays=*/0, {Copies[0], Copies[1]}));

  B.setInstrAndDebugLoc(applyRegionPlan(Plan));
  releaseResults(*MRI, *Sub);
  releaseResults(*MRI, *ULT);
  releaseResults(*MRI, *UGE);
  // The old registers have their types and their users, and no
  // definition. The old instructions define other registers.
  EXPECT_TRUE(MRI->def_empty(Diff));
  EXPECT_TRUE(MRI->def_empty(Borrow));
  EXPECT_TRUE(MRI->def_empty(Dst));
  EXPECT_FALSE(MRI->use_nodbg_empty(Diff));
  EXPECT_NE(Sub->getOperand(0).getReg(), Diff);
  EXPECT_EQ(MRI->getType(Sub->getOperand(0).getReg()), LLT::scalar(64));
  EXPECT_EQ(MRI->getType(ULT->getOperand(0).getReg()), LLT::scalar(1));

  auto USubO = B.buildInstr(TargetOpcode::G_USUBO, {Diff, Borrow},
                            {Copies[0], Copies[1]});
  // A register of a replaced sibling has one definition: the new
  // instruction. A builder that folds constants reads it.
  EXPECT_EQ(MRI->getVRegDef(Borrow), &*USubO);
  auto One = B.buildConstant(LLT::scalar(1), 1);
  B.buildInstr(TargetOpcode::G_XOR, {Dst}, {Borrow, One.getReg(0)});
  Sub->eraseFromParent();
  ULT->eraseFromParent();
  UGE->eraseFromParent();
  EXPECT_EQ(MRI->getVRegDef(Diff), &*USubO);
  EXPECT_TRUE(MF->verify(nullptr, "after the replacement", &errs(),
                         /*AbortOnError=*/false));
}

TEST_F(AArch64GISelMITest, ScalarWidthsOfPointers) {
  StringRef MIRString = "  %3:_(p0) = G_INTTOPTR %0(s64)\n"
                        "  %4:_(p0) = G_PTR_ADD %3, %1(s64)\n"
                        "  %5:_(p1) = G_INTTOPTR %0(s64)\n"
                        "  %6:_(s32) = G_TRUNC %1(s64)\n"
                        "  %7:_(<2 x s32>) = G_BUILD_VECTOR %6(s32), %6\n";
  setUp(MIRString);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *P0 = findOpcode(*MF, TargetOpcode::G_INTTOPTR);
  MachineInstr *Add = findOpcode(*MF, TargetOpcode::G_PTR_ADD);
  MachineInstr *P1 = findOpcode(*MF, TargetOpcode::G_INTTOPTR, 1);
  MachineInstr *Trunc = findOpcode(*MF, TargetOpcode::G_TRUNC);
  MachineInstr *Vec = findOpcode(*MF, TargetOpcode::G_BUILD_VECTOR);
  Register Ptr = P0->getOperand(0).getReg();
  Register Sum = Add->getOperand(0).getReg();
  Register Other = P1->getOperand(0).getReg();
  Register Int = Trunc->getOperand(0).getReg();
  unsigned W[3] = {0, 0, 0};
  // The registers that the rule has as pointers are pointers, and the
  // others are scalars.
  EXPECT_TRUE(getScalarWidths(*MRI, {Ptr, Int, Sum}, W, 0b101));
  EXPECT_EQ(W[0], 64u);
  EXPECT_EQ(W[1], 32u);
  EXPECT_EQ(W[2], 64u);
  EXPECT_TRUE(getScalarWidths(*MRI, {Copies[0], Int}, W));
  EXPECT_FALSE(getScalarWidths(*MRI, {Ptr, Int, Sum}, W));
  EXPECT_FALSE(getScalarWidths(*MRI, {Ptr, Int, Sum}, W, 0b001));
  EXPECT_FALSE(getScalarWidths(*MRI, {Ptr, Int, Sum}, W, 0b111));
  EXPECT_FALSE(getScalarWidths(*MRI, {Vec->getOperand(0).getReg()}, W));
  // Two pointers of one width have one type: a new pointer takes its type
  // from one of them.
  EXPECT_FALSE(getScalarWidths(*MRI, {Ptr, Other}, W, 0b11));
  EXPECT_TRUE(getScalarWidths(*MRI, {Other}, W, 0b1));
}

TEST_F(AArch64GISelMITest, DropFlags) {
  StringRef MIRString = "  %3:_(s64) = nuw nsw G_ADD %0, %1\n"
                        "  %4:_(s64) = G_SUB %0, %1\n"
                        "  %5:_(s64) = nnan nsz G_FADD %0, %1\n";
  setUp(MIRString);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Add = findOpcode(*MF, TargetOpcode::G_ADD);
  MachineInstr *Sub = findOpcode(*MF, TargetOpcode::G_SUB);
  MachineInstr *FAdd = findOpcode(*MF, TargetOpcode::G_FADD);
  ASSERT_TRUE(Add->getFlag(MachineInstr::NoUWrap));
  ASSERT_TRUE(FAdd->getFlag(MachineInstr::FmNsz));
  Add->setFlag(MachineInstr::NoMerge);
  dropFlags(B, *Add);
  dropFlags(B, *Sub);
  dropFlags(B, *FAdd);
  EXPECT_FALSE(Add->getFlag(MachineInstr::NoUWrap));
  EXPECT_FALSE(Add->getFlag(MachineInstr::NoSWrap));
  // Not a flag on the value of the instruction.
  EXPECT_TRUE(Add->getFlag(MachineInstr::NoMerge));
  EXPECT_EQ(Sub->getFlags(), 0u);
  EXPECT_EQ(FAdd->getFlags(), 0u);
}

} // namespace
