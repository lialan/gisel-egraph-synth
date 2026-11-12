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
#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/CodeGen/MachineFrameInfo.h"

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
  // A fixed vector has the type code (lanes << 16) | element width, which
  // is not the width of a scalar: a rule for scalars does not have it in
  // its schedule.
  Register V = Vec->getOperand(0).getReg();
  EXPECT_TRUE(getScalarWidths(*MRI, {V}, W));
  EXPECT_EQ(W[0], (2u << 16) | 32u);
  // A lane-wise rule reads the element widths if all registers are vectors
  // with one number of lanes.
  EXPECT_TRUE(getScalarWidths(*MRI, {V, V}, W, 0, /*Lift=*/true));
  EXPECT_EQ(W[0], 32u);
  EXPECT_EQ(W[1], 32u);
  EXPECT_TRUE(getScalarWidths(*MRI, {V, Int}, W, 0, /*Lift=*/true));
  EXPECT_EQ(W[0], (2u << 16) | 32u);
  EXPECT_EQ(W[1], 32u);
  EXPECT_TRUE(getScalarWidths(*MRI, {Int, V}, W, 0, /*Lift=*/true));
  EXPECT_EQ(W[0], 32u);
  EXPECT_EQ(W[1], (2u << 16) | 32u);
  // A vector of scalars is not a vector of pointers.
  EXPECT_FALSE(getScalarWidths(*MRI, {V}, W, 0b1));
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

TEST_F(AArch64GISelMITest, StablePhiInputs) {
  StringRef MIRString = "  %3:_(s64) = G_ADD %0, %1\n"
                        "  %4:_(s1) = G_TRUNC %2(s64)\n"
                        "  G_BRCOND %4(s1), %bb.3\n"
                        "  G_BR %bb.2\n"
                        "\n"
                        "  bb.2:\n"
                        "  %5:_(s64) = G_SUB %0, %1\n"
                        "  G_BR %bb.3\n"
                        "\n"
                        "  bb.3:\n"
                        "  %6:_(s64) = G_PHI %0(s64), %bb.1, %3(s64), %bb.2\n"
                        "  %7:_(s64) = G_PHI %0(s64), %bb.1, %5(s64), %bb.2\n"
                        "  G_BR %bb.4\n"
                        "\n"
                        "  bb.4:\n"
                        "  %8:_(s64) = G_PHI %6(s64), %bb.3, %9(s64), %bb.4\n"
                        "  %9:_(s64) = G_ADD %8, %0\n"
                        "  G_BRCOND %4(s1), %bb.4\n"
                        "  G_BR %bb.5\n"
                        "\n"
                        "  bb.5:\n"
                        "  %10:_(s64) = G_PHI %9(s64), %bb.4\n";
  setUp(MIRString);
  if (!TM)
    GTEST_SKIP();
  MachineDominatorTree MDT(*MF);
  auto Dominates = [&](const MachineInstr &Def, const MachineInstr &Use) {
    return MDT.dominates(&Def, &Use);
  };
  auto IsStable = [&](unsigned Skip) {
    return hasStablePhiInputs(*MRI, *findOpcode(*MF, TargetOpcode::G_PHI, Skip),
                              Dominates);
  };
  // The two incoming values are defined in the entry block.
  EXPECT_TRUE(IsStable(0));
  // %5 is defined in a predecessor: its block does not dominate the G_PHI.
  EXPECT_FALSE(IsStable(1));
  // %9 is the value of the iteration before: it is defined in the block of
  // the G_PHI.
  EXPECT_FALSE(IsStable(2));
  // After the loop, %9 is the value of the last iteration.
  EXPECT_TRUE(IsStable(3));
  // Not a G_PHI.
  EXPECT_FALSE(hasStablePhiInputs(*MRI, *findOpcode(*MF, TargetOpcode::G_ADD),
                                  Dominates));
  // Without a dominator tree, no incoming value is known to dominate.
  auto Never = [](const MachineInstr &, const MachineInstr &) { return false; };
  EXPECT_FALSE(
      hasStablePhiInputs(*MRI, *findOpcode(*MF, TargetOpcode::G_PHI), Never));
}

TEST_F(AArch64GISelMITest, ForwardedStoreValue) {
  StringRef MIRString =
      "  %3:_(p0) = G_INTTOPTR %0(s64)\n"
      "  %4:_(p0) = G_INTTOPTR %1(s64)\n"
      "  G_STORE %2(s64), %3(p0) :: (store (s64))\n"
      "  %5:_(s64) = G_ADD %0, %1\n"
      "  %6:_(s64) = G_LOAD %3(p0) :: (load (s64))\n"
      "  G_STORE %2(s64), %3(p0) :: (store (s8))\n"
      "  %7:_(s64) = G_ZEXTLOAD %3(p0) :: (load (s8))\n"
      "  %8:_(s64) = G_SEXTLOAD %3(p0) :: (load (s8))\n"
      "  %9:_(s8) = G_LOAD %3(p0) :: (load (s8))\n"
      "  %10:_(s64) = G_ZEXTLOAD %3(p0) :: (load (s16))\n"
      "  G_STORE %2(s64), %3(p0) :: (store (s64))\n"
      "  G_STORE %2(s64), %4(p0) :: (store (s64))\n"
      "  %11:_(s64) = G_LOAD %3(p0) :: (load (s64))\n"
      "  G_STORE %2(s64), %3(p0) :: (volatile store (s64))\n"
      "  %12:_(s64) = G_LOAD %3(p0) :: (load (s64))\n"
      "  G_STORE %2(s64), %3(p0) :: (store (s64))\n"
      "  %13:_(s64) = G_LOAD %3(p0) :: (volatile load (s64))\n"
      "  %14:_(s64) = G_LOAD %3(p0) :: (load seq_cst (s64))\n"
      "  %15:_(p0) = G_LOAD %3(p0) :: (load (p0))\n"
      "  %16:_(s64) = G_ATOMICRMW_ADD %4(p0), %0 :: (load store seq_cst "
      "(s64))\n"
      "  %17:_(s64) = G_LOAD %3(p0) :: (load (s64))\n"
      "  G_STORE %3(p0), %4(p0) :: (store (p0))\n"
      "  %18:_(p0) = G_LOAD %4(p0) :: (load (p0))\n"
      "  %19:_(s64) = G_LOAD %4(p0) :: (load (s64))\n";
  setUp(MIRString);
  if (!TM)
    GTEST_SKIP();
  auto Dst = [&](unsigned Opc, unsigned Skip) {
    return findOpcode(*MF, Opc, Skip)->getOperand(0).getReg();
  };
  auto Load = [&](unsigned Skip) { return Dst(TargetOpcode::G_LOAD, Skip); };
  Register Ptr = Dst(TargetOpcode::G_INTTOPTR, 0);
  Register ZExt8 = Dst(TargetOpcode::G_ZEXTLOAD, 0);
  Register SExt8 = Dst(TargetOpcode::G_SEXTLOAD, 0);
  Register ZExt16 = Dst(TargetOpcode::G_ZEXTLOAD, 1);

  // %6: a G_ADD between the G_STORE and the load does not write memory.
  EXPECT_EQ(getForwardedStoreValue(*MRI, Load(0), 64), Copies[2]);
  // Not the number of bits of the load.
  EXPECT_FALSE(getForwardedStoreValue(*MRI, Load(0), 32).isValid());
  EXPECT_FALSE(getForwardedStoreValue(*MRI, Load(0), 0).isValid());
  // %7, %8, %9: the low 8 bits of a wider value.
  EXPECT_EQ(getForwardedStoreValue(*MRI, ZExt8, 8), Copies[2]);
  EXPECT_EQ(getForwardedStoreValue(*MRI, SExt8, 8), Copies[2]);
  EXPECT_EQ(getForwardedStoreValue(*MRI, Load(1), 8), Copies[2]);
  // %10: the G_STORE wrote 8 bits and the load reads 16 bits.
  EXPECT_FALSE(getForwardedStoreValue(*MRI, ZExt16, 16).isValid());
  // %11: the nearest G_STORE has another pointer register.
  EXPECT_FALSE(getForwardedStoreValue(*MRI, Load(2), 64).isValid());
  // %12: a volatile G_STORE.
  EXPECT_FALSE(getForwardedStoreValue(*MRI, Load(3), 64).isValid());
  // %13, %14: a volatile load and an atomic load.
  EXPECT_FALSE(getForwardedStoreValue(*MRI, Load(4), 64).isValid());
  EXPECT_FALSE(getForwardedStoreValue(*MRI, Load(5), 64).isValid());
  // %15: the bits of an integer are not a pointer.
  EXPECT_FALSE(getForwardedStoreValue(*MRI, Load(6), 64).isValid());
  // %17: an atomic read-modify-write is nearer than the G_STORE.
  EXPECT_FALSE(getForwardedStoreValue(*MRI, Load(7), 64).isValid());
  // %18: a pointer of the same type.
  EXPECT_EQ(getForwardedStoreValue(*MRI, Load(8), 64), Ptr);
  // %19: the bits of a pointer are not an integer.
  EXPECT_FALSE(getForwardedStoreValue(*MRI, Load(9), 64).isValid());
  // Not a load.
  EXPECT_FALSE(getForwardedStoreValue(*MRI, Copies[0], 64).isValid());
}

TEST_F(AArch64GISelMITest, ForwardedStoreValueDistance) {
  // MaxForwardDistance instructions is the limit: the G_STORE is the
  // instruction number MaxForwardDistance before the first load, and one
  // more before the second load.
  std::string MIRString = "  %3:_(p0) = G_INTTOPTR %0(s64)\n"
                          "  G_STORE %2(s64), %3(p0) :: (store (s64))\n";
  for (unsigned I = 0; I + 1 < MaxForwardDistance; ++I)
    MIRString += "  %" + std::to_string(10 + I) + ":_(s64) = G_ADD %0, %1\n";
  MIRString += "  %4:_(s64) = G_LOAD %3(p0) :: (load (s64))\n"
               "  %5:_(s64) = G_LOAD %3(p0) :: (load (s64))\n";
  setUp(MIRString);
  if (!TM)
    GTEST_SKIP();
  Register First =
      findOpcode(*MF, TargetOpcode::G_LOAD, 0)->getOperand(0).getReg();
  Register Second =
      findOpcode(*MF, TargetOpcode::G_LOAD, 1)->getOperand(0).getReg();
  EXPECT_EQ(getForwardedStoreValue(*MRI, First, 64), Copies[2]);
  EXPECT_FALSE(getForwardedStoreValue(*MRI, Second, 64).isValid());
}

TEST_F(AArch64GISelMITest, ExtLoadFact) {
  setUp("  %3:_(p0) = G_INTTOPTR %0(s64)\n"
        "  %4:_(s64) = G_ZEXTLOAD %3(p0) :: (load (s8))\n"
        "  %5:_(s64) = G_SEXTLOAD %3(p0) :: (load (s16))\n"
        "  %6:_(s64) = G_LOAD %3(p0) :: (load (s64))\n");
  if (!TM)
    GTEST_SKIP();
  auto Dst = [&](unsigned Opc) {
    return findOpcode(*MF, Opc)->getOperand(0).getReg();
  };
  Register ZExt = Dst(TargetOpcode::G_ZEXTLOAD);
  Register SExt = Dst(TargetOpcode::G_SEXTLOAD);
  EXPECT_TRUE(isExtLoadOf(*MRI, ZExt, /*Signed=*/false, 8));
  EXPECT_FALSE(isExtLoadOf(*MRI, ZExt, /*Signed=*/true, 8));
  EXPECT_FALSE(isExtLoadOf(*MRI, ZExt, /*Signed=*/false, 16));
  EXPECT_TRUE(isExtLoadOf(*MRI, SExt, /*Signed=*/true, 16));
  EXPECT_FALSE(isExtLoadOf(*MRI, SExt, /*Signed=*/false, 16));
  EXPECT_FALSE(isExtLoadOf(*MRI, SExt, /*Signed=*/true, 0));
  // A G_LOAD and a value that no load defines.
  EXPECT_FALSE(isExtLoadOf(*MRI, Dst(TargetOpcode::G_LOAD), false, 64));
  EXPECT_FALSE(isExtLoadOf(*MRI, Copies[0], false, 8));
}

TEST_F(AArch64GISelMITest, MayWriteMemory) {
  setUp("  %3:_(p0) = G_INTTOPTR %0(s64)\n"
        "  %4:_(p0) = G_INTTOPTR %1(s64)\n"
        "  %5:_(s64) = G_LOAD %3(p0) :: (load (s64))\n"
        "  %6:_(s64) = G_ADD %0, %1\n"
        "  G_STORE %2(s64), %3(p0) :: (store (s64))\n"
        "  %7:_(s64) = G_ATOMICRMW_XCHG %3(p0), %0 :: (load store seq_cst "
        "(s64))\n"
        "  %8:_(s64) = G_ATOMIC_CMPXCHG %3(p0), %0, %1 :: (load store seq_cst "
        "seq_cst (s64))\n"
        "  G_MEMCPY %3(p0), %4(p0), %0(s64), 0 :: (store (s8)), (load (s8))\n"
        "  %9:_(s8) = G_TRUNC %2(s64)\n"
        "  G_MEMSET %3(p0), %9(s8), %0(s64), 0 :: (store (s8))\n"
        "  G_FENCE 7, 1\n");
  if (!TM)
    GTEST_SKIP();
  auto Writes = [&](unsigned Opc) {
    return mayWriteMemory(*findOpcode(*MF, Opc));
  };
  EXPECT_FALSE(Writes(TargetOpcode::G_INTTOPTR));
  EXPECT_FALSE(Writes(TargetOpcode::G_LOAD));
  EXPECT_FALSE(Writes(TargetOpcode::G_ADD));
  EXPECT_TRUE(Writes(TargetOpcode::G_STORE));
  EXPECT_TRUE(Writes(TargetOpcode::G_ATOMICRMW_XCHG));
  EXPECT_TRUE(Writes(TargetOpcode::G_ATOMIC_CMPXCHG));
  EXPECT_TRUE(Writes(TargetOpcode::G_MEMCPY));
  EXPECT_TRUE(Writes(TargetOpcode::G_MEMSET));
  // What a G_FENCE does is not a property of its operands.
  EXPECT_TRUE(Writes(TargetOpcode::G_FENCE));
}

TEST_F(AArch64GISelMITest, ConstantBits) {
  setUp("  %3:_(s32) = G_CONSTANT i32 7\n"
        "  %4:_(s32) = G_FCONSTANT float 2.000000e+00\n"
        "  %5:_(s64) = G_FCONSTANT double -5.000000e-01\n"
        "  %6:_(p0) = G_CONSTANT i64 0\n"
        "  %7:_(<2 x s32>) = G_BUILD_VECTOR %4(s32), %4(s32)\n"
        "  %8:_(<2 x s32>) = G_BUILD_VECTOR %3(s32), %4(s32)\n"
        "  %9:_(<2 x s32>) = G_BUILD_VECTOR %3(s32), %3(s32)\n"
        "  %10:_(s64) = G_FREEZE %0\n");
  if (!TM)
    GTEST_SKIP();
  auto Dst = [&](unsigned Opc, unsigned Skip = 0) {
    return findOpcode(*MF, Opc, Skip)->getOperand(0).getReg();
  };
  Register Int = Dst(TargetOpcode::G_CONSTANT);
  Register Float = Dst(TargetOpcode::G_FCONSTANT);
  Register Double = Dst(TargetOpcode::G_FCONSTANT, 1);
  Register Null = Dst(TargetOpcode::G_CONSTANT, 1);
  Register FSplat = Dst(TargetOpcode::G_BUILD_VECTOR);
  Register Mixed = Dst(TargetOpcode::G_BUILD_VECTOR, 1);
  Register ISplat = Dst(TargetOpcode::G_BUILD_VECTOR, 2);
  Register Frame = B.buildFrameIndex(LLT::pointer(0, 64),
                                     MF->getFrameInfo().CreateStackObject(
                                         8, Align(8), /*isSpillSlot=*/false))
                       .getReg(0);

  EXPECT_EQ(*getConstantBits(Int, *MRI), APInt(32, 7));
  // A G_FCONSTANT has its bit pattern.
  EXPECT_EQ(*getConstantBits(Float, *MRI), APInt(32, 0x40000000));
  EXPECT_EQ(*getConstantBits(Double, *MRI),
            APInt(64, UINT64_C(0xBFE0000000000000)));
  EXPECT_EQ(*getConstantBits(Null, *MRI), APInt(64, 0));
  // A vector only with AllowSplat, and only with one constant in all
  // lanes.
  EXPECT_FALSE(getConstantBits(FSplat, *MRI));
  EXPECT_EQ(*getConstantBits(FSplat, *MRI, /*AllowSplat=*/true),
            APInt(32, 0x40000000));
  EXPECT_EQ(*getConstantBits(ISplat, *MRI, /*AllowSplat=*/true), APInt(32, 7));
  EXPECT_FALSE(getConstantBits(Mixed, *MRI, /*AllowSplat=*/true));
  // The bits of an address and of an argument are not known.
  EXPECT_FALSE(getConstantBits(Frame, *MRI));
  EXPECT_FALSE(getConstantBits(Copies[0], *MRI));

  // An address is a constant of the function: neither undef nor poison.
  EXPECT_TRUE(isAddressConstant(Frame, *MRI));
  EXPECT_FALSE(isAddressConstant(Null, *MRI));
  EXPECT_TRUE(isDefinedValue(Frame, *MRI));
  EXPECT_TRUE(isDefinedValue(Float, *MRI));
  EXPECT_TRUE(isDefinedValue(Dst(TargetOpcode::G_FREEZE), *MRI));
  EXPECT_FALSE(isDefinedValue(Copies[0], *MRI));

  // The known bits of a G_FCONSTANT are its bits.
  GISelValueTracking VT(*MF);
  KnownBits K = getKnownBitsOrConstant(VT, *MRI, Float);
  EXPECT_TRUE(K.isConstant());
  EXPECT_EQ(K.getConstant(), APInt(32, 0x40000000));
  EXPECT_FALSE(getKnownBitsOrConstant(VT, *MRI, Copies[0]).isConstant());
}

TEST(GISynthPredicates, FloatLiterals) {
  EXPECT_EQ(getFPLiteralBits(FPLiteral::Zero, 32), APInt(32, 0));
  EXPECT_EQ(getFPLiteralBits(FPLiteral::NegZero, 32), APInt(32, 0x80000000));
  EXPECT_EQ(getFPLiteralBits(FPLiteral::One, 32), APInt(32, 0x3F800000));
  EXPECT_EQ(getFPLiteralBits(FPLiteral::NegOne, 16), APInt(16, 0xBC00));
  EXPECT_EQ(getFPLiteralBits(FPLiteral::Two, 64),
            APInt(64, UINT64_C(0x4000000000000000)));
  EXPECT_EQ(getFPLiteralBits(FPLiteral::Half, 64),
            APInt(64, UINT64_C(0x3FE0000000000000)));
}

TEST(GISynthPredicates, ExactInverse) {
  auto Bits = [](float F) { return APFloat(F).bitcastToAPInt(); };
  EXPECT_TRUE(hasExactInverse(Bits(2.0f)));
  EXPECT_TRUE(hasExactInverse(Bits(-0.125f)));
  EXPECT_TRUE(hasExactInverse(Bits(1.0f)));
  EXPECT_FALSE(hasExactInverse(Bits(3.0f)));
  EXPECT_FALSE(hasExactInverse(Bits(0.0f)));
  EXPECT_FALSE(
      hasExactInverse(APFloat::getInf(APFloat::IEEEsingle()).bitcastToAPInt()));
  EXPECT_FALSE(
      hasExactInverse(APFloat::getNaN(APFloat::IEEEsingle()).bitcastToAPInt()));
  // 2^-126 is the smallest normal number: its reciprocal 2^126 is a
  // number. The reciprocal of 2^127 is 2^-127, a subnormal number.
  EXPECT_TRUE(hasExactInverse(APInt(32, 0x00800000)));
  EXPECT_FALSE(hasExactInverse(APInt(32, 0x7F000000)));
  // A subnormal number.
  EXPECT_FALSE(hasExactInverse(APInt(32, 0x00400000)));
  // No format of the model.
  EXPECT_FALSE(hasExactInverse(APInt(8, 1)));
}

TEST(GISynthPredicates, ComputedFloatConstants) {
  auto Bits = [](float F) { return APFloat(F).bitcastToAPInt(); };
  EXPECT_EQ(fpNegBits(Bits(1.5f)), Bits(-1.5f));
  EXPECT_EQ(fpNegBits(Bits(-0.0f)), Bits(0.0f));
  // The negation of a NaN changes only its sign.
  EXPECT_EQ(fpNegBits(APInt(32, 0x7FA00001)), APInt(32, 0xFFA00001));
  EXPECT_EQ(fpDivBits(Bits(1.0f), Bits(4.0f)), Bits(0.25f));
  // Rounded to nearest: 1 / 3.
  EXPECT_EQ(fpDivBits(Bits(1.0f), Bits(3.0f)), APInt(32, 0x3EAAAAAB));
  EXPECT_FALSE(isNaNBits(fpDivBits(Bits(1.0f), Bits(0.0f))));
  EXPECT_TRUE(isNaNBits(fpDivBits(Bits(0.0f), Bits(0.0f))));
  EXPECT_TRUE(isNaNBits(APInt(16, 0x7E00)));
  EXPECT_FALSE(isNaNBits(APInt(16, 0x7C00)));
}

TEST_F(AArch64GISelMITest, BuildConstantBits) {
  setUp();
  if (!TM)
    GTEST_SKIP();
  LLT S32 = LLT::scalar(32);
  LLT P0 = LLT::pointer(0, 64);
  auto F = buildConstantBits(B, S32, APInt(32, 0x40000000), /*IsFP=*/true);
  EXPECT_EQ(F->getOpcode(), TargetOpcode::G_FCONSTANT);
  EXPECT_EQ(*getConstantBits(F.getReg(0), *MRI), APInt(32, 0x40000000));
  auto I = buildConstantBits(B, S32, APInt(32, 5), /*IsFP=*/false);
  EXPECT_EQ(I->getOpcode(), TargetOpcode::G_CONSTANT);
  auto P = buildConstantBits(B, P0, APInt(64, 16), /*IsFP=*/false);
  EXPECT_EQ(P->getOpcode(), TargetOpcode::G_CONSTANT);
  EXPECT_TRUE(MRI->getType(P.getReg(0)).isPointer());
  // Each lane of a vector has the constant.
  auto V = buildConstantBits(B, LLT::fixed_vector(2, S32),
                             APInt(32, 0x3F800000), /*IsFP=*/true);
  EXPECT_EQ(V->getOpcode(), TargetOpcode::G_BUILD_VECTOR);
  EXPECT_EQ(*getConstantBits(V.getReg(0), *MRI, /*AllowSplat=*/true),
            APInt(32, 0x3F800000));
}

TEST_F(AArch64GISelMITest, SameFPEnvironment) {
  setUp("  %3:_(s64) = G_STRICT_FADD %0, %1\n"
        "  %4:_(s64) = G_ADD %0, %1\n"
        "  %5:_(s64) = nofpexcept G_STRICT_FMUL %3, %2\n"
        "  %6:_(s32) = G_GET_ROUNDING\n"
        "  %7:_(s64) = G_STRICT_FSUB %5, %2\n"
        "  %8:_(p0) = G_INTTOPTR %0(s64)\n"
        "  G_STORE %7(s64), %8(p0) :: (store (s64))\n"
        "  %9:_(s64) = G_STRICT_FDIV %7, %2\n");
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Add = findOpcode(*MF, TargetOpcode::G_STRICT_FADD);
  MachineInstr *Mul = findOpcode(*MF, TargetOpcode::G_STRICT_FMUL);
  MachineInstr *Sub = findOpcode(*MF, TargetOpcode::G_STRICT_FSUB);
  MachineInstr *Div = findOpcode(*MF, TargetOpcode::G_STRICT_FDIV);
  EXPECT_TRUE(isConstrainedFPOpcode(TargetOpcode::G_STRICT_FCMPS));
  EXPECT_FALSE(isConstrainedFPOpcode(TargetOpcode::G_FADD));

  // A G_ADD and a constrained operation do not read the environment.
  EXPECT_TRUE(isSameFPEnvironment(*Add, *Mul));
  EXPECT_TRUE(isSameFPEnvironment(*MRI, Add->getOperand(0).getReg(),
                                  Mul->getOperand(0).getReg()));
  // The first instruction is before the second one.
  EXPECT_FALSE(isSameFPEnvironment(*Mul, *Add));
  EXPECT_FALSE(isSameFPEnvironment(*Add, *Add));
  // An instruction that reads the environment is between the two.
  EXPECT_FALSE(isSameFPEnvironment(*Mul, *Sub));
  EXPECT_FALSE(isSameFPEnvironment(*Add, *Sub));
  // A write to memory is between the two.
  EXPECT_FALSE(isSameFPEnvironment(*Sub, *Div));

  EXPECT_TRUE(
      mayAccessFPEnvironment(*findOpcode(*MF, TargetOpcode::G_GET_ROUNDING)));
  EXPECT_TRUE(mayAccessFPEnvironment(*findOpcode(*MF, TargetOpcode::G_STORE)));
  EXPECT_FALSE(mayAccessFPEnvironment(*findOpcode(*MF, TargetOpcode::G_ADD)));
  EXPECT_FALSE(mayAccessFPEnvironment(*Add));
  // A copy of a physical register: a call can be next to it.
  EXPECT_TRUE(mayAccessFPEnvironment(*findOpcode(*MF, TargetOpcode::COPY)));

  EXPECT_FALSE(ignoresFPExceptions(*MRI, Add->getOperand(0).getReg()));
  EXPECT_TRUE(ignoresFPExceptions(*MRI, Mul->getOperand(0).getReg()));
}

TEST_F(AArch64GISelMITest, SameFPEnvironmentOtherBlock) {
  setUp("  %3:_(s64) = G_STRICT_FADD %0, %1\n"
        "  G_BR %bb.2\n"
        "\n"
        "  bb.2:\n"
        "  %4:_(s64) = G_STRICT_FMUL %3, %2\n");
  if (!TM)
    GTEST_SKIP();
  EXPECT_FALSE(
      isSameFPEnvironment(*findOpcode(*MF, TargetOpcode::G_STRICT_FADD),
                          *findOpcode(*MF, TargetOpcode::G_STRICT_FMUL)));
}

TEST_F(AArch64GISelMITest, EraseDeadSourceOp) {
  setUp("  %3:_(s64) = G_STRICT_FADD %0, %1\n"
        "  %4:_(s64) = G_FNEG %3\n"
        "  %5:_(s64) = G_STRICT_FMUL %0, %1\n"
        "  %6:_(s64) = G_STRICT_FSUB %5, %2\n"
        "  %7:_(p0) = G_INTTOPTR %0(s64)\n"
        "  G_STORE %6(s64), %7(p0) :: (store (s64))\n");
  if (!TM)
    GTEST_SKIP();
  auto Dst = [&](unsigned Opc) {
    return findOpcode(*MF, Opc)->getOperand(0).getReg();
  };
  Register Add = Dst(TargetOpcode::G_STRICT_FADD);
  Register Neg = Dst(TargetOpcode::G_FNEG);
  Register Mul = Dst(TargetOpcode::G_STRICT_FMUL);
  Register Sub = Dst(TargetOpcode::G_STRICT_FSUB);
  // A value with a user stays.
  eraseDeadSourceOp(*MRI, Add);
  eraseDeadSourceOp(*MRI, Mul);
  eraseDeadSourceOp(*MRI, Sub);
  EXPECT_TRUE(MRI->getVRegDef(Add) && MRI->getVRegDef(Mul) &&
              MRI->getVRegDef(Sub));
  // From the root down: the G_FNEG has no user, then the constrained
  // operation below it has none. The compiler does not remove the second
  // one (it raises exceptions).
  EXPECT_FALSE(isTriviallyDead(*MRI->getVRegDef(Add), *MRI));
  eraseDeadSourceOp(*MRI, Neg);
  EXPECT_FALSE(MRI->getVRegDef(Neg));
  EXPECT_FALSE(isTriviallyDead(*MRI->getVRegDef(Add), *MRI));
  eraseDeadSourceOp(*MRI, Add);
  EXPECT_FALSE(MRI->getVRegDef(Add));
  EXPECT_TRUE(MRI->getVRegDef(Mul));
}

} // namespace
