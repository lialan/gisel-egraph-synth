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

TEST_F(AArch64GISelMITest, SiblingInsertPointSiblingFirst) {
  setUp(SiblingFirst);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Sub = findOpcode(*MF, TargetOpcode::G_SUB);
  MachineInstr *Add = findOpcode(*MF, TargetOpcode::G_ADD);
  MachineInstr *Select = findOpcode(*MF, TargetOpcode::G_SELECT);
  Register AddReg = Add->getOperand(0).getReg();

  // The sibling stays: the replacement of the root is built before the root.
  EXPECT_EQ(siblingInsertPoint(*Select, *Sub, {Copies[0], Copies[1], AddReg},
                               /*SibStays=*/true, /*Move=*/true),
            Select);
  EXPECT_TRUE(isBefore(*Sub, *Select));
  // The two roots are replaced: before the sibling, which is the first.
  EXPECT_EQ(siblingInsertPoint(*Select, *Sub, {Copies[0], Copies[1]},
                               /*SibStays=*/false),
            Sub);
  // An input of the replacement is defined after the sibling.
  EXPECT_EQ(siblingInsertPoint(*Select, *Sub, {Copies[0], AddReg},
                               /*SibStays=*/false),
            nullptr);
}

TEST_F(AArch64GISelMITest, SiblingInsertPointRootFirst) {
  setUp(RootFirst);
  if (!TM)
    GTEST_SKIP();
  MachineInstr *Sub = findOpcode(*MF, TargetOpcode::G_SUB);
  MachineInstr *Add = findOpcode(*MF, TargetOpcode::G_ADD);
  MachineInstr *Select = findOpcode(*MF, TargetOpcode::G_SELECT);
  Register AddReg = Add->getOperand(0).getReg();

  // The two roots are replaced: before the root, where every input of its
  // tree is defined.
  EXPECT_EQ(siblingInsertPoint(*Select, *Sub, {Copies[0], Copies[1], AddReg},
                               /*SibStays=*/false),
            Select);
  // The sibling stays. The check does not move it.
  EXPECT_EQ(siblingInsertPoint(*Select, *Sub, {}, /*SibStays=*/true), Select);
  EXPECT_TRUE(isBefore(*Select, *Sub));
  // The apply function moves it before the root.
  EXPECT_EQ(siblingInsertPoint(*Select, *Sub, {}, /*SibStays=*/true,
                               /*Move=*/true),
            Select);
  EXPECT_TRUE(isBefore(*Sub, *Select));
  EXPECT_EQ(Sub->getParent(), Select->getParent());
  EXPECT_EQ(std::next(Sub->getIterator()), Select->getIterator());
  EXPECT_TRUE(MF->verify(nullptr, "after the move", &errs(),
                         /*AbortOnError=*/false));
}

TEST_F(AArch64GISelMITest, SiblingInsertPointTooFar) {
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
  EXPECT_EQ(siblingInsertPoint(*Select, *Sub, {}, /*SibStays=*/true), nullptr);
  EXPECT_EQ(siblingInsertPoint(*Select, *Sub, {}, /*SibStays=*/false), nullptr);
}

} // namespace
