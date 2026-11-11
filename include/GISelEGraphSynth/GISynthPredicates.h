//===- llvm/CodeGen/GlobalISel/GISynthPredicates.h --------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// Run-time guards of the combine rules produced by the offline rule
/// synthesizer (llvm/utils/gisel-rule-synth). This header holds the small set
/// of reusable primitives; the per-rule guards are generated into
/// GISynthGeneratedPredicates.inc and only combine these primitives with
/// GISelValueTracking known bits. No solver or search runs at compile time.
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_GLOBALISEL_GISYNTHPREDICATES_H
#define LLVM_CODEGEN_GLOBALISEL_GISYNTHPREDICATES_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/CodeGen/GlobalISel/GISelValueTracking.h"
#include "llvm/CodeGen/GlobalISel/MachineIRBuilder.h"
#include "llvm/CodeGen/GlobalISel/Utils.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/Register.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/KnownBits.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdint>
#include <initializer_list>
#include <optional>

namespace llvm {
namespace gisynth {

/// Writes the scalar bit width of each register to \p W. Fails for vectors,
/// pointers and invalid types: the rules are only proved for scalars. Also
/// fails for a floating-point type that does not have the IEEE format of its
/// width (bfloat): the conversions are proved for the IEEE formats.
inline bool getScalarWidths(const MachineRegisterInfo &MRI,
                            std::initializer_list<Register> Regs, unsigned *W) {
  for (Register R : Regs) {
    LLT Ty = MRI.getType(R);
    if (!Ty.isValid() || !Ty.isScalar())
      return false;
    if (Ty.isFloat() && !Ty.isFloatIEEE())
      return false;
    *W++ = Ty.getSizeInBits();
  }
  return true;
}

/// True if the operand widths \p W equal one of the width schedules the rule
/// was proved for.
template <size_t N, size_t M>
bool isVerifiedSchedule(const unsigned (&W)[N],
                        const uint16_t (&Verified)[M][N]) {
  for (const auto &S : Verified) {
    bool Eq = true;
    for (size_t I = 0; I < N; ++I)
      Eq &= S[I] == W[I];
    if (Eq)
      return true;
  }
  return false;
}

/// Unsigned bounds derived from known bits (the bounds of
/// ConstantRange::fromKnownBits(K, /*IsSigned=*/false)).
inline bool umaxULEUmin(const KnownBits &A, const KnownBits &B) {
  unsigned W = std::max(A.getBitWidth(), B.getBitWidth());
  return A.getMaxValue().zext(W).ule(B.getMinValue().zext(W));
}

inline bool umaxULTUmin(const KnownBits &A, const KnownBits &B) {
  unsigned W = std::max(A.getBitWidth(), B.getBitWidth());
  return A.getMaxValue().zext(W).ult(B.getMinValue().zext(W));
}

inline bool umaxULTWidth(const KnownBits &A, unsigned Width) {
  return A.getMaxValue().ult(Width);
}

/// True if \p Mask has ones in every bit that survives a logical right shift
/// by \p Amt: bits [umin(Amt), width).
inline bool coversHighAfterShift(const APInt &Mask, const KnownBits &Amt) {
  unsigned W = Mask.getBitWidth();
  return Mask.countl_one() >= W - Amt.getMinValue().getLimitedValue(W);
}

/// True if \p Mask has ones in every bit that survives a left shift by
/// \p Amt: bits [0, width - umin(Amt)).
inline bool coversLowAfterShift(const APInt &Mask, const KnownBits &Amt) {
  unsigned W = Mask.getBitWidth();
  return Mask.countr_one() >= W - Amt.getMinValue().getLimitedValue(W);
}

/// A rule for a region with several outputs replaces the root and, with it,
/// values below the root that have other users (\p Outs). The replacement is
/// built before the first of these values, so that it dominates every user.
/// Returns the instruction that defines that first value, or nullptr if the
/// rule cannot apply: a value of \p Outs is not defined before the root in
/// the block of the root (within \p MaxDistance instructions), or an input
/// that the replacement reads (\p Inputs) is defined after that position.
inline MachineInstr *firstRegionOutput(MachineInstr &Root,
                                       std::initializer_list<Register> Outs,
                                       std::initializer_list<Register> Inputs,
                                       unsigned MaxDistance = 64) {
  MachineBasicBlock &MBB = *Root.getParent();
  size_t Found = 0;
  unsigned Distance = 0;
  for (MachineBasicBlock::iterator It = Root.getIterator(), E = MBB.begin();
       It != E && Distance != MaxDistance; ++Distance) {
    --It;
    bool IsOut = false;
    for (const MachineOperand &MO : It->all_defs()) {
      if (is_contained(Outs, MO.getReg()))
        IsOut = true;
      else if (is_contained(Inputs, MO.getReg()))
        return nullptr;
    }
    if (IsOut && ++Found == Outs.size())
      return &*It;
  }
  return nullptr;
}

/// True if \p Reg has exactly \p N uses. Debug uses do not count.
inline bool hasNUses(const MachineRegisterInfo &MRI, Register Reg, unsigned N) {
  return hasNItems(MRI.use_nodbg_begin(Reg), MRI.use_nodbg_end(), N);
}

/// The plan of a rule for a region with several outputs. The match step
/// makes every check and fills the plan. The apply step only executes it.
struct RegionPlan {
  /// The other roots of the region (the siblings), in the order of the rule.
  SmallVector<MachineInstr *, 2> Sibs;
  /// The inputs that only the siblings read, in the order of the rule.
  SmallVector<Register, 2> Extra;
  /// The siblings that stay and that the apply step moves before InsertPt,
  /// in the order of the block.
  SmallVector<MachineInstr *, 2> Move;
  /// The replacement is built before this instruction.
  MachineInstr *InsertPt = nullptr;
};

/// The condition of a rule for a region with several outputs: each value of
/// \p Outs has a user that is not in the matched pattern (else the rule for
/// the root alone applies), and the replacement can be built (see
/// firstRegionOutput). Fills \p Plan.
inline bool isJointRegion(const MachineRegisterInfo &MRI, Register Dst,
                          std::initializer_list<Register> Outs,
                          std::initializer_list<Register> Inputs,
                          RegionPlan &Plan) {
  Plan = RegionPlan();
  for (Register R : Outs)
    if (MRI.hasOneNonDBGUse(R))
      return false;
  MachineInstr *Root = MRI.getVRegDef(Dst);
  if (!Root)
    return false;
  Plan.InsertPt = firstRegionOutput(*Root, Outs, Inputs);
  return Plan.InsertPt != nullptr;
}

/// A rule for a region with several roots matches the tree of one root
/// (\p Root). Another root (a sibling) is an instruction of the block of
/// \p Root that reads \p Anchor and that \p Match accepts. It is not an
/// instruction of the matched tree (the definitions of \p Tree) and not one
/// of \p Others. Returns the first such instruction among the first
/// \p MaxUsers users of \p Anchor, or nullptr.
template <typename MatchFn>
MachineInstr *findSiblingRoot(const MachineRegisterInfo &MRI,
                              MachineInstr &Root, Register Anchor,
                              MatchFn Match, unsigned MaxUsers = 8,
                              ArrayRef<Register> Tree = {},
                              ArrayRef<MachineInstr *> Others = {}) {
  unsigned NumUsers = 0;
  for (MachineInstr &UseMI : MRI.use_nodbg_instructions(Anchor)) {
    if (++NumUsers > MaxUsers)
      return nullptr;
    if (&UseMI == &Root || UseMI.getParent() != Root.getParent() ||
        is_contained(Others, &UseMI) ||
        any_of(Tree, [&](Register R) { return MRI.getVRegDef(R) == &UseMI; }))
      continue;
    if (Match(UseMI))
      return &UseMI;
  }
  return nullptr;
}

/// Fills the position part of \p Plan for the root \p Root and the siblings
/// Plan.Sibs. Returns false if the rule cannot apply.
///
/// Bit J of \p Stays: the sibling J stays, and a replacement reads its
/// results. Else the rule replaces it. \p Inputs has each register that a
/// new instruction or a sibling that stays reads, but not the results of
/// the siblings that stay.
///
/// The replacement is built before the first instruction that the rule
/// replaces (the root, or a sibling before it), so that it dominates the
/// users of every replaced value. Each register of \p Inputs must be
/// defined before that position. A sibling that stays and that is after
/// that position is moved before it. The root and the siblings are not
/// more than \p MaxDistance instructions apart.
inline bool planRegion(MachineInstr &Root, RegionPlan &Plan, unsigned Stays,
                       std::initializer_list<Register> Inputs,
                       unsigned MaxDistance = 64) {
  MachineBasicBlock &MBB = *Root.getParent();
  const unsigned NumSibs = Plan.Sibs.size();
  auto DefinesInput = [&](const MachineInstr &MI) {
    return any_of(MI.all_defs(), [&](const MachineOperand &MO) {
      return is_contained(Inputs, MO.getReg());
    });
  };
  // An input that the root or a sibling that the rule replaces defines:
  // the replacement would read a value that it replaces.
  if (DefinesInput(Root))
    return false;
  // The position of each sibling: its distance before the root, or the
  // negative of its distance after the root.
  SmallVector<int, 2> Pos(NumSibs, 0);
  unsigned Found = 0;
  // The distance of the nearest definition of an input before the root.
  unsigned NearestInput = 0;
  unsigned Distance = 0;
  for (MachineBasicBlock::iterator It = Root.getIterator(), E = MBB.begin();
       It != E && Distance != MaxDistance && Found != NumSibs;) {
    --It;
    ++Distance;
    for (unsigned J = 0; J != NumSibs; ++J) {
      if (Plan.Sibs[J] == &*It) {
        Pos[J] = Distance;
        ++Found;
      }
    }
    if (!NearestInput && DefinesInput(*It))
      NearestInput = Distance;
  }
  Distance = 0;
  for (MachineBasicBlock::iterator It = std::next(Root.getIterator()),
                                   E = MBB.end();
       It != E && Distance != MaxDistance && Found != NumSibs; ++It) {
    ++Distance;
    // An input that is defined after the root: no instruction before the
    // root can read it.
    if (DefinesInput(*It))
      return false;
    for (unsigned J = 0; J != NumSibs; ++J) {
      if (Plan.Sibs[J] == &*It) {
        Pos[J] = -int(Distance);
        ++Found;
      }
    }
  }
  if (Found != NumSibs)
    return false;
  // The first instruction that the rule replaces.
  int First = 0;
  Plan.InsertPt = &Root;
  for (unsigned J = 0; J != NumSibs; ++J) {
    if (!((Stays >> J) & 1) && Pos[J] > First) {
      First = Pos[J];
      Plan.InsertPt = Plan.Sibs[J];
    }
  }
  if (NearestInput && int(NearestInput) <= First)
    return false;
  // The siblings that stay and that are after that position, in the order
  // of the block.
  SmallVector<unsigned, 2> Late;
  for (unsigned J = 0; J != NumSibs; ++J)
    if (((Stays >> J) & 1) && Pos[J] < First)
      Late.push_back(J);
  llvm::sort(Late, [&](unsigned A, unsigned B) { return Pos[A] > Pos[B]; });
  Plan.Move.clear();
  for (unsigned J : Late)
    Plan.Move.push_back(Plan.Sibs[J]);
  return true;
}

/// Executes the position part of \p Plan: moves the siblings that stay
/// before the position of the replacement. Their operands are defined
/// before it (planRegion). Returns the instruction before which the
/// replacement is built.
inline MachineInstr &applyRegionPlan(const RegionPlan &Plan) {
  MachineBasicBlock &MBB = *Plan.InsertPt->getParent();
  for (MachineInstr *MI : Plan.Move)
    MBB.splice(Plan.InsertPt->getIterator(), &MBB, MI->getIterator());
  return *Plan.InsertPt;
}

/// Gives each result of \p MI a new register. The apply step of a rule for
/// a region calls this for each instruction that it replaces, before it
/// builds the replacement: a new instruction can then define an old
/// register, and a later new instruction can read it, while that register
/// has one definition. The apply step erases \p MI after that.
inline void releaseResults(MachineRegisterInfo &MRI, MachineInstr &MI) {
  for (MachineOperand &MO : MI.all_defs())
    MO.setReg(MRI.cloneVirtualRegister(MO.getReg()));
}

#include "llvm/CodeGen/GlobalISel/GISynthGeneratedPredicates.inc"

} // end namespace gisynth
} // end namespace llvm

#endif // LLVM_CODEGEN_GLOBALISEL_GISYNTHPREDICATES_H
