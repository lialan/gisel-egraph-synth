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

/// The condition of a rule for a region with several outputs: each value of
/// \p Outs has a user that is not in the matched pattern (else the rule for
/// the root alone applies), and the replacement can be built (see
/// firstRegionOutput).
inline bool isJointRegion(const MachineRegisterInfo &MRI, Register Dst,
                          std::initializer_list<Register> Outs,
                          std::initializer_list<Register> Inputs) {
  for (Register R : Outs)
    if (MRI.hasOneNonDBGUse(R))
      return false;
  MachineInstr *Root = MRI.getVRegDef(Dst);
  return Root && firstRegionOutput(*Root, Outs, Inputs);
}

/// A rule for a region with two roots matches the tree of one root
/// (\p Root). The other root (the sibling) is an instruction of the block
/// of \p Root that reads \p Anchor and that \p Match accepts. Returns the
/// first such instruction among the first \p MaxUsers users of \p Anchor,
/// or nullptr.
template <typename MatchFn>
MachineInstr *findSiblingRoot(const MachineRegisterInfo &MRI,
                              MachineInstr &Root, Register Anchor,
                              MatchFn Match, unsigned MaxUsers = 8) {
  unsigned NumUsers = 0;
  for (MachineInstr &UseMI : MRI.use_nodbg_instructions(Anchor)) {
    if (++NumUsers > MaxUsers)
      return nullptr;
    if (&UseMI != &Root && UseMI.getParent() == Root.getParent() &&
        Match(UseMI))
      return &UseMI;
  }
  return nullptr;
}

/// Returns the instruction before which the replacement of a region with
/// the roots \p Root and \p Sib is built, or nullptr if the rule cannot
/// apply: the two roots are not near in one block (see firstRegionOutput).
///
/// \p SibStays: the replacement of \p Root reads the results of \p Sib. It
/// is built before \p Root, so \p Sib must be before \p Root. If it is
/// not, \p Move moves it there; its operands are inputs of the tree of
/// \p Root, which are defined before \p Root.
///
/// Else the rule replaces the two roots. The replacement is built before
/// the first of them, and each input that it reads (\p Inputs) must be
/// defined before that position.
inline MachineInstr *siblingInsertPoint(MachineInstr &Root, MachineInstr &Sib,
                                        std::initializer_list<Register> Inputs,
                                        bool SibStays, bool Move = false) {
  Register SibDef = Sib.getOperand(0).getReg();
  // The sibling is before the root.
  if (SibStays ? firstRegionOutput(Root, {SibDef}, {})
               : firstRegionOutput(Root, {SibDef}, Inputs))
    return SibStays ? &Root : &Sib;
  // The root is before the sibling: the inputs are defined before it.
  if (!firstRegionOutput(Sib, {Root.getOperand(0).getReg()}, {}))
    return nullptr;
  if (SibStays && Move)
    Root.getParent()->splice(Root.getIterator(), Sib.getParent(),
                             Sib.getIterator());
  return &Root;
}

#include "llvm/CodeGen/GlobalISel/GISynthGeneratedPredicates.inc"

} // end namespace gisynth
} // end namespace llvm

#endif // LLVM_CODEGEN_GLOBALISEL_GISYNTHPREDICATES_H
