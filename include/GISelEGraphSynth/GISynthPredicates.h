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

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/FloatingPointMode.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/CodeGen/GlobalISel/GISelValueTracking.h"
#include "llvm/CodeGen/GlobalISel/GenericMachineInstrs.h"
#include "llvm/CodeGen/GlobalISel/MachineIRBuilder.h"
#include "llvm/CodeGen/GlobalISel/Utils.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/Register.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Intrinsics.h"
// The intrinsics of the generated rules of a target.
#include "llvm/IR/IntrinsicsAMDGPU.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/KnownBits.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdint>
#include <initializer_list>
#include <optional>

namespace llvm {
namespace gisynth {

/// The largest number of lanes of a vector that a rule can have.
constexpr unsigned MaxVectorLanes = 16;

/// Writes the type code of each register to \p W: the bit width of a scalar
/// or of a pointer, and (lanes << 16) | element width for a fixed vector.
/// Fails for scalable vectors, for vectors with more than MaxVectorLanes
/// lanes and for invalid types. Also fails for a floating-point type that
/// does not have the IEEE format of its width (bfloat): the conversions are
/// proved for the IEEE formats.
///
/// The bit I of \p Pointers says that the register I is a pointer (or a
/// vector of pointers) in the rule; every other register must be a scalar or
/// a vector of scalars. A pointer is its bits in a proof, so its address
/// space must be integral and its offsets must have the width of the pointer
/// (G_PTR_ADD is then the addition of the bits). The pointers of one width
/// must have one type: a new pointer of a replacement takes its type from one
/// of them.
///
/// With \p Lift, the rule has only operators that compute each lane of a
/// vector from the same lane of their operands. Such a rule that is proved
/// for scalars holds for each lane of vectors: if every register is a fixed
/// vector and all have the same number of lanes, \p W gets the element
/// widths.
inline bool getScalarWidths(const MachineRegisterInfo &MRI,
                            std::initializer_list<Register> Regs, unsigned *W,
                            uint64_t Pointers = 0, bool Lift = false) {
  SmallVector<LLT, 4> PtrTys;
  unsigned Idx = 0;
  unsigned *Begin = W;
  unsigned CommonLanes = 0;
  bool SameLanes = true;
  for (Register R : Regs) {
    LLT Ty = MRI.getType(R);
    if (!Ty.isValid())
      return false;
    unsigned Lanes = 0;
    if (Ty.isVector()) {
      if (Ty.isScalable() || Ty.getNumElements() > MaxVectorLanes)
        return false;
      Lanes = Ty.getNumElements();
      Ty = Ty.getElementType();
    }
    if (Idx == 0)
      CommonLanes = Lanes;
    SameLanes &= Lanes == CommonLanes;
    if ((Pointers >> Idx++) & 1) {
      const MachineInstr *Def = MRI.getVRegDef(R);
      if (!Ty.isPointer() || !Def)
        return false;
      const DataLayout &DL = Def->getMF()->getDataLayout();
      unsigned AS = Ty.getAddressSpace();
      if (DL.isNonIntegralAddressSpace(AS) ||
          DL.getIndexSizeInBits(AS) != Ty.getSizeInBits())
        return false;
      for (LLT Seen : PtrTys)
        if (Seen.getSizeInBits() == Ty.getSizeInBits() && Seen != Ty)
          return false;
      PtrTys.push_back(Ty);
    } else {
      if (!Ty.isScalar())
        return false;
      if (Ty.isFloat() && !Ty.isFloatIEEE())
        return false;
    }
    *W++ = (Lanes << 16) | Ty.getSizeInBits();
  }
  if (Lift && CommonLanes && SameLanes)
    for (unsigned *I = Begin; I != W; ++I)
      *I &= 0xffff;
  return true;
}

/// The value of the constant \p R: a G_CONSTANT, or a G_BUILD_VECTOR whose
/// operands are all the same G_CONSTANT (the value of each lane).
inline std::optional<APInt> getConstantOrSplat(Register R,
                                               const MachineRegisterInfo &MRI) {
  if (MRI.getType(R).isVector())
    return getIConstantSplatVal(R, MRI);
  return getIConstantVRegVal(R, MRI);
}

/// True if \p MI is a call of the intrinsic \p ID that a rule can replace: a
/// G_INTRINSIC has no side effect and is not convergent.
inline bool isIntrinsic(const MachineInstr &MI, Intrinsic::ID ID) {
  return MI.getOpcode() == TargetOpcode::G_INTRINSIC &&
         cast<GIntrinsic>(MI).is(ID);
}

/// True if \p MO is the mask \p Mask of a G_SHUFFLE_VECTOR.
inline bool isShuffleMask(const MachineOperand &MO, ArrayRef<int> Mask) {
  return MO.isShuffleMask() && MO.getShuffleMask() == Mask;
}

/// True if \p R is the integer constant \p Value (an index of a lane).
inline bool isConstantIndex(Register R, const MachineRegisterInfo &MRI,
                            uint64_t Value) {
  std::optional<APInt> C = getIConstantVRegVal(R, MRI);
  return C && C->getActiveBits() <= 64 && C->getZExtValue() == Value;
}

/// True if the function has the IEEE treatment of subnormal numbers
/// (DenormalMode) for the floating-point format of the width of each register
/// of \p Regs. A rule with a floating-point operation on the value of a number
/// is proved for this treatment: with another mode, an operation takes a
/// subnormal operand as zero or can give zero for a subnormal result. A
/// register can be an integer; the check is then stricter than necessary.
inline bool hasIEEEDenormalMode(const MachineRegisterInfo &MRI,
                                std::initializer_list<Register> Regs) {
  for (Register R : Regs) {
    const fltSemantics *Sem;
    switch (MRI.getType(R).getScalarSizeInBits()) {
    case 16:
      Sem = &APFloat::IEEEhalf();
      break;
    case 32:
      Sem = &APFloat::IEEEsingle();
      break;
    case 64:
      Sem = &APFloat::IEEEdouble();
      break;
    default:
      continue;
    }
    const MachineInstr *Def = MRI.getVRegDef(R);
    if (!Def || Def->getMF()->getDenormalMode(*Sem) != DenormalMode::getIEEE())
      return false;
  }
  return true;
}

/// True if the type codes \p W (getScalarWidths) equal one of the schedules the
/// rule was proved for.
template <typename T, size_t N, size_t M>
bool isVerifiedSchedule(const unsigned (&W)[N], const T (&Verified)[M][N]) {
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

/// The largest number of incoming values of a G_PHI of a rule.
constexpr unsigned MaxPhiInputs = 4;

/// True if \p Phi is a G_PHI whose incoming values a rule can read at the
/// position of an instruction that the G_PHI dominates. The synthesizer
/// proves a rule for each edge into the block of the G_PHI, and it takes an
/// incoming value and each other occurrence of the same register in the rule
/// as one value. That is correct if the definition of each incoming value is
/// in a block that properly dominates the block of the G_PHI: the definition
/// then does not execute again between the G_PHI and an instruction that the
/// G_PHI dominates, and it dominates that instruction. (A value that a loop
/// computes again is the value of an earlier iteration in the G_PHI.)
///
/// \p Dominates(Def, Use) says if the instruction Def dominates the
/// instruction Use; an answer that is always false is correct
/// (CombinerHelper::dominates without a dominator tree).
template <typename DominatesFn>
bool hasStablePhiInputs(const MachineRegisterInfo &MRI, const MachineInstr &Phi,
                        DominatesFn Dominates) {
  if (Phi.getOpcode() != TargetOpcode::G_PHI)
    return false;
  unsigned NumInputs = (Phi.getNumOperands() - 1) / 2;
  if (NumInputs == 0 || NumInputs > MaxPhiInputs)
    return false;
  for (unsigned I = 1, E = Phi.getNumOperands(); I < E; I += 2) {
    const MachineOperand &MO = Phi.getOperand(I);
    if (!MO.isReg() || !MO.getReg().isVirtual())
      return false;
    const MachineInstr *Def = MRI.getVRegDef(MO.getReg());
    if (!Def || Def->getParent() == Phi.getParent() || !Dominates(*Def, Phi))
      return false;
  }
  return true;
}

/// hasStablePhiInputs for the G_PHI that defines \p Phi, with the dominance
/// query of \p Helper (a CombinerHelper).
template <typename HelperT>
bool isStablePhi(const MachineRegisterInfo &MRI, const HelperT &Helper,
                 Register Phi) {
  const MachineInstr *Def = MRI.getVRegDef(Phi);
  return Def && hasStablePhiInputs(
                    MRI, *Def,
                    [&](const MachineInstr &DefMI, const MachineInstr &UseMI) {
                      return Helper.dominates(DefMI, UseMI);
                    });
}

/// The largest number of instructions between a load and the G_STORE whose
/// value a rule takes for the load.
constexpr unsigned MaxForwardDistance = 32;

/// True if \p MI can change the content of memory, or if what it does is
/// not known. The synthesizer has no list of the opcodes that write memory:
/// each store, atomic operation, memory intrinsic, call and instruction
/// with other effects has one of these properties.
inline bool mayWriteMemory(const MachineInstr &MI) {
  return MI.mayStore() || MI.isCall() || MI.hasUnmodeledSideEffects() ||
         MI.isInlineAsm();
}

/// The number of bits that the load or store \p MI reads or writes, or 0
/// if the number is not fixed.
inline unsigned getFixedMemBits(const GMemOperation &MI) {
  LocationSize Size = MI.getMemSizeInBits();
  if (!Size.hasValue() || Size.isScalable())
    return 0;
  return Size.getValue().getFixedValue();
}

/// The value operand of the G_STORE whose bits the load that defines
/// \p LoadDst reads, or no register. The load is a G_LOAD, G_ZEXTLOAD or
/// G_SEXTLOAD of \p MemBits bits. The G_STORE is the nearest instruction
/// before the load, in the block of the load, that can write memory
/// (mayWriteMemory); it writes \p MemBits bits through the pointer
/// register of the load, so the memory that the load reads has the low
/// \p MemBits bits of the value. The two instructions are not volatile and
/// not atomic. (A load that races with a write of another thread has an
/// undefined result, so each value is a correct result for it.)
///
/// The result of the load and the value are integers (the value has at
/// least \p MemBits bits; the result of a G_LOAD has \p MemBits bits and
/// the result of an extending load has more), or the load is a G_LOAD and
/// they have the same floating-point type or the same pointer type. The
/// lanes of a vector in memory have no model.
inline Register getForwardedStoreValue(const MachineRegisterInfo &MRI,
                                       Register LoadDst, unsigned MemBits) {
  const auto *Load = dyn_cast_or_null<GAnyLoad>(MRI.getVRegDef(LoadDst));
  if (!Load || isa<GFPExtLoad>(Load) || !Load->isSimple() || MemBits == 0 ||
      getFixedMemBits(*Load) != MemBits)
    return Register();
  LLT DstTy = MRI.getType(LoadDst);
  bool IsExt = Load->getOpcode() != TargetOpcode::G_LOAD;
  if (!DstTy.isValid() || DstTy.isVector() ||
      (IsExt ? DstTy.getSizeInBits() <= MemBits
             : DstTy.getSizeInBits() != MemBits))
    return Register();
  const MachineBasicBlock &MBB = *Load->getParent();
  unsigned Distance = 0;
  for (MachineBasicBlock::const_iterator I = Load->getIterator(),
                                         B = MBB.begin();
       I != B;) {
    --I;
    if (++Distance > MaxForwardDistance)
      return Register();
    if (!mayWriteMemory(*I))
      continue;
    // The nearest instruction that writes memory.
    const auto *Store = dyn_cast<GStore>(&*I);
    if (!Store || !Store->isSimple() ||
        Store->getPointerReg() != Load->getPointerReg() ||
        getFixedMemBits(*Store) != MemBits)
      return Register();
    Register Value = Store->getValueReg();
    LLT Ty = MRI.getType(Value);
    if (!Value.isVirtual() || !Ty.isValid() || Ty.isVector() ||
        Ty.getSizeInBits() < MemBits)
      return Register();
    auto IsInteger = [](LLT T) { return T.isScalar() && !T.isFloat(); };
    if (!IsInteger(DstTy) || !IsInteger(Ty)) {
      // The same value, not the bits of a value of another type.
      if (IsExt || DstTy != Ty)
        return Register();
    }
    return Value;
  }
  return Register();
}

/// True if the definition of \p Reg is a G_ZEXTLOAD (or, with \p Signed, a
/// G_SEXTLOAD) of \p MemBits bits: the value is the zero (sign) extension
/// of its low \p MemBits bits. A rule matches such a load in the place of
/// a G_ASSERT_ZEXT (G_ASSERT_SEXT) of its result.
inline bool isExtLoadOf(const MachineRegisterInfo &MRI, Register Reg,
                        bool Signed, unsigned MemBits) {
  const MachineInstr *Def = MRI.getVRegDef(Reg);
  unsigned Opc = Signed ? TargetOpcode::G_SEXTLOAD : TargetOpcode::G_ZEXTLOAD;
  LLT Ty = MRI.getType(Reg);
  return Def && Def->getOpcode() == Opc && Ty.isScalar() && MemBits != 0 &&
         MemBits < Ty.getSizeInBits() &&
         getFixedMemBits(cast<GMemOperation>(*Def)) == MemBits;
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

/// Removes the flags of \p MI that the proof of a rule does not have: the
/// flags that make poison (nsw, exact, nnan, inbounds) and the fast-math flags
/// that permit other results. A rule is proved for a source without flags.
/// That covers a source with flags if the replacement only reads the inputs
/// of the source. A replacement that reads the value of an instruction of the
/// source needs that instruction, and the instructions of the source that it
/// reads, without flags.
inline void dropFlags(MachineIRBuilder &B, MachineInstr &MI) {
  constexpr uint32_t Flags =
      MachineInstr::NoUWrap | MachineInstr::NoSWrap | MachineInstr::NoUSWrap |
      MachineInstr::IsExact | MachineInstr::Disjoint | MachineInstr::NonNeg |
      MachineInstr::SameSign | MachineInstr::InBounds | MachineInstr::FmNoNans |
      MachineInstr::FmNoInfs | MachineInstr::FmNsz | MachineInstr::FmArcp |
      MachineInstr::FmContract | MachineInstr::FmAfn | MachineInstr::FmReassoc;
  if (!(MI.getFlags() & Flags))
    return;
  // The flags are a part of the identity of an instruction for CSE.
  GISelChangeObserver *Observer = B.getObserver();
  if (Observer)
    Observer->changingInstr(MI);
  MI.clearFlags(Flags);
  if (Observer)
    Observer->changedInstr(MI);
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

//===--- Constants ------------------------------------------------------===//

/// True if \p Reg is the address of an object of the function or of the
/// module (G_GLOBAL_VALUE, G_FRAME_INDEX, ...): a constant of the function
/// whose bits the compiler does not know. It is neither undef nor poison.
inline bool isAddressConstant(Register Reg, const MachineRegisterInfo &MRI) {
  const MachineInstr *Def = Reg.isVirtual() ? MRI.getVRegDef(Reg) : nullptr;
  if (!Def)
    return false;
  switch (Def->getOpcode()) {
  case TargetOpcode::G_GLOBAL_VALUE:
  case TargetOpcode::G_PTRAUTH_GLOBAL_VALUE:
  case TargetOpcode::G_FRAME_INDEX:
  case TargetOpcode::G_CONSTANT_POOL:
  case TargetOpcode::G_BLOCK_ADDR:
  case TargetOpcode::G_JUMP_TABLE:
    return true;
  default:
    return false;
  }
}

/// True if the value of \p Reg is neither undef nor poison: the fact of the
/// compiler, and also each address constant.
inline bool isDefinedValue(Register Reg, const MachineRegisterInfo &MRI) {
  return isAddressConstant(Reg, MRI) ||
         isGuaranteedNotToBeUndefOrPoison(Reg, MRI);
}

/// The bits of the constant that defines \p Reg: a G_CONSTANT (an integer or
/// a pointer), a G_FCONSTANT (its bit pattern), or, with \p AllowSplat, a
/// G_BUILD_VECTOR with one such constant in each lane. A rule reads each
/// constant of its source with this function, and the extractor writes the
/// same values.
inline std::optional<APInt> getConstantBits(Register Reg,
                                            const MachineRegisterInfo &MRI,
                                            bool AllowSplat = false) {
  LLT Ty = MRI.getType(Reg);
  if (!Ty.isValid())
    return std::nullopt;
  if (Ty.isVector()) {
    if (!AllowSplat || Ty.getElementType().isPointer())
      return std::nullopt;
    if (std::optional<APInt> C = getIConstantSplatVal(Reg, MRI))
      return C;
    if (std::optional<FPValueAndVReg> FC =
            getFConstantSplat(Reg, MRI, /*AllowUndef=*/false))
      return FC->Value.bitcastToAPInt();
    return std::nullopt;
  }
  if (std::optional<APInt> C = getIConstantVRegVal(Reg, MRI))
    return C;
  const MachineInstr *Def = MRI.getVRegDef(Reg);
  if (Def && Def->getOpcode() == TargetOpcode::G_FCONSTANT)
    return Def->getOperand(1).getFPImm()->getValueAPF().bitcastToAPInt();
  return std::nullopt;
}

/// The floating-point constants that a rule names: a rule with the literal
/// has the constant in each format.
enum class FPLiteral { Zero, NegZero, One, NegOne, Two, Half };

/// The bit pattern of \p Lit in the format with \p Bits bits (16, 32 or 64).
inline APInt getFPLiteralBits(FPLiteral Lit, unsigned Bits) {
  const fltSemantics &Sem = Bits == 16   ? APFloat::IEEEhalf()
                            : Bits == 32 ? APFloat::IEEEsingle()
                                         : APFloat::IEEEdouble();
  assert((Bits == 16 || Bits == 32 || Bits == 64) && "no format of the model");
  APFloat F = APFloat::getZero(Sem);
  switch (Lit) {
  case FPLiteral::Zero:
    break;
  case FPLiteral::NegZero:
    F = APFloat::getZero(Sem, /*Negative=*/true);
    break;
  case FPLiteral::One:
    F = APFloat::getOne(Sem);
    break;
  case FPLiteral::NegOne:
    F = APFloat::getOne(Sem, /*Negative=*/true);
    break;
  case FPLiteral::Two:
    F = scalbn(APFloat::getOne(Sem), 1, APFloat::rmNearestTiesToEven);
    break;
  case FPLiteral::Half:
    F = scalbn(APFloat::getOne(Sem), -1, APFloat::rmNearestTiesToEven);
    break;
  }
  return F.bitcastToAPInt();
}

/// True if \p Bits is the bit pattern of a power of 2 whose reciprocal is a
/// normal number of the format: a division by the value is the
/// multiplication by the reciprocal, with the same result for each operand
/// and in each rounding mode.
inline bool hasExactInverse(const APInt &Bits) {
  unsigned W = Bits.getBitWidth();
  if (W != 16 && W != 32 && W != 64)
    return false;
  const fltSemantics &Sem = W == 16   ? APFloat::IEEEhalf()
                            : W == 32 ? APFloat::IEEEsingle()
                                      : APFloat::IEEEdouble();
  APFloat F(Sem, Bits);
  APFloat Inv(Sem);
  return F.isFiniteNonZero() && !F.isDenormal() && F.getExactInverse(&Inv) &&
         !Inv.isDenormal();
}

/// The IEEE format with \p Bits bits (16, 32 or 64): the formats of the
/// model.
inline const fltSemantics &getIEEEFormat(unsigned Bits) {
  assert((Bits == 16 || Bits == 32 || Bits == 64) && "no format of the model");
  return Bits == 16   ? APFloat::IEEEhalf()
         : Bits == 32 ? APFloat::IEEEsingle()
                      : APFloat::IEEEdouble();
}

/// Builds the constant with the bit pattern \p Bits into \p Res (a type or
/// a register): a G_FCONSTANT if \p IsFP, else a G_CONSTANT (an integer or
/// a pointer). The builder makes a G_BUILD_VECTOR for a vector type.
inline MachineInstrBuilder buildConstantBits(MachineIRBuilder &B,
                                             const DstOp &Res,
                                             const APInt &Bits, bool IsFP) {
  assert(Res.getLLTTy(*B.getMRI()).getScalarSizeInBits() ==
             Bits.getBitWidth() &&
         "wrong width");
  if (IsFP)
    return B.buildFConstant(Res,
                            APFloat(getIEEEFormat(Bits.getBitWidth()), Bits));
  return B.buildConstant(Res, Bits);
}

/// The known bits of \p Reg. The value tracking has no known bits for a
/// G_FCONSTANT; each bit of a constant is known (getConstantBits).
inline KnownBits getKnownBitsOrConstant(GISelValueTracking &VT,
                                        const MachineRegisterInfo &MRI,
                                        Register Reg) {
  if (std::optional<APInt> C = getConstantBits(Reg, MRI, /*AllowSplat=*/true))
    return KnownBits::makeConstant(*C);
  return VT.getKnownBits(Reg);
}

/// The bit pattern of the negation of the floating-point value \p A.
inline APInt fpNegBits(const APInt &A) {
  APInt R = A;
  R.flipBit(A.getBitWidth() - 1);
  return R;
}

/// The bit pattern of \p A / \p B, rounded to nearest (ties to even): a
/// constant that a rule computes. The bits of a NaN result are not
/// specified, so a rule checks isNaNBits before it uses the result.
inline APInt fpDivBits(const APInt &A, const APInt &B) {
  const fltSemantics &Sem = getIEEEFormat(A.getBitWidth());
  APFloat F(Sem, A);
  F.divide(APFloat(Sem, B), APFloat::rmNearestTiesToEven);
  return F.bitcastToAPInt();
}

/// True if \p A is the bit pattern of a NaN.
inline bool isNaNBits(const APInt &A) {
  return APFloat(getIEEEFormat(A.getBitWidth()), A).isNaN();
}

//===--- The floating-point environment ---------------------------------===//

/// The largest number of instructions between a constrained operation of a
/// source and the root of its rule (isSameFPEnvironment).
constexpr unsigned MaxFPEnvDistance = 64;

/// True if \p Opc is a constrained floating-point operation: it rounds in
/// the mode of the floating-point environment and raises exceptions. It
/// does not change the mode and does not read the exception flags.
inline bool isConstrainedFPOpcode(unsigned Opc) {
  switch (Opc) {
  case TargetOpcode::G_STRICT_FADD:
  case TargetOpcode::G_STRICT_FSUB:
  case TargetOpcode::G_STRICT_FMUL:
  case TargetOpcode::G_STRICT_FDIV:
  case TargetOpcode::G_STRICT_FREM:
  case TargetOpcode::G_STRICT_FMA:
  case TargetOpcode::G_STRICT_FSQRT:
  case TargetOpcode::G_STRICT_FLDEXP:
  case TargetOpcode::G_STRICT_FCMP:
  case TargetOpcode::G_STRICT_FCMPS:
    return true;
  default:
    return false;
  }
}

/// True if \p MI can read or write the floating-point environment, or has
/// an effect that a trap of a floating-point exception must stay before or
/// after: a call, an instruction with a side effect (the instructions that
/// read or set the rounding mode and the exception flags are such), a write
/// to memory, inline assembly, an instruction of the target and a copy of a
/// physical register. A constrained operation is not such an instruction.
inline bool mayAccessFPEnvironment(const MachineInstr &MI) {
  if (MI.isDebugInstr() || isConstrainedFPOpcode(MI.getOpcode()))
    return false;
  if (MI.isCall() || MI.isInlineAsm() || MI.mayStore() ||
      MI.hasUnmodeledSideEffects())
    return true;
  if (isPreISelGenericOpcode(MI.getOpcode()))
    return false;
  if (!MI.isCopy())
    return true;
  return any_of(MI.operands(), [](const MachineOperand &MO) {
    return MO.isReg() && MO.getReg().isPhysical();
  });
}

/// True if \p Def is before \p Use in the block of \p Use, at most
/// MaxFPEnvDistance instructions before it, and no instruction between them
/// is one of mayAccessFPEnvironment. The two instructions then have the same
/// rounding mode, the program reads the exception flags of \p Def only
/// after \p Use, and an instruction at the position of \p Use can raise the
/// exceptions of \p Def in its place.
inline bool isSameFPEnvironment(const MachineInstr &Def,
                                const MachineInstr &Use) {
  if (Def.getParent() != Use.getParent() || &Def == &Use)
    return false;
  const MachineBasicBlock &MBB = *Use.getParent();
  unsigned Distance = 0;
  for (MachineBasicBlock::const_iterator I = Use.getIterator(), B = MBB.begin();
       I != B;) {
    --I;
    if (&*I == &Def)
      return true;
    if (++Distance > MaxFPEnvDistance || mayAccessFPEnvironment(*I))
      return false;
  }
  return false;
}

/// isSameFPEnvironment for the definitions of two registers.
inline bool isSameFPEnvironment(const MachineRegisterInfo &MRI, Register Def,
                                Register Use) {
  const MachineInstr *D = MRI.getVRegDef(Def);
  const MachineInstr *U = MRI.getVRegDef(Use);
  return D && U && isSameFPEnvironment(*D, *U);
}

/// True if the constrained operation that defines \p Reg has the flag
/// nofpexcept: the program does not read the exceptions that it raises.
inline bool ignoresFPExceptions(const MachineRegisterInfo &MRI, Register Reg) {
  const MachineInstr *Def = MRI.getVRegDef(Reg);
  return Def && Def->getFlag(MachineInstr::NoFPExcept);
}

/// Erases the instruction of a source that defines \p Reg if no instruction
/// reads a result of it. A constrained operation without the flag nofpexcept
/// is never dead for the compiler (it raises exceptions); the apply step of
/// a rule calls this for each value below its root, from the root down,
/// after it erased the root: the replacement raises the exceptions of the
/// constrained operations of the source.
inline void eraseDeadSourceOp(MachineRegisterInfo &MRI, Register Reg) {
  MachineInstr *Def = MRI.getVRegDef(Reg);
  if (!Def)
    return;
  if (!isConstrainedFPOpcode(Def->getOpcode())) {
    if (isTriviallyDead(*Def, MRI))
      Def->eraseFromParent();
    return;
  }
  for (const MachineOperand &MO : Def->all_defs())
    if (!MRI.use_nodbg_empty(MO.getReg()))
      return;
  Def->eraseFromParent();
}

#include "llvm/CodeGen/GlobalISel/GISynthGeneratedPredicates.inc"

} // end namespace gisynth
} // end namespace llvm

#endif // LLVM_CODEGEN_GLOBALISEL_GISYNTHPREDICATES_H
