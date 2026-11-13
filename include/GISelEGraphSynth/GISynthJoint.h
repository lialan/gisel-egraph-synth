//===- GISelEGraphSynth/GISynthJoint.h --------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// Run-time part of the joint region rules of tools/gisel-rule-synth
/// (girs/joint.py). A joint rule replaces several outputs of a region of one
/// basic block at once, and can keep (reuse) instructions of the region.
///
/// The rule is an ordinary single-root GICombineRule: TableGen matches the
/// opcode of one instruction of the region (the anchor), and the C++ matcher
/// of this header finds the other instructions of the region. The generated
/// code (GISynthJointRules.inc) only holds a static description of the rule:
///
///   * the source region DAG (Src): one NodeDesc per instruction, with the
///     inputs of the region (values defined outside of it) as Input refs;
///   * the order in which the matcher finds the instructions (Steps): the
///     anchor, the definition of an operand of an instruction found before
///     (DefOf), or a user of a value found before (UserOf, bounded fanout);
///   * the action of each source instruction (Actions): Erase (dies),
///     Replace (an output whose users get a new value; the instruction dies),
///     Keep (stays as it is), Relax (stays, and its poison-generating flags
///     are dropped because a new instruction reads it: the proof is for the
///     instruction without flags);
///   * the new instructions (Tgt), in the order in which they are built, and
///     the new value of each replaced output (Outputs);
///   * the guards: the inputs that must be neither undef nor poison
///     (isStableValue), the inputs that must be distinct registers, and the
///     width maps (one per proof) of the width classes of the rule.
///
/// The matcher makes every check before it fills the plan; it changes
/// nothing. The applier builds the new instructions at the position of the
/// plan, replaces the uses of the outputs and erases the instructions that
/// are dead. Nothing here runs a solver or a search.
//===----------------------------------------------------------------------===//

#ifndef GISELEGRAPHSYNTH_GISYNTHJOINT_H
#define GISELEGRAPHSYNTH_GISYNTHJOINT_H

#include "GISelEGraphSynth/GISynthPredicates.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/CodeGen/GlobalISel/CombinerHelper.h"
#include "llvm/CodeGen/GlobalISel/MachineIRBuilder.h"
#include "llvm/CodeGen/GlobalISel/Utils.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include <array>
#include <cstdint>

namespace llvm {
namespace gisynth {
namespace joint {

//===--- Definedness ------------------------------------------------------===//

/// The largest number of instructions before an entry copy that
/// isNoUndefArgumentCopy looks at.
constexpr unsigned MaxEntryScan = 64;
/// The depth of the recursion of isStableValue.
constexpr unsigned MaxStableDepth = 6;

/// True if \p Reg is a copy of a physical register at the entry of a
/// function whose IR arguments are all `noundef`:
///
///   * \p Reg is defined by a COPY in the entry block whose source is a
///     physical register (no subregister, not undef) that is a live-in of the
///     entry block, and no instruction before the COPY changes that register;
///   * the function is not variadic, has arguments, and every argument has
///     the attribute noundef.
///
/// GISelValueTracking does not see through such a copy, so it never says
/// that an argument is defined. The lowering of the arguments has no record
/// of which physical register carries which argument, so this asks for all
/// arguments: then a call that passes undef or poison is undefined behaviour
/// in the IR. The other live-ins of the entry block (the inputs that the
/// hardware or the ABI supplies, the bits of a register above a narrower
/// argument) are bits of a physical register, which hold one value.
inline bool isNoUndefArgumentCopy(Register Reg,
                                  const MachineRegisterInfo &MRI) {
  if (!Reg.isVirtual())
    return false;
  const MachineInstr *Def = MRI.getVRegDef(Reg);
  if (!Def || !Def->isCopy())
    return false;
  const MachineOperand &Src = Def->getOperand(1);
  if (!Src.getReg().isPhysical() || Src.getSubReg() || Src.isUndef())
    return false;
  const MachineFunction &MF = *Def->getMF();
  const MachineBasicBlock &Entry = MF.front();
  if (Def->getParent() != &Entry || !Entry.isLiveIn(Src.getReg()))
    return false;
  const Function &F = MF.getFunction();
  if (F.isVarArg() || F.arg_empty())
    return false;
  for (const Argument &A : F.args())
    if (!A.hasAttribute(Attribute::NoUndef))
      return false;
  const TargetRegisterInfo *TRI = MF.getSubtarget().getRegisterInfo();
  unsigned Scanned = 0;
  for (auto I = Entry.begin(); &*I != Def; ++I) {
    if (++Scanned > MaxEntryScan || I->modifiesRegister(Src.getReg(), TRI))
      return false;
  }
  return true;
}

/// True if \p Reg is neither undef nor poison: what a guard `defined(x)` of a
/// joint rule checks, and what the corpus writes as the fact "defined" of a
/// value of a region (the same function, so that a rule that the search
/// accepts for an instance also matches it in the compiler).
///
/// A value is defined if gisynth::isDefinedValue says so (LLVM's
/// isGuaranteedNotToBeUndefOrPoison, or the address of an object), if it is
/// a copy of an argument (isNoUndefArgumentCopy), a copy of a defined
/// virtual register, a hint (G_ASSERT_*) of a defined value, or a generic
/// instruction that cannot create undef or poison (LLVM's
/// canCreateUndefOrPoison with its flags) whose register operands are
/// defined.
inline bool isStableValue(Register Reg, const MachineRegisterInfo &MRI,
                          unsigned Depth = 0) {
  if (!Reg.isVirtual())
    return false;
  if (isDefinedValue(Reg, MRI))
    return true;
  const MachineInstr *Def = MRI.getVRegDef(Reg);
  if (!Def || Depth >= MaxStableDepth)
    return false;
  switch (Def->getOpcode()) {
  case TargetOpcode::COPY: {
    const MachineOperand &Src = Def->getOperand(1);
    if (Src.getReg().isPhysical())
      return isNoUndefArgumentCopy(Reg, MRI);
    return !Src.getSubReg() && isStableValue(Src.getReg(), MRI, Depth + 1);
  }
  case TargetOpcode::G_ASSERT_ZEXT:
  case TargetOpcode::G_ASSERT_SEXT:
  case TargetOpcode::G_ASSERT_ALIGN:
    return isStableValue(Def->getOperand(1).getReg(), MRI, Depth + 1);
  default:
    break;
  }
  if (!isPreISelGenericOpcode(Def->getOpcode()) ||
      Def->getOpcode() == TargetOpcode::G_PHI ||
      Def->getNumExplicitDefs() == 0 || Def->mayLoadOrStore() ||
      Def->hasUnmodeledSideEffects())
    return false;
  if (canCreateUndefOrPoison(Reg, MRI, /*ConsiderFlagsAndMetadata=*/true))
    return false;
  for (const MachineOperand &MO : Def->uses())
    if (MO.isReg() && !isStableValue(MO.getReg(), MRI, Depth + 1))
      return false;
  return true;
}

//===--- The description of a rule ----------------------------------------===//

constexpr unsigned MaxOps = 3;
constexpr unsigned MaxDefs = 2;
constexpr unsigned MaxNodes = 12;
constexpr unsigned MaxInputs = 8;
constexpr unsigned MaxClasses = 4;
/// The largest number of users of a value that a UserOf step looks at.
constexpr unsigned MaxUsers = 16;
/// The largest number of candidate bindings of one match.
constexpr unsigned MaxTrials = 256;
/// The largest distance, in instructions of the block, between the anchor
/// and any instruction that the placement looks at.
constexpr unsigned MaxDistance = 128;

/// A value of a rule: an input of the region, a result of a source
/// instruction, a result of a new instruction, or an integer literal (0, 1
/// or -1, which is all ones) of a width class.
struct Ref {
  enum KindTy : uint8_t { None, Input, Src, Tgt, Lit };
  KindTy Kind = None;
  uint8_t Idx = 0;
  uint8_t Res = 0;
  int8_t LitVal = 0;
};

constexpr Ref in(unsigned I) { return {Ref::Input, uint8_t(I), 0, 0}; }
constexpr Ref src(unsigned N, unsigned R = 0) {
  return {Ref::Src, uint8_t(N), uint8_t(R), 0};
}
constexpr Ref tgt(unsigned N, unsigned R = 0) {
  return {Ref::Tgt, uint8_t(N), uint8_t(R), 0};
}
constexpr Ref lit(int V) { return {Ref::Lit, 0, 0, int8_t(V)}; }

/// One instruction of a rule. Attr is the predicate of a G_ICMP, the
/// trailing immediate of an operator that has one, or -1.
struct NodeDesc {
  unsigned Opcode;
  int Attr;
  uint8_t NumDefs;
  uint8_t NumOps;
  bool Commutative;
  std::array<Ref, MaxOps> Ops;
  std::array<uint8_t, MaxDefs> DefClass;
  std::array<uint8_t, MaxOps> OpClass;
};

enum class Find : uint8_t { Anchor, DefOf, UserOf };

/// How the matcher finds the source instruction Node. DefOf: Via is
/// src(parent, operand slot) of an instruction found before. UserOf: Via is
/// a value found before (an input or a result of a source instruction).
struct MatchStep {
  uint8_t Node;
  Find How;
  Ref Via;
};

enum class Action : uint8_t { Erase, Replace, Keep, Relax };

/// The replaced output src(Node, Res) gets the value Value (of the width
/// class Class).
struct OutputDesc {
  uint8_t Node;
  uint8_t Res;
  Ref Value;
  uint8_t Class;
};

struct RuleDesc {
  const char *Name;
  ArrayRef<NodeDesc> Src;
  ArrayRef<MatchStep> Steps;
  ArrayRef<Action> Actions;
  ArrayRef<NodeDesc> Tgt;
  ArrayRef<OutputDesc> Outputs;
  unsigned NumInputs;
  ArrayRef<uint8_t> InputClass;
  /// Bit I: input I must be a stable value (isStableValue).
  uint32_t Defined;
  /// Bit I: input I must be a register that no other input has.
  uint32_t Distinct;
  unsigned NumClasses;
  /// The width of each class, NumClasses entries per proved width map.
  ArrayRef<uint16_t> WidthMaps;
};

/// What the matcher found and the applier uses.
struct JointPlan {
  std::array<MachineInstr *, MaxNodes> Src{};
  std::array<bool, MaxNodes> Swapped{};
  std::array<Register, MaxInputs> In{};
  std::array<LLT, MaxClasses> ClassTy;
  MachineInstr *InsertPt = nullptr;
};

//===--- Matching ---------------------------------------------------------===//

namespace detail {

inline void note(const RuleDesc &R, const char *What) {
  DEBUG_WITH_TYPE("gisel-synth-joint",
                  dbgs() << "gisel-synth-joint: " << What << ": " << R.Name
                         << "\n");
}

/// The operand indices of the register uses of \p MI, in order.
inline SmallVector<unsigned, MaxOps> regUses(const MachineInstr &MI) {
  SmallVector<unsigned, MaxOps> Out;
  for (unsigned I = MI.getNumExplicitDefs(), E = MI.getNumExplicitOperands();
       I != E; ++I)
    if (MI.getOperand(I).isReg())
      Out.push_back(I);
  return Out;
}

/// The register of the operand slot \p K of the source instruction \p N:
/// the two operands of a commutative instruction can be swapped.
inline Register slotReg(const RuleDesc &R, const JointPlan &S, unsigned N,
                        unsigned K) {
  const MachineInstr *MI = S.Src[N];
  auto Uses = regUses(*MI);
  unsigned I = (R.Src[N].Commutative && S.Swapped[N] && K < 2) ? 1 - K : K;
  return MI->getOperand(Uses[I]).getReg();
}

inline Register valueReg(const JointPlan &S, const Ref &X) {
  switch (X.Kind) {
  case Ref::Input:
    return S.In[X.Idx];
  case Ref::Src:
    return S.Src[X.Idx] ? S.Src[X.Idx]->getOperand(X.Res).getReg()
                        : Register();
  default:
    return Register();
  }
}

inline bool isLit(Register Reg, int Lit, const MachineRegisterInfo &MRI) {
  std::optional<APInt> C = getIConstantVRegVal(Reg, MRI);
  if (!C)
    return false;
  return Lit == -1 ? C->isAllOnes() : C->getZExtValue() == uint64_t(Lit);
}

/// True if \p MI can be the source instruction \p N.
inline bool nodeOK(const RuleDesc &R, const JointPlan &S, unsigned N,
                   const MachineInstr &MI, const MachineInstr &Root) {
  const NodeDesc &D = R.Src[N];
  if (MI.getOpcode() != D.Opcode || MI.getParent() != Root.getParent() ||
      MI.getNumExplicitDefs() != D.NumDefs)
    return false;
  for (unsigned J = 0; J != R.Src.size(); ++J)
    if (J != N && S.Src[J] == &MI)
      return false;
  if (regUses(MI).size() != D.NumOps)
    return false;
  for (unsigned I = 0; I != D.NumDefs; ++I)
    if (!MI.getOperand(I).getReg().isVirtual())
      return false;
  if (D.Opcode == TargetOpcode::G_ICMP)
    return MI.getOperand(1).getPredicate() == unsigned(D.Attr);
  if (D.Attr >= 0) {
    const MachineOperand &Last =
        MI.getOperand(MI.getNumExplicitOperands() - 1);
    return Last.isImm() && Last.getImm() == D.Attr;
  }
  return true;
}

/// Binds the operands of the source instruction \p N (just bound). An
/// operand that is a source instruction that is not bound yet is checked
/// when that instruction is bound, and again in finish().
inline bool bindOperands(const RuleDesc &R, const MachineRegisterInfo &MRI,
                         JointPlan &S, unsigned N) {
  const NodeDesc &D = R.Src[N];
  for (unsigned K = 0; K != D.NumOps; ++K) {
    Register Reg = slotReg(R, S, N, K);
    const Ref &X = D.Ops[K];
    switch (X.Kind) {
    case Ref::Input:
      if (!S.In[X.Idx])
        S.In[X.Idx] = Reg;
      else if (S.In[X.Idx] != Reg)
        return false;
      break;
    case Ref::Src:
      if (S.Src[X.Idx] && S.Src[X.Idx]->getOperand(X.Res).getReg() != Reg)
        return false;
      break;
    case Ref::Lit:
      if (!isLit(Reg, X.LitVal, MRI))
        return false;
      break;
    default:
      return false;
    }
  }
  // The results of N that other bound instructions read.
  for (unsigned J = 0; J != R.Src.size(); ++J) {
    if (!S.Src[J] || J == N)
      continue;
    const NodeDesc &E = R.Src[J];
    for (unsigned K = 0; K != E.NumOps; ++K)
      if (E.Ops[K].Kind == Ref::Src && E.Ops[K].Idx == N &&
          slotReg(R, S, J, K) != S.Src[N]->getOperand(E.Ops[K].Res).getReg())
        return false;
  }
  return true;
}

/// Positions of the instructions of the block of \p Root that are not more
/// than MaxDistance instructions before or after it.
inline DenseMap<const MachineInstr *, int> positions(MachineInstr &Root) {
  DenseMap<const MachineInstr *, int> Pos;
  MachineBasicBlock &MBB = *Root.getParent();
  int P = 0;
  Pos[&Root] = 0;
  for (auto It = Root.getIterator(); It != MBB.begin() && P > -int(MaxDistance);)
    Pos[&*--It] = --P;
  P = 0;
  for (auto It = std::next(Root.getIterator());
       It != MBB.end() && P < int(MaxDistance); ++It)
    Pos[&*It] = ++P;
  return Pos;
}

/// The checks that need the whole binding: the consistency of every
/// operand, the inputs, the types, the users of the instructions that die,
/// the guards and the position of the new instructions.
inline bool finish(const RuleDesc &R, const MachineRegisterInfo &MRI,
                   MachineInstr &Root, JointPlan &S) {
  const unsigned NumSrc = R.Src.size();
  SmallPtrSet<const MachineInstr *, MaxNodes> Matched;
  for (unsigned N = 0; N != NumSrc; ++N) {
    if (!S.Src[N])
      return false;
    Matched.insert(S.Src[N]);
  }
  for (unsigned N = 0; N != NumSrc; ++N) {
    const NodeDesc &D = R.Src[N];
    for (unsigned K = 0; K != D.NumOps; ++K) {
      Register Reg = slotReg(R, S, N, K);
      const Ref &X = D.Ops[K];
      if (X.Kind == Ref::Input || X.Kind == Ref::Src) {
        if (valueReg(S, X) != Reg)
          return false;
      } else if (X.Kind == Ref::Lit && !isLit(Reg, X.LitVal, MRI)) {
        return false;
      }
    }
  }
  // An input is a virtual register that no instruction of the region
  // defines.
  for (unsigned I = 0; I != R.NumInputs; ++I) {
    Register Reg = S.In[I];
    if (!Reg || !Reg.isVirtual())
      return false;
    const MachineInstr *Def = MRI.getVRegDef(Reg);
    if (!Def || Matched.count(Def))
      return false;
    if ((R.Distinct >> I) & 1)
      for (unsigned J = 0; J != R.NumInputs; ++J)
        if (J != I && S.In[J] == Reg)
          return false;
  }
  // Each width class has one LLT, a scalar that is not a floating-point
  // value or a pointer, and the widths are those of a proved width map.
  std::array<LLT, MaxClasses> Ty;
  auto Class = [&](unsigned C, Register Reg) {
    LLT T = MRI.getType(Reg);
    if (!T.isValid() || !T.isScalar() || T.isFloat() || C >= MaxClasses)
      return false;
    if (!Ty[C].isValid())
      Ty[C] = T;
    return Ty[C] == T;
  };
  for (unsigned I = 0; I != R.NumInputs; ++I)
    if (!Class(R.InputClass[I], S.In[I])) {
      note(R, "reject types");
      return false;
    }
  for (unsigned N = 0; N != NumSrc; ++N)
    for (unsigned D = 0; D != R.Src[N].NumDefs; ++D)
      if (!Class(R.Src[N].DefClass[D], S.Src[N]->getOperand(D).getReg())) {
        note(R, "reject types");
        return false;
      }
  bool Proved = false;
  for (unsigned M = 0; M + R.NumClasses <= R.WidthMaps.size();
       M += R.NumClasses) {
    bool Same = true;
    for (unsigned C = 0; C != R.NumClasses; ++C)
      Same &= Ty[C].isValid() &&
              Ty[C].getSizeInBits() == R.WidthMaps[M + C];
    Proved |= Same;
  }
  if (!Proved) {
    note(R, "reject width");
    return false;
  }
  // The users of the instructions of the region. An instruction that the
  // rule erases has no user outside of the region; a result of an
  // instruction that the rule replaces and that is not an output has none
  // either. Every user of an output gets the new value.
  for (unsigned N = 0; N != NumSrc; ++N) {
    Action A = R.Actions[N];
    if (A == Action::Keep || A == Action::Relax)
      continue;
    for (unsigned D = 0; D != R.Src[N].NumDefs; ++D) {
      bool IsOutput = false;
      for (const OutputDesc &O : R.Outputs)
        IsOutput |= O.Node == N && O.Res == D;
      if (IsOutput)
        continue;
      for (const MachineInstr &U :
           MRI.use_nodbg_instructions(S.Src[N]->getOperand(D).getReg())) {
        if (!Matched.count(&U)) {
          note(R, "reject boundary");
          return false;
        }
      }
    }
  }
  for (unsigned I = 0; I != R.NumInputs; ++I)
    if (((R.Defined >> I) & 1) && !isStableValue(S.In[I], MRI)) {
      note(R, "reject defined");
      return false;
    }
  // The position of the new instructions: after the definition of each
  // value that they read (in this block), and not after a user of an output
  // in this block. A definition in another block dominates this block: a
  // matched instruction reads it.
  auto Pos = positions(Root);
  auto PosOf = [&](const MachineInstr *MI) -> std::optional<int> {
    auto It = Pos.find(MI);
    if (It == Pos.end())
      return std::nullopt;
    return It->second;
  };
  for (const MachineInstr *MI : Matched)
    if (!PosOf(MI)) {
      note(R, "reject distance");
      return false;
    }
  const MachineInstr *First = nullptr;
  for (unsigned N = 0; N != NumSrc; ++N)
    if (R.Actions[N] == Action::Replace &&
        (!First || *PosOf(S.Src[N]) < *PosOf(First)))
      First = S.Src[N];
  if (!First)
    return false;
  int InsertPos = *PosOf(First);
  const MachineInstr *After = nullptr;
  auto Needs = [&](Register Reg) {
    const MachineInstr *Def = MRI.getVRegDef(Reg);
    if (!Def)
      return false;
    if (Def->getParent() != Root.getParent())
      return true;
    std::optional<int> P = PosOf(Def);
    if (!P)
      return false;
    if (*P >= InsertPos && (!After || *P > *PosOf(After)))
      After = Def;
    return true;
  };
  auto NeedsRef = [&](const Ref &X) {
    if (X.Kind == Ref::Input || X.Kind == Ref::Src)
      return Needs(valueReg(S, X));
    return true;
  };
  for (const NodeDesc &D : R.Tgt)
    for (unsigned K = 0; K != D.NumOps; ++K)
      if (!NeedsRef(D.Ops[K])) {
        note(R, "reject placement");
        return false;
      }
  for (const OutputDesc &O : R.Outputs)
    if (!NeedsRef(O.Value)) {
      note(R, "reject placement");
      return false;
    }
  MachineInstr *Insert = const_cast<MachineInstr *>(First);
  if (After) {
    auto Next = std::next(After->getIterator());
    if (Next == Root.getParent()->end()) {
      note(R, "reject placement");
      return false;
    }
    Insert = const_cast<MachineInstr *>(&*Next);
    InsertPos = *PosOf(After) + 1;
  }
  for (const OutputDesc &O : R.Outputs) {
    Register Old = S.Src[O.Node]->getOperand(O.Res).getReg();
    for (const MachineInstr &U : MRI.use_nodbg_instructions(Old)) {
      // A user in another block is dominated by this block, a G_PHI reads
      // the value at the end of a predecessor, and a matched instruction
      // dies with the region.
      if (U.getParent() != Root.getParent() || U.isPHI() || Matched.count(&U))
        continue;
      std::optional<int> P = PosOf(&U);
      // A user after the scanned instructions is after the position.
      if (P && *P < InsertPos) {
        note(R, "reject placement");
        return false;
      }
    }
  }
  // The instructions that stay must not read a value that dies.
  for (unsigned N = 0; N != NumSrc; ++N) {
    if (R.Actions[N] != Action::Keep && R.Actions[N] != Action::Relax)
      continue;
    const NodeDesc &D = R.Src[N];
    for (unsigned K = 0; K != D.NumOps; ++K)
      if (D.Ops[K].Kind == Ref::Src &&
          (R.Actions[D.Ops[K].Idx] == Action::Erase ||
           R.Actions[D.Ops[K].Idx] == Action::Replace))
        return false;
  }
  S.ClassTy = Ty;
  S.InsertPt = Insert;
  return true;
}

inline bool search(const RuleDesc &R, const MachineRegisterInfo &MRI,
                   MachineInstr &Root, const JointPlan &S, unsigned Step,
                   JointPlan &Out, unsigned &Trials) {
  if (Step == R.Steps.size()) {
    JointPlan T = S;
    if (!finish(R, MRI, Root, T))
      return false;
    Out = T;
    return true;
  }
  const MatchStep &M = R.Steps[Step];
  const NodeDesc &D = R.Src[M.Node];
  auto Try = [&](MachineInstr &MI) {
    if (!nodeOK(R, S, M.Node, MI, Root))
      return false;
    for (unsigned O = 0; O != (D.Commutative ? 2u : 1u); ++O) {
      if (++Trials > MaxTrials)
        return false;
      JointPlan T = S;
      T.Src[M.Node] = &MI;
      T.Swapped[M.Node] = O;
      if (bindOperands(R, MRI, T, M.Node) &&
          search(R, MRI, Root, T, Step + 1, Out, Trials))
        return true;
    }
    return false;
  };
  switch (M.How) {
  case Find::Anchor:
    return Try(Root);
  case Find::DefOf: {
    if (!S.Src[M.Via.Idx])
      return false;
    Register Reg = slotReg(R, S, M.Via.Idx, M.Via.Res);
    MachineInstr *Def = Reg.isVirtual() ? MRI.getVRegDef(Reg) : nullptr;
    return Def && Try(*Def);
  }
  case Find::UserOf: {
    Register Reg = valueReg(S, M.Via);
    if (!Reg)
      return false;
    SmallPtrSet<MachineInstr *, MaxUsers> Seen;
    unsigned Users = 0;
    for (MachineInstr &U : MRI.use_nodbg_instructions(Reg)) {
      if (++Users > MaxUsers) {
        note(R, "reject fanout");
        return false;
      }
      if (Seen.insert(&U).second && Try(U))
        return true;
    }
    return false;
  }
  }
  return false;
}

} // end namespace detail

/// Matches the rule \p R with the anchor \p Root. Fills \p Plan and returns
/// true if every check holds; changes nothing.
inline bool match(const RuleDesc &R, MachineInstr &Root,
                  const MachineRegisterInfo &MRI, JointPlan &Plan) {
  detail::note(R, "anchor");
  JointPlan S;
  unsigned Trials = 0;
  if (!detail::search(R, MRI, Root, S, 0, Plan, Trials)) {
    detail::note(R, Trials > MaxTrials ? "reject trials" : "reject pattern");
    return false;
  }
  detail::note(R, "matched");
  return true;
}

//===--- Applying ---------------------------------------------------------===//

/// Executes the plan of a match of \p R: drops the flags of the
/// instructions to relax, builds the new instructions before
/// Plan.InsertPt (each one once, in order), gives the users of each
/// replaced output its new value, and erases the source instructions that
/// are dead.
inline void apply(const RuleDesc &R, MachineIRBuilder &B,
                  const JointPlan &Plan) {
  MachineRegisterInfo &MRI = *B.getMRI();
  GISelChangeObserver *Observer = B.getObserver();
  B.setInstrAndDebugLoc(*Plan.InsertPt);
  for (unsigned N = 0; N != R.Src.size(); ++N)
    if (R.Actions[N] == Action::Relax)
      dropFlags(B, *Plan.Src[N]);
  SmallVector<std::array<Register, MaxDefs>, 8> New(R.Tgt.size());
  auto Value = [&](const Ref &X, unsigned C) -> Register {
    switch (X.Kind) {
    case Ref::Input:
      return Plan.In[X.Idx];
    case Ref::Src:
      return Plan.Src[X.Idx]->getOperand(X.Res).getReg();
    case Ref::Tgt:
      return New[X.Idx][X.Res];
    case Ref::Lit: {
      LLT Ty = Plan.ClassTy[C];
      unsigned W = Ty.getSizeInBits();
      APInt V = X.LitVal == -1 ? APInt::getAllOnes(W) : APInt(W, X.LitVal);
      return B.buildConstant(Ty, V).getReg(0);
    }
    default:
      llvm_unreachable("no value");
    }
  };
  for (unsigned T = 0; T != R.Tgt.size(); ++T) {
    const NodeDesc &D = R.Tgt[T];
    SmallVector<DstOp, MaxDefs> Dsts;
    for (unsigned I = 0; I != D.NumDefs; ++I)
      Dsts.push_back(Plan.ClassTy[D.DefClass[I]]);
    SmallVector<SrcOp, MaxOps + 1> Srcs;
    if (D.Opcode == TargetOpcode::G_ICMP)
      Srcs.push_back(CmpInst::Predicate(D.Attr));
    for (unsigned K = 0; K != D.NumOps; ++K)
      Srcs.push_back(Value(D.Ops[K], D.OpClass[K]));
    if (D.Opcode != TargetOpcode::G_ICMP && D.Attr >= 0)
      Srcs.push_back(int64_t(D.Attr));
    auto MIB = B.buildInstr(D.Opcode, Dsts, Srcs);
    for (unsigned I = 0; I != D.NumDefs; ++I)
      New[T][I] = MIB->getOperand(I).getReg();
  }
  // Only the uses of an output get the new value (MRI.replaceRegWith would
  // also rename the definition of the old instruction). The types are
  // equal: one width class has one LLT (finish).
  for (const OutputDesc &O : R.Outputs) {
    Register Old = Plan.Src[O.Node]->getOperand(O.Res).getReg();
    Register NewReg = Value(O.Value, O.Class);
    if (Old == NewReg)
      continue;
    if (Observer)
      Observer->changingAllUsesOfReg(MRI, Old);
    for (MachineOperand &MO : make_early_inc_range(MRI.use_operands(Old)))
      MO.setReg(NewReg);
    if (Observer)
      Observer->finishedChangingAllUsesOfReg();
  }
  // Users before definitions (the source instructions are in a
  // topological order).
  for (unsigned N = R.Src.size(); N-- != 0;) {
    if (R.Actions[N] != Action::Erase && R.Actions[N] != Action::Replace)
      continue;
    MachineInstr *MI = Plan.Src[N];
    if (isTriviallyDead(*MI, MRI)) {
      salvageDebugInfo(MRI, *MI);
      MI->eraseFromParent();
    }
  }
  detail::note(R, "applied");
}

} // end namespace joint
} // end namespace gisynth
} // end namespace llvm

#endif // GISELEGRAPHSYNTH_GISYNTHJOINT_H
