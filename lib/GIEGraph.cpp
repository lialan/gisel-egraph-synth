//===- llvm/CodeGen/GlobalISel/GIEGraph.cpp - Typed e-graph for gMIR ------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// Implementation of the experimental gMIR e-graph: hash-consing, union-find,
/// congruence closure, analyses, pattern matching, bounded saturation and
/// cost-based extraction.
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/GlobalISel/GIEGraph.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/Twine.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include <deque>
#include <set>

using namespace llvm;
using namespace llvm::egraph;

//===----------------------------------------------------------------------===//
// Opcode helpers
//===----------------------------------------------------------------------===//

static std::optional<APInt> shiftAmount(const APInt &Val, const APInt &Amt) {
  if (Amt.uge(Val.getBitWidth()))
    return std::nullopt;
  return Amt.zextOrTrunc(Val.getBitWidth());
}

/// The undefined behaviour of a division or remainder (OpProperties::
/// MayTrap).
static bool divisionTraps(bool IsSigned, const APInt &A, const APInt &B) {
  return B.isZero() || (IsSigned && A.isMinSignedValue() && B.isAllOnes());
}

/// A bit count as a constant of \p Width bits.
static std::optional<APInt> countToAPInt(unsigned Count, unsigned Width) {
  if (!isUIntN(Width, Count))
    return std::nullopt;
  return APInt(Width, Count);
}

static std::optional<uint64_t> invertBranchAttr(uint64_t Attr) {
  // Bit 1: the terminator can be inverted. Bit 0: this is the inverted form.
  if (!(Attr & 2))
    return std::nullopt;
  return Attr ^ 1;
}

static std::vector<OpProperties> buildOpProperties() {
  using namespace TargetOpcode;
  std::vector<OpProperties> T;
  auto Op = [&](unsigned Opc, const char *Name, const char *Short,
                OpShape Shape = OpShape::Binary) {
    T.emplace_back();
    OpProperties &P = T.back();
    P.Opcode = Opc;
    P.Name = Name;
    P.ShortName = Short;
    P.Shape = Shape;
    switch (Shape) {
    case OpShape::Binary:
    case OpShape::Compare:
    case OpShape::PtrAdd:
      P.NumOperands = 2;
      break;
    case OpShape::Unary:
    case OpShape::Cast:
    case OpShape::BitCount:
      P.NumOperands = 1;
      break;
    case OpShape::Select:
      P.NumOperands = 3;
      break;
    case OpShape::Phi:
      P.NumOperands = -1;
      break;
    case OpShape::Effect:
      P.NumOperands = 0;
      break;
    }
    return &P;
  };

  OpProperties *P = Op(G_ADD, "G_ADD", "add");
  P->Commutative = P->Associative = true;
  P->RightIdentity = 0;
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    return A + B;
  };

  P = Op(G_SUB, "G_SUB", "sub");
  P->RightIdentity = 0;
  P->SelfValue = 0;
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    return A - B;
  };

  P = Op(G_MUL, "G_MUL", "mul");
  P->Commutative = P->Associative = true;
  P->RightIdentity = 1;
  P->RightAbsorbing = 0;
  P->DistributesOver = {G_ADD};
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    return A * B;
  };

  P = Op(G_AND, "G_AND", "and");
  P->Commutative = P->Associative = P->Idempotent = true;
  P->RightIdentity = -1;
  P->RightAbsorbing = 0;
  P->DistributesOver = {G_OR, G_XOR};
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    return A & B;
  };

  P = Op(G_OR, "G_OR", "or");
  P->Commutative = P->Associative = P->Idempotent = true;
  P->RightIdentity = 0;
  P->RightAbsorbing = -1;
  P->DistributesOver = {G_AND};
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    return A | B;
  };

  P = Op(G_XOR, "G_XOR", "xor");
  P->Commutative = P->Associative = true;
  P->RightIdentity = 0;
  P->SelfValue = 0;
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    return A ^ B;
  };

  P = Op(G_SHL, "G_SHL", "shl");
  P->IsShift = true;
  P->RightIdentity = 0;
  P->RightDistributesOverConst = {G_ADD};
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    if (auto Amt = shiftAmount(A, B))
      return A.shl(*Amt);
    return std::nullopt;
  };

  P = Op(G_LSHR, "G_LSHR", "lshr");
  P->IsShift = true;
  P->RightIdentity = 0;
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    if (auto Amt = shiftAmount(A, B))
      return A.lshr(*Amt);
    return std::nullopt;
  };

  P = Op(G_ASHR, "G_ASHR", "ashr");
  P->IsShift = true;
  P->RightIdentity = 0;
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    if (auto Amt = shiftAmount(A, B))
      return A.ashr(*Amt);
    return std::nullopt;
  };

  // Division and remainder. All identities hold where the behaviour is
  // defined; see OpProperties::MayTrap for how the rest is handled.
  P = Op(G_UDIV, "G_UDIV", "udiv");
  P->MayTrap = true;
  P->RightIdentity = 1;
  P->LeftAbsorbing = 0;
  P->SelfValue = 1;
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    if (divisionTraps(/*IsSigned=*/false, A, B))
      return std::nullopt;
    return A.udiv(B);
  };

  P = Op(G_SDIV, "G_SDIV", "sdiv");
  P->MayTrap = P->IsSigned = true;
  P->RightIdentity = 1;
  P->LeftAbsorbing = 0;
  P->SelfValue = 1;
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    if (divisionTraps(/*IsSigned=*/true, A, B))
      return std::nullopt;
    return A.sdiv(B);
  };

  P = Op(G_UREM, "G_UREM", "urem");
  P->MayTrap = true;
  P->LeftAbsorbing = 0;
  P->RightConstResult = {{1, 0}};
  P->SelfValue = 0;
  P->RemainderOf = G_UDIV;
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    if (divisionTraps(/*IsSigned=*/false, A, B))
      return std::nullopt;
    return A.urem(B);
  };

  P = Op(G_SREM, "G_SREM", "srem");
  P->MayTrap = P->IsSigned = true;
  P->LeftAbsorbing = 0;
  P->RightConstResult = {{1, 0}, {-1, 0}};
  P->SelfValue = 0;
  P->RemainderOf = G_SDIV;
  P->Fold = [](const APInt &A, const APInt &B) -> std::optional<APInt> {
    if (divisionTraps(/*IsSigned=*/true, A, B))
      return std::nullopt;
    return A.srem(B);
  };

  // Casts. All three are homomorphisms for the bitwise operators. trunc is
  // also one for G_ADD, G_SUB and G_MUL, but those are not listed: hoisting
  // makes the arithmetic wider, and narrow multiply-add patterns are lost
  // (measured on AMDGPU). This is the same choice as the combiner's
  // hoist_logic_op_with_same_opcode_hands.
  P = Op(G_TRUNC, "G_TRUNC", "trunc", OpShape::Cast);
  P->Cast = CastKind::Truncate;
  P->ComposesTo = {{G_TRUNC, G_TRUNC}};
  P->HomomorphicOver = {G_AND, G_OR, G_XOR};
  P->FoldUnary = [](const APInt &A, unsigned W) -> std::optional<APInt> {
    return A.trunc(W);
  };
  // Every constant has many preimages. The sign-extended one keeps -1 as
  // -1, so that a NOT is still a NOT after hoisting.
  P->Preimage = [](const APInt &C, unsigned W) -> std::optional<APInt> {
    return C.sext(W);
  };

  P = Op(G_ZEXT, "G_ZEXT", "zext", OpShape::Cast);
  P->Cast = CastKind::ZeroExtend;
  P->ComposesTo = {{G_ZEXT, G_ZEXT}};
  P->HomomorphicOver = {G_AND, G_OR, G_XOR};
  P->FoldUnary = [](const APInt &A, unsigned W) -> std::optional<APInt> {
    return A.zext(W);
  };
  P->Preimage = [](const APInt &C, unsigned W) -> std::optional<APInt> {
    if (!C.isIntN(W))
      return std::nullopt;
    return C.trunc(W);
  };

  P = Op(G_SEXT, "G_SEXT", "sext", OpShape::Cast);
  P->Cast = CastKind::SignExtend;
  P->ComposesTo = {{G_SEXT, G_SEXT}, {G_ZEXT, G_ZEXT}};
  P->HomomorphicOver = {G_AND, G_OR, G_XOR};
  P->FoldUnary = [](const APInt &A, unsigned W) -> std::optional<APInt> {
    return A.sext(W);
  };
  P->Preimage = [](const APInt &C, unsigned W) -> std::optional<APInt> {
    if (!C.isSignedIntN(W))
      return std::nullopt;
    return C.trunc(W);
  };

  // Bit permutations: involutions and homomorphisms for the bitwise
  // operators.
  P = Op(G_BSWAP, "G_BSWAP", "bswap", OpShape::Unary);
  P->Involution = true;
  P->HomomorphicOver = {G_AND, G_OR, G_XOR};
  P->FoldUnary = [](const APInt &A, unsigned W) -> std::optional<APInt> {
    if (A.getBitWidth() % 16 != 0)
      return std::nullopt;
    return A.byteSwap();
  };
  P->Preimage = P->FoldUnary;

  P = Op(G_BITREVERSE, "G_BITREVERSE", "bitreverse", OpShape::Unary);
  P->Involution = true;
  P->HomomorphicOver = {G_AND, G_OR, G_XOR};
  P->FoldUnary = [](const APInt &A, unsigned W) -> std::optional<APInt> {
    return A.reverseBits();
  };
  P->Preimage = P->FoldUnary;

  // Bit counts. A population count does not depend on the positions of the
  // bits; reversing the bits exchanges leading and trailing zeros.
  P = Op(G_CTPOP, "G_CTPOP", "ctpop", OpShape::BitCount);
  P->InvariantUnder = {G_BSWAP, G_BITREVERSE, G_ZEXT};
  P->FoldUnary = [](const APInt &A, unsigned W) {
    return countToAPInt(A.popcount(), W);
  };

  P = Op(G_CTLZ, "G_CTLZ", "ctlz", OpShape::BitCount);
  P->ComposesTo = {{G_BITREVERSE, G_CTTZ}};
  P->FoldUnary = [](const APInt &A, unsigned W) {
    return countToAPInt(A.countl_zero(), W);
  };

  P = Op(G_CTTZ, "G_CTTZ", "cttz", OpShape::BitCount);
  P->ComposesTo = {{G_BITREVERSE, G_CTLZ}};
  P->FoldUnary = [](const APInt &A, unsigned W) {
    return countToAPInt(A.countr_zero(), W);
  };

  // The predicate algebra of comparisons (swapped, inverse, reflexive)
  // comes from CmpInst; see addCompareRulesFromProperties.
  Op(G_ICMP, "G_ICMP", "icmp", OpShape::Compare);
  Op(G_SELECT, "G_SELECT", "select", OpShape::Select);

  P = Op(G_PTR_ADD, "G_PTR_ADD", "ptradd", OpShape::PtrAdd);
  P->RightIdentity = 0;
  P->ActsBy = G_ADD;

  P = Op(G_PHI, "G_PHI", "phi", OpShape::Phi);
  P->Idempotent = true;

  // A conditional branch with its condition as the operand. The following
  // unconditional branch, if any, is the other target.
  P = Op(G_BRCOND, "G_BRCOND", "brcond", OpShape::Effect);
  P->NumOperands = 1;
  P->InvertAttr = invertBranchAttr;
  Op(G_BR, "G_BR", "br", OpShape::Effect);
  return T;
}

ArrayRef<OpProperties> llvm::egraph::getAllOpProperties() {
  static const std::vector<OpProperties> Table = buildOpProperties();
  return Table;
}

const OpProperties *llvm::egraph::getOpProperties(unsigned Opcode) {
  for (const OpProperties &P : getAllOpProperties())
    if (P.Opcode == Opcode)
      return &P;
  return nullptr;
}

static std::optional<unsigned> getOpcodeByName(StringRef Name) {
  for (const OpProperties &P : getAllOpProperties())
    if (Name == P.Name)
      return P.Opcode;
  return std::nullopt;
}

static StringRef getOpcodeName(unsigned Opc) {
  if (const OpProperties *P = getOpProperties(Opc))
    return P->Name;
  return "G_<unknown>";
}

bool llvm::egraph::isACOperator(unsigned Opc) {
  const OpProperties *P = getOpProperties(Opc);
  return P && P->Associative && P->Commutative;
}

static bool isShift(unsigned Opc) {
  const OpProperties *P = getOpProperties(Opc);
  return P && P->IsShift;
}

/// True if the division or remainder \p N has defined behaviour for all
/// values of its operands: the divisor is a constant other than zero (and
/// other than -1 for a signed operation).
static bool isDefinedDivision(const EGraph &G, const OpProperties &P,
                              const ENode &N) {
  const std::optional<APInt> &Divisor = G.getClass(N.Ops[1]).Const;
  return Divisor && !Divisor->isZero() && !(P.IsSigned && Divisor->isAllOnes());
}

static StringRef getICmpPredicateName(uint64_t Attr) {
  return CmpInst::getPredicateName(static_cast<CmpInst::Predicate>(Attr));
}

/// Print the attribute of an operation as it is written in patterns.
static void printAttr(raw_ostream &OS, unsigned Opc, uint64_t Attr) {
  const OpProperties *P = getOpProperties(Opc);
  if (P && P->Shape == OpShape::Compare)
    OS << ":" << getICmpPredicateName(Attr);
  else if (Attr)
    OS << ":" << Attr;
}

//===----------------------------------------------------------------------===//
// ENode
//===----------------------------------------------------------------------===//

ENode ENode::makeInput(LLT Ty, unsigned Idx) {
  ENode N;
  N.Kind = ENodeKind::Input;
  N.Ty = Ty;
  N.InputIdx = Idx;
  return N;
}

ENode ENode::makeConstant(LLT Ty, const APInt &Val) {
  assert(Ty.isScalar() && Ty.getSizeInBits() == Val.getBitWidth() &&
         "constant width must match its type");
  ENode N;
  N.Kind = ENodeKind::Constant;
  N.Opcode = TargetOpcode::G_CONSTANT;
  N.Ty = Ty;
  N.Imm = Val;
  return N;
}

ENode ENode::makeOp(unsigned Opcode, LLT Ty, ArrayRef<EClassId> Ops,
                    uint32_t Flags, uint64_t Attr) {
  ENode N;
  N.Kind = ENodeKind::Operation;
  N.Opcode = Opcode;
  N.Ty = Ty;
  N.Flags = Flags;
  N.Attr = Attr;
  N.Ops.assign(Ops.begin(), Ops.end());
  return N;
}

bool ENode::operator==(const ENode &O) const {
  if (Kind != O.Kind || Opcode != O.Opcode || Flags != O.Flags || Ty != O.Ty ||
      Attr != O.Attr)
    return false;
  switch (Kind) {
  case ENodeKind::Input:
    return InputIdx == O.InputIdx;
  case ENodeKind::Constant:
    return Imm.getBitWidth() == O.Imm.getBitWidth() && Imm == O.Imm;
  case ENodeKind::Operation:
    return Ops == O.Ops;
  }
  llvm_unreachable("bad kind");
}

hash_code llvm::egraph::hash_value(const ENode &N) {
  hash_code H = hash_combine(static_cast<unsigned>(N.Kind), N.Opcode, N.Flags,
                             N.Ty.getUniqueRAWLLTData(), N.Attr);
  switch (N.Kind) {
  case ENodeKind::Input:
    return hash_combine(H, N.InputIdx);
  case ENodeKind::Constant:
    return hash_combine(H, hash_value(N.Imm));
  case ENodeKind::Operation:
    return hash_combine(H, hash_combine_range(N.Ops.begin(), N.Ops.end()));
  }
  llvm_unreachable("bad kind");
}

//===----------------------------------------------------------------------===//
// EGraph
//===----------------------------------------------------------------------===//

EClassId EGraph::addInput(const InputInfo &Info) {
  unsigned Idx = Inputs.size();
  Inputs.push_back(Info);
  return add(ENode::makeInput(Info.Ty, Idx));
}

EClassId EGraph::addConstant(LLT Ty, const APInt &Val) {
  return add(ENode::makeConstant(Ty, Val));
}

EClassId EGraph::addOp(unsigned Opcode, LLT Ty, ArrayRef<EClassId> Ops,
                       uint32_t Flags, uint64_t Attr) {
  return add(ENode::makeOp(Opcode, Ty, Ops, Flags, Attr));
}

EClassId EGraph::find(EClassId Id) const {
  assert(Id < Parent.size() && "invalid e-class id");
  EClassId Root = Id;
  while (Parent[Root] != Root)
    Root = Parent[Root];
  // Path compression.
  while (Parent[Id] != Root) {
    EClassId Next = Parent[Id];
    Parent[Id] = Root;
    Id = Next;
  }
  return Root;
}

ENode EGraph::canonicalize(const ENode &N) const {
  ENode C = N;
  for (EClassId &Op : C.Ops)
    Op = find(Op);
  // Commutativity is part of the canonical form rather than a rewrite rule:
  // the operands of a commutative operation are ordered by class id, so
  // a op b and b op a hash-cons to the same e-node immediately. rebuild()
  // re-canonicalizes after merges, which re-sorts operands whose ids changed.
  // The matcher compensates by trying both operand orders.
  // A comparison is handled the same way, with the swapped predicate:
  // a < b and b > a are the same e-node.
  if (C.isOperation() && C.Ops.size() == 2 && C.Ops[0] > C.Ops[1]) {
    const OpProperties *P = getOpProperties(C.Opcode);
    if (P && P->Commutative) {
      std::swap(C.Ops[0], C.Ops[1]);
    } else if (P && P->Shape == OpShape::Compare) {
      std::swap(C.Ops[0], C.Ops[1]);
      C.Attr =
          CmpInst::getSwappedPredicate(static_cast<CmpInst::Predicate>(C.Attr));
    }
  }
  return C;
}

std::optional<EClassId> EGraph::lookup(const ENode &N) const {
  auto It = Memo.find(canonicalize(N));
  if (It == Memo.end())
    return std::nullopt;
  return find(It->second);
}

EClassId EGraph::addACTerm(unsigned Opc, LLT Ty, ArrayRef<EClassId> Leaves) {
  assert(!Leaves.empty() && "empty AC term");
  SmallVector<EClassId, 8> L;
  for (EClassId X : Leaves)
    L.push_back(find(X));
  llvm::sort(L);
  EClassId Acc = L[0];
  for (unsigned I = 1, E = L.size(); I != E; ++I)
    Acc = addOp(Opc, Ty, {Acc, L[I]});
  return Acc;
}

std::optional<EClassId> EGraph::lookupACTerm(unsigned Opc, LLT Ty,
                                             ArrayRef<EClassId> Leaves) const {
  assert(!Leaves.empty() && "empty AC term");
  SmallVector<EClassId, 8> L;
  for (EClassId X : Leaves)
    L.push_back(find(X));
  llvm::sort(L);
  EClassId Acc = L[0];
  for (unsigned I = 1, E = L.size(); I != E; ++I) {
    std::optional<EClassId> Next = lookup(ENode::makeOp(Opc, Ty, {Acc, L[I]}));
    if (!Next)
      return std::nullopt;
    Acc = *Next;
  }
  return Acc;
}

bool EGraph::flattenAC(EClassId Root, const ENode &N, bool StopAtMixed,
                       unsigned MaxLeaves, SmallVectorImpl<EClassId> &Leaves,
                       bool *UsedFlagged) const {
  // Flatten through the first unflagged node of the same operator in each
  // operand class (deterministic), never through a class on the current
  // path. Flagged nodes are leaves unless UsedFlagged is given: flattening
  // them drops their flags, which is only a refinement, so the caller is
  // told whether that happened. With StopAtMixed, classes that also contain
  // another kind of node (e.g. a G_MUL in a class of sums) stay leaves, so
  // that patterns can match that other node.
  Leaves.clear();
  if (UsedFlagged)
    *UsedFlagged = false;
  SmallVector<EClassId, 8> Path = {find(Root)};
  bool TooBig = false;
  std::function<void(EClassId)> Flatten = [&](EClassId L) {
    L = find(L);
    if (TooBig)
      return;
    const ENode *Inner = nullptr, *FlaggedInner = nullptr;
    bool Mixed = false;
    if (!is_contained(Path, L)) {
      for (const ENode &M : Classes[L].Nodes) {
        if (M.isOperation() && M.Opcode == N.Opcode && M.Ty == N.Ty) {
          if (!M.Flags && !Inner)
            Inner = &M;
          else if (M.Flags && !FlaggedInner)
            FlaggedInner = &M;
        } else {
          Mixed = true;
        }
      }
    }
    if (!Inner && UsedFlagged && FlaggedInner) {
      Inner = FlaggedInner;
      *UsedFlagged = true;
    }
    if (!Inner || (StopAtMixed && Mixed)) {
      Leaves.push_back(L);
      TooBig = Leaves.size() > MaxLeaves;
      return;
    }
    Path.push_back(L);
    SmallVector<EClassId, 2> Ops(Inner->Ops.begin(), Inner->Ops.end());
    for (EClassId Op : Ops)
      Flatten(Op);
    Path.pop_back();
  };
  for (EClassId Op : N.Ops)
    Flatten(Op);
  return !TooBig;
}

void EGraph::getACViews(EClassId C, unsigned Opc, SmallVectorImpl<ACView> &Out,
                        unsigned MaxLeaves, unsigned MaxViews) const {
  C = find(C);
  LLT Ty = Classes[C].Ty;
  // Per AC node of the class: its operands, its full flattening, and its
  // flattening that stops at mixed classes (see flattenAC). Classes in the
  // canonical form already contain the full flattening of their terms, so
  // this covers the groupings that matter without enumerating all of them.
  SmallVector<EClassId, 8> Leaves;
  auto Push = [&](ArrayRef<EClassId> L, bool ViaRefinement) {
    if (Out.size() >= MaxViews)
      return;
    ACView V;
    V.Leaves.assign(L.begin(), L.end());
    llvm::sort(V.Leaves);
    V.ViaRefinement = ViaRefinement;
    for (const ACView &O : Out)
      if (O.Leaves == V.Leaves && (!O.ViaRefinement || ViaRefinement))
        return;
    Out.push_back(std::move(V));
  };
  for (const ENode &N : Classes[C].Nodes) {
    if (!N.isOperation() || N.Opcode != Opc || N.Ty != Ty)
      continue;
    SmallVector<EClassId, 2> Ops;
    for (EClassId Op : N.Ops)
      Ops.push_back(find(Op));
    Push(Ops, N.Flags != 0);
    if (N.Flags)
      continue;
    for (bool StopAtMixed : {false, true})
      if (flattenAC(C, N, StopAtMixed, MaxLeaves, Leaves) && Leaves.size() > 2)
        Push(Leaves, false);
    // Also look through flagged nodes; such a view only justifies
    // refinements.
    bool UsedFlagged;
    if (flattenAC(C, N, /*StopAtMixed=*/false, MaxLeaves, Leaves,
                  &UsedFlagged) &&
        UsedFlagged)
      Push(Leaves, true);
  }
}

unsigned EGraph::canonicalizeAC(unsigned MaxLeaves, unsigned MaxNodes) {
  assert(!Dirty && "rebuild() the e-graph before canonicalizing");
  unsigned Merges = 0;
  SmallVector<EClassId, 8> Leaves;
  for (EClassId Id : getClassIds()) {
    // Copy: adding nodes may reallocate the class vector.
    SmallVector<ENode, 2> Nodes = Classes[find(Id)].Nodes;
    for (const ENode &N : Nodes) {
      if (NumNodes >= MaxNodes)
        return Merges;
      if (!N.isOperation() || N.Flags || !isACOperator(N.Opcode))
        continue;
      // Two leaves: the node is its own canonical form.
      if (!flattenAC(Id, N, /*StopAtMixed=*/false, MaxLeaves, Leaves) ||
          Leaves.size() < 3)
        continue;
      EClassId K = addACTerm(N.Opcode, N.Ty, Leaves);
      Merges += merge(Id, K);
    }
  }
  return Merges;
}

unsigned EGraph::collapseIdempotentPhis() {
  assert(!Dirty && "rebuild() the e-graph before collapsing PHIs");
  SmallVector<std::pair<EClassId, EClassId>, 4> Pending;
  for (EClassId Id : getClassIds()) {
    for (const ENode &N : Classes[Id].Nodes) {
      if (!N.isOperation() || N.Ops.empty())
        continue;
      const OpProperties *P = getOpProperties(N.Opcode);
      if (!P || P->Shape != OpShape::Phi || !P->Idempotent)
        continue;
      // The value on every incoming edge is the same class, so the PHI has
      // exactly that value (including undef and poison).
      EClassId First = find(N.Ops[0]);
      if (First != Id &&
          all_of(N.Ops, [&](EClassId Op) { return find(Op) == First; }))
        Pending.push_back({Id, First});
    }
  }
  unsigned Merges = 0;
  for (auto [A, B] : Pending)
    Merges += merge(A, B);
  return Merges;
}

EClassId EGraph::add(ENode N) {
  N = canonicalize(N);
  auto It = Memo.find(N);
  if (It != Memo.end())
    return find(It->second);

  EClassId Id = Classes.size();
  Classes.emplace_back();
  Parent.push_back(Id);
  EClass &C = Classes.back();
  C.Ty = N.Ty;
  if (N.isConstant())
    C.Const = N.Imm;
  C.NotUndef = computeNodeNotUndef(N);
  C.NotPoison = computeNodeNotPoison(N);
  Memo.emplace(N, Id);
  C.Nodes.push_back(std::move(N));
  ++NumNodes;
  ++NumClasses;
  return Id;
}

bool EGraph::merge(EClassId A, EClassId B) {
  A = find(A);
  B = find(B);
  if (A == B)
    return false;
  if (Classes[A].Ty != Classes[B].Ty) {
    assert(false && "attempt to merge e-classes of different types");
    return false;
  }
  // Union by size; ties broken by the smaller id for determinism.
  EClassId Winner = A, Loser = B;
  if (Classes[B].Nodes.size() > Classes[A].Nodes.size() ||
      (Classes[B].Nodes.size() == Classes[A].Nodes.size() && B < A))
    std::swap(Winner, Loser);

  EClass &W = Classes[Winner];
  EClass &L = Classes[Loser];
  if (W.Const && L.Const)
    assert(*W.Const == *L.Const && "merging classes with different constants");
  if (!W.Const)
    W.Const = L.Const;
  W.NotUndef |= L.NotUndef;
  W.NotPoison |= L.NotPoison;
  for (ENode &N : L.Nodes)
    W.Nodes.push_back(std::move(N));
  for (EClassId R : L.RefinesTo)
    W.RefinesTo.push_back(R);
  L.Nodes.clear();
  L.RefinesTo.clear();
  L.Const.reset();
  Parent[Loser] = Winner;
  --NumClasses;
  Dirty = true;
  return true;
}

bool EGraph::addRefinement(EClassId From, EClassId To) {
  From = find(From);
  To = find(To);
  if (From == To)
    return false;
  if (Classes[From].Ty != Classes[To].Ty) {
    assert(false && "refinement between e-classes of different types");
    return false;
  }
  for (EClassId R : Classes[From].RefinesTo)
    if (find(R) == To)
      return false;
  Classes[From].RefinesTo.push_back(To);
  return true;
}

SmallVector<EClassId, 4> EGraph::getRefinementClosure(EClassId Id) const {
  SmallVector<EClassId, 4> Result;
  Id = find(Id);
  // Fast path: most classes have no refinement edges.
  if (Classes[Id].RefinesTo.empty())
    return Result;
  SmallDenseSet<EClassId, 8> Seen;
  Seen.insert(Id);
  std::deque<EClassId> Work;
  Work.push_back(Id);
  while (!Work.empty()) {
    EClassId C = Work.front();
    Work.pop_front();
    for (EClassId R : Classes[C].RefinesTo) {
      R = find(R);
      if (!Seen.insert(R).second)
        continue;
      Result.push_back(R);
      Work.push_back(R);
    }
  }
  return Result;
}

bool EGraph::refinesTo(EClassId From, EClassId To) const {
  From = find(From);
  To = find(To);
  if (From == To)
    return true;
  return is_contained(getRefinementClosure(From), To);
}

SmallVector<EClassId, 32> EGraph::getClassIds() const {
  SmallVector<EClassId, 32> Ids;
  for (EClassId I = 0, E = Classes.size(); I != E; ++I)
    if (Parent[I] == I)
      Ids.push_back(I);
  return Ids;
}

bool EGraph::computeNodeNotUndef(const ENode &N) const {
  switch (N.Kind) {
  case ENodeKind::Input:
    return Inputs[N.InputIdx].NotUndef;
  case ENodeKind::Constant:
    return true;
  case ENodeKind::Operation: {
    // No supported operator produces undef from defined operands.
    const OpProperties *P = getOpProperties(N.Opcode);
    if (!P || !P->hasResult())
      return false;
    return all_of(N.Ops, [&](EClassId Op) { return getClass(Op).NotUndef; });
  }
  }
  llvm_unreachable("bad kind");
}

bool EGraph::computeNodeNotPoison(const ENode &N) const {
  switch (N.Kind) {
  case ENodeKind::Input:
    return Inputs[N.InputIdx].NotPoison;
  case ENodeKind::Constant:
    return true;
  case ENodeKind::Operation: {
    // Any poison-generating flag may introduce poison.
    const OpProperties *P = getOpProperties(N.Opcode);
    if (N.Flags != 0 || !P || !P->hasResult())
      return false;
    if (P->IsShift) {
      const std::optional<APInt> &Amt = getClass(N.Ops[1]).Const;
      if (!Amt || Amt->uge(N.Ty.getScalarSizeInBits()))
        return false;
    }
    // Undefined behaviour is treated like poison: a value that may trap is
    // never dropped by an exact rewrite.
    if (P->MayTrap && !isDefinedDivision(*this, *P, N))
      return false;
    // For a select or a PHI, requiring all operands is conservative.
    return all_of(N.Ops, [&](EClassId Op) { return getClass(Op).NotPoison; });
  }
  }
  llvm_unreachable("bad kind");
}

void EGraph::recomputeAnalyses() {
  SmallVector<EClassId, 32> Ids = getClassIds();
  for (EClassId Id : Ids) {
    EClass &C = Classes[Id];
    for (const ENode &N : C.Nodes) {
      if (!N.isConstant())
        continue;
      if (C.Const)
        assert(*C.Const == N.Imm && "class with two different constants");
      else
        C.Const = N.Imm;
    }
  }
  // NotUndef / NotPoison are monotone: once established they stay valid. Run
  // to a fixpoint.
  bool Changed = true;
  while (Changed) {
    Changed = false;
    for (EClassId Id : Ids) {
      EClass &C = Classes[Id];
      if (C.NotUndef && C.NotPoison)
        continue;
      for (const ENode &N : C.Nodes) {
        if (!C.NotUndef && computeNodeNotUndef(N)) {
          C.NotUndef = true;
          Changed = true;
        }
        if (!C.NotPoison && computeNodeNotPoison(N)) {
          C.NotPoison = true;
          Changed = true;
        }
      }
    }
  }
}

void EGraph::rebuild() {
  // Congruence closure by re-canonicalization: repeatedly re-hash every node
  // with canonical operands; two classes containing the same canonical node
  // are congruent and get merged. Repeat until no merge happens. This is
  // simpler than egg's incremental parent-list repair and adequate for the
  // bounded region sizes used here.
  while (true) {
    Memo.clear();
    SmallVector<std::pair<EClassId, EClassId>, 8> Pending;
    for (EClassId Id : getClassIds()) {
      EClass &C = Classes[Id];
      SmallVector<ENode, 2> NewNodes;
      for (const ENode &N : C.Nodes) {
        ENode CN = canonicalize(N);
        auto [It, Inserted] = Memo.try_emplace(CN, Id);
        if (!Inserted) {
          if (find(It->second) != Id)
            Pending.push_back({It->second, Id});
          continue; // Duplicate node; keep only the first copy.
        }
        NewNodes.push_back(std::move(CN));
      }
      C.Nodes = std::move(NewNodes);
    }
    for (auto &[N, Id] : Pruned) {
      N = canonicalize(N);
      Id = find(Id);
      auto [It, Inserted] = Memo.try_emplace(N, Id);
      if (!Inserted && find(It->second) != Id)
        Pending.push_back({It->second, Id});
    }
    bool Merged = false;
    for (auto [A, B] : Pending)
      Merged |= merge(A, B);
    if (!Merged)
      break;
  }
  NumNodes = Memo.size();
  // Canonicalize refinement edges.
  for (EClassId Id : getClassIds()) {
    EClass &C = Classes[Id];
    SmallVector<EClassId, 1> NewRefs;
    for (EClassId R : C.RefinesTo) {
      R = find(R);
      if (R != Id && !is_contained(NewRefs, R))
        NewRefs.push_back(R);
    }
    C.RefinesTo = std::move(NewRefs);
  }
  recomputeAnalyses();
  pruneConstantClasses();
  Dirty = false;
}

void EGraph::pruneConstantClasses() {
  // A class with a known constant value is best represented by the constant
  // itself. Keeping its other nodes only feeds the rules with ever-larger
  // constant expressions (e.g. once `a == a + 0`, the class of 0 collects
  // 0 + 0, 0 * 2, 0 << 1, ...), so saturation would not terminate within the
  // budget. This mirrors the usual constant-folding analysis in egg.
  for (EClassId Id : getClassIds()) {
    EClass &C = Classes[Id];
    if (!C.Const || C.Nodes.size() == 1)
      continue;
    SmallVector<ENode, 2> Keep;
    for (ENode &N : C.Nodes) {
      if (N.isConstant())
        Keep.push_back(std::move(N));
      else
        Pruned.push_back({std::move(N), Id});
    }
    assert(!Keep.empty() && "constant class without a constant node");
    C.Nodes = std::move(Keep);
  }
}

void EGraph::print(raw_ostream &OS) const {
  for (EClassId Id : getClassIds()) {
    const EClass &C = Classes[Id];
    OS << "e" << Id << " : " << C.Ty;
    if (C.Const)
      OS << " const=" << C.Const->getSExtValue();
    if (C.NotUndef)
      OS << " not-undef";
    if (C.NotPoison)
      OS << " not-poison";
    OS << "\n";
    for (const ENode &N : C.Nodes) {
      OS << "  ";
      switch (N.Kind) {
      case ENodeKind::Input:
        OS << "input#" << N.InputIdx;
        break;
      case ENodeKind::Constant:
        OS << "G_CONSTANT " << N.Imm.getSExtValue();
        break;
      case ENodeKind::Operation:
        OS << getOpcodeName(N.Opcode);
        printAttr(OS, N.Opcode, N.Attr);
        if (N.Flags)
          OS << " flags=" << N.Flags;
        for (EClassId Op : N.Ops)
          OS << " e" << find(Op);
        break;
      }
      OS << "\n";
    }
    for (EClassId R : C.RefinesTo)
      OS << "  ~> e" << find(R) << "\n";
  }
}

//===----------------------------------------------------------------------===//
// Pattern parsing
//===----------------------------------------------------------------------===//

namespace {
class PatternParser {
public:
  PatternParser(StringRef RuleName, StringRef Text, bool IsRHS,
                std::vector<std::string> &VarNames,
                std::vector<std::string> &ConstNames)
      : RuleName(RuleName), Text(Text), IsRHS(IsRHS), VarNames(VarNames),
        ConstNames(ConstNames) {}

  Pattern parse() {
    Pattern P;
    P.Root = parseNode(P);
    skipWS();
    if (!Text.empty())
      error("trailing characters");
    return P;
  }

private:
  [[noreturn]] void error(const Twine &Msg) {
    report_fatal_error(Twine("GIEGraph rule '") + RuleName + "': " + Msg);
  }

  void skipWS() { Text = Text.ltrim(); }

  StringRef token() {
    skipWS();
    size_t Len = Text.find_first_of(" \t\n()");
    StringRef Tok = Text.take_front(Len);
    Text = Text.drop_front(Tok.size());
    if (Tok.empty())
      error("unexpected end of pattern");
    return Tok;
  }

  unsigned lookupOrAdd(std::vector<std::string> &Names, StringRef Name,
                       bool MayAdd) {
    for (unsigned I = 0, E = Names.size(); I != E; ++I)
      if (Names[I] == Name)
        return I;
    if (!MayAdd)
      error(Twine("variable '") + Name + "' not bound by the left-hand side");
    Names.push_back(Name.str());
    return Names.size() - 1;
  }

  unsigned parseNode(Pattern &P) {
    skipWS();
    PatNode N;
    if (Text.consume_front("(")) {
      auto [OpName, AttrName] = token().split(':');
      std::optional<unsigned> Opc = getOpcodeByName(OpName);
      if (!Opc)
        error(Twine("unknown opcode '") + OpName + "'");
      const OpProperties *Props = getOpProperties(*Opc);
      N.Kind = PatNode::Op;
      N.Opcode = *Opc;
      parseAttr(N, *Props, AttrName);
      while (true) {
        skipWS();
        if (Text.consume_front(")"))
          break;
        N.Children.push_back(parseNode(P));
      }
      if (Props->NumOperands < 0)
        error(Twine("'") + OpName + "' cannot be used in a pattern");
      if (N.Children.size() != unsigned(Props->NumOperands))
        error(Twine("'") + OpName + "' takes " + Twine(Props->NumOperands) +
              " operands");
    } else {
      StringRef Tok = token();
      if (Tok.consume_front("?")) {
        N.Kind = PatNode::Var;
        N.Index = lookupOrAdd(VarNames, Tok, !IsRHS);
      } else if (Tok.consume_front("#")) {
        N.Kind = PatNode::ConstVar;
        N.Index = lookupOrAdd(ConstNames, Tok, !IsRHS);
      } else if (Tok.consume_front("$")) {
        if (!IsRHS)
          error("computed constants are only allowed on the right-hand side");
        N.Kind = PatNode::Computed;
        if (Tok.getAsInteger(10, N.Index))
          error("bad computed constant index");
      } else {
        N.Kind = PatNode::Literal;
        if (Tok.getAsInteger(10, N.Value))
          error(Twine("bad literal '") + Tok + "'");
      }
    }
    P.Nodes.push_back(std::move(N));
    return P.Nodes.size() - 1;
  }

  void parseAttr(PatNode &N, const OpProperties &Props, StringRef AttrName) {
    if (AttrName.empty()) {
      // A created comparison needs a predicate.
      if (IsRHS && Props.Shape == OpShape::Compare)
        error("comparison without a predicate on the right-hand side");
      return;
    }
    if (AttrName == "inverted") {
      if (!IsRHS || !Props.InvertAttr)
        error("':inverted' needs an invertible operator on the right-hand "
              "side");
      N.AttrKind = PatNode::InvertedRootAttr;
      return;
    }
    if (Props.Shape != OpShape::Compare)
      error(Twine("unexpected attribute '") + AttrName + "'");
    for (unsigned Pred = CmpInst::FIRST_ICMP_PREDICATE;
         Pred <= CmpInst::LAST_ICMP_PREDICATE; ++Pred) {
      if (getICmpPredicateName(Pred) != AttrName)
        continue;
      N.AttrKind = PatNode::ExactAttr;
      N.Attr = Pred;
      return;
    }
    error(Twine("unknown predicate '") + AttrName + "'");
  }

  StringRef RuleName;
  StringRef Text;
  bool IsRHS;
  std::vector<std::string> &VarNames;
  std::vector<std::string> &ConstNames;
};

/// The variables a pattern is poison for; see RewriteRule::MentionL.
struct PoisonUse {
  uint32_t Strict = 0, Mention = 0;
};
} // namespace

static PoisonUse computePoisonUse(const Pattern &P, unsigned Idx) {
  const PatNode &N = P.Nodes[Idx];
  PoisonUse U;
  if (N.Kind == PatNode::Var) {
    U.Strict = U.Mention = 1u << N.Index;
    return U;
  }
  if (N.Kind != PatNode::Op)
    return U;
  if (getOpProperties(N.Opcode)->Shape == OpShape::Select) {
    PoisonUse Cond = computePoisonUse(P, N.Children[0]);
    PoisonUse TrueArm = computePoisonUse(P, N.Children[1]);
    PoisonUse FalseArm = computePoisonUse(P, N.Children[2]);
    // With a constant condition only the selected arm matters. The condition
    // is an s1, so the literal is true if its low bit is set.
    const PatNode &CondNode = P.Nodes[N.Children[0]];
    if (CondNode.Kind == PatNode::Literal)
      return (CondNode.Value & 1) ? TrueArm : FalseArm;
    U.Strict = Cond.Strict | (TrueArm.Strict & FalseArm.Strict);
    U.Mention = Cond.Mention | TrueArm.Mention | FalseArm.Mention;
    return U;
  }
  // All other operators are poison iff an operand is.
  for (unsigned C : N.Children) {
    PoisonUse Child = computePoisonUse(P, C);
    U.Strict |= Child.Strict;
    U.Mention |= Child.Mention;
  }
  return U;
}

static void countVarOccurrences(const Pattern &P,
                                SmallVectorImpl<unsigned> &Occ) {
  for (const PatNode &N : P.Nodes)
    if (N.Kind == PatNode::Var)
      ++Occ[N.Index];
}

RewriteRule::RewriteRule(StringRef Name, StringRef LHSText, StringRef RHSText,
                         ApplyFn Fn, bool PoisonExact)
    : Name(Name.str()), PoisonExact(PoisonExact), Fn(std::move(Fn)) {
  LHS = PatternParser(Name, LHSText, /*IsRHS=*/false, VarNames, ConstNames)
            .parse();
  RHS = PatternParser(Name, RHSText, /*IsRHS=*/true, VarNames, ConstNames)
            .parse();
  if (LHS.Nodes[LHS.Root].Kind != PatNode::Op)
    report_fatal_error(Twine("GIEGraph rule '") + Name +
                       "': left-hand side must be an operation");
  if (VarNames.size() > 32)
    report_fatal_error(Twine("GIEGraph rule '") + Name +
                       "': too many variables");
  OccL.assign(VarNames.size(), 0);
  OccR.assign(VarNames.size(), 0);
  countVarOccurrences(LHS, OccL);
  countVarOccurrences(RHS, OccR);
  PoisonUse L = computePoisonUse(LHS, LHS.Root);
  PoisonUse R = computePoisonUse(RHS, RHS.Root);
  MentionL = L.Mention;
  StrictL = L.Strict;
  MentionR = R.Mention;
  StrictR = R.Strict;
  if (PoisonExact && MentionL != MentionR)
    report_fatal_error(Twine("GIEGraph rule '") + Name +
                       "': a poison-exact rule must use the same variables "
                       "on both sides");
}

bool RewriteRule::needsDefinedForRefinement(unsigned Var) const {
  // RHS poison must imply LHS poison. The RHS can only be poison because of
  // a variable it mentions, so this holds if the LHS is strict in each of
  // them.
  uint32_t Bit = 1u << Var;
  return !PoisonExact && (MentionR & Bit) && !(StrictL & Bit);
}

bool RewriteRule::needsDefinedForExactness(unsigned Var) const {
  // Additionally, LHS poison must imply RHS poison.
  uint32_t Bit = 1u << Var;
  return needsDefinedForRefinement(Var) ||
         (!PoisonExact && (MentionL & Bit) && !(StrictR & Bit));
}

// Soundness of a rule instance (see the design document):
//  * All operators appearing in the patterns are unflagged and, except for
//    the arms of a select, propagate poison exactly (shift amounts are
//    constants in range). So a side is poison if a variable it is strict in
//    is poison, and only if a variable it mentions is poison. Operations
//    with undefined behaviour are only matched as refinements and only
//    created if the matched pattern has the same undefined behaviour.
//  * Each occurrence of an undef-carrying value may observe a different
//    value. If a variable occurs exactly once on each side, the sets of
//    possible results coincide. If it occurs several times on a side, the
//    identity is only guaranteed on the "diagonal" (all occurrences equal).
namespace {
/// Definedness of a variable's binding. An AC term bound to a variable is
/// built from unflagged operators, so it is not undef (not poison) if all
/// of its leaves are.
struct BindingFacts {
  bool NotUndef = true;
  bool NotPoison = true;
};
} // namespace

static BindingFacts getBindingFacts(const EGraph &G, const RuleMatch &M,
                                    unsigned V) {
  BindingFacts F;
  auto Add = [&](EClassId C) {
    const EClass &Cls = G.getClass(C);
    F.NotUndef &= Cls.NotUndef;
    F.NotPoison &= Cls.NotPoison;
  };
  if (M.isSumBound(V))
    for (EClassId L : M.VarSums[V].Leaves)
      Add(L);
  else
    Add(M.Vars[V]);
  return F;
}

// Matching modulo AC (views, extension, AC terms bound to variables) only
// regroups and reorders the operands of unflagged associative and
// commutative operators, which is exact: every leaf occurs once on each
// side. Leaves kept aside by extension (RuleMatch::Rest) also occur once on
// each side, and `x op Rest` preserves refinement of x, so the
// classification below only depends on the rule's variables.
bool RewriteRule::isExactFor(const EGraph &G, const RuleMatch &M) const {
  for (unsigned V = 0, E = VarNames.size(); V != E; ++V) {
    BindingFacts C = getBindingFacts(G, M, V);
    // E.g. a dropped variable: LHS is poison when it is, RHS is not.
    if (needsDefinedForExactness(V) && !C.NotPoison)
      return false;
    unsigned L = OccL[V], R = OccR[V];
    if (R == 0) {
      if (L > 1 && !C.NotUndef)
        return false;
    } else if (!(L == 1 && R == 1) && !C.NotUndef) {
      return false;
    }
  }
  return true;
}

bool RewriteRule::isRefinementFor(const EGraph &G, const RuleMatch &M) const {
  // RHS variables are a subset of LHS variables. Using a variable at most
  // once on the RHS picks one point of the diagonal of the LHS' possible
  // values.
  for (unsigned V = 0, E = VarNames.size(); V != E; ++V) {
    BindingFacts C = getBindingFacts(G, M, V);
    if (needsDefinedForRefinement(V) && !C.NotPoison)
      return false;
    if (OccR[V] > 1 && !C.NotUndef)
      return false;
  }
  return true;
}

static void printPattern(raw_ostream &OS, const Pattern &P, unsigned Idx,
                         ArrayRef<std::string> Vars,
                         ArrayRef<std::string> Consts) {
  const PatNode &N = P.Nodes[Idx];
  switch (N.Kind) {
  case PatNode::Var:
    OS << "?" << Vars[N.Index];
    return;
  case PatNode::ConstVar:
    OS << "#" << Consts[N.Index];
    return;
  case PatNode::Literal:
    OS << N.Value;
    return;
  case PatNode::Computed:
    OS << "$" << N.Index;
    return;
  case PatNode::Op:
    OS << "(" << getOpcodeName(N.Opcode);
    if (N.AttrKind == PatNode::ExactAttr)
      printAttr(OS, N.Opcode, N.Attr);
    else if (N.AttrKind == PatNode::InvertedRootAttr)
      OS << ":inverted";
    for (unsigned C : N.Children) {
      OS << " ";
      printPattern(OS, P, C, Vars, Consts);
    }
    OS << ")";
    return;
  }
}

void RewriteRule::print(raw_ostream &OS) const {
  OS << Name << ": ";
  printPattern(OS, LHS, LHS.Root, VarNames, ConstNames);
  OS << " => ";
  printPattern(OS, RHS, RHS.Root, VarNames, ConstNames);
  auto PrintVars = [&](StringRef Label, bool Exact) {
    bool Any = false;
    for (unsigned V = 0, E = VarNames.size(); V != E; ++V) {
      // Variables needed for a refinement are not repeated for exactness.
      bool Needed =
          Exact ? needsDefinedForExactness(V) && !needsDefinedForRefinement(V)
                : needsDefinedForRefinement(V);
      if (!Needed)
        continue;
      OS << (Any ? " " : (" ; " + Label + ": ").str()) << VarNames[V];
      Any = true;
    }
  };
  PrintVars("refine-defined", /*Exact=*/false);
  PrintVars("exact-defined", /*Exact=*/true);
}

//===----------------------------------------------------------------------===//
// Matching
//===----------------------------------------------------------------------===//

ArrayRef<ACView> ACViewCache::get(EClassId C, unsigned Opc) {
  C = G.find(C);
  auto [It, Inserted] = Views.try_emplace({C, Opc});
  if (Inserted)
    G.getACViews(C, Opc, It->second, MaxLeaves, MaxViews);
  return It->second;
}

std::optional<EClassId> ACViewCache::lookup(unsigned Opc, LLT Ty,
                                            ArrayRef<EClassId> Leaves) {
  std::vector<EClassId> Key(Leaves.begin(), Leaves.end());
  Key.push_back(Opc);
  auto [It, Inserted] = Terms.try_emplace(std::move(Key));
  if (Inserted)
    It->second = G.lookupACTerm(Opc, Ty, Leaves);
  return It->second;
}

namespace {
static constexpr EClassId Unbound = ~0u;

/// Matches a rule's LHS. Patterns of AC operators are matched modulo AC:
/// against every view of a class (ACView), a binary pattern (op P1 P2)
/// matches if one child matches a single leaf and the other the remaining
/// leaves. At the root, two single leaves may also be chosen and the
/// remaining leaves become RuleMatch::Rest ("matching with extension").
/// Several leaves match a variable as an AC term (a class if one exists,
/// otherwise RuleMatch::VarSums), and a structural pattern only if a class
/// for their canonical form exists.
class Matcher {
public:
  Matcher(const EGraph &G, const RewriteRule &R,
          SmallVectorImpl<RuleMatch> &Out, unsigned Limit, ACViewCache &Cache)
      : G(G), R(R), Out(Out), Limit(Limit), Cache(Cache) {}

  void run(EClassId Root) {
    Cur.Root = Root;
    Cur.Vars.assign(R.getNumVars(), Unbound);
    Cur.VarSums.assign(R.getNumVars(), ACTerm());
    Cur.Consts.assign(R.getNumConstVars(), std::nullopt);
    Cur.Rest = ACTerm();
    Cur.PatClasses.assign(R.getLHS().Nodes.size(), RuleMatch::NoClass);
    Cur.RootAttr = 0;
    Cur.Guards.clear();
    Cur.ViaRefinement = false;
    Seen.clear();
    const Pattern &P = R.getLHS();
    matchAt(P.Root, Root, /*AllowRefine=*/false, [&] {
      // Different views often yield the same match; keep one copy.
      if (Out.size() < Limit && Seen.insert(key(Cur)).second)
        Out.push_back(Cur);
    });
  }

private:
  bool full() const { return Out.size() >= Limit; }

  static std::vector<uint64_t> key(const RuleMatch &M) {
    std::vector<uint64_t> K;
    K.push_back(M.ViaRefinement);
    K.push_back(M.RootAttr);
    for (unsigned V = 0, E = M.Vars.size(); V != E; ++V) {
      K.push_back(M.Vars[V]);
      if (M.isSumBound(V)) {
        K.push_back(M.VarSums[V].Opcode);
        K.insert(K.end(), M.VarSums[V].Leaves.begin(),
                 M.VarSums[V].Leaves.end());
        K.push_back(~0ull);
      }
    }
    for (const std::optional<APInt> &C : M.Consts)
      K.push_back(C ? uint64_t(hash_value(*C)) : ~uint64_t(0));
    K.push_back(M.Rest.Opcode);
    K.insert(K.end(), M.Rest.Leaves.begin(), M.Rest.Leaves.end());
    return K;
  }

  void bindClass(unsigned V, EClassId C, function_ref<void()> K) {
    EClassId &Slot = Cur.Vars[V];
    if (Slot == Unbound) {
      Slot = C;
      K();
      Slot = Unbound;
    } else if (Slot == RuleMatch::SumBound) {
      const ACTerm &T = Cur.VarSums[V];
      std::optional<EClassId> S =
          Cache.lookup(T.Opcode, G.getType(C), T.Leaves);
      if (S && *S == G.find(C))
        K();
    } else if (G.find(Slot) == G.find(C)) {
      K();
    }
  }

  /// Bind variable \p V to the AC term Opc(Leaves...). The term is kept as
  /// is (no lookup) unless it has to be compared with a class.
  void bindSum(unsigned V, unsigned Opc, LLT Ty, ArrayRef<EClassId> Leaves,
               function_ref<void()> K) {
    EClassId &Slot = Cur.Vars[V];
    if (Slot != Unbound && Slot != RuleMatch::SumBound) {
      std::optional<EClassId> S = Cache.lookup(Opc, Ty, Leaves);
      if (S && *S == G.find(Slot))
        K();
      return;
    }
    if (Slot == Unbound) {
      Slot = RuleMatch::SumBound;
      Cur.VarSums[V].Opcode = Opc;
      Cur.VarSums[V].Leaves.assign(Leaves.begin(), Leaves.end());
      K();
      Cur.VarSums[V] = ACTerm();
      Slot = Unbound;
    } else if (Slot == RuleMatch::SumBound && Cur.VarSums[V].Opcode == Opc &&
               ArrayRef<EClassId>(Cur.VarSums[V].Leaves) == Leaves) {
      K();
    }
  }

  void matchAt(unsigned PIdx, EClassId C, bool AllowRefine,
               function_ref<void()> K) {
    if (full())
      return;
    const PatNode &PN = R.getLHS().Nodes[PIdx];
    C = G.find(C);
    if (PN.Kind == PatNode::Var) {
      bindClass(PN.Index, C, K);
      return;
    }
    bool IsRoot = PIdx == R.getLHS().Root;
    // Structural patterns: try the class itself, then (if allowed) the
    // classes it refines to.
    matchStructural(PIdx, C, IsRoot, K);
    if (!AllowRefine)
      return;
    SmallVector<EClassId, 4> Closure = G.getRefinementClosure(C);
    if (Closure.empty())
      return;
    bool Saved = Cur.ViaRefinement;
    Cur.ViaRefinement = true;
    for (EClassId D : Closure)
      matchStructural(PIdx, D, /*IsRoot=*/false, K);
    Cur.ViaRefinement = Saved;
  }

  /// Cheap necessary condition for pattern \p PIdx to match class \p C.
  bool mayMatch(unsigned PIdx, EClassId C) const {
    const PatNode &PN = R.getLHS().Nodes[PIdx];
    const EClass &Cls = G.getClass(C);
    switch (PN.Kind) {
    case PatNode::Var:
      return true;
    case PatNode::Literal:
    case PatNode::ConstVar:
      return Cls.Const.has_value() || !Cls.RefinesTo.empty();
    case PatNode::Op:
      if (!Cls.RefinesTo.empty())
        return true;
      return any_of(Cls.Nodes, [&](const ENode &N) {
        return N.isOperation() && N.Opcode == PN.Opcode;
      });
    case PatNode::Computed:
      break;
    }
    return false;
  }

  /// Match pattern \p PIdx against the AC term Opc(Leaves...) (sorted).
  void matchLeaves(unsigned PIdx, unsigned Opc, LLT Ty,
                   ArrayRef<EClassId> Leaves, function_ref<void()> K) {
    if (Leaves.size() == 1) {
      if (mayMatch(PIdx, Leaves[0]))
        matchAt(PIdx, Leaves[0], /*AllowRefine=*/true, K);
      return;
    }
    const PatNode &PN = R.getLHS().Nodes[PIdx];
    if (PN.Kind == PatNode::Var) {
      bindSum(PN.Index, Opc, Ty, Leaves, K);
      return;
    }
    // A structural pattern can only match a class that already exists. The
    // canonical form of the leaves is an Opc node, so only a pattern of the
    // same operator (or a class merged with something else) can match.
    if (std::optional<EClassId> C = Cache.lookup(Opc, Ty, Leaves))
      if (mayMatch(PIdx, *C))
        matchAt(PIdx, *C, /*AllowRefine=*/true, K);
  }

  /// For (op ?a <constant>) with ?a used once in the LHS, extension only
  /// produces regroupings of what the complete split (?a takes all other
  /// leaves) already yields: the constant interacts with ?a as a whole.
  bool extensionIsRedundant(const PatNode &PN) const {
    const Pattern &P = R.getLHS();
    auto IsConst = [&](unsigned I) {
      PatNode::KindTy K = P.Nodes[I].Kind;
      return K == PatNode::Literal || K == PatNode::ConstVar;
    };
    auto IsLinearVar = [&](unsigned I) {
      return P.Nodes[I].Kind == PatNode::Var &&
             R.getLHSOccurrences(P.Nodes[I].Index) == 1;
    };
    unsigned A = PN.Children[0], B = PN.Children[1];
    return (IsLinearVar(A) && IsConst(B)) || (IsConst(A) && IsLinearVar(B));
  }

  void matchAC(const PatNode &PN, EClassId C, bool AllowExtension,
               function_ref<void()> K) {
    LLT Ty = G.getType(C);
    unsigned P0 = PN.Children[0], P1 = PN.Children[1];
    SmallVector<EClassId, 8> Others;
    auto Without = [&](ArrayRef<EClassId> L, unsigned I, unsigned J) {
      Others.clear();
      for (unsigned X = 0, E = L.size(); X != E; ++X)
        if (X != I && X != J)
          Others.push_back(L[X]);
      return SmallVector<EClassId, 8>(Others);
    };
    for (const ACView &V : Cache.get(C, PN.Opcode)) {
      if (full())
        return;
      bool Saved = Cur.ViaRefinement;
      Cur.ViaRefinement |= V.ViaRefinement;
      ArrayRef<EClassId> L = V.Leaves;
      unsigned N = L.size();
      // One child matches a single leaf, the other child all other leaves.
      for (unsigned I = 0; I != N; ++I) {
        if (I && L[I] == L[I - 1])
          continue;
        SmallVector<EClassId, 8> Rest = Without(L, I, I);
        ArrayRef<EClassId> One = L.slice(I, 1);
        matchLeaves(P0, PN.Opcode, Ty, One,
                    [&] { matchLeaves(P1, PN.Opcode, Ty, Rest, K); });
        if (N > 2)
          matchLeaves(P0, PN.Opcode, Ty, Rest,
                      [&] { matchLeaves(P1, PN.Opcode, Ty, One, K); });
      }
      // Extension: two single leaves; the others are kept aside.
      if (AllowExtension && N >= 3 && !extensionIsRedundant(PN)) {
        for (unsigned I = 0; I != N; ++I) {
          if (I && L[I] == L[I - 1])
            continue;
          for (unsigned J = I + 1; J != N; ++J) {
            if (J > I + 1 && L[J] == L[J - 1])
              continue;
            Cur.Rest.Opcode = PN.Opcode;
            Cur.Rest.Leaves = Without(L, I, J);
            ArrayRef<EClassId> A = L.slice(I, 1), B = L.slice(J, 1);
            matchLeaves(P0, PN.Opcode, Ty, A,
                        [&] { matchLeaves(P1, PN.Opcode, Ty, B, K); });
            if (L[I] != L[J])
              matchLeaves(P0, PN.Opcode, Ty, B,
                          [&] { matchLeaves(P1, PN.Opcode, Ty, A, K); });
            Cur.Rest = ACTerm();
          }
        }
      }
      Cur.ViaRefinement = Saved;
    }
  }

  void matchStructural(unsigned PIdx, EClassId C, bool IsRoot,
                       function_ref<void()> K) {
    const PatNode &PN = R.getLHS().Nodes[PIdx];
    const EClass &Cls = G.getClass(C);
    switch (PN.Kind) {
    case PatNode::Var:
    case PatNode::Computed:
      llvm_unreachable("not structural");
    case PatNode::Literal: {
      if (!Cls.Const)
        return;
      APInt Lit(Cls.Const->getBitWidth(), PN.Value, /*isSigned=*/true,
                /*implicitTrunc=*/true);
      if (*Cls.Const == Lit)
        K();
      return;
    }
    case PatNode::ConstVar: {
      if (!Cls.Const)
        return;
      std::optional<APInt> &Slot = Cur.Consts[PN.Index];
      if (!Slot) {
        Slot = *Cls.Const;
        K();
        Slot.reset();
      } else if (Slot->getBitWidth() == Cls.Const->getBitWidth() &&
                 *Slot == *Cls.Const) {
        K();
      }
      return;
    }
    case PatNode::Op: {
      if (isACOperator(PN.Opcode) && PN.Children.size() == 2) {
        matchAC(PN, C, /*AllowExtension=*/IsRoot, K);
        return;
      }
      const OpProperties *P = getOpProperties(PN.Opcode);
      for (const ENode &N : Cls.Nodes) {
        if (full())
          return;
        if (!N.isOperation() || N.Opcode != PN.Opcode ||
            N.Ops.size() != PN.Children.size())
          continue;
        // Commutative operations and comparisons are stored in one
        // canonical operand order (see EGraph::canonicalize), so also match
        // the other order; for a comparison, with the swapped predicate.
        bool Direct = true;
        bool Swapped = P->Commutative && N.Ops[0] != N.Ops[1];
        if (PN.AttrKind == PatNode::ExactAttr) {
          Direct = N.Attr == PN.Attr;
          Swapped = P->Shape == OpShape::Compare && N.Ops[0] != N.Ops[1] &&
                    CmpInst::getSwappedPredicate(
                        static_cast<CmpInst::Predicate>(N.Attr)) == PN.Attr;
          if (!Direct && !Swapped)
            continue;
        }
        if (isShift(N.Opcode)) {
          // Only shifts that cannot create poison are rewritten.
          const std::optional<APInt> &Amt = G.getClass(N.Ops[1]).Const;
          if (!Amt || Amt->uge(N.Ty.getScalarSizeInBits()))
            continue;
        }
        // A flagged operation (nuw/nsw/exact/disjoint...) is refined by the
        // same operation without flags: the flags only add poison. Matching
        // it as the unflagged operator is therefore sound, but the result
        // can only justify a refinement, never a merge.
        bool SavedRefinement = Cur.ViaRefinement;
        uint64_t SavedAttr = Cur.RootAttr;
        if (N.Flags)
          Cur.ViaRefinement = true;
        // A division that may trap: the pattern operator is the total
        // function, so again only a refinement is justified. Remember it;
        // the right-hand side may repeat it.
        bool Guarded = P->MayTrap && !isDefinedDivision(G, *P, N);
        if (Guarded) {
          Cur.ViaRefinement = true;
          Cur.Guards.push_back({P->IsSigned, N.Ops[0], N.Ops[1]});
        }
        if (IsRoot)
          Cur.RootAttr = N.Attr;
        Cur.PatClasses[PIdx] = C;
        if (Direct)
          matchChildren(PN, N, 0, /*Swap=*/false, K);
        if (Swapped)
          matchChildren(PN, N, 0, /*Swap=*/true, K);
        Cur.PatClasses[PIdx] = RuleMatch::NoClass;
        if (Guarded)
          Cur.Guards.pop_back();
        Cur.RootAttr = SavedAttr;
        Cur.ViaRefinement = SavedRefinement;
      }
      return;
    }
    }
  }

  void matchChildren(const PatNode &PN, const ENode &N, unsigned I, bool Swap,
                     function_ref<void()> K) {
    if (I == PN.Children.size()) {
      K();
      return;
    }
    EClassId Op = N.Ops[Swap ? N.Ops.size() - 1 - I : I];
    matchAt(PN.Children[I], Op, /*AllowRefine=*/true,
            [&] { matchChildren(PN, N, I + 1, Swap, K); });
  }

  const EGraph &G;
  const RewriteRule &R;
  SmallVectorImpl<RuleMatch> &Out;
  unsigned Limit;
  ACViewCache &Cache;
  RuleMatch Cur;
  std::set<std::vector<uint64_t>> Seen;
};
} // namespace

void llvm::egraph::matchRule(const EGraph &G, const RewriteRule &Rule,
                             SmallVectorImpl<RuleMatch> &Matches,
                             unsigned Limit, ACViewCache *Cache) {
  assert(G.isClean() && "rebuild() the e-graph before matching");
  std::optional<ACViewCache> LocalCache;
  if (!Cache) {
    SaturationLimits Defaults;
    LocalCache.emplace(G, Defaults.MaxACLeaves, Defaults.MaxACViews);
    Cache = &*LocalCache;
  }
  assert(&Cache->getGraph() == &G && "view cache of another graph");
  Matcher M(G, Rule, Matches, Limit, *Cache);
  for (EClassId Id : G.getClassIds()) {
    if (Matches.size() >= Limit)
      return;
    M.run(Id);
  }
}

//===----------------------------------------------------------------------===//
// Application
//===----------------------------------------------------------------------===//

namespace {
/// Instantiates a right-hand side. Types are derived from the operator
/// shapes: build() gets the type its position must have (invalid if the
/// position does not determine it, e.g. the operand of a cast), and
/// inferType() gives the type a pattern has by itself. An instantiation that
/// is not well-typed is rejected, which makes rules whose validity depends
/// on the types (e.g. the compositions of casts) self-guarding.
class Instantiator {
public:
  Instantiator(EGraph &G, const RewriteRule &R, const RuleMatch &M,
               ArrayRef<APInt> Computed)
      : G(G), R(R), M(M), Computed(Computed) {}

  std::optional<EClassId> build(unsigned PIdx, LLT Expected,
                                bool IsShiftAmount = false) {
    const PatNode &PN = R.getRHS().Nodes[PIdx];
    switch (PN.Kind) {
    case PatNode::Var: {
      if (M.isSumBound(PN.Index)) {
        const ACTerm &T = M.VarSums[PN.Index];
        LLT Ty = G.getType(T.Leaves[0]);
        if (Expected.isValid() && Ty != Expected)
          return std::nullopt;
        return G.addACTerm(T.Opcode, Ty, T.Leaves);
      }
      EClassId C = M.Vars[PN.Index];
      if (!IsShiftAmount && Expected.isValid() && G.getType(C) != Expected)
        return std::nullopt;
      return C;
    }
    case PatNode::Literal:
      if (!Expected.isValid() || !Expected.isScalar())
        return std::nullopt;
      return G.addConstant(Expected,
                           APInt(Expected.getSizeInBits(), PN.Value,
                                 /*isSigned=*/true, /*implicitTrunc=*/true));
    case PatNode::Computed:
      if (PN.Index >= Computed.size())
        return std::nullopt;
      return buildConstant(Computed[PN.Index], Expected,
                           /*MayResize=*/false);
    case PatNode::ConstVar: {
      const std::optional<APInt> &V = M.Consts[PN.Index];
      if (!V)
        return std::nullopt;
      // Only shift amounts may change width, and only if the value fits.
      return buildConstant(*V, Expected, /*MayResize=*/IsShiftAmount);
    }
    case PatNode::Op:
      return buildOp(PN, PIdx, Expected);
    }
    llvm_unreachable("bad pattern node");
  }

private:
  std::optional<EClassId> buildConstant(const APInt &V, LLT Expected,
                                        bool MayResize) {
    if (!Expected.isValid())
      return G.addConstant(LLT::scalar(V.getBitWidth()), V);
    if (!Expected.isScalar())
      return std::nullopt;
    unsigned Width = Expected.getSizeInBits();
    if (V.getBitWidth() == Width)
      return G.addConstant(Expected, V);
    if (!MayResize || V.getActiveBits() > Width)
      return std::nullopt;
    return G.addConstant(Expected, V.zextOrTrunc(Width));
  }

  /// The type of pattern \p PIdx if it can be told without context, else an
  /// invalid type.
  LLT inferType(unsigned PIdx) const {
    const PatNode &PN = R.getRHS().Nodes[PIdx];
    switch (PN.Kind) {
    case PatNode::Var:
      if (M.isSumBound(PN.Index))
        return G.getType(M.VarSums[PN.Index].Leaves[0]);
      return G.getType(M.Vars[PN.Index]);
    case PatNode::Literal:
      return LLT();
    case PatNode::Computed:
      if (PN.Index >= Computed.size())
        return LLT();
      return LLT::scalar(Computed[PN.Index].getBitWidth());
    case PatNode::ConstVar:
      if (!M.Consts[PN.Index])
        return LLT();
      return LLT::scalar(M.Consts[PN.Index]->getBitWidth());
    case PatNode::Op:
      break;
    }
    const OpProperties *P = getOpProperties(PN.Opcode);
    switch (P->Shape) {
    case OpShape::Binary: {
      LLT Ty = inferType(PN.Children[0]);
      return Ty.isValid() || P->IsShift ? Ty : inferType(PN.Children[1]);
    }
    case OpShape::Unary:
    case OpShape::PtrAdd:
      return inferType(PN.Children[0]);
    case OpShape::Compare:
      return LLT::scalar(1);
    case OpShape::Select: {
      LLT Ty = inferType(PN.Children[1]);
      return Ty.isValid() ? Ty : inferType(PN.Children[2]);
    }
    case OpShape::Cast:
    case OpShape::BitCount:
    case OpShape::Phi:
    case OpShape::Effect:
      break;
    }
    return LLT();
  }

  std::optional<EClassId> buildOp(const PatNode &PN, unsigned PIdx,
                                  LLT Expected) {
    const OpProperties *P = getOpProperties(PN.Opcode);
    LLT Ty = Expected.isValid() ? Expected : inferType(PIdx);
    SmallVector<EClassId, 3> Ops;
    // Build operand \p I with the given type; false if that fails.
    auto Operand = [&](unsigned I, LLT OpTy, bool IsShiftAmount = false) {
      std::optional<EClassId> C = build(PN.Children[I], OpTy, IsShiftAmount);
      if (C)
        Ops.push_back(*C);
      return C.has_value();
    };

    switch (P->Shape) {
    case OpShape::Binary:
      if (!Ty.isValid() || !Ty.isScalar() || !Operand(0, Ty) ||
          !Operand(1, Ty, /*IsShiftAmount=*/P->IsShift))
        return std::nullopt;
      if (P->IsShift) {
        // RHS shifts must not be able to create poison.
        std::optional<APInt> Amt = G.getConstant(Ops[1]);
        if (!Amt || Amt->uge(Ty.getSizeInBits()))
          return std::nullopt;
      }
      break;
    case OpShape::Unary:
      if (!Ty.isValid() || !Ty.isScalar() || !Operand(0, Ty))
        return std::nullopt;
      break;
    case OpShape::Cast:
    case OpShape::BitCount: {
      // The result type comes from the context, the source type from the
      // operand.
      if (!Ty.isValid() || !Ty.isScalar() || !Operand(0, LLT()))
        return std::nullopt;
      LLT SrcTy = G.getType(Ops[0]);
      if (!SrcTy.isScalar())
        return std::nullopt;
      unsigned Width = Ty.getSizeInBits(), SrcWidth = SrcTy.getSizeInBits();
      if (P->Cast == CastKind::Truncate
              ? Width >= SrcWidth
              : P->Cast != CastKind::None && Width <= SrcWidth)
        return std::nullopt;
      break;
    }
    case OpShape::Compare: {
      if (Ty != LLT::scalar(1))
        return std::nullopt;
      LLT OpTy = inferType(PN.Children[0]);
      if (!OpTy.isValid())
        OpTy = inferType(PN.Children[1]);
      if (!OpTy.isValid() || !Operand(0, OpTy) || !Operand(1, OpTy))
        return std::nullopt;
      break;
    }
    case OpShape::Select:
      if (!Ty.isValid() || !Operand(0, LLT::scalar(1)) || !Operand(1, Ty) ||
          !Operand(2, Ty))
        return std::nullopt;
      break;
    case OpShape::PtrAdd: {
      if (!Ty.isValid() || !Ty.isPointer() || !Operand(0, Ty))
        return std::nullopt;
      LLT OffsetTy = inferType(PN.Children[1]);
      if (!OffsetTy.isValid())
        OffsetTy = LLT::scalar(Ty.getSizeInBits());
      if (!OffsetTy.isScalar() || !Operand(1, OffsetTy))
        return std::nullopt;
      break;
    }
    case OpShape::Phi:
      return std::nullopt;
    case OpShape::Effect:
      if (Expected.isValid())
        return std::nullopt;
      Ty = LLT();
      for (unsigned I = 0, E = PN.Children.size(); I != E; ++I)
        if (!Operand(I, LLT()))
          return std::nullopt;
      break;
    }

    // A division is only created if it cannot trap, or if the matched
    // pattern contains a division that traps in (at least) the same cases.
    if (P->MayTrap && !isCoveredDivision(*P, Ops))
      return std::nullopt;

    uint64_t Attr = PN.Attr;
    if (PN.AttrKind == PatNode::InvertedRootAttr) {
      std::optional<uint64_t> Inverted = P->InvertAttr(M.RootAttr);
      if (!Inverted)
        return std::nullopt;
      Attr = *Inverted;
    }
    return G.addOp(PN.Opcode, Ty, Ops, /*Flags=*/0, Attr);
  }

  bool isCoveredDivision(const OpProperties &P, ArrayRef<EClassId> Ops) const {
    if (isDefinedDivision(G, P, ENode::makeOp(P.Opcode, LLT(), Ops)))
      return true;
    return any_of(M.Guards, [&](const RuleMatch::DivGuard &Guard) {
      if (!G.equivalent(Guard.Divisor, Ops[1]))
        return false;
      // A zero divisor is the only way an unsigned division traps. A signed
      // one also overflows, which depends on the dividend.
      return !P.IsSigned ||
             (Guard.Signed && G.equivalent(Guard.Dividend, Ops[0]));
    });
  }

  EGraph &G;
  const RewriteRule &R;
  const RuleMatch &M;
  ArrayRef<APInt> Computed;
};
} // namespace

ApplyResult llvm::egraph::applyMatch(EGraph &G, const RewriteRule &Rule,
                                     const RuleMatch &M) {
  SmallVector<APInt, 2> Computed;
  if (Rule.getApplyFn() && !Rule.getApplyFn()(G, M, Computed))
    return ApplyResult::Rejected;
  bool Exact = !M.ViaRefinement && Rule.isExactFor(G, M);
  if (!Exact && !Rule.isRefinementFor(G, M))
    return ApplyResult::Unsafe;
  // An instantiation that is not well-typed, or that could create poison or
  // undefined behaviour, is rejected.
  LLT RootTy = G.getType(M.Root);
  std::optional<EClassId> New =
      Instantiator(G, Rule, M, Computed).build(Rule.getRHS().Root, RootTy);
  if (!New || G.getType(*New) != RootTy)
    return ApplyResult::Rejected;
  if (!M.Rest.empty()) {
    // The root is LHS op Rest, so it is related to RHS op Rest.
    SmallVector<EClassId, 8> Leaves(M.Rest.Leaves.begin(), M.Rest.Leaves.end());
    Leaves.push_back(*New);
    New = G.addACTerm(M.Rest.Opcode, G.getType(M.Root), Leaves);
  }
  if (Exact)
    return G.merge(M.Root, *New) ? ApplyResult::Merged : ApplyResult::NoChange;
  return G.addRefinement(M.Root, *New) ? ApplyResult::Refined
                                       : ApplyResult::NoChange;
}

SaturationStats llvm::egraph::saturate(EGraph &G, ArrayRef<RewriteRule> Rules,
                                       const SaturationLimits &Limits) {
  SaturationStats Stats;
  Stats.RuleApplications.assign(Rules.size(), 0);
  G.rebuild();
  // Associativity and commutativity are not rules but a canonical form.
  auto CanonicalizeAC = [&] {
    if (unsigned N = G.canonicalizeAC(Limits.MaxACLeaves, Limits.MaxNodes)) {
      Stats.ACMerges += N;
      G.rebuild();
    }
  };
  // Neither is op(a, ..., a) == a for PHIs.
  auto CollapsePhis = [&] {
    if (unsigned N = G.collapseIdempotentPhis()) {
      Stats.PhiMerges += N;
      G.rebuild();
    }
  };
  CanonicalizeAC();
  CollapsePhis();
  SmallVector<unsigned, 32> TimesBanned(Rules.size(), 0);
  SmallVector<unsigned, 32> BannedUntil(Rules.size(), 0);
  for (unsigned Iter = 0; Iter < Limits.MaxIterations; ++Iter) {
    ++Stats.Iterations;
    // Read phase: collect matches for all rules on the current graph.
    SmallVector<std::pair<unsigned, RuleMatch>, 64> All;
    ACViewCache Views(G, Limits.MaxACLeaves, Limits.MaxACViews);
    unsigned Budget = Limits.MaxMatchesPerIteration;
    bool AnyBanned = false;
    for (unsigned RI = 0, RE = Rules.size(); RI != RE && Budget; ++RI) {
      if (Iter < BannedUntil[RI]) {
        AnyBanned = true;
        continue;
      }
      unsigned Threshold = ~0u;
      if (Limits.RuleMatchLimit)
        Threshold = Limits.RuleMatchLimit << std::min(TimesBanned[RI], 16u);
      SmallVector<RuleMatch, 16> Ms;
      // Ask for one match more than the threshold to detect an overflow.
      matchRule(G, Rules[RI], Ms,
                Threshold == ~0u ? Budget : std::min(Budget, Threshold + 1),
                &Views);
      if (Ms.size() > Threshold) {
        BannedUntil[RI] =
            Iter + (Limits.RuleBanLength << std::min(TimesBanned[RI], 16u));
        ++TimesBanned[RI];
        ++Stats.Bans;
        AnyBanned = true;
        continue;
      }
      Budget -= Ms.size();
      for (RuleMatch &M : Ms)
        All.push_back({RI, std::move(M)});
    }
    if (!Budget)
      Stats.HitMatchLimit = true;
    Stats.Matches += All.size();

    // Write phase.
    bool Changed = false;
    unsigned ClassesBefore = G.getNumClasses() + G.getNumNodes();
    for (auto &[RI, M] : All) {
      if (G.getNumNodes() >= Limits.MaxNodes) {
        Stats.HitNodeLimit = true;
        break;
      }
      switch (applyMatch(G, Rules[RI], M)) {
      case ApplyResult::Merged:
        ++Stats.Merges;
        ++Stats.RuleApplications[RI];
        Changed = true;
        break;
      case ApplyResult::Refined:
        ++Stats.Refinements;
        ++Stats.RuleApplications[RI];
        Changed = true;
        break;
      case ApplyResult::Unsafe:
        ++Stats.RejectedUnsafe;
        break;
      case ApplyResult::NoChange:
      case ApplyResult::Rejected:
        break;
      }
    }
    G.rebuild();
    CanonicalizeAC();
    CollapsePhis();
    if (G.getNumClasses() + G.getNumNodes() != ClassesBefore)
      Changed = true;
    if (Stats.HitNodeLimit)
      break;
    // With banned rules the graph is not saturated yet: keep going (within
    // the iteration limit) until the bans expire.
    if (!Changed && !AnyBanned) {
      Stats.Saturated = true;
      break;
    }
  }
  if (!Stats.Saturated && !Stats.HitNodeLimit &&
      Stats.Iterations >= Limits.MaxIterations)
    Stats.HitIterationLimit = true;
  return Stats;
}

//===----------------------------------------------------------------------===//
// Extraction
//===----------------------------------------------------------------------===//

CostModel::~CostModel() = default;

unsigned CostModel::getNodeCost(const ENode &N) const {
  return N.isOperation() ? 1 : 0;
}

unsigned DefaultCostModel::getNodeCost(const ENode &N) const {
  switch (N.Kind) {
  case ENodeKind::Input:
    return InputCost;
  case ENodeKind::Constant:
    return ConstantCost;
  case ENodeKind::Operation:
    break;
  }
  const OpProperties *P = getOpProperties(N.Opcode);
  unsigned Base = SimpleOpCost;
  if (N.Opcode == TargetOpcode::G_MUL)
    Base = MulCost;
  else if (P && P->MayTrap)
    Base = DivCost;
  if (ScaleByWidth && N.Ty.isValid())
    Base *= std::max<unsigned>(1, (N.Ty.getSizeInBits() + 31) / 32);
  return std::max(1u, Base);
}

static uint64_t addCost(uint64_t A, uint64_t B) {
  if (A == Extractor::Infinite || B == Extractor::Infinite)
    return Extractor::Infinite;
  uint64_t S = A + B;
  return S < A ? Extractor::Infinite : S;
}

Extractor::Extractor(const EGraph &G, const CostModel &CM) : G(G) {
  assert(G.isClean() && "rebuild() the e-graph before extraction");
  SmallVector<EClassId, 32> Ids = G.getClassIds();
  EClassId MaxId = Ids.empty() ? 0 : Ids.back();
  Choices.assign(MaxId + 1, Choice());

  auto LocalCost = [&](const ENode &N) -> uint64_t {
    uint64_t C = CM.getNodeCost(N);
    if (N.isOperation())
      C = std::max<uint64_t>(C, 1); // Guarantees acyclic choices.
    return C;
  };
  auto NodeCost = [&](const ENode &N) -> uint64_t {
    uint64_t C = LocalCost(N);
    for (EClassId Op : N.Ops)
      C = addCost(C, Choices[G.find(Op)].Cost);
    return C;
  };

  // Bellman-Ford style fixpoint. Costs only decrease, so this terminates.
  // Refinement edges are only taken when strictly cheaper, which (together
  // with operation costs >= 1) guarantees that choices are acyclic.
  bool Changed = true;
  while (Changed) {
    Changed = false;
    for (EClassId Id : Ids) {
      const EClass &C = G.getClass(Id);
      Choice &Cur = Choices[Id];
      for (unsigned NI = 0, NE = C.Nodes.size(); NI != NE; ++NI) {
        uint64_t Cost = NodeCost(C.Nodes[NI]);
        if (Cost < Cur.Cost) {
          Cur.Cost = Cost;
          Cur.LocalCost = LocalCost(C.Nodes[NI]);
          Cur.NodeIdx = NI;
          Changed = true;
        }
      }
      for (EClassId R : C.RefinesTo) {
        uint64_t Cost = Choices[G.find(R)].Cost;
        if (Cost < Cur.Cost) {
          Cur.Cost = Cost;
          Cur.LocalCost = 0;
          Cur.NodeIdx = -1;
          Cur.RefTarget = G.find(R);
          Changed = true;
        }
      }
    }
  }
}

uint64_t Extractor::getTreeCost(EClassId Id) const {
  return Choices[resolve(Id)].Cost;
}

EClassId Extractor::resolve(EClassId Id) const {
  Id = G.find(Id);
  for (unsigned Steps = 0; Steps < Choices.size(); ++Steps) {
    const Choice &C = Choices[Id];
    if (C.NodeIdx >= 0 || C.Cost == Infinite)
      return Id;
    Id = G.find(C.RefTarget);
  }
  llvm_unreachable("cycle in refinement choices");
}

const ENode *Extractor::getChosenNode(EClassId Id) const {
  Id = resolve(Id);
  const Choice &C = Choices[Id];
  if (C.NodeIdx < 0)
    return nullptr;
  return &G.getClass(Id).Nodes[C.NodeIdx];
}

uint64_t Extractor::getDagCost(ArrayRef<EClassId> Roots) const {
  DenseSet<EClassId> Visited;
  SmallVector<EClassId, 16> Work;
  for (EClassId R : Roots)
    Work.push_back(resolve(R));
  uint64_t Total = 0;
  while (!Work.empty()) {
    EClassId Id = Work.pop_back_val();
    if (!Visited.insert(Id).second)
      continue;
    const ENode *N = getChosenNode(Id);
    if (!N)
      return Infinite;
    Total = addCost(Total, Choices[Id].LocalCost);
    for (EClassId Op : N->Ops)
      Work.push_back(resolve(Op));
  }
  return Total;
}

void Extractor::printExpr(
    raw_ostream &OS, EClassId Id,
    function_ref<void(raw_ostream &, unsigned)> PrintInput) const {
  const ENode *N = getChosenNode(Id);
  if (!N) {
    OS << "<none>";
    return;
  }
  switch (N->Kind) {
  case ENodeKind::Input:
    if (PrintInput)
      PrintInput(OS, N->InputIdx);
    else
      OS << "%in" << N->InputIdx;
    return;
  case ENodeKind::Constant:
    N->Imm.print(OS, /*isSigned=*/true);
    return;
  case ENodeKind::Operation:
    OS << "(" << getOpcodeName(N->Opcode);
    printAttr(OS, N->Opcode, N->Attr);
    if (N->Flags)
      OS << "<flags:" << N->Flags << ">";
    for (EClassId Op : N->Ops) {
      OS << " ";
      printExpr(OS, Op, PrintInput);
    }
    OS << ")";
    return;
  }
}

std::string Extractor::getExprString(EClassId Id) const {
  std::string S;
  raw_string_ostream OS(S);
  printExpr(OS, Id);
  return S;
}
