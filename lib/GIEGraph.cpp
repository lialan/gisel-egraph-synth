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

static std::vector<OpProperties> buildOpProperties() {
  using namespace TargetOpcode;
  std::vector<OpProperties> T;
  auto Op = [&](unsigned Opc, const char *Name, const char *Short) {
    T.emplace_back();
    OpProperties &P = T.back();
    P.Opcode = Opc;
    P.Name = Name;
    P.ShortName = Short;
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

/// Every operator in the property table is, without flags, poison iff an
/// operand is poison (for shifts: provided the amount is a constant in
/// range), and never produces undef from defined operands (see
/// OpProperties).
static bool isPoisonPropagatingOnly(unsigned Opc) {
  return getOpProperties(Opc) != nullptr;
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
                    uint32_t Flags) {
  ENode N;
  N.Kind = ENodeKind::Operation;
  N.Opcode = Opcode;
  N.Ty = Ty;
  N.Flags = Flags;
  N.Ops.assign(Ops.begin(), Ops.end());
  return N;
}

bool ENode::operator==(const ENode &O) const {
  if (Kind != O.Kind || Opcode != O.Opcode || Flags != O.Flags || Ty != O.Ty)
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
                             N.Ty.getUniqueRAWLLTData());
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
                       uint32_t Flags) {
  return add(ENode::makeOp(Opcode, Ty, Ops, Flags));
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
  if (C.isOperation() && C.Ops.size() == 2 && C.Ops[0] > C.Ops[1]) {
    const OpProperties *P = getOpProperties(C.Opcode);
    if (P && P->Commutative)
      std::swap(C.Ops[0], C.Ops[1]);
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
  case ENodeKind::Operation:
    if (!isPoisonPropagatingOnly(N.Opcode))
      return false;
    return all_of(N.Ops, [&](EClassId Op) { return getClass(Op).NotUndef; });
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
    if (N.Flags != 0 || !isPoisonPropagatingOnly(N.Opcode))
      return false;
    if (isShift(N.Opcode)) {
      const std::optional<APInt> &Amt = getClass(N.Ops[1]).Const;
      if (!Amt || Amt->uge(N.Ty.getScalarSizeInBits()))
        return false;
    }
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
      StringRef OpName = token();
      std::optional<unsigned> Opc = getOpcodeByName(OpName);
      if (!Opc)
        error(Twine("unknown opcode '") + OpName + "'");
      N.Kind = PatNode::Op;
      N.Opcode = *Opc;
      while (true) {
        skipWS();
        if (Text.consume_front(")"))
          break;
        N.Children.push_back(parseNode(P));
      }
      if (N.Children.size() != 2)
        error("only binary operations are supported");
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

  StringRef RuleName;
  StringRef Text;
  bool IsRHS;
  std::vector<std::string> &VarNames;
  std::vector<std::string> &ConstNames;
};
} // namespace

static void countVarOccurrences(const Pattern &P,
                                SmallVectorImpl<unsigned> &Occ) {
  for (const PatNode &N : P.Nodes)
    if (N.Kind == PatNode::Var)
      ++Occ[N.Index];
}

RewriteRule::RewriteRule(StringRef Name, StringRef LHSText, StringRef RHSText,
                         ApplyFn Fn)
    : Name(Name.str()), Fn(std::move(Fn)) {
  LHS = PatternParser(Name, LHSText, /*IsRHS=*/false, VarNames, ConstNames)
            .parse();
  RHS = PatternParser(Name, RHSText, /*IsRHS=*/true, VarNames, ConstNames)
            .parse();
  if (LHS.Nodes[LHS.Root].Kind != PatNode::Op)
    report_fatal_error(Twine("GIEGraph rule '") + Name +
                       "': left-hand side must be an operation");
  OccL.assign(VarNames.size(), 0);
  OccR.assign(VarNames.size(), 0);
  countVarOccurrences(LHS, OccL);
  countVarOccurrences(RHS, OccR);
}

// Soundness of a rule instance (see the design document):
//  * All operators appearing in the patterns are unflagged and propagate
//    poison exactly (shift amounts are constants in range), so each side is
//    poison iff one of the variables it mentions is poison.
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
    unsigned L = OccL[V], R = OccR[V];
    if (R == 0) {
      // The variable is dropped: LHS is poison when it is, RHS is not.
      if (!C.NotPoison)
        return false;
      if (L > 1 && !C.NotUndef)
        return false;
    } else if (!(L == 1 && R == 1) && !C.NotUndef) {
      return false;
    }
  }
  return true;
}

bool RewriteRule::isRefinementFor(const EGraph &G, const RuleMatch &M) const {
  // RHS variables are a subset of LHS variables, so RHS poison implies LHS
  // poison. Using a variable at most once on the RHS picks one point of the
  // diagonal of the LHS' possible values.
  for (unsigned V = 0, E = VarNames.size(); V != E; ++V)
    if (OccR[V] > 1 && !getBindingFacts(G, M, V).NotUndef)
      return false;
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
    matchStructural(PN, C, IsRoot, K);
    if (!AllowRefine)
      return;
    SmallVector<EClassId, 4> Closure = G.getRefinementClosure(C);
    if (Closure.empty())
      return;
    bool Saved = Cur.ViaRefinement;
    Cur.ViaRefinement = true;
    for (EClassId D : Closure)
      matchStructural(PN, D, /*IsRoot=*/false, K);
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

  void matchStructural(const PatNode &PN, EClassId C, bool IsRoot,
                       function_ref<void()> K) {
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
      for (const ENode &N : Cls.Nodes) {
        if (full())
          return;
        if (!N.isOperation() || N.Opcode != PN.Opcode ||
            N.Ops.size() != PN.Children.size())
          continue;
        if (isShift(N.Opcode)) {
          // Only shifts that cannot create poison are rewritten.
          const std::optional<APInt> &Amt = G.getClass(N.Ops[1]).Const;
          if (!Amt || Amt->uge(N.Ty.getScalarSizeInBits()))
            continue;
        }
        // A flagged operation (nuw/nsw/exact/disjoint) is refined by the
        // same operation without flags: the flags only add poison. Matching
        // it as the unflagged operator is therefore sound, but the result
        // can only justify a refinement, never a merge.
        bool Saved = Cur.ViaRefinement;
        if (N.Flags)
          Cur.ViaRefinement = true;
        matchChildren(PN, N, 0, /*Swap=*/false, K);
        // Commutative operations are stored in one canonical operand order
        // (see EGraph::canonicalize), so also match the other order.
        if (N.Ops.size() == 2 && N.Ops[0] != N.Ops[1]) {
          const OpProperties *P = getOpProperties(N.Opcode);
          if (P && P->Commutative)
            matchChildren(PN, N, 0, /*Swap=*/true, K);
        }
        Cur.ViaRefinement = Saved;
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
/// Instantiates a right-hand side. All non-amount positions have the root
/// type; computed/literal constants get the type of their position.
class Instantiator {
public:
  Instantiator(EGraph &G, const RewriteRule &R, const RuleMatch &M,
               ArrayRef<APInt> Computed)
      : G(G), R(R), M(M), Computed(Computed), Ty(G.getType(M.Root)) {}

  std::optional<EClassId> build(unsigned PIdx, bool IsShiftAmount) {
    const PatNode &PN = R.getRHS().Nodes[PIdx];
    unsigned Width = Ty.getSizeInBits();
    switch (PN.Kind) {
    case PatNode::Var: {
      if (M.isSumBound(PN.Index)) {
        const ACTerm &T = M.VarSums[PN.Index];
        if (G.getType(T.Leaves[0]) != Ty)
          return std::nullopt;
        return G.addACTerm(T.Opcode, Ty, T.Leaves);
      }
      EClassId C = M.Vars[PN.Index];
      if (!IsShiftAmount && G.getType(C) != Ty)
        return std::nullopt;
      return C;
    }
    case PatNode::Literal:
      return G.addConstant(Ty, APInt(Width, PN.Value, /*isSigned=*/true,
                                     /*implicitTrunc=*/true));
    case PatNode::Computed:
      if (PN.Index >= Computed.size() ||
          Computed[PN.Index].getBitWidth() != Width)
        return std::nullopt;
      return G.addConstant(Ty, Computed[PN.Index]);
    case PatNode::ConstVar: {
      const std::optional<APInt> &V = M.Consts[PN.Index];
      if (!V)
        return std::nullopt;
      if (V->getBitWidth() != Width) {
        // Only shift amounts may change width, and only if the value fits.
        if (!IsShiftAmount || V->getActiveBits() > Width)
          return std::nullopt;
        return G.addConstant(Ty, V->zextOrTrunc(Width));
      }
      return G.addConstant(Ty, *V);
    }
    case PatNode::Op: {
      SmallVector<EClassId, 2> Ops;
      for (unsigned I = 0, E = PN.Children.size(); I != E; ++I) {
        bool Amt = isShift(PN.Opcode) && I == 1;
        std::optional<EClassId> C = build(PN.Children[I], Amt);
        if (!C)
          return std::nullopt;
        Ops.push_back(*C);
      }
      if (isShift(PN.Opcode)) {
        // RHS shifts must not be able to create poison.
        std::optional<APInt> Amt = G.getConstant(Ops[1]);
        if (!Amt || Amt->uge(Width))
          return std::nullopt;
      }
      return G.addOp(PN.Opcode, Ty, Ops);
    }
    }
    llvm_unreachable("bad pattern node");
  }

private:
  EGraph &G;
  const RewriteRule &R;
  const RuleMatch &M;
  ArrayRef<APInt> Computed;
  LLT Ty;
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
  // Check shift amounts in the RHS before creating any node, so a rejected
  // instantiation leaves the graph untouched as far as possible.
  std::optional<EClassId> New =
      Instantiator(G, Rule, M, Computed)
          .build(Rule.getRHS().Root, /*IsShiftAmount=*/false);
  if (!New)
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
  CanonicalizeAC();
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
  unsigned Base = N.Opcode == TargetOpcode::G_MUL ? MulCost : SimpleOpCost;
  if (ScaleByWidth)
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
