//===- GIEGraphLinear.cpp - Linear forms modulo 2^W in the e-graph --------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// The linear view of an integer class (see applyLinearViews in GIEGraph.h
/// and docs/TargetAwareViews.md).
///
/// A class of integers is seen as the linear form `c + sum(k_i * t_i)` modulo
/// 2^W, where W is the width of the integer (of the element of a fixed
/// vector, lane by lane). The decomposition goes through the unflagged
/// operators G_ADD, G_SUB, G_MUL with a constant operand and G_SHL by a
/// constant smaller than W; everything else is a leaf t_i: inputs, other
/// operators, flagged nodes, products of two non-constants, shifts by a
/// variable or out-of-range amount, casts. The coefficients and the constant
/// are computed with APInt in the width W, so they wrap around exactly like
/// the operators.
///
/// Soundness: when every read of every leaf is the same value that is
/// neither undef nor poison, the class and each implementation of its form
/// compute the same polynomial of degree one in the ring of integers modulo
/// 2^W (a shift by s < W multiplies by 2^s). Both sides use only operators
/// without poison-generating flags, with constant shift amounts in range and
/// without division, so each side is poison iff a leaf that it reads is
/// poison. These are the preconditions of classifyLeafReads, which decides
/// from the number of reads of each leaf on each side whether the class may
/// be merged with an implementation, only refined to it, or neither.
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GIEGraph.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include <map>

using namespace llvm;
using namespace llvm::egraph;

namespace {

/// The types of the view: integer scalars, and fixed vectors of integers
/// (lane by lane, never as one wide integer).
bool isLinearType(LLT Ty) {
  if (!Ty.isValid())
    return false;
  if (Ty.isScalar())
    return !Ty.isFloat();
  return Ty.isFixedVector() && Ty.getElementType().isScalar() &&
         !Ty.getElementType().isFloat();
}

bool isLinearOpcode(unsigned Opc) {
  switch (Opc) {
  case TargetOpcode::G_ADD:
  case TargetOpcode::G_SUB:
  case TargetOpcode::G_MUL:
  case TargetOpcode::G_SHL:
    return true;
  default:
    return false;
  }
}

/// A leaf of a linear form with its coefficient and the number of times
/// that the decomposition reads it.
struct LinearTerm {
  EClassId Leaf;
  APInt Coeff;
  unsigned Reads;
};

/// The linear form `Const + sum(Coeff_i * Leaf_i)` of a class.
struct LinearForm {
  EClassId Class = 0;
  LLT Ty;
  APInt Const;
  /// In increasing order of the canonical class ids of the leaves. A
  /// coefficient may be zero: the decomposition still reads the leaf.
  SmallVector<LinearTerm, 8> Terms;
  /// The linear operators and the constant addends of the decomposition.
  unsigned NumOps = 0, NumConsts = 0;
};

/// A node of a class that the decomposition goes through, and the constant
/// factor that a G_MUL or G_SHL applies to its operand \p Operand.
struct LinearNode {
  const ENode *N = nullptr;
  APInt Factor;
  unsigned Operand = 0;
};

/// Computes the linear form of one class on a clean graph.
///
/// The decomposition of a class goes through its first linear node (in the
/// order of the class) and the decompositions of the operand classes. A
/// class is a leaf if it has no linear node, if it is being decomposed
/// already (it is on the path), or if its decomposition has a leaf that is
/// the class itself or uses it as an operand: such a cycle, e.g.
/// x == (x + x) + (0 - x) after a merge, only restates the class (the same
/// rule as for the AC flattening, EGraph::flattenAC).
class Decomposer {
public:
  enum StatusKind { Ok, NoLinearNode, OverBudget, Unsupported };

  Decomposer(const EGraph &G, const SaturationLimits &Limits, LLT Ty)
      : G(G), Limits(Limits), Ty(Ty), W(Ty.getScalarSizeInBits()) {}

  StatusKind run(EClassId Root);
  LinearForm takeForm(EClassId Root);

private:
  struct LeafInfo {
    APInt Coeff;
    unsigned Reads;
  };
  /// The form of one subexpression.
  struct Partial {
    APInt Const;
    /// Ordered by class id (deterministic).
    std::map<EClassId, LeafInfo> Leaves;
    unsigned NumOps = 0, NumConsts = 0;
  };

  std::optional<LinearNode> getLinearNode(EClassId C);
  bool isNonSplatConstant(EClassId C) const;
  bool isCycle(const Partial &P, EClassId C) const;
  void addLeaf(Partial &Out, EClassId C, const APInt &Coeff, unsigned Reads);
  void visitClass(EClassId C, const APInt &Scale, Partial &Out);
  void visitNode(const LinearNode &LN, Partial &Out);

  const EGraph &G;
  const SaturationLimits &Limits;
  LLT Ty;
  unsigned W;
  Partial Result;
  /// The classes being decomposed.
  SmallVector<EClassId, 8> Path;
  unsigned Visits = 0;
  StatusKind Status = Ok;
};

/// The first node of \p C, in the order of the class, that the decomposition
/// goes through. A G_MUL or G_SHL whose constant operand is a vector constant
/// that is not a splat would need a coefficient per lane: if the class has
/// no other linear node, the view is not supported.
std::optional<LinearNode> Decomposer::getLinearNode(EClassId C) {
  bool NonSplat = false;
  for (const ENode &N : G.getClass(C).Nodes) {
    if (!N.isOperation() || N.Flags || !isLinearOpcode(N.Opcode) ||
        N.Ty != Ty || N.Ops.size() != 2)
      continue;
    switch (N.Opcode) {
    case TargetOpcode::G_ADD:
    case TargetOpcode::G_SUB:
      return LinearNode{&N, APInt(W, 1), 0};
    case TargetOpcode::G_MUL:
      for (unsigned I : {1u, 0u}) {
        std::optional<APInt> K = G.getSplatConstant(N.Ops[I]);
        if (K && K->getBitWidth() == W)
          return LinearNode{&N, *K, 1 - I};
      }
      NonSplat |= isNonSplatConstant(N.Ops[0]) || isNonSplatConstant(N.Ops[1]);
      continue;
    case TargetOpcode::G_SHL: {
      // A shift by W or more is poison: the node is not linear.
      std::optional<APInt> Amt = G.getSplatConstant(N.Ops[1]);
      if (Amt && Amt->ult(W))
        return LinearNode{&N, APInt::getOneBitSet(W, Amt->getZExtValue()), 0};
      NonSplat |= !Amt && isNonSplatConstant(N.Ops[1]);
      continue;
    }
    default:
      continue;
    }
  }
  if (NonSplat)
    Status = Unsupported;
  return std::nullopt;
}

/// True if \p C is a fixed vector whose lanes are constants that are not all
/// equal.
bool Decomposer::isNonSplatConstant(EClassId C) const {
  LLT CTy = G.getType(C);
  if (!CTy.isFixedVector() || G.getSplatConstant(C))
    return false;
  for (unsigned I = 0, E = CTy.getNumElements(); I != E; ++I)
    if (G.getLaneConstant(C, I).Kind != LaneConstant::Constant)
      return false;
  return true;
}

/// True if a leaf of \p P is \p C or uses \p C as an operand.
bool Decomposer::isCycle(const Partial &P, EClassId C) const {
  return any_of(P.Leaves, [&](const auto &Leaf) {
    return Leaf.first == C ||
           any_of(G.getClass(Leaf.first).Nodes, [&](const ENode &M) {
             return any_of(M.Ops, [&](EClassId Op) { return G.find(Op) == C; });
           });
  });
}

void Decomposer::addLeaf(Partial &Out, EClassId C, const APInt &Coeff,
                         unsigned Reads) {
  auto [It, Inserted] = Out.Leaves.try_emplace(C, LeafInfo{APInt(W, 0), 0});
  It->second.Coeff += Coeff;
  It->second.Reads += Reads;
  if (Out.Leaves.size() > Limits.MaxViewTerms)
    Status = OverBudget;
}

/// Add \p Scale times the form of \p C to \p Out.
void Decomposer::visitClass(EClassId C, const APInt &Scale, Partial &Out) {
  if (Status != Ok)
    return;
  if (++Visits > Limits.MaxViewVisits) {
    Status = OverBudget;
    return;
  }
  C = G.find(C);
  if (std::optional<APInt> K = G.getSplatConstant(C)) {
    if (K->getBitWidth() != W) {
      Status = Unsupported;
      return;
    }
    Out.Const += Scale * *K;
    ++Out.NumConsts;
    return;
  }
  if (isNonSplatConstant(C)) {
    Status = Unsupported;
    return;
  }
  std::optional<LinearNode> LN;
  if (!is_contained(Path, C))
    LN = getLinearNode(C);
  if (Status != Ok)
    return;
  if (LN) {
    Partial Sub;
    Sub.Const = APInt(W, 0);
    Path.push_back(C);
    visitNode(*LN, Sub);
    Path.pop_back();
    if (Status != Ok)
      return;
    if (!isCycle(Sub, C)) {
      Out.Const += Scale * Sub.Const;
      Out.NumOps += Sub.NumOps;
      Out.NumConsts += Sub.NumConsts;
      for (const auto &[Leaf, Info] : Sub.Leaves)
        addLeaf(Out, Leaf, Scale * Info.Coeff, Info.Reads);
      return;
    }
  }
  addLeaf(Out, C, Scale, 1);
}

void Decomposer::visitNode(const LinearNode &LN, Partial &Out) {
  const ENode &N = *LN.N;
  ++Out.NumOps;
  APInt One(W, 1);
  switch (N.Opcode) {
  case TargetOpcode::G_ADD:
    visitClass(N.Ops[0], One, Out);
    visitClass(N.Ops[1], One, Out);
    return;
  case TargetOpcode::G_SUB:
    visitClass(N.Ops[0], One, Out);
    visitClass(N.Ops[1], -One, Out);
    return;
  default:
    // G_MUL and G_SHL: a constant factor of one operand.
    visitClass(N.Ops[LN.Operand], LN.Factor, Out);
    return;
  }
}

Decomposer::StatusKind Decomposer::run(EClassId Root) {
  std::optional<LinearNode> LN = getLinearNode(Root);
  if (Status != Ok)
    return Status;
  if (!LN)
    return NoLinearNode;
  Visits = 1;
  Result.Const = APInt(W, 0);
  Path.push_back(Root);
  visitNode(*LN, Result);
  Path.pop_back();
  // A decomposition that reaches the class itself only restates it.
  if (Status == Ok && isCycle(Result, Root))
    return NoLinearNode;
  return Status;
}

LinearForm Decomposer::takeForm(EClassId Root) {
  LinearForm F;
  F.Class = Root;
  F.Ty = Ty;
  F.Const = Result.Const;
  F.NumOps = Result.NumOps;
  F.NumConsts = Result.NumConsts;
  for (const auto &[Leaf, Info] : Result.Leaves)
    F.Terms.push_back({Leaf, Info.Coeff, Info.Reads});
  return F;
}

//===----------------------------------------------------------------------===//
// Implementations of a form
//===----------------------------------------------------------------------===//

/// How the canonical implementation computes `k * t` for k != 0: t, t << s,
/// or t * k, added (k = 1, 2^s, otherwise) or subtracted (k = -1, -2^s).
struct TermPlan {
  enum KindTy : uint8_t { Plain, Shift, Mul } Kind;
  bool Negative;
  unsigned Amount;
};

TermPlan planTerm(const APInt &K) {
  if (K.isOne())
    return {TermPlan::Plain, false, 0};
  if (K.isPowerOf2())
    return {TermPlan::Shift, false, K.logBase2()};
  APInt Neg = -K;
  if (Neg.isOne())
    return {TermPlan::Plain, true, 0};
  if (Neg.isPowerOf2())
    return {TermPlan::Shift, true, Neg.logBase2()};
  return {TermPlan::Mul, false, 0};
}

/// The number of operations of the canonical implementation of \p F (see
/// buildCanonical).
unsigned getCanonicalSize(const LinearForm &F) {
  unsigned Pos = 0, Neg = 0, Ops = 0;
  for (const LinearTerm &T : F.Terms) {
    if (T.Coeff.isZero())
      continue;
    TermPlan P = planTerm(T.Coeff);
    Ops += P.Kind != TermPlan::Plain;
    ++(P.Negative ? Neg : Pos);
  }
  unsigned HasConst = !F.Const.isZero();
  if (!Pos && !Neg)
    return 0;
  if (!Pos)
    return Ops + Neg; // c - (n0 + n1 + ...)
  if (!Neg)
    return Ops + Pos + HasConst - 1;
  return Ops + Pos + Neg - 1 + HasConst; // (p - n) + c
}

/// Builds nodes of type \p Ty: adds them (Create), or only looks them up on
/// a clean graph.
class Builder {
public:
  Builder(EGraph &G, LLT Ty, bool Create) : G(G), Ty(Ty), Create(Create) {}

  std::optional<EClassId> constant(const APInt &V) {
    if (Create)
      return G.addConstantSplat(Ty, V);
    if (!Ty.isVector())
      return G.lookup(ENode::makeConstant(Ty, V));
    std::optional<EClassId> Lane =
        G.lookup(ENode::makeConstant(Ty.getElementType(), V));
    if (!Lane)
      return std::nullopt;
    SmallVector<EClassId, 8> Lanes(Ty.getNumElements(), *Lane);
    return G.lookup(ENode::makeOp(TargetOpcode::G_BUILD_VECTOR, Ty, Lanes));
  }
  std::optional<EClassId> op(unsigned Opc, std::optional<EClassId> A,
                             std::optional<EClassId> B) {
    if (!A || !B)
      return std::nullopt;
    ENode N = ENode::makeOp(Opc, Ty, {*A, *B});
    if (Create)
      return G.add(N);
    return G.lookup(N);
  }
  /// The canonical form of an AC sum (EGraph::addACTerm).
  std::optional<EClassId> sum(ArrayRef<EClassId> Leaves) {
    if (Create)
      return G.addACTerm(TargetOpcode::G_ADD, Ty, Leaves);
    return G.lookupACTerm(TargetOpcode::G_ADD, Ty, Leaves);
  }
  /// \p T << \p S (T itself for S = 0). The amount has the type of the value.
  std::optional<EClassId> shl(EClassId T, unsigned S) {
    if (!S)
      return T;
    return op(TargetOpcode::G_SHL, T,
              constant(APInt(Ty.getScalarSizeInBits(), S)));
  }
  std::optional<EClassId> mul(EClassId T, const APInt &K) {
    return op(TargetOpcode::G_MUL, T, constant(K));
  }

private:
  EGraph &G;
  LLT Ty;
  bool Create;
};

/// The canonical implementation of \p F: the terms added (coefficient 1,
/// 2^s, or another one realized as a G_MUL) and the constant form the AC sum
/// P, the terms subtracted (-1, -2^s) the AC sum N, both in the canonical
/// order of EGraph::addACTerm (so the sums are the canonical forms of
/// EGraph::canonicalizeAC). The result is P (with the constant as a leaf),
/// c - N without added terms, or (P - N) + c; a form without terms is the
/// constant. If \p Products is not null, it receives the index and the class
/// of each term realized as a G_MUL.
std::optional<EClassId>
buildCanonical(Builder &B, const LinearForm &F,
               SmallVectorImpl<std::pair<unsigned, EClassId>> *Products) {
  SmallVector<EClassId, 8> Pos, Neg;
  for (unsigned I = 0, E = F.Terms.size(); I != E; ++I) {
    const LinearTerm &T = F.Terms[I];
    if (T.Coeff.isZero())
      continue;
    TermPlan P = planTerm(T.Coeff);
    std::optional<EClassId> C;
    switch (P.Kind) {
    case TermPlan::Plain:
      C = T.Leaf;
      break;
    case TermPlan::Shift:
      C = B.shl(T.Leaf, P.Amount);
      break;
    case TermPlan::Mul:
      C = B.mul(T.Leaf, T.Coeff);
      if (C && Products)
        Products->push_back({I, *C});
      break;
    }
    if (!C)
      return std::nullopt;
    (P.Negative ? Neg : Pos).push_back(*C);
  }
  bool HasConst = !F.Const.isZero();
  if (Pos.empty() && Neg.empty())
    return B.constant(F.Const);
  if (Pos.empty())
    return B.op(TargetOpcode::G_SUB, B.constant(F.Const), B.sum(Neg));
  if (Neg.empty()) {
    if (HasConst) {
      std::optional<EClassId> C = B.constant(F.Const);
      if (!C)
        return std::nullopt;
      Pos.push_back(*C);
    }
    return B.sum(Pos);
  }
  std::optional<EClassId> D = B.op(TargetOpcode::G_SUB, B.sum(Pos), B.sum(Neg));
  if (!HasConst)
    return D;
  return B.op(TargetOpcode::G_ADD, D, B.constant(F.Const));
}

/// A coefficient with two set bits, 2^Hi + 2^Lo, or a run of ones,
/// 2^Hi - 2^Lo, both shifts inside the width (Lo may be greater than Hi).
struct ShiftAdd {
  unsigned Hi, Lo;
  bool Sub;
};

std::optional<ShiftAdd> getShiftAdd(const APInt &K) {
  unsigned W = K.getBitWidth();
  if (K.popcount() == 2)
    return ShiftAdd{K.logBase2(), K.countr_zero(), false};
  unsigned Idx, Len;
  // The ones of K are the bits [Idx, Idx + Len): K = 2^(Idx+Len) - 2^Idx.
  if (K.isShiftedMask(Idx, Len) && Idx + Len < W)
    return ShiftAdd{Idx + Len, Idx, true};
  // The ones of -K are the bits [Idx, Idx + Len): K = 2^Idx - 2^(Idx+Len).
  APInt Neg = -K;
  if (Neg.isShiftedMask(Idx, Len) && Idx + Len < W)
    return ShiftAdd{Idx, Idx + Len, true};
  return std::nullopt;
}

/// (\p T << Hi) +/- (\p T << Lo).
std::optional<EClassId> buildShiftAdd(Builder &B, EClassId T,
                                      const ShiftAdd &S) {
  return B.op(S.Sub ? TargetOpcode::G_SUB : TargetOpcode::G_ADD, B.shl(T, S.Hi),
              B.shl(T, S.Lo));
}

/// The reads of the leaves by the class (as often as its decomposition reads
/// them) and by the canonical implementation (once per leaf with a nonzero
/// coefficient).
SmallVector<LeafReads, 8> getLeafReads(const LinearForm &F) {
  SmallVector<LeafReads, 8> Reads;
  for (const LinearTerm &L : F.Terms)
    Reads.push_back({L.Leaf, L.Reads, L.Coeff.isZero() ? 0u : 1u});
  return Reads;
}

/// A view that the write phase relates to its class.
struct Todo {
  LinearForm Form;
  /// The existing class of the canonical implementation, if the view only
  /// looked it up; otherwise the implementations are built.
  std::optional<EClassId> Found;
};

} // end anonymous namespace

unsigned llvm::egraph::applyLinearViews(EGraph &G,
                                        const SaturationLimits &Limits,
                                        ViewStats &Stats) {
  assert(G.isClean() && "rebuild() the e-graph before computing views");
  // Read phase: the views of the unchanged graph.
  std::vector<Todo> Work;
  for (EClassId Id : G.getClassIds()) {
    const EClass &C = G.getClass(Id);
    if (C.Const || none_of(C.Nodes, [](const ENode &N) {
          return N.isOperation() && !N.Flags && isLinearOpcode(N.Opcode);
        }))
      continue;
    if (!isLinearType(C.Ty)) {
      ++Stats.Unsupported;
      continue;
    }
    if (G.getSplatConstant(Id))
      continue;
    Decomposer D(G, Limits, C.Ty);
    switch (D.run(Id)) {
    case Decomposer::Ok:
      break;
    case Decomposer::NoLinearNode:
      continue;
    case Decomposer::OverBudget:
      ++Stats.Budget;
      continue;
    case Decomposer::Unsupported:
      ++Stats.Unsupported;
      continue;
    }
    LinearForm F = D.takeForm(Id);
    // Only a view that the node-by-node form does not show adds nodes: an
    // implementation with fewer operations, or, if the class can be merged
    // with it, like terms (a leaf read twice), a zero coefficient or folded
    // constants, which make classes with the same form one class. A
    // refinement is only taken by extraction if it is cheaper, so it needs
    // fewer operations. Otherwise, with two or more linear operators, the
    // canonical implementation is only looked up, so that two classes with
    // the same form meet without new nodes; a single operator (a + b, x * 3)
    // has nothing to show.
    bool Fewer = getCanonicalSize(F) < F.NumOps;
    auto LikeOrZero = [](const LinearTerm &T) {
      return T.Reads > 1 || T.Coeff.isZero();
    };
    bool Simplifies = any_of(F.Terms, LikeOrZero) || F.NumConsts > 1;
    bool Reduces =
        Fewer || (Simplifies &&
                  classifyLeafReads(G, getLeafReads(F)) == RewriteKind::Exact);
    if (!Reduces && F.NumOps < 2)
      continue;
    ++Stats.Views;
    Todo T{std::move(F), std::nullopt};
    if (!Reduces) {
      Builder Lookup(G, T.Form.Ty, /*Create=*/false);
      std::optional<EClassId> Impl = buildCanonical(Lookup, T.Form, nullptr);
      if (!Impl || G.find(*Impl) == Id)
        continue;
      T.Found = G.find(*Impl);
    }
    Work.push_back(std::move(T));
  }

  // Write phase: build the implementations and relate the classes to them.
  unsigned NodesBefore = G.getNumNodes(), Changes = 0;
  bool AtNodeLimit = false;
  auto Relate = [&](EClassId From, EClassId To, RewriteKind K) {
    ++Stats.Candidates;
    ApplyResult R = relateClasses(G, From, To, K);
    Stats.count(R);
    if (R == ApplyResult::Merged || R == ApplyResult::Refined)
      ++Changes;
  };
  // Nodes may only be added below the node limit.
  auto MayAdd = [&] {
    if (G.getNumNodes() < Limits.MaxNodes)
      return true;
    if (!AtNodeLimit)
      ++Stats.Budget;
    AtNodeLimit = true;
    return false;
  };
  for (const Todo &T : Work) {
    const LinearForm &F = T.Form;
    if (!Limits.MaxViewCandidates) {
      ++Stats.Budget;
      continue;
    }
    RewriteKind K = classifyLeafReads(G, getLeafReads(F));
    if (K == RewriteKind::Unsafe) {
      ++Stats.Unsafe;
      continue;
    }
    if (T.Found) {
      Relate(F.Class, *T.Found, K);
      G.markLinearForm(F.Class);
      G.markLinearForm(*T.Found);
      continue;
    }
    if (!MayAdd())
      continue;
    Builder B(G, F.Ty, /*Create=*/true);
    SmallVector<std::pair<unsigned, EClassId>, 2> Products;
    std::optional<EClassId> Impl = buildCanonical(B, F, &Products);
    if (!Impl)
      continue;
    Relate(F.Class, *Impl, K);
    G.markLinearForm(F.Class);
    G.markLinearForm(*Impl);
    // The shift-add form of each product with a suitable coefficient, in
    // the class of the product: (t << Hi) +/- (t << Lo) reads t twice, so it
    // needs a t that is not undef (classifyLeafReads).
    unsigned Candidates = 1;
    for (auto [Idx, Product] : Products) {
      const LinearTerm &L = F.Terms[Idx];
      std::optional<ShiftAdd> S = getShiftAdd(L.Coeff);
      if (!S)
        continue;
      RewriteKind SK = classifyLeafReads(G, {{L.Leaf, 1, 2}});
      if (SK == RewriteKind::Unsafe) {
        ++Stats.Unsafe;
        continue;
      }
      if (Candidates == Limits.MaxViewCandidates) {
        ++Stats.Budget;
        break;
      }
      if (!MayAdd())
        break;
      std::optional<EClassId> SA = buildShiftAdd(B, L.Leaf, *S);
      if (!SA)
        continue;
      ++Candidates;
      Relate(Product, *SA, SK);
    }
  }
  return Changes + (G.getNumNodes() - NodesBefore);
}
