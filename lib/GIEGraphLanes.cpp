//===- GIEGraphLanes.cpp - Lane rules of fixed vectors --------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// The rules of the e-graph that move lanes of fixed vectors (OpShape::Vector).
// A table rule (GIEGraphRules.cpp) cannot write them: the index or the mask
// of the result is computed from another index or mask.
//
// Each rule is an equality of the lanes, including poison: lane i of both
// sides is the same scalar value. A rule therefore merges two classes. No
// rule writes a lane without a value (a shuffle mask entry -1): a node with
// such a lane is only a source of a rule where the lane is not read. A rule
// that changes which lanes of an operation are computed (scalarize, the
// permutation of an operation, the lanes of a build) only applies to an
// operator without undefined behaviour (isLaneWiseOperator): the lanes that
// one side does not compute could have trapped.
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GIEGraph.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include <functional>

using namespace llvm;
using namespace llvm::egraph;

namespace {

unsigned getLanes(LLT Ty) {
  return Ty.isValid() && Ty.isFixedVector() ? Ty.getNumElements() : 0;
}

/// One equality that the read phase found: the class \p Class and a
/// function that builds (or finds) the class of the other side.
struct LaneEq {
  const char *Rule;
  EClassId Class;
  std::function<std::optional<EClassId>(EGraph &)> Build;
};

class LaneRules {
public:
  explicit LaneRules(const EGraph &G) : G(G) {}

  void collect(SmallVectorImpl<LaneEq> &Out);

private:
  const EGraph &G;

  /// The nodes of \p C with the opcode \p Opc.
  SmallVector<const ENode *, 2> nodesOf(EClassId C, unsigned Opc) const {
    SmallVector<const ENode *, 2> Out;
    for (const ENode &N : G.getClass(C).Nodes)
      if (N.isOperation() && N.Opcode == Opc)
        Out.push_back(&N);
    return Out;
  }

  /// The source (class, lane) of lane \p I of a shuffle node, or nullopt for
  /// a lane without a value.
  std::optional<std::pair<EClassId, unsigned>>
  shuffleLane(const ENode &S, unsigned I) const {
    int M = G.getMask(S.Attr)[I];
    if (M < 0)
      return std::nullopt;
    unsigned N = getLanes(G.getType(S.Ops[0]));
    return std::make_pair(G.find(S.Ops[unsigned(M) < N ? 0 : 1]),
                          unsigned(M) % N);
  }

  void extractRules(EClassId C, const ENode &N, SmallVectorImpl<LaneEq> &Out);
  void buildRules(EClassId C, const ENode &N, SmallVectorImpl<LaneEq> &Out);
  void shuffleRules(EClassId C, const ENode &N, SmallVectorImpl<LaneEq> &Out);
  void insertRules(EClassId C, const ENode &N, SmallVectorImpl<LaneEq> &Out);
  void laneWiseRules(EClassId C, const ENode &N, const OpProperties &P,
                     SmallVectorImpl<LaneEq> &Out);
};

/// A G_EXTRACT_VECTOR_ELT of lane \p Lane of the class \p V.
std::optional<EClassId> extract(EGraph &G, EClassId V, unsigned Lane) {
  LLT Ty = G.getType(V);
  if (Lane >= getLanes(Ty))
    return std::nullopt;
  return G.addOp(TargetOpcode::G_EXTRACT_VECTOR_ELT, Ty.getElementType(), {V},
                 0, Lane);
}

/// The scalar node of lane \p Lane of the lane-wise node \p N.
std::optional<EClassId> scalarLane(EGraph &G, const ENode &N, unsigned Lane) {
  SmallVector<EClassId, 3> Ops;
  for (EClassId Op : N.Ops) {
    if (!getLanes(G.getType(Op))) {
      // A scalar operand (the condition of a G_SELECT) is one value for
      // all lanes.
      Ops.push_back(Op);
      continue;
    }
    std::optional<EClassId> E = extract(G, Op, Lane);
    if (!E)
      return std::nullopt;
    Ops.push_back(*E);
  }
  return G.addOp(N.Opcode, N.Ty.getElementType(), Ops, N.Flags, N.Attr);
}

void LaneRules::extractRules(EClassId C, const ENode &N,
                             SmallVectorImpl<LaneEq> &Out) {
  unsigned I = N.Attr;
  EClassId V = G.find(N.Ops[0]);
  for (const ENode &M : G.getClass(V).Nodes) {
    if (!M.isOperation())
      continue;
    switch (M.Opcode) {
    case TargetOpcode::G_BUILD_VECTOR:
      if (I < M.Ops.size()) {
        EClassId Lane = M.Ops[I];
        Out.push_back({"vector-extract-of-build", C,
                       [Lane](EGraph &) { return Lane; }});
      }
      continue;
    case TargetOpcode::G_INSERT_VECTOR_ELT: {
      EClassId Vec = M.Ops[0], Elt = M.Ops[1];
      if (M.Attr == I)
        Out.push_back({"vector-extract-of-insert", C,
                       [Elt](EGraph &) { return Elt; }});
      else
        Out.push_back({"vector-extract-of-insert", C,
                       [Vec, I](EGraph &G) { return extract(G, Vec, I); }});
      continue;
    }
    case TargetOpcode::G_SHUFFLE_VECTOR:
      if (auto Src = shuffleLane(M, I))
        Out.push_back({"vector-extract-of-shuffle", C, [Src](EGraph &G) {
                         return extract(G, Src->first, Src->second);
                       }});
      continue;
    case TargetOpcode::G_CONCAT_VECTORS: {
      unsigned Part = getLanes(G.getType(M.Ops[0]));
      if (!Part || I / Part >= M.Ops.size())
        continue;
      EClassId Src = M.Ops[I / Part];
      Out.push_back({"vector-extract-of-concat", C, [Src, I, Part](EGraph &G) {
                       return extract(G, Src, I % Part);
                     }});
      continue;
    }
    default:
      break;
    }
    const OpProperties *P = getOpProperties(M.Opcode);
    if (P && isLaneWiseOperator(*P) && getLanes(M.Ty)) {
      ENode Copy = M;
      Out.push_back({"vector-scalarize", C, [Copy, I](EGraph &G) {
                       return scalarLane(G, Copy, I);
                     }});
    }
  }
}

void LaneRules::buildRules(EClassId C, const ENode &N,
                           SmallVectorImpl<LaneEq> &Out) {
  // Each lane is an extraction of a lane of at most two vectors of one
  // type: the vector itself, or a shuffle of them.
  SmallVector<EClassId, 2> Srcs;
  SmallVector<int, 8> Mask;
  for (EClassId Op : N.Ops) {
    const ENode *E = nullptr;
    for (const ENode *X : nodesOf(G.find(Op), TargetOpcode::G_EXTRACT_VECTOR_ELT))
      if (!E || G.find(X->Ops[0]) < G.find(E->Ops[0]))
        E = X;
    if (!E)
      return;
    EClassId V = G.find(E->Ops[0]);
    auto It = find(Srcs, V);
    if (It == Srcs.end()) {
      if (Srcs.size() == 2)
        return;
      Srcs.push_back(V);
      It = Srcs.end() - 1;
    }
    Mask.push_back(int(E->Attr) + int(It - Srcs.begin()) *
                                      int(getLanes(G.getType(V))));
  }
  if (Srcs.empty() || (Srcs.size() == 2 &&
                       G.getType(Srcs[0]) != G.getType(Srcs[1])))
    return;
  LLT SrcTy = G.getType(Srcs[0]);
  bool Identity = Srcs.size() == 1 && SrcTy == N.Ty;
  for (unsigned I = 0, E = Mask.size(); Identity && I != E; ++I)
    Identity = Mask[I] == int(I);
  if (Identity) {
    EClassId V = Srcs[0];
    Out.push_back({"vector-build-of-extracts", C,
                   [V](EGraph &) { return V; }});
    return;
  }
  EClassId A = Srcs[0], B = Srcs.back();
  LLT Ty = N.Ty;
  SmallVector<int, 8> M(Mask);
  Out.push_back({"vector-build-of-extracts", C,
                 [A, B, Ty, M](EGraph &G) -> std::optional<EClassId> {
                   return G.addOp(TargetOpcode::G_SHUFFLE_VECTOR, Ty, {A, B}, 0,
                                  G.internMask(M));
                 }});
}

void LaneRules::shuffleRules(EClassId C, const ENode &N,
                             SmallVectorImpl<LaneEq> &Out) {
  ArrayRef<int> Mask = G.getMask(N.Attr);
  unsigned SrcLanes = getLanes(G.getType(N.Ops[0]));
  // The identity of one operand.
  for (unsigned K = 0; K != 2; ++K) {
    if (G.getType(N.Ops[K]) != N.Ty)
      continue;
    bool Identity = true;
    for (unsigned I = 0, E = Mask.size(); Identity && I != E; ++I)
      Identity = Mask[I] == int(I + K * SrcLanes);
    if (Identity) {
      EClassId V = N.Ops[K];
      Out.push_back({"vector-shuffle-identity", C,
                     [V](EGraph &) { return V; }});
    }
  }
  // The composition with the shuffles of the operands: each lane of the
  // result is a lane of at most two vectors of one type.
  SmallVector<EClassId, 2> Srcs;
  SmallVector<int, 8> NewMask;
  bool Changed = false;
  for (unsigned I = 0, E = Mask.size(); I != E; ++I) {
    auto Src = shuffleLane(N, I);
    if (!Src)
      return;
    auto [V, Lane] = *Src;
    for (const ENode *S : nodesOf(V, TargetOpcode::G_SHUFFLE_VECTOR)) {
      if (auto Inner = shuffleLane(*S, Lane)) {
        std::tie(V, Lane) = *Inner;
        Changed = true;
        break;
      }
    }
    auto It = find(Srcs, V);
    if (It == Srcs.end()) {
      if (Srcs.size() == 2)
        return;
      Srcs.push_back(V);
      It = Srcs.end() - 1;
    }
    NewMask.push_back(int(Lane) +
                      int(It - Srcs.begin()) * int(getLanes(G.getType(V))));
  }
  if (!Changed ||
      (Srcs.size() == 2 && G.getType(Srcs[0]) != G.getType(Srcs[1])))
    return;
  EClassId A = Srcs[0], B = Srcs.back();
  LLT Ty = N.Ty;
  if (Srcs.size() == 1 && G.getType(A) == Ty) {
    bool Identity = true;
    for (unsigned I = 0, E = NewMask.size(); Identity && I != E; ++I)
      Identity = NewMask[I] == int(I);
    if (Identity) {
      Out.push_back({"vector-shuffle-of-shuffle", C,
                     [A](EGraph &) { return A; }});
      return;
    }
  }
  Out.push_back({"vector-shuffle-of-shuffle", C,
                 [A, B, Ty, NewMask](EGraph &G) -> std::optional<EClassId> {
                   return G.addOp(TargetOpcode::G_SHUFFLE_VECTOR, Ty, {A, B}, 0,
                                  G.internMask(NewMask));
                 }});
}

void LaneRules::insertRules(EClassId C, const ENode &N,
                            SmallVectorImpl<LaneEq> &Out) {
  // insert(v, extract(v, j), j) == v.
  EClassId V = G.find(N.Ops[0]);
  for (const ENode *E :
       nodesOf(G.find(N.Ops[1]), TargetOpcode::G_EXTRACT_VECTOR_ELT))
    if (E->Attr == N.Attr && G.find(E->Ops[0]) == V) {
      Out.push_back({"vector-insert-of-extract", C,
                     [V](EGraph &) { return V; }});
      return;
    }
}

void LaneRules::laneWiseRules(EClassId C, const ENode &N, const OpProperties &P,
                              SmallVectorImpl<LaneEq> &Out) {
  unsigned Lanes = getLanes(N.Ty);
  if (!Lanes)
    return;
  // op(shuffle(a, _, m), shuffle(b, _, m)) == shuffle(op(a, b), _, m) for a
  // permutation m of one operand with the lanes of the result.
  std::optional<SmallVector<int, 8>> Perm;
  SmallVector<std::optional<EClassId>, 3> Whole;
  bool AllShuffles = true;
  for (EClassId Op : N.Ops) {
    if (!getLanes(G.getType(Op))) {
      Whole.push_back(std::nullopt);
      continue;
    }
    std::optional<EClassId> Found;
    for (const ENode *S : nodesOf(G.find(Op), TargetOpcode::G_SHUFFLE_VECTOR)) {
      ArrayRef<int> M = G.getMask(S->Attr);
      if (getLanes(G.getType(S->Ops[0])) != Lanes ||
          any_of(M, [&](int X) { return X < 0 || X >= int(Lanes); }))
        continue;
      if (Perm && ArrayRef<int>(*Perm) != M)
        continue;
      Perm = SmallVector<int, 8>(M.begin(), M.end());
      Found = G.find(S->Ops[0]);
      break;
    }
    if (!Found) {
      AllShuffles = false;
      break;
    }
    Whole.push_back(Found);
  }
  if (AllShuffles && Perm) {
    ENode Copy = N;
    SmallVector<int, 8> M = *Perm;
    Out.push_back({"vector-permute-lanewise", C,
                   [Copy, Whole, M](EGraph &G) -> std::optional<EClassId> {
                     SmallVector<EClassId, 3> Ops;
                     for (unsigned I = 0, E = Copy.Ops.size(); I != E; ++I)
                       Ops.push_back(Whole[I] ? *Whole[I] : Copy.Ops[I]);
                     EClassId Op = G.addOp(Copy.Opcode, Copy.Ty, Ops,
                                           Copy.Flags, Copy.Attr);
                     return G.addOp(TargetOpcode::G_SHUFFLE_VECTOR, Copy.Ty,
                                    {Op, Op}, 0, G.internMask(M));
                   }});
  }
  // op(build(a...), build(b...)) == build(op(a0, b0), ...): the lanes of
  // constants then fold one by one, in their own width.
  SmallVector<const ENode *, 3> Builds;
  for (EClassId Op : N.Ops) {
    if (!getLanes(G.getType(Op))) {
      Builds.push_back(nullptr);
      continue;
    }
    auto Bs = nodesOf(G.find(Op), TargetOpcode::G_BUILD_VECTOR);
    if (Bs.empty())
      return;
    Builds.push_back(Bs.front());
  }
  ENode Copy = N;
  SmallVector<SmallVector<EClassId, 2>, 3> Lanesof;
  for (const ENode *B : Builds)
    Lanesof.push_back(B ? B->Ops : SmallVector<EClassId, 2>());
  Out.push_back({"vector-lanewise-of-build", C,
                 [Copy, Lanesof, Lanes](EGraph &G) -> std::optional<EClassId> {
                   SmallVector<EClassId, 8> Elts;
                   for (unsigned I = 0; I != Lanes; ++I) {
                     SmallVector<EClassId, 3> Ops;
                     for (unsigned K = 0, E = Copy.Ops.size(); K != E; ++K)
                       Ops.push_back(Lanesof[K].empty() ? Copy.Ops[K]
                                                        : Lanesof[K][I]);
                     Elts.push_back(G.addOp(Copy.Opcode,
                                            Copy.Ty.getElementType(), Ops,
                                            Copy.Flags, Copy.Attr));
                   }
                   return G.addOp(TargetOpcode::G_BUILD_VECTOR, Copy.Ty, Elts);
                 }});
}

void LaneRules::collect(SmallVectorImpl<LaneEq> &Out) {
  for (EClassId C : G.getClassIds()) {
    for (const ENode &N : G.getClass(C).Nodes) {
      if (!N.isOperation())
        continue;
      switch (N.Opcode) {
      case TargetOpcode::G_EXTRACT_VECTOR_ELT:
        extractRules(C, N, Out);
        continue;
      case TargetOpcode::G_BUILD_VECTOR:
        buildRules(C, N, Out);
        continue;
      case TargetOpcode::G_SHUFFLE_VECTOR:
        shuffleRules(C, N, Out);
        continue;
      case TargetOpcode::G_INSERT_VECTOR_ELT:
        insertRules(C, N, Out);
        continue;
      default:
        break;
      }
      const OpProperties *P = getOpProperties(N.Opcode);
      if (P && isLaneWiseOperator(*P))
        laneWiseRules(C, N, *P, Out);
    }
  }
}

} // end anonymous namespace

unsigned
llvm::egraph::applyLaneRules(EGraph &G, unsigned MaxNodes,
                             std::map<std::string, unsigned> &Applications) {
  SmallVector<LaneEq, 32> Eqs;
  LaneRules(G).collect(Eqs);
  unsigned Merges = 0;
  for (LaneEq &E : Eqs) {
    if (G.getNumNodes() >= MaxNodes)
      break;
    std::optional<EClassId> Other = E.Build(G);
    if (!Other || G.getType(*Other) != G.getType(E.Class) ||
        G.equivalent(*Other, E.Class))
      continue;
    if (G.merge(E.Class, *Other)) {
      ++Merges;
      ++Applications[E.Rule];
    }
  }
  return Merges;
}
