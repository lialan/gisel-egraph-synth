//===- GIEGraphLinearTest.cpp - Linear and AC views of the e-graph --------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Tests of the views of sums: the AC canonical forms
// (EGraph::canonicalizeAC) with AC matching. The tests check what may be
// related and how (merge or refinement), including undef and poison inputs,
// wrap-around, cycles and budgets.
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GIEGraph.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "gtest/gtest.h"
#include <tuple>

using namespace llvm;
using namespace llvm::egraph;
using namespace llvm::TargetOpcode;

namespace {

class GIEGraphSumsTest : public testing::Test {
protected:
  EGraph G;
  const LLT S8 = LLT::scalar(8);
  const LLT S32 = LLT::scalar(32);
  const LLT V2S32 = LLT::fixed_vector(2, 32);

  EClassId input(LLT Ty, bool NotUndef, bool NotPoison) {
    InputInfo I;
    I.Ty = Ty;
    I.NotUndef = NotUndef;
    I.NotPoison = NotPoison;
    return G.addInput(I);
  }
  /// An input; Defined means neither undef nor poison.
  EClassId in(LLT Ty, bool Defined = false) {
    return input(Ty, Defined, Defined);
  }
  EClassId in(bool Defined = false) { return in(S32, Defined); }
  /// An input that is never undef but may be poison.
  EClassId inNotUndef() { return input(S32, true, false); }
  /// A scalar constant, or a splat of a fixed vector.
  EClassId cst(int64_t V, LLT Ty) {
    unsigned W = Ty.getScalarSizeInBits();
    return G.addConstantSplat(Ty, APInt(W, V, /*isSigned=*/true,
                                        /*implicitTrunc=*/true));
  }
  EClassId cst(int64_t V) { return cst(V, S32); }
  EClassId op(unsigned Opc, EClassId A, EClassId B, uint32_t Flags = 0) {
    return G.addOp(Opc, G.getType(A), {A, B}, Flags);
  }
  EClassId add(EClassId A, EClassId B) { return op(G_ADD, A, B); }
  EClassId sub(EClassId A, EClassId B) { return op(G_SUB, A, B); }
  EClassId mul(EClassId A, EClassId B) { return op(G_MUL, A, B); }
  EClassId shl(EClassId A, EClassId B) { return op(G_SHL, A, B); }

  /// The linear view alone, once, on a rebuilt graph.
  ViewStats linearOnce(SaturationLimits Limits = SaturationLimits()) {
    G.rebuild();
    ViewStats S;
    applyLinearViews(G, Limits, S);
    G.rebuild();
    return S;
  }
  SaturationStats runAll(SaturationLimits Limits = SaturationLimits()) {
    std::vector<RewriteRule> All = getDefaultIntegerRules();
    return saturate(G, All, Limits);
  }
  /// Saturation with the named table rules only, without the linear view.
  SaturationStats runRules(ArrayRef<StringRef> Names,
                           SaturationLimits Limits = SaturationLimits()) {
    std::vector<RewriteRule> Out;
    for (const RewriteRule &R : getDefaultIntegerRules())
      if (is_contained(Names, R.getName()))
        Out.push_back(R);
    EXPECT_EQ(Out.size(), Names.size());
    Limits.EnableLinear = false;
    return saturate(G, Out, Limits);
  }
  EClassId lookup(function_ref<EClassId()> Build) {
    EClassId Id = Build();
    G.rebuild();
    return G.find(Id);
  }
  std::string extract(EClassId Root, unsigned MulCost = 2) {
    DefaultCostModel CM;
    CM.MulCost = MulCost;
    Extractor E(G, CM);
    return E.getExprString(Root);
  }
  uint64_t cost(EClassId Root) {
    DefaultCostModel CM;
    Extractor E(G, CM);
    return E.getTreeCost(Root);
  }
};

//===----------------------------------------------------------------------===//
// AC terms
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphSumsTest, ACSumKeepsMultiplicityAndWrapsConstants) {
  // (a + 0xfffffff0) + (b + (a + 0x20)) is the term {a, a, b, 0x10}: a is
  // counted twice (not deduplicated), and the constants fold modulo 2^32.
  // Regrouping reads each leaf once on each side, so this is exact even for
  // an a that may be undef.
  EClassId A = in(), B = in();
  EClassId T = add(add(A, cst(0xfffffff0)), add(B, add(A, cst(0x20))));
  runRules({"fold-add"});
  EClassId Canon = lookup([&] {
    return G.addACTerm(G_ADD, S32, {A, A, B, cst(0x10)});
  });
  EXPECT_TRUE(G.equivalent(T, Canon));
  EClassId Once = lookup([&] {
    return G.addACTerm(G_ADD, S32, {A, B, cst(0x10)});
  });
  EXPECT_FALSE(G.equivalent(T, Once));
}

TEST_F(GIEGraphSumsTest, ACXorCancelsPairsByTheDefinednessPolicy) {
  // ((a ^ b) ^ c) ^ (a ^ d): the two reads of a cancel. Exact only for an a
  // that is neither undef nor poison.
  auto Build = [&](EClassId A) {
    EClassId B = in(), C = in(), D = in();
    EClassId T = op(G_XOR, op(G_XOR, op(G_XOR, A, B), C), op(G_XOR, A, D));
    EClassId Rest = G.addACTerm(G_XOR, S32, {B, C, D});
    return std::make_pair(T, Rest);
  };
  auto [TU, RU] = Build(in());
  auto [TN, RN] = Build(inNotUndef());
  auto [TD, RD] = Build(in(true));
  runRules({"xor-self", "xor-zero"});
  EXPECT_FALSE(G.equivalent(TU, RU));
  EXPECT_TRUE(G.refinesTo(TU, RU));
  EXPECT_FALSE(G.equivalent(TN, RN));
  EXPECT_TRUE(G.refinesTo(TN, RN));
  EXPECT_TRUE(G.equivalent(TD, RD));
  // An odd number of reads keeps one: a ^ a ^ a ^ b refines to a ^ b; it
  // is never equal to it for an a that may be undef.
  EClassId U = in(), V = in();
  EClassId T3 = op(G_XOR, op(G_XOR, op(G_XOR, U, U), U), V);
  runRules({"xor-self", "xor-zero"});
  EClassId UV = lookup([&] { return op(G_XOR, U, V); });
  EXPECT_FALSE(G.equivalent(T3, UV));
  EXPECT_TRUE(G.refinesTo(T3, UV));
}

TEST_F(GIEGraphSumsTest, ACAndOrDeduplicateAndMergeMasks) {
  // (x & 0xff) & (y & (x & 0x0f)) is x & y & 0x0f and
  // (x | 0xf0) | (y | (x | 0x03)) is x | y | 0xf3. Deduplicating x reads it
  // once instead of twice: exact for a defined x, a refinement otherwise.
  auto Build = [&](EClassId X) {
    EClassId Y = in();
    EClassId A = op(G_AND, op(G_AND, X, cst(0xff)),
                    op(G_AND, Y, op(G_AND, X, cst(0x0f))));
    EClassId O =
        op(G_OR, op(G_OR, X, cst(0xf0)), op(G_OR, Y, op(G_OR, X, cst(0x03))));
    EClassId AC = G.addACTerm(G_AND, S32, {X, Y, cst(0x0f)});
    EClassId OC = G.addACTerm(G_OR, S32, {X, Y, cst(0xf3)});
    return std::make_tuple(A, O, AC, OC);
  };
  auto [AD, OD, ACD, OCD] = Build(in(true));
  auto [AU, OU, ACU, OCU] = Build(in());
  runRules({"and-self", "or-self", "fold-and", "fold-or"});
  EXPECT_TRUE(G.equivalent(AD, ACD));
  EXPECT_TRUE(G.equivalent(OD, OCD));
  EXPECT_FALSE(G.equivalent(AU, ACU));
  EXPECT_TRUE(G.refinesTo(AU, ACU));
  EXPECT_FALSE(G.equivalent(OU, OCU));
  EXPECT_TRUE(G.refinesTo(OU, OCU));
}

TEST_F(GIEGraphSumsTest, ACCanonicalFormFollowsAMerge) {
  // (a + b) + c and (b + b) + c have different terms until a and b are
  // found equal (here by a merge, as a rule would do). After the merge both
  // are the term {b, b, c}, and its canonical form is found again.
  EClassId A = in(), B = in(), C = in();
  EClassId T1 = add(add(A, B), C);
  EClassId T2 = add(add(B, B), C);
  EClassId X1 = op(G_XOR, op(G_XOR, A, C), B);
  runRules({});
  EXPECT_FALSE(G.equivalent(T1, T2));
  G.merge(A, B);
  runRules({});
  EXPECT_TRUE(G.equivalent(T1, T2));
  std::optional<EClassId> K = G.lookupACTerm(G_ADD, S32, {B, C, A});
  ASSERT_TRUE(K);
  EXPECT_TRUE(G.equivalent(*K, T1));
  // The xor term is now {b, b, c}. The inputs may be undef, so it only
  // refines to c.
  runRules({"xor-self", "xor-zero"});
  EXPECT_FALSE(G.equivalent(X1, C));
  EXPECT_TRUE(G.refinesTo(X1, C));
}

TEST_F(GIEGraphSumsTest, ACCycleThroughAnIdentity) {
  // x + 0 is merged with x, so the class of x has a node that uses the
  // class itself. Terms that use x keep x as a leaf (no 0 leaf, no
  // unbounded flattening), and saturation stops.
  EClassId X = in(), Y = in(), Z = in();
  EClassId X0 = add(X, cst(0));
  EClassId T = add(add(X0, Y), Z);
  SaturationStats S = runAll();
  EXPECT_TRUE(G.equivalent(X0, X));
  EXPECT_TRUE(S.Saturated);
  std::optional<EClassId> K = G.lookupACTerm(G_ADD, S32, {X, Y, Z});
  ASSERT_TRUE(K);
  EXPECT_TRUE(G.equivalent(*K, T));
  EXPECT_EQ(cost(T), 2u);
  // Measured: 15 nodes.
  EXPECT_LE(G.getNumNodes(), 25u);
}

TEST_F(GIEGraphSumsTest, ACCycleThroughASum) {
  // y == (y - x) + x: after the merge the class of y has a sum that uses a
  // class built from y. A term with the leaf y is not expanded through it.
  EClassId X = in(true), Y = in(true), Z = in(true);
  EClassId D = sub(Y, X);
  EClassId S = add(D, X);
  G.merge(S, Y);
  EClassId T = add(add(Y, Z), X);
  runRules({});
  std::optional<EClassId> K = G.lookupACTerm(G_ADD, S32, {X, Y, Z});
  ASSERT_TRUE(K);
  EXPECT_TRUE(G.equivalent(*K, T));
  EXPECT_FALSE(G.lookupACTerm(G_ADD, S32, {D, X, X, Z}));
}

TEST_F(GIEGraphSumsTest, ACMultipleDecompositionsAreNotMixed) {
  // A class with two xor nodes a ^ b and c ^ d (equal by assumption, as if
  // a rule had found it). In (a ^ b) ^ a the two reads of a cancel through
  // the first decomposition; the leaves of the two decompositions are never
  // combined.
  EClassId A = in(true), B = in(true), C = in(true), D = in(true);
  EClassId AB = op(G_XOR, A, B);
  EClassId CD = op(G_XOR, C, D);
  G.merge(AB, CD);
  EClassId T = op(G_XOR, AB, A);
  runRules({"xor-self", "xor-zero"});
  EXPECT_TRUE(G.equivalent(T, B));
  for (EClassId Wrong : {A, C, D})
    EXPECT_FALSE(G.equivalent(T, Wrong));
  EXPECT_FALSE(G.equivalent(T, lookup([&] { return op(G_XOR, A, C); })));
  // Both decompositions are still in the class.
  unsigned Xors = 0;
  for (const ENode &N : G.getClass(AB).Nodes)
    Xors += N.isOperation() && N.Opcode == G_XOR;
  EXPECT_GE(Xors, 2u);
}

TEST_F(GIEGraphSumsTest, ACSharedInnerSumStaysAvailable) {
  // s = a + b is used by t = s + c and by u = s * d. Canonicalizing t does
  // not take s away from u: s keeps its node and is computed once.
  EClassId A = in(), B = in(), C = in(), D = in();
  EClassId Sum = add(A, B);
  EClassId T = add(Sum, C);
  EClassId U = mul(Sum, D);
  EClassId T2 = add(add(C, B), A);
  runAll();
  EXPECT_TRUE(G.equivalent(T, T2));
  EXPECT_EQ(G.lookup(ENode::makeOp(G_ADD, S32, {A, B})), G.find(Sum));
  DefaultCostModel CM;
  Extractor E(G, CM);
  // s (1) + t (1) + u (2).
  EXPECT_EQ(E.getDagCost({T, U}), 4u);
}

TEST_F(GIEGraphSumsTest, ACBudgetFallsBackToNodes) {
  // With at most 3 leaves per flattening, a sum of 6 leaves keeps its
  // node-by-node form (counted as a budget stop): a regrouping that only a
  // flattening of 4 or more leaves shows is not found, while a sum of 3
  // leaves is still canonical. Nothing is merged wrongly.
  EClassId L[7];
  for (EClassId &X : L)
    X = in();
  EClassId Big = add(add(add(add(add(L[0], L[1]), L[2]), L[3]), L[4]), L[5]);
  EClassId Pairs = add(add(add(L[0], L[3]), add(L[1], L[4])), add(L[2], L[5]));
  EClassId Other = add(add(add(add(add(L[0], L[1]), L[2]), L[3]), L[4]), L[6]);
  EClassId Small = add(add(L[0], L[1]), L[2]);
  EClassId SmallRegrouped = add(L[2], add(L[1], L[0]));
  SaturationLimits Lim;
  Lim.MaxACLeaves = 3;
  SaturationStats S = runRules({}, Lim);
  EXPECT_GT(S.Views["ac"].Budget, 0u);
  EXPECT_EQ(S.Views["ac"].Merges, S.ACMerges);
  EXPECT_TRUE(G.equivalent(Small, SmallRegrouped));
  EXPECT_FALSE(G.equivalent(Big, Pairs));
  EXPECT_FALSE(G.equivalent(Big, Other));
  // With the default budget the regrouping is found.
  S = runRules({});
  EXPECT_EQ(S.Views["ac"].Budget, 0u);
  EXPECT_TRUE(G.equivalent(Big, Pairs));
  EXPECT_FALSE(G.equivalent(Big, Other));
}

TEST_F(GIEGraphSumsTest, ACStatisticsCountFlagsAndMerges) {
  // A flagged sum is a leaf of the terms that use it (counted as outside
  // the supported subset); unflagged regroupings are merged.
  const uint32_t NSW = MachineInstr::NoSWrap;
  EClassId A = in(), B = in(), C = in();
  EClassId F = op(G_ADD, op(G_ADD, A, B, NSW), C, NSW);
  EClassId T1 = add(add(A, B), C), T2 = add(A, add(B, C));
  SaturationStats S = runRules({});
  const ViewStats &AC = S.Views["ac"];
  EXPECT_TRUE(G.equivalent(T1, T2));
  EXPECT_FALSE(G.equivalent(F, T1));
  EXPECT_GE(AC.Unsupported, 2u);
  EXPECT_GE(AC.Merges, 1u);
  EXPECT_GE(AC.Views, 2u);
  EXPECT_EQ(AC.Budget, 0u);
}

} // namespace
