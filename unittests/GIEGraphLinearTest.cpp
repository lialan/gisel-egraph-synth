//===- GIEGraphLinearTest.cpp - Linear and AC views of the e-graph --------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Tests of the views of sums: the linear view modulo 2^W (applyLinearViews)
// and the AC canonical forms (EGraph::canonicalizeAC) with AC matching. The
// tests check what may be related and how (merge or refinement), including
// undef and poison inputs, wrap-around, flags and budgets.
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
// The linear view
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphSumsTest, LinearViewOfShiftsAndSums) {
  // ((x << 3) + x) - (y + y) + 7 is 9x - 2y + 7. The view relates it to the
  // canonical implementation (x * 9 - (y << 1)) + 7: merged for defined
  // inputs, refined for inputs that may be undef (x and y are read twice).
  EClassId X = in(true), Y = in(true);
  EClassId R = add(sub(add(shl(X, cst(3)), X), add(Y, Y)), cst(7));
  EClassId U = in(), V = in();
  EClassId Q = add(sub(add(shl(U, cst(3)), U), add(V, V)), cst(7));
  G.rebuild();
  unsigned Before = G.getNumNodes();
  ViewStats S = linearOnce();
  unsigned After = G.getNumNodes();
  EClassId Canon =
      lookup([&] { return add(sub(mul(X, cst(9)), shl(Y, cst(1))), cst(7)); });
  EClassId QCanon =
      lookup([&] { return add(sub(mul(U, cst(9)), shl(V, cst(1))), cst(7)); });
  EXPECT_TRUE(G.equivalent(R, Canon));
  EXPECT_FALSE(G.equivalent(Q, QCanon));
  EXPECT_TRUE(G.refinesTo(Q, QCanon));
  // The term 9x has the shift-add form 8x + x, which is the original
  // (x << 3) + x: only for the defined x.
  EXPECT_TRUE(G.equivalent(add(shl(X, cst(3)), X), mul(X, cst(9))));
  EXPECT_FALSE(G.equivalent(add(shl(U, cst(3)), U), mul(U, cst(9))));
  EXPECT_GE(S.Views, 2u);
  EXPECT_GE(S.Merges, 2u);
  EXPECT_GE(S.Refinements, 2u);
  EXPECT_GE(S.Unsafe, 1u); // The shift-add form of 9u.
  // Measured: 21 -> 31 nodes.
  EXPECT_LE(After, Before + 12);
}

TEST_F(GIEGraphSumsTest, LinearViewOnlyAddsNodesWhereItSimplifies) {
  // a + b, (a - b) + c and a * 3 show nothing that their nodes do not: no
  // node is added.
  EClassId A = in(), B = in(), C = in();
  add(A, B);
  add(sub(A, B), C);
  mul(A, cst(3));
  G.rebuild();
  unsigned Before = G.getNumNodes();
  ViewStats S = linearOnce();
  EXPECT_EQ(G.getNumNodes(), Before);
  EXPECT_EQ(S.Candidates, 0u);
  EXPECT_EQ(S.Merges + S.Refinements, 0u);
}

TEST_F(GIEGraphSumsTest, LinearCancellationIsFoundInTheFirstIteration) {
  // (x * 3) + (y * 2) - (x + x + x) is 2y. With inputs that may be undef or
  // poison this is a refinement (x is dropped).
  auto Build = [&] {
    EClassId X = in(), Y = in();
    EClassId R = sub(add(mul(X, cst(3)), mul(Y, cst(2))), add(add(X, X), X));
    return std::make_pair(R, Y);
  };
  SaturationLimits One;
  One.MaxIterations = 1;
  EClassId R, Y;
  std::tie(R, Y) = Build();
  runAll(One);
  EXPECT_EQ(extract(R), "(G_SHL %in1 1)");
  EXPECT_TRUE(G.refinesTo(R, lookup([&] { return shl(Y, cst(1)); })));
  // Measured: 19 nodes after the first iteration.
  EXPECT_LE(G.getNumNodes(), 30u);

  // The table rules alone need more iterations (5, with 136 nodes).
  G = EGraph();
  One.EnableLinear = false;
  std::tie(R, Y) = Build();
  runAll(One);
  EXPECT_NE(extract(R), "(G_SHL %in1 1)");

  // With the default budget the graph saturates. Measured: 9 iterations,
  // 221 nodes; without the linear view the iteration limit stops the
  // rules at 222 nodes.
  G = EGraph();
  std::tie(R, Y) = Build();
  SaturationStats S = runAll();
  EXPECT_TRUE(S.Saturated);
  EXPECT_LE(G.getNumNodes(), 300u);
  EXPECT_EQ(extract(R), "(G_SHL %in1 1)");
}

TEST_F(GIEGraphSumsTest, LinearCancellationOfDefinedValuesIsExact) {
  EClassId X = in(true), Y = in(true);
  EClassId Sum = add(add(X, X), X);
  EClassId R = sub(add(mul(X, cst(3)), mul(Y, cst(2))), Sum);
  linearOnce();
  EXPECT_TRUE(G.equivalent(R, lookup([&] { return shl(Y, cst(1)); })));
  // The inner sum is 3x as well.
  EXPECT_TRUE(G.equivalent(Sum, lookup([&] { return mul(X, cst(3)); })));
  // With all rules the graph saturates. Measured: 5 iterations, 61 nodes;
  // without the linear view the iteration limit stops the rules at 195
  // nodes.
  G = EGraph();
  X = in(true);
  Y = in(true);
  R = sub(add(mul(X, cst(3)), mul(Y, cst(2))), add(add(X, X), X));
  SaturationStats S = runAll();
  EXPECT_TRUE(S.Saturated);
  EXPECT_LE(G.getNumNodes(), 100u);
  EXPECT_EQ(extract(R), "(G_SHL %in1 1)");
}

TEST_F(GIEGraphSumsTest, LinearSameFormIsOneClass) {
  // (x << 2) + x + 11, (x * 3) + (x + x) + 11 and x * 5 + 11 have the form
  // 5x + 11. For a defined x all of them are related exactly to the same
  // canonical implementation and become one class.
  EClassId X = in(true);
  EClassId A = add(add(shl(X, cst(2)), X), cst(11));
  EClassId B = add(add(mul(X, cst(3)), add(X, X)), cst(11));
  EClassId C = add(mul(X, cst(5)), cst(11));
  // For an x that may be undef, A and B read x twice: both only refine to
  // 5x + 11, and they stay apart.
  EClassId U = in();
  EClassId AU = add(add(shl(U, cst(2)), U), cst(11));
  EClassId BU = add(add(mul(U, cst(3)), add(U, U)), cst(11));
  EClassId CU = add(mul(U, cst(5)), cst(11));
  linearOnce();
  EXPECT_TRUE(G.equivalent(A, C));
  EXPECT_TRUE(G.equivalent(B, C));
  EXPECT_FALSE(G.equivalent(AU, CU));
  EXPECT_FALSE(G.equivalent(BU, CU));
  EXPECT_FALSE(G.equivalent(AU, BU));
  EXPECT_TRUE(G.refinesTo(AU, CU));
  EXPECT_TRUE(G.refinesTo(BU, CU));
}

TEST_F(GIEGraphSumsTest, LinearOriginalFormStaysInTheClass) {
  // (x << 2) + x + c and 5x + c are one class; the shift form stays in it,
  // so a cost model with an expensive multiplication still has it.
  EClassId X = in(true), C = in();
  EClassId A = add(add(shl(X, cst(2)), X), C);
  EClassId B = add(mul(X, cst(5)), C);
  runAll();
  ASSERT_TRUE(G.equivalent(A, B));
  std::string Cheap = extract(A, /*MulCost=*/10);
  EXPECT_NE(Cheap.find("G_SHL"), std::string::npos) << Cheap;
  EXPECT_EQ(Cheap.find("G_MUL"), std::string::npos) << Cheap;
  // With the default costs (a multiplication costs as much as a shift and
  // an add) a tie keeps a form with a shift too.
  EXPECT_EQ(extract(A).find("G_MUL"), std::string::npos) << extract(A);
}

TEST_F(GIEGraphSumsTest, LinearCoefficientsWrapAround) {
  // In 32 bits, x * 2^31 + x * 2^31 is 0, as is (x << 31) << 1; in 8 bits
  // x * 200 + x * 100 is x * 44.
  EClassId X = in(true);
  EClassId A = add(mul(X, cst(INT32_MIN)), mul(X, cst(INT32_MIN)));
  EClassId B = shl(shl(X, cst(31)), cst(1));
  EClassId X8 = in(S8, true);
  EClassId C = add(mul(X8, cst(200, S8)), mul(X8, cst(100, S8)));
  // x * -1 + x is 0.
  EClassId D = add(mul(X, cst(-1)), X);
  linearOnce();
  EClassId Zero = lookup([&] { return cst(0); });
  EXPECT_TRUE(G.equivalent(A, Zero));
  EXPECT_TRUE(G.equivalent(B, Zero));
  EXPECT_TRUE(G.equivalent(D, Zero));
  EXPECT_TRUE(G.equivalent(C, lookup([&] { return mul(X8, cst(44, S8)); })));
  // A value that may be poison is only refined to 0 when it is dropped.
  EClassId P = inNotUndef();
  EClassId E = shl(shl(P, cst(31)), cst(1));
  linearOnce();
  EXPECT_FALSE(G.equivalent(E, Zero));
  EXPECT_TRUE(G.refinesTo(E, Zero));
}

TEST_F(GIEGraphSumsTest, LinearNonLinearTermsAreOpaque) {
  // x * y and x << y are leaves: (p + p) - p is p for p = x * y, and the
  // view never sees x or y inside them.
  EClassId X = in(true), Y = in(true);
  EClassId P = mul(X, Y);
  EClassId Q = shl(X, Y);
  EClassId A = sub(add(P, P), P);
  EClassId B = sub(add(Q, X), X);
  // No polynomial expansion: (x + 1) * (y + 1) - x * y is not x + y + 1.
  EClassId C = sub(mul(add(X, cst(1)), add(Y, cst(1))), P);
  linearOnce();
  EXPECT_TRUE(G.equivalent(A, P));
  EXPECT_TRUE(G.equivalent(B, Q));
  EXPECT_FALSE(G.equivalent(C, lookup([&] { return add(add(X, Y), cst(1)); })));
  EXPECT_FALSE(G.equivalent(Q, P));
}

TEST_F(GIEGraphSumsTest, LinearOutOfRangeShiftIsALeaf) {
  // x << 32 is poison in 32 bits, not x * 2^32 == 0: (x << 32) + y must not
  // become y, even for a defined x.
  EClassId X = in(true), Y = in(true);
  EClassId S = shl(X, cst(32));
  EClassId A = add(S, Y);
  // (s + x) - s with the poison leaf s is only refined to x.
  EClassId B = sub(add(S, X), S);
  linearOnce();
  EXPECT_FALSE(G.equivalent(A, Y));
  EXPECT_FALSE(G.refinesTo(A, Y));
  EXPECT_FALSE(G.equivalent(B, X));
  EXPECT_TRUE(G.refinesTo(B, X));
  EXPECT_EQ(G.getClass(S).Nodes.size(), 1u);
}

TEST_F(GIEGraphSumsTest, LinearFlaggedNodesAreLeaves) {
  // add nsw (x, x) may be poison where x is not: (x +nsw x) - x is not x,
  // whereas (x + x) - x is.
  const uint32_t NSW = MachineInstr::NoSWrap;
  EClassId X = in(true);
  EClassId A = sub(op(G_ADD, X, X, NSW), X);
  EClassId B = sub(add(X, X), X);
  EClassId C = sub(op(G_SHL, X, cst(3), NSW), mul(X, cst(8)));
  linearOnce();
  EXPECT_FALSE(G.equivalent(A, X));
  EXPECT_TRUE(G.equivalent(B, X));
  EXPECT_FALSE(G.equivalent(C, lookup([&] { return cst(0); })));
  // The table rules can drop the flag, which only refines.
  runAll();
  EXPECT_FALSE(G.equivalent(A, X));
  EXPECT_FALSE(G.equivalent(C, lookup([&] { return cst(0); })));
}

TEST_F(GIEGraphSumsTest, LinearMaybeUndefIsOnlyRefined) {
  // x + x - x reads x three times and the result once: exact iff x is not
  // undef. Poison does not matter: both sides are poison iff x is.
  EClassId U = in(), N = inNotUndef(), D = in(true);
  EClassId RU = sub(add(U, U), U);
  EClassId RN = sub(add(N, N), N);
  EClassId RD = sub(add(D, D), D);
  linearOnce();
  EXPECT_FALSE(G.equivalent(RU, U));
  EXPECT_TRUE(G.refinesTo(RU, U));
  EXPECT_TRUE(G.equivalent(RN, N));
  EXPECT_TRUE(G.equivalent(RD, D));
}

TEST_F(GIEGraphSumsTest, LinearDroppedPoisonIsOnlyRefined) {
  // x - x + y drops x: exact iff x is neither undef nor poison.
  EClassId Y = in();
  EClassId U = in(), N = inNotUndef(), D = in(true);
  EClassId RU = add(sub(U, U), Y);
  EClassId RN = add(sub(N, N), Y);
  EClassId RD = add(sub(D, D), Y);
  linearOnce();
  EXPECT_FALSE(G.equivalent(RU, Y));
  EXPECT_TRUE(G.refinesTo(RU, Y));
  EXPECT_FALSE(G.equivalent(RN, Y));
  EXPECT_TRUE(G.refinesTo(RN, Y));
  EXPECT_TRUE(G.equivalent(RD, Y));
}

TEST_F(GIEGraphSumsTest, LinearVectorsArePerLane) {
  // <2 x s32> with splat constants: the arithmetic of each lane, in 32 bits.
  EClassId X = in(V2S32, true), Y = in(V2S32, true);
  EClassId R =
      add(sub(add(shl(X, cst(3, V2S32)), X), add(Y, Y)), cst(7, V2S32));
  // 2^31 + 2^31 wraps around in a lane; as one 64-bit integer it would not.
  EClassId W =
      add(mul(X, cst(INT32_MIN, V2S32)), mul(X, cst(INT32_MIN, V2S32)));
  ViewStats S = linearOnce();
  EClassId Canon = lookup([&] {
    EClassId Diff = sub(mul(X, cst(9, V2S32)), shl(Y, cst(1, V2S32)));
    return add(Diff, cst(7, V2S32));
  });
  EXPECT_TRUE(G.equivalent(R, Canon));
  EXPECT_TRUE(G.equivalent(W, lookup([&] { return cst(0, V2S32); })));
  EXPECT_EQ(S.Unsupported, 0u);
}

TEST_F(GIEGraphSumsTest, LinearNonSplatVectorIsUnsupported) {
  // A constant with different lanes would need a coefficient per lane.
  EClassId X = in(V2S32, true);
  EClassId K = G.addOp(G_BUILD_VECTOR, V2S32, {cst(1), cst(2)});
  EClassId A = sub(add(X, K), K);
  EClassId B = add(mul(X, K), X);
  ViewStats S = linearOnce();
  EXPECT_FALSE(G.equivalent(A, X));
  EXPECT_FALSE(G.refinesTo(A, X));
  EXPECT_GE(S.Unsupported, 2u);
  EXPECT_EQ(S.Candidates, 0u);
  (void)B;
}

TEST_F(GIEGraphSumsTest, LinearShiftAddFormsNeedADefinedTerm) {
  // (x * 7) + (x * 3) is x * 10, and 10 = 8 + 2 gives (x << 3) + (x << 1),
  // which reads x twice. (x * 9) - (x * 16) is x * -7 = x - (x << 3).
  EClassId X = in(true), U = in();
  EClassId A = add(mul(X, cst(7)), mul(X, cst(3)));
  EClassId B = sub(mul(X, cst(9)), mul(X, cst(16)));
  EClassId AU = add(mul(U, cst(7)), mul(U, cst(3)));
  ViewStats S = linearOnce();
  EXPECT_TRUE(G.equivalent(A, lookup([&] { return mul(X, cst(10)); })));
  EXPECT_TRUE(G.equivalent(
      A, lookup([&] { return add(shl(X, cst(3)), shl(X, cst(1))); })));
  EXPECT_TRUE(G.equivalent(B, lookup([&] { return mul(X, cst(-7)); })));
  EXPECT_TRUE(G.equivalent(B, lookup([&] { return sub(X, shl(X, cst(3))); })));
  // For an x that may be undef, x * 10 is only a refinement of AU and the
  // shift-add form is not related to it.
  EClassId SA = lookup([&] { return add(shl(U, cst(3)), shl(U, cst(1))); });
  EXPECT_TRUE(G.refinesTo(AU, lookup([&] { return mul(U, cst(10)); })));
  EXPECT_FALSE(G.equivalent(AU, SA));
  EXPECT_FALSE(G.refinesTo(AU, SA));
  EXPECT_GE(S.Unsafe, 1u);
}

TEST_F(GIEGraphSumsTest, LinearBudgetsAreCounted) {
  // A view with more terms, visits or candidates than allowed is abandoned
  // (counted), and the class keeps its nodes.
  auto Build = [&] {
    EClassId A = in(true), B = in(true), C = in(true);
    return std::make_tuple(sub(add(add(A, B), C), C), A, B);
  };
  {
    EClassId R, A, B;
    std::tie(R, A, B) = Build();
    SaturationLimits L;
    L.MaxViewTerms = 2;
    ViewStats S = linearOnce(L);
    EXPECT_GE(S.Budget, 1u);
    EXPECT_FALSE(G.equivalent(R, lookup([&] { return add(A, B); })));
  }
  G = EGraph();
  {
    EClassId R, A, B;
    std::tie(R, A, B) = Build();
    SaturationLimits L;
    L.MaxViewVisits = 3;
    ViewStats S = linearOnce(L);
    EXPECT_GE(S.Budget, 1u);
    EXPECT_FALSE(G.equivalent(R, lookup([&] { return add(A, B); })));
  }
  G = EGraph();
  {
    EClassId R, A, B;
    std::tie(R, A, B) = Build();
    SaturationLimits L;
    L.MaxViewCandidates = 0;
    ViewStats S = linearOnce(L);
    EXPECT_GE(S.Budget, 1u);
    EXPECT_FALSE(G.equivalent(R, lookup([&] { return add(A, B); })));
  }
  G = EGraph();
  {
    // At the node limit, no implementation is built.
    EClassId X = in(true);
    add(add(shl(X, cst(3)), X), cst(7));
    G.rebuild();
    SaturationLimits L;
    L.MaxNodes = G.getNumNodes();
    unsigned Before = G.getNumNodes();
    ViewStats S = linearOnce(L);
    EXPECT_EQ(S.Budget, 1u);
    EXPECT_EQ(G.getNumNodes(), Before);
  }
  G = EGraph();
  {
    // Within the budgets the same view simplifies.
    EClassId R, A, B;
    std::tie(R, A, B) = Build();
    ViewStats S = linearOnce();
    EXPECT_EQ(S.Budget, 0u);
    EXPECT_TRUE(G.equivalent(R, lookup([&] { return add(A, B); })));
  }
}

TEST_F(GIEGraphSumsTest, LinearViewCanBeTurnedOff) {
  EClassId X = in(), Y = in();
  EClassId R = sub(add(mul(X, cst(3)), mul(Y, cst(2))), add(add(X, X), X));
  SaturationLimits L;
  L.EnableLinear = false;
  L.MaxIterations = 1;
  SaturationStats S = runAll(L);
  EXPECT_EQ(S.Views.count("linear"), 0u);
  EXPECT_NE(extract(R), "(G_SHL %in1 1)");
}

std::string buildAndExtract() {
  EGraph G;
  LLT S32 = LLT::scalar(32);
  auto In = [&] {
    InputInfo I;
    I.Ty = S32;
    return G.addInput(I);
  };
  auto Cst = [&](int64_t V) { return G.addConstant(S32, APInt(32, V)); };
  auto Op = [&](unsigned Opc, EClassId A, EClassId B) {
    return G.addOp(Opc, S32, {A, B});
  };
  EClassId X = In(), Y = In(), Z = In();
  EClassId R1 =
      Op(G_ADD, Op(G_SUB, Op(G_ADD, Op(G_SHL, X, Cst(3)), X), Op(G_ADD, Y, Y)),
         Cst(7));
  EClassId R2 = Op(G_SUB, Op(G_ADD, Op(G_MUL, X, Cst(3)), Op(G_MUL, Z, Cst(2))),
                   Op(G_ADD, Op(G_ADD, X, X), X));
  std::vector<RewriteRule> Rules = getDefaultIntegerRules();
  SaturationStats S = saturate(G, Rules, SaturationLimits());
  Extractor E(G, DefaultCostModel());
  const ViewStats &V = S.Views["linear"];
  return E.getExprString(R1) + " " + E.getExprString(R2) +
         " nodes=" + std::to_string(G.getNumNodes()) +
         " views=" + std::to_string(V.Views) +
         " candidates=" + std::to_string(V.Candidates) +
         " merges=" + std::to_string(V.Merges) +
         " refinements=" + std::to_string(V.Refinements);
}

TEST_F(GIEGraphSumsTest, LinearViewIsDeterministic) {
  std::string First = buildAndExtract();
  for (int I = 0; I < 3; ++I)
    EXPECT_EQ(First, buildAndExtract());
}

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
