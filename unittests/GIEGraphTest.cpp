//===- GIEGraphTest.cpp - Unit tests for the gMIR e-graph -----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/GlobalISel/GIEGraph.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "gtest/gtest.h"

using namespace llvm;
using namespace llvm::egraph;

namespace {

class GIEGraphTest : public testing::Test {
protected:
  EGraph G;
  const LLT S32 = LLT::scalar(32);
  const LLT S64 = LLT::scalar(64);

  /// A symbolic input. "Defined" inputs are known not undef and not poison
  /// (e.g. frozen values).
  EClassId in(LLT Ty, bool Defined = false) {
    return G.addInput({Ty, Defined, Defined});
  }
  EClassId in(bool Defined = false) { return in(S32, Defined); }
  EClassId cst(int64_t V, LLT Ty) {
    return G.addConstant(Ty, APInt(Ty.getSizeInBits(), V, /*isSigned=*/true));
  }
  EClassId cst(int64_t V) { return cst(V, S32); }
  EClassId op(unsigned Opc, EClassId A, EClassId B, uint32_t Flags = 0) {
    return G.addOp(Opc, G.getType(A), {A, B}, Flags);
  }
  EClassId add(EClassId A, EClassId B) { return op(TargetOpcode::G_ADD, A, B); }
  EClassId sub(EClassId A, EClassId B) { return op(TargetOpcode::G_SUB, A, B); }
  EClassId mul(EClassId A, EClassId B) { return op(TargetOpcode::G_MUL, A, B); }
  EClassId shl(EClassId A, EClassId B) { return op(TargetOpcode::G_SHL, A, B); }

  static std::vector<RewriteRule> rules(ArrayRef<StringRef> Names) {
    std::vector<RewriteRule> All = getDefaultIntegerRules(), Out;
    for (StringRef N : Names) {
      bool Found = false;
      for (const RewriteRule &R : All)
        if (R.getName() == N) {
          Out.push_back(R);
          Found = true;
        }
      EXPECT_TRUE(Found) << "no rule named " << N.str();
    }
    return Out;
  }

  SaturationStats run(ArrayRef<RewriteRule> Rules,
                      SaturationLimits Limits = SaturationLimits()) {
    return saturate(G, Rules, Limits);
  }
  SaturationStats runAll(SaturationLimits Limits = SaturationLimits()) {
    std::vector<RewriteRule> All = getDefaultIntegerRules();
    return saturate(G, All, Limits);
  }

  /// Look up (or create) a class after saturation and rebuild.
  EClassId lookup(function_ref<EClassId()> Build) {
    EClassId Id = Build();
    G.rebuild();
    return G.find(Id);
  }
};

//===----------------------------------------------------------------------===//
// Core e-graph behaviour
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphTest, HashConsing) {
  EClassId A = in(), B = in();
  EClassId X = add(A, B);
  EClassId Y = add(A, B);
  EXPECT_EQ(X, Y);
  EXPECT_NE(add(B, A), X); // No commutativity without rules.
  EXPECT_EQ(cst(7), cst(7));
  EXPECT_EQ(G.getNumNodes(), 5u);
}

TEST_F(GIEGraphTest, InputsAreDistinct) {
  // Two inputs with the same type are never assumed equal.
  EClassId A = in(), B = in();
  EXPECT_NE(A, B);
  runAll();
  EXPECT_FALSE(G.equivalent(A, B));
}

TEST_F(GIEGraphTest, TypeSeparation) {
  EXPECT_NE(cst(0, S32), cst(0, S64));
  EClassId A32 = in(S32), A64 = in(S64);
  EClassId Z32 = add(A32, cst(0, S32));
  EClassId Z64 = add(A64, cst(0, S64));
  runAll();
  EXPECT_TRUE(G.equivalent(Z32, A32));
  EXPECT_TRUE(G.equivalent(Z64, A64));
  EXPECT_FALSE(G.equivalent(A32, A64));
  EXPECT_EQ(G.getType(Z64), S64);
}

TEST_F(GIEGraphTest, ConstantIdentityUsesWidth) {
  // -1 must be "all ones" of the right width.
  EClassId A64 = in(S64);
  EClassId X = op(TargetOpcode::G_AND, A64, cst(-1, S64));
  EClassId Y = op(TargetOpcode::G_AND, A64, cst(0xffffffff, S64));
  run(rules({"and-ones"}));
  EXPECT_TRUE(G.equivalent(X, A64));
  EXPECT_FALSE(G.equivalent(Y, A64));
}

TEST_F(GIEGraphTest, MergeAndCongruence) {
  EClassId A = in(), B = in(), C = in();
  EClassId X = add(add(A, C), C);
  EClassId Y = add(add(B, C), C);
  EXPECT_FALSE(G.equivalent(X, Y));
  EXPECT_TRUE(G.merge(A, B));
  EXPECT_FALSE(G.merge(A, B));
  G.rebuild();
  EXPECT_TRUE(G.equivalent(X, Y));
  EXPECT_TRUE(G.equivalent(add(A, C), add(B, C)));
}

TEST_F(GIEGraphTest, RebuildDeduplicatesNodes) {
  EClassId A = in(), B = in();
  EClassId X = add(A, A), Y = add(B, B);
  unsigned Before = G.getNumNodes();
  G.merge(A, B);
  G.rebuild();
  EXPECT_TRUE(G.equivalent(X, Y));
  // a, b (two input nodes in one class) and one add node.
  EXPECT_EQ(G.getNumNodes(), Before - 1);
  EXPECT_EQ(G.getClass(X).Nodes.size(), 1u);
}

//===----------------------------------------------------------------------===//
// Rewriting
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphTest, Commutativity) {
  EClassId A = in(), B = in();
  EClassId X = add(A, B), Y = add(B, A);
  SaturationStats S = run(rules({"add-comm"}));
  EXPECT_TRUE(G.equivalent(X, Y));
  EXPECT_TRUE(S.Saturated);
}

TEST_F(GIEGraphTest, Associativity) {
  EClassId A = in(), B = in(), C = in();
  EClassId X = add(add(A, B), C), Y = add(A, add(B, C));
  run(rules({"add-assoc-r"}));
  EXPECT_TRUE(G.equivalent(X, Y));
}

TEST_F(GIEGraphTest, FlaggedNodesAreOnlyRefined) {
  // Flags are part of the node identity and flagged nodes are never merged
  // with unflagged ones: "add nsw a, b" may be poison where "add a, b" is not.
  EClassId A = in(), B = in();
  EClassId X = op(TargetOpcode::G_ADD, A, B, MachineInstr::NoSWrap);
  EClassId Y = op(TargetOpcode::G_ADD, B, A, MachineInstr::NoSWrap);
  EClassId Z = add(A, B);
  runAll();
  EXPECT_FALSE(G.equivalent(X, Y));
  EXPECT_FALSE(G.equivalent(X, Z));
  // Dropping the flag is a refinement, so the commuted unflagged add refines
  // the flagged one, but not the other way around.
  EXPECT_TRUE(G.refinesTo(X, Z));
  EXPECT_FALSE(G.refinesTo(Z, X));
  EXPECT_FALSE(G.refinesTo(Z, Y));
  // add nsw (a, 0) is refined by a, but not equal to it.
  EClassId W = op(TargetOpcode::G_ADD, A, cst(0), MachineInstr::NoSWrap);
  runAll();
  EXPECT_FALSE(G.equivalent(W, A));
  EXPECT_TRUE(G.refinesTo(W, A));
  // Extraction keeps the flagged node unless the refinement is cheaper.
  Extractor E(G, DefaultCostModel());
  EXPECT_EQ(E.getChosenNode(X)->Flags, uint32_t(MachineInstr::NoSWrap));
  EXPECT_TRUE(E.getChosenNode(W)->isInput());
}

TEST_F(GIEGraphTest, ConstantFolding) {
  EClassId A = in();
  EClassId X = mul(add(cst(2), cst(3)), A);
  EClassId Y = add(add(A, cst(5)), cst(-5));
  runAll();
  EXPECT_EQ(G.getConstant(add(cst(2), cst(3)))->getZExtValue(), 5u);
  G.rebuild();
  EXPECT_TRUE(G.equivalent(X, mul(A, cst(5))));
  G.rebuild();
  EXPECT_TRUE(G.equivalent(Y, A));
}

TEST_F(GIEGraphTest, ShiftSemantics) {
  EClassId A = in();
  EClassId X = shl(A, cst(3));
  EClassId Big = shl(A, cst(40)); // poison for s32: must not be touched.
  EClassId FoldBig = shl(cst(1), cst(32));
  runAll();
  EXPECT_TRUE(G.equivalent(X, mul(A, cst(8))));
  G.rebuild();
  EXPECT_FALSE(G.getConstant(FoldBig).has_value());
  EXPECT_EQ(G.getClass(Big).Nodes.size(), 1u);
  EXPECT_FALSE(G.getClass(Big).NotPoison);
  // The shift amount may have a different type than the shifted value.
  EClassId A64 = in(S64);
  EClassId Y = shl(A64, cst(4, S32));
  runAll();
  EXPECT_TRUE(G.equivalent(Y, mul(A64, cst(16, S64))));
}

TEST_F(GIEGraphTest, MulByPowerOfTwo) {
  EClassId A = in(S64);
  EClassId X = mul(A, cst(int64_t(1) << 40, S64));
  run(rules({"mul-pow2-to-shl"}));
  EXPECT_TRUE(G.equivalent(X, shl(A, cst(40, S64))));
  // Not a power of two.
  EClassId Y = mul(A, cst(12, S64));
  run(rules({"mul-pow2-to-shl"}));
  EXPECT_EQ(G.getClass(Y).Nodes.size(), 1u);
}

//===----------------------------------------------------------------------===//
// Undef / poison safety
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphTest, SelfCancellationIsOnlyARefinement) {
  // x - x may be undef/poison when x is, so it is not *equal* to 0, but 0
  // refines it.
  EClassId X = in();
  EClassId D = sub(X, X);
  EClassId Zero = cst(0);
  SaturationStats S = run(rules({"sub-self"}));
  EXPECT_FALSE(G.equivalent(D, Zero));
  EXPECT_TRUE(G.refinesTo(D, Zero));
  EXPECT_FALSE(G.refinesTo(Zero, D));
  EXPECT_EQ(S.Refinements, 1u);
  EXPECT_EQ(S.Merges, 0u);
}

TEST_F(GIEGraphTest, SelfCancellationOfDefinedValueIsExact) {
  EClassId X = in(/*Defined=*/true);
  EClassId D = op(TargetOpcode::G_XOR, X, X);
  run(rules({"xor-self"}));
  EXPECT_TRUE(G.equivalent(D, cst(0)));
}

TEST_F(GIEGraphTest, UndefInputBlocksDuplication) {
  // shl a, 1 must never be rewritten to a + a for a possibly-undef a.
  EClassId A = in();
  EClassId X = shl(A, cst(1));
  EClassId Y = add(A, A);
  runAll();
  EXPECT_FALSE(G.equivalent(X, Y));
  EXPECT_FALSE(G.refinesTo(X, Y));
  // ... but a + a may be replaced by a << 1 (via a * 2).
  EXPECT_TRUE(G.refinesTo(Y, X));
}

TEST_F(GIEGraphTest, ImplicitDefLikeInputs) {
  // An input that may be undef keeps "and a, a -> a" one-directional.
  EClassId U = in();
  EClassId X = op(TargetOpcode::G_AND, U, U);
  run(rules({"and-self"}));
  EXPECT_FALSE(G.equivalent(X, U));
  EXPECT_TRUE(G.refinesTo(X, U));
}

TEST_F(GIEGraphTest, AbsorbingRequiresNotPoison) {
  EClassId A = in(), F = in(/*Defined=*/true);
  EClassId X = mul(A, cst(0));
  EClassId Y = mul(F, cst(0));
  run(rules({"mul-zero"}));
  EXPECT_FALSE(G.equivalent(X, cst(0)));
  EXPECT_TRUE(G.refinesTo(X, cst(0)));
  EXPECT_TRUE(G.equivalent(Y, cst(0)));
}

TEST_F(GIEGraphTest, RefinementDoesNotLeakIntoEquality) {
  // Even though x - x ~> 0, an unrelated use of 0 must never be replaced by
  // x - x: the constant class must not acquire the subtraction.
  EClassId X = in();
  EClassId D = sub(X, X);
  EClassId Zero = cst(0);
  EClassId Y = add(in(), Zero);
  runAll();
  Extractor E(G, DefaultCostModel());
  EXPECT_EQ(E.getChosenNode(Zero)->Kind, ENodeKind::Constant);
  EXPECT_FALSE(G.refinesTo(Zero, D));
  (void)Y;
}

//===----------------------------------------------------------------------===//
// Saturation limits and determinism
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphTest, SaturationTerminatesWithNodeLimit) {
  // A long chain of additions blows up under AC rules.
  EClassId Acc = in();
  for (int I = 0; I < 12; ++I)
    Acc = add(Acc, in());
  SaturationLimits L;
  L.MaxNodes = 500;
  L.MaxIterations = 50;
  SaturationStats S = runAll(L);
  EXPECT_TRUE(S.HitNodeLimit);
  EXPECT_FALSE(S.Saturated);
  // Each iteration may overshoot by at most the nodes of a single RHS.
  EXPECT_LT(G.getNumNodes(), 520u);
}

TEST_F(GIEGraphTest, AdditiveIdentitySaturates) {
  // Once a == a + 0, every class can be re-expressed through itself. Without
  // pruning of constant classes, the class of 0 accumulates 0 + 0, 0 * 2,
  // 0 << 1, ... and the factoring/folding rules keep producing fresh
  // constants, so this tiny region used to hit the node limit.
  EClassId A = in(), C = in(), D = in();
  EClassId T = add(A, cst(0));
  EClassId U = mul(T, C);
  EClassId V = op(TargetOpcode::G_XOR, T, D);
  SaturationStats S = runAll();
  EXPECT_TRUE(S.Saturated);
  EXPECT_LT(G.getNumNodes(), 50u);
  EXPECT_TRUE(G.equivalent(T, A));
  Extractor E(G, DefaultCostModel());
  EXPECT_EQ(E.getDagCost({U, V}), 3u);
  // The constant class keeps only its constant leaf.
  EXPECT_EQ(G.getClass(cst(0)).Nodes.size(), 1u);
}

TEST_F(GIEGraphTest, BackoffBansExplosiveRules) {
  // With a low per-rule match limit, the AC rules on a long sum get banned
  // instead of flooding the graph, and the graph stays much smaller.
  auto Build = [&] {
    EClassId Acc = in();
    for (int I = 0; I < 8; ++I)
      Acc = add(Acc, in());
  };
  SaturationLimits L;
  L.MaxIterations = 6;
  L.MaxNodes = 1000000;
  L.RuleMatchLimit = 0; // No backoff.
  Build();
  SaturationStats NoBackoff = runAll(L);
  unsigned NodesNoBackoff = G.getNumNodes();
  EXPECT_EQ(NoBackoff.Bans, 0u);

  G = EGraph();
  L.RuleMatchLimit = 16;
  Build();
  SaturationStats Backoff = runAll(L);
  EXPECT_GT(Backoff.Bans, 0u);
  EXPECT_FALSE(Backoff.Saturated);
  EXPECT_LT(G.getNumNodes(), NodesNoBackoff);
}

TEST_F(GIEGraphTest, SaturationTerminatesWithIterationLimit) {
  EClassId Acc = in();
  for (int I = 0; I < 6; ++I)
    Acc = add(Acc, in());
  SaturationLimits L;
  L.MaxIterations = 2;
  L.MaxNodes = 1000000;
  SaturationStats S = runAll(L);
  EXPECT_EQ(S.Iterations, 2u);
  EXPECT_TRUE(S.HitIterationLimit);
}

static std::string buildAndExtract() {
  EGraph G;
  LLT S32 = LLT::scalar(32);
  auto In = [&] { return G.addInput({S32, false, false}); };
  EClassId A = In(), B = In(), C = In(), D = In();
  auto Op = [&](unsigned Opc, EClassId X, EClassId Y) {
    return G.addOp(Opc, S32, {X, Y});
  };
  EClassId Root = Op(TargetOpcode::G_ADD,
                     Op(TargetOpcode::G_MUL, Op(TargetOpcode::G_ADD, A, B), C),
                     Op(TargetOpcode::G_MUL, Op(TargetOpcode::G_ADD, B, A), D));
  std::vector<RewriteRule> Rules = getDefaultIntegerRules();
  SaturationStats S = saturate(G, Rules, SaturationLimits());
  Extractor E(G, DefaultCostModel());
  return E.getExprString(Root) + " nodes=" + std::to_string(G.getNumNodes()) +
         " merges=" + std::to_string(S.Merges);
}

TEST_F(GIEGraphTest, Deterministic) {
  std::string First = buildAndExtract();
  for (int I = 0; I < 3; ++I)
    EXPECT_EQ(First, buildAndExtract());
}

//===----------------------------------------------------------------------===//
// Extraction
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphTest, ExtractionAvoidsCycles) {
  // After merging a + 0 with a, the class contains a node referring to
  // itself. Extraction must pick the input.
  EClassId A = in();
  EClassId X = add(A, cst(0));
  run(rules({"add-zero"}));
  ASSERT_TRUE(G.equivalent(X, A));
  Extractor E(G, DefaultCostModel());
  EXPECT_TRUE(E.getChosenNode(X)->isInput());
  EXPECT_EQ(E.getTreeCost(X), 0u);
}

TEST_F(GIEGraphTest, ExtractionWithRefinementCycle) {
  EClassId A = in(), B = in();
  EClassId X = add(A, B), Y = mul(A, B);
  G.addRefinement(X, Y);
  G.addRefinement(Y, X);
  G.rebuild();
  Extractor E(G, DefaultCostModel());
  EXPECT_EQ(E.getTreeCost(X), 1u);
  EXPECT_EQ(E.getTreeCost(Y), 1u);
  EXPECT_EQ(E.getChosenNode(Y)->Opcode, unsigned(TargetOpcode::G_ADD));
}

TEST_F(GIEGraphTest, DagCostCountsSharedOnce) {
  EClassId A = in(), B = in();
  EClassId S = add(A, B);
  EClassId Root = mul(S, S);
  G.rebuild();
  Extractor E(G, DefaultCostModel());
  EXPECT_EQ(E.getTreeCost(Root), 4u); // mul(2) + add(1) + add(1)
  EXPECT_EQ(E.getDagCost({Root}), 3u);
}

//===----------------------------------------------------------------------===//
// Multi-rule composition
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphTest, FactoringThroughCommutativity) {
  // (a + b) * c + (b + a) * d  ==>  (a + b) * (c + d)
  EClassId A = in(), B = in(), C = in(), D = in();
  EClassId Root = add(mul(add(A, B), C), mul(add(B, A), D));
  runAll();
  EClassId Want = lookup([&] { return mul(add(A, B), add(C, D)); });
  // a + b may be undef: factoring is a refinement, not an equivalence.
  EXPECT_FALSE(G.equivalent(Root, Want));
  EXPECT_TRUE(G.refinesTo(Root, Want));
  Extractor E(G, DefaultCostModel());
  EXPECT_EQ(E.getDagCost({Root}), 4u);
}

TEST_F(GIEGraphTest, FactoringOfDefinedValuesIsExact) {
  EClassId A = in(true), B = in(true), C = in(), D = in();
  EClassId Root = add(mul(add(A, B), C), mul(add(B, A), D));
  runAll();
  EClassId Want = lookup([&] { return mul(add(A, B), add(C, D)); });
  EXPECT_TRUE(G.equivalent(Root, Want));
}

//===----------------------------------------------------------------------===//
// Coverage of existing GlobalISel integer_reassoc_combines (Combine.td).
//===----------------------------------------------------------------------===//

struct CoverageCase {
  const char *Name;
  // Builds (original, expected) in the fixture.
  std::function<std::pair<EClassId, EClassId>(GIEGraphTest &)> Build;
};

class GIEGraphCoverageTest : public GIEGraphTest {
public:
  using GIEGraphTest::add;
  using GIEGraphTest::cst;
  using GIEGraphTest::in;
  using GIEGraphTest::sub;

  /// Returns true if \p Expected is reachable (equal or refining) from the
  /// original expression, and whether extraction picks something no more
  /// expensive than the expected expression.
  void check(EClassId Orig, function_ref<EClassId()> BuildExpected,
             uint64_t ExpectedCost) {
    runAll();
    EClassId Exp = lookup(BuildExpected);
    EXPECT_TRUE(G.refinesTo(Orig, Exp));
    Extractor E(G, DefaultCostModel());
    EXPECT_LE(E.getDagCost({Orig}), ExpectedCost);
  }
};

TEST_F(GIEGraphCoverageTest, APlusBMinusCMinusB) {
  // ((A + (B - C)) - B) -> A - C
  EClassId A = in(), B = in(), C = in();
  check(sub(add(A, sub(B, C)), B), [&] { return sub(A, C); }, 1);
}

TEST_F(GIEGraphCoverageTest, AMinusBMinusCMinusC) {
  // ((A - (B - C)) - C) -> A - B
  EClassId A = in(), B = in(), C = in();
  check(sub(sub(A, sub(B, C)), C), [&] { return sub(A, B); }, 1);
}

TEST_F(GIEGraphCoverageTest, ZeroMinusAPlusB) {
  // ((0 - A) + B) -> B - A
  EClassId A = in(), B = in();
  check(add(sub(cst(0), A), B), [&] { return sub(B, A); }, 1);
}

TEST_F(GIEGraphCoverageTest, APlusZeroMinusB) {
  // (A + (0 - B)) -> A - B
  EClassId A = in(), B = in();
  check(add(A, sub(cst(0), B)), [&] { return sub(A, B); }, 1);
}

TEST_F(GIEGraphCoverageTest, APlusBMinusA) {
  // (A + (B - A)) -> B
  EClassId A = in(), B = in();
  check(add(A, sub(B, A)), [&] { return B; }, 0);
}

TEST_F(GIEGraphCoverageTest, BMinusAPlusA) {
  // ((B - A) + A) -> B
  EClassId A = in(), B = in();
  check(add(sub(B, A), A), [&] { return B; }, 0);
}

TEST_F(GIEGraphCoverageTest, AMinusBPlusCMinusA) {
  // ((A - B) + (C - A)) -> C - B
  EClassId A = in(), B = in(), C = in();
  check(add(sub(A, B), sub(C, A)), [&] { return sub(C, B); }, 1);
}

TEST_F(GIEGraphCoverageTest, AMinusBPlusBMinusC) {
  // ((A - B) + (B - C)) -> A - C
  EClassId A = in(), B = in(), C = in();
  check(add(sub(A, B), sub(B, C)), [&] { return sub(A, C); }, 1);
}

TEST_F(GIEGraphCoverageTest, APlusBMinusAPlusC) {
  // (A + (B - (A + C))) -> B - C
  EClassId A = in(), B = in(), C = in();
  check(add(A, sub(B, add(A, C))), [&] { return sub(B, C); }, 1);
}

TEST_F(GIEGraphCoverageTest, AMinusBMinusC) {
  // (A - (B - C)) -> A + (C - B). Same cost; checks reachability only.
  EClassId A = in(), B = in(), C = in();
  check(sub(A, sub(B, C)), [&] { return add(A, sub(C, B)); }, 2);
}

TEST_F(GIEGraphCoverageTest, AMinusZeroMinusB) {
  // (A - (0 - B)) -> A + B
  EClassId A = in(), B = in();
  check(sub(A, sub(cst(0), B)), [&] { return add(A, B); }, 1);
}

TEST_F(GIEGraphCoverageTest, AMinusAMinusB) {
  // AMinusBMinusA: A - (A - B) -> B
  EClassId A = in(), B = in();
  check(sub(A, sub(A, B)), [&] { return B; }, 0);
}

TEST_F(GIEGraphCoverageTest, NotAPlusNegOne) {
  // (not (A + -1)) -> 0 - A
  EClassId A = in();
  check(
      op(TargetOpcode::G_XOR, add(A, cst(-1)), cst(-1)),
      [&] { return sub(cst(0), A); }, 1);
}

TEST_F(GIEGraphCoverageTest, APlusBMinusCPlusA) {
  // (A + (B - (C + A))) -> B - C
  EClassId A = in(), B = in(), C = in();
  check(add(A, sub(B, add(C, A))), [&] { return sub(B, C); }, 1);
}

TEST_F(GIEGraphCoverageTest, APlusC1MinusC2) {
  // (A + C1) - C2 -> A + (C1 - C2)
  EClassId A = in();
  check(sub(add(A, cst(10)), cst(3)), [&] { return add(A, cst(7)); }, 1);
}

TEST_F(GIEGraphCoverageTest, C2MinusAPlusC1) {
  // C2 - (A + C1) -> (C2 - C1) - A
  EClassId A = in();
  check(sub(cst(10), add(A, cst(3))), [&] { return sub(cst(7), A); }, 1);
}

TEST_F(GIEGraphCoverageTest, AMinusC1MinusC2) {
  // (A - C1) - C2 -> A - (C1 + C2)
  EClassId A = in();
  check(sub(sub(A, cst(10)), cst(3)), [&] { return sub(A, cst(13)); }, 1);
}

TEST_F(GIEGraphCoverageTest, C1MinusAMinusC2) {
  // (C1 - A) - C2 -> (C1 - C2) - A
  EClassId A = in();
  check(sub(sub(cst(10), A), cst(3)), [&] { return sub(cst(7), A); }, 1);
}

TEST_F(GIEGraphCoverageTest, AMinusC1PlusC2) {
  // (A - C1) + C2 -> A + (C2 - C1)
  EClassId A = in();
  check(add(sub(A, cst(10)), cst(3)), [&] { return add(A, cst(-7)); }, 1);
}

TEST_F(GIEGraphCoverageTest, SubAddReg) {
  // sub_add_reg: (x + y) - y -> x, (x + y) - x -> y, x - (y + x) -> 0 - y
  EClassId X = in(), Y = in();
  check(sub(add(X, Y), Y), [&] { return X; }, 0);
}

TEST_F(GIEGraphCoverageTest, SubAddRegNeg) {
  EClassId X = in(), Y = in();
  check(sub(X, add(Y, X)), [&] { return sub(cst(0), Y); }, 1);
}

TEST_F(GIEGraphCoverageTest, MulByNegOne) {
  // mul_by_neg_one: x * -1 -> 0 - x (same cost model value as sub)
  EClassId X = in();
  check(mul(X, cst(-1)), [&] { return sub(cst(0), X); }, 1);
}

} // namespace
