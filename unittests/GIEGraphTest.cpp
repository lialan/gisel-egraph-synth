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
#include "llvm/IR/InstrTypes.h"
#include "llvm/Support/raw_ostream.h"
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
    return G.addConstant(Ty, APInt(Ty.getSizeInBits(), V, /*isSigned=*/true,
                                   /*implicitTrunc=*/true));
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

  /// (x0 - y0) + (x1 - y1) + ... with K terms. The negation rules keep
  /// producing new terms for this shape, so it exercises the budgets.
  EClassId sumOfDifferences(int K) {
    EClassId Acc = sub(in(), in());
    for (int I = 1; I < K; ++I)
      Acc = add(Acc, sub(in(), in()));
    return Acc;
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
  // Commutative operands are canonicalized (sorted), so this is the same node.
  EXPECT_EQ(add(B, A), X);
  EXPECT_NE(sub(B, A), sub(A, B));
  EXPECT_EQ(cst(7), cst(7));
  EXPECT_EQ(G.getNumNodes(), 6u);
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
  // Commutativity is canonicalization, not a rule: both orders hash-cons to
  // the same e-node without any saturation.
  EClassId A = in(), B = in();
  EClassId X = add(A, B), Y = add(B, A);
  EXPECT_EQ(X, Y);
  EXPECT_EQ(G.getNumNodes(), 3u);
  // Non-commutative operators keep their operand order.
  EXPECT_NE(sub(A, B), sub(B, A));
}

TEST_F(GIEGraphTest, CommutedPatternMatch) {
  // The constant gets the smaller class id, so the canonical node is
  // add(0, a); the pattern (G_ADD ?a 0) must still match it.
  EClassId Zero = cst(0);
  EClassId A = in();
  EClassId X = add(A, Zero);
  EXPECT_EQ(G.getClass(X).Nodes[0].Ops[0], Zero);
  run(rules({"add-zero"}));
  EXPECT_TRUE(G.equivalent(X, A));
}

TEST_F(GIEGraphTest, CommutativeCanonicalFormAfterMerge) {
  // add(a, b) and add(b, c) become congruent once a == c, although their
  // operands are in different orders; rebuild() re-sorts them.
  EClassId A = in(), B = in(), C = in();
  EClassId X = add(A, B), Y = add(B, C);
  EXPECT_FALSE(G.equivalent(X, Y));
  G.merge(A, C);
  G.rebuild();
  EXPECT_TRUE(G.equivalent(X, Y));
}

TEST_F(GIEGraphTest, Associativity) {
  // Associativity of AC operators is canonicalization, not a rule: both
  // groupings flatten to the same canonical form without any rule.
  EClassId A = in(), B = in(), C = in();
  EClassId X = add(add(A, B), C), Y = add(A, add(B, C));
  EClassId Z = add(add(C, A), B);
  run({});
  EXPECT_TRUE(G.equivalent(X, Y));
  EXPECT_TRUE(G.equivalent(X, Z));
  // Different operators and different leaves stay apart.
  EClassId M = mul(mul(A, B), C);
  EClassId W = add(add(A, B), A);
  run({});
  EXPECT_FALSE(G.equivalent(X, M));
  EXPECT_FALSE(G.equivalent(X, W));
}

TEST_F(GIEGraphTest, ACMatchingWithExtension) {
  // (a + 10) + 3: fold-add matches the two constant leaves of the flattened
  // sum {a, 10, 3}; the leaf a is kept aside and re-added.
  EClassId A = in();
  EClassId X = add(add(A, cst(10)), cst(3));
  run(rules({"fold-add"}));
  EXPECT_TRUE(G.equivalent(X, lookup([&] { return add(A, cst(13)); })));
}

TEST_F(GIEGraphTest, ACVariableBindsSeveralLeaves) {
  // (a * b * d) + (a * c): in factor-mul-add, ?b matches the two leaves
  // {b, d} of the product, for which no class exists yet; it is built when
  // the rule fires.
  EClassId A = in(true), B = in(), C = in(), D = in();
  EClassId X = add(mul(mul(A, B), D), mul(A, C));
  run(rules({"factor-mul-add"}));
  EXPECT_TRUE(
      G.equivalent(X, lookup([&] { return mul(A, add(mul(B, D), C)); })));
}

TEST_F(GIEGraphTest, ACCancellationInsideASum) {
  // (a + b) + (0 - a) == b: add-neg-to-sub pairs a with -a, sub-self turns
  // a - a into 0 and add-zero drops it from 0 + b.
  EClassId A = in(true), B = in();
  EClassId X = add(add(A, B), sub(cst(0), A));
  run(rules({"add-neg-to-sub", "sub-self", "add-zero"}));
  EXPECT_TRUE(G.equivalent(X, B));
  // Without knowing that a is defined, this is only a refinement.
  EClassId U = in(), V = in();
  EClassId Y = add(add(U, V), sub(cst(0), U));
  run(rules({"add-neg-to-sub", "sub-self", "add-zero"}));
  EXPECT_FALSE(G.equivalent(Y, V));
  EXPECT_TRUE(G.refinesTo(Y, V));
}

TEST_F(GIEGraphTest, ACFlaggedNodesAreNotRegrouped) {
  // Reassociation does not preserve nsw, so flagged nodes are never
  // flattened into the canonical form (the flagged sum is not equal to any
  // regrouping, flagged or not).
  const uint32_t NSW = MachineInstr::NoSWrap;
  EClassId A = in(), B = in(), C = in();
  EClassId X =
      op(TargetOpcode::G_ADD, op(TargetOpcode::G_ADD, A, B, NSW), C, NSW);
  EClassId Y =
      op(TargetOpcode::G_ADD, A, op(TargetOpcode::G_ADD, B, C, NSW), NSW);
  EClassId Z = add(A, add(B, C));
  runAll();
  EXPECT_FALSE(G.equivalent(X, Y));
  EXPECT_FALSE(G.equivalent(X, Z));
  EXPECT_FALSE(G.equivalent(Y, Z));
}

TEST_F(GIEGraphTest, FlaggedNodesAreOnlyRefined) {
  // Flags are part of the node identity and flagged nodes are never merged
  // with unflagged ones: "add nsw a, b" may be poison where "add a, b" is not.
  EClassId A = in(), B = in();
  EClassId X = op(TargetOpcode::G_ADD, A, B, MachineInstr::NoSWrap);
  EClassId Y = op(TargetOpcode::G_ADD, B, A, MachineInstr::NoSWrap);
  EClassId Z = add(A, B);
  runAll();
  // Commuting does not change the flags' meaning (nsw is symmetric), so the
  // two flagged adds are the same canonical e-node.
  EXPECT_TRUE(G.equivalent(X, Y));
  EXPECT_FALSE(G.equivalent(X, Z));
  // Dropping a flag is only ever a refinement, never the other way around.
  // (No rule rewrites a + b to itself, so there is no X ~> Z edge here; the
  // flagged match below shows the refinement direction.)
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

TEST_F(GIEGraphTest, LongSumSaturatesImmediately) {
  // With associativity and commutativity as rules, a sum of 13 inputs used to
  // hit the node limit. As a canonical form it needs a single iteration: the
  // only new nodes are the canonical chain.
  EClassId Acc = in();
  for (int I = 0; I < 12; ++I)
    Acc = add(Acc, in());
  SaturationStats S = runAll();
  EXPECT_TRUE(S.Saturated);
  EXPECT_EQ(S.Iterations, 1u);
  EXPECT_LT(G.getNumNodes(), 40u);
}

TEST_F(GIEGraphTest, SaturationTerminatesWithNodeLimit) {
  sumOfDifferences(3);
  SaturationLimits L;
  L.MaxNodes = 200;
  L.MaxIterations = 50;
  SaturationStats S = runAll(L);
  EXPECT_TRUE(S.HitNodeLimit);
  EXPECT_FALSE(S.Saturated);
  // Each iteration may overshoot by at most the nodes of a single RHS (an
  // AC term is built with at most MaxACLeaves nodes).
  EXPECT_LT(G.getNumNodes(), 220u);
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
  // With a low per-rule match limit, the rules that keep matching get banned
  // instead of flooding the graph, and the graph stays much smaller.
  auto Build = [&] { sumOfDifferences(4); };
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

TEST_F(GIEGraphTest, OneBitLiterals) {
  // Pattern literals are truncated to the type width: for s1, the literal 1
  // of mul-one and the literal -1 of and-ones are both the value 1. This
  // used to assert in the APInt constructor.
  LLT S1 = LLT::scalar(1);
  EClassId A = in(S1), B = in(S1);
  EClassId One = cst(1, S1);
  EClassId M = mul(A, One);
  EClassId X = op(TargetOpcode::G_AND, B, One);
  EClassId Y = add(A, A);
  runAll();
  EXPECT_TRUE(G.equivalent(M, A));
  EXPECT_TRUE(G.equivalent(X, B));
  // a + a == a * 2 == 0 in s1 (2 truncates to 0); a may be undef, so this is
  // only a refinement.
  EXPECT_TRUE(G.refinesTo(Y, cst(0, S1)));
}

TEST_F(GIEGraphTest, SaturationTerminatesWithIterationLimit) {
  sumOfDifferences(4);
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

//===----------------------------------------------------------------------===//
// Operators that are not binary operations of one type
//===----------------------------------------------------------------------===//

class GIEGraphOpsTest : public GIEGraphTest {
protected:
  const LLT S1 = LLT::scalar(1);
  const LLT S8 = LLT::scalar(8);
  const LLT S16 = LLT::scalar(16);
  const LLT P0 = LLT::pointer(0, 64);

  EClassId un(unsigned Opc, LLT Ty, EClassId A) {
    return G.addOp(Opc, Ty, {A});
  }
  EClassId trunc(LLT Ty, EClassId A) {
    return un(TargetOpcode::G_TRUNC, Ty, A);
  }
  EClassId zext(LLT Ty, EClassId A) { return un(TargetOpcode::G_ZEXT, Ty, A); }
  EClassId sext(LLT Ty, EClassId A) { return un(TargetOpcode::G_SEXT, Ty, A); }
  EClassId bswap(EClassId A) {
    return un(TargetOpcode::G_BSWAP, G.getType(A), A);
  }
  EClassId bitreverse(EClassId A) {
    return un(TargetOpcode::G_BITREVERSE, G.getType(A), A);
  }
  EClassId icmp(CmpInst::Predicate Pred, EClassId A, EClassId B) {
    return G.addOp(TargetOpcode::G_ICMP, S1, {A, B}, /*Flags=*/0, Pred);
  }
  EClassId select(EClassId C, EClassId A, EClassId B) {
    return G.addOp(TargetOpcode::G_SELECT, G.getType(A), {C, A, B});
  }
  EClassId boolean(bool V) { return cst(V ? -1 : 0, S1); }
  EClassId notOf(EClassId A) {
    return op(TargetOpcode::G_XOR, A, cst(-1, G.getType(A)));
  }
  EClassId udiv(EClassId A, EClassId B) {
    return op(TargetOpcode::G_UDIV, A, B);
  }
  EClassId ptrAdd(EClassId P, EClassId Offset) {
    return G.addOp(TargetOpcode::G_PTR_ADD, G.getType(P), {P, Offset});
  }
  EClassId phi(unsigned Site, ArrayRef<EClassId> Incoming) {
    return G.addOp(TargetOpcode::G_PHI, G.getType(Incoming[0]), Incoming,
                   /*Flags=*/0, Site);
  }
  /// A conditional branch. See OpShape::Effect for the attribute.
  EClassId brCond(EClassId C, unsigned Site, bool Invertible,
                  bool Inverted = false) {
    return G.addOp(TargetOpcode::G_BRCOND, LLT(), {C}, /*Flags=*/0,
                   (Site << 2) | (Invertible ? 2 : 0) | (Inverted ? 1 : 0));
  }
};

TEST_F(GIEGraphOpsTest, CastsCompose) {
  EClassId A = in(S8), B = in(S64);
  EClassId ZZ = zext(S32, zext(S16, A));
  EClassId SZ = sext(S32, zext(S16, A));
  EClassId SS = sext(S32, sext(S16, A));
  EClassId TT = trunc(S8, trunc(S32, B));
  EClassId Z = zext(S32, A), S = sext(S32, A), T = trunc(S8, B);
  runAll();
  EXPECT_TRUE(G.equivalent(ZZ, Z));
  EXPECT_TRUE(G.equivalent(SZ, Z));
  EXPECT_TRUE(G.equivalent(SS, S));
  EXPECT_TRUE(G.equivalent(TT, T));
  EXPECT_FALSE(G.equivalent(Z, S));
}

TEST_F(GIEGraphOpsTest, TruncationOfExtensionDependsOnWidths) {
  // The three rules have the same left-hand side; only the well-typed
  // right-hand side applies.
  EClassId A = in(S16);
  EClassId Same = trunc(S16, zext(S64, A));
  EClassId Narrow = trunc(S8, sext(S64, A));
  EClassId Wide = trunc(S32, sext(S64, A));
  EClassId TruncA = trunc(S8, A), SExtA = sext(S32, A);
  runAll();
  EXPECT_TRUE(G.equivalent(Same, A));
  EXPECT_TRUE(G.equivalent(Narrow, TruncA));
  EXPECT_TRUE(G.equivalent(Wide, SExtA));
  EXPECT_EQ(G.getType(Wide), S32);
}

TEST_F(GIEGraphOpsTest, ZExtOfTruncIsAMask) {
  EClassId A = in();
  EClassId X = zext(S32, trunc(S8, A));
  EClassId Y = op(TargetOpcode::G_AND, A, cst(255));
  // Not applicable if the source and result types differ.
  EClassId B = in(S64);
  EClassId Z = zext(S32, trunc(S8, B));
  runAll();
  EXPECT_TRUE(G.equivalent(X, Y));
  Extractor E(G, DefaultCostModel());
  EXPECT_EQ(E.getChosenNode(Z)->Opcode, unsigned(TargetOpcode::G_ZEXT));
}

TEST_F(GIEGraphOpsTest, InvolutionsAndBitCounts) {
  EClassId A = in();
  EClassId BB = bswap(bswap(A)), RR = bitreverse(bitreverse(A));
  EClassId PopSwapped = un(TargetOpcode::G_CTPOP, S32, bswap(A));
  EClassId PopWide = un(TargetOpcode::G_CTPOP, S32, zext(S64, A));
  EClassId Pop = un(TargetOpcode::G_CTPOP, S32, A);
  EClassId LzReversed = un(TargetOpcode::G_CTLZ, S32, bitreverse(A));
  EClassId Tz = un(TargetOpcode::G_CTTZ, S32, A);
  EClassId Lz = un(TargetOpcode::G_CTLZ, S32, A);
  runAll();
  EXPECT_TRUE(G.equivalent(BB, A));
  EXPECT_TRUE(G.equivalent(RR, A));
  EXPECT_TRUE(G.equivalent(PopSwapped, Pop));
  EXPECT_TRUE(G.equivalent(PopWide, Pop));
  EXPECT_TRUE(G.equivalent(LzReversed, Tz));
  EXPECT_FALSE(G.equivalent(Lz, Tz));
}

TEST_F(GIEGraphOpsTest, UnaryConstantFolding) {
  EClassId Swapped = bswap(cst(0x11223344));
  EClassId Pop = un(TargetOpcode::G_CTPOP, S8, cst(0xf0f0));
  EClassId Lz = un(TargetOpcode::G_CTLZ, S32, cst(0));
  EClassId Ext = sext(S64, cst(-2));
  runAll();
  EXPECT_EQ(G.getConstant(Swapped)->getZExtValue(), 0x44332211u);
  EXPECT_EQ(G.getConstant(Pop)->getZExtValue(), 8u);
  EXPECT_EQ(G.getConstant(Lz)->getZExtValue(), 32u);
  EXPECT_EQ(G.getConstant(Ext)->getSExtValue(), -2);
  EXPECT_EQ(G.getType(Ext), S64);
}

TEST_F(GIEGraphOpsTest, HomomorphismsAreHoisted) {
  EClassId A = in(S8), B = in(S8), X = in(S64), Y = in(S64), C = in(), D = in();
  auto And = [&](EClassId L, EClassId R) {
    return op(TargetOpcode::G_AND, L, R);
  };
  EClassId AndOfZExt = And(zext(S32, A), zext(S32, B));
  EClassId ZExtOfAnd = zext(S32, And(A, B));
  EClassId XorOfTrunc = op(TargetOpcode::G_XOR, trunc(S32, X), trunc(S32, Y));
  EClassId TruncOfXor = trunc(S32, op(TargetOpcode::G_XOR, X, Y));
  // Arithmetic is not made wider.
  EClassId AddOfTrunc = add(trunc(S32, X), trunc(S32, Y));
  EClassId TruncOfAdd = trunc(S32, add(X, Y));
  // The constant is sign-extended: a NOT stays a NOT.
  EClassId NotOfTrunc = op(TargetOpcode::G_XOR, trunc(S32, X), cst(-1));
  EClassId TruncOfNot = trunc(S32, op(TargetOpcode::G_XOR, X, cst(-1, S64)));
  EClassId AndOfSwap = And(bswap(C), bswap(D));
  EClassId SwapOfAnd = bswap(And(C, D));
  // With a constant that has a preimage: zext(a) & 0xff == zext(a & 0xff),
  // and a & 0xff == a for an s8.
  EClassId Masked = And(zext(S32, A), cst(0xff));
  // 0x100 is not the zero extension of an s8.
  EClassId NotHoisted = op(TargetOpcode::G_OR, zext(S32, A), cst(0x100));
  EClassId ZExtA = zext(S32, A);
  runAll();
  EXPECT_TRUE(G.equivalent(AndOfZExt, ZExtOfAnd));
  EXPECT_TRUE(G.equivalent(XorOfTrunc, TruncOfXor));
  EXPECT_FALSE(G.equivalent(AddOfTrunc, TruncOfAdd));
  EXPECT_TRUE(G.equivalent(NotOfTrunc, TruncOfNot));
  EXPECT_TRUE(G.equivalent(AndOfSwap, SwapOfAnd));
  EXPECT_TRUE(G.equivalent(Masked, ZExtA));
  Extractor E(G, DefaultCostModel());
  EXPECT_EQ(E.getChosenNode(NotHoisted)->Opcode, unsigned(TargetOpcode::G_OR));
}

TEST_F(GIEGraphOpsTest, CompareOperandsAreCanonical) {
  // a < b and b > a are the same e-node.
  EClassId A = in(), B = in();
  EXPECT_EQ(icmp(CmpInst::ICMP_ULT, A, B), icmp(CmpInst::ICMP_UGT, B, A));
  EXPECT_EQ(icmp(CmpInst::ICMP_EQ, A, B), icmp(CmpInst::ICMP_EQ, B, A));
  EXPECT_NE(icmp(CmpInst::ICMP_ULT, A, B), icmp(CmpInst::ICMP_ULT, B, A));
  EXPECT_NE(icmp(CmpInst::ICMP_ULT, A, B), icmp(CmpInst::ICMP_SLT, A, B));
}

TEST_F(GIEGraphOpsTest, CompareWithItself) {
  EClassId A = in(), F = in(/*Defined=*/true);
  EClassId X = icmp(CmpInst::ICMP_ULE, A, A);
  EClassId Y = icmp(CmpInst::ICMP_SLT, F, F);
  runAll();
  // A possibly undef or poison value: only a refinement.
  EXPECT_FALSE(G.equivalent(X, boolean(true)));
  EXPECT_TRUE(G.refinesTo(X, boolean(true)));
  EXPECT_TRUE(G.equivalent(Y, boolean(false)));
}

TEST_F(GIEGraphOpsTest, NegatedCompareIsTheInversePredicate) {
  EClassId A = in(), B = in();
  EClassId X = notOf(icmp(CmpInst::ICMP_ULT, A, B));
  EClassId Y = icmp(CmpInst::ICMP_UGE, A, B);
  // Through the canonical operand order: !(b > a) is b <= a, i.e. a >= b.
  EClassId Z = notOf(icmp(CmpInst::ICMP_SGT, B, A));
  EClassId W = icmp(CmpInst::ICMP_SGE, A, B);
  runAll();
  EXPECT_TRUE(G.equivalent(X, Y));
  EXPECT_TRUE(G.equivalent(Z, W));
  EXPECT_FALSE(G.equivalent(X, W));
}

TEST_F(GIEGraphOpsTest, CompareWithConstants) {
  EClassId F = in(/*Defined=*/true);
  EClassId NeverBelowZero = icmp(CmpInst::ICMP_ULT, F, cst(0));
  EClassId AlwaysAtMostMax = icmp(CmpInst::ICMP_SLE, F, cst(0x7fffffff));
  EClassId Unknown = icmp(CmpInst::ICMP_ULT, F, cst(1));
  EClassId Folded = icmp(CmpInst::ICMP_SLT, cst(-1), cst(0));
  EClassId FoldedUnsigned = icmp(CmpInst::ICMP_ULT, cst(-1), cst(0));
  EClassId A = in(), B = in();
  EClassId DiffIsZero = icmp(CmpInst::ICMP_EQ, sub(A, B), cst(0));
  EClassId Equal = icmp(CmpInst::ICMP_EQ, A, B);
  runAll();
  EXPECT_TRUE(G.equivalent(NeverBelowZero, boolean(false)));
  EXPECT_TRUE(G.equivalent(AlwaysAtMostMax, boolean(true)));
  EXPECT_FALSE(G.getConstant(Unknown).has_value());
  EXPECT_TRUE(G.equivalent(Folded, boolean(true)));
  EXPECT_TRUE(G.equivalent(FoldedUnsigned, boolean(false)));
  EXPECT_TRUE(G.equivalent(DiffIsZero, Equal));
}

TEST_F(GIEGraphOpsTest, SelectWithConstantCondition) {
  // The arm that is not selected does not matter, even if it is poison.
  EClassId A = in(), B = in();
  EClassId T = select(boolean(true), A, B);
  EClassId F = select(boolean(false), A, B);
  runAll();
  EXPECT_TRUE(G.equivalent(T, A));
  EXPECT_TRUE(G.equivalent(F, B));
}

TEST_F(GIEGraphOpsTest, SelectOfEqualArms) {
  // select c, a, a is poison if c is; a is not.
  EClassId C = in(S1), A = in();
  EClassId X = select(C, A, A);
  EClassId DC = in(S1, /*Defined=*/true), DA = in(/*Defined=*/true);
  EClassId Y = select(DC, DA, DA);
  runAll();
  EXPECT_FALSE(G.equivalent(X, A));
  EXPECT_TRUE(G.refinesTo(X, A));
  EXPECT_FALSE(G.refinesTo(A, X));
  EXPECT_TRUE(G.equivalent(Y, DA));
}

TEST_F(GIEGraphOpsTest, SelectOfNegatedCondition) {
  // Exact for arbitrary operands: both sides are poison in the same cases.
  EClassId C = in(S1), A = in(), B = in();
  EClassId X = select(notOf(C), A, B);
  EClassId Y = select(C, B, A);
  runAll();
  EXPECT_TRUE(G.equivalent(X, Y));
}

TEST_F(GIEGraphOpsTest, SelectOfBooleans) {
  EClassId C = in(S1);
  EClassId Bool = select(C, boolean(true), boolean(false));
  EClassId Not = select(C, boolean(false), boolean(true));
  EClassId ZExt = select(C, cst(1), cst(0));
  EClassId SExt = select(C, cst(-1), cst(0));
  EClassId NotC = notOf(C), ZExtC = zext(S32, C), SExtC = sext(S32, C);
  runAll();
  EXPECT_TRUE(G.equivalent(Bool, C));
  EXPECT_TRUE(G.equivalent(Not, NotC));
  EXPECT_TRUE(G.equivalent(ZExt, ZExtC));
  EXPECT_TRUE(G.equivalent(SExt, SExtC));
  EXPECT_FALSE(G.equivalent(ZExt, SExt));
}

TEST_F(GIEGraphOpsTest, ConstantsFoldThroughSelect) {
  EClassId C = in(S1);
  EClassId Arms = select(C, cst(1), cst(2));
  EClassId Sum = add(Arms, cst(10));
  EClassId Folded = select(C, cst(11), cst(12));
  // (select c, 1, 2) == 1 is select c, true, false, which is c.
  EClassId Cmp = icmp(CmpInst::ICMP_EQ, Arms, cst(1));
  runAll();
  EXPECT_TRUE(G.equivalent(Sum, Folded));
  EXPECT_TRUE(G.equivalent(Cmp, C));
}

TEST_F(GIEGraphOpsTest, SelectFactorsACommonOperand) {
  EClassId C = in(S1), A = in(/*Defined=*/true), X = in(), Y = in();
  EClassId Sel = select(C, add(A, X), add(Y, A));
  EClassId Factored = add(A, select(C, X, Y));
  // With a possibly undef common operand, fewer uses are only a refinement.
  EClassId U = in();
  EClassId SelU = select(C, add(U, X), add(U, Y));
  EClassId FactoredU = add(U, select(C, X, Y));
  runAll();
  EXPECT_TRUE(G.equivalent(Sel, Factored));
  EXPECT_FALSE(G.equivalent(SelU, FactoredU));
  EXPECT_TRUE(G.refinesTo(SelU, FactoredU));
}

TEST_F(GIEGraphOpsTest, DivisionByAConstant) {
  // A division by a non-zero constant cannot trap, so these are exact.
  EClassId A = in(/*Defined=*/true);
  EClassId ByOne = udiv(A, cst(1));
  EClassId ByEight = udiv(A, cst(8));
  EClassId RemEight = op(TargetOpcode::G_UREM, A, cst(8));
  EClassId RemOne = op(TargetOpcode::G_UREM, A, cst(1));
  EClassId Shifted = op(TargetOpcode::G_LSHR, A, cst(3));
  EClassId Masked = op(TargetOpcode::G_AND, A, cst(7));
  EClassId Folded = udiv(cst(7), cst(2));
  EClassId ByZero = udiv(cst(7), cst(0));
  EClassId Overflow = op(TargetOpcode::G_SDIV, cst(INT32_MIN), cst(-1));
  runAll();
  EXPECT_TRUE(G.equivalent(ByOne, A));
  EXPECT_TRUE(G.equivalent(ByEight, Shifted));
  EXPECT_TRUE(G.equivalent(RemEight, Masked));
  EXPECT_TRUE(G.equivalent(RemOne, cst(0)));
  EXPECT_EQ(G.getConstant(Folded)->getZExtValue(), 3u);
  // Undefined behaviour is never folded away to a value.
  EXPECT_FALSE(G.getConstant(ByZero).has_value());
  EXPECT_FALSE(G.getConstant(Overflow).has_value());
}

TEST_F(GIEGraphOpsTest, DivisionThatMayTrapIsOnlyRefined) {
  // a / a traps for a == 0 even if a is not poison, so 1 only refines it.
  EClassId A = in(/*Defined=*/true), B = in(/*Defined=*/true);
  EClassId Self = udiv(A, A);
  EClassId ZeroDividend = udiv(cst(0), B);
  // Dropping the division drops its undefined behaviour.
  EClassId Dropped = op(TargetOpcode::G_AND, udiv(A, B), cst(0));
  runAll();
  EXPECT_FALSE(G.equivalent(Self, cst(1)));
  EXPECT_TRUE(G.refinesTo(Self, cst(1)));
  EXPECT_FALSE(G.equivalent(ZeroDividend, cst(0)));
  EXPECT_TRUE(G.refinesTo(ZeroDividend, cst(0)));
  EXPECT_FALSE(G.equivalent(Dropped, cst(0)));
  EXPECT_TRUE(G.refinesTo(Dropped, cst(0)));
}

TEST_F(GIEGraphOpsTest, RemainderFromDivision) {
  // a - (a / b) * b is a % b. The remainder traps exactly when the matched
  // division does, so it may be created.
  EClassId A = in(), B = in();
  EClassId X = sub(A, mul(udiv(A, B), B));
  runAll();
  EClassId Rem = lookup([&] { return op(TargetOpcode::G_UREM, A, B); });
  EXPECT_TRUE(G.refinesTo(X, Rem));
  Extractor E(G, DefaultCostModel());
  EXPECT_EQ(E.getChosenNode(X)->Opcode, unsigned(TargetOpcode::G_UREM));
}

TEST_F(GIEGraphOpsTest, DivisionIsNotCreatedWithoutAGuard) {
  // Not an identity; it only shows that a rule cannot introduce a division
  // that may trap where the matched pattern has none.
  RewriteRule Bad("bad", "(G_SUB ?a ?b)", "(G_UDIV ?a ?b)");
  EClassId A = in(/*Defined=*/true), B = in(/*Defined=*/true);
  sub(A, B);
  sub(A, cst(4));
  G.rebuild();
  SmallVector<RuleMatch, 4> Matches;
  matchRule(G, Bad, Matches);
  ASSERT_EQ(Matches.size(), 2u);
  unsigned Rejected = 0, Merged = 0;
  for (const RuleMatch &M : Matches) {
    ApplyResult Res = applyMatch(G, Bad, M);
    Rejected += Res == ApplyResult::Rejected;
    Merged += Res == ApplyResult::Merged;
  }
  // Only the division by the constant 4 is created.
  EXPECT_EQ(Rejected, 1u);
  EXPECT_EQ(Merged, 1u);
}

TEST_F(GIEGraphOpsTest, PointerArithmetic) {
  EClassId P = in(P0), A = in(S64), B = in(S64);
  EClassId X = ptrAdd(ptrAdd(P, A), B);
  EClassId Y = ptrAdd(P, add(A, B));
  EClassId Z = ptrAdd(P, cst(0, S64));
  // inbounds may add poison: only a refinement.
  EClassId Flagged = G.addOp(TargetOpcode::G_PTR_ADD, P0, {P, cst(0, S64)},
                             MachineInstr::InBounds);
  runAll();
  EXPECT_TRUE(G.equivalent(X, Y));
  EXPECT_TRUE(G.equivalent(Z, P));
  EXPECT_EQ(G.getType(X), P0);
  EXPECT_FALSE(G.equivalent(Flagged, P));
  EXPECT_TRUE(G.refinesTo(Flagged, P));
}

TEST_F(GIEGraphOpsTest, PhiOfOneValue) {
  EClassId X = in(), Y = in();
  EClassId Same = phi(0, {X, X});
  EClassId Different = phi(1, {X, Y});
  EClassId Constant = phi(2, {cst(5), cst(5)});
  // PHIs of different blocks are different nodes, PHIs of one block with
  // the same incoming values are the same node.
  EXPECT_NE(phi(3, {X, Y}), Different);
  EXPECT_EQ(phi(1, {X, Y}), Different);
  // Equal incoming values may only be found during saturation.
  EClassId Later = phi(4, {X, add(X, cst(0))});
  SaturationStats S = runAll();
  EXPECT_TRUE(G.equivalent(Same, X));
  EXPECT_TRUE(G.equivalent(Later, X));
  EXPECT_FALSE(G.equivalent(Different, X));
  EXPECT_EQ(G.getConstant(Constant)->getZExtValue(), 5u);
  EXPECT_EQ(S.PhiMerges, 3u);
}

TEST_F(GIEGraphOpsTest, BranchOnNegatedCondition) {
  EClassId C = in(S1);
  EClassId Br = brCond(notOf(C), /*Site=*/0, /*Invertible=*/true);
  // Without an unconditional branch after it the targets cannot be
  // exchanged.
  EClassId Fixed = brCond(notOf(C), /*Site=*/1, /*Invertible=*/false);
  runAll();
  EClassId Inverted = lookup([&] {
    return brCond(C, /*Site=*/0, /*Invertible=*/true, /*Inverted=*/true);
  });
  EXPECT_TRUE(G.equivalent(Br, Inverted));
  EXPECT_FALSE(G.equivalent(Br, Fixed));
  Extractor E(G, DefaultCostModel());
  EXPECT_EQ(E.getChosenNode(Br)->Attr & 1, 1u);
  EXPECT_EQ(E.getTreeCost(Br), 1u);
  EXPECT_EQ(E.getChosenNode(Fixed)->Attr & 1, 0u);
  EXPECT_EQ(E.getTreeCost(Fixed), 2u);
}

TEST_F(GIEGraphOpsTest, PatternsAreChecked) {
  // Arity and attributes come from the operator properties.
  EXPECT_DEATH(RewriteRule("r", "(G_ZEXT ?a ?b)", "?a"), "takes 1 operands");
  EXPECT_DEATH(RewriteRule("r", "(G_SELECT ?c ?a)", "?a"), "takes 3 operands");
  EXPECT_DEATH(RewriteRule("r", "(G_ICMP:foo ?a ?b)", "?a"),
               "unknown predicate");
  EXPECT_DEATH(RewriteRule("r", "(G_AND ?a ?b)", "(G_ICMP ?a ?b)"),
               "without an attribute");
  EXPECT_DEATH(RewriteRule("r", "(G_PHI ?a ?b)", "?a"),
               "cannot be used in a pattern");
}

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

//===----------------------------------------------------------------------===//
// The remaining integer operators: minimum and maximum, saturating
// arithmetic, rotations, bit fields, parts of a value, and operators with an
// overflow result.
//===----------------------------------------------------------------------===//

namespace T = TargetOpcode;

class GIEGraphIntegerOpsTest : public GIEGraphOpsTest {
protected:
  EClassId typed(unsigned Opc, LLT Ty, ArrayRef<EClassId> Ops,
                 uint64_t Attr = 0, uint32_t Flags = 0) {
    return G.addOp(Opc, Ty, Ops, Flags, Attr);
  }
  /// The value that constant folding gives op(Ops), sign-extended, or
  /// std::nullopt if the class has no constant.
  std::optional<int64_t> folded(unsigned Opc, LLT Ty, ArrayRef<EClassId> Ops,
                                uint64_t Attr = 0) {
    EClassId C = typed(Opc, Ty, Ops, Attr);
    runAll();
    std::optional<APInt> V = G.getConstant(C);
    if (!V)
      return std::nullopt;
    return V->getSExtValue();
  }
  std::optional<int64_t> folded8(unsigned Opc, int64_t A, int64_t B) {
    return folded(Opc, S8, {cst(A, S8), cst(B, S8)});
  }
};

TEST_F(GIEGraphIntegerOpsTest, EveryGenericIntegerOpcodeHasProperties) {
  // The operators that the table must describe. Hints (G_ASSERT_*), the
  // constant folding barrier and indirect branches are deliberately values
  // or instructions outside of the graph.
  for (unsigned Opc : {T::G_ADD,
                       T::G_SUB,
                       T::G_MUL,
                       T::G_UDIV,
                       T::G_SDIV,
                       T::G_UREM,
                       T::G_SREM,
                       T::G_UDIVREM,
                       T::G_SDIVREM,
                       T::G_AND,
                       T::G_OR,
                       T::G_XOR,
                       T::G_SHL,
                       T::G_LSHR,
                       T::G_ASHR,
                       T::G_ROTL,
                       T::G_ROTR,
                       T::G_FSHL,
                       T::G_FSHR,
                       T::G_SMIN,
                       T::G_SMAX,
                       T::G_UMIN,
                       T::G_UMAX,
                       T::G_ABS,
                       T::G_ABDS,
                       T::G_ABDU,
                       T::G_UAVGFLOOR,
                       T::G_UAVGCEIL,
                       T::G_SAVGFLOOR,
                       T::G_SAVGCEIL,
                       T::G_UMULH,
                       T::G_SMULH,
                       T::G_UADDSAT,
                       T::G_SADDSAT,
                       T::G_USUBSAT,
                       T::G_SSUBSAT,
                       T::G_USHLSAT,
                       T::G_SSHLSAT,
                       T::G_SMULFIX,
                       T::G_UMULFIX,
                       T::G_SMULFIXSAT,
                       T::G_UMULFIXSAT,
                       T::G_SDIVFIX,
                       T::G_UDIVFIX,
                       T::G_SDIVFIXSAT,
                       T::G_UDIVFIXSAT,
                       T::G_CLMUL,
                       T::G_CLMULR,
                       T::G_CLMULH,
                       T::G_UADDO,
                       T::G_SADDO,
                       T::G_USUBO,
                       T::G_SSUBO,
                       T::G_UMULO,
                       T::G_SMULO,
                       T::G_UADDE,
                       T::G_SADDE,
                       T::G_USUBE,
                       T::G_SSUBE,
                       T::G_ICMP,
                       T::G_SCMP,
                       T::G_UCMP,
                       T::G_SELECT,
                       T::G_TRUNC,
                       T::G_ZEXT,
                       T::G_SEXT,
                       T::G_ANYEXT,
                       T::G_SEXT_INREG,
                       T::G_TRUNC_SSAT_S,
                       T::G_TRUNC_SSAT_U,
                       T::G_TRUNC_USAT_U,
                       T::G_PTRTOINT,
                       T::G_INTTOPTR,
                       T::G_PTR_ADD,
                       T::G_PTRMASK,
                       T::G_BSWAP,
                       T::G_BITREVERSE,
                       T::G_CTPOP,
                       T::G_CTLZ,
                       T::G_CTTZ,
                       T::G_CTLS,
                       T::G_EXTRACT,
                       T::G_INSERT,
                       T::G_SBFX,
                       T::G_UBFX,
                       T::G_MERGE_VALUES,
                       T::G_UNMERGE_VALUES,
                       T::G_FREEZE,
                       T::G_PHI,
                       T::G_BRCOND,
                       T::G_BR})
    EXPECT_NE(getOpProperties(Opc), nullptr) << "opcode " << Opc;
  uint32_t Flags = 0;
  EXPECT_EQ(getOpPropertiesForInstr(T::G_CTLZ_ZERO_POISON, Flags),
            getOpProperties(T::G_CTLZ));
  EXPECT_EQ(Flags, PoisonVariantFlag);
  EXPECT_EQ(getOpPropertiesForInstr(T::G_CTTZ_ZERO_POISON, Flags),
            getOpProperties(T::G_CTTZ));
}

TEST_F(GIEGraphIntegerOpsTest, FoldMinMaxAndDifferences) {
  EXPECT_EQ(folded8(T::G_SMIN, -3, 5), -3);
  EXPECT_EQ(folded8(T::G_SMAX, -3, 5), 5);
  EXPECT_EQ(folded8(T::G_UMIN, -3, 5), 5);
  EXPECT_EQ(folded8(T::G_UMAX, -3, 5), -3);
  EXPECT_EQ(folded8(T::G_ABDS, -3, 5), 8);
  EXPECT_EQ(folded8(T::G_ABDU, -3, 5), -8); // 253 - 5 == 248
  EXPECT_EQ(folded(T::G_ABS, S8, {cst(-5, S8)}), 5);
  EXPECT_EQ(folded(T::G_ABS, S8, {cst(-128, S8)}), -128);
  EXPECT_EQ(folded(T::G_SCMP, S8, {cst(-3, S8), cst(5, S8)}), -1);
  EXPECT_EQ(folded(T::G_UCMP, S8, {cst(-3, S8), cst(5, S8)}), 1);
  EXPECT_EQ(folded(T::G_SCMP, S8, {cst(5, S8), cst(5, S8)}), 0);
}

TEST_F(GIEGraphIntegerOpsTest, FoldAveragesAndHighProducts) {
  EXPECT_EQ(folded8(T::G_UAVGFLOOR, 255, 1), -128); // 128
  EXPECT_EQ(folded8(T::G_UAVGCEIL, 254, 1), -128);  // 128
  EXPECT_EQ(folded8(T::G_SAVGFLOOR, -3, 2), -1);
  EXPECT_EQ(folded8(T::G_SAVGCEIL, -3, 2), 0);
  EXPECT_EQ(folded8(T::G_UMULH, 200, 3), 2);
  EXPECT_EQ(folded8(T::G_SMULH, -56, 3), -1);
  EXPECT_EQ(folded8(T::G_CLMUL, 7, 5), 27);
  EXPECT_EQ(folded8(T::G_CLMULH, 0x80, 0x80), 0x40);
  EXPECT_EQ(folded8(T::G_CLMULR, 0x80, 0x80), -128);
}

TEST_F(GIEGraphIntegerOpsTest, FoldSaturatingArithmetic) {
  EXPECT_EQ(folded8(T::G_UADDSAT, 200, 100), -1);
  EXPECT_EQ(folded8(T::G_SADDSAT, 100, 100), 127);
  EXPECT_EQ(folded8(T::G_USUBSAT, 5, 10), 0);
  EXPECT_EQ(folded8(T::G_SSUBSAT, -100, 100), -128);
  EXPECT_EQ(folded8(T::G_USHLSAT, 3, 2), 12);
  EXPECT_EQ(folded8(T::G_USHLSAT, 0x40, 2), -1);
  EXPECT_EQ(folded8(T::G_SSHLSAT, 0x40, 2), 127);
  EXPECT_EQ(folded8(T::G_SSHLSAT, -64, 2), -128);
  // An amount that is not smaller than the width gives poison.
  EXPECT_EQ(folded8(T::G_USHLSAT, 3, 8), std::nullopt);
  EXPECT_EQ(folded(T::G_TRUNC_SSAT_S, S8, {cst(300, S16)}), 127);
  EXPECT_EQ(folded(T::G_TRUNC_SSAT_S, S8, {cst(-300, S16)}), -128);
  EXPECT_EQ(folded(T::G_TRUNC_SSAT_U, S8, {cst(-5, S16)}), 0);
  EXPECT_EQ(folded(T::G_TRUNC_SSAT_U, S8, {cst(300, S16)}), -1);
  EXPECT_EQ(folded(T::G_TRUNC_USAT_U, S8, {cst(300, S16)}), -1);
  EXPECT_EQ(folded(T::G_TRUNC_USAT_U, S8, {cst(200, S16)}), -56);
}

TEST_F(GIEGraphIntegerOpsTest, FoldRotationsAndFunnelShifts) {
  EXPECT_EQ(folded8(T::G_ROTL, 0x81, 1), 0x03);
  EXPECT_EQ(folded8(T::G_ROTL, 0x81, 9), 0x03);
  EXPECT_EQ(folded8(T::G_ROTR, 0x81, 1), -64);
  EXPECT_EQ(folded(T::G_FSHL, S8, {cst(0x01, S8), cst(0x80, S8), cst(1, S8)}),
            0x03);
  EXPECT_EQ(folded(T::G_FSHR, S8, {cst(0x01, S8), cst(0x80, S8), cst(1, S8)}),
            -64);
}

TEST_F(GIEGraphIntegerOpsTest, FoldBitFieldsAndParts) {
  EXPECT_EQ(folded(T::G_CTLS, S32, {cst(0, S8)}), 7);
  EXPECT_EQ(folded(T::G_CTLS, S32, {cst(1, S8)}), 6);
  EXPECT_EQ(folded(T::G_CTLS, S32, {cst(-1, S8)}), 7);
  EXPECT_EQ(folded(T::G_CTLS, S32, {cst(0x40, S8)}), 0);
  EXPECT_EQ(folded(T::G_SEXT_INREG, S8, {cst(0x0F, S8)}, 4), -1);
  EXPECT_EQ(folded(T::G_SEXT_INREG, S8, {cst(0x17, S8)}, 4), 7);
  EXPECT_EQ(folded(T::G_EXTRACT, S8, {cst(0x1234, S16)}, 4), 0x23);
  EXPECT_EQ(folded(T::G_INSERT, S16, {cst(0x1234, S16), cst(0xAB, S8)}, 4),
            0x1AB4);
  EXPECT_EQ(folded(T::G_UBFX, S8, {cst(0xB4, S8), cst(2, S8), cst(3, S8)}), 5);
  EXPECT_EQ(folded(T::G_SBFX, S8, {cst(0xB4, S8), cst(2, S8), cst(3, S8)}), -3);
  // A field that is not inside the value gives poison.
  EXPECT_EQ(folded(T::G_UBFX, S8, {cst(0xB4, S8), cst(6, S8), cst(3, S8)}),
            std::nullopt);
  EXPECT_EQ(folded(T::G_MERGE_VALUES, S16, {cst(0x34, S8), cst(0x12, S8)}),
            0x1234);
  EXPECT_EQ(folded(T::G_UNMERGE_VALUES, S8, {cst(0x1234, S16)}, 0), 0x34);
  EXPECT_EQ(folded(T::G_UNMERGE_VALUES, S8, {cst(0x1234, S16)}, 1), 0x12);
}

TEST_F(GIEGraphIntegerOpsTest, FoldOverflowResults) {
  // {operator, a, b, value, overflow}; a true s1 is -1.
  struct Case {
    unsigned Opc;
    int64_t A, B, Value, Overflow;
  };
  for (const Case &C :
       {Case{T::G_UADDO, 200, 100, 44, -1}, Case{T::G_UADDO, 100, 100, -56, 0},
        Case{T::G_SADDO, 100, 100, -56, -1}, Case{T::G_SADDO, -100, 100, 0, 0},
        Case{T::G_USUBO, 5, 10, -5, -1}, Case{T::G_USUBO, 10, 5, 5, 0},
        Case{T::G_SSUBO, -100, 100, 56, -1}, Case{T::G_SSUBO, 100, 50, 50, 0},
        Case{T::G_UMULO, 16, 16, 0, -1}, Case{T::G_UMULO, 15, 17, -1, 0},
        Case{T::G_SMULO, 16, 8, -128, -1}, Case{T::G_SMULO, -16, 8, -128, 0}}) {
    EClassId A = cst(C.A, S8), B = cst(C.B, S8);
    EXPECT_EQ(folded(C.Opc, S8, {A, B}, 0), C.Value) << C.Opc;
    EXPECT_EQ(folded(C.Opc, S1, {A, B}, 1), C.Overflow) << C.Opc;
  }
  EClassId One = boolean(true);
  EXPECT_EQ(folded(T::G_UADDE, S8, {cst(200, S8), cst(55, S8), One}, 0), 0);
  EXPECT_EQ(folded(T::G_UADDE, S1, {cst(200, S8), cst(55, S8), One}, 1), -1);
  EXPECT_EQ(folded(T::G_SADDE, S8, {cst(100, S8), cst(27, S8), One}, 0), -128);
  EXPECT_EQ(folded(T::G_SADDE, S1, {cst(100, S8), cst(27, S8), One}, 1), -1);
  EXPECT_EQ(folded(T::G_USUBE, S8, {cst(5, S8), cst(5, S8), One}, 0), -1);
  EXPECT_EQ(folded(T::G_USUBE, S1, {cst(5, S8), cst(5, S8), One}, 1), -1);
  EXPECT_EQ(folded(T::G_SSUBE, S8, {cst(-128, S8), cst(0, S8), One}, 0), 127);
  EXPECT_EQ(folded(T::G_SSUBE, S1, {cst(-128, S8), cst(0, S8), One}, 1), -1);
}

TEST_F(GIEGraphIntegerOpsTest, SelectOfComparisonIsMinOrMax) {
  EClassId A = in(S32, /*Defined=*/true), B = in(S32, /*Defined=*/true);
  EClassId Min = select(icmp(CmpInst::ICMP_SLT, A, B), A, B);
  EClassId Max = select(icmp(CmpInst::ICMP_SGE, A, B), A, B);
  EClassId UMin = select(icmp(CmpInst::ICMP_UGT, A, B), B, A);
  EClassId SMin = op(T::G_SMIN, A, B), SMax = op(T::G_SMAX, A, B);
  EClassId UMinOp = op(T::G_UMIN, A, B);
  // max - min is the absolute difference.
  EClassId Diff = sub(SMax, SMin), Abds = op(T::G_ABDS, A, B);
  runAll();
  EXPECT_TRUE(G.equivalent(Min, SMin));
  EXPECT_TRUE(G.equivalent(Max, SMax));
  EXPECT_TRUE(G.equivalent(UMin, UMinOp));
  EXPECT_FALSE(G.equivalent(SMin, UMinOp));
  EXPECT_TRUE(G.equivalent(Diff, Abds));
}

TEST_F(GIEGraphIntegerOpsTest, SelectOfUndefinedValuesIsOnlyRefined) {
  // The select uses each value twice. If a value is undef, the two uses can
  // differ, so the minimum is only a refinement.
  EClassId A = in(), B = in();
  EClassId Sel = select(icmp(CmpInst::ICMP_SLT, A, B), A, B);
  EClassId SMin = op(T::G_SMIN, A, B);
  runAll();
  EXPECT_FALSE(G.equivalent(Sel, SMin));
  EXPECT_TRUE(G.refinesTo(Sel, SMin));
  EXPECT_FALSE(G.refinesTo(SMin, Sel));
}

TEST_F(GIEGraphIntegerOpsTest, LatticeAbsorption) {
  EClassId A = in(S32, /*Defined=*/true), B = in(S32, /*Defined=*/true);
  EClassId L = op(T::G_UMIN, A, op(T::G_UMAX, A, B));
  EClassId Sat = op(T::G_UADDSAT, A, cst(0));
  EClassId Clmul = op(T::G_CLMUL, A, cst(1));
  EClassId Rot = op(T::G_ROTL, A, cst(0));
  runAll();
  EXPECT_TRUE(G.equivalent(L, A));
  EXPECT_TRUE(G.equivalent(Sat, A));
  EXPECT_TRUE(G.equivalent(Clmul, A));
  EXPECT_TRUE(G.equivalent(Rot, A));
}

TEST_F(GIEGraphIntegerOpsTest, AbsoluteValue) {
  EClassId A = in(S32, /*Defined=*/true);
  EClassId Neg = sub(cst(0), A);
  EClassId Sel = select(icmp(CmpInst::ICMP_SLT, A, cst(0)), Neg, A);
  EClassId Max = op(T::G_SMAX, A, Neg);
  EClassId Abs = un(T::G_ABS, S32, A), AbsAbs = un(T::G_ABS, S32, Abs);
  runAll();
  EXPECT_TRUE(G.equivalent(Sel, Abs));
  EXPECT_TRUE(G.equivalent(Max, Abs));
  EXPECT_TRUE(G.equivalent(AbsAbs, Abs));
}

TEST_F(GIEGraphIntegerOpsTest, OverflowResults) {
  EClassId A = in(S32, /*Defined=*/true), B = in(S32, /*Defined=*/true);
  EClassId Sum = typed(T::G_UADDO, S32, {A, B}, 0);
  EClassId Carry = typed(T::G_UADDO, S1, {A, B}, 1);
  EClassId NoCarry = typed(T::G_UADDO, S1, {A, cst(0)}, 1);
  EClassId Borrow = typed(T::G_USUBO, S1, {A, B}, 1);
  EClassId NoBorrow = typed(T::G_USUBO, S1, {A, A}, 1);
  EClassId MulOne = typed(T::G_UMULO, S1, {A, cst(1)}, 1);
  // A carry operand that is 0.
  EClassId SumE = typed(T::G_UADDE, S32, {A, B, boolean(false)}, 0);
  EClassId CarryE = typed(T::G_UADDE, S1, {A, B, boolean(false)}, 1);
  EClassId Add = add(A, B), Ult = icmp(CmpInst::ICMP_ULT, A, B);
  runAll();
  EXPECT_TRUE(G.equivalent(Sum, Add));
  EXPECT_TRUE(G.equivalent(SumE, Add));
  EXPECT_TRUE(G.equivalent(CarryE, Carry));
  EXPECT_FALSE(G.equivalent(Carry, Sum));
  EXPECT_EQ(G.getConstant(NoCarry), APInt(1, 0));
  EXPECT_EQ(G.getConstant(NoBorrow), APInt(1, 0));
  EXPECT_EQ(G.getConstant(MulOne), APInt(1, 0));
  EXPECT_TRUE(G.equivalent(Borrow, Ult));
  EXPECT_FALSE(G.getConstant(Carry).has_value());
}

TEST_F(GIEGraphIntegerOpsTest, QuotientAndRemainderOfOneDivision) {
  EClassId A = in(), B = in();
  EClassId Quot = typed(T::G_SDIVREM, S32, {A, B}, 0);
  EClassId Rem = typed(T::G_SDIVREM, S32, {A, B}, 1);
  EClassId Div = op(T::G_SDIV, A, B), SRem = op(T::G_SREM, A, B);
  runAll();
  EXPECT_TRUE(G.equivalent(Quot, Div) || G.refinesTo(Quot, Div));
  EXPECT_TRUE(G.equivalent(Rem, SRem) || G.refinesTo(Rem, SRem));
  EXPECT_FALSE(G.equivalent(Quot, Rem));
}

TEST_F(GIEGraphIntegerOpsTest, PartsOfAValue) {
  EClassId A = in(S8, /*Defined=*/true), B = in(S8, /*Defined=*/true);
  EClassId X = in(S16, /*Defined=*/true);
  EClassId Merge = typed(T::G_MERGE_VALUES, S16, {A, B});
  EClassId Low = typed(T::G_UNMERGE_VALUES, S8, {Merge}, 0);
  EClassId High = typed(T::G_UNMERGE_VALUES, S8, {Merge}, 1);
  EClassId XLow = typed(T::G_UNMERGE_VALUES, S8, {X}, 0);
  EClassId XHigh = typed(T::G_UNMERGE_VALUES, S8, {X}, 1);
  EClassId Again = typed(T::G_MERGE_VALUES, S16, {XLow, XHigh});
  EClassId Swapped = typed(T::G_MERGE_VALUES, S16, {XHigh, XLow});
  EClassId ZeroHigh = typed(T::G_MERGE_VALUES, S16, {A, cst(0, S8)});
  EClassId Trunc = trunc(S8, X), ZExt = zext(S16, A);
  runAll();
  EXPECT_TRUE(G.equivalent(Low, A));
  EXPECT_TRUE(G.equivalent(High, B));
  EXPECT_TRUE(G.equivalent(Again, X));
  EXPECT_FALSE(G.equivalent(Swapped, X));
  EXPECT_TRUE(G.equivalent(XLow, Trunc));
  EXPECT_FALSE(G.equivalent(XHigh, Trunc));
  EXPECT_TRUE(G.equivalent(ZeroHigh, ZExt));
}

TEST_F(GIEGraphIntegerOpsTest, MergeOfSomeResultsIsNotTheValue) {
  // Only two of the four parts: the concatenation is not the value.
  EClassId X = in(S32);
  EClassId P0 = typed(T::G_UNMERGE_VALUES, S8, {X}, 0);
  EClassId P1 = typed(T::G_UNMERGE_VALUES, S8, {X}, 1);
  EClassId Half = typed(T::G_MERGE_VALUES, S16, {P0, P1});
  SaturationStats S = runAll();
  EXPECT_TRUE(S.Saturated);
  EXPECT_EQ(G.getType(Half), S16);
  EXPECT_FALSE(G.equivalent(Half, X));
}

TEST_F(GIEGraphIntegerOpsTest, SignExtensionInPlace) {
  EClassId X = in();
  EClassId Ext = sext(S32, trunc(S8, X));
  EClassId InReg = typed(T::G_SEXT_INREG, S32, {X}, 8);
  EClassId Other = typed(T::G_SEXT_INREG, S32, {X}, 16);
  EClassId Shifts = op(T::G_ASHR, shl(X, cst(24)), cst(24));
  runAll();
  EXPECT_TRUE(G.equivalent(Ext, InReg));
  EXPECT_TRUE(G.equivalent(InReg, Shifts));
  EXPECT_FALSE(G.equivalent(InReg, Other));
}

TEST_F(GIEGraphIntegerOpsTest, BitFields) {
  EClassId X = in();
  EClassId Field = typed(T::G_UBFX, S32, {X, cst(4), cst(8)});
  EClassId Mask = op(T::G_AND, op(T::G_LSHR, X, cst(4)), cst(255));
  EClassId Signed = typed(T::G_SBFX, S32, {X, cst(4), cst(8)});
  EClassId Shifts = op(T::G_ASHR, shl(X, cst(20)), cst(24));
  EClassId Low = typed(T::G_EXTRACT, S16, {X}, 0);
  EClassId Mid = typed(T::G_EXTRACT, S8, {X}, 8);
  EClassId Trunc = trunc(S16, X);
  EClassId TruncShift = trunc(S8, op(T::G_LSHR, X, cst(8)));
  runAll();
  EXPECT_TRUE(G.equivalent(Field, Mask));
  EXPECT_TRUE(G.equivalent(Signed, Shifts));
  EXPECT_FALSE(G.equivalent(Field, Signed));
  EXPECT_TRUE(G.equivalent(Low, Trunc));
  EXPECT_TRUE(G.equivalent(Mid, TruncShift));
}

TEST_F(GIEGraphIntegerOpsTest, FunnelShifts) {
  EClassId A = in(S32, /*Defined=*/true), B = in(S32, /*Defined=*/true);
  EClassId C = in();
  EClassId Self = typed(T::G_FSHL, S32, {A, A, C});
  EClassId Rot = op(T::G_ROTL, A, C);
  EClassId LeftZero = typed(T::G_FSHL, S32, {A, B, cst(0)});
  EClassId RightZero = typed(T::G_FSHR, S32, {A, B, cst(0)});
  // A rotation by a constant distributes over the bitwise operators.
  EClassId K = cst(5);
  EClassId Sum = op(T::G_AND, op(T::G_ROTL, A, K), op(T::G_ROTL, B, K));
  EClassId Hoisted = op(T::G_ROTL, op(T::G_AND, A, B), K);
  runAll();
  EXPECT_TRUE(G.equivalent(Self, Rot));
  EXPECT_TRUE(G.equivalent(LeftZero, A));
  EXPECT_TRUE(G.equivalent(RightZero, B));
  EXPECT_TRUE(G.equivalent(Sum, Hoisted));
}

TEST_F(GIEGraphIntegerOpsTest, PointerConversions) {
  EClassId P = in(P0), X = in(S64);
  EClassId Same = un(T::G_INTTOPTR, P0, un(T::G_PTRTOINT, S64, P));
  // A 32-bit integer does not hold the pointer.
  EClassId Narrow = un(T::G_INTTOPTR, P0, un(T::G_PTRTOINT, S32, P));
  EClassId Back = un(T::G_PTRTOINT, S64, un(T::G_INTTOPTR, P0, X));
  EClassId Masked = G.addOp(T::G_PTRMASK, P0, {P, cst(-1, S64)});
  runAll();
  EXPECT_TRUE(G.equivalent(Same, P));
  EXPECT_FALSE(G.equivalent(Narrow, P));
  EXPECT_TRUE(G.equivalent(Back, X));
  EXPECT_TRUE(G.equivalent(Masked, P));
}

TEST_F(GIEGraphIntegerOpsTest, FreezeOfADefinedValue) {
  EClassId A = in(S32, /*Defined=*/true), U = in();
  EClassId FA = typed(T::G_FREEZE, S32, {A}, /*Site=*/0);
  EClassId FU1 = typed(T::G_FREEZE, S32, {U}, /*Site=*/1);
  EClassId FU2 = typed(T::G_FREEZE, S32, {U}, /*Site=*/2);
  // A frozen value is defined, so its square can be shared.
  EClassId Twice = add(FU1, FU1), Double = mul(FU1, cst(2));
  runAll();
  EXPECT_TRUE(G.equivalent(FA, A));
  EXPECT_FALSE(G.equivalent(FU1, U));
  // Two freezes of an undefined value can have different values.
  EXPECT_FALSE(G.equivalent(FU1, FU2));
  EXPECT_TRUE(G.getClass(FU1).NotUndef);
  EXPECT_TRUE(G.getClass(FU1).NotPoison);
  EXPECT_TRUE(G.equivalent(Twice, Double));
}

TEST_F(GIEGraphIntegerOpsTest, PoisonVariantIsOnlyRefined) {
  // G_CTLZ_ZERO_POISON is a G_CTLZ node that can be poison: a rule that
  // matches it gives a refinement, never an equality.
  EClassId A = in(S32, /*Defined=*/true);
  EClassId Rev = bitreverse(A);
  EClassId ZeroPoison =
      typed(T::G_CTLZ, S32, {Rev}, 0, /*Flags=*/PoisonVariantFlag);
  EClassId Plain = typed(T::G_CTLZ, S32, {Rev});
  EClassId Cttz = typed(T::G_CTTZ, S32, {A});
  runAll();
  EXPECT_TRUE(G.equivalent(Plain, Cttz));
  EXPECT_FALSE(G.equivalent(ZeroPoison, Cttz));
  EXPECT_TRUE(G.refinesTo(ZeroPoison, Cttz));
  EXPECT_FALSE(G.getClass(ZeroPoison).NotPoison);
  EXPECT_TRUE(G.getClass(Plain).NotPoison);
}

TEST_F(GIEGraphIntegerOpsTest, FixedPointOverflowIsPoison) {
  EClassId A = in(S32, /*Defined=*/true), B = in(S32, /*Defined=*/true);
  EClassId Mul = typed(T::G_SMULFIX, S32, {A, B}, /*Scale=*/4);
  EClassId Swapped = typed(T::G_SMULFIX, S32, {B, A}, 4);
  EClassId OtherScale = typed(T::G_SMULFIX, S32, {A, B}, 8);
  EClassId Sat = typed(T::G_SMULFIXSAT, S32, {A, B}, 4);
  runAll();
  // Commutative, and the scale is part of the operation.
  EXPECT_TRUE(G.equivalent(Mul, Swapped));
  EXPECT_FALSE(G.equivalent(Mul, OtherScale));
  EXPECT_FALSE(G.getClass(Mul).NotPoison);
  EXPECT_TRUE(G.getClass(Sat).NotPoison);
}

} // namespace
