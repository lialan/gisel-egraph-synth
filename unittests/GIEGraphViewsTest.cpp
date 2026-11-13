//===- GIEGraphViewsTest.cpp - Facts, typed constants and analysis views --===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Tests of the shared semantic layer (known bits of classes and their
// source, typed constants of scalars, splats and lanes, the definedness
// policy of view rewrites) and of the analysis views on top of it.
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GIEGraph.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Support/raw_ostream.h"
#include "gtest/gtest.h"

using namespace llvm;
using namespace llvm::egraph;
using namespace llvm::TargetOpcode;

namespace {

class GIEGraphViewsTest : public testing::Test {
protected:
  EGraph G;
  const LLT S1 = LLT::scalar(1);
  const LLT S16 = LLT::scalar(16);
  const LLT S32 = LLT::scalar(32);
  const LLT V2S32 = LLT::fixed_vector(2, 32);

  /// An input; Defined means neither undef nor poison.
  EClassId in(LLT Ty, bool Defined = false) {
    return G.addInput({Ty, Defined, Defined});
  }
  EClassId in(bool Defined = false) { return in(S32, Defined); }
  /// An input with context facts: the bits of \p Zero are known zero.
  EClassId inKnownZero(uint64_t Zero, bool Defined = false) {
    InputInfo I{S32, Defined, Defined};
    I.Known = KnownBits(32);
    I.Known.Zero = APInt(32, Zero);
    return G.addInput(I);
  }
  EClassId cst(int64_t V, LLT Ty) {
    unsigned W = Ty.getScalarSizeInBits();
    return G.addConstantSplat(Ty, APInt(W, V, /*isSigned=*/true,
                                        /*implicitTrunc=*/true));
  }
  EClassId cst(int64_t V) { return cst(V, S32); }
  EClassId op(unsigned Opc, EClassId A, EClassId B) {
    return G.addOp(Opc, G.getType(A), {A, B});
  }

  SaturationStats runAll(SaturationLimits Limits = SaturationLimits()) {
    std::vector<RewriteRule> All = getDefaultIntegerRules();
    return saturate(G, All, Limits);
  }
  EClassId lookup(function_ref<EClassId()> Build) {
    EClassId Id = Build();
    G.rebuild();
    return G.find(Id);
  }
  std::string extract(EClassId Root) {
    DefaultCostModel CM;
    Extractor E(G, CM);
    return E.getExprString(Root);
  }
  unsigned contextFacts(const SaturationStats &S) {
    unsigned N = 0;
    for (unsigned C : S.ContextFactApplications)
      N += C;
    return N;
  }
};

//===----------------------------------------------------------------------===//
// Known bits of classes
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphViewsTest, KnownBitsFollowTheStructure) {
  EClassId X = in();
  EClassId Shl = op(G_SHL, X, cst(4));
  EClassId Or = op(G_OR, Shl, cst(3));
  EClassId Sh = op(G_LSHR, X, cst(28));
  G.rebuild();
  const KnownBits &K = G.getKnownBits(Or);
  EXPECT_EQ(K.getBitWidth(), 32u);
  EXPECT_EQ(K.One.getZExtValue(), 3u);
  EXPECT_EQ(K.Zero.getZExtValue(), 0xcu);
  // The high 28 bits of x >> 28 are zero.
  EXPECT_EQ(G.getKnownBits(Sh).Zero.countl_one(), 28u);
  // No input facts are involved: the context adds nothing.
  EXPECT_EQ(G.getKnownBits(Or, FactSource::Structure).Zero,
            G.getKnownBits(Or, FactSource::Context).Zero);
}

TEST_F(GIEGraphViewsTest, ContextFactsAreSeparate) {
  EClassId A = inKnownZero(1); // even
  EClassId Sum = op(G_ADD, A, cst(1));
  G.rebuild();
  EXPECT_TRUE(G.getKnownBits(Sum, FactSource::Context).One[0]);
  EXPECT_FALSE(G.getKnownBits(Sum, FactSource::Structure).One[0]);
  EXPECT_FALSE(G.getKnownBits(Sum, FactSource::Structure).Zero[0]);
}

TEST_F(GIEGraphViewsTest, FreezeOfMaybePoisonHasNoFacts) {
  // freeze(poison) is an arbitrary value, not one with the facts of x << 1.
  EClassId X = in();
  EClassId F = G.addOp(G_FREEZE, S32, {op(G_SHL, X, cst(1))}, 0, 0);
  EClassId D = in(true);
  EClassId FD = G.addOp(G_FREEZE, S32, {op(G_SHL, D, cst(1))}, 0, 1);
  G.rebuild();
  EXPECT_FALSE(G.getKnownBits(F).Zero[0]);
  EXPECT_TRUE(G.getKnownBits(FD).Zero[0]);
}

TEST_F(GIEGraphViewsTest, VectorFactsArePerLane) {
  // <2 x s32>: the facts of each lane, never of the 64-bit integer.
  EClassId X = in(V2S32);
  EClassId Shl = op(G_SHL, X, cst(1, V2S32));
  G.rebuild();
  const KnownBits &K = G.getKnownBits(Shl);
  ASSERT_EQ(K.getBitWidth(), 32u);
  EXPECT_TRUE(K.Zero[0]);
  // A build of lanes has the facts that all lanes share.
  EClassId B = G.addOp(G_BUILD_VECTOR, V2S32, {cst(4), cst(6)});
  G.rebuild();
  // 4 = 0b100 and 6 = 0b110: bit 0 is zero and bit 2 one in both lanes.
  EXPECT_EQ(G.getKnownBits(B).Zero.countr_one(), 1u);
  EXPECT_EQ(G.getKnownBits(B).One.getZExtValue(), 4u);
}

//===----------------------------------------------------------------------===//
// Rules with a precondition on facts
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphViewsTest, AddOfDisjointBitsIsOrFromTheStructure) {
  // (x << 1) + 1 == (x << 1) | 1: the low bit of x << 1 is zero, which the
  // matched expression itself shows (no guard needed).
  EClassId X = in();
  EClassId T = op(G_SHL, X, cst(1));
  EClassId Sum = op(G_ADD, T, cst(1));
  SaturationStats S = runAll();
  EXPECT_TRUE(G.equivalent(Sum, lookup([&] { return op(G_OR, T, cst(1)); })));
  EXPECT_EQ(contextFacts(S), 0u);
  EXPECT_GT(S.Views["facts"].Merges, 0u);
}

TEST_F(GIEGraphViewsTest, AddOfDisjointBitsIsOrFromTheContext) {
  // x + 1 == x | 1 only because x is known to be even outside the region:
  // the rewrite is recorded as needing context facts.
  EClassId X = inKnownZero(1);
  EClassId Sum = op(G_ADD, X, cst(1));
  SaturationStats S = runAll();
  EXPECT_TRUE(G.equivalent(Sum, lookup([&] { return op(G_OR, X, cst(1)); })));
  EXPECT_GT(contextFacts(S), 0u);
}

TEST_F(GIEGraphViewsTest, FactPreconditionThatDoesNotHoldIsRejected) {
  EClassId X = in();
  EClassId Sum = op(G_ADD, X, cst(1));
  runAll();
  EXPECT_FALSE(G.equivalent(Sum, lookup([&] { return op(G_OR, X, cst(1)); })));
  // An input with the wrong facts (bit 1, not bit 0, known zero).
  EClassId Y = inKnownZero(2);
  EClassId Sum2 = op(G_ADD, Y, cst(1));
  runAll();
  EXPECT_FALSE(
      G.equivalent(Sum2, lookup([&] { return op(G_OR, Y, cst(1)); })));
}

TEST_F(GIEGraphViewsTest, FactRulesCanBeTurnedOff) {
  EClassId X = inKnownZero(1);
  EClassId Sum = op(G_ADD, X, cst(1));
  SaturationLimits L;
  L.EnableFacts = false;
  SaturationStats S = runAll(L);
  EXPECT_FALSE(G.equivalent(Sum, lookup([&] { return op(G_OR, X, cst(1)); })));
  EXPECT_EQ(S.Views.count("facts"), 0u);
}

TEST_F(GIEGraphViewsTest, RedundantMaskOfKnownBits) {
  // (x >> 24) & 0xff == x >> 24: the mask keeps every bit that can be one.
  EClassId X = in();
  EClassId Sh = op(G_LSHR, X, cst(24));
  EClassId And = op(G_AND, Sh, cst(0xff));
  runAll();
  EXPECT_TRUE(G.equivalent(And, Sh));
}

TEST_F(GIEGraphViewsTest, KnownConstantIsExactOnlyWithoutPoison) {
  // ((x << 4) & 15) has all bits known (zero). With a maybe-poison x the
  // class is poison when x is, so it only refines to 0.
  EClassId X = in();
  EClassId V = op(G_AND, op(G_SHL, X, cst(4)), cst(15));
  EClassId D = in(true);
  EClassId W = op(G_AND, op(G_SHL, D, cst(4)), cst(15));
  runAll();
  EClassId Zero = lookup([&] { return cst(0); });
  EXPECT_FALSE(G.equivalent(V, Zero));
  EXPECT_TRUE(G.refinesTo(V, Zero));
  EXPECT_TRUE(G.equivalent(W, Zero));
}

TEST_F(GIEGraphViewsTest, VectorFactRuleIsLaneWise) {
  // <2 x s32>: (x << 1) + splat(1) == (x << 1) | splat(1) in each lane.
  EClassId X = in(V2S32);
  EClassId T = op(G_SHL, X, cst(1, V2S32));
  EClassId Sum = op(G_ADD, T, cst(1, V2S32));
  runAll();
  EXPECT_TRUE(G.equivalent(
      Sum, lookup([&] { return op(G_OR, T, cst(1, V2S32)); })));
}

//===----------------------------------------------------------------------===//
// Typed constants
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphViewsTest, ConstantsOfScalarsSplatsAndLanes) {
  EClassId Z = cst(0), Ones = cst(-1);
  EClassId VZ = cst(0, V2S32);
  EClassId Mixed = G.addOp(G_BUILD_VECTOR, V2S32, {cst(0), cst(7)});
  EClassId X = in();
  EClassId Partial = G.addOp(G_BUILD_VECTOR, V2S32, {X, cst(7)});
  G.rebuild();
  EXPECT_TRUE(G.isAllZero(Z));
  EXPECT_TRUE(G.isAllOnes(Ones));
  EXPECT_TRUE(G.isAllZero(VZ));
  EXPECT_FALSE(G.isAllZero(Mixed));
  ASSERT_TRUE(G.getSplatConstant(VZ));
  EXPECT_FALSE(G.getSplatConstant(Mixed));
  // Lanes of a non-splat, and a lane that is not known.
  LaneConstant L1 = G.getLaneConstant(Mixed, 1);
  EXPECT_EQ(L1.Kind, LaneConstant::Constant);
  EXPECT_EQ(L1.Value.getZExtValue(), 7u);
  EXPECT_EQ(L1.Value.getBitWidth(), 32u);
  EXPECT_EQ(G.getLaneConstant(Partial, 0).Kind, LaneConstant::Unknown);
  EXPECT_EQ(G.getLaneConstant(Partial, 1).Kind, LaneConstant::Constant);
  EXPECT_EQ(G.getLaneConstant(Mixed, 2).Kind, LaneConstant::Unknown);
  // Lane 0 of a scalar is the scalar.
  EXPECT_EQ(G.getLaneConstant(Ones, 0).Kind, LaneConstant::Constant);
}

TEST_F(GIEGraphViewsTest, ShuffleLaneWithoutValueIsNotAConstant) {
  EClassId A = G.addOp(G_BUILD_VECTOR, V2S32, {cst(1), cst(1)});
  EClassId Shuf = G.addOp(G_SHUFFLE_VECTOR, V2S32, {A, A}, 0,
                          G.internMask({0, -1}));
  G.rebuild();
  EXPECT_EQ(G.getLaneConstant(Shuf, 1).Kind, LaneConstant::NoValue);
  EXPECT_FALSE(G.isAllOnes(Shuf));
  EXPECT_FALSE(G.getSplatConstant(Shuf));
}

//===----------------------------------------------------------------------===//
// The definedness policy of view rewrites
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphViewsTest, LeafReadPolicy) {
  EClassId U = in(), D = in(true);
  InputInfo NP{S32, /*NotUndef=*/true, /*NotPoison=*/false};
  EClassId P = G.addInput(NP);
  G.rebuild();
  // x ^ x -> 0: dropping a leaf read twice.
  EXPECT_EQ(classifyLeafReads(G, {{U, 2, 0}}), RewriteKind::Refinement);
  EXPECT_EQ(classifyLeafReads(G, {{P, 2, 0}}), RewriteKind::Refinement);
  EXPECT_EQ(classifyLeafReads(G, {{D, 2, 0}}), RewriteKind::Exact);
  // x * 0 -> 0 (one read dropped) is exact for an undef that is not poison.
  InputInfo UNP{S32, /*NotUndef=*/false, /*NotPoison=*/true};
  EClassId Q = G.addInput(UNP);
  G.rebuild();
  EXPECT_EQ(classifyLeafReads(G, {{Q, 1, 0}}), RewriteKind::Exact);
  // x + x -> x << 1: fewer reads.
  EXPECT_EQ(classifyLeafReads(G, {{U, 2, 1}}), RewriteKind::Refinement);
  EXPECT_EQ(classifyLeafReads(G, {{D, 2, 1}}), RewriteKind::Exact);
  // x << 1 -> x + x: more reads of an undef value.
  EXPECT_EQ(classifyLeafReads(G, {{U, 1, 2}}), RewriteKind::Unsafe);
  EXPECT_EQ(classifyLeafReads(G, {{D, 1, 2}}), RewriteKind::Exact);
  // A leaf that only the right-hand side reads.
  EXPECT_EQ(classifyLeafReads(G, {{U, 0, 1}}), RewriteKind::Unsafe);
  EXPECT_EQ(classifyLeafReads(G, {{D, 0, 1}}), RewriteKind::Exact);
  // Entries of one class add up.
  EXPECT_EQ(classifyLeafReads(G, {{U, 1, 1}, {U, 1, 0}}),
            RewriteKind::Refinement);
}

//===----------------------------------------------------------------------===//
// Commutative normalization and AC views
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphViewsTest, ACConstantsOfASum) {
  // (a + 7) + (b + 9) == a + b + 16 (one read of each leaf: exact).
  EClassId A = in(), B = in();
  EClassId X = op(G_ADD, op(G_ADD, A, cst(7)), op(G_ADD, B, cst(9)));
  runAll();
  EXPECT_TRUE(G.equivalent(
      X, lookup([&] { return op(G_ADD, op(G_ADD, A, B), cst(16)); })));
}

TEST_F(GIEGraphViewsTest, ACParityOfXor) {
  // ((x ^ y) ^ (z ^ y)) ^ x: the pairs cancel. Exact for defined x and y;
  // for maybe-undef ones only a refinement to z.
  EClassId X = in(true), Y = in(true), Z = in();
  EClassId E =
      op(G_XOR, op(G_XOR, op(G_XOR, X, Y), op(G_XOR, Z, Y)), X);
  runAll();
  EXPECT_TRUE(G.equivalent(E, Z));
  EClassId U = in(), V = in(), W = in();
  EClassId F =
      op(G_XOR, op(G_XOR, op(G_XOR, U, V), op(G_XOR, W, V)), U);
  runAll();
  EXPECT_FALSE(G.equivalent(F, W));
  EXPECT_TRUE(G.refinesTo(F, W));
  EXPECT_EQ(extract(F), extract(W));
}

TEST_F(GIEGraphViewsTest, ACMasksOfAnd) {
  // (x & 0xff) & (y & 0x3f) == x & y & 0x3f.
  EClassId X = in(), Y = in();
  EClassId E = op(G_AND, op(G_AND, X, cst(0xff)), op(G_AND, Y, cst(0x3f)));
  runAll();
  EXPECT_TRUE(G.equivalent(
      E, lookup([&] { return op(G_AND, op(G_AND, X, Y), cst(0x3f)); })));
}

TEST_F(GIEGraphViewsTest, ACDuplicatesOfOr) {
  // (x | 0xf0) | (x | 0x03) == x | 0xf3.
  EClassId X = in(true);
  EClassId E = op(G_OR, op(G_OR, X, cst(0xf0)), op(G_OR, X, cst(0x03)));
  runAll();
  EXPECT_TRUE(G.equivalent(E, lookup([&] { return op(G_OR, X, cst(0xf3)); })));
}

} // namespace
