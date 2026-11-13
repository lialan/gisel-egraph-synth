//===- GIEGraphSliceTest.cpp - The bit-slice view of the e-graph ----------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Tests of applySliceViews: a class as an extension of a range of bits of
// another class, the forms that the view adds, the relations to them
// (merge or refinement) and the budgets. Most tests saturate without table
// rules, so that every relation they check is made by the view.
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GIEGraph.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "gtest/gtest.h"
#include <functional>
#include <map>

using namespace llvm;
using namespace llvm::egraph;
using namespace llvm::TargetOpcode;

namespace {

class GIEGraphSliceTest : public testing::Test {
protected:
  EGraph G;
  const LLT S8 = LLT::scalar(8);
  const LLT S16 = LLT::scalar(16);
  const LLT S32 = LLT::scalar(32);
  const LLT S64 = LLT::scalar(64);
  const LLT V2S32 = LLT::fixed_vector(2, 32);

  /// An input; Defined means neither undef nor poison.
  EClassId in(LLT Ty, bool Defined = false) {
    InputInfo I;
    I.Ty = Ty;
    I.NotUndef = I.NotPoison = Defined;
    return G.addInput(I);
  }
  EClassId in(bool Defined = false) { return in(S32, Defined); }
  EClassId cst(uint64_t V, LLT Ty) {
    return G.addConstantSplat(Ty, APInt(Ty.getScalarSizeInBits(), V));
  }
  EClassId cst(uint64_t V) { return cst(V, S32); }
  EClassId op(unsigned Opc, EClassId A, EClassId B, uint32_t Flags = 0) {
    return G.addOp(Opc, G.getType(A), {A, B}, Flags);
  }
  /// A shift or a mask by a constant of the type of \p A.
  EClassId opc(unsigned Opc, EClassId A, uint64_t K, uint32_t Flags = 0) {
    return op(Opc, A, cst(K, G.getType(A)), Flags);
  }
  EClassId cast(unsigned Opc, LLT Ty, EClassId A) {
    return G.addOp(Opc, Ty, {A});
  }
  /// A G_UBFX or G_SBFX with the position and width in \p PosTy (the type
  /// of X if not given).
  EClassId bitField(unsigned Opc, EClassId X, uint64_t Lo, uint64_t Width,
                    LLT PosTy = LLT()) {
    LLT Ty = G.getType(X);
    if (!PosTy.isValid())
      PosTy = Ty;
    return G.addOp(Opc, Ty, {X, cst(Lo, PosTy), cst(Width, PosTy)});
  }
  EClassId sextInReg(EClassId X, unsigned Bits) {
    return G.addOp(G_SEXT_INREG, G.getType(X), {X}, 0, Bits);
  }

  /// Saturate with the views only, without table rules: every relation
  /// then comes from a view.
  SaturationStats runViews(SaturationLimits Limits = SaturationLimits()) {
    return saturate(G, {}, Limits);
  }
  SaturationStats runAll(SaturationLimits Limits = SaturationLimits()) {
    std::vector<RewriteRule> All = getDefaultIntegerRules();
    return saturate(G, All, Limits);
  }
  /// The class of the node that \p Build adds, after a rebuild.
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
  uint64_t cost(EClassId Root) {
    DefaultCostModel CM;
    Extractor E(G, CM);
    return E.getDagCost({Root});
  }
  static ViewStats slice(const SaturationStats &S) {
    auto It = S.Views.find("slice");
    return It == S.Views.end() ? ViewStats() : It->second;
  }
};

//===----------------------------------------------------------------------===//
// Shifts and masks
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphSliceTest, ShiftAndMaskIsABitField) {
  // (x >> 8) & 0xff == zext(x[8 +: 8]) == G_UBFX x, 8, 8: one read of x on
  // each side, so the classes merge even for a maybe-poison x.
  EClassId X = in();
  EClassId C = opc(G_AND, opc(G_LSHR, X, 8), 0xff);
  SaturationStats S = runViews();
  EXPECT_TRUE(
      G.equivalent(C, lookup([&] { return bitField(G_UBFX, X, 8, 8); })));
  EXPECT_EQ(slice(S).Views, 1u);
  EXPECT_EQ(slice(S).Merges, 1u);
  EXPECT_EQ(slice(S).Refinements, 0u);
  EXPECT_EQ(cost(C), 1u);
}

TEST_F(GIEGraphSliceTest, NestedSlicesCompose) {
  // ((x >> 4) & 0xff) >> 2 & 0xf: the slice of a slice adds the offsets,
  // x[6 +: 4]. The original costs 4, the bit field 1, the shift and mask 2.
  EClassId X = in();
  EClassId A = opc(G_LSHR, X, 4);
  EClassId B = opc(G_AND, A, 0xff);
  EClassId C = opc(G_LSHR, B, 2);
  EClassId D = opc(G_AND, C, 0xf);
  G.rebuild();
  EXPECT_EQ(cost(D), 4u);
  SaturationStats S = runViews();
  EXPECT_TRUE(
      G.equivalent(D, lookup([&] { return bitField(G_UBFX, X, 6, 4); })));
  EXPECT_TRUE(G.equivalent(
      D, lookup([&] { return opc(G_AND, opc(G_LSHR, X, 6), 0xf); })));
  // The intermediate classes are slices of x too.
  EXPECT_TRUE(
      G.equivalent(B, lookup([&] { return bitField(G_UBFX, X, 4, 8); })));
  EXPECT_TRUE(
      G.equivalent(C, lookup([&] { return bitField(G_UBFX, X, 6, 6); })));
  EXPECT_EQ(cost(D), 1u);
  EXPECT_EQ(extract(D), "(G_UBFX %in0 6 4)");
  EXPECT_EQ(slice(S).Views, 3u);
  EXPECT_EQ(slice(S).Refinements, 0u);
  EXPECT_TRUE(S.Saturated);
}

TEST_F(GIEGraphSliceTest, MaskOfAShiftedFieldIsASlice) {
  // (x & 0xf0f) >> 8 == (x >> 8) & 0xf: the mask restricted to the field is
  // a mask of low bits.
  EClassId X = in();
  EClassId C = opc(G_LSHR, opc(G_AND, X, 0xf0f), 8);
  runViews();
  EXPECT_TRUE(
      G.equivalent(C, lookup([&] { return bitField(G_UBFX, X, 8, 4); })));
}

TEST_F(GIEGraphSliceTest, NonContiguousMaskIsNotASlice) {
  // x & 0xf0f and (x >> 4) & 0xf0f keep two fields: no view, the classes
  // keep their forms.
  EClassId X = in();
  EClassId C = opc(G_AND, X, 0xf0f);
  EClassId D = opc(G_AND, opc(G_LSHR, X, 4), 0xf0f);
  SaturationStats S = runViews();
  EXPECT_EQ(slice(S).Views, 0u);
  EXPECT_EQ(slice(S).Candidates, 0u);
  EXPECT_EQ(G.getClass(C).Nodes.size(), 1u);
  EXPECT_EQ(G.getClass(D).Nodes.size(), 1u);
}

//===----------------------------------------------------------------------===//
// Bounds
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphSliceTest, FieldUpToTheTopBitIsAShift) {
  // ((x >> 4) & 0x0fffffff) >> 4 == x[8 +: 24] == x >> 8: the field reaches
  // bit 31, so the form is a plain shift.
  EClassId X = in();
  EClassId C = opc(G_LSHR, opc(G_AND, opc(G_LSHR, X, 4), 0x0fffffff), 4);
  runViews();
  EClassId Shift = lookup([&] { return opc(G_LSHR, X, 8); });
  EXPECT_TRUE(G.equivalent(C, Shift));
  EXPECT_EQ(extract(C), "(G_LSHR %in0 8)");
}

TEST_F(GIEGraphSliceTest, FieldOutsideOfTheValueIsRejected) {
  // G_UBFX x, 28, 8 selects bits outside of the value (28 + 8 > 32), and a
  // shift by 32 is poison: neither is a slice.
  EClassId X = in();
  EClassId C = opc(G_AND, bitField(G_UBFX, X, 28, 8), 0xf);
  EClassId D = opc(G_AND, opc(G_LSHR, X, 32), 0xff);
  SaturationStats S = runViews();
  EXPECT_EQ(slice(S).Views, 0u);
  EXPECT_FALSE(G.equivalent(C, lookup([&] { return opc(G_LSHR, X, 28); })));
  EXPECT_FALSE(
      G.equivalent(C, lookup([&] { return bitField(G_UBFX, X, 28, 4); })));
  EXPECT_EQ(G.getClass(C).Nodes.size(), 1u);
  EXPECT_EQ(G.getClass(D).Nodes.size(), 1u);
}

TEST_F(GIEGraphSliceTest, FieldOfShiftedInZerosIsNotASlice) {
  // (x << 8) >> 4 has zeros below the bits of x: not a field of x.
  EClassId X = in();
  EClassId C = opc(G_LSHR, opc(G_SHL, X, 8), 4);
  SaturationStats S = runViews();
  EXPECT_EQ(slice(S).Views, 0u);
  EXPECT_EQ(G.getClass(C).Nodes.size(), 1u);
}

//===----------------------------------------------------------------------===//
// Sign extensions
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphSliceTest, SignedFieldOfShifts) {
  // (x << 24) >>a 24 == sext_inreg(x, 8); (x << 8) >>a 20 == sbfx(x, 12, 12).
  EClassId X = in();
  EClassId C = opc(G_ASHR, opc(G_SHL, X, 24), 24);
  EClassId D = opc(G_ASHR, opc(G_SHL, X, 8), 20);
  runViews();
  EXPECT_TRUE(G.equivalent(C, lookup([&] { return sextInReg(X, 8); })));
  EXPECT_TRUE(
      G.equivalent(D, lookup([&] { return bitField(G_SBFX, X, 12, 12); })));
  EXPECT_TRUE(G.equivalent(
      D, lookup([&] { return sextInReg(opc(G_LSHR, X, 12), 12); })));
  EXPECT_EQ(cost(C), 1u);
  EXPECT_EQ(cost(D), 1u);
}

TEST_F(GIEGraphSliceTest, ShiftOfASignExtension) {
  // ashr(sext(x), 4) == sext(ashr(x, 4)): the field x[4 +: 12] extended by
  // its sign bit, in either type.
  EClassId X = in(S16);
  EClassId C = opc(G_ASHR, cast(G_SEXT, S32, X), 4);
  runViews();
  EXPECT_TRUE(G.equivalent(
      C, lookup([&] { return cast(G_SEXT, S32, opc(G_ASHR, X, 4)); })));
  // A zero extension of a sign extension is neither: no slice of x.
  EClassId Y = in(S16);
  EClassId D = opc(G_AND, opc(G_LSHR, cast(G_SEXT, S32, Y), 4), 0xfffff);
  runViews();
  EXPECT_FALSE(G.equivalent(
      D, lookup([&] { return cast(G_ZEXT, S32, opc(G_ASHR, Y, 4)); })));
  EXPECT_FALSE(G.equivalent(
      D, lookup([&] { return cast(G_SEXT, S32, opc(G_ASHR, Y, 4)); })));
}

TEST_F(GIEGraphSliceTest, SignBitsAboveTheFieldOfASignExtension) {
  // ashr(sext(x), 20) for an s16 x has the sign bit of x in every bit: the
  // field above the bits of x is the sign extension of x[15 +: 1].
  EClassId X = in(S16);
  EClassId C = opc(G_ASHR, cast(G_SEXT, S32, X), 20);
  runViews();
  EXPECT_TRUE(G.equivalent(
      C, lookup([&] { return cast(G_SEXT, S32, opc(G_ASHR, X, 15)); })));
}

//===----------------------------------------------------------------------===//
// Widths
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphSliceTest, TruncateThenExtendIsAMask) {
  // zext(trunc(x) to s16) to s32 == x & 0xffff.
  EClassId X = in();
  EClassId C = cast(G_ZEXT, S32, cast(G_TRUNC, S16, X));
  runViews();
  EXPECT_TRUE(G.equivalent(C, lookup([&] { return opc(G_AND, X, 0xffff); })));
  // sext(trunc(x)) == sext_inreg(x, 16).
  EClassId D = cast(G_SEXT, S32, cast(G_TRUNC, S16, X));
  runViews();
  EXPECT_TRUE(G.equivalent(D, lookup([&] { return sextInReg(X, 16); })));
}

TEST_F(GIEGraphSliceTest, TruncateOfExtensionIsTheValue) {
  // trunc(zext(x)) == x: the slice is the whole of x.
  EClassId X = in(S16);
  EClassId C = cast(G_TRUNC, S16, cast(G_ZEXT, S32, X));
  EClassId D = cast(G_TRUNC, S16, cast(G_ANYEXT, S32, X));
  SaturationStats S = runViews();
  EXPECT_TRUE(G.equivalent(C, X));
  // The high bits of G_ANYEXT are not specified, but the field does not
  // contain them.
  EXPECT_TRUE(G.equivalent(D, X));
  EXPECT_EQ(slice(S).Refinements, 0u);
  // A field that contains them is not a slice.
  EClassId Y = in(S16);
  EClassId E = opc(G_LSHR, cast(G_ANYEXT, S32, Y), 8);
  EClassId F = cast(G_TRUNC, S16, E);
  runViews();
  EXPECT_EQ(G.getClass(F).Nodes.size(), 1u);
}

TEST_F(GIEGraphSliceTest, FieldOfAWideValueIsTakenInTheNarrowType) {
  // trunc((x >> 20) & 0xffff) >> 4 & 0xff for an s64 x is x[24 +: 8], which
  // is inside the low 32 bits: trunc(x) >> 24.
  EClassId X = in(S64);
  EClassId T = cast(G_TRUNC, S32, opc(G_AND, opc(G_LSHR, X, 20), 0xffff));
  EClassId C = opc(G_AND, opc(G_LSHR, T, 4), 0xff);
  EXPECT_EQ(cost(lookup([&] { return C; })), 7u);
  runViews();
  EClassId Narrow =
      lookup([&] { return opc(G_LSHR, cast(G_TRUNC, S32, X), 24); });
  EXPECT_TRUE(G.equivalent(C, Narrow));
  EXPECT_EQ(cost(C), 2u);
}

TEST_F(GIEGraphSliceTest, FieldAboveTheNarrowTypeIsShiftedFirst) {
  // trunc(x >> 40) & 0xff for an s64 x: x[40 +: 8], above bit 32, so the
  // forms shift in the wide type: trunc(ubfx(x, 40, 8)). The position of a
  // bit field of an s64 value is an s32.
  EClassId X = in(S64);
  EClassId C = opc(G_AND, cast(G_TRUNC, S32, opc(G_LSHR, X, 40)), 0xff);
  runViews();
  EXPECT_TRUE(G.equivalent(C, lookup([&] {
                             return cast(G_TRUNC, S32,
                                         bitField(G_UBFX, X, 40, 8, S32));
                           })));
}

TEST_F(GIEGraphSliceTest, TypesOfBitFieldPositions) {
  // A bit field of a value of the view keeps the type of its position; a
  // new one of an s64 value gets s32 (the legalizer cannot narrow it).
  EClassId X = in(S64);
  EClassId F = bitField(G_UBFX, X, 8, 40);
  EClassId C = opc(G_AND, opc(G_LSHR, F, 4), 0xff);
  EClassId Y = in(S64);
  EClassId D =
      opc(G_AND, opc(G_LSHR, opc(G_AND, opc(G_LSHR, Y, 4), 0xfff), 4), 0xff);
  runViews();
  EXPECT_TRUE(
      G.equivalent(C, lookup([&] { return bitField(G_UBFX, X, 12, 8); })));
  EXPECT_TRUE(
      G.equivalent(D, lookup([&] { return bitField(G_UBFX, Y, 8, 8, S32); })));
  // No bit field of a value wider than 64 bits: only the shift and mask.
  const LLT S128 = LLT::scalar(128);
  EClassId Z = in(S128);
  EClassId E =
      opc(G_AND, opc(G_LSHR, opc(G_AND, opc(G_LSHR, Z, 4), 0xfff), 4), 0xff);
  runViews();
  EXPECT_TRUE(G.equivalent(
      E, lookup([&] { return opc(G_AND, opc(G_LSHR, Z, 8), 0xff); })));
  for (EClassId Id : G.getClassIds())
    for (const ENode &N : G.getClass(Id).Nodes)
      if (N.isOperation() && N.Opcode == G_UBFX)
        EXPECT_NE(N.Ty, S128);
}

TEST_F(GIEGraphSliceTest, ExtractAndUnmergeAreSlices) {
  // G_EXTRACT and the results of G_UNMERGE_VALUES are fields too.
  EClassId X = in(S64);
  EClassId Hi = G.addOp(G_UNMERGE_VALUES, S32, {X}, 0, 1);
  EClassId C = opc(G_AND, opc(G_LSHR, Hi, 8), 0xff);
  EClassId Mid = G.addOp(G_EXTRACT, S16, {X}, 0, 16);
  EClassId D = cast(G_ZEXT, S32, opc(G_LSHR, Mid, 12));
  runViews();
  EXPECT_TRUE(G.equivalent(C, lookup([&] {
                             return cast(G_TRUNC, S32,
                                         bitField(G_UBFX, X, 40, 8, S32));
                           })));
  // x[28 +: 4] is inside the low 32 bits of x.
  EXPECT_TRUE(G.equivalent(
      D, lookup([&] { return opc(G_LSHR, cast(G_TRUNC, S32, X), 28); })));
}

//===----------------------------------------------------------------------===//
// Concatenations and definedness
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphSliceTest, PartOfAMergeDropsTheOtherPart) {
  // trunc(merge(a, b)) == a when b is not poison; otherwise the merge is
  // poison when b is and a is not, so it only refines to a.
  EClassId A = in(S16), B = in(S16);
  EClassId C = cast(G_TRUNC, S16, G.addOp(G_MERGE_VALUES, S32, {A, B}));
  EClassId Hi =
      cast(G_TRUNC, S16, opc(G_LSHR, G.addOp(G_MERGE_VALUES, S32, {A, B}), 16));
  SaturationStats S = runViews();
  EXPECT_FALSE(G.equivalent(C, A));
  EXPECT_TRUE(G.refinesTo(C, A));
  EXPECT_FALSE(G.equivalent(Hi, B));
  EXPECT_TRUE(G.refinesTo(Hi, B));
  EXPECT_EQ(extract(C), extract(A));
  // Also the shifted merge: lshr(merge(a, b), 16) ~> zext(b).
  EXPECT_EQ(slice(S).Merges, 0u);
  EXPECT_EQ(slice(S).Refinements, 3u);

  EClassId P = in(S16), Q = in(S16, /*Defined=*/true);
  EClassId D = cast(G_TRUNC, S16, G.addOp(G_MERGE_VALUES, S32, {P, Q}));
  runViews();
  EXPECT_TRUE(G.equivalent(D, P));
}

TEST_F(GIEGraphSliceTest, FieldAcrossTwoPartsIsASliceOfTheMerge) {
  // merge(a, b)[8 +: 16] has bits of both parts: it is a field of the
  // merge, not of a part, and nothing is dropped.
  EClassId A = in(S16), B = in(S16);
  EClassId M = G.addOp(G_MERGE_VALUES, S32, {A, B});
  EClassId C = opc(G_AND, opc(G_LSHR, M, 8), 0xffff);
  SaturationStats S = runViews();
  EXPECT_TRUE(
      G.equivalent(C, lookup([&] { return bitField(G_UBFX, M, 8, 16); })));
  EXPECT_EQ(slice(S).Refinements, 0u);
  EXPECT_TRUE(G.getRefinementClosure(C).empty());
}

TEST_F(GIEGraphSliceTest, FieldOfAnOrConcatenation) {
  // or(zext(a), shl(zext(b), 16)) is the concatenation of a and b; its high
  // half is b. The low half of the OR is known zero in the field, so the
  // OR reads it for nothing: a refinement unless a is not poison.
  EClassId A = in(S16), B = in(S16);
  EClassId V =
      op(G_OR, cast(G_ZEXT, S32, A), opc(G_SHL, cast(G_ZEXT, S32, B), 16));
  EClassId Hi = cast(G_TRUNC, S16, opc(G_LSHR, V, 16));
  EClassId Field = opc(G_AND, opc(G_LSHR, V, 20), 0xff);
  SaturationStats S = runViews();
  EXPECT_TRUE(G.refinesTo(Hi, B));
  EXPECT_FALSE(G.equivalent(Hi, B));
  EXPECT_EQ(extract(Hi), extract(B));
  // x[20 +: 8] of the concatenation is b[4 +: 8].
  EXPECT_TRUE(G.refinesTo(Field, lookup([&] {
                            return cast(G_ZEXT, S32, bitField(G_UBFX, B, 4, 8));
                          })));
  EXPECT_EQ(slice(S).ContextFacts, 0u);

  EClassId P = in(S16, /*Defined=*/true), Q = in(S16);
  EClassId W =
      op(G_OR, cast(G_ZEXT, S32, P), opc(G_SHL, cast(G_ZEXT, S32, Q), 16));
  EClassId Hi2 = cast(G_TRUNC, S16, opc(G_LSHR, W, 16));
  runViews();
  EXPECT_TRUE(G.equivalent(Hi2, Q));
}

TEST_F(GIEGraphSliceTest, FieldSelectedByContextFacts) {
  // y | (x << 16) where y is known to fit in 16 bits only from the context
  // (the facts of the input): the high half is x, a view that needs the
  // context facts.
  InputInfo YI;
  YI.Ty = S32;
  YI.Known = KnownBits(32);
  YI.Known.Zero = APInt::getHighBitsSet(32, 16);
  auto HighHalf = [&](EClassId Y, EClassId X) {
    EClassId Or = op(G_OR, Y, opc(G_SHL, cast(G_ZEXT, S32, X), 16));
    return cast(G_TRUNC, S16, opc(G_LSHR, Or, 16));
  };
  EClassId X = in(S16);
  EClassId C = HighHalf(G.addInput(YI), X);
  SaturationStats S = runViews();
  EXPECT_TRUE(G.refinesTo(C, X));
  // The shift too: lshr(or, 16) ~> zext(x).
  EXPECT_EQ(slice(S).ContextFacts, 2u);
  // Without the facts feature, the context facts are not used.
  EClassId X2 = in(S16);
  EClassId C2 = HighHalf(G.addInput(YI), X2);
  SaturationLimits L;
  L.EnableFacts = false;
  S = runViews(L);
  EXPECT_FALSE(G.refinesTo(C2, X2));
  EXPECT_EQ(slice(S).ContextFacts, 0u);
}

TEST_F(GIEGraphSliceTest, FlaggedNodeOnlyRefines) {
  // lshr exact is poison if it shifts out ones: the view without the flag
  // only refines it.
  EClassId X = in(true);
  EClassId C = opc(G_AND, opc(G_LSHR, X, 8, MachineInstr::IsExact), 0xff);
  runViews();
  EClassId U = lookup([&] { return bitField(G_UBFX, X, 8, 8); });
  EXPECT_FALSE(G.equivalent(C, U));
  EXPECT_TRUE(G.refinesTo(C, U));
}

TEST_F(GIEGraphSliceTest, VectorsAreNotSliced) {
  // A vector is lanes, never one wide integer.
  EClassId X = in(V2S32);
  EClassId C = op(G_AND, op(G_LSHR, X, cst(8, V2S32)), cst(0xff, V2S32));
  SaturationStats S = runViews();
  EXPECT_EQ(slice(S).Views, 0u);
  EXPECT_GT(slice(S).Unsupported, 0u);
  EXPECT_EQ(G.getClass(C).Nodes.size(), 1u);
}

//===----------------------------------------------------------------------===//
// Budgets, switches and determinism
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphSliceTest, BudgetStopsAreCounted) {
  EClassId X = in();
  EClassId D =
      opc(G_AND, opc(G_LSHR, opc(G_AND, opc(G_LSHR, X, 4), 0xff), 2), 0xf);
  SaturationLimits L;
  L.MaxViewVisits = 2;
  SaturationStats S = runViews(L);
  EXPECT_GT(slice(S).Budget, 0u);
  EXPECT_EQ(slice(S).Merges, 0u);
  EXPECT_EQ(G.getClass(D).Nodes.size(), 1u);
}

TEST_F(GIEGraphSliceTest, CandidateBudgetKeepsTheFirstForms) {
  // One form per view: the bit field, not the shift and mask.
  EClassId X = in();
  EClassId C = opc(G_AND, opc(G_LSHR, X, 8), 0xff);
  EClassId Y = in();
  EClassId D = opc(G_ASHR, opc(G_SHL, Y, 8), 20);
  SaturationLimits L;
  L.MaxViewCandidates = 1;
  SaturationStats S = runViews(L);
  EXPECT_TRUE(
      G.equivalent(C, lookup([&] { return bitField(G_UBFX, X, 8, 8); })));
  EXPECT_TRUE(
      G.equivalent(D, lookup([&] { return bitField(G_SBFX, Y, 12, 12); })));
  // sext_inreg(y >> 12, 12) was not added.
  EXPECT_FALSE(G.lookup(ENode::makeOp(G_LSHR, S32, {Y, G.find(cst(12))})));
  EXPECT_GT(slice(S).Budget, 0u);
}

TEST_F(GIEGraphSliceTest, NodeLimitStopsTheView) {
  EClassId X = in();
  EClassId C = opc(G_AND, opc(G_LSHR, X, 8), 0xff);
  G.rebuild();
  SaturationLimits L;
  L.MaxNodes = G.getNumNodes() + 1;
  SaturationStats S = runViews(L);
  // The view stops adding forms at the node limit: here after the first.
  EXPECT_EQ(G.getNumNodes(), L.MaxNodes);
  EXPECT_EQ(slice(S).Candidates, 1u);
  EXPECT_GT(slice(S).Budget, 0u);
  EXPECT_TRUE(
      G.equivalent(C, lookup([&] { return bitField(G_UBFX, X, 8, 8); })));
}

TEST_F(GIEGraphSliceTest, SliceViewCanBeTurnedOff) {
  EClassId X = in();
  EClassId D =
      opc(G_AND, opc(G_LSHR, opc(G_AND, opc(G_LSHR, X, 4), 0xff), 2), 0xf);
  SaturationLimits L;
  L.EnableSlice = false;
  SaturationStats S = runViews(L);
  EXPECT_EQ(S.Views.count("slice"), 0u);
  EXPECT_EQ(G.getClass(D).Nodes.size(), 1u);
  EXPECT_EQ(cost(D), 4u);
}

TEST_F(GIEGraphSliceTest, WithTheTableRules) {
  // The view and the table rules together: the nested slice is one bit
  // field, and the run is the same each time.
  auto Build = [](EGraph &H) {
    LLT Ty = LLT::scalar(32);
    auto C = [&](uint64_t V) { return H.addConstant(Ty, APInt(32, V)); };
    InputInfo I;
    I.Ty = Ty;
    EClassId X = H.addInput(I);
    EClassId A = H.addOp(G_LSHR, Ty, {X, C(4)});
    EClassId B = H.addOp(G_AND, Ty, {A, C(0xff)});
    EClassId D = H.addOp(G_LSHR, Ty, {B, C(2)});
    EClassId E = H.addOp(G_AND, Ty, {D, C(0xf)});
    EClassId F = H.addOp(G_ASHR, Ty, {H.addOp(G_SHL, Ty, {X, C(8)}), C(20)});
    return std::make_pair(E, F);
  };
  std::vector<RewriteRule> All = getDefaultIntegerRules();
  std::string Prints[2];
  unsigned Nodes[2];
  for (unsigned I = 0; I != 2; ++I) {
    EGraph H;
    auto [E, F] = Build(H);
    SaturationStats S = saturate(H, All, SaturationLimits());
    DefaultCostModel CM;
    Extractor Ex(H, CM);
    EXPECT_EQ(Ex.getExprString(E), "(G_UBFX %in0 6 4)");
    EXPECT_EQ(Ex.getExprString(F), "(G_SBFX %in0 12 12)");
    EXPECT_GT(slice(S).Merges, 0u);
    raw_string_ostream OS(Prints[I]);
    H.print(OS);
    Nodes[I] = H.getNumNodes();
  }
  EXPECT_EQ(Prints[0], Prints[1]);
  EXPECT_EQ(Nodes[0], Nodes[1]);
}

//===----------------------------------------------------------------------===//
// Exhaustive check on small widths
//===----------------------------------------------------------------------===//

using ValueCache = std::map<EClassId, std::optional<APInt>>;

std::optional<APInt> evalClass(const EGraph &G, const Extractor &E, EClassId Id,
                               ArrayRef<APInt> Vals, ValueCache &Cache);

/// The value of the node \p N when input I has the value Vals[I], with the
/// operands computed through the nodes that \p E chose; std::nullopt for
/// poison.
std::optional<APInt> evalNode(const EGraph &G, const Extractor &E,
                              const ENode &N, ArrayRef<APInt> Vals,
                              ValueCache &Cache) {
  switch (N.Kind) {
  case ENodeKind::Input:
    return Vals[N.InputIdx];
  case ENodeKind::Constant:
    return N.Imm;
  case ENodeKind::Operation:
    break;
  }
  SmallVector<APInt, 3> Ops;
  for (EClassId Op : N.Ops) {
    std::optional<APInt> V = evalClass(G, E, Op, Vals, Cache);
    if (!V)
      return std::nullopt;
    Ops.push_back(*V);
  }
  return foldOperator(*getOpProperties(N.Opcode), Ops, N.Attr,
                      N.Ty.getSizeInBits());
}

std::optional<APInt> evalClass(const EGraph &G, const Extractor &E, EClassId Id,
                               ArrayRef<APInt> Vals, ValueCache &Cache) {
  Id = G.find(Id);
  auto It = Cache.find(Id);
  if (It != Cache.end())
    return It->second;
  const ENode *N = E.getChosenNode(Id);
  std::optional<APInt> V =
      N ? evalNode(G, E, *N, Vals, Cache) : std::optional<APInt>();
  Cache[Id] = V;
  return V;
}

/// For every value of the inputs (of InputBits bits each): every node of a
/// class has the value of the class, and every class that it refines to
/// has its value unless it is poison.
void expectConsistent(const EGraph &G, ArrayRef<unsigned> InputBits) {
  DefaultCostModel CM;
  Extractor E(G, CM);
  unsigned Total = 0;
  for (unsigned B : InputBits)
    Total += B;
  ASSERT_LE(Total, 16u);
  for (uint64_t Assign = 0; Assign != (uint64_t(1) << Total); ++Assign) {
    SmallVector<APInt, 2> Vals;
    unsigned Shift = 0;
    for (unsigned B : InputBits) {
      Vals.push_back(
          APInt(B, (Assign >> Shift) & maskTrailingOnes<uint64_t>(B)));
      Shift += B;
    }
    ValueCache Cache;
    for (EClassId C : G.getClassIds()) {
      std::optional<APInt> V = evalClass(G, E, C, Vals, Cache);
      for (const ENode &N : G.getClass(C).Nodes) {
        if (evalNode(G, E, N, Vals, Cache) != V) {
          ADD_FAILURE() << "a node differs from its class " << C
                        << " for the input assignment " << Assign;
          return;
        }
      }
      if (!V)
        continue;
      for (EClassId R : G.getRefinementClosure(C)) {
        if (evalClass(G, E, R, Vals, Cache) != V) {
          ADD_FAILURE() << "class " << C << " refines to " << R
                        << " of another value for the input assignment "
                        << Assign;
          return;
        }
      }
    }
  }
}

TEST_F(GIEGraphSliceTest, ExhaustiveOnSmallWidths) {
  // Chains of three slice operators on an s8 value, and chains of two on
  // the concatenations of two s4 values: after the view, all nodes of a
  // class have one value and every refinement keeps it, for every input.
  // (A check of the implementation, not a proof; the argument is in
  // docs/TargetAwareViews.md.)
  auto W = [&](EClassId X) { return G.getType(X).getSizeInBits(); };
  SmallVector<std::function<EClassId(EClassId)>, 16> Ops = {
      [&](EClassId X) { return opc(G_LSHR, X, 1); },
      [&](EClassId X) { return opc(G_LSHR, X, 3); },
      [&](EClassId X) { return opc(G_ASHR, X, 2); },
      [&](EClassId X) { return opc(G_SHL, X, 2); },
      [&](EClassId X) {
        return opc(G_AND, X, 0x3c & maskTrailingOnes<uint64_t>(W(X)));
      },
      [&](EClassId X) { return opc(G_AND, X, 0x07); },
      [&](EClassId X) {
        return W(X) > 4 ? cast(G_TRUNC, LLT::scalar(W(X) / 2), X) : X;
      },
      [&](EClassId X) {
        return W(X) < 32 ? cast(G_ZEXT, LLT::scalar(2 * W(X)), X) : X;
      },
      [&](EClassId X) {
        return W(X) < 32 ? cast(G_SEXT, LLT::scalar(2 * W(X)), X) : X;
      },
      [&](EClassId X) { return sextInReg(X, 3); },
      [&](EClassId X) { return bitField(G_UBFX, X, 1, 3); },
      [&](EClassId X) { return bitField(G_SBFX, X, 2, 2); },
  };
  unsigned Views = 0, Merges = 0, Refinements = 0;
  auto Count = [&](const SaturationStats &S) {
    Views += slice(S).Views;
    Merges += slice(S).Merges;
    Refinements += slice(S).Refinements;
  };
  for (unsigned I = 0, N = Ops.size(); I != N; ++I)
    for (unsigned J = 0; J != N; ++J)
      for (unsigned K = 0; K != N; ++K) {
        SCOPED_TRACE(testing::Message()
                     << "chain " << I << " " << J << " " << K);
        G = EGraph();
        EClassId X = in(S8, /*Defined=*/(I + J + K) % 2);
        Ops[K](Ops[J](Ops[I](X)));
        Count(runViews());
        expectConsistent(G, {8});
        if (HasFailure())
          return;
      }
  const LLT S4 = LLT::scalar(4);
  for (unsigned Shape = 0; Shape != 2; ++Shape)
    for (unsigned J = 0, N = Ops.size(); J != N; ++J)
      for (unsigned K = 0; K != N; ++K) {
        SCOPED_TRACE(testing::Message()
                     << "concatenation " << Shape << " " << J << " " << K);
        G = EGraph();
        EClassId A = in(S4, /*Defined=*/J % 2), B = in(S4, /*Defined=*/K % 2);
        EClassId V = Shape == 0 ? G.addOp(G_MERGE_VALUES, S8, {A, B})
                                : op(G_OR, cast(G_ZEXT, S8, A),
                                     opc(G_SHL, cast(G_ZEXT, S8, B), 4));
        Ops[K](Ops[J](V));
        Count(runViews());
        expectConsistent(G, {4, 4});
        if (HasFailure())
          return;
      }
  // The chains exercised the view.
  EXPECT_GT(Views, 1000u);
  EXPECT_GT(Merges, 500u);
  EXPECT_GT(Refinements, 50u);
}

} // namespace
