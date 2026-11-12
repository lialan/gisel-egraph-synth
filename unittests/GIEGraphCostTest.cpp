//===- GIEGraphCostTest.cpp - DAG costs, patterns, banks and tuples -------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Tests of the generic cost layer of extraction: the DAG cost with target
// pattern covers (through a test cost model, not a target), the rules of
// sharing, the bank states, the sharing-aware improvement of the choices,
// and the tuple rules (siblings, the carry of G_UADDO as a comparison).
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GIEGraph.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/IR/InstrTypes.h"
#include "gtest/gtest.h"
#include <set>

using namespace llvm;
using namespace llvm::egraph;
using namespace llvm::TargetOpcode;

namespace {

/// The definedness facts of an input of type \p Ty (no known bits).
InputInfo inputInfo(LLT Ty, bool Defined) {
  InputInfo Info;
  Info.Ty = Ty;
  Info.NotUndef = Info.NotPoison = Defined;
  return Info;
}

/// A cost model with a fused three-operand add (a test pattern, not a
/// target): G_ADD whose operand is a G_ADD costs one instruction of 8 bytes.
/// Optional bank states: the inputs in UniformInputs are uniform.
class FusedAddCostModel : public DefaultCostModel {
public:
  bool Fuse = true;
  bool Banks = false;
  std::set<unsigned> UniformInputs;
  /// Also propose a cover of three adds (root, inner, inner of inner).
  bool ThreeLevels = false;

  void findCovers(const EGraph &G, const CostDag &D,
                  SmallVectorImpl<PatternCover> &Covers) const override {
    if (!Fuse)
      return;
    for (unsigned I = 0, E = D.Items.size(); I != E; ++I) {
      const ENode &N = *D.Items[I].N;
      if (!N.isOperation() || N.Opcode != G_ADD)
        continue;
      for (unsigned Op : D.Items[I].Ops) {
        const ENode &In = *D.Items[Op].N;
        if (!In.isOperation() || In.Opcode != G_ADD)
          continue;
        PatternCover C;
        C.Root = I;
        C.Inner.push_back(Op);
        C.Cost = {1, 8, 1};
        C.Name = "ADD3";
        Covers.push_back(C);
        if (!ThreeLevels)
          continue;
        for (unsigned Op2 : D.Items[Op].Ops)
          if (D.Items[Op2].N->isOperation() &&
              D.Items[Op2].N->Opcode == G_ADD) {
            PatternCover C3 = C;
            C3.Inner.push_back(Op2);
            C3.Name = "ADD4";
            Covers.insert(Covers.begin(), C3);
          }
      }
    }
  }
  bool hasBankStates() const override { return Banks; }
  bool canBeUniform(const EGraph &G, const ENode &N) const override {
    return !N.isInput() || UniformInputs.count(N.InputIdx);
  }
};

class GIEGraphCostTest : public testing::Test {
protected:
  EGraph G;
  const LLT S1 = LLT::scalar(1);
  const LLT S32 = LLT::scalar(32);

  EClassId in(bool Defined = false) {
    return G.addInput(inputInfo(S32, Defined));
  }
  EClassId cst(int64_t V) {
    return G.addConstant(S32, APInt(32, V, /*isSigned=*/true));
  }
  EClassId op(unsigned Opc, EClassId A, EClassId B) {
    return G.addOp(Opc, G.getType(A), {A, B});
  }
  EClassId add(EClassId A, EClassId B) { return op(G_ADD, A, B); }
  EClassId icmp(CmpInst::Predicate P, EClassId A, EClassId B) {
    return G.addOp(G_ICMP, S1, {A, B}, 0, P);
  }

  /// Extract \p Roots (all in the state Any unless \p States) and return
  /// the evaluation of the DAG.
  DagEvaluation extract(Extractor &E, const CostModel &CM,
                        ArrayRef<EClassId> Roots, bool Improve = true,
                        ArrayRef<BankState> States = {}) {
    ExtractionOptions Opts;
    Opts.ImproveDag = Improve;
    E.extract(Roots, States, CM, Opts);
    CostDag D;
    DagEvaluation Ev;
    if (!E.getDag(Roots, States, D)) {
      Ev.Cost = CostVector::infinite();
      return Ev;
    }
    evaluateDag(G, CM, D, &Ev);
    return Ev;
  }

  SaturationStats runAll(SaturationLimits Limits = SaturationLimits()) {
    std::vector<RewriteRule> All = getDefaultIntegerRules();
    return saturate(G, All, Limits);
  }
};

//===----------------------------------------------------------------------===//
// DAG cost with pattern covers
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphCostTest, CoverReplacesTheCostOfItsNodes) {
  EClassId A = in(), B = in(), C = in();
  EClassId R = add(add(A, B), C);
  G.rebuild();
  FusedAddCostModel CM;
  Extractor E(G, CM);
  DagEvaluation Ev = extract(E, CM, {R});
  EXPECT_EQ(Ev.Cost.Instrs, 1u);
  EXPECT_EQ(Ev.Cost.Bytes, 8u);
  EXPECT_EQ(Ev.Cost.Depth, 1u);
  ASSERT_EQ(Ev.Covers.size(), 1u);
  EXPECT_STREQ(Ev.Covers[0].Name, "ADD3");
  // Without the pattern: two instructions of 4 bytes, one after the other.
  CM.Fuse = false;
  Extractor E2(G, CM);
  DagEvaluation Flat = extract(E2, CM, {R});
  EXPECT_EQ(Flat.Cost.Instrs, 2u);
  EXPECT_EQ(Flat.Cost.Bytes, 8u);
  EXPECT_EQ(Flat.Cost.Depth, 2u);
  EXPECT_TRUE(Flat.Covers.empty());
  // The flat DAG cost agrees with getDagCost.
  EXPECT_EQ(E2.getDagCost({R}), 2u);
}

TEST_F(GIEGraphCostTest, SharedInnerNodeIsNotCovered) {
  // t = a + b; r = t + c; s = t ^ d: implementing r as one instruction still
  // needs t for s, so there is no saving.
  EClassId A = in(), B = in(), C = in(), D = in();
  EClassId T = add(A, B);
  EClassId R = add(T, C);
  EClassId S = op(G_XOR, T, D);
  G.rebuild();
  FusedAddCostModel CM;
  Extractor E(G, CM);
  DagEvaluation Ev = extract(E, CM, {R, S});
  EXPECT_EQ(Ev.Cost.Instrs, 3u);
  EXPECT_TRUE(Ev.Covers.empty());
}

TEST_F(GIEGraphCostTest, InnerRootIsNotCovered) {
  // The inner add is used outside of the DAG (a root): it stays.
  EClassId A = in(), B = in(), C = in();
  EClassId T = add(A, B);
  EClassId R = add(T, C);
  G.rebuild();
  FusedAddCostModel CM;
  Extractor E(G, CM);
  DagEvaluation Ev = extract(E, CM, {R, T});
  EXPECT_EQ(Ev.Cost.Instrs, 2u);
  EXPECT_TRUE(Ev.Covers.empty());
}

TEST_F(GIEGraphCostTest, OverlappingCoversAreNotDoubleCounted) {
  // ((a + b) + c) + d: the covers {t3; t2} and {t2; t1} overlap in t2. The
  // users come first, so t3 takes t2 and t1 stays: two instructions, never
  // one (t2 subtracted twice) or a negative saving.
  EClassId A = in(), B = in(), C = in(), D = in();
  EClassId T1 = add(A, B);
  EClassId T2 = add(T1, C);
  EClassId T3 = add(T2, D);
  G.rebuild();
  FusedAddCostModel CM;
  Extractor E(G, CM);
  DagEvaluation Ev = extract(E, CM, {T3});
  EXPECT_EQ(Ev.Cost.Instrs, 2u);
  ASSERT_EQ(Ev.Covers.size(), 1u);
  // A target that also proposes one instruction for all three adds (listed
  // first for the root): it is applied, and the two-add covers that overlap
  // it are not.
  CM.ThreeLevels = true;
  Extractor E2(G, CM);
  DagEvaluation Ev2 = extract(E2, CM, {T3});
  EXPECT_EQ(Ev2.Cost.Instrs, 1u);
  ASSERT_EQ(Ev2.Covers.size(), 1u);
  EXPECT_STREQ(Ev2.Covers[0].Name, "ADD4");
}

TEST_F(GIEGraphCostTest, CoverIsRejectedIfAnInnerHasAnotherUser) {
  // The cover {r; t} where t is also read by u (inside the DAG) is rejected
  // by evaluateDag even if a target proposes it.
  EClassId A = in(), B = in(), C = in();
  EClassId T = add(A, B);
  EClassId R = add(T, C);
  EClassId U = add(T, A);
  EClassId Root = op(G_XOR, R, U);
  G.rebuild();
  FusedAddCostModel CM;
  Extractor E(G, CM);
  DagEvaluation Ev = extract(E, CM, {Root});
  EXPECT_EQ(Ev.Cost.Instrs, 4u);
  EXPECT_TRUE(Ev.Covers.empty());
}

//===----------------------------------------------------------------------===//
// Sharing-aware extraction
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphCostTest, ImprovementChoosesTheFormThatThePatternMakesCheaper) {
  // r has two forms of tree cost 2: d * c (first) and (a + b) + c. Only the
  // DAG cost with the pattern sees that the second is one instruction.
  EClassId A = in(), B = in(), C = in(), D = in();
  EClassId Mul = op(G_MUL, D, C);
  EClassId Sum = add(add(A, B), C);
  G.merge(Mul, Sum);
  G.rebuild();
  FusedAddCostModel CM;
  Extractor E(G, CM);
  EXPECT_EQ(E.getChosenNode(Mul)->Opcode, unsigned(G_MUL));
  DagEvaluation Tree = extract(E, CM, {Mul}, /*Improve=*/false);
  EXPECT_EQ(Tree.Cost.Instrs, 2u);
  DagEvaluation Dag = extract(E, CM, {Mul}, /*Improve=*/true);
  EXPECT_EQ(Dag.Cost.Instrs, 1u);
  EXPECT_EQ(E.getChosenNode(Mul)->Opcode, unsigned(G_ADD));
}

TEST_F(GIEGraphCostTest, ImprovementChoosesTheSharedForm) {
  // Roots t = a + b and r, where r is d * e (first) or t + c. By tree cost
  // they tie (2); by DAG cost t + c is cheaper, because t is computed anyway.
  EClassId A = in(), B = in(), C = in(), D = in(), Ein = in();
  EClassId T = add(A, B);
  EClassId Mul = op(G_MUL, D, Ein);
  EClassId Sum = add(T, C);
  G.merge(Mul, Sum);
  G.rebuild();
  DefaultCostModel CM;
  Extractor E(G, CM);
  DagEvaluation Tree = extract(E, CM, {T, Mul}, /*Improve=*/false);
  EXPECT_EQ(Tree.Cost.Instrs, 3u);
  DagEvaluation Dag = extract(E, CM, {T, Mul}, /*Improve=*/true);
  EXPECT_EQ(Dag.Cost.Instrs, 2u);
  EXPECT_EQ(E.getExprString(Mul), "(G_ADD %in2 (G_ADD %in0 %in1))");
  EXPECT_EQ(E.getDagCost({T, Mul}), 2u);
}

TEST_F(GIEGraphCostTest, ImprovementIsDeterministic) {
  auto Build = [](EGraph &G) {
    LLT S32 = LLT::scalar(32);
    auto In = [&] { return G.addInput(inputInfo(S32, false)); };
    EClassId A = In(), B = In(), C = In(), D = In(), E = In();
    EClassId T = G.addOp(G_ADD, S32, {A, B});
    EClassId Mul = G.addOp(G_MUL, S32, {D, E});
    EClassId Sum = G.addOp(G_ADD, S32, {T, C});
    EClassId X = G.addOp(G_XOR, S32, {T, D});
    G.merge(Mul, Sum);
    G.rebuild();
    return std::make_pair(Mul, X);
  };
  std::string First;
  for (int Run = 0; Run < 3; ++Run) {
    EGraph H;
    auto [R1, R2] = Build(H);
    FusedAddCostModel CM;
    Extractor E(H, CM);
    E.extract({R1, R2}, {}, CM, ExtractionOptions());
    std::string S = E.getExprString(R1) + " " + E.getExprString(R2);
    if (Run == 0)
      First = S;
    EXPECT_EQ(S, First);
  }
}

TEST_F(GIEGraphCostTest, RefinementTargetIsAnAlternative) {
  // r ~> t + c (a refinement edge) where t is a root: taking the edge shares
  // t. By tree cost r keeps its own node d * e (2 < 2 is false).
  EClassId A = in(), B = in(), C = in(), D = in(), Ein = in();
  EClassId T = add(A, B);
  EClassId R = op(G_MUL, D, Ein);
  EClassId Sum = add(T, C);
  G.addRefinement(R, Sum);
  G.rebuild();
  DefaultCostModel CM;
  Extractor E(G, CM);
  DagEvaluation Tree = extract(E, CM, {T, R}, /*Improve=*/false);
  EXPECT_EQ(Tree.Cost.Instrs, 3u);
  DagEvaluation Dag = extract(E, CM, {T, R}, /*Improve=*/true);
  EXPECT_EQ(Dag.Cost.Instrs, 2u);
  EXPECT_EQ(E.resolve(R), G.find(Sum));
}

//===----------------------------------------------------------------------===//
// Bank states
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphCostTest, UniformRootTakesAUniformImplementation) {
  // r = u + w (uniform inputs) is also v - (v - u - w)-like: here simply a
  // cheaper node that reads the divergent input v. A root that must stay
  // uniform takes the uniform form.
  EClassId U = in(), W = in(), V = in();
  EClassId Uniform = op(G_MUL, U, W); // tree cost 2
  EClassId Divergent = add(V, U);     // tree cost 1
  G.merge(Uniform, Divergent);
  G.rebuild();
  FusedAddCostModel CM;
  CM.Fuse = false;
  CM.Banks = true;
  CM.UniformInputs = {0, 1};
  Extractor E(G, CM);
  DagEvaluation Any = extract(E, CM, {Uniform}, true, {BankState::Any});
  EXPECT_EQ(Any.Cost.Instrs, 1u);
  EXPECT_EQ(E.getChosenNode(Uniform)->Opcode, unsigned(G_ADD));
  DagEvaluation Uni = extract(E, CM, {Uniform}, true, {BankState::Uniform});
  EXPECT_EQ(Uni.Cost.Instrs, 2u);
  EXPECT_EQ(E.getChosenNode(Uniform)->Opcode, unsigned(G_MUL));
  EXPECT_EQ(Uni.BankViolations, 0u);
  // Without bank states the requirement does not exist.
  CM.Banks = false;
  Extractor E2(G, CM);
  DagEvaluation NoBanks =
      extract(E2, CM, {Uniform}, true, {BankState::Uniform});
  EXPECT_EQ(NoBanks.Cost.Instrs, 1u);
}

TEST_F(GIEGraphCostTest, UniformRootFromADivergentValueIsInfinite) {
  EClassId V = in(), U = in();
  EClassId R = add(V, U);
  G.rebuild();
  FusedAddCostModel CM;
  CM.Banks = true;
  CM.UniformInputs = {1};
  Extractor E(G, CM);
  E.extract({R}, {BankState::Uniform}, CM, ExtractionOptions());
  CostDag D;
  ASSERT_TRUE(E.getDag({R}, {BankState::Uniform}, D));
  DagEvaluation Ev;
  CostVector C = evaluateDag(G, CM, D, &Ev);
  EXPECT_TRUE(C.isInfinite());
  EXPECT_EQ(Ev.BankViolations, 1u);
  // The bank state of each item.
  EXPECT_EQ(D.Items.back().Bank, BankState::Any);
}

TEST_F(GIEGraphCostTest, ImprovementKeepsTheBankStates) {
  // The improvement may not move a uniform root to a divergent form even if
  // that form is shared and cheaper by DAG cost.
  EClassId U = in(), W = in(), V = in(), X = in();
  EClassId Shared = add(V, X);               // a divergent root
  EClassId Uniform = op(G_MUL, U, W);        // the uniform root, cost 2
  EClassId ViaShared = op(G_SUB, Shared, X); // equal to it here, cost 1
  G.merge(Uniform, ViaShared);
  G.rebuild();
  FusedAddCostModel CM;
  CM.Fuse = false;
  CM.Banks = true;
  CM.UniformInputs = {0, 1};
  Extractor E(G, CM);
  DagEvaluation Ev = extract(E, CM, {Shared, Uniform}, true,
                             {BankState::Any, BankState::Uniform});
  EXPECT_EQ(E.getChosenNode(Uniform)->Opcode, unsigned(G_MUL));
  EXPECT_EQ(Ev.Cost.Instrs, 3u);
  EXPECT_EQ(Ev.BankViolations, 0u);
}

//===----------------------------------------------------------------------===//
// Tuples
//===----------------------------------------------------------------------===//

TEST_F(GIEGraphCostTest, CarryOfAnAddIsAComparison) {
  // carry(a + b) == (a + b) <u a == (a + b) <u b == a >u (a + b).
  EClassId A = in(/*Defined=*/true), B = in(/*Defined=*/true);
  EClassId S = add(A, B);
  EClassId CmpA = icmp(CmpInst::ICMP_ULT, S, A);
  EClassId CmpB = icmp(CmpInst::ICMP_ULT, S, B);
  EClassId Swapped = icmp(CmpInst::ICMP_UGT, A, S);
  runAll();
  std::optional<EClassId> Carry =
      G.lookup(ENode::makeOp(G_UADDO, S1, {A, B}, 0, 1));
  ASSERT_TRUE(Carry.has_value());
  EXPECT_TRUE(G.equivalent(CmpA, *Carry));
  EXPECT_TRUE(G.equivalent(CmpB, *Carry));
  EXPECT_TRUE(G.equivalent(Swapped, *Carry));
  // The sibling sum is the add.
  std::optional<EClassId> Sum =
      G.lookup(ENode::makeOp(G_UADDO, S32, {A, B}, 0, 0));
  ASSERT_TRUE(Sum.has_value());
  EXPECT_TRUE(G.equivalent(*Sum, S));
}

TEST_F(GIEGraphCostTest, CarryIsOnlyARefinementIfTheOperandMayBeUndef) {
  // The comparison reads a twice: with an undef a it can be anything, and
  // the carry is one of its values. Not the other way around.
  EClassId A = in(/*Defined=*/false), B = in(/*Defined=*/true);
  EClassId S = add(A, B);
  EClassId Cmp = icmp(CmpInst::ICMP_ULT, S, A);
  SaturationStats St = runAll();
  std::optional<EClassId> Carry =
      G.lookup(ENode::makeOp(G_UADDO, S1, {A, B}, 0, 1));
  ASSERT_TRUE(Carry.has_value());
  EXPECT_FALSE(G.equivalent(Cmp, *Carry));
  EXPECT_TRUE(G.refinesTo(Cmp, *Carry));
  EXPECT_FALSE(G.refinesTo(*Carry, Cmp));
  EXPECT_GE(St.Views["tuples"].Refinements, 1u);
  // b may be undef as well: it is read once on each side.
  EGraph H;
  EClassId A2 = H.addInput(inputInfo(S32, true)),
           B2 = H.addInput(inputInfo(S32, false));
  EClassId S2 = H.addOp(G_ADD, S32, {A2, B2});
  EClassId Cmp2 = H.addOp(G_ICMP, S1, {S2, A2}, 0, CmpInst::ICMP_ULT);
  std::vector<RewriteRule> All = getDefaultIntegerRules();
  saturate(H, All, SaturationLimits());
  std::optional<EClassId> Carry2 =
      H.lookup(ENode::makeOp(G_UADDO, S1, {A2, B2}, 0, 1));
  ASSERT_TRUE(Carry2.has_value());
  EXPECT_TRUE(H.equivalent(Cmp2, *Carry2));
}

TEST_F(GIEGraphCostTest, FlaggedAddIsNotAComparisonOfTheCarry) {
  // add nuw is poison when it wraps: the comparison is then poison and the
  // carry 1. Only a refinement (cmp ~> carry), never a merge.
  EClassId A = in(true), B = in(true);
  EClassId S = G.addOp(G_ADD, S32, {A, B}, MachineInstr::NoUWrap);
  EClassId Cmp = icmp(CmpInst::ICMP_ULT, S, A);
  runAll();
  std::optional<EClassId> Carry =
      G.lookup(ENode::makeOp(G_UADDO, S1, {A, B}, 0, 1));
  if (Carry)
    EXPECT_FALSE(G.equivalent(Cmp, *Carry));
}

TEST_F(GIEGraphCostTest, SiblingResultsAreAdded) {
  // The other result of an instruction with the same operands.
  EClassId A = in(true), B = in(true);
  G.addOp(G_UADDO, S32, {A, B}, 0, 0);
  EClassId Q = G.addOp(G_UDIVREM, S32, {A, B}, 0, 0);
  EClassId Rem = op(G_UREM, A, B);
  runAll();
  EXPECT_TRUE(G.lookup(ENode::makeOp(G_UADDO, S1, {A, B}, 0, 1)));
  std::optional<EClassId> R =
      G.lookup(ENode::makeOp(G_UDIVREM, S32, {A, B}, 0, 1));
  ASSERT_TRUE(R.has_value());
  // udivrem:1 is the remainder (the rule udivrem-1-to-urem). A division may
  // trap, so that is a refinement only: the remainder of the program is not
  // replaced by the instruction of the quotient.
  EXPECT_TRUE(G.refinesTo(*R, Rem));
  EXPECT_FALSE(G.equivalent(*R, Rem));
  EXPECT_FALSE(G.equivalent(Q, Rem));
}

TEST_F(GIEGraphCostTest, TuplesCanBeTurnedOff) {
  EClassId A = in(true), B = in(true);
  EClassId S = add(A, B);
  icmp(CmpInst::ICMP_ULT, S, A);
  SaturationLimits L;
  L.EnableTuples = false;
  runAll(L);
  EXPECT_FALSE(G.lookup(ENode::makeOp(G_UADDO, S1, {A, B}, 0, 1)));
}

TEST_F(GIEGraphCostTest, JointExtractionUsesOneInstructionForBothResults) {
  EClassId A = in(), B = in();
  EClassId S = add(A, B);
  EClassId Cmp = icmp(CmpInst::ICMP_ULT, S, A);
  EClassId Ext = G.addOp(G_ZEXT, S32, {Cmp});
  runAll();
  DefaultCostModel CM;
  // Both results used (the carry through an external user, the zext):
  // one G_UADDO.
  {
    Extractor E(G, CM);
    DagEvaluation Ev = extract(E, CM, {S, Ext});
    EXPECT_EQ(Ev.Cost.Instrs, 2u); // uaddo + zext
    const ENode *SumN = E.getChosenNode(S);
    const ENode *CarryN = E.getChosenNode(Cmp);
    ASSERT_TRUE(SumN && CarryN);
    EXPECT_EQ(SumN->Opcode, unsigned(G_UADDO));
    EXPECT_EQ(SumN->Attr, 0u);
    EXPECT_EQ(CarryN->Opcode, unsigned(G_UADDO));
    EXPECT_EQ(CarryN->Attr, 1u);
    EXPECT_EQ(E.getMultiResultKey(*SumN), E.getMultiResultKey(*CarryN));
    EXPECT_EQ(E.getDagCost({S, Ext}), 2u);
  }
  // Without the sharing-aware improvement: the add and the carry are two
  // instructions (the tree costs tie).
  {
    Extractor E(G, CM);
    DagEvaluation Ev = extract(E, CM, {S, Ext}, /*Improve=*/false);
    EXPECT_EQ(Ev.Cost.Instrs, 3u);
  }
  // Only the sum used: a plain G_ADD.
  {
    Extractor E(G, CM);
    DagEvaluation Ev = extract(E, CM, {S});
    EXPECT_EQ(Ev.Cost.Instrs, 1u);
    EXPECT_EQ(E.getChosenNode(S)->Opcode, unsigned(G_ADD));
  }
  // Only the carry used: one G_UADDO (its sum unused), not add + compare.
  {
    Extractor E(G, CM);
    DagEvaluation Ev = extract(E, CM, {Cmp});
    EXPECT_EQ(Ev.Cost.Instrs, 1u);
    EXPECT_EQ(E.getChosenNode(Cmp)->Opcode, unsigned(G_UADDO));
  }
}

} // namespace
