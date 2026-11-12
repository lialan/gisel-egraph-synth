//===- GIEGraphTuples.cpp - Operators with several results ----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// The tuple rules (see applyTupleRules in GIEGraph.h).
///
/// An instruction with several results is one e-node per result (ENode::Attr
/// is the index of the result); extraction counts the nodes of one
/// instruction once (Extractor::getMultiResultKey) and the emission builds it
/// once. Two things are added here:
///
///  * Siblings. For a node of result I of an instruction with several
///    results, the nodes of the other results with the same operands. Each
///    is a new class that is related to nothing; a table rule relates it to
///    a single-result operator (OpProperties::ProjectionOps, e.g. the rule
///    uaddo-0-to-add merges G_UADDO:0(a, b) with G_ADD a b), and then
///    extraction can compute several results with one instruction. A
///    sibling computes nothing that the program does not compute already:
///    it is another result of an instruction with the same operands, so in
///    particular a division with the same trapping behaviour.
///
///  * The carry of an addition as a comparison (getTupleRules): the carry
///    of a + b is set iff the wrapped sum is (unsigned) less than a, and
///    also iff it is less than b:
///
///      (G_ICMP:ult (G_ADD ?a ?b) ?a)  =>  (G_UADDO:1 ?a ?b)
///
///    (the commuted add and the swapped comparison `a ugt (a + b)` are the
///    same pattern for the matcher). On defined values both sides are equal,
///    and both are poison iff a or b is (an unflagged add and compare; a
///    flagged node is only matched as a refinement). The left-hand side
///    reads ?a twice and the right-hand side once, so the classification of
///    the table rules (RewriteRule::isExactFor, the same policy as
///    classifyLeafReads) makes it
///      - a merge (both directions) if ?a is not undef, and
///      - otherwise only the refinement icmp ~> uaddo:1: each read of an
///        undef ?a may see a different value, so the comparison can be true
///        or false for any b, and the carry is one of its values (the one in
///        which both reads agree). The other direction would replace one
///        read by two independent ones and is never applied.
///    The rule is a table rule so that verify_rules.py proves it like the
///    others (-gisel-egraph-print-rules prints it), but it is applied here,
///    behind SaturationLimits::EnableTuples, and not by the saturation loop.
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GIEGraph.h"
#include "llvm/CodeGen/TargetOpcodes.h"

using namespace llvm;
using namespace llvm::egraph;

std::vector<RewriteRule> llvm::egraph::getTupleRules() {
  std::vector<RewriteRule> Rules;
  Rules.emplace_back("uaddo-carry-from-icmp", "(G_ICMP:ult (G_ADD ?a ?b) ?a)",
                     "(G_UADDO:1 ?a ?b)");
  return Rules;
}

/// The nodes of the other results of the instruction of \p N, an operation
/// with several results, that the graph does not have.
static void collectSiblings(const EGraph &G, const ENode &N,
                            std::vector<ENode> &Out, ViewStats &Stats) {
  const OpProperties *P = getOpProperties(N.Opcode);
  unsigned NumResults;
  LLT MainTy;
  if (P->Shape == OpShape::Unmerge) {
    unsigned Part = N.Ty.getSizeInBits();
    unsigned Whole = G.getType(N.Ops[0]).getSizeInBits();
    if (!Part || Whole % Part) {
      ++Stats.Unsupported;
      return;
    }
    NumResults = Whole / Part;
  } else {
    NumResults = P->ResultKinds.size();
    for (unsigned I = 0, E = N.Ops.size(); I != E; ++I)
      if (I < P->OperandKinds.size() && P->OperandKinds[I] == TypeKind::Main)
        MainTy = G.getType(N.Ops[I]);
  }
  for (unsigned R = 0; R != NumResults; ++R) {
    if (R == N.Attr)
      continue;
    LLT Ty =
        P->Shape == OpShape::Unmerge ? N.Ty : getTypedResultType(*P, R, MainTy);
    if (!Ty.isValid()) {
      // A result of a type of its own (TypeKind::Free).
      ++Stats.Unsupported;
      continue;
    }
    Out.push_back(ENode::makeOp(N.Opcode, Ty, N.Ops, N.Flags, R));
  }
}

unsigned llvm::egraph::applyTupleRules(EGraph &G,
                                       const SaturationLimits &Limits,
                                       ViewStats &Stats) {
  static const std::vector<RewriteRule> Rules = getTupleRules();
  unsigned Changes = 0;

  // Read phase: the matches of the rules on the clean graph.
  SmallVector<std::pair<unsigned, RuleMatch>, 8> Matches;
  {
    ACViewCache Views(G, Limits.MaxACLeaves, Limits.MaxACViews);
    for (unsigned RI = 0, RE = Rules.size(); RI != RE; ++RI) {
      SmallVector<RuleMatch, 8> Ms;
      matchRule(G, Rules[RI], Ms, Limits.MaxMatchesPerIteration, &Views);
      for (RuleMatch &M : Ms)
        Matches.push_back({RI, std::move(M)});
    }
  }
  // Write phase.
  for (auto &[RI, M] : Matches) {
    if (G.getNumNodes() >= Limits.MaxNodes) {
      ++Stats.Budget;
      break;
    }
    ++Stats.Views;
    unsigned Before = G.getNumNodes();
    ApplyResult R = applyMatch(G, Rules[RI], M);
    Stats.Candidates += G.getNumNodes() - Before;
    Stats.count(R);
    if (R == ApplyResult::Rejected)
      ++Stats.Unsupported;
    if (R == ApplyResult::Merged || R == ApplyResult::Refined ||
        G.getNumNodes() != Before)
      ++Changes;
  }

  // The siblings, also of the nodes that the rules added. Collected first:
  // adding nodes may move the classes.
  std::vector<ENode> Siblings;
  for (EClassId Id : G.getClassIds())
    for (const ENode &N : G.getClass(Id).Nodes)
      if (N.isOperation() && getOpProperties(N.Opcode)->hasProjections())
        collectSiblings(G, N, Siblings, Stats);
  for (const ENode &S : Siblings) {
    if (G.getNumNodes() >= Limits.MaxNodes) {
      ++Stats.Budget;
      break;
    }
    unsigned Before = G.getNumNodes();
    G.add(S);
    if (G.getNumNodes() != Before) {
      ++Stats.Candidates;
      ++Changes;
    }
  }
  return Changes;
}
