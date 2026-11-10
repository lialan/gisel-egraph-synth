//===- llvm/CodeGen/GlobalISel/GIEGraphRules.cpp - E-graph rule library ---===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// The default library of algebraic rewrite rules for scalar integer gMIR.
///
/// Most rules are generated from the operator properties in
/// getAllOpProperties() (GIEGraph.cpp): commutativity, associativity,
/// identities, absorbing elements, self-application, distributivity
/// (factoring direction only) and constant folding. The hand-written rules
/// below relate *different* operators (negation through G_SUB, ~a as
/// -1 - a, multiplication by powers of two as shifts, ...).
///
/// Every rule is a fixed-width bitvector identity LHS == RHS that holds for
/// *all* assignments of the pattern variables. Whether a particular match is
/// an exact equivalence (and may merge e-classes) or only a refinement (and
/// becomes a refinement edge) is derived automatically from the variable
/// occurrence counts and the not-undef / not-poison analyses; see
/// RewriteRule::isExactFor and RewriteRule::isRefinementFor. Rules therefore
/// only need to state the identity, its preconditions on constants, and how
/// to compute derived constants.
///
/// The bitvector identities were checked offline for widths 8, 16, 32 and 64
/// with an SMT solver (llvm/utils/gisel-egraph/verify_rules.py). Pattern
/// operators denote the unflagged operations; a flagged instruction
/// (nuw/nsw/exact/disjoint) only matches as a refinement.
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Twine.h"
#include "llvm/CodeGen/GlobalISel/GIEGraph.h"
#include "llvm/Support/ErrorHandling.h"
#include <string>

using namespace llvm;
using namespace llvm::egraph;

namespace {
using Computed = SmallVectorImpl<APInt>;

unsigned rootWidth(const EGraph &G, const RuleMatch &M) {
  return G.getType(M.Root).getSizeInBits();
}

/// Fold a binary operation on two constants with \p Fn. Folds that would
/// produce poison (e.g. out-of-range shifts) return std::nullopt and are not
/// applied.
RewriteRule::ApplyFn foldWith(std::optional<APInt> (*Fn)(const APInt &,
                                                         const APInt &)) {
  return [Fn](const EGraph &G, const RuleMatch &M, Computed &Out) {
    std::optional<APInt> R = Fn(*M.Consts[0], *M.Consts[1]);
    if (!R || R->getBitWidth() != rootWidth(G, M))
      return false;
    Out.push_back(*R);
    return true;
  };
}

/// Name fragment for a literal in generated rule names: add-zero, mul-one,
/// and-ones, ...
std::string literalName(int64_t V) {
  switch (V) {
  case 0:
    return "zero";
  case 1:
    return "one";
  case -1:
    return "ones";
  default:
    return "c" + std::to_string(V);
  }
}

const OpProperties &propsOf(unsigned Opcode) {
  const OpProperties *P = getOpProperties(Opcode);
  if (!P)
    report_fatal_error("GIEGraph: operator property refers to an "
                       "unsupported opcode");
  return *P;
}

std::string bin(const OpProperties &P, StringRef A, StringRef B) {
  return ("(" + Twine(P.Name) + " " + A + " " + B + ")").str();
}
} // namespace

void llvm::egraph::addAlgebraRulesFromProperties(
    ArrayRef<OpProperties> Props, std::vector<RewriteRule> &Rules) {
  auto Add = [&](const OpProperties &P, StringRef Suffix, const std::string &L,
                 const std::string &R) {
    Rules.emplace_back((Twine(P.ShortName) + "-" + Suffix).str(), L, R);
  };
  // Commutativity, and associativity of commutative operators, are not
  // rules: they are enforced by canonicalization (EGraph::canonicalize,
  // EGraph::canonicalizeAC, AC matching; see getImplicitPropertyRules).
  for (const OpProperties &P : Props) {
    if (!P.Associative || P.Commutative)
      continue;
    Add(P, "assoc-r", bin(P, bin(P, "?a", "?b"), "?c"),
        bin(P, "?a", bin(P, "?b", "?c")));
    Add(P, "assoc-l", bin(P, "?a", bin(P, "?b", "?c")),
        bin(P, bin(P, "?a", "?b"), "?c"));
  }
  // Identities: a op e == a.
  for (const OpProperties &P : Props)
    if (P.RightIdentity)
      Add(P, literalName(*P.RightIdentity),
          bin(P, "?a", std::to_string(*P.RightIdentity)), "?a");
  // Absorbing elements: a op z == z (drops ?a, so a refinement unless ?a is
  // not poison).
  for (const OpProperties &P : Props)
    if (P.RightAbsorbing)
      Add(P, literalName(*P.RightAbsorbing),
          bin(P, "?a", std::to_string(*P.RightAbsorbing)),
          std::to_string(*P.RightAbsorbing));
  // Self-application: idempotence (a op a == a) and a op a == c.
  for (const OpProperties &P : Props) {
    if (P.Idempotent)
      Add(P, "self", bin(P, "?a", "?a"), "?a");
    else if (P.SelfValue)
      Add(P, "self", bin(P, "?a", "?a"), std::to_string(*P.SelfValue));
  }
}

std::vector<RewriteRule>
llvm::egraph::getImplicitPropertyRules(ArrayRef<OpProperties> Props) {
  std::vector<RewriteRule> Rules;
  for (const OpProperties &P : Props)
    if (P.Commutative)
      Rules.emplace_back((Twine(P.ShortName) + "-comm").str(),
                         bin(P, "?a", "?b"), bin(P, "?b", "?a"));
  for (const OpProperties &P : Props)
    if (P.Associative && P.Commutative)
      Rules.emplace_back((Twine(P.ShortName) + "-assoc").str(),
                         bin(P, bin(P, "?a", "?b"), "?c"),
                         bin(P, "?a", bin(P, "?b", "?c")));
  return Rules;
}

void llvm::egraph::addFactoringRulesFromProperties(
    ArrayRef<OpProperties> Props, std::vector<RewriteRule> &Rules) {
  // Factoring reduces the number of uses of the shared operand, so these
  // rules are refinements unless that operand is known not to be undef.
  for (const OpProperties &O : Props) {
    for (unsigned IOpc : O.DistributesOver) {
      const OpProperties &I = propsOf(IOpc);
      std::string Name =
          (Twine("factor-") + O.ShortName + "-" + I.ShortName).str();
      // (a O b) I (a O c)  =>  a O (b I c)
      Rules.emplace_back(Name, bin(I, bin(O, "?a", "?b"), bin(O, "?a", "?c")),
                         bin(O, "?a", bin(I, "?b", "?c")));
      if (!O.RightIdentity)
        continue;
      // With a == a O e:  (a O b) I a  =>  a O (b I e).
      std::string E = std::to_string(*O.RightIdentity);
      Rules.emplace_back(Name + "-id", bin(I, bin(O, "?a", "?b"), "?a"),
                         bin(O, "?a", bin(I, "?b", E)));
      // a I (a O b)  =>  a O (e I b); covered by commutativity otherwise.
      if (!I.Commutative)
        Rules.emplace_back(Name + "-id-l", bin(I, "?a", bin(O, "?a", "?b")),
                           bin(O, "?a", bin(I, E, "?b")));
    }
    for (unsigned IOpc : O.RightDistributesOverConst) {
      const OpProperties &I = propsOf(IOpc);
      // (a O #k) I (b O #k)  =>  (a I b) O #k
      Rules.emplace_back(
          (Twine("factor-") + O.ShortName + "-" + I.ShortName).str(),
          bin(I, bin(O, "?a", "#k"), bin(O, "?b", "#k")),
          bin(O, bin(I, "?a", "?b"), "#k"));
    }
  }
}

void llvm::egraph::addFoldingRulesFromProperties(
    ArrayRef<OpProperties> Props, std::vector<RewriteRule> &Rules) {
  for (const OpProperties &P : Props)
    if (P.Fold)
      Rules.emplace_back((Twine("fold-") + P.ShortName).str(),
                         bin(P, "#a", "#b"), "$0", foldWith(P.Fold));
}

std::vector<RewriteRule> llvm::egraph::getDefaultIntegerRules() {
  std::vector<RewriteRule> R;
  auto Add = [&](StringRef Name, StringRef L, StringRef Rhs,
                 RewriteRule::ApplyFn Fn = nullptr) {
    R.emplace_back(Name, L, Rhs, std::move(Fn));
  };

  ArrayRef<OpProperties> Props = getAllOpProperties();
  addAlgebraRulesFromProperties(Props, R);

  // Negation / subtraction.
  Add("sub-to-add-neg", "(G_SUB ?a ?b)", "(G_ADD ?a (G_SUB 0 ?b))",
      [](const EGraph &G, const RuleMatch &M, Computed &) {
        // Do not rewrite a negation (0 - b) itself.
        if (M.isSumBound(0))
          return true;
        std::optional<APInt> A = G.getConstant(M.Vars[0]);
        return !(A && A->isZero());
      });
  Add("add-neg-to-sub", "(G_ADD ?a (G_SUB 0 ?b))", "(G_SUB ?a ?b)");
  Add("neg-neg", "(G_SUB 0 (G_SUB 0 ?a))", "?a");
  Add("neg-sub", "(G_SUB 0 (G_SUB ?a ?b))", "(G_SUB ?b ?a)");
  Add("neg-add", "(G_SUB 0 (G_ADD ?a ?b))",
      "(G_ADD (G_SUB 0 ?a) (G_SUB 0 ?b))");
  Add("add-negs", "(G_ADD (G_SUB 0 ?a) (G_SUB 0 ?b))",
      "(G_SUB 0 (G_ADD ?a ?b))");
  Add("neg-mul", "(G_SUB 0 (G_MUL ?a ?b))", "(G_MUL ?a (G_SUB 0 ?b))");
  Add("mul-neg", "(G_MUL ?a (G_SUB 0 ?b))", "(G_SUB 0 (G_MUL ?a ?b))");
  Add("mul-negconst", "(G_MUL ?a #c)", "(G_SUB 0 (G_MUL ?a $0))",
      [](const EGraph &G, const RuleMatch &M, Computed &Out) {
        const APInt &C = *M.Consts[0];
        if (!C.isNegative() || C.isMinSignedValue())
          return false;
        Out.push_back(-C);
        return true;
      });

  // Bitwise not as arithmetic: ~a == -1 - a. Connects xor-based patterns
  // (e.g. NotAPlusNegOne in Combine.td) to the additive rules.
  Add("xor-ones-to-sub", "(G_XOR ?a -1)", "(G_SUB -1 ?a)");

  // a + c with a negative constant c is a - (-c). Classes with a known
  // constant only keep the constant leaf (see EGraph::pruneConstantClasses),
  // so the negation of a constant cannot be matched structurally as
  // (G_SUB 0 ?b) and needs this dedicated form.
  Add("add-negconst", "(G_ADD ?a #c)", "(G_SUB ?a $0)",
      [](const EGraph &G, const RuleMatch &M, Computed &Out) {
        const APInt &C = *M.Consts[0];
        if (!C.isNegative() || C.isMinSignedValue())
          return false;
        Out.push_back(-C);
        return true;
      });

  addFactoringRulesFromProperties(Props, R);
  // a + a == a * 2 relates two operators, so it is not a property of either.
  // It reduces the uses of ?a (a refinement unless ?a is not undef).
  Add("add-self", "(G_ADD ?a ?a)", "(G_MUL ?a 2)");

  // Strength reduction / its inverse (exact: one use of ?a on each side).
  Add("mul-pow2-to-shl", "(G_MUL ?a #c)", "(G_SHL ?a $0)",
      [](const EGraph &G, const RuleMatch &M, Computed &Out) {
        const APInt &C = *M.Consts[0];
        if (!C.isPowerOf2() || C.isOne())
          return false;
        Out.push_back(APInt(rootWidth(G, M), C.logBase2()));
        return true;
      });
  Add("shl-to-mul", "(G_SHL ?a #k)", "(G_MUL ?a $0)",
      [](const EGraph &G, const RuleMatch &M, Computed &Out) {
        unsigned W = rootWidth(G, M);
        const APInt &K = *M.Consts[0];
        if (K.isZero() || K.uge(W))
          return false;
        Out.push_back(APInt::getOneBitSet(W, K.getZExtValue()));
        return true;
      });

  addFoldingRulesFromProperties(Props, R);

  // Rule names must be unique: statistics, reports and tests refer to them.
  for (unsigned I = 0, E = R.size(); I != E; ++I)
    for (unsigned J = 0; J != I; ++J)
      if (R[I].getName() == R[J].getName())
        report_fatal_error(Twine("GIEGraph: duplicate rule name '") +
                           R[I].getName() + "'");
  return R;
}
