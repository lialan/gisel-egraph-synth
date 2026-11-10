//===- llvm/CodeGen/GlobalISel/GIEGraphRules.cpp - E-graph rule library ---===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// The default library of generic algebraic rewrite rules for scalar integer
/// gMIR.
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

#include "llvm/CodeGen/GlobalISel/GIEGraph.h"

using namespace llvm;
using namespace llvm::egraph;

namespace {
using Computed = SmallVectorImpl<APInt>;

unsigned rootWidth(const EGraph &G, const RuleMatch &M) {
  return G.getType(M.Root).getSizeInBits();
}

/// Fold a binary operation on two constants. Shifts by an out-of-range amount
/// are poison and are never folded.
template <typename FnT> RewriteRule::ApplyFn foldWith(FnT Fn) {
  return [Fn](const EGraph &G, const RuleMatch &M, Computed &Out) {
    const APInt &A = *M.Consts[0];
    const APInt &B = *M.Consts[1];
    std::optional<APInt> R = Fn(A, B);
    if (!R || R->getBitWidth() != rootWidth(G, M))
      return false;
    Out.push_back(*R);
    return true;
  };
}

std::optional<APInt> shiftAmount(const APInt &Val, const APInt &Amt) {
  if (Amt.uge(Val.getBitWidth()))
    return std::nullopt;
  return Amt.zextOrTrunc(Val.getBitWidth());
}
} // namespace

std::vector<RewriteRule> llvm::egraph::getDefaultIntegerRules() {
  std::vector<RewriteRule> R;
  auto Add = [&](StringRef Name, StringRef L, StringRef Rhs,
                 RewriteRule::ApplyFn Fn = nullptr) {
    R.emplace_back(Name, L, Rhs, std::move(Fn));
  };

  // Commutativity.
  for (StringRef Op : {"G_ADD", "G_MUL", "G_AND", "G_OR", "G_XOR"}) {
    std::string O = Op.str();
    Add((Op.lower() + "-comm").substr(2), "(" + O + " ?a ?b)",
        "(" + O + " ?b ?a)");
  }

  // Associativity (both directions).
  for (StringRef Op : {"G_ADD", "G_MUL", "G_AND", "G_OR", "G_XOR"}) {
    std::string O = Op.str();
    Add((Op.lower() + "-assoc-r").substr(2),
        "(" + O + " (" + O + " ?a ?b) ?c)", "(" + O + " ?a (" + O + " ?b ?c))");
    Add((Op.lower() + "-assoc-l").substr(2),
        "(" + O + " ?a (" + O + " ?b ?c))", "(" + O + " (" + O + " ?a ?b) ?c)");
  }

  // Identities: x op e == x.
  Add("add-zero", "(G_ADD ?a 0)", "?a");
  Add("sub-zero", "(G_SUB ?a 0)", "?a");
  Add("mul-one", "(G_MUL ?a 1)", "?a");
  Add("and-ones", "(G_AND ?a -1)", "?a");
  Add("or-zero", "(G_OR ?a 0)", "?a");
  Add("xor-zero", "(G_XOR ?a 0)", "?a");
  Add("shl-zero", "(G_SHL ?a 0)", "?a");
  Add("lshr-zero", "(G_LSHR ?a 0)", "?a");
  Add("ashr-zero", "(G_ASHR ?a 0)", "?a");

  // Absorbing elements (drop ?a: refinement unless ?a is not poison).
  Add("mul-zero", "(G_MUL ?a 0)", "0");
  Add("and-zero", "(G_AND ?a 0)", "0");
  Add("or-ones", "(G_OR ?a -1)", "-1");

  // Idempotence / self-cancellation.
  Add("and-self", "(G_AND ?a ?a)", "?a");
  Add("or-self", "(G_OR ?a ?a)", "?a");
  Add("sub-self", "(G_SUB ?a ?a)", "0");
  Add("xor-self", "(G_XOR ?a ?a)", "0");

  // Negation / subtraction.
  Add("sub-to-add-neg", "(G_SUB ?a ?b)", "(G_ADD ?a (G_SUB 0 ?b))",
      [](const EGraph &G, const RuleMatch &M, Computed &) {
        // Do not rewrite a negation (0 - b) itself.
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

  // Factoring (one direction only: never expand). These reduce the number of
  // uses of ?a, so they are refinements unless ?a is known not undef.
  Add("factor-mul", "(G_ADD (G_MUL ?a ?b) (G_MUL ?a ?c))",
      "(G_MUL ?a (G_ADD ?b ?c))");
  Add("factor-mul-one", "(G_ADD (G_MUL ?a ?b) ?a)", "(G_MUL ?a (G_ADD ?b 1))");
  Add("add-self", "(G_ADD ?a ?a)", "(G_MUL ?a 2)");
  Add("factor-and-or", "(G_OR (G_AND ?a ?b) (G_AND ?a ?c))",
      "(G_AND ?a (G_OR ?b ?c))");
  Add("factor-or-and", "(G_AND (G_OR ?a ?b) (G_OR ?a ?c))",
      "(G_OR ?a (G_AND ?b ?c))");
  Add("factor-and-xor", "(G_XOR (G_AND ?a ?b) (G_AND ?a ?c))",
      "(G_AND ?a (G_XOR ?b ?c))");
  Add("factor-shl-add", "(G_ADD (G_SHL ?a #k) (G_SHL ?b #k))",
      "(G_SHL (G_ADD ?a ?b) #k)");

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

  // Constant folding.
  Add("fold-add", "(G_ADD #a #b)", "$0",
      foldWith([](const APInt &A, const APInt &B) -> std::optional<APInt> {
        return A + B;
      }));
  Add("fold-sub", "(G_SUB #a #b)", "$0",
      foldWith([](const APInt &A, const APInt &B) -> std::optional<APInt> {
        return A - B;
      }));
  Add("fold-mul", "(G_MUL #a #b)", "$0",
      foldWith([](const APInt &A, const APInt &B) -> std::optional<APInt> {
        return A * B;
      }));
  Add("fold-and", "(G_AND #a #b)", "$0",
      foldWith([](const APInt &A, const APInt &B) -> std::optional<APInt> {
        return A & B;
      }));
  Add("fold-or", "(G_OR #a #b)", "$0",
      foldWith([](const APInt &A, const APInt &B) -> std::optional<APInt> {
        return A | B;
      }));
  Add("fold-xor", "(G_XOR #a #b)", "$0",
      foldWith([](const APInt &A, const APInt &B) -> std::optional<APInt> {
        return A ^ B;
      }));
  Add("fold-shl", "(G_SHL #a #b)", "$0",
      foldWith([](const APInt &A, const APInt &B) -> std::optional<APInt> {
        if (auto Amt = shiftAmount(A, B))
          return A.shl(*Amt);
        return std::nullopt;
      }));
  Add("fold-lshr", "(G_LSHR #a #b)", "$0",
      foldWith([](const APInt &A, const APInt &B) -> std::optional<APInt> {
        if (auto Amt = shiftAmount(A, B))
          return A.lshr(*Amt);
        return std::nullopt;
      }));
  Add("fold-ashr", "(G_ASHR #a #b)", "$0",
      foldWith([](const APInt &A, const APInt &B) -> std::optional<APInt> {
        if (auto Amt = shiftAmount(A, B))
          return A.ashr(*Amt);
        return std::nullopt;
      }));
  return R;
}
