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
/// (factoring direction only), the algebra of unary operators and casts
/// (involutions, compositions, homomorphisms), comparisons, selects, and
/// constant folding. The hand-written rules below relate *different*
/// operators (negation through G_SUB, ~a as -1 - a, multiplication and
/// division by powers of two as shifts, ...).
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
/// The bitvector identities, and the poison behaviour the classification
/// assumes, were checked offline with an SMT solver
/// (llvm/utils/gisel-egraph/verify_rules.py). Pattern operators denote the
/// unflagged operations; a flagged instruction (nuw/nsw/exact/disjoint...)
/// only matches as a refinement, and so does a division that may trap.
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Twine.h"
#include "llvm/CodeGen/GlobalISel/GIEGraph.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/IR/Instructions.h"
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

std::string un(const OpProperties &P, StringRef A) {
  return ("(" + Twine(P.Name) + " " + A + ")").str();
}

std::string sel(const OpProperties &P, StringRef C, StringRef A, StringRef B) {
  return ("(" + Twine(P.Name) + " " + C + " " + A + " " + B + ")").str();
}

/// A comparison pattern with predicate \p Pred.
std::string cmp(const OpProperties &P, CmpInst::Predicate Pred, StringRef A,
                StringRef B) {
  return ("(" + Twine(P.Name) + ":" + CmpInst::getPredicateName(Pred) + " " +
          A + " " + B + ")")
      .str();
}

/// All integer comparison predicates, in a fixed order.
SmallVector<CmpInst::Predicate, 10> icmpPredicates() {
  SmallVector<CmpInst::Predicate, 10> Preds;
  for (unsigned P = CmpInst::FIRST_ICMP_PREDICATE;
       P <= CmpInst::LAST_ICMP_PREDICATE; ++P)
    Preds.push_back(static_cast<CmpInst::Predicate>(P));
  return Preds;
}

APInt boolean(bool V) { return APInt(1, V); }

/// The width of the class bound to variable \p V (never an AC term in the
/// positions this is used for).
unsigned varWidth(const EGraph &G, const RuleMatch &M, unsigned V) {
  assert(!M.isSumBound(V) && "variable bound to an AC term");
  return G.getType(M.Vars[V]).getSizeInBits();
}

/// Fold two constants (#a, #b) each with a third (#d) through a select:
/// computes $0 and $1 for (op (select ?c #a #b) #d), or with the constant
/// on the left if \p ConstOnLeft.
RewriteRule::ApplyFn foldArmsWith(std::optional<APInt> (*Fn)(const APInt &,
                                                             const APInt &),
                                  bool ConstOnLeft) {
  return [Fn, ConstOnLeft](const EGraph &G, const RuleMatch &M, Computed &Out) {
    // Constant variables are numbered in the order they appear in the
    // pattern: #a #b #d, or #d #a #b with the constant on the left.
    unsigned FirstArm = ConstOnLeft ? 1 : 0;
    const APInt &D = *M.Consts[ConstOnLeft ? 0 : 2];
    for (unsigned Arm = 0; Arm != 2; ++Arm) {
      const APInt &A = *M.Consts[FirstArm + Arm];
      std::optional<APInt> R = ConstOnLeft ? Fn(D, A) : Fn(A, D);
      if (!R || R->getBitWidth() != rootWidth(G, M))
        return false;
      Out.push_back(*R);
    }
    return true;
  };
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
  for (const OpProperties &P : Props)
    if (P.LeftAbsorbing)
      Add(P, "left-" + literalName(*P.LeftAbsorbing),
          bin(P, std::to_string(*P.LeftAbsorbing), "?a"),
          std::to_string(*P.LeftAbsorbing));
  // Constant results: a op c == r.
  for (const OpProperties &P : Props)
    for (auto [C, R] : P.RightConstResult)
      Add(P, literalName(C), bin(P, "?a", std::to_string(C)),
          std::to_string(R));
  // Self-application: idempotence (a op a == a) and a op a == c.
  for (const OpProperties &P : Props) {
    // The idempotence of a PHI is a canonical form (see
    // EGraph::collapseIdempotentPhis).
    if (P.Shape != OpShape::Binary)
      continue;
    if (P.Idempotent)
      Add(P, "self", bin(P, "?a", "?a"), "?a");
    else if (P.SelfValue)
      Add(P, "self", bin(P, "?a", "?a"), std::to_string(*P.SelfValue));
  }
  // Remainders: a - (a D b) * b == a op b.
  for (const OpProperties &P : Props) {
    if (!P.RemainderOf)
      continue;
    const OpProperties &D = propsOf(P.RemainderOf);
    const OpProperties &Sub = propsOf(TargetOpcode::G_SUB);
    const OpProperties &Mul = propsOf(TargetOpcode::G_MUL);
    Add(P, (Twine("from-") + D.ShortName).str(),
        bin(Sub, "?a", bin(Mul, bin(D, "?a", "?b"), "?b")), bin(P, "?a", "?b"));
  }
}

void llvm::egraph::addUnaryRulesFromProperties(
    ArrayRef<OpProperties> Props, std::vector<RewriteRule> &Rules) {
  auto Add = [&](const Twine &Name, const std::string &L, const std::string &R,
                 RewriteRule::ApplyFn Fn = nullptr) {
    Rules.emplace_back(Name.str(), L, R, std::move(Fn));
  };
  // Involutions: op(op(a)) == a.
  for (const OpProperties &P : Props)
    if (P.Involution)
      Add(Twine(P.ShortName) + "-involution", un(P, un(P, "?a")), "?a");
  // Compositions: op(g(a)) == h(a) and op(g(a)) == op(a).
  for (const OpProperties &P : Props) {
    for (auto [Inner, Result] : P.ComposesTo)
      Add(Twine(P.ShortName) + "-of-" + propsOf(Inner).ShortName,
          un(P, un(propsOf(Inner), "?a")), un(propsOf(Result), "?a"));
    for (unsigned Inner : P.InvariantUnder)
      Add(Twine(P.ShortName) + "-of-" + propsOf(Inner).ShortName,
          un(P, un(propsOf(Inner), "?a")), un(P, "?a"));
  }
  // A truncation of an extension is the value itself, a truncation or an
  // extension, depending on the widths. The three rules have the same
  // left-hand side; for given types only one of the right-hand sides is
  // well-typed.
  for (const OpProperties &T : Props) {
    if (T.Cast != CastKind::Truncate)
      continue;
    for (const OpProperties &E : Props) {
      if (E.Cast != CastKind::ZeroExtend && E.Cast != CastKind::SignExtend)
        continue;
      std::string Name = (Twine(T.ShortName) + "-of-" + E.ShortName).str();
      std::string L = un(T, un(E, "?a"));
      Add(Name + "-same", L, "?a");
      Add(Name + "-narrow", L, un(T, "?a"));
      Add(Name + "-wide", L, un(E, "?a"));
    }
  }
  // Homomorphisms: op(a) I op(b)  =>  op(a I b), and with a constant c that
  // has a preimage p: op(a) I c  =>  op(a I p).
  for (const OpProperties &P : Props) {
    for (unsigned IOpc : P.HomomorphicOver) {
      const OpProperties &I = propsOf(IOpc);
      std::string Name =
          (Twine("hoist-") + P.ShortName + "-" + I.ShortName).str();
      Add(Name, bin(I, un(P, "?a"), un(P, "?b")), un(P, bin(I, "?a", "?b")));
      if (!P.Preimage)
        continue;
      RewriteRule::ApplyFn Fn = [Preimage = P.Preimage](const EGraph &G,
                                                        const RuleMatch &M,
                                                        Computed &Out) {
        std::optional<APInt> C = Preimage(*M.Consts[0], varWidth(G, M, 0));
        if (!C)
          return false;
        Out.push_back(*C);
        return true;
      };
      Add(Name + "-const", bin(I, un(P, "?a"), "#c"), un(P, bin(I, "?a", "$0")),
          Fn);
      if (!I.Commutative)
        Add(Name + "-const-l", bin(I, "#c", un(P, "?a")),
            un(P, bin(I, "$0", "?a")), Fn);
    }
  }
}

void llvm::egraph::addCompareRulesFromProperties(
    ArrayRef<OpProperties> Props, std::vector<RewriteRule> &Rules) {
  const OpProperties &Xor = propsOf(TargetOpcode::G_XOR);
  for (const OpProperties &P : Props) {
    if (P.Shape != OpShape::Compare)
      continue;
    for (CmpInst::Predicate Pred : icmpPredicates()) {
      std::string Name =
          (Twine(P.ShortName) + "-" + CmpInst::getPredicateName(Pred)).str();
      // Reflexive and irreflexive predicates: a pred a.
      Rules.emplace_back(Name + "-self", cmp(P, Pred, "?a", "?a"),
                         CmpInst::isTrueWhenEqual(Pred) ? "-1" : "0");
      // The negation of a comparison is the inverse predicate.
      Rules.emplace_back(
          "not-" + Name, bin(Xor, cmp(P, Pred, "?a", "?b"), "-1"),
          cmp(P, CmpInst::getInversePredicate(Pred), "?a", "?b"));
      // A comparison with a constant that every value or no value
      // satisfies, e.g. a ult 0.
      Rules.emplace_back(
          Name + "-range", cmp(P, Pred, "?a", "#c"), "$0",
          [Pred](const EGraph &, const RuleMatch &M, Computed &Out) {
            ConstantRange CR =
                ConstantRange::makeExactICmpRegion(Pred, *M.Consts[0]);
            if (!CR.isFullSet() && !CR.isEmptySet())
              return false;
            Out.push_back(boolean(CR.isFullSet()));
            return true;
          });
    }
  }
}

void llvm::egraph::addSelectRulesFromProperties(
    ArrayRef<OpProperties> Props, std::vector<RewriteRule> &Rules) {
  const OpProperties &Xor = propsOf(TargetOpcode::G_XOR);
  const OpProperties &ZExt = propsOf(TargetOpcode::G_ZEXT);
  const OpProperties &SExt = propsOf(TargetOpcode::G_SEXT);
  for (const OpProperties &S : Props) {
    if (S.Shape != OpShape::Select)
      continue;
    auto Add = [&](const Twine &Suffix, const std::string &L,
                   const std::string &R, RewriteRule::ApplyFn Fn = nullptr,
                   bool PoisonExact = false) {
      Rules.emplace_back((Twine(S.ShortName) + "-" + Suffix).str(), L, R,
                         std::move(Fn), PoisonExact);
    };
    // The condition is an s1, so -1 is true.
    Add("true", sel(S, "-1", "?a", "?b"), "?a");
    Add("false", sel(S, "0", "?a", "?b"), "?b");
    Add("same", sel(S, "?c", "?a", "?a"), "?a");
    // Both sides are poison iff the condition or the selected arm is.
    Add("not", sel(S, bin(Xor, "?c", "-1"), "?a", "?b"),
        sel(S, "?c", "?b", "?a"), nullptr, /*PoisonExact=*/true);
    // Boolean arms. The first two are only well-typed for an s1 result, the
    // last two only for a wider one.
    Add("bool", sel(S, "?c", "-1", "0"), "?c");
    Add("bool-not", sel(S, "?c", "0", "-1"), bin(Xor, "?c", "-1"));
    Add("zext", sel(S, "?c", "1", "0"), un(ZExt, "?c"));
    Add("sext", sel(S, "?c", "-1", "0"), un(SExt, "?c"));

    // Factoring an operator with a common operand out of both arms. Both
    // sides are poison iff ?a, the condition or the selected arm is.
    for (const OpProperties &O : Props) {
      if (O.Shape != OpShape::Binary || O.IsShift || O.MayTrap)
        continue;
      std::string Name = (Twine("factor-") + O.ShortName).str();
      Add(Name, sel(S, "?c", bin(O, "?a", "?x"), bin(O, "?a", "?y")),
          bin(O, "?a", sel(S, "?c", "?x", "?y")), nullptr,
          /*PoisonExact=*/true);
      if (!O.Commutative)
        Add(Name + "-r", sel(S, "?c", bin(O, "?x", "?a"), bin(O, "?y", "?a")),
            bin(O, sel(S, "?c", "?x", "?y"), "?a"), nullptr,
            /*PoisonExact=*/true);
    }

    // Constant folding through a select of constants.
    std::string Arms = sel(S, "?c", "#a", "#b");
    std::string Folded = sel(S, "?c", "$0", "$1");
    for (const OpProperties &O : Props) {
      std::string Name = (Twine("fold-") + O.ShortName).str();
      if (O.Shape == OpShape::Binary && O.Fold) {
        Add(Name, bin(O, Arms, "#d"), Folded,
            foldArmsWith(O.Fold, /*ConstOnLeft=*/false));
        // A shift by a select is not a shift by a constant.
        if (!O.Commutative && !O.IsShift)
          Add(Name + "-l", bin(O, "#d", Arms), Folded,
              foldArmsWith(O.Fold, /*ConstOnLeft=*/true));
      } else if (O.FoldUnary) {
        Add(Name, un(O, Arms), Folded,
            [Fold = O.FoldUnary](const EGraph &G, const RuleMatch &M,
                                 Computed &Out) {
              for (unsigned Arm = 0; Arm != 2; ++Arm) {
                std::optional<APInt> R = Fold(*M.Consts[Arm], rootWidth(G, M));
                if (!R)
                  return false;
                Out.push_back(*R);
              }
              return true;
            });
      } else if (O.Shape == OpShape::Compare) {
        for (CmpInst::Predicate Pred : icmpPredicates())
          Add(Name + "-" + CmpInst::getPredicateName(Pred),
              cmp(O, Pred, Arms, "#d"), Folded,
              [Pred](const EGraph &, const RuleMatch &M, Computed &Out) {
                for (unsigned Arm = 0; Arm != 2; ++Arm)
                  Out.push_back(boolean(
                      ICmpInst::compare(*M.Consts[Arm], *M.Consts[2], Pred)));
                return true;
              });
      }
    }
  }
}

void llvm::egraph::addStructuralRulesFromProperties(
    ArrayRef<OpProperties> Props, std::vector<RewriteRule> &Rules) {
  for (const OpProperties &P : Props) {
    // An action of A: (p op a) op b == p op (a A b).
    if (P.ActsBy)
      Rules.emplace_back((Twine(P.ShortName) + "-assoc").str(),
                         bin(P, bin(P, "?p", "?a"), "?b"),
                         bin(P, "?p", bin(propsOf(P.ActsBy), "?a", "?b")));
    // An invertible terminator: op(~c) is the inverted form of op(c).
    if (P.InvertAttr)
      Rules.emplace_back((Twine(P.ShortName) + "-not").str(),
                         un(P, bin(propsOf(TargetOpcode::G_XOR), "?c", "-1")),
                         ("(" + Twine(P.Name) + ":inverted ?c)").str());
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
  for (const OpProperties &P : Props) {
    if (P.Shape != OpShape::Compare)
      continue;
    for (CmpInst::Predicate Pred : icmpPredicates())
      Rules.emplace_back(
          (Twine(P.ShortName) + "-" + CmpInst::getPredicateName(Pred) + "-swap")
              .str(),
          cmp(P, Pred, "?a", "?b"),
          cmp(P, CmpInst::getSwappedPredicate(Pred), "?b", "?a"));
  }
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
  for (const OpProperties &P : Props) {
    std::string Name = (Twine("fold-") + P.ShortName).str();
    if (P.Fold) {
      Rules.emplace_back(Name, bin(P, "#a", "#b"), "$0", foldWith(P.Fold));
    } else if (P.FoldUnary) {
      Rules.emplace_back(
          Name, un(P, "#a"), "$0",
          [Fold = P.FoldUnary](const EGraph &G, const RuleMatch &M,
                               Computed &Out) {
            std::optional<APInt> R = Fold(*M.Consts[0], rootWidth(G, M));
            if (!R)
              return false;
            Out.push_back(*R);
            return true;
          });
    } else if (P.Shape == OpShape::Compare) {
      for (CmpInst::Predicate Pred : icmpPredicates())
        Rules.emplace_back(
            (Name + "-" + CmpInst::getPredicateName(Pred)).str(),
            cmp(P, Pred, "#a", "#b"), "$0",
            [Pred](const EGraph &, const RuleMatch &M, Computed &Out) {
              Out.push_back(
                  boolean(ICmpInst::compare(*M.Consts[0], *M.Consts[1], Pred)));
              return true;
            });
    }
  }
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

  addUnaryRulesFromProperties(Props, R);
  // zext(trunc(a)) keeps the low bits of a. PatClasses[1] is the class of
  // the truncation (pattern nodes are numbered in post-order).
  Add("zext-of-trunc-to-and", "(G_ZEXT (G_TRUNC ?a))", "(G_AND ?a $0)",
      [](const EGraph &G, const RuleMatch &M, Computed &Out) {
        unsigned W = rootWidth(G, M);
        unsigned MidW = G.getType(M.PatClasses[1]).getSizeInBits();
        if (varWidth(G, M, 0) != W)
          return false;
        Out.push_back(APInt::getLowBitsSet(W, MidW));
        return true;
      });

  addCompareRulesFromProperties(Props, R);
  // Equality of a difference with zero.
  for (StringRef Pred : {"eq", "ne"}) {
    std::string Cmp = ("(G_ICMP:" + Pred + " ?a ?b)").str();
    Add(("icmp-" + Pred + "-xor-zero").str(),
        ("(G_ICMP:" + Pred + " (G_XOR ?a ?b) 0)").str(), Cmp);
    Add(("icmp-" + Pred + "-sub-zero").str(),
        ("(G_ICMP:" + Pred + " (G_SUB ?a ?b) 0)").str(), Cmp);
  }

  addSelectRulesFromProperties(Props, R);
  addStructuralRulesFromProperties(Props, R);

  // Division by a power of two and by -1.
  Add("udiv-pow2-to-lshr", "(G_UDIV ?a #c)", "(G_LSHR ?a $0)",
      [](const EGraph &G, const RuleMatch &M, Computed &Out) {
        const APInt &C = *M.Consts[0];
        if (!C.isPowerOf2() || C.isOne())
          return false;
        Out.push_back(APInt(rootWidth(G, M), C.logBase2()));
        return true;
      });
  Add("urem-pow2-to-and", "(G_UREM ?a #c)", "(G_AND ?a $0)",
      [](const EGraph &G, const RuleMatch &M, Computed &Out) {
        const APInt &C = *M.Consts[0];
        if (!C.isPowerOf2())
          return false;
        Out.push_back(C - 1);
        return true;
      });
  Add("sdiv-ones-to-neg", "(G_SDIV ?a -1)", "(G_SUB 0 ?a)");

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
