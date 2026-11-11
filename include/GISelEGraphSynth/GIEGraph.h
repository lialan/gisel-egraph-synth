//===- llvm/CodeGen/GlobalISel/GIEGraph.h - Typed e-graph for gMIR -*- C++ -*-//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// An experimental, target-independent e-graph over Generic MIR operators.
///
/// E-nodes reuse TargetOpcode::G_* opcodes and LLT types: scalar integer
/// arithmetic, casts, comparisons, selects, bit operations, pointer
/// arithmetic, PHIs and conditional branches (see OpProperties). The graph
/// supports hash-consing, union-find with congruence closure, a small
/// e-class analysis (constant value, "not undef", "not poison") and
/// *refinement edges*.
///
/// LLVM values may be undef or poison, so many textbook algebraic identities
/// are only refinements (the right-hand side is "more defined" than the
/// left-hand side) rather than equivalences. Merging two e-classes asserts
/// that their values are interchangeable in *both* directions; doing so for a
/// one-way refinement would be unsound, because extraction could later replace
/// the refined value by the less-defined one. Therefore the graph keeps two
/// relations:
///
///  * equality (union-find + congruence closure), used only for proven
///    equivalences, and
///  * refinement edges `From ~> To`, meaning "every use of From may be
///    replaced by To". Extraction may follow refinement edges, matching may
///    look through them (which in turn only yields refinements), but they are
///    never used to merge classes.
///
/// See llvm/docs/GlobalISel/GIEGraphCombiner-Design.md for the full design and
/// the soundness argument.
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_GLOBALISEL_GIEGRAPH_H
#define LLVM_CODEGEN_GLOBALISEL_GIEGRAPH_H

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/FunctionExtras.h"
#include "llvm/ADT/Hashing.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/CodeGenTypes/LowLevelType.h"
#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

namespace llvm {
class raw_ostream;

namespace egraph {

using EClassId = unsigned;

enum class ENodeKind : uint8_t {
  /// An opaque, typed symbolic input (e.g. a virtual register defined outside
  /// the region). Identified by InputIdx; inputs with different indices are
  /// never assumed equal.
  Input,
  /// A G_CONSTANT with an APInt value whose width equals the type size.
  Constant,
  /// A generic operation (TargetOpcode::G_*) with e-class operands.
  Operation,
};

/// An immutable expression node. Operands refer to e-classes.
struct ENode {
  ENodeKind Kind = ENodeKind::Operation;
  /// TargetOpcode::G_* opcode (G_CONSTANT for constants, 0 for inputs).
  unsigned Opcode = 0;
  /// Semantically relevant MachineInstr flags (nuw/nsw/exact/disjoint...).
  /// Flags are part of the node identity: `add nsw a, b` and `add a, b` are
  /// different operators.
  uint32_t Flags = 0;
  LLT Ty;
  /// Input index for ENodeKind::Input.
  unsigned InputIdx = 0;
  /// Value for ENodeKind::Constant (width == Ty.getSizeInBits()).
  APInt Imm;
  /// Operator-specific immediate of an operation; part of the node identity.
  /// For OpShape::Compare it is the CmpInst::Predicate. For OpShape::Phi and
  /// OpShape::Effect it identifies the instruction (see OpProperties). For an
  /// operator with several results it is the index of the result, and for
  /// OpProperties::ImmAttr the immediate operand of the instruction.
  uint64_t Attr = 0;
  SmallVector<EClassId, 2> Ops;

  static ENode makeInput(LLT Ty, unsigned Idx);
  static ENode makeConstant(LLT Ty, const APInt &Val);
  static ENode makeOp(unsigned Opcode, LLT Ty, ArrayRef<EClassId> Ops,
                      uint32_t Flags = 0, uint64_t Attr = 0);

  bool isInput() const { return Kind == ENodeKind::Input; }
  bool isConstant() const { return Kind == ENodeKind::Constant; }
  bool isOperation() const { return Kind == ENodeKind::Operation; }

  bool operator==(const ENode &O) const;
  bool operator!=(const ENode &O) const { return !(*this == O); }
};

hash_code hash_value(const ENode &N);

/// Definedness facts about a symbolic input.
struct InputInfo {
  LLT Ty;
  bool NotUndef = false;
  bool NotPoison = false;
};

/// An equivalence class of e-nodes plus analysis data. All nodes in a class
/// denote exactly the same value (including undef/poison behaviour).
struct EClass {
  LLT Ty;
  SmallVector<ENode, 2> Nodes;
  /// Classes whose value refines this class' value (this ~> target).
  SmallVector<EClassId, 1> RefinesTo;
  /// Analysis: known constant value of the class.
  std::optional<APInt> Const;
  /// Analysis: the value is a single well-defined value or poison (never a
  /// "fluctuating" undef value). Allows duplicating/merging uses.
  bool NotUndef = false;
  /// Analysis: the value is never poison.
  bool NotPoison = false;
};

/// A term of an associative and commutative (AC) operator, represented by
/// the multiset of its leaf classes: Opcode(Leaves[0], Leaves[1], ...).
/// Leaves are canonical class ids in increasing order.
struct ACTerm {
  unsigned Opcode = 0;
  SmallVector<EClassId, 4> Leaves;
  bool empty() const { return Leaves.empty(); }
  bool operator==(const ACTerm &O) const {
    return Opcode == O.Opcode && Leaves == O.Leaves;
  }
};

/// One way to see a class as an AC term: the leaves obtained by flattening
/// nested nodes of the same AC operator. ViaRefinement is set if a flagged
/// node was flattened (such a view only justifies refinements).
struct ACView {
  SmallVector<EClassId, 8> Leaves;
  bool ViaRefinement = false;
};

/// True if \p Opcode is associative and commutative. Such operators are not
/// rewritten by associativity/commutativity rules; the graph keeps their
/// terms in a canonical form and the matcher works modulo AC.
bool isACOperator(unsigned Opcode);

/// A typed e-graph over gMIR operators.
class EGraph {
public:
  EGraph() = default;

  /// Add a symbolic input with the given definedness facts.
  EClassId addInput(const InputInfo &Info);
  EClassId addConstant(LLT Ty, const APInt &Val);
  EClassId addOp(unsigned Opcode, LLT Ty, ArrayRef<EClassId> Ops,
                 uint32_t Flags = 0, uint64_t Attr = 0);
  /// Generic hash-consed node insertion. Operands are canonicalized.
  EClassId add(ENode N);

  /// Canonical representative of \p Id.
  EClassId find(EClassId Id) const;
  bool equivalent(EClassId A, EClassId B) const { return find(A) == find(B); }

  /// Assert that \p A and \p B denote exactly the same value. Returns true if
  /// two distinct classes were merged. The types must match.
  bool merge(EClassId A, EClassId B);

  /// Record that \p To refines \p From (uses of From may be replaced by To).
  /// Returns true if a new edge was added.
  bool addRefinement(EClassId From, EClassId To);

  /// True if \p To is reachable from \p From via equalities and refinement
  /// edges (i.e. a use of From may be replaced by To).
  bool refinesTo(EClassId From, EClassId To) const;

  /// Restore the congruence invariant and recompute analyses. Must be called
  /// after merges before matching/extraction.
  void rebuild();
  bool isClean() const { return !Dirty; }

  const EClass &getClass(EClassId Id) const { return Classes[find(Id)]; }
  LLT getType(EClassId Id) const { return getClass(Id).Ty; }
  std::optional<APInt> getConstant(EClassId Id) const {
    return getClass(Id).Const;
  }
  const InputInfo &getInputInfo(unsigned Idx) const { return Inputs[Idx]; }
  unsigned getNumInputs() const { return Inputs.size(); }

  /// Canonical class ids in increasing order.
  SmallVector<EClassId, 32> getClassIds() const;
  /// Canonical classes reachable from \p Id via refinement edges, excluding
  /// \p Id itself, in deterministic (BFS) order.
  SmallVector<EClassId, 4> getRefinementClosure(EClassId Id) const;

  unsigned getNumNodes() const { return NumNodes; }
  unsigned getNumClasses() const { return NumClasses; }

  /// Canonicalize the operands of \p N.
  ENode canonicalize(const ENode &N) const;

  /// Hash-consing lookup without insertion. Requires a clean graph.
  std::optional<EClassId> lookup(const ENode &N) const;

  /// The canonical form of the AC term Opc(Leaves...): the leaves sorted by
  /// class id and combined left to right, ((l0 op l1) op l2) op ... A single
  /// leaf is returned as is.
  EClassId addACTerm(unsigned Opc, LLT Ty, ArrayRef<EClassId> Leaves);
  /// Like addACTerm, but only looks the canonical form up.
  std::optional<EClassId> lookupACTerm(unsigned Opc, LLT Ty,
                                       ArrayRef<EClassId> Leaves) const;

  /// The AC views of class \p C for operator \p Opc (see ACView): for each
  /// node of \p C, its operands, its full flattening and its flattening up
  /// to classes that also contain other kinds of nodes. At most \p MaxViews
  /// views with at most \p MaxLeaves leaves each, in a deterministic order.
  void getACViews(EClassId C, unsigned Opc, SmallVectorImpl<ACView> &Out,
                  unsigned MaxLeaves, unsigned MaxViews) const;

  /// Associativity (with commutativity) as canonicalization: merge every
  /// class containing an unflagged AC node with the canonical form of the
  /// node's flattening (see addACTerm), so that terms that are equal modulo
  /// AC end up in the same class. Requires a clean graph; returns the number
  /// of merges. Stops adding nodes once the graph has \p MaxNodes nodes.
  unsigned canonicalizeAC(unsigned MaxLeaves, unsigned MaxNodes);

  /// N-ary idempotence, op(a, ..., a) == a, as canonicalization: merge every
  /// class containing a node of an idempotent OpShape::Phi operator whose
  /// operands are all the same class with that class. Requires a clean
  /// graph; returns the number of merges.
  unsigned collapseIdempotentPhis();

  /// Flatten the AC node \p N of class \p Root into \p Leaves (see the
  /// implementation for the choices made). Returns false if the term has
  /// more than \p MaxLeaves leaves.
  /// If \p UsedFlagged is non-null, flagged nodes are flattened too and
  /// *UsedFlagged tells whether one was (the result is then a refinement).
  bool flattenAC(EClassId Root, const ENode &N, bool StopAtMixed,
                 unsigned MaxLeaves, SmallVectorImpl<EClassId> &Leaves,
                 bool *UsedFlagged = nullptr) const;

  void print(raw_ostream &OS) const;

private:
  struct ENodeHash {
    size_t operator()(const ENode &N) const { return hash_value(N); }
  };
  void recomputeAnalyses();
  void pruneConstantClasses();
  bool computeNodeNotUndef(const ENode &N) const;
  bool computeNodeNotPoison(const ENode &N) const;

  std::vector<EClass> Classes;
  mutable std::vector<EClassId> Parent;
  std::vector<InputInfo> Inputs;
  std::unordered_map<ENode, EClassId, ENodeHash> Memo;
  /// Non-constant nodes removed from classes with a known constant value.
  /// They are invisible to matching and extraction but stay in the hash-cons
  /// memo, so re-deriving them is a no-op instead of a new class, and they
  /// still take part in congruence closure.
  std::vector<std::pair<ENode, EClassId>> Pruned;
  unsigned NumNodes = 0;
  unsigned NumClasses = 0;
  bool Dirty = false;
};

//===----------------------------------------------------------------------===//
// Rewrite rules
//===----------------------------------------------------------------------===//

/// A node of a rewrite pattern. Patterns are written as S-expressions:
///   (G_ADD ?a (G_SUB ?b ?a))   ?x : e-class variable
///   #c                         : constant variable (matches a known constant)
///   0, -1, 1                   : literal, sign-extended/truncated to the width
///   $0                         : computed constant (RHS only)
///   (G_ICMP:ult ?a ?b)         : operation with a given attribute (predicate)
///   (G_UADDO:1 ?a ?b)          : result 1 of an operator with several results
///   (G_SEXT_INREG:8 ?a)        : immediate operand (OpProperties::ImmAttr)
///   (G_SEXT_INREG:$0 ?a)       : RHS only: the immediate is the computed
///                                constant $0
///   (G_BRCOND:inverted ?c)     : RHS only: the attribute of the matched LHS
///                                root, transformed by OpProperties::InvertAttr
/// An operation without an attribute matches a node with any attribute; on
/// the RHS it is created with attribute 0.
/// The literals `smin` and `smax` are the smallest and the largest signed
/// value of the width.
struct PatNode {
  enum KindTy : uint8_t { Var, ConstVar, Literal, Computed, Op } Kind;
  enum AttrKindTy : uint8_t {
    AnyAttr,
    ExactAttr,
    InvertedRootAttr,
    ComputedAttr
  };
  AttrKindTy AttrKind = AnyAttr;
  unsigned Opcode = 0;
  unsigned Index = 0;
  int64_t Value = 0;
  uint64_t Attr = 0;
  SmallVector<unsigned, 2> Children;
};

struct Pattern {
  std::vector<PatNode> Nodes;
  unsigned Root = 0;
};

/// A single match of a rule's left-hand side.
struct RuleMatch {
  /// Marks Vars[V] of a variable bound to VarSums[V] instead of a class.
  static constexpr EClassId SumBound = ~0u - 1;

  EClassId Root = 0;
  SmallVector<EClassId, 4> Vars;
  /// For variables matched against several leaves of an AC term for which
  /// no class exists yet: the AC term (materialized when the rule fires).
  SmallVector<ACTerm, 0> VarSums;
  /// AC matching with extension: the root is `LHS op Rest`, where LHS is
  /// the matched pattern and Rest the remaining leaves of the root's view.
  /// The rule then relates the root to `RHS op Rest`.
  ACTerm Rest;
  SmallVector<std::optional<APInt>, 2> Consts;
  /// The class matched by each operation node of the LHS pattern (indexed
  /// like Pattern::Nodes); NoClass for other nodes and for operations matched
  /// modulo AC.
  static constexpr EClassId NoClass = ~0u;
  SmallVector<EClassId, 8> PatClasses;
  /// ENode::Attr of the node matched by each operation node of the LHS
  /// pattern (indexed like PatClasses).
  SmallVector<uint64_t, 8> PatAttrs;
  /// ENode::Attr of the node matched by the LHS root.
  uint64_t RootAttr = 0;
  /// A division or remainder matched by the LHS pattern that may have
  /// undefined behaviour. The original program executes it, so the RHS may
  /// contain a division with the same undefined behaviour.
  struct DivGuard {
    bool Signed;
    EClassId Dividend, Divisor;
  };
  SmallVector<DivGuard, 1> Guards;
  /// True if some structural part of the match was found by following a
  /// refinement edge, or matched an operation that is more defined than the
  /// pattern operator assumes (flags, possible undefined behaviour). Such a
  /// match only justifies a refinement.
  bool ViaRefinement = false;

  bool isSumBound(unsigned V) const { return Vars[V] == SumBound; }
};

class ACViewCache;

class RewriteRule {
public:
  /// Optional precondition / constant computation hook. Returns false to
  /// reject the match. May append computed constants ($0, $1, ...). A
  /// computed constant must have the bit width of the position it is used
  /// in.
  using ApplyFn = std::function<bool(const EGraph &, const RuleMatch &,
                                     SmallVectorImpl<APInt> &)>;

  /// Parse a rule. Reports a fatal error on malformed patterns (rules are
  /// compiled-in). \p PoisonExact asserts that LHS and RHS are poison under
  /// exactly the same conditions for every binding, even though that does
  /// not follow from the syntactic classification (see isExactFor); such
  /// rules are checked offline (verify_rules.py).
  RewriteRule(StringRef Name, StringRef LHS, StringRef RHS,
              ApplyFn Fn = nullptr, bool PoisonExact = false);

  StringRef getName() const { return Name; }
  const Pattern &getLHS() const { return LHS; }
  const Pattern &getRHS() const { return RHS; }
  unsigned getNumVars() const { return VarNames.size(); }
  unsigned getNumConstVars() const { return ConstNames.size(); }
  /// The operators of the left-hand side, sorted. A rule cannot match in a
  /// graph that lacks one of them.
  ArrayRef<unsigned> getLHSOpcodes() const { return LHSOpcodes; }
  unsigned getLHSOccurrences(unsigned Var) const { return OccL[Var]; }
  unsigned getRHSOccurrences(unsigned Var) const { return OccR[Var]; }
  const ApplyFn &getApplyFn() const { return Fn; }

  /// True if, for this binding, LHS and RHS denote exactly the same value
  /// (including undef and poison behaviour), so the classes may be merged.
  bool isExactFor(const EGraph &G, const RuleMatch &M) const;
  /// True if, for this binding, RHS refines LHS (uses of LHS may be replaced
  /// by RHS).
  bool isRefinementFor(const EGraph &G, const RuleMatch &M) const;

  /// Prints 'name: LHS => RHS', followed by the definedness requirements of
  /// the soundness classification: '; refine-defined: a b' lists the
  /// variables that must not be poison for RHS to refine LHS, and
  /// '; exact-defined: c' those that additionally must not be poison for the
  /// two sides to be equivalent.
  void print(raw_ostream &OS) const;

private:
  bool needsDefinedForRefinement(unsigned Var) const;
  bool needsDefinedForExactness(unsigned Var) const;

  std::string Name;
  Pattern LHS, RHS;
  std::vector<std::string> VarNames, ConstNames;
  SmallVector<unsigned, 4> OccL, OccR;
  SmallVector<unsigned, 4> LHSOpcodes;
  /// Per side, bit V is set if variable V is mentioned (the side may be
  /// poison because V is) and if it is strict (the side is poison whenever V
  /// is). They differ for the arms of a select.
  uint32_t MentionL = 0, StrictL = 0, MentionR = 0, StrictR = 0;
  bool PoisonExact = false;
  ApplyFn Fn;
};

//===----------------------------------------------------------------------===//
// Operator properties
//===----------------------------------------------------------------------===//

/// How the operands and the result of an operator are typed, and how its
/// result depends on poison operands.
enum class OpShape : uint8_t {
  /// T = op(T, T). Poison iff an operand is poison. For shifts and
  /// rotations the second operand is an amount of any scalar type.
  Binary,
  /// T = op(T). Poison iff the operand is poison.
  Unary,
  /// T2 = op(T1): a conversion between scalars of different widths, or
  /// between a pointer and a scalar (see OpProperties::Cast). Poison iff the
  /// operand is poison.
  Cast,
  /// T2 = op(T1): a bit count. The result type is independent of the source
  /// type. Poison iff the operand is poison.
  BitCount,
  /// s1 = op(T, T) with a CmpInst::Predicate in ENode::Attr. Poison iff an
  /// operand is poison.
  Compare,
  /// T = op(s1, T, T). Poison iff the condition or the selected arm is
  /// poison.
  Select,
  /// P = op(P, I): a pointer combined with an integer (an offset, a mask).
  /// Poison iff an operand is poison.
  PtrAdd,
  /// T = op(T, ..., T) with one operand per predecessor block, in a fixed
  /// order. ENode::Attr identifies the instruction, so two nodes are only
  /// congruent if they belong to the same block. Poison iff the incoming
  /// value is poison.
  Phi,
  /// An operator described by OpProperties::OperandKinds and ResultKinds: any
  /// number of operands and results, each of the main type T, an independent
  /// scalar type, or s1. With several results, each result is an e-node of
  /// its own and ENode::Attr is the index of the result. Every result is
  /// poison iff an operand is poison.
  Typed,
  /// T2 = op(T1, ..., T1): the concatenation of scalars of one type, least
  /// significant first. Poison iff an operand is poison.
  Merge,
  /// T1 = op(T2): result number ENode::Attr of splitting a scalar into
  /// scalars of one type, least significant first. Poison iff the operand is
  /// poison.
  Unmerge,
  /// A terminator: no result. Its class has no type, is never an operand
  /// and is only ever merged with another form of the same terminator.
  /// ENode::Attr identifies the instruction in bits 2 and up; bit 1 is set
  /// if the terminator can be inverted and bit 0 if this node is the
  /// inverted form.
  Effect,
};

enum class CastKind : uint8_t {
  None,
  Truncate,
  ZeroExtend,
  SignExtend,
  /// The high bits are not specified. Two extensions of one value to one
  /// type are the same value (as for CSE).
  AnyExtend,
  /// A truncation that clamps the value to the range of the result.
  SatTruncate,
  PtrToInt,
  IntToPtr,
  /// The bits [Attr, Attr + result width) of the operand.
  Extract,
};

/// The type of an operand or a result of an OpShape::Typed operator.
enum class TypeKind : uint8_t {
  /// The scalar type T that the operator computes in.
  Main,
  /// A scalar type of its own (an amount, a bit position, a result that
  /// only holds a small range).
  Free,
  /// s1.
  Bool,
};

/// ENode::Flags bit of the poison-generating variant of an operator; see
/// OpProperties::PoisonVariant.
constexpr uint32_t PoisonVariantFlag = 1u << 31;

/// Properties of a supported generic operator. The generic part of the rule
/// library is derived from these properties (see the add*RulesFromProperties
/// functions), so supporting a new operator, or a new fact about an existing
/// one, is a table entry rather than a set of hand-written rules.
///
/// The Shape gives the typing and poison behaviour of the unflagged
/// operator; no operator produces undef from defined operands. Operators
/// with MayTrap additionally have undefined behaviour for some operands. The
/// soundness classification of rule matches (RewriteRule::isExactFor)
/// relies on this.
///
/// Constants are integer literals sign-extended or truncated to the type
/// width, so -1 is all-ones. SignedMin and SignedMax stand for the smallest
/// and the largest signed value of the width.
struct OpProperties {
  static constexpr int64_t SignedMin = INT64_MIN;
  static constexpr int64_t SignedMax = INT64_MAX;

  unsigned Opcode = 0;
  /// TargetOpcode name used in patterns, e.g. "G_ADD".
  const char *Name = nullptr;
  /// Short name used in generated rule names, e.g. "add".
  const char *ShortName = nullptr;
  OpShape Shape = OpShape::Binary;
  /// The second operand is a shift amount (poison if out of range).
  bool IsShift = false;
  /// The second operand is a rotation amount of any scalar type, taken
  /// modulo the width.
  bool IsRotate = false;
  /// The instruction has a trailing immediate operand; it is ENode::Attr.
  /// Rules generated for all operators of a shape skip such operators.
  bool ImmAttr = false;
  /// ENode::Attr identifies the instruction, so two nodes are never
  /// congruent, and the result is neither undef nor poison (G_FREEZE).
  /// Rules do not create such nodes.
  bool StopsPoison = false;
  /// A bit-field extract (value, position, width): poison unless position
  /// and width are constants that select bits inside the value.
  bool IsBitField = false;
  /// The result can be poison although no operand is, e.g. because the exact
  /// result does not fit (non-saturating fixed-point arithmetic). Rules do
  /// not create such nodes.
  bool MayBePoison = false;
  /// The opcode of the variant that is poison for some operands and equal to
  /// this operator otherwise (G_CTLZ_ZERO_POISON for G_CTLZ). An instruction
  /// with that opcode is an e-node of this operator with PoisonVariantFlag,
  /// so like every flagged node it only matches as a refinement.
  unsigned PoisonVariant = 0;
  /// OpShape::Typed: the kinds of the operands and of the results.
  SmallVector<TypeKind, 3> OperandKinds;
  SmallVector<TypeKind, 2> ResultKinds;
  /// For an operator with several results: per result, the operator with one
  /// result that computes the same value (0 if there is none), e.g.
  /// {G_ADD, 0} for G_UADDO, {G_SDIV, G_SREM} for G_SDIVREM and {G_TRUNC}
  /// for G_UNMERGE_VALUES (only its first result is a truncation).
  SmallVector<unsigned, 2> ProjectionOps;
  /// Arithmetic with an overflow bit (result 1): the bit is 0 if the second
  /// operand is one of these constants.
  SmallVector<int64_t, 2> NoOverflowWith;
  /// The overflow bit of op(a, a) is 0.
  bool NoOverflowSelf = false;
  /// The overflow bit is the comparison of the operands with this
  /// CmpInst::Predicate (0 if none): G_USUBO borrows iff a ult b.
  unsigned OverflowPredicate = 0;
  /// The operator with a carry operand equal to 0 is this operator:
  ///   op(a, b, 0) == W(a, b), for every result.
  unsigned WithoutCarry = 0;
  /// A funnel shift of a value with itself is this rotation:
  ///   op(a, a, c) == R(a, c)
  unsigned SameOperandsOp = 0;
  /// A funnel shift by 0 is this operand (-1 if not applicable).
  int ZeroAmountOperand = -1;
  /// The operator is the inverse of this one: op(g(a)) == a if the types
  /// agree (G_INTTOPTR and G_PTRTOINT; every result of G_UNMERGE_VALUES of a
  /// G_MERGE_VALUES is the corresponding part, and merging all the results
  /// gives the original value).
  unsigned InverseOf = 0;
  /// G_MERGE_VALUES of a value and 0 is this extension.
  unsigned ZeroHighPartOp = 0;
  /// The operator with the immediate 0 is this operator (G_EXTRACT at
  /// offset 0 is G_TRUNC).
  unsigned ZeroImmOp = 0;
  /// Division and remainder: undefined behaviour if the second operand is
  /// zero and, if IsSigned, for the minimum value divided by -1. Such a node
  /// is only matched as a refinement, and a rule only creates one if a
  /// division with the same operands was matched (RuleMatch::Guards) or the
  /// divisor is a constant for which the behaviour is defined.
  bool MayTrap = false;
  bool IsSigned = false;

  //===--- Binary operators -----------------------------------------------===//

  /// a op b == b op a. Not a rewrite rule: e-nodes of commutative operators
  /// are canonicalized by sorting their operand classes, and the matcher
  /// tries both operand orders.
  bool Commutative = false;
  /// (a op b) op c == a op (b op c). If the operator is also commutative,
  /// this is not a rewrite rule either: AC terms are canonicalized
  /// (EGraph::canonicalizeAC) and patterns are matched modulo AC. Otherwise
  /// the two associativity rules are generated.
  bool Associative = false;
  /// a op a == a. For OpShape::Phi: op(a, ..., a) == a, enforced by
  /// EGraph::collapseIdempotentPhis instead of a rule.
  bool Idempotent = false;
  /// a op e == a. For a commutative operator this is also a left identity.
  std::optional<int64_t> RightIdentity;
  /// a op z == z (z is absorbing / an annihilator).
  std::optional<int64_t> RightAbsorbing;
  /// z op a == z.
  std::optional<int64_t> LeftAbsorbing;
  /// a op c == r for each listed pair (c, r), e.g. a urem 1 == 0.
  SmallVector<std::pair<int64_t, int64_t>, 2> RightConstResult;
  /// a op a == c (e.g. a - a == 0, a ^ a == 0).
  std::optional<int64_t> SelfValue;
  /// This operator is the remainder of the division D:
  ///   a - (a D b) * b == a op b
  unsigned RemainderOf = 0;
  /// The other operator D of a lattice (absorption): a op (a D b) == a.
  unsigned LatticeDual = 0;
  /// The operator selects one operand with this CmpInst::Predicate (0 if
  /// none): a op b == select(a pred b, a, b).
  unsigned SelectPredicate = 0;
  /// The operator is the difference of a maximum and a minimum {Max, Min}:
  ///   a op b == (a Max b) - (a Min b)
  std::pair<unsigned, unsigned> DifferenceOf = {0, 0};
  /// Left distributivity over each listed operator I:
  ///   a op (b I c) == (a op b) I (a op c)
  /// Only the factoring direction is generated, never the expansion:
  ///   (a op b) I (a op c)  =>  a op (b I c)
  /// and, if op has a right identity e (so a == a op e):
  ///   (a op b) I a  =>  a op (b I e)
  ///   a I (a op b)  =>  a op (e I b)    (only if I is not commutative)
  SmallVector<unsigned, 2> DistributesOver;
  /// Right distributivity over each listed operator I with a shared constant
  /// right operand (used for shifts, whose amount must stay a constant):
  ///   (a op #k) I (b op #k)  =>  (a I b) op #k
  SmallVector<unsigned, 4> RightDistributesOverConst;
  /// Constant folding; returns std::nullopt if the result is poison or the
  /// behaviour undefined (e.g. an out-of-range shift, a division by zero).
  /// The result must have the width of the first operand.
  std::optional<APInt> (*Fold)(const APInt &, const APInt &) = nullptr;

  //===--- Unary operators, casts and bit counts --------------------------===//

  /// op(op(a)) == a.
  bool Involution = false;
  /// The kind of conversion of an OpShape::Cast operator. The compositions
  /// of a truncation with an extension are derived from the kinds:
  ///   trunc(ext(a)) == a, trunc(a) or ext(a), depending on the widths.
  CastKind Cast = CastKind::None;
  /// op(g(a)) == h(a) for each listed pair (g, h), e.g.
  /// sext(zext(a)) == zext(a) and ctlz(bitreverse(a)) == cttz(a).
  SmallVector<std::pair<unsigned, unsigned>, 2> ComposesTo;
  /// op(g(a)) == op(a) for each listed operator g.
  SmallVector<unsigned, 2> InvariantUnder;
  /// The operator is a homomorphism for each listed binary operator I:
  ///   op(a I b) == op(a) I op(b)
  /// Only the hoisting direction is generated:
  ///   op(a) I op(b)  =>  op(a I b)
  /// and, if a constant c has a preimage p (op(p) == c, see Preimage):
  ///   op(a) I c  =>  op(a I p)
  SmallVector<unsigned, 4> HomomorphicOver;
  /// Constant folding of a unary operator to a constant of \p ResultWidth
  /// bits; returns std::nullopt if the operation is not defined for the
  /// operand width or the result does not fit.
  std::optional<APInt> (*FoldUnary)(const APInt &,
                                    unsigned ResultWidth) = nullptr;
  /// A constant p of \p SrcWidth bits with op(p) == \p C, if there is one.
  std::optional<APInt> (*Preimage)(const APInt &C, unsigned SrcWidth) = nullptr;
  /// Constant folding of any other operator: the operands, ENode::Attr and
  /// the width of the result. Returns std::nullopt if the result is poison,
  /// the behaviour undefined or the operation not defined for these widths.
  std::optional<APInt> (*FoldN)(ArrayRef<APInt> Ops, uint64_t Attr,
                                unsigned ResultWidth) = nullptr;

  //===--- Pointer arithmetic ---------------------------------------------===//

  /// The operator is an action of the listed binary operator A on its first
  /// operand: (p op a) op b == p op (a A b).
  unsigned ActsBy = 0;

  //===--- Terminators ----------------------------------------------------===//

  /// The operator has an inverted form: op(~c) with attribute A is the same
  /// terminator as op(c) with attribute InvertAttr(A). Returns std::nullopt
  /// if the node cannot be inverted.
  std::optional<uint64_t> (*InvertAttr)(uint64_t) = nullptr;

  /// The number of operands, or -1 if it varies (OpShape::Phi,
  /// OpShape::Merge).
  int NumOperands = 2;

  bool hasResult() const { return Shape != OpShape::Effect; }
  /// True if ENode::Attr is the index of a result.
  bool hasProjections() const {
    return Shape == OpShape::Unmerge || ResultKinds.size() > 1;
  }
  /// True if the second operand is an amount of any scalar type.
  bool hasAmount() const { return IsShift || IsRotate; }
};

/// The value of the pattern literal \p V at \p Width bits (see
/// OpProperties::SignedMin).
APInt getLiteralValue(int64_t V, unsigned Width);

/// The properties of the operator that an instruction with opcode
/// \p MIOpcode is an e-node of, or null. \p Flags is set to the ENode::Flags
/// bits that the opcode implies (see OpProperties::PoisonVariant).
const OpProperties *getOpPropertiesForInstr(unsigned MIOpcode, uint32_t &Flags);

/// The type of result \p Index of the OpShape::Typed operator \p P whose
/// main type is \p MainTy; invalid for a TypeKind::Free result.
LLT getTypedResultType(const OpProperties &P, unsigned Index, LLT MainTy);

/// The properties of all supported operators, in a fixed order.
ArrayRef<OpProperties> getAllOpProperties();
/// The properties of \p Opcode, or null if the operator is not supported.
const OpProperties *getOpProperties(unsigned Opcode);

/// Append the rules implied by \p Props (see OpProperties) to \p Rules.
/// Rules of one kind are emitted together for all operators, in table order:
/// associativity, identities, absorbing elements, constant results,
/// self-application and remainders; then (via the functions below) unary
/// operators and casts, comparisons, selects, factoring, and constant
/// folding.
void addAlgebraRulesFromProperties(ArrayRef<OpProperties> Props,
                                   std::vector<RewriteRule> &Rules);
/// Rules of unary operators, casts and bit counts: involutions,
/// compositions, invariance, hoisting out of a homomorphic operator, and the
/// compositions of truncations with extensions.
void addUnaryRulesFromProperties(ArrayRef<OpProperties> Props,
                                 std::vector<RewriteRule> &Rules);
/// Rules of OpShape::Compare operators, per predicate: comparison of a value
/// with itself, negation of the result, comparison with a constant that no
/// value or every value satisfies.
void addCompareRulesFromProperties(ArrayRef<OpProperties> Props,
                                   std::vector<RewriteRule> &Rules);
/// Rules of OpShape::Select operators: constant and inverted conditions,
/// equal arms, boolean arms, and factoring an operator out of both arms.
void addSelectRulesFromProperties(ArrayRef<OpProperties> Props,
                                  std::vector<RewriteRule> &Rules);
/// Rules of pointer arithmetic (OpProperties::ActsBy) and of terminators
/// (OpProperties::InvertAttr).
void addStructuralRulesFromProperties(ArrayRef<OpProperties> Props,
                                      std::vector<RewriteRule> &Rules);
/// Identities that hold by \p Props but are enforced by canonicalization
/// instead of rewriting (commutativity, associativity of AC operators, and
/// swapping the operands of a comparison).
/// They are never applied; they exist so that the properties can be checked
/// offline like the rules
/// (-gisel-egraph-print-rules, verify_rules.py).
std::vector<RewriteRule> getImplicitPropertyRules(ArrayRef<OpProperties> Props);
void addFactoringRulesFromProperties(ArrayRef<OpProperties> Props,
                                     std::vector<RewriteRule> &Rules);
void addFoldingRulesFromProperties(ArrayRef<OpProperties> Props,
                                   std::vector<RewriteRule> &Rules);

/// The default library of algebraic rules for scalar integer gMIR: the rules
/// derived from getAllOpProperties() plus a few hand-written rules that
/// relate different operators (negation, strength reduction, ...).
std::vector<RewriteRule> getDefaultIntegerRules();

/// Collect all matches of \p Rule's LHS (up to \p Limit). Patterns rooted
/// at an AC operator are matched modulo AC using the views in \p Cache (a
/// cache with default limits is used if it is null).
void matchRule(const EGraph &G, const RewriteRule &Rule,
               SmallVectorImpl<RuleMatch> &Matches, unsigned Limit = ~0u,
               ACViewCache *Cache = nullptr);

/// Result of applying one match.
enum class ApplyResult { NoChange, Merged, Refined, Rejected, Unsafe };

/// Apply one match: merges if exact, adds a refinement edge if only a
/// refinement, and does nothing if neither can be justified.
ApplyResult applyMatch(EGraph &G, const RewriteRule &Rule, const RuleMatch &M);

struct SaturationLimits {
  unsigned MaxIterations = 10;
  unsigned MaxNodes = 5000;
  unsigned MaxMatchesPerIteration = 20000;
  /// Backoff scheduling (as in egg's BackoffScheduler): a rule that matches
  /// more than RuleMatchLimit << N times in one iteration, where N is the
  /// number of times it was banned before, is banned for RuleBanLength << N
  /// iterations and its matches are dropped. This keeps explosive rules
  /// (mostly associativity/commutativity) from starving the others. Zero
  /// disables backoff.
  unsigned RuleMatchLimit = 1000;
  unsigned RuleBanLength = 2;
  /// AC terms: maximum number of leaves of a flattened term and maximum
  /// number of views per class and operator.
  unsigned MaxACLeaves = 8;
  unsigned MaxACViews = 8;
};

/// Memoized AC views of a clean graph (valid until the graph changes).
class ACViewCache {
public:
  ACViewCache(const EGraph &G, unsigned MaxLeaves, unsigned MaxViews)
      : G(G), MaxLeaves(MaxLeaves), MaxViews(MaxViews) {}
  ArrayRef<ACView> get(EClassId C, unsigned Opc);
  /// Memoized EGraph::lookupACTerm.
  std::optional<EClassId> lookup(unsigned Opc, LLT Ty,
                                 ArrayRef<EClassId> Leaves);
  const EGraph &getGraph() const { return G; }

private:
  const EGraph &G;
  unsigned MaxLeaves, MaxViews;
  // std::map: references to cached views stay valid while new entries are
  // added (matching is recursive).
  std::map<std::pair<EClassId, unsigned>, SmallVector<ACView, 4>> Views;
  std::map<std::vector<EClassId>, std::optional<EClassId>> Terms;
};

struct SaturationStats {
  unsigned Iterations = 0;
  unsigned Matches = 0;
  unsigned Merges = 0;
  /// Merges made by AC canonicalization.
  unsigned ACMerges = 0;
  /// Merges made by EGraph::collapseIdempotentPhis.
  unsigned PhiMerges = 0;
  unsigned Refinements = 0;
  unsigned RejectedUnsafe = 0;
  bool Saturated = false;
  bool HitNodeLimit = false;
  bool HitIterationLimit = false;
  bool HitMatchLimit = false;
  /// Number of times a rule was banned by the backoff scheduler.
  unsigned Bans = 0;
  /// Number of matches applied per rule name (in rule order).
  SmallVector<unsigned, 32> RuleApplications;
};

/// Bounded equality saturation. Deterministic for a given graph and rule set.
SaturationStats saturate(EGraph &G, ArrayRef<RewriteRule> Rules,
                         const SaturationLimits &Limits);

//===----------------------------------------------------------------------===//
// Extraction
//===----------------------------------------------------------------------===//

/// Cost model for extraction. Targets may subclass this.
class CostModel {
public:
  virtual ~CostModel();
  /// Cost of a single node, not including operands. Operations must cost at
  /// least 1 so that extraction is cycle-free.
  virtual unsigned getNodeCost(const ENode &N) const;
  /// False if \p N must not be extracted, e.g. because the target cannot
  /// legalize it. The nodes of the original program must be allowed.
  virtual bool isAllowed(const EGraph &G, const ENode &N) const { return true; }
};

/// Simple configurable cost model (see the design document for rationale).
class DefaultCostModel : public CostModel {
public:
  unsigned ConstantCost = 0;
  unsigned InputCost = 0;
  unsigned SimpleOpCost = 1; // add/sub/and/or/xor/shifts, casts, compares...
  unsigned MulCost = 2;
  unsigned DivCost = 16; // division and remainder
  /// Multiply operation cost by ceil(width / 32) when set.
  bool ScaleByWidth = true;
  unsigned getNodeCost(const ENode &N) const override;
};

/// Tree-cost extractor with refinement-aware choices. Shared subexpressions
/// are counted once per use when choosing (tree cost) but getDagCost() counts
/// each class once.
class Extractor {
public:
  static constexpr uint64_t Infinite = ~uint64_t(0);

  Extractor(const EGraph &G, const CostModel &CM);

  uint64_t getTreeCost(EClassId Id) const;
  /// The class whose chosen node implements \p Id (following refinement
  /// edges chosen by the extractor).
  EClassId resolve(EClassId Id) const;
  /// The chosen node for \p Id (after resolve). Never null for a class with
  /// finite cost.
  const ENode *getChosenNode(EClassId Id) const;
  /// Sum of node costs of the distinct classes needed to compute \p Roots.
  uint64_t getDagCost(ArrayRef<EClassId> Roots) const;
  /// Print the chosen expression as an S-expression.
  void printExpr(
      raw_ostream &OS, EClassId Id,
      function_ref<void(raw_ostream &, unsigned)> PrintInput = nullptr) const;
  std::string getExprString(EClassId Id) const;

private:
  const EGraph &G;
  // The cost model is only used during construction; the local cost of each
  // chosen node is cached so that the extractor does not keep a reference to
  // the (possibly temporary) cost model.
  struct Choice {
    uint64_t Cost = Infinite;
    uint64_t LocalCost = 0; // cost of the chosen node without operands
    int NodeIdx = -1;       // index into class nodes
    EClassId RefTarget = 0; // valid if NodeIdx == -1 and Cost finite
  };
  std::vector<Choice> Choices; // indexed by canonical class id
};

} // namespace egraph
} // namespace llvm

#endif // LLVM_CODEGEN_GLOBALISEL_GIEGRAPH_H
