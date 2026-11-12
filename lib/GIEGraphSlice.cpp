//===- GIEGraphSlice.cpp - Bit slices in the e-graph ----------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// The bit-slice view of an integer class (see applySliceViews in
/// GIEGraph.h): the class as an extension of a range of bits of another
/// class,
///
///   C == E_W(S[Lo +: N])   with E a zero or a sign extension to W bits,
///
/// where S[Lo +: N] is the N-bit value of the bits [Lo, Lo + N) of S. A view
/// is found by composing the operators that select, move or extend bits:
/// shifts by constants, masks, truncations, extensions, bit-field extracts
/// and the parts of a concatenation. The direct forms of the slice (a
/// G_UBFX, a shift and a mask, ...) are added as ordinary nodes, and the
/// class is related to them through classifyLeafReads. See
/// docs/TargetAwareViews.md (Bit-slice view) for the forms, the bounds and
/// the definedness argument.
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GIEGraph.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/Support/MathExtras.h"
#include <functional>
#include <map>
#include <set>
#include <tuple>

using namespace llvm;
using namespace llvm::egraph;

namespace {

/// How a field is extended to the width of the value that contains it.
/// None: the field is the whole value.
enum class Ext : uint8_t { None, Zero, Sign };

/// The values that a slice is taken of: scalar integers. A vector is never
/// one wide integer.
bool isSliceType(LLT Ty) {
  return Ty.isValid() && Ty.isScalar() && !Ty.isFloat() &&
         Ty.getSizeInBits() > 0;
}

/// The widest value that a G_UBFX or G_SBFX form is made for. The legalizer
/// widens the types of a bit-field extract but cannot narrow them
/// (LegalizerHelper::narrowScalar has no case for it), so a form must not
/// need narrowing: an AMDGPU target takes values of up to 64 bits.
constexpr unsigned MaxBitFieldWidth = 64;

/// The operators that a step of a view goes through.
bool isSliceOperator(unsigned Opc) {
  using namespace TargetOpcode;
  switch (Opc) {
  case G_LSHR:
  case G_ASHR:
  case G_SHL:
  case G_AND:
  case G_OR:
  case G_XOR:
  case G_TRUNC:
  case G_ZEXT:
  case G_SEXT:
  case G_ANYEXT:
  case G_SEXT_INREG:
  case G_UBFX:
  case G_SBFX:
  case G_EXTRACT:
  case G_MERGE_VALUES:
  case G_UNMERGE_VALUES:
    return true;
  default:
    return false;
  }
}

/// One step of a view through one node of a class D: the field
/// D[Lo +: Width] is Fill(Src[SrcLo +: SrcWidth]) extended to Width bits.
struct Step {
  EClassId Src = 0;
  unsigned SrcLo = 0, SrcWidth = 0;
  /// How the bits of Src fill the field; None if they are all of it.
  Ext Fill = Ext::None;
  /// Classes that the node reads besides Src and that the field does not
  /// depend on: the other parts of a concatenation, an operand of a bitwise
  /// operator whose known bits select the field.
  SmallVector<EClassId, 2> Dropped;
  /// The node has poison-generating flags.
  bool Flagged = false;
  /// The known bits that select the field are context facts of the inputs.
  bool Context = false;
  /// The type of the amount operand of a shift or of the position operand
  /// of a bit-field extract (IsPosition), and the width of the value that
  /// it applies to (0 if none).
  LLT AmountTy;
  unsigned AmountWidth = 0;
  bool IsPosition = false;
};

/// A view of a class C of width W: C == E_W(Src[Lo +: Width]), with E None
/// iff Width == W, found through Steps nodes.
struct View {
  EClassId Src = 0;
  unsigned Lo = 0, Width = 0;
  Ext E = Ext::None;
  unsigned Steps = 0;
  /// The classes that the nodes of the view read and the forms do not.
  SmallVector<EClassId, 4> Dropped;
  /// A node of the view has poison-generating flags: the view only
  /// justifies a refinement.
  bool Flagged = false;
  /// The view needed context facts.
  bool Context = false;
  /// The types of the amounts of the shifts and of the positions of the
  /// bit-field extracts of the view, by the width of the value (the first
  /// one of each width).
  SmallVector<std::pair<unsigned, LLT>, 2> AmountTys, PositionTys;
};

/// Is \p A a better view than \p B? The deeper one; then one without
/// flags, without context facts, with fewer dropped classes. On a tie the
/// first one found is kept, so the result is deterministic.
bool isBetter(const View &A, const View &B) {
  return std::make_tuple(A.Steps, !A.Flagged, !A.Context,
                         -int(A.Dropped.size())) >
         std::make_tuple(B.Steps, !B.Flagged, !B.Context,
                         -int(B.Dropped.size()));
}

/// The extension of a view E_W(F) whose field has been rewritten as
/// F == Fill(F') with a field F' of fewer bits: E_W(Fill(F')) is
/// E'_W(F'), or nothing if it is not an extension of F'.
std::optional<Ext> composeExt(Ext E, Ext Fill) {
  switch (Fill) {
  case Ext::None:
    return E;
  case Ext::Zero:
    // The top bit of a zero extension of F' is 0, so a sign extension of
    // it is a zero extension too.
    return Ext::Zero;
  case Ext::Sign:
    // A zero extension of a sign extension of F' is neither.
    if (E == Ext::Zero)
      return std::nullopt;
    return Ext::Sign;
  }
  llvm_unreachable("bad extension");
}

/// The read phase: the deepest view of a class, by a depth-first search
/// over the nodes of the classes with memoization. A state (class, field,
/// extension) on the current path is not entered again, so cycles of
/// classes end the search.
class SliceAnalysis {
public:
  SliceAnalysis(const EGraph &G, const SaturationLimits &Limits)
      : G(G), Limits(Limits) {}

  enum class Outcome { None, Found, Budget };
  /// The view of \p C, if it composes at least two operators.
  Outcome viewOf(EClassId C, View &Out);

private:
  /// The field D[Lo +: Width], extended by E to the width of the class
  /// whose view is computed.
  using Key = std::tuple<EClassId, unsigned, unsigned, Ext>;

  const View &best(EClassId D, unsigned Lo, unsigned Width, Ext E);
  void stepsOf(const ENode &N, unsigned Lo, unsigned Width,
               SmallVectorImpl<Step> &Out) const;
  std::optional<uint64_t> getSmallConstant(EClassId Id) const {
    std::optional<APInt> C = G.getConstant(Id);
    if (!C || C->getActiveBits() > 32)
      return std::nullopt;
    return C->getZExtValue();
  }

  const EGraph &G;
  const SaturationLimits &Limits;
  std::map<Key, View> Memo;
  std::set<Key> OnPath;
  unsigned Visits = 0;
  bool OverBudget = false;
};

void SliceAnalysis::stepsOf(const ENode &N, unsigned Lo, unsigned Width,
                            SmallVectorImpl<Step> &Out) const {
  using namespace TargetOpcode;
  if (!N.isOperation() || !isSliceOperator(N.Opcode) || !isSliceType(N.Ty))
    return;
  const unsigned WD = N.Ty.getSizeInBits();
  const bool Flagged = N.Flags != 0;
  auto MakeStep = [&](EClassId Src, unsigned SrcLo, unsigned SrcWidth,
                      Ext Fill) {
    Step S;
    S.Src = Src;
    S.SrcLo = SrcLo;
    S.SrcWidth = SrcWidth;
    S.Fill = SrcWidth == Width ? Ext::None : Fill;
    S.Flagged = Flagged;
    return S;
  };
  // D[i] == Src[Off + i] for i < Avail; for Avail <= i < WD, D[i] is 0
  // (Fill Zero), the sign bit Src[Off + Avail - 1] (Fill Sign) or not
  // specified (Fill None: such a bit must not be in the field).
  auto Through = [&](EClassId Src, uint64_t Off, uint64_t Avail,
                     Ext Fill) -> std::optional<Step> {
    LLT SrcTy = G.getType(Src);
    if (!isSliceType(SrcTy) || Avail == 0 ||
        Off + Avail > SrcTy.getSizeInBits())
      return std::nullopt;
    if (Lo + Width <= Avail)
      return MakeStep(Src, Off + Lo, Width, Ext::None);
    if (Fill == Ext::None)
      return std::nullopt;
    if (Lo < Avail)
      return MakeStep(Src, Off + Lo, Avail - Lo, Fill);
    // A field of zeros is a constant, not a slice. A field of sign bits is
    // the extension of the sign bit.
    if (Fill == Ext::Zero)
      return std::nullopt;
    return MakeStep(Src, Off + Avail - 1, 1, Ext::Sign);
  };
  auto Push = [&](std::optional<Step> S, std::optional<EClassId> Amount) {
    if (!S)
      return;
    if (Amount) {
      S->AmountTy = G.getType(*Amount);
      S->AmountWidth = WD;
      S->IsPosition = N.Opcode == G_UBFX || N.Opcode == G_SBFX;
    }
    Out.push_back(std::move(*S));
  };

  switch (N.Opcode) {
  case G_LSHR:
  case G_ASHR:
  case G_SHL: {
    // A shift by a constant inside the width; a larger amount is poison.
    std::optional<uint64_t> Amt = getSmallConstant(N.Ops[1]);
    if (!Amt || *Amt >= WD)
      return;
    if (N.Opcode == G_LSHR)
      Push(Through(N.Ops[0], *Amt, WD - *Amt, Ext::Zero), N.Ops[1]);
    else if (N.Opcode == G_ASHR)
      Push(Through(N.Ops[0], *Amt, WD - *Amt, Ext::Sign), N.Ops[1]);
    else if (Lo >= *Amt && isSliceType(G.getType(N.Ops[0])))
      // The field lies above the zeros that the shift brings in.
      Push(MakeStep(N.Ops[0], Lo - *Amt, Width, Ext::None), N.Ops[1]);
    return;
  }
  case G_AND:
  case G_OR:
  case G_XOR: {
    // An operand X selects the field of the other operand Y by its known
    // bits: an AND keeps the low bits of the field where X is one and
    // clears the bits above, where X is zero; an OR and an XOR keep the
    // field of Y if X is zero in it. A constant is an operand whose bits
    // are all known. The facts of the structure are tried first; the
    // context facts of the inputs belong to the facts feature.
    for (unsigned I = 0; I != 2; ++I) {
      EClassId X = N.Ops[I], Y = N.Ops[1 - I];
      if (!isSliceType(G.getType(Y)))
        continue;
      for (FactSource Src : {FactSource::Structure, FactSource::Context}) {
        if (Src == FactSource::Context && !Limits.EnableFacts)
          break;
        const KnownBits &K = G.getKnownBits(X, Src);
        if (K.getBitWidth() != WD)
          break;
        APInt Zero = K.Zero.extractBits(Width, Lo);
        unsigned Keep = 0;
        if (N.Opcode == G_AND) {
          unsigned Ones = K.One.extractBits(Width, Lo).countr_one();
          if (Ones && (Zero | APInt::getLowBitsSet(Width, Ones)).isAllOnes())
            Keep = Ones;
        } else if (Zero.isAllOnes()) {
          Keep = Width;
        }
        if (!Keep)
          continue;
        Step S = MakeStep(Y, Lo, Keep, Ext::Zero);
        if (!G.getConstant(X))
          S.Dropped.push_back(X);
        S.Context = Src == FactSource::Context;
        Push(std::move(S), std::nullopt);
        break;
      }
    }
    return;
  }
  case G_TRUNC:
  case G_ZEXT:
  case G_SEXT:
  case G_ANYEXT: {
    EClassId Src = N.Ops[0];
    if (!isSliceType(G.getType(Src)))
      return;
    unsigned WS = G.getType(Src).getSizeInBits();
    if (N.Opcode == G_TRUNC) {
      if (WS > WD)
        Push(Through(Src, 0, WD, Ext::None), std::nullopt);
      return;
    }
    if (WS >= WD)
      return;
    // The high bits of G_ANYEXT are not specified: a field must not
    // contain them.
    Ext Fill = N.Opcode == G_ZEXT   ? Ext::Zero
               : N.Opcode == G_SEXT ? Ext::Sign
                                    : Ext::None;
    Push(Through(Src, 0, WS, Fill), std::nullopt);
    return;
  }
  case G_SEXT_INREG:
    // The sign extension of the low Attr bits.
    if (N.Attr >= 1 && N.Attr <= WD)
      Push(Through(N.Ops[0], 0, N.Attr, Ext::Sign), std::nullopt);
    return;
  case G_UBFX:
  case G_SBFX: {
    // Poison unless the position and the width are constants that select
    // bits inside the value.
    std::optional<uint64_t> Pos = getSmallConstant(N.Ops[1]);
    std::optional<uint64_t> Len = getSmallConstant(N.Ops[2]);
    if (!Pos || !Len || *Len == 0 || *Pos + *Len > WD)
      return;
    Push(Through(N.Ops[0], *Pos, *Len,
                 N.Opcode == G_UBFX ? Ext::Zero : Ext::Sign),
         N.Ops[1]);
    return;
  }
  case G_EXTRACT:
    // The bits [Attr, Attr + WD) of the operand.
    Push(Through(N.Ops[0], N.Attr, WD, Ext::None), std::nullopt);
    return;
  case G_UNMERGE_VALUES:
    // Result Attr of the division of the operand into parts of WD bits.
    Push(Through(N.Ops[0], N.Attr * WD, WD, Ext::None), std::nullopt);
    return;
  case G_MERGE_VALUES: {
    // Parts of one type, least significant first. A field inside one part
    // is a field of that part; the other parts are dropped.
    if (N.Ops.empty() || !isSliceType(G.getType(N.Ops[0])))
      return;
    unsigned Part = G.getType(N.Ops[0]).getSizeInBits();
    if (Part * N.Ops.size() != WD)
      return;
    unsigned Idx = Lo / Part;
    if ((Lo + Width - 1) / Part != Idx)
      return;
    Step S = MakeStep(N.Ops[Idx], Lo - Idx * Part, Width, Ext::None);
    for (unsigned I = 0, E = N.Ops.size(); I != E; ++I)
      if (I != Idx && !G.getConstant(N.Ops[I]))
        S.Dropped.push_back(N.Ops[I]);
    Push(std::move(S), std::nullopt);
    return;
  }
  default:
    return;
  }
}

const View &SliceAnalysis::best(EClassId D, unsigned Lo, unsigned Width,
                                Ext E) {
  D = G.find(D);
  Key K{D, Lo, Width, E};
  auto It = Memo.find(K);
  if (It != Memo.end())
    return It->second;
  // Without a step, the view is the field itself.
  View Result;
  Result.Src = D;
  Result.Lo = Lo;
  Result.Width = Width;
  Result.E = E;
  OnPath.insert(K);
  for (const ENode &N : G.getClass(D).Nodes) {
    if (OverBudget)
      break;
    if (++Visits > Limits.MaxViewVisits) {
      OverBudget = true;
      break;
    }
    SmallVector<Step, 2> Steps;
    stepsOf(N, Lo, Width, Steps);
    for (Step &S : Steps) {
      std::optional<Ext> NextE = composeExt(E, S.Fill);
      if (!NextE || OnPath.count({G.find(S.Src), S.SrcLo, S.SrcWidth, *NextE}))
        continue;
      View V = best(S.Src, S.SrcLo, S.SrcWidth, *NextE);
      if (OverBudget)
        break;
      ++V.Steps;
      V.Dropped.append(S.Dropped.begin(), S.Dropped.end());
      V.Flagged |= S.Flagged;
      V.Context |= S.Context;
      auto &Tys = S.IsPosition ? V.PositionTys : V.AmountTys;
      if (S.AmountWidth &&
          none_of(Tys, [&](const auto &P) { return P.first == S.AmountWidth; }))
        Tys.push_back({S.AmountWidth, S.AmountTy});
      if (isBetter(V, Result))
        Result = std::move(V);
    }
  }
  OnPath.erase(K);
  return Memo[K] = std::move(Result);
}

SliceAnalysis::Outcome SliceAnalysis::viewOf(EClassId C, View &Out) {
  C = G.find(C);
  const EClass &Cls = G.getClass(C);
  if (!isSliceType(Cls.Ty) || Cls.Const ||
      none_of(Cls.Nodes, [](const ENode &N) {
        return N.isOperation() && isSliceOperator(N.Opcode);
      }))
    return Outcome::None;
  Memo.clear();
  OnPath.clear();
  Visits = 0;
  OverBudget = false;
  View V = best(C, 0, Cls.Ty.getSizeInBits(), Ext::None);
  if (OverBudget)
    return Outcome::Budget;
  // Only a composition of operators is new: a single operator is the node
  // itself, and the table rules relate it to its other forms.
  if (V.Steps < 2 || G.find(V.Src) == C || G.getConstant(V.Src))
    return Outcome::None;
  if (1 + V.Dropped.size() > Limits.MaxViewTerms)
    return Outcome::Budget;
  Out = std::move(V);
  return Outcome::Found;
}

//===----------------------------------------------------------------------===//
// The direct forms of a view
//===----------------------------------------------------------------------===//

/// Builds the nodes of a form (the write phase), or only looks them up (the
/// read phase: does the graph have the form already?).
class FormBuilder {
public:
  using Value = std::optional<EClassId>;

  /// Adds the nodes of a form to \p G.
  FormBuilder(EGraph &G, const View &V) : MG(&G), G(G), V(V) {}
  /// Looks the nodes of a form up in the clean graph \p G.
  FormBuilder(const EGraph &G, const View &V) : G(G), V(V) {}

  Value cast(unsigned Opc, LLT Ty, Value X) {
    if (!X)
      return std::nullopt;
    return add(ENode::makeOp(Opc, Ty, {*X}));
  }
  Value shift(unsigned Opc, Value X, unsigned Amount) {
    if (!X)
      return std::nullopt;
    LLT Ty = G.getType(*X);
    return binary(Opc, Ty, *X, constant(amountType(Ty), Amount));
  }
  /// X & (2^Bits - 1).
  Value andLow(Value X, unsigned Bits) {
    if (!X)
      return std::nullopt;
    LLT Ty = G.getType(*X);
    return binary(TargetOpcode::G_AND, Ty, *X,
                  add(ENode::makeConstant(
                      Ty, APInt::getLowBitsSet(Ty.getSizeInBits(), Bits))));
  }
  /// A G_UBFX or G_SBFX of the bits [Lo, Lo + Width) of X.
  Value bitField(unsigned Opc, Value X, unsigned Lo, unsigned Width) {
    if (!X)
      return std::nullopt;
    LLT Ty = G.getType(*X);
    assert(Ty.getSizeInBits() <= MaxBitFieldWidth && "too wide a bit field");
    LLT ATy = positionType(Ty);
    Value Pos = constant(ATy, Lo), Len = constant(ATy, Width);
    if (!Pos || !Len)
      return std::nullopt;
    return add(ENode::makeOp(Opc, Ty, {*X, *Pos, *Len}));
  }
  Value sextInReg(Value X, unsigned Bits) {
    if (!X)
      return std::nullopt;
    return add(ENode::makeOp(TargetOpcode::G_SEXT_INREG, G.getType(*X), {*X},
                             /*Flags=*/0, Bits));
  }

private:
  Value add(const ENode &N) { return MG ? Value(MG->add(N)) : G.lookup(N); }
  Value constant(LLT Ty, uint64_t Val) {
    return add(ENode::makeConstant(Ty, APInt(Ty.getSizeInBits(), Val)));
  }
  Value binary(unsigned Opc, LLT Ty, EClassId X, Value Y) {
    if (!Y)
      return std::nullopt;
    return add(ENode::makeOp(Opc, Ty, {X, *Y}));
  }
  /// The type of the amount of a shift of a value of type \p Ty: the type
  /// that the shifts of the view use for this width (so that a target that
  /// wants s32 amounts for s64 shifts gets them), else \p Ty (the type
  /// that an amount has in the IR; the legalizer adapts it).
  LLT amountType(LLT Ty) const { return find(V.AmountTys, Ty, Ty); }
  /// The type of the position and the width of a bit-field extract of a
  /// value of type \p Ty: the type that the bit-field extracts of the view
  /// use for this width, else \p Ty, but at most 32 bits: the legalizer
  /// cannot narrow it, and 32 bits is what targets with a bit-field extract
  /// of 64-bit values take (AMDGPU).
  LLT positionType(LLT Ty) const {
    return find(V.PositionTys, Ty,
                Ty.getSizeInBits() > 32 ? Ty.changeElementSize(32) : Ty);
  }
  /// The type recorded in \p Tys for the width of \p Ty, if it holds the
  /// number of bits of \p Ty, else \p Default.
  static LLT find(ArrayRef<std::pair<unsigned, LLT>> Tys, LLT Ty, LLT Default) {
    unsigned W = Ty.getSizeInBits();
    for (const auto &[Width, ATy] : Tys)
      if (Width == W && isSliceType(ATy) && isUIntN(ATy.getSizeInBits(), W))
        return ATy;
    return Default;
  }

  EGraph *MG = nullptr;
  const EGraph &G;
  const View &V;
};

using Form = std::function<FormBuilder::Value(FormBuilder &)>;

/// The forms of E(B[Lo +: N]) in the type of B (\p W bits). The bits of B
/// above \p Top are zero (E Zero) or copies of bit Top - 1 (E Sign); Top is
/// W if there are none.
void addSameWidthForms(const Form &B, unsigned W, unsigned Top, unsigned Lo,
                       unsigned N, Ext E, SmallVectorImpl<Form> &Out) {
  using namespace TargetOpcode;
  const bool BitField = W <= MaxBitFieldWidth;
  if (E == Ext::None || (Lo == 0 && N == Top)) {
    Out.push_back(B);
    return;
  }
  if (E == Ext::Zero) {
    if (Lo + N == Top) {
      Out.push_back([=](FormBuilder &F) { return F.shift(G_LSHR, B(F), Lo); });
    } else if (Lo == 0) {
      Out.push_back([=](FormBuilder &F) { return F.andLow(B(F), N); });
    } else {
      if (BitField)
        Out.push_back(
            [=](FormBuilder &F) { return F.bitField(G_UBFX, B(F), Lo, N); });
      Out.push_back([=](FormBuilder &F) {
        return F.andLow(F.shift(G_LSHR, B(F), Lo), N);
      });
    }
    return;
  }
  if (Lo + N == Top) {
    Out.push_back([=](FormBuilder &F) { return F.shift(G_ASHR, B(F), Lo); });
  } else if (Lo == 0) {
    Out.push_back([=](FormBuilder &F) { return F.sextInReg(B(F), N); });
  } else {
    if (BitField)
      Out.push_back(
          [=](FormBuilder &F) { return F.bitField(G_SBFX, B(F), Lo, N); });
    Out.push_back([=](FormBuilder &F) {
      return F.sextInReg(F.shift(G_LSHR, B(F), Lo), N);
    });
  }
}

/// The forms of the view \p V of a class of type \p Ty, the most direct
/// first.
void getForms(const EGraph &G, const View &V, LLT Ty,
              SmallVectorImpl<Form> &Out) {
  using namespace TargetOpcode;
  const EClassId Src = V.Src;
  const LLT SrcTy = G.getType(Src);
  const unsigned W = Ty.getSizeInBits(), WS = SrcTy.getSizeInBits();
  const unsigned Lo = V.Lo, N = V.Width;
  const Ext E = V.E;
  const Form S = [Src](FormBuilder &) { return FormBuilder::Value(Src); };
  if (W == WS) {
    addSameWidthForms(S, W, W, Lo, N, E, Out);
    return;
  }
  if (W < WS) {
    if (Lo + N <= W) {
      // The field is inside the low W bits of S: truncate first.
      Form T = [=](FormBuilder &F) { return F.cast(G_TRUNC, Ty, S(F)); };
      addSameWidthForms(T, W, W, Lo, N, E, Out);
      return;
    }
    // The field reaches above bit W of S: shift it down first.
    if (E == Ext::None || Lo + N == WS) {
      unsigned Opc = E == Ext::Sign ? G_ASHR : G_LSHR;
      Out.push_back([=](FormBuilder &F) {
        return F.cast(G_TRUNC, Ty, F.shift(Opc, S(F), Lo));
      });
      return;
    }
    const bool BitField = WS <= MaxBitFieldWidth;
    if (E == Ext::Zero) {
      if (BitField)
        Out.push_back([=](FormBuilder &F) {
          return F.cast(G_TRUNC, Ty, F.bitField(G_UBFX, S(F), Lo, N));
        });
      Out.push_back([=](FormBuilder &F) {
        return F.andLow(F.cast(G_TRUNC, Ty, F.shift(G_LSHR, S(F), Lo)), N);
      });
      return;
    }
    if (BitField)
      Out.push_back([=](FormBuilder &F) {
        return F.cast(G_TRUNC, Ty, F.bitField(G_SBFX, S(F), Lo, N));
      });
    Out.push_back([=](FormBuilder &F) {
      return F.sextInReg(F.cast(G_TRUNC, Ty, F.shift(G_LSHR, S(F), Lo)), N);
    });
    return;
  }
  // W > WS: the field is extended (N <= WS < W). Extend S first; then also
  // extend the field taken in the type of S.
  assert(E != Ext::None && "a field of a narrower value is extended");
  const unsigned ExtOpc = E == Ext::Sign ? G_SEXT : G_ZEXT;
  Form B = [=](FormBuilder &F) { return F.cast(ExtOpc, Ty, S(F)); };
  addSameWidthForms(B, W, WS, Lo, N, E, Out);
  if (N < WS) {
    SmallVector<Form, 2> Narrow;
    addSameWidthForms(S, WS, WS, Lo, N, E, Narrow);
    Form First = Narrow.front();
    Out.push_back([=](FormBuilder &F) { return F.cast(ExtOpc, Ty, First(F)); });
  }
}

/// The relation that the view justifies between the class and a form. On
/// values that are neither undef nor poison both are E_W(Src[Lo +: N]).
/// The nodes of the view read Src once and each dropped class once; each
/// form reads Src once. No operator of either side has undefined behaviour
/// or poison of its own (shifts and bit fields are inside the width), so
/// each side is poison iff a class that it reads is.
RewriteKind classifyView(const EGraph &G, const View &V) {
  SmallVector<LeafReads, 4> Leaves;
  Leaves.push_back({V.Src, 1, 1});
  for (EClassId D : V.Dropped)
    Leaves.push_back({D, 1, 0});
  RewriteKind K = classifyLeafReads(G, Leaves);
  // A node with a poison-generating flag is refined by the node without
  // the flag, never equal to it.
  if (V.Flagged && K == RewriteKind::Exact)
    K = RewriteKind::Refinement;
  return K;
}

struct Todo {
  EClassId Class;
  View V;
};

} // end anonymous namespace

unsigned llvm::egraph::applySliceViews(EGraph &G,
                                       const SaturationLimits &Limits,
                                       ViewStats &Stats) {
  // Read phase: the views of the classes, on the unchanged graph, in
  // increasing class id.
  SmallVector<Todo, 16> Work;
  {
    const EGraph &CG = G;
    SliceAnalysis A(CG, Limits);
    for (EClassId C : CG.getClassIds()) {
      const EClass &Cls = CG.getClass(C);
      if (Cls.Ty.isValid() && Cls.Ty.isVector()) {
        // The bits of a vector are lanes, never one wide integer.
        if (any_of(Cls.Nodes, [](const ENode &N) {
              return N.isOperation() && isSliceOperator(N.Opcode);
            }))
          ++Stats.Unsupported;
        continue;
      }
      View V;
      switch (A.viewOf(C, V)) {
      case SliceAnalysis::Outcome::None:
        continue;
      case SliceAnalysis::Outcome::Budget:
        ++Stats.Budget;
        continue;
      case SliceAnalysis::Outcome::Found:
        break;
      }
      // Nothing to do if the class already has, or refines to, every form
      // that the view would add.
      SmallVector<Form, 4> Forms;
      getForms(CG, V, Cls.Ty, Forms);
      FormBuilder Lookup(CG, V);
      size_t Num = std::min<size_t>(Forms.size(), Limits.MaxViewCandidates);
      if (all_of(ArrayRef<Form>(Forms).take_front(Num), [&](const Form &F) {
            FormBuilder::Value X = F(Lookup);
            return X && CG.refinesTo(C, *X);
          }))
        continue;
      Work.push_back({C, std::move(V)});
    }
  }

  // Write phase: add the forms and relate the class to them.
  unsigned Changes = 0;
  unsigned NodesBefore = G.getNumNodes();
  for (const Todo &T : Work) {
    if (G.getNumNodes() >= Limits.MaxNodes) {
      ++Stats.Budget;
      break;
    }
    ++Stats.Views;
    LLT Ty = G.getType(T.Class);
    SmallVector<Form, 4> Forms;
    getForms(G, T.V, Ty, Forms);
    if (Forms.size() > Limits.MaxViewCandidates) {
      ++Stats.Budget;
      Forms.truncate(Limits.MaxViewCandidates);
    }
    RewriteKind K = classifyView(G, T.V);
    FormBuilder Build(G, T.V);
    for (const Form &F : Forms) {
      if (G.getNumNodes() >= Limits.MaxNodes) {
        ++Stats.Budget;
        break;
      }
      FormBuilder::Value X = F(Build);
      if (!X || G.getType(*X) != Ty || G.refinesTo(T.Class, *X))
        continue;
      ++Stats.Candidates;
      ApplyResult R = relateClasses(G, T.Class, *X, K);
      Stats.count(R);
      if (R == ApplyResult::Merged || R == ApplyResult::Refined) {
        ++Changes;
        if (T.V.Context)
          ++Stats.ContextFacts;
      }
    }
  }
  return Changes + (G.getNumNodes() - NodesBefore);
}
