//===- GIEGraphTargetAMDGPU.cpp - AMDGPU costs of the e-graph combiner ----===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// The AMDGPU model of TargetCosts (GIEGraphTargetCosts.h): the three-operand
/// VALU instructions that instruction selection forms from two generic
/// operations (the ThreeOp family of VOP3Instructions.td), the bank of a
/// value (SGPR for a uniform value, VGPR otherwise) and the size of the
/// encodings.
///
/// The pass emits generic MIR; the instruction selector forms the fused
/// instruction later. So a cover is credited exactly when the selector of
/// the pinned LLVM revision forms it, and with the copies that it then
/// needs:
///  * the subtarget has the instruction (the feature of its predicate);
///  * the outer operation is divergent (VGPR result; ThreeOp_i32_Pats
///    produce a VGPR_32). A uniform outer operation is selected as SALU
///    instructions and gets no credit (SALU fusions such as s_lshl2_add_u32
///    are not modelled);
///  * the inner operation is read once (HasOneUseBinOp) and is not a root;
///  * the inner operation is divergent. A uniform inner operation is in an
///    SGPR and register bank legalization copies it to a VGPR for the
///    divergent outer operation; the selector does not look through that
///    copy, except for the outer operator cshl_32 (GIIgnoreCopies), where it
///    does and then the GISel predicate of ThreeOpFrag counts the SGPR-bank
///    sources (the two operands of the uniform inner operation) against the
///    constant bus limit (1 before GFX10, 2 from GFX10 on);
///  * for a divergent inner operation, register bank legalization copies
///    every uniform source to a VGPR, so the ThreeOpFrag predicate always
///    holds. SIFoldOperands then folds SGPR sources and constants back into
///    the instruction as far as the constant bus allows (an inline constant
///    is free; a literal needs a VOP3 literal, which exists from GFX10 on
///    and uses the constant bus); every source that it cannot fold stays a
///    v_mov_b32, which the cover counts.
/// This reproduces the measured selection of every combination of VGPR,
/// SGPR, inline and literal sources for each pattern on gfx803, gfx900 and
/// gfx1100 (see docs/TargetAwareViews.md).
///
/// Before register bank selection the bank of a value is a prediction: the
/// pass computes the uniformity analysis (MachineUniformityInfo) and AMDGPU
/// register bank selection of this revision (AMDGPURegBankSelect) puts a
/// value in an SGPR exactly when the analysis finds it uniform. The plugin
/// has no AMDGPU headers: instructions are found by name through
/// TargetInstrInfo and subtarget features by name through MCSubtargetInfo.
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GIEGraphTargetCosts.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/RegisterBank.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"

using namespace llvm;
using namespace llvm::egraph;
using namespace llvm::TargetOpcode;

TargetCosts::~TargetCosts() = default;

namespace {

/// An instruction of the ThreeOp family: Outer(Inner(x0, x1), x2) as one
/// instruction with the sources (x0, x1, x2). From VOP3Instructions.td at the
/// pinned revision: ThreeOp_i32_Pats (ThreeOpFrag<op1, op2>) and IMAD32_Pats.
struct ThreeOpPattern {
  unsigned Outer;
  unsigned Inner;
  /// The pseudo instruction (its MCInstrInfo name).
  const char *Name;
  /// The subtarget feature of the predicate of the instruction, and a
  /// feature that disables the pattern (or null).
  const char *Feature;
  const char *DisabledBy;
  /// The outer operator is cshl_32, whose operands are matched through
  /// copies (GIIgnoreCopies in AMDGPUInstructions.td).
  bool LooksThroughCopies;
  /// IMAD32_Pats (V_MAD_U64_U32 with a 64-bit addend): one instruction only
  /// for an addend in a VGPR and sources without a literal (measured).
  bool AddendInVGPR;
  /// The latency estimate (a proxy).
  unsigned Latency;
};

/// In the order in which the selector prefers them when several match at one
/// operation (measured): the higher AddedComplexity first, then, for equal
/// complexity, the pattern defined later in VOP3Instructions.td first (e.g.
/// add(xor, add) becomes v_xad_u32 and add(add, shl) becomes v_add3_u32).
const ThreeOpPattern ThreeOpPatterns[] = {
    // HasMadU32Inst, AddedComplexity = 10.
    {G_ADD, G_MUL, "V_MAD_U32_e64", "mad-u32-inst", nullptr, false, false, 4},
    // IMAD32_Pats<V_MAD_U64_U32_e64>: isGFX9Plus and NotHasMADIntraFwdBug.
    // (With the bug, GFX11 selects V_MAD_U64_U32_gfx11_e64 and a move;
    // that variant is not modelled.)
    {G_ADD, G_MUL, "V_MAD_U64_U32_e64", "gfx9-insts", "mad-intra-fwd-bug",
     false, true, 4},
    // isGFX10Plus.
    {G_XOR, G_XOR, "V_XOR3_B32_e64", "gfx10-insts", nullptr, false, false, 1},
    // ThreeOp_i32_Pats in the isGFX9Plus block, latest definition first.
    {G_ADD, G_XOR, "V_XAD_U32_e64", "gfx9-insts", nullptr, false, false, 1},
    {G_OR, G_OR, "V_OR3_B32_e64", "gfx9-insts", nullptr, false, false, 1},
    {G_OR, G_AND, "V_AND_OR_B32_e64", "gfx9-insts", nullptr, false, false, 1},
    {G_OR, G_SHL, "V_LSHL_OR_B32_e64", "gfx9-insts", nullptr, false, false, 1},
    {G_PTR_ADD, G_PTR_ADD, "V_ADD3_U32_e64", "gfx9-insts", nullptr, false,
     false, 1},
    {G_ADD, G_ADD, "V_ADD3_U32_e64", "gfx9-insts", nullptr, false, false, 1},
    {G_SHL, G_ADD, "V_ADD_LSHL_U32_e64", "gfx9-insts", nullptr, true, false, 1},
    {G_ADD, G_SHL, "V_LSHL_ADD_U32_e64", "gfx9-insts", nullptr, false, false,
     1},
    // HasAddMinMaxInsts.
    {G_SMAX, G_SADDSAT, "V_ADD_MAX_I32_e64", "add-min-max-insts", nullptr,
     false, false, 1},
    {G_UMAX, G_UADDSAT, "V_ADD_MAX_U32_e64", "add-min-max-insts", nullptr,
     false, false, 1},
    {G_SMIN, G_SADDSAT, "V_ADD_MIN_I32_e64", "add-min-max-insts", nullptr,
     false, false, 1},
    {G_UMIN, G_UADDSAT, "V_ADD_MIN_U32_e64", "add-min-max-insts", nullptr,
     false, false, 1},
};

/// The opcodes of the instructions of ThreeOpPatterns, by name. The opcode
/// table is the same for every AMDGPU subtarget, so it is read once.
const StringMap<unsigned> &getOpcodesByName(const TargetInstrInfo &TII) {
  static const StringMap<unsigned> Map = [&] {
    StringMap<unsigned> M;
    for (const ThreeOpPattern &P : ThreeOpPatterns)
      M.try_emplace(P.Name, 0);
    for (unsigned Opc = 0, E = TII.getNumOpcodes(); Opc != E; ++Opc) {
      auto It = M.find(TII.getName(Opc));
      if (It != M.end())
        It->second = Opc;
    }
    return M;
  }();
  return Map;
}

/// A source of an instruction: a VGPR value, an SGPR value, an inline
/// constant or a literal constant.
enum class SrcKind { VGPR, SGPR, Inline, Literal };

/// The operators with a 4-byte VALU encoding (VOP1, VOP2, VOPC) for 32 bits.
bool hasShortVALUEncoding(unsigned Opc) {
  switch (Opc) {
  case G_ADD:
  case G_SUB:
  case G_AND:
  case G_OR:
  case G_XOR:
  case G_SHL:
  case G_LSHR:
  case G_ASHR:
  case G_SMIN:
  case G_SMAX:
  case G_UMIN:
  case G_UMAX:
  case G_ICMP:
  case G_SELECT:
  case G_UADDO:
  case G_USUBO:
  case G_UADDE:
  case G_USUBE:
  case G_BITREVERSE:
    return true;
  default:
    return false;
  }
}

/// The operators that only have a VOP3 encoding (8 bytes) for 32 bits.
bool hasOnlyVOP3Encoding(unsigned Opc) {
  switch (Opc) {
  case G_MUL:
  case G_UMULH:
  case G_SMULH:
  case G_UBFX:
  case G_SBFX:
  case G_CTPOP:
  case G_FSHL:
  case G_FSHR:
    return true;
  default:
    return false;
  }
}

class AMDGPUTargetCosts : public TargetCosts {
public:
  AMDGPUTargetCosts(const MachineFunction &MF, bool IsLegalized,
                    bool IsRegBankSelected)
      : IsLegalized(IsLegalized), IsRegBankSelected(IsRegBankSelected) {
    const TargetSubtargetInfo &ST = MF.getSubtarget();
    CPU = ST.getCPU().str();
    auto Has = [&](const char *Feature) {
      return ST.checkFeatures((Twine("+") + Feature).str());
    };
    HasGFX10Insts = Has("gfx10-insts");
    HasRealTrue16 = Has("real-true16");
    // ThreeOpFrag: Subtarget->getConstantBusLimit(V_ADD3_U32_e64), which is
    // 1 before GFX10 and 2 from GFX10 on for these instructions.
    ConstantBusLimit = HasGFX10Insts ? 2 : 1;
    // A VOP3 instruction can encode a literal from GFX10 on.
    VOP3Literal = HasGFX10Insts;
    Inv2PiInline = Has("inv-2pi-inline-imm");
    const StringMap<unsigned> &Opcodes = getOpcodesByName(*ST.getInstrInfo());
    for (const ThreeOpPattern &P : ThreeOpPatterns)
      if (Opcodes.lookup(P.Name) && Has(P.Feature) &&
          !(P.DisabledBy && Has(P.DisabledBy)))
        Available.push_back(&P);
  }

  bool hasUniformBank() const override { return true; }

  bool isUniformBank(const RegisterBank &RB) const override {
    return RB.getName() == StringRef("SGPR");
  }

  CostVector getItemCost(const EGraph &G, const CostDag &D, unsigned I,
                         const CostVector &Default) const override;
  void findCovers(const EGraph &G, const CostDag &D,
                  SmallVectorImpl<PatternCover> &Covers) const override;
  // After the legalizer, with true 16-bit registers (gfx11 and later), a
  // new 16-bit scalar operation is not created: on permute_i8.ll
  // (zext_store_div, gfx1100) a rewrite that truncated a shared 32-bit
  // value into a lane of a <2 x i16> build was valid generic MIR, verified
  // after the pass, but the registers of the 16-bit lanes were corrupted
  // after register allocation ("Using an undefined physical register" in a
  // V_PERM_B32). The instructions of the region itself stay allowed.
  bool restrictsNewNode(const EGraph &G, const ENode &N) const override {
    return IsLegalized && HasRealTrue16 && N.isOperation() &&
           N.Ty.isValid() && !N.Ty.isVector() && N.Ty.getSizeInBits() == 16;
  }

  void describe(raw_ostream &OS) const override;

private:
  bool isInlineConstant(const APInt &V) const;
  SrcKind getKind(const CostDag &D, unsigned I) const;
  std::optional<PatternCover> matchCover(const CostDag &D, unsigned Root,
                                         unsigned Pos,
                                         const ThreeOpPattern &P) const;

  bool IsLegalized, IsRegBankSelected;
  std::string CPU;
  bool HasGFX10Insts = false;
  bool HasRealTrue16 = false;
  unsigned ConstantBusLimit = 1;
  bool VOP3Literal = false;
  bool Inv2PiInline = false;
  SmallVector<const ThreeOpPattern *, 16> Available;
};

/// A 32-bit scalar integer, or a 32-bit pointer.
bool is32Bit(LLT Ty) {
  return Ty.isValid() && !Ty.isVector() && Ty.getSizeInBits() == 32 &&
         !Ty.isFloat();
}

/// A 64-bit scalar integer.
bool is64BitInt(LLT Ty) {
  return Ty.isValid() && Ty.isScalar() && Ty.getSizeInBits() == 64 &&
         !Ty.isFloat();
}

/// An integer inline constant of a 64-bit operand.
bool isInlineConstant64(const APInt &V) {
  if (V.getBitWidth() > 64)
    return false;
  int64_t S = V.getSExtValue();
  return S >= -16 && S <= 64;
}

bool AMDGPUTargetCosts::isInlineConstant(const APInt &V) const {
  if (V.getBitWidth() != 32)
    return false;
  int64_t S = V.getSExtValue();
  if (S >= -16 && S <= 64)
    return true;
  // The floating-point inline constants, as 32-bit patterns: +-0.5, +-1.0,
  // +-2.0, +-4.0 and 1/(2*pi).
  switch (V.getZExtValue()) {
  case 0x3f000000:
  case 0xbf000000:
  case 0x3f800000:
  case 0xbf800000:
  case 0x40000000:
  case 0xc0000000:
  case 0x40800000:
  case 0xc0800000:
    return true;
  case 0x3e22f983:
    return Inv2PiInline;
  default:
    return false;
  }
}

SrcKind AMDGPUTargetCosts::getKind(const CostDag &D, unsigned I) const {
  const CostDag::Item &It = D.Items[I];
  if (It.N->isConstant())
    return isInlineConstant(It.N->Imm) ? SrcKind::Inline : SrcKind::Literal;
  // Without bank states every value counts as divergent.
  return It.Bank == BankState::Uniform ? SrcKind::SGPR : SrcKind::VGPR;
}

CostVector AMDGPUTargetCosts::getItemCost(const EGraph &G, const CostDag &D,
                                          unsigned I,
                                          const CostVector &Default) const {
  const CostDag::Item &It = D.Items[I];
  const ENode &N = *It.N;
  // 64-bit logic and shifts: the default counts two instructions (one per
  // 32 bits), but s_and_b64 and friends are one SALU instruction, and
  // v_lshlrev_b64 and friends one VALU instruction (measured on gfx900 and
  // gfx1100). A divergent 64-bit and/or/xor stays two v_*_b32. Only without
  // a literal (a 64-bit literal needs moves first).
  if (N.isOperation() && is64BitInt(N.Ty) && none_of(It.Ops, [&](unsigned Op) {
        return D.Items[Op].N->isConstant() &&
               !isInlineConstant64(D.Items[Op].N->Imm);
      })) {
    bool Uniform = It.Bank == BankState::Uniform;
    switch (N.Opcode) {
    case G_AND:
    case G_OR:
    case G_XOR:
      if (Uniform)
        return {1, 4, 1};
      return Default;
    case G_SHL:
    case G_LSHR:
    case G_ASHR:
      return {1, Uniform ? 4u : 8u, 1};
    default:
      return Default;
    }
  }
  // The size of one 32-bit instruction: SOP1/SOP2/SOPC for a uniform value,
  // VOP1/VOP2/VOPC or VOP3 for a divergent one, 4 more bytes for a literal.
  if (!N.isOperation() || Default.Instrs != 1 ||
      !(is32Bit(N.Ty) || (N.Opcode == G_ICMP && !It.Ops.empty() &&
                          is32Bit(D.Items[It.Ops[0]].N->Ty))))
    return Default;
  bool Literal = any_of(
      It.Ops, [&](unsigned Op) { return getKind(D, Op) == SrcKind::Literal; });
  CostVector C = Default;
  if (It.Bank == BankState::Uniform || hasShortVALUEncoding(N.Opcode))
    C.Bytes = Literal ? 8 : 4;
  else if (hasOnlyVOP3Encoding(N.Opcode))
    C.Bytes = Literal && VOP3Literal ? 12 : 8;
  return C;
}

std::optional<PatternCover>
AMDGPUTargetCosts::matchCover(const CostDag &D, unsigned Root, unsigned Pos,
                              const ThreeOpPattern &P) const {
  const CostDag::Item &Outer = D.Items[Root];
  unsigned J = Outer.Ops[Pos];
  const CostDag::Item &Inner = D.Items[J];
  const ENode &IN = *Inner.N;
  if (!IN.isOperation() || IN.Opcode != P.Inner || IN.Ops.size() != 2 ||
      !is32Bit(IN.Ty) || Inner.Uses != 1 || Inner.IsRoot)
    return std::nullopt;
  unsigned Srcs[3] = {Inner.Ops[0], Inner.Ops[1], Outer.Ops[1 - Pos]};
  if (any_of(Srcs, [&](unsigned S) { return !is32Bit(D.Items[S].N->Ty); }))
    return std::nullopt;
  SrcKind Kinds[3] = {getKind(D, Srcs[0]), getKind(D, Srcs[1]),
                      getKind(D, Srcs[2])};
  if (Inner.Bank == BankState::Uniform) {
    // Behind the copy to a VGPR: only cshl_32 finds it, and then the
    // predicate of ThreeOpFrag counts the SGPR-bank sources (the operands of
    // the uniform inner operation, constants included, and the other operand
    // of the outer one).
    if (!P.LooksThroughCopies)
      return std::nullopt;
    unsigned SgprSources = 2 + (Kinds[2] != SrcKind::VGPR);
    if (SgprSources > ConstantBusLimit)
      return std::nullopt;
  }
  if (P.AddendInVGPR &&
      (Kinds[2] != SrcKind::VGPR || Kinds[0] == SrcKind::Literal ||
       Kinds[1] == SrcKind::Literal))
    return std::nullopt;

  // The sources that SIFoldOperands cannot fold into the instruction stay
  // in VGPRs (v_mov_b32): distinct SGPRs beyond the constant bus limit, and
  // literals without a VOP3 literal (before GFX10) or beyond the bus.
  unsigned Bus = ConstantBusLimit, LiteralSlots = VOP3Literal ? 1 : 0;
  unsigned Movs = 0, MovBytes = 0;
  bool EncodedLiteral = false;
  SmallVector<unsigned, 3> Sgprs;
  for (unsigned K = 0; K != 3; ++K) {
    if (Kinds[K] != SrcKind::SGPR || is_contained(Sgprs, Srcs[K]))
      continue;
    Sgprs.push_back(Srcs[K]);
    if (Bus) {
      --Bus;
    } else {
      ++Movs;
      MovBytes += 4;
    }
  }
  for (unsigned K = 0; K != 3; ++K) {
    if (Kinds[K] != SrcKind::Literal)
      continue;
    if (LiteralSlots && Bus) {
      --LiteralSlots;
      --Bus;
      EncodedLiteral = true;
    } else {
      ++Movs;
      MovBytes += 8;
    }
  }
  PatternCover C;
  C.Root = Root;
  C.Inner.push_back(J);
  C.Cost.Instrs = 1 + Movs;
  C.Cost.Bytes = 8 + (EncodedLiteral ? 4 : 0) + MovBytes;
  C.Cost.Depth = P.Latency + (Movs ? 1 : 0);
  C.Name = P.Name;
  return C;
}

void AMDGPUTargetCosts::findCovers(
    const EGraph &G, const CostDag &D,
    SmallVectorImpl<PatternCover> &Covers) const {
  for (unsigned I = 0, E = D.Items.size(); I != E; ++I) {
    const CostDag::Item &It = D.Items[I];
    const ENode &N = *It.N;
    // A uniform result is computed by SALU instructions: no VALU fusion.
    if (!N.isOperation() || N.Ops.size() != 2 || !is32Bit(N.Ty) ||
        It.Bank == BankState::Uniform)
      continue;
    for (const ThreeOpPattern *P : Available) {
      if (P->Outer != N.Opcode)
        continue;
      // The inner operation is the first operand of op2 in ThreeOpFrag; a
      // commutative outer operator also matches it as the second one.
      bool Commutative = N.Opcode != G_SHL && N.Opcode != G_PTR_ADD;
      for (unsigned Pos = 0; Pos != (Commutative ? 2u : 1u); ++Pos)
        if (std::optional<PatternCover> C = matchCover(D, I, Pos, *P))
          Covers.push_back(*C);
    }
  }
}

void AMDGPUTargetCosts::describe(raw_ostream &OS) const {
  OS << "amdgpu " << (CPU.empty() ? "generic" : CPU)
     << ": constant-bus=" << ConstantBusLimit
     << " vop3-literal=" << (VOP3Literal ? "yes" : "no") << " three-op=";
  if (Available.empty())
    OS << "none";
  SmallVector<StringRef, 16> Names;
  for (const ThreeOpPattern *P : Available)
    if (!is_contained(Names, P->Name))
      Names.push_back(P->Name);
  for (unsigned I = 0, E = Names.size(); I != E; ++I)
    OS << (I ? "," : "") << Names[I];
  OS << " bank-source="
     << (IsRegBankSelected ? "register-banks" : "uniformity-analysis")
     << " position="
     << (IsRegBankSelected ? "post-regbankselect"
         : IsLegalized     ? "post-legalizer"
                           : "pre-legalizer");
}

} // namespace

std::unique_ptr<TargetCosts> llvm::egraph::createAMDGPUTargetCosts(
    const MachineFunction &MF, bool IsLegalized, bool IsRegBankSelected) {
  if (!MF.getTarget().getTargetTriple().isAMDGCN())
    return nullptr;
  return std::make_unique<AMDGPUTargetCosts>(MF, IsLegalized,
                                             IsRegBankSelected);
}
