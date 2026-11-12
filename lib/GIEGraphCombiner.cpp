//===- llvm/CodeGen/GlobalISel/GIEGraphCombiner.cpp - E-graph combiner ----===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// Experimental equality-saturation combiner for scalar gMIR. See
/// GIEGraphCombiner.h and llvm/docs/GlobalISel/GIEGraphCombiner-Design.md.
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/GlobalISel/GIEGraphCombiner.h"
#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/CodeGen/GlobalISel/GIEGraph.h"
#include "llvm/CodeGen/GlobalISel/GISelValueTracking.h"
#include "llvm/CodeGen/GlobalISel/LegalizerInfo.h"
#include "llvm/CodeGen/GlobalISel/MachineIRBuilder.h"
#include "llvm/CodeGen/GlobalISel/Utils.h"
#include "llvm/CodeGen/LowLevelTypeUtils.h"
#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/PassTimingInfo.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include <map>
#include <set>

#define DEBUG_TYPE "gisel-egraph"

using namespace llvm;
using namespace llvm::egraph;

STATISTIC(NumRegions, "Number of e-graph regions examined");
STATISTIC(NumRegionsNoRoot, "Number of regions without live results");
STATISTIC(NumOrigNodes, "Number of e-nodes before saturation");
STATISTIC(NumSaturatedNodes, "Number of e-nodes after saturation");
STATISTIC(NumEClasses, "Number of e-classes after saturation");
STATISTIC(NumMatches, "Number of rewrite matches");
STATISTIC(NumMerges, "Number of e-class merges from rewrites");
STATISTIC(NumACMerges, "Number of e-class merges from AC canonicalization");
STATISTIC(NumPhiMerges, "Number of e-class merges from PHIs of one value");
STATISTIC(NumRefinements, "Number of refinement edges from rewrites");
STATISTIC(NumUnsafe, "Number of matches rejected as unsound");
STATISTIC(NumIterations, "Number of saturation iterations");
STATISTIC(NumSaturated, "Number of regions saturated within budget");
STATISTIC(NumBudgetLimited, "Number of regions stopped by a budget");
STATISTIC(NumProfitable, "Number of regions with a cheaper candidate");
STATISTIC(NumApplied, "Number of regions rewritten");
STATISTIC(NumDominanceRejected,
          "Number of profitable candidates rejected for dominance");
STATISTIC(CostSaved, "Estimated cost saved by rewritten regions");
STATISTIC(ShadowCostSaved, "Estimated cost saved by profitable candidates");

namespace {
enum class EGraphMode { Shadow, Rewrite };
enum class EGraphStages { Both, PreLegalizer, PostLegalizer };
} // namespace

static cl::opt<EGraphStages> Stages(
    "gisel-egraph-stages", cl::Hidden, cl::init(EGraphStages::Both),
    cl::desc("The positions at which the experimental GlobalISel e-graph "
             "combiner runs, if the target schedules it at both"),
    cl::values(clEnumValN(EGraphStages::Both, "both",
                          "Before and after the legalizer"),
               clEnumValN(EGraphStages::PreLegalizer, "pre-legalizer",
                          "Only before the legalizer"),
               clEnumValN(EGraphStages::PostLegalizer, "post-legalizer",
                          "Only after the legalizer")));

static cl::opt<EGraphMode> Mode(
    "gisel-egraph-mode", cl::Hidden, cl::init(EGraphMode::Shadow),
    cl::desc("Operating mode of the experimental GlobalISel e-graph combiner"),
    cl::values(clEnumValN(EGraphMode::Shadow, "shadow",
                          "Analyze and report only; never modify MIR"),
               clEnumValN(EGraphMode::Rewrite, "rewrite",
                          "Rewrite regions with a cheaper candidate")));

static cl::opt<unsigned>
    MaxRegionInstrs("gisel-egraph-max-region-instrs", cl::Hidden, cl::init(32),
                    cl::desc("Maximum number of instructions per region"));
static cl::opt<unsigned>
    MaxNodes("gisel-egraph-max-nodes", cl::Hidden, cl::init(5000),
             cl::desc("Maximum number of e-nodes per region"));
static cl::opt<unsigned>
    MaxIterations("gisel-egraph-max-iterations", cl::Hidden, cl::init(10),
                  cl::desc("Maximum number of saturation iterations"));
static cl::opt<unsigned> MaxMatches(
    "gisel-egraph-max-matches", cl::Hidden, cl::init(20000),
    cl::desc("Maximum number of rewrite matches per saturation iteration"));
static cl::opt<unsigned> MaxACLeaves(
    "gisel-egraph-max-ac-leaves", cl::Hidden, cl::init(8),
    cl::desc("Maximum number of leaves of a flattened associative and "
             "commutative term"));
static cl::opt<unsigned>
    MaxACViews("gisel-egraph-max-ac-views", cl::Hidden, cl::init(8),
               cl::desc("Maximum number of flattened views of an e-class per "
                        "associative and commutative operator"));
static cl::opt<unsigned>
    ConstantCost("gisel-egraph-constant-cost", cl::Hidden, cl::init(0),
                 cl::desc("Extraction cost of a G_CONSTANT"));
static cl::opt<unsigned> MulCost("gisel-egraph-mul-cost", cl::Hidden,
                                 cl::init(2),
                                 cl::desc("Extraction cost of a 32-bit G_MUL"));
static cl::opt<bool>
    Report("gisel-egraph-report", cl::Hidden, cl::init(false),
           cl::desc("Print a per-region report of the e-graph combiner"));

/// Flags that change the semantics of the supported operations. They are part
/// of the e-node identity; a flagged node is only ever matched as a
/// refinement (dropping the flag), never merged with an unflagged node.
static constexpr uint32_t SemanticFlags =
    MachineInstr::NoUWrap | MachineInstr::NoSWrap | MachineInstr::IsExact |
    MachineInstr::Disjoint | MachineInstr::NonNeg | MachineInstr::NoUSWrap |
    MachineInstr::SameSign | MachineInstr::InBounds;

static cl::opt<bool> PrintRules(
    "gisel-egraph-print-rules", cl::Hidden, cl::init(false),
    cl::desc("Print the rewrite rules of the e-graph combiner (one per line, "
             "'name: LHS => RHS') to stderr when the pass first runs"));

static cl::opt<bool> PrintOps(
    "gisel-egraph-print-ops", cl::Hidden, cl::init(false),
    cl::desc("Print the typing metadata of the operators of the e-graph "
             "combiner as JSON to stdout when the pass first runs"));
static cl::opt<bool> PrintOpSamples(
    "gisel-egraph-print-op-samples", cl::Hidden, cl::init(false),
    cl::desc("With -gisel-egraph-print-ops: also print values of the fold "
             "function of each operator"));
static cl::opt<std::string> ExportFile(
    "gisel-egraph-export", cl::Hidden,
    cl::desc("Append one JSON record per region with a cheaper candidate to "
             "this file: the typed DAG of the region and the DAG that the "
             "extractor selected (for llvm/utils/gisel-rule-synth)"));
static cl::opt<bool> ExportAll(
    "gisel-egraph-export-all", cl::Hidden, cl::init(false),
    cl::desc("With -gisel-egraph-export: also write the regions without a "
             "cheaper candidate"));

/// The version of the record format of -gisel-egraph-export.
static constexpr unsigned ExportVersion = 1;

static const char *TimerGroupName = "gisel-egraph";
static const char *TimerGroupDesc = "GlobalISel e-graph combiner";

static const std::vector<RewriteRule> &getRules() {
  static const std::vector<RewriteRule> Rules = getDefaultIntegerRules();
  return Rules;
}

/// True if \p MF has the IEEE treatment of subnormal numbers for the
/// floating-point format of \p Ty.
static bool hasIEEEDenormalMode(const MachineFunction &MF, LLT Ty) {
  return MF.getDenormalMode(getFltSemanticForLLT(Ty)) ==
         DenormalMode::getIEEE();
}

/// A region instruction: a supported operation (see OpProperties) whose
/// register operands are all virtual registers of scalar or pointer type,
/// with the types that the shape of the operator requires.
static bool isCandidate(const MachineInstr &MI,
                        const MachineRegisterInfo &MRI) {
  uint32_t ImpliedFlags;
  const OpProperties *P = getOpPropertiesForInstr(MI.getOpcode(), ImpliedFlags);
  if (!P || (MI.getFlags() & ~SemanticFlags))
    return false;
  SmallVector<LLT, 4> Defs, Uses;
  unsigned NumImms = 0;
  for (const MachineOperand &MO : MI.operands()) {
    if (MO.isImm()) {
      ++NumImms;
      continue;
    }
    // Predicates and basic blocks are part of the e-node's attribute.
    if (!MO.isReg())
      continue;
    if (!MO.getReg().isVirtual() || MO.isImplicit())
      return false;
    LLT Ty = MRI.getType(MO.getReg());
    if (!Ty.isValid() || Ty.isVector() || Ty.getSizeInBits() > 128)
      return false;
    (MO.isDef() ? Defs : Uses).push_back(Ty);
  }
  if (NumImms != (P->ImmAttr ? 1u : 0u))
    return false;
  if (P->NumOperands >= 0 && Uses.size() != unsigned(P->NumOperands))
    return false;

  const LLT S1 = LLT::scalar(1);
  auto OneDef = [&] { return Defs.size() == 1; };
  auto AllEqualScalars = [](ArrayRef<LLT> Tys) {
    return !Tys.empty() && Tys[0].isScalar() && all_equal(Tys);
  };
  switch (P->Shape) {
  case OpShape::Binary:
    return OneDef() && Defs[0].isScalar() && Uses[0] == Defs[0] &&
           (P->hasAmount() ? Uses[1].isScalar() : Uses[1] == Defs[0]);
  case OpShape::Unary:
    return OneDef() && Defs[0].isScalar() && Uses[0] == Defs[0];
  case OpShape::Cast:
    if (!OneDef())
      return false;
    switch (P->Cast) {
    case CastKind::PtrToInt:
      return Uses[0].isPointer() && Defs[0].isScalar();
    case CastKind::IntToPtr:
      return Uses[0].isScalar() && Defs[0].isPointer();
    default:
      // The conversions with a floating-point format are checked in full:
      // their rules and folds use the format of the type.
      if (isFPCast(P->Cast)) {
        // The rules of a conversion between two formats hold for the IEEE
        // treatment of subnormal numbers: with another mode, the
        // conversion takes a subnormal operand as zero or can give zero
        // for a subnormal result.
        if ((P->Cast == CastKind::FPExtend ||
             P->Cast == CastKind::FPTruncate) &&
            !(hasIEEEDenormalMode(*MI.getMF(), Defs[0]) &&
              hasIEEEDenormalMode(*MI.getMF(), Uses[0])))
          return false;
        return isValidCast(*P, Defs[0], Uses[0], /*Attr=*/0);
      }
      return Uses[0].isScalar() && Defs[0].isScalar();
    }
  case OpShape::BitCount:
    return OneDef() && Defs[0].isScalar() && Uses[0].isScalar();
  case OpShape::Compare:
    return OneDef() && Defs[0] == S1 && Uses[0] == Uses[1];
  case OpShape::Select:
    return OneDef() && Uses[0] == S1 && Uses[1] == Defs[0] &&
           Uses[2] == Defs[0];
  case OpShape::PtrAdd:
    return OneDef() && Defs[0].isPointer() && Uses[0] == Defs[0] &&
           Uses[1].isScalar();
  case OpShape::Phi:
    return OneDef() && !Uses.empty() &&
           all_of(Uses, [&](LLT Ty) { return Ty == Defs[0]; });
  case OpShape::Typed: {
    if (Defs.size() != P->ResultKinds.size())
      return false;
    // All operands and results of kind Main have one scalar type.
    LLT MainTy;
    auto Check = [&](TypeKind Kind, LLT Ty) {
      switch (Kind) {
      case TypeKind::Main:
        if (!MainTy.isValid())
          MainTy = Ty;
        return Ty.isScalar() && Ty == MainTy;
      case TypeKind::Free:
        return Ty.isScalar();
      case TypeKind::Bool:
        return Ty == S1;
      }
      llvm_unreachable("bad kind");
    };
    for (unsigned I = 0, E = Uses.size(); I != E; ++I)
      if (!Check(P->OperandKinds[I], Uses[I]))
        return false;
    for (unsigned I = 0, E = Defs.size(); I != E; ++I)
      if (!Check(P->ResultKinds[I], Defs[I]))
        return false;
    return true;
  }
  case OpShape::Merge:
    return OneDef() && Defs[0].isScalar() && Uses.size() >= 2 &&
           AllEqualScalars(Uses) &&
           Uses[0].getSizeInBits() * Uses.size() == Defs[0].getSizeInBits();
  case OpShape::Unmerge:
    return Defs.size() >= 2 && Uses[0].isScalar() && AllEqualScalars(Defs) &&
           Defs[0].getSizeInBits() * Defs.size() == Uses[0].getSizeInBits();
  case OpShape::Effect:
    return Defs.empty() && (Uses.empty() || Uses[0] == S1);
  }
  llvm_unreachable("bad shape");
}

/// Conservative definedness of a region input. We intentionally do not use
/// the generic isGuaranteedNotToBeUndefOrPoison helpers here: they recurse
/// through COPYs of physical registers, which is not safe in this context.
static InputInfo getInputInfo(Register Reg, const MachineRegisterInfo &MRI) {
  InputInfo Info;
  Info.Ty = MRI.getType(Reg);
  const MachineInstr *Def = MRI.getVRegDef(Reg);
  if (!Def)
    return Info;
  switch (Def->getOpcode()) {
  case TargetOpcode::G_FREEZE:
  case TargetOpcode::G_CONSTANT:
    Info.NotUndef = Info.NotPoison = true;
    break;
  default:
    break;
  }
  return Info;
}

namespace {
/// A value of a region that is used outside of it (operand \p DefIdx of
/// \p MI), or a terminator.
struct RootRef {
  MachineInstr *MI;
  unsigned DefIdx;
  bool isValue() const { return MI->getNumExplicitDefs() != 0; }
  Register getReg() const { return MI->getOperand(DefIdx).getReg(); }
};

struct Region {
  SmallVector<MachineInstr *, 32> Instrs; // In block order.
  SmallVector<RootRef, 4> Roots;
};

/// The opcode of the instruction that implements \p N.
unsigned getInstrOpcode(const ENode &N) {
  return (N.Flags & PoisonVariantFlag)
             ? getOpProperties(N.Opcode)->PoisonVariant
             : N.Opcode;
}

/// The types of the results of the instruction that implements \p N.
SmallVector<LLT, 2> getInstrResultTypes(const EGraph &G, const ENode &N) {
  const OpProperties *P = getOpProperties(N.Opcode);
  SmallVector<LLT, 2> Tys;
  if (P->Shape == OpShape::Unmerge) {
    Tys.assign(G.getType(N.Ops[0]).getSizeInBits() / N.Ty.getSizeInBits(),
               N.Ty);
  } else if (P->hasProjections()) {
    // Every result of an operator with several results is of the main type
    // or s1. The main type is the type of an operand.
    LLT MainTy;
    for (unsigned I = 0, E = N.Ops.size(); I != E; ++I)
      if (P->OperandKinds[I] == TypeKind::Main)
        MainTy = G.getType(N.Ops[I]);
    for (unsigned I = 0, E = P->ResultKinds.size(); I != E; ++I)
      Tys.push_back(getTypedResultType(*P, I, MainTy));
  } else {
    Tys.push_back(N.Ty);
  }
  return Tys;
}

/// The cost model of the pass: the default costs, and only the operations
/// that the target accepts at the position of the pass.
///
/// Before the legalizer, a rule can introduce an operator that the region
/// does not contain (a minimum for a select of a comparison). If the
/// legalizer expands it again, the cost of one node is wrong, so only
/// operations that the target implements directly are extracted. That finds
/// the rewrites that are good for every target.
///
/// After the legalizer, every instruction and constant that the pass
/// creates must be legal. The search then works on the operations that the
/// legalizer made for this target, and its result is specific to the target.
class TargetCostModel : public DefaultCostModel {
public:
  const LegalizerInfo *LI = nullptr;
  const TargetInstrInfo *TII = nullptr;
  /// True after the legalizer.
  bool RequireLegal = false;

  /// Record the operation \p N of the region; it is always allowed.
  void addOriginal(const EGraph &G, const ENode &N) {
    SmallVector<LLT, 4> Types;
    unsigned Opc = getQuery(G, N, Types);
    Original.insert(getKey(Opc, Types));
  }

  bool isAllowed(const EGraph &G, const ENode &N) const override {
    if (N.isOperation()) {
      const OpProperties *P = getOpProperties(N.Opcode);
      if (!P->hasResult() || P->Shape == OpShape::Phi)
        return true;
    }
    if (!LI)
      return true;
    // A constant is an instruction of its own after the legalizer only.
    if (N.isConstant() && !RequireLegal)
      return true;
    SmallVector<LLT, 4> Types;
    unsigned Opc = getQuery(G, N, Types);
    if (Original.count(getKey(Opc, Types)))
      return true;
    switch (LI->getAction({Opc, Types}).Action) {
    case LegalizeActions::Legal:
      return true;
    case LegalizeActions::Custom:
    case LegalizeActions::NarrowScalar:
    case LegalizeActions::WidenScalar:
      return !RequireLegal;
    default:
      return false;
    }
  }

private:
  static std::vector<uint64_t> getKey(unsigned Opc, ArrayRef<LLT> Types) {
    std::vector<uint64_t> Key = {Opc};
    for (LLT Ty : Types)
      Key.push_back(getTypeKey(Ty));
    return Key;
  }

  /// Return the opcode of the instruction that implements \p N, and set
  /// \p Types to the types of its legality query.
  unsigned getQuery(const EGraph &G, const ENode &N,
                    SmallVectorImpl<LLT> &Types) const {
    if (N.isConstant()) {
      Types.push_back(N.Ty);
      return N.Ty.isFloat() ? TargetOpcode::G_FCONSTANT
                            : TargetOpcode::G_CONSTANT;
    }
    const OpProperties *P = getOpProperties(N.Opcode);
    unsigned Opc = getInstrOpcode(N);
    // The types of the register operands, in the order of the instruction.
    SmallVector<LLT, 6> OperandTys;
    if (P->Shape == OpShape::Unmerge)
      OperandTys.push_back(N.Ty);
    else
      append_range(OperandTys, getInstrResultTypes(G, N));
    for (EClassId Op : N.Ops)
      OperandTys.push_back(G.getType(Op));
    SmallBitVector Seen(8);
    const MCInstrDesc &Desc = TII->get(Opc);
    ArrayRef<MCOperandInfo> Info = Desc.operands();
    for (unsigned I = 0, E = Desc.getNumOperands(); I != E; ++I) {
      if (!Info[I].isGenericType() || I >= OperandTys.size())
        continue;
      unsigned Idx = Info[I].getGenericTypeIndex();
      if (Seen[Idx])
        continue;
      Seen.set(Idx);
      if (Types.size() <= Idx)
        Types.resize(Idx + 1);
      Types[Idx] = OperandTys[I];
    }
    return Opc;
  }

  std::set<std::vector<uint64_t>> Original;
};

class EGraphCombinerImpl {
public:
  EGraphCombinerImpl(MachineFunction &MF, bool CanRewrite, bool IsLegalized)
      : MF(MF), MRI(MF.getRegInfo()), CanRewrite(CanRewrite),
        IsLegalized(IsLegalized) {
    CM.ConstantCost = ConstantCost;
    CM.MulCost = MulCost;
    CM.LI = MF.getSubtarget().getLegalizerInfo();
    CM.TII = MF.getSubtarget().getInstrInfo();
    CM.RequireLegal = IsLegalized;
  }

  bool run();

private:
  void numberBlock(MachineBasicBlock &MBB);
  Region formRegion(MachineInstr &Seed);
  bool processRegion(MachineBasicBlock &MBB, Region &R);
  /// The dominator tree, computed on first use: it is only needed for
  /// candidates that replace a PHI by one of its incoming values.
  MachineDominatorTree &getDomTree() {
    if (!MDT)
      MDT.emplace(MF);
    return *MDT;
  }
  /// Known bits for -gisel-egraph-export, computed on first use.
  GISelValueTracking &getValueTracking() {
    if (!VT)
      VT.emplace(MF);
    return *VT;
  }
  void exportNode(json::OStream &J, const ENode &N) const;

  MachineFunction &MF;
  MachineRegisterInfo &MRI;
  bool CanRewrite;
  bool IsLegalized;
  TargetCostModel CM;
  std::optional<MachineDominatorTree> MDT;
  std::optional<GISelValueTracking> VT;
  DenseMap<const MachineInstr *, unsigned> Order;
  SmallPtrSet<const MachineInstr *, 32> Visited;
  SmallPtrSet<const MachineInstr *, 32> Erased;
};
} // namespace

/// Write the operator, the attribute and the flags of the operation \p N.
void EGraphCombinerImpl::exportNode(json::OStream &J, const ENode &N) const {
  const OpProperties *P = getOpProperties(N.Opcode);
  J.attribute("op", CM.TII->getName(getInstrOpcode(N)));
  if (P->Shape == OpShape::Compare)
    J.attribute("pred", getComparePredicateName(N.Attr));
  else if (P->hasProjections())
    J.attribute("res", N.Attr);
  else if (P->ImmAttr)
    J.attribute("imm", N.Attr);
  else if (P->Shape == OpShape::Phi || P->Shape == OpShape::Effect ||
           P->StopsPoison)
    J.attribute("site", N.Attr);
  static const std::pair<uint32_t, const char *> FlagNames[] = {
      {MachineInstr::NoUWrap, "nuw"},
      {MachineInstr::NoSWrap, "nsw"},
      {MachineInstr::IsExact, "exact"},
      {MachineInstr::Disjoint, "disjoint"},
      {MachineInstr::NonNeg, "nneg"},
      {MachineInstr::NoUSWrap, "nusw"},
      {MachineInstr::SameSign, "samesign"},
      {MachineInstr::InBounds, "inbounds"}};
  if (N.Flags & ~PoisonVariantFlag)
    J.attributeArray("flags", [&] {
      for (const auto &[Flag, Name] : FlagNames)
        if (N.Flags & Flag)
          J.value(Name);
    });
}

void EGraphCombinerImpl::numberBlock(MachineBasicBlock &MBB) {
  Order.clear();
  unsigned I = 0;
  for (MachineInstr &MI : MBB)
    Order[&MI] = I++;
}

Region EGraphCombinerImpl::formRegion(MachineInstr &Seed) {
  MachineBasicBlock *MBB = Seed.getParent();
  SetVector<MachineInstr *> In;
  SmallVector<MachineInstr *, 16> Work;
  Work.push_back(&Seed);
  auto Eligible = [&](MachineInstr *MI) {
    return MI && MI->getParent() == MBB && !Visited.count(MI) &&
           !Erased.count(MI) && !In.contains(MI) && isCandidate(*MI, MRI);
  };
  while (!Work.empty() && In.size() < MaxRegionInstrs) {
    MachineInstr *MI = Work.pop_back_val();
    if (!In.insert(MI))
      continue;
    for (const MachineOperand &MO : MI->operands()) {
      if (!MO.isReg())
        continue;
      if (MO.isDef()) {
        for (MachineInstr &User : MRI.use_nodbg_instructions(MO.getReg()))
          if (Eligible(&User))
            Work.push_back(&User);
        continue;
      }
      // The incoming values of a PHI are values of other blocks, or of the
      // previous iteration of this block. They are inputs.
      if (MI->isPHI())
        continue;
      MachineInstr *Def = MRI.getVRegDef(MO.getReg());
      if (Eligible(Def))
        Work.push_back(Def);
    }
    // A conditional branch and the unconditional branch after it are one
    // terminator with two targets.
    if (MI->getOpcode() == TargetOpcode::G_BRCOND) {
      MachineInstr *Next = MI->getNextNode();
      if (Next && Next->getOpcode() == TargetOpcode::G_BR && Eligible(Next))
        Work.push_back(Next);
    }
  }

  Region R;
  R.Instrs.assign(In.begin(), In.end());
  llvm::sort(R.Instrs, [&](const MachineInstr *A, const MachineInstr *B) {
    return Order.lookup(A) < Order.lookup(B);
  });
  for (MachineInstr *MI : R.Instrs) {
    Visited.insert(MI);
    // Terminators are always kept. A PHI of the region stays in place too,
    // so its uses count as external.
    if (MI->getNumExplicitDefs() == 0) {
      R.Roots.push_back({MI, 0});
      continue;
    }
    for (unsigned I = 0, E = MI->getNumExplicitDefs(); I != E; ++I)
      if (any_of(
              MRI.use_nodbg_instructions(MI->getOperand(I).getReg()),
              [&](MachineInstr &U) { return !In.contains(&U) || U.isPHI(); }))
        R.Roots.push_back({MI, I});
  }
  return R;
}

bool EGraphCombinerImpl::processRegion(MachineBasicBlock &MBB, Region &R) {
  ++NumRegions;
  if (R.Roots.empty()) {
    ++NumRegionsNoRoot;
    return false;
  }

  // 1. Translate the region into an e-graph.
  EGraph G;
  // The class of a register's value in this block and, for a register that
  // is defined in this block and used by a PHI of this block, the class of
  // its value in the previous iteration.
  DenseMap<Register, EClassId> RegClass, CarriedClass;
  // The class of a terminator.
  DenseMap<const MachineInstr *, EClassId> InstrClass;
  // Per input: its register, whether it is a value of the previous
  // iteration, and whether it is only known as the incoming value of a PHI
  // (it then does not have to dominate this block).
  SmallVector<Register, 8> InputRegs;
  SmallVector<bool, 8> InputIsCarried, InputIsPhiOnly;
  DenseMap<Register, unsigned> InputIndex;
  // The instructions that ENode::Attr of PHI and terminator nodes refers
  // to. PHIs with the same incoming values share an entry.
  SmallVector<MachineInstr *, 4> Sites;
  std::map<std::vector<EClassId>, unsigned> PhiSites;
  SmallSetVector<MachineInstr *, 4> ConstDefs;
  // The definitions of the region: the class, the instruction and the index
  // of the result (a G_CONSTANT has index 0). The emission uses an
  // instruction again if the extracted expression contains it unchanged.
  struct OrigDef {
    EClassId Class;
    MachineInstr *MI;
    unsigned DefIdx;
  };
  SmallVector<OrigDef, 32> OrigDefs;
  // The flags of the node of each instruction of the region.
  DenseMap<const MachineInstr *, uint32_t> OrigFlags;
  // For -gisel-egraph-export: the nodes of the region as they were added
  // (the operands are the classes before the saturation), and the classes
  // of the inputs and of the constants.
  struct ExportNode {
    EClassId Class;
    ENode N;
    MachineInstr *MI;
    unsigned DefIdx;
  };
  bool Exporting = !ExportFile.empty();
  std::vector<ExportNode> ExportNodes;
  SmallVector<EClassId, 8> InputClasses;
  SmallVector<std::pair<EClassId, APInt>, 8> ExportConsts;
  uint64_t OldCost = 0;

  auto GetOperandClass = [&](Register Reg, bool IsPhiOperand) {
    MachineInstr *Def = MRI.getVRegDef(Reg);
    bool Carried = IsPhiOperand && Def && Def->getParent() == &MBB;
    DenseMap<Register, EClassId> &Map = Carried ? CarriedClass : RegClass;
    auto It = Map.find(Reg);
    if (It != Map.end()) {
      // A use by another instruction of this block shows that the register
      // is available here.
      auto Idx = InputIndex.find(Reg);
      if (!IsPhiOperand && Idx != InputIndex.end())
        InputIsPhiOnly[Idx->second] = false;
      return It->second;
    }
    EClassId Id;
    LLT Ty = MRI.getType(Reg);
    std::optional<APInt> C;
    if (Ty.isScalar())
      C = getIConstantVRegVal(Reg, MRI);
    // A floating-point constant is its bit pattern. It is only a constant
    // here if its type tells it from an integer with the same bits.
    if (!C && Ty.isFloat() && hasFPFormat(Ty))
      if (const ConstantFP *FP = getConstantFPVRegVal(Reg, MRI))
        C = FP->getValueAPF().bitcastToAPInt();
    if (C) {
      Id = G.addConstant(Ty, *C);
      if (Exporting)
        ExportConsts.push_back({Id, *C});
      ConstDefs.insert(Def);
      if (Def->getOpcode() == TargetOpcode::G_CONSTANT ||
          Def->getOpcode() == TargetOpcode::G_FCONSTANT)
        OrigDefs.push_back({Id, Def, 0});
      CM.addOriginal(G, ENode::makeConstant(Ty, *C));
    } else {
      Id = G.addInput(getInputInfo(Reg, MRI));
      if (!Carried)
        InputIndex[Reg] = InputRegs.size();
      InputRegs.push_back(Reg);
      InputClasses.push_back(Id);
      InputIsCarried.push_back(Carried);
      InputIsPhiOnly.push_back(IsPhiOperand);
    }
    Map[Reg] = Id;
    return Id;
  };

  {
    NamedRegionTimer T("build", "Build e-graph", TimerGroupName, TimerGroupDesc,
                       TimePassesIsEnabled);
    for (MachineInstr *MI : R.Instrs) {
      uint32_t ImpliedFlags;
      const OpProperties *P =
          getOpPropertiesForInstr(MI->getOpcode(), ImpliedFlags);
      SmallVector<EClassId, 3> Ops;
      uint64_t Attr = 0;
      switch (P->Shape) {
      case OpShape::Phi: {
        // One operand per predecessor, ordered by block number.
        SmallVector<std::pair<int, EClassId>, 4> Incoming;
        for (unsigned I = 1, E = MI->getNumOperands(); I < E; I += 2)
          Incoming.push_back({MI->getOperand(I + 1).getMBB()->getNumber(),
                              GetOperandClass(MI->getOperand(I).getReg(),
                                              /*IsPhiOperand=*/true)});
        llvm::stable_sort(Incoming, llvm::less_first());
        for (auto [Pred, Class] : Incoming)
          Ops.push_back(Class);
        auto [It, Inserted] = PhiSites.try_emplace(
            std::vector<EClassId>(Ops.begin(), Ops.end()), Sites.size());
        if (Inserted)
          Sites.push_back(MI);
        Attr = It->second;
        break;
      }
      case OpShape::Effect: {
        for (const MachineOperand &MO : MI->operands())
          if (MO.isReg())
            Ops.push_back(GetOperandClass(MO.getReg(), false));
        // See OpShape::Effect: bit 1 is set if the two targets can be
        // exchanged.
        MachineInstr *Next = MI->getNextNode();
        bool HasBr = MI->getOpcode() == TargetOpcode::G_BRCOND && Next &&
                     Next->getOpcode() == TargetOpcode::G_BR &&
                     is_contained(R.Instrs, Next);
        Attr = (uint64_t(Sites.size()) << 2) | (HasBr ? 2 : 0);
        Sites.push_back(MI);
        break;
      }
      default:
        for (const MachineOperand &MO : MI->operands()) {
          if (MO.isReg() && MO.isUse())
            Ops.push_back(GetOperandClass(MO.getReg(), false));
          else if (MO.isPredicate())
            Attr = MO.getPredicate();
          else if (MO.isImm())
            Attr = MO.getImm();
        }
        // See OpProperties::StopsPoison.
        if (P->StopsPoison) {
          Attr = Sites.size();
          Sites.push_back(MI);
        }
        break;
      }
      uint32_t Flags = (MI->getFlags() & SemanticFlags) | ImpliedFlags;
      if (!P->hasResult()) {
        ENode N = ENode::makeOp(P->Opcode, LLT(), Ops, Flags, Attr);
        OldCost += std::max(1u, CM.getNodeCost(N));
        EClassId Id = G.add(N);
        InstrClass[MI] = Id;
        if (Exporting)
          ExportNodes.push_back({Id, std::move(N), MI, 0});
        continue;
      }
      // One node per result; the instruction is counted once.
      for (unsigned I = 0, E = MI->getNumExplicitDefs(); I != E; ++I) {
        Register Def = MI->getOperand(I).getReg();
        LLT Ty = MRI.getType(Def);
        ENode N = ENode::makeOp(P->Opcode, Ty, Ops, Flags,
                                P->hasProjections() ? I : Attr);
        if (I == 0)
          OldCost += std::max(1u, CM.getNodeCost(N));
        CM.addOriginal(G, N);
        EClassId Id = G.add(N);
        if (Exporting)
          ExportNodes.push_back({Id, std::move(N), MI, I});
        RegClass[Def] = Id;
        if (P->Shape != OpShape::Phi)
          OrigDefs.push_back({Id, MI, I});
      }
      OrigFlags[MI] = Flags;
    }
  }
  unsigned OrigNodes = G.getNumNodes();
  NumOrigNodes += OrigNodes;

  // 2. Bounded equality saturation.
  SaturationLimits Limits;
  Limits.MaxIterations = MaxIterations;
  Limits.MaxNodes = MaxNodes;
  Limits.MaxMatchesPerIteration = MaxMatches;
  Limits.MaxACLeaves = MaxACLeaves;
  Limits.MaxACViews = MaxACViews;
  SaturationStats S;
  {
    NamedRegionTimer T("saturate", "Saturate e-graph", TimerGroupName,
                       TimerGroupDesc, TimePassesIsEnabled);
    S = saturate(G, getRules(), Limits);
  }
  NumSaturatedNodes += G.getNumNodes();
  NumEClasses += G.getNumClasses();
  NumMatches += S.Matches;
  NumMerges += S.Merges;
  NumACMerges += S.ACMerges;
  NumPhiMerges += S.PhiMerges;
  NumRefinements += S.Refinements;
  NumUnsafe += S.RejectedUnsafe;
  NumIterations += S.Iterations;
  if (S.Saturated)
    ++NumSaturated;
  else
    ++NumBudgetLimited;

  // 3. Extraction.
  NamedRegionTimer ExtractTimer("extract", "Extract and rewrite",
                                TimerGroupName, TimerGroupDesc,
                                TimePassesIsEnabled);
  Extractor E(G, CM);
  SmallVector<EClassId, 4> RootClasses;
  for (const RootRef &Root : R.Roots)
    RootClasses.push_back(Root.isValue() ? RegClass.lookup(Root.getReg())
                                         : InstrClass.lookup(Root.MI));
  uint64_t NewCost = E.getDagCost(RootClasses);
  bool Profitable = NewCost < OldCost;
  if (Profitable) {
    ++NumProfitable;
    ShadowCostSaved += OldCost - NewCost;
  }

  // 4. Validate the candidate: acyclic, every input dominates the point where
  // it is first needed, and whether refinement edges are used. Mirrors the
  // emission order below exactly.
  bool UsesRefinement = false;
  StringRef Blocker;
  DenseSet<EClassId> Done;
  {
    DenseSet<EClassId> OnStack;
    std::function<bool(EClassId, unsigned)> Check = [&](EClassId C,
                                                        unsigned Pos) -> bool {
      EClassId Rc = E.resolve(C);
      if (Rc != G.find(C))
        UsesRefinement = true;
      if (Done.contains(Rc))
        return true;
      if (!OnStack.insert(Rc).second) {
        Blocker = "cycle";
        return false;
      }
      const ENode *N = E.getChosenNode(Rc);
      if (!N) {
        Blocker = "no-choice";
        return false;
      }
      if (N->isInput()) {
        // The value of a register in the previous iteration is not
        // available as a register.
        const MachineInstr *Def = MRI.getVRegDef(InputRegs[N->InputIdx]);
        if (!Def || InputIsCarried[N->InputIdx] ||
            (Def->getParent() == &MBB && Order.lookup(Def) >= Pos) ||
            (InputIsPhiOnly[N->InputIdx] && Def->getParent() != &MBB &&
             !getDomTree().dominates(Def->getParent(), &MBB))) {
          Blocker = "dominance";
          return false;
        }
      }
      // A PHI is not emitted again: the original instruction is used.
      bool IsPhi =
          N->isOperation() && getOpProperties(N->Opcode)->Shape == OpShape::Phi;
      if (!IsPhi)
        for (EClassId Op : N->Ops)
          if (!Check(Op, Pos))
            return false;
      OnStack.erase(Rc);
      Done.insert(Rc);
      return true;
    };
    for (unsigned I = 0, End = R.Roots.size(); I != End; ++I)
      if (!Check(RootClasses[I], Order.lookup(R.Roots[I].MI)))
        break;
  }

  bool DoRewrite = CanRewrite && Profitable && Blocker.empty();
  if (CanRewrite && Profitable && !Blocker.empty())
    ++NumDominanceRejected;
  if (DoRewrite)
    for (Register Reg : InputRegs)
      if (MRI.getRegClassOrRegBank(Reg))
        DoRewrite = false, Blocker = "reg-attrs";
  if (DoRewrite)
    for (const RootRef &Root : R.Roots)
      if (Root.isValue() && MRI.getRegClassOrRegBank(Root.getReg()))
        DoRewrite = false, Blocker = "reg-attrs";

  if (Report) {
    raw_ostream &OS = errs();
    const TargetRegisterInfo *TRI = MF.getSubtarget().getRegisterInfo();
    OS << "GIEGraph: " << MF.getName() << ": " << printMBBReference(MBB)
       << (IsLegalized ? ": legalized" : ":") << " instrs=" << R.Instrs.size()
       << " roots=" << R.Roots.size() << " inputs=" << InputRegs.size()
       << " nodes=" << OrigNodes << "->" << G.getNumNodes()
       << " classes=" << G.getNumClasses() << " iters=" << S.Iterations << " "
       << (S.Saturated       ? "saturated"
           : S.HitNodeLimit  ? "node-limit"
           : S.HitMatchLimit ? "match-limit"
                             : "iteration-limit")
       << " merges=" << S.Merges << " ac-merges=" << S.ACMerges
       << " phi-merges=" << S.PhiMerges << " refinements=" << S.Refinements
       << " unsafe=" << S.RejectedUnsafe << " cost=" << OldCost << "->"
       << NewCost << (Profitable ? " profitable" : " not-profitable");
    if (Profitable)
      OS << (UsesRefinement ? " (refinement)" : " (equivalence)");
    if (Profitable)
      OS << (DoRewrite     ? " rewritten"
             : !CanRewrite ? " shadow"
                           : (" blocked:" + Blocker).str().c_str());
    OS << "\n";
    if (Profitable) {
      auto PrintInput = [&](raw_ostream &OS, unsigned Idx) {
        OS << printReg(InputRegs[Idx], TRI);
      };
      for (unsigned I = 0, End = R.Roots.size(); I != End; ++I) {
        OS << "  root ";
        if (R.Roots[I].isValue())
          OS << printReg(R.Roots[I].getReg(), TRI) << " = ";
        E.printExpr(OS, RootClasses[I], PrintInput);
        OS << "\n";
      }
      OS << "  rules:";
      ArrayRef<RewriteRule> Rules = getRules();
      for (unsigned RI = 0, RE = Rules.size(); RI != RE; ++RI)
        if (S.RuleApplications[RI])
          OS << " " << Rules[RI].getName() << "=" << S.RuleApplications[RI];
      OS << "\n";
    }
  }

  if (Exporting && (Profitable || ExportAll)) {
    static std::unique_ptr<raw_fd_ostream> Out;
    if (!Out) {
      std::error_code EC;
      Out =
          std::make_unique<raw_fd_ostream>(ExportFile, EC, sys::fs::OF_Append);
      if (EC)
        report_fatal_error(Twine("cannot open ") + ExportFile + ": " +
                           EC.message());
    }
    auto Hex = [](const APInt &V) {
      return "0x" + toString(V, 16, /*Signed=*/false);
    };
    auto RegName = [](Register Reg) {
      return "%" + utostr(Reg.virtRegIndex());
    };
    auto TypeName = [](LLT Ty) {
      std::string Name;
      raw_string_ostream OS(Name);
      OS << Ty;
      return Name;
    };
    auto KnownBitsOf = [&](json::OStream &J, Register Reg) {
      if (!MRI.getType(Reg).isScalar())
        return;
      KnownBits KB = getValueTracking().getKnownBits(Reg);
      J.attribute("zero", Hex(KB.Zero));
      J.attribute("one", Hex(KB.One));
    };
    json::OStream J(*Out);
    J.object([&] {
      J.attribute("version", ExportVersion);
      J.attribute("fn", MF.getName());
      J.attribute("bb", MBB.getNumber());
      J.attribute("stage", IsLegalized ? "post-legalizer" : "pre-legalizer");
      J.attribute("triple", MF.getTarget().getTargetTriple().str());
      J.attribute("profitable", Profitable);
      J.attribute("refinement", UsesRefinement);
      J.attribute("blocker", Blocker);
      J.attribute("saturated", S.Saturated);
      J.attributeObject("cost", [&] {
        J.attribute("original", OldCost);
        J.attribute("optimized", NewCost);
      });
      J.attributeArray("inputs", [&] {
        for (unsigned I = 0, End = InputRegs.size(); I != End; ++I) {
          Register Reg = InputRegs[I];
          J.object([&] {
            J.attribute("id", InputClasses[I]);
            J.attribute("in", I);
            J.attribute("reg", RegName(Reg));
            J.attribute("type", TypeName(MRI.getType(Reg)));
            KnownBitsOf(J, Reg);
            const MachineInstr *Def = MRI.getVRegDef(Reg);
            J.attribute("def", Def ? CM.TII->getName(Def->getOpcode())
                                   : StringRef("<none>"));
            const InputInfo &Info = G.getInputInfo(I);
            J.attribute("not_undef", Info.NotUndef);
            J.attribute("not_poison", Info.NotPoison);
            if (InputIsCarried[I])
              J.attribute("carried", true);
          });
        }
      });
      J.attributeArray("constants", [&] {
        for (const std::pair<EClassId, APInt> &C : ExportConsts)
          J.object([&] {
            J.attribute("id", C.first);
            J.attribute("type", TypeName(G.getType(C.first)));
            J.attribute("value", Hex(C.second));
          });
      });
      // The region, in program order. An instruction with several results
      // has one node per result. "best" is the id of the "optimized" node
      // that the extractor selected for the value of the node.
      J.attributeArray("original", [&] {
        for (const ExportNode &EN : ExportNodes)
          J.object([&] {
            J.attribute("id", EN.Class);
            exportNode(J, EN.N);
            if (E.getChosenNode(E.resolve(EN.Class)))
              J.attribute("best", E.resolve(EN.Class));
            J.attribute("instr", Order.lookup(EN.MI));
            if (EN.MI->getNumExplicitDefs()) {
              Register Reg = EN.MI->getOperand(EN.DefIdx).getReg();
              J.attribute("reg", RegName(Reg));
              J.attribute("type", TypeName(MRI.getType(Reg)));
              J.attribute("uses", uint64_t(range_size(
                                      MRI.use_nodbg_instructions(Reg))));
              KnownBitsOf(J, Reg);
              const EClass &C = G.getClass(EN.Class);
              J.attribute("not_undef", C.NotUndef);
              J.attribute("not_poison", C.NotPoison);
            }
            J.attributeArray("args", [&] {
              for (EClassId Op : EN.N.Ops)
                J.value(Op);
            });
          });
      });
      // The expressions that the extractor selected, operands first.
      J.attributeArray("optimized", [&] {
        DenseSet<EClassId> Written;
        std::function<void(EClassId)> Write = [&](EClassId C) {
          EClassId Rc = E.resolve(C);
          const ENode *N = E.getChosenNode(Rc);
          if (!N || !Written.insert(Rc).second)
            return;
          for (EClassId Op : N->Ops)
            Write(Op);
          J.object([&] {
            J.attribute("id", Rc);
            if (N->isInput()) {
              J.attribute("in", N->InputIdx);
            } else if (N->isConstant()) {
              J.attribute("type", TypeName(N->Ty));
              J.attribute("value", Hex(N->Imm));
            } else {
              exportNode(J, *N);
              if (N->Ty.isValid())
                J.attribute("type", TypeName(N->Ty));
              J.attributeArray("args", [&] {
                for (EClassId Op : N->Ops)
                  J.value(E.resolve(Op));
              });
            }
          });
        };
        for (EClassId Root : RootClasses)
          Write(Root);
        for (const ExportNode &EN : ExportNodes)
          Write(EN.Class);
      });
      J.attributeArray("roots", [&] {
        for (unsigned I = 0, End = R.Roots.size(); I != End; ++I)
          J.object([&] {
            const RootRef &Root = R.Roots[I];
            if (Root.isValue())
              J.attribute("reg", RegName(Root.getReg()));
            J.attribute("original", Root.isValue()
                                        ? RegClass.lookup(Root.getReg())
                                        : InstrClass.lookup(Root.MI));
            // "original" is an id of the "original" nodes, inputs and
            // constants (a class before the saturation); "optimized" is an
            // id of the "optimized" nodes.
            J.attribute("optimized", E.resolve(RootClasses[I]));
          });
      });
      J.attributeObject("rules", [&] {
        ArrayRef<RewriteRule> Rules = getRules();
        for (unsigned RI = 0, RE = Rules.size(); RI != RE; ++RI)
          if (S.RuleApplications[RI])
            J.attribute(Rules[RI].getName(), S.RuleApplications[RI]);
      });
    });
    *Out << "\n";
    Out->flush();
  }

  if (!DoRewrite)
    return false;

  // 5. Emit the extracted expressions. Each root's expression is emitted
  // immediately before the original root instruction (after the PHIs if the
  // root is a PHI); classes shared with earlier roots are reused. PHIs and
  // terminators are not emitted again: a PHI that is still needed is kept,
  // and a terminator is updated in place.
  MachineIRBuilder B(MF);
  DenseMap<EClassId, Register> Mat;
  // The instructions of the region by class. An instruction that the new
  // code contains unchanged is not emitted again: later passes can depend on
  // the sequence and on the operand sequence of the instructions.
  DenseMap<EClassId, SmallVector<std::pair<MachineInstr *, unsigned>, 2>>
      ClassDefs;
  for (const OrigDef &D : OrigDefs)
    ClassDefs[G.find(D.Class)].push_back({D.MI, D.DefIdx});
  // Twice the position of the root that is emitted, and the positions of
  // the instructions that were moved (twice the position of that root,
  // minus one).
  int64_t CurPos = 0;
  DenseMap<const MachineInstr *, int64_t> MovedPos;
  // Make sure that \p MI, an instruction that is used again, is before the
  // insertion point. Its operands are available there.
  auto MoveBeforeInsertPt = [&](MachineInstr *MI) {
    if (MI->getParent() != &MBB)
      return;
    auto It = MovedPos.find(MI);
    int64_t Pos =
        It != MovedPos.end() ? It->second : 2 * int64_t(Order.lookup(MI));
    if (Pos <= CurPos)
      return;
    if (B.getInsertPt() != MI->getIterator())
      MBB.splice(B.getInsertPt(), &MBB, MI->getIterator());
    MovedPos[MI] = CurPos - 1;
  };
  // Return true if \p MI, an instruction of another block, is available in
  // this block.
  auto IsAvailable = [&](const MachineInstr *MI) {
    const MachineBasicBlock *DefMBB = MI->getParent();
    return DefMBB == &MBB || DefMBB == &MF.front() ||
           getDomTree().dominates(DefMBB, &MBB);
  };
  // The results of the emitted instructions with several results, by
  // opcode, flags and operand classes.
  std::map<std::vector<uint64_t>, SmallVector<Register, 2>> MultiDefs;
  SmallPtrSet<const MachineInstr *, 4> Kept;
  std::function<Register(EClassId)> Materialize = [&](EClassId C) {
    EClassId Rc = E.resolve(C);
    auto It = Mat.find(Rc);
    if (It != Mat.end())
      return It->second;
    const ENode *N = E.getChosenNode(Rc);
    Register Res;
    switch (N->Kind) {
    case ENodeKind::Input:
      Res = InputRegs[N->InputIdx];
      break;
    case ENodeKind::Constant: {
      for (auto [MI, DefIdx] : ClassDefs.lookup(Rc)) {
        Register Def = MI->getOperand(0).getReg();
        unsigned ConstOpc = N->Ty.isFloat() ? TargetOpcode::G_FCONSTANT
                                            : TargetOpcode::G_CONSTANT;
        if (MI->getOpcode() != ConstOpc || MRI.getType(Def) != N->Ty ||
            !IsAvailable(MI))
          continue;
        MoveBeforeInsertPt(MI);
        Res = Def;
        break;
      }
      if (!Res && N->Ty.isFloat())
        Res = B.buildFConstant(N->Ty,
                               APFloat(getFltSemanticForLLT(N->Ty), N->Imm))
                  .getReg(0);
      if (!Res)
        Res = B.buildConstant(N->Ty, N->Imm).getReg(0);
      break;
    }
    case ENodeKind::Operation: {
      const OpProperties *P = getOpProperties(N->Opcode);
      assert(P->hasResult() && "terminator used as a value");
      if (P->Shape == OpShape::Phi) {
        MachineInstr *Phi = Sites[N->Attr];
        Kept.insert(Phi);
        Res = Phi->getOperand(0).getReg();
        break;
      }
      SmallVector<EClassId, 3> Ops(N->Ops.begin(), N->Ops.end());
      uint64_t Attr = N->Attr;
      // Operands of commutative nodes and of comparisons are ordered by
      // class id; emit them in GlobalISel's canonical form instead (constant
      // on the right).
      if (Ops.size() == 2 && E.getChosenNode(Ops[0])->isConstant() &&
          !E.getChosenNode(Ops[1])->isConstant()) {
        if (P->Commutative) {
          std::swap(Ops[0], Ops[1]);
        } else if (P->Shape == OpShape::Compare) {
          std::swap(Ops[0], Ops[1]);
          Attr = CmpInst::getSwappedPredicate(
              static_cast<CmpInst::Predicate>(Attr));
        }
      }
      // Emit the arms of a select before its condition, so that the
      // comparison is next to the select. On a target with a condition
      // register, an instruction between the two can overwrite the register.
      if (P->Shape == OpShape::Select) {
        Materialize(Ops[1]);
        Materialize(Ops[2]);
      }
      SmallVector<SrcOp, 4> Srcs;
      SmallVector<Register, 4> SrcRegs;
      for (EClassId Op : Ops) {
        SrcRegs.push_back(Materialize(Op));
        Srcs.push_back(SrcRegs.back());
      }
      unsigned Opc = getInstrOpcode(*N);
      uint32_t Flags = N->Flags & ~PoisonVariantFlag;
      // The key of an instruction with several results. The type of the
      // parts is part of the key of an unmerge: a value can be divided in
      // more than one way.
      std::vector<uint64_t> Key;
      if (P->hasProjections()) {
        Key = {Opc, Flags};
        if (P->Shape == OpShape::Unmerge)
          Key.push_back(getTypeKey(N->Ty));
        for (EClassId Op : N->Ops)
          Key.push_back(E.resolve(Op));
      }
      // Use an instruction of the region again if it computes this node
      // from the same registers.
      if (!P->hasProjections() || !MultiDefs.count(Key)) {
        MachineInstr *Old = nullptr;
        unsigned OldIdx = 0;
        for (auto [MI, DefIdx] : ClassDefs.lookup(Rc)) {
          if (MI->getOpcode() != Opc || OrigFlags.lookup(MI) != N->Flags ||
              MRI.getType(MI->getOperand(DefIdx).getReg()) != N->Ty ||
              (P->hasProjections() && DefIdx != N->Attr) ||
              (P->StopsPoison && Sites[N->Attr] != MI))
            continue;
          SmallVector<Register, 4> UseRegs;
          uint64_t OldAttr = 0;
          for (const MachineOperand &MO : MI->operands()) {
            if (MO.isReg() && MO.isUse())
              UseRegs.push_back(MO.getReg());
            else if (MO.isPredicate())
              OldAttr = MO.getPredicate();
            else if (MO.isImm())
              OldAttr = MO.getImm();
          }
          bool Same = UseRegs == SrcRegs;
          bool Swapped = UseRegs.size() == 2 && UseRegs[0] == SrcRegs[1] &&
                         UseRegs[1] == SrcRegs[0];
          bool Match;
          if (P->Shape == OpShape::Compare)
            Match = (Same && OldAttr == Attr) ||
                    (Swapped &&
                     OldAttr == CmpInst::getSwappedPredicate(
                                    static_cast<CmpInst::Predicate>(Attr)));
          else
            Match = (!P->ImmAttr || OldAttr == Attr) &&
                    (Same || (Swapped && P->Commutative));
          if (Match) {
            Old = MI;
            OldIdx = DefIdx;
            break;
          }
        }
        if (Old) {
          MoveBeforeInsertPt(Old);
          Kept.insert(Old);
          if (P->hasProjections()) {
            SmallVector<Register, 2> &Defs = MultiDefs[Key];
            for (unsigned I = 0, End = Old->getNumExplicitDefs(); I != End; ++I)
              Defs.push_back(Old->getOperand(I).getReg());
          }
          Res = Old->getOperand(OldIdx).getReg();
          break;
        }
      }
      if (P->Shape == OpShape::Compare) {
        Res = B.buildICmp(static_cast<CmpInst::Predicate>(Attr), N->Ty, Srcs[0],
                          Srcs[1], Flags)
                  .getReg(0);
        break;
      }
      if (P->hasProjections()) {
        // One instruction computes all the results.
        SmallVector<Register, 2> &Defs = MultiDefs[Key];
        if (Defs.empty()) {
          SmallVector<DstOp, 2> Dsts;
          for (LLT Ty : getInstrResultTypes(G, *N))
            Dsts.push_back(Ty);
          MachineInstrBuilder MIB = B.buildInstr(Opc, Dsts, Srcs, Flags);
          for (unsigned I = 0, End = Dsts.size(); I != End; ++I)
            Defs.push_back(MIB.getReg(I));
        }
        Res = Defs[Attr];
        break;
      }
      if (P->ImmAttr)
        Srcs.push_back(SrcOp(int64_t(Attr)));
      Res = B.buildInstr(Opc, {N->Ty}, Srcs, Flags).getReg(0);
      break;
    }
    }
    Mat[Rc] = Res;
    return Res;
  };

  SmallVector<std::pair<Register, Register>, 4> Replacements;
  for (unsigned I = 0, End = R.Roots.size(); I != End; ++I) {
    MachineInstr *Root = R.Roots[I].MI;
    if (!R.Roots[I].isValue()) {
      // A terminator: use the operands of the chosen form and, if that is
      // the inverted form, exchange the targets of the conditional and the
      // unconditional branch.
      const ENode *N = E.getChosenNode(RootClasses[I]);
      B.setInstrAndDebugLoc(*Root);
      CurPos = 2 * int64_t(Order.lookup(Root));
      unsigned OpIdx = 0;
      for (MachineOperand &MO : Root->operands())
        if (MO.isReg())
          MO.setReg(Materialize(N->Ops[OpIdx++]));
      if (N->Attr & 1) {
        MachineOperand &Taken = Root->getOperand(1);
        MachineOperand &NotTaken = Root->getNextNode()->getOperand(0);
        MachineBasicBlock *Tmp = Taken.getMBB();
        Taken.setMBB(NotTaken.getMBB());
        NotTaken.setMBB(Tmp);
      }
      continue;
    }
    if (Root->isPHI()) {
      B.setInsertPt(MBB, MBB.SkipPHIsAndLabels(MBB.begin()));
      B.setDebugLoc(Root->getDebugLoc());
    } else {
      B.setInstrAndDebugLoc(*Root);
    }
    CurPos = 2 * int64_t(Order.lookup(Root));
    Replacements.push_back({R.Roots[I].getReg(), Materialize(RootClasses[I])});
  }
  // Mark everything we emitted as visited so it is not re-processed.
  for (MachineInstr &MI : MBB)
    if (!Order.count(&MI))
      Visited.insert(&MI);

  // Redirect the uses of each root (but not its definition, which is erased
  // below) to the new value. replaceRegWith() would also rewrite the def.
  for (auto [Old, New] : Replacements)
    for (MachineOperand &MO : make_early_inc_range(MRI.use_operands(Old)))
      MO.setReg(New);

  // 6. Erase the old region (users before definitions), except for
  // terminators and the PHIs that the new code uses.
  for (MachineInstr *MI : reverse(R.Instrs)) {
    if (MI->getNumExplicitDefs() == 0 || Kept.count(MI))
      continue;
    salvageDebugInfo(MRI, *MI);
    for (const MachineOperand &MO : MI->defs()) {
      assert(MRI.use_nodbg_empty(MO.getReg()) && "region value still used");
      MRI.markUsesInDebugValueAsUndef(MO.getReg());
    }
    Erased.insert(MI);
    MI->eraseFromParent();
  }
  for (MachineInstr *Def : ConstDefs) {
    if (!isTriviallyDead(*Def, MRI))
      continue;
    MRI.markUsesInDebugValueAsUndef(Def->getOperand(0).getReg());
    Erased.insert(Def);
    Def->eraseFromParent();
  }

  ++NumApplied;
  CostSaved += OldCost - NewCost;
  numberBlock(MBB);
  return true;
}

bool EGraphCombinerImpl::run() {
  bool Changed = false;
  for (MachineBasicBlock &MBB : MF) {
    numberBlock(MBB);
    SmallVector<MachineInstr *, 64> Snapshot;
    for (MachineInstr &MI : MBB)
      Snapshot.push_back(&MI);
    for (MachineInstr *MI : Snapshot) {
      // An unconditional branch has no operands; it only takes part in a
      // region together with a conditional branch.
      if (Erased.count(MI) || Visited.count(MI) || !isCandidate(*MI, MRI) ||
          MI->getOpcode() == TargetOpcode::G_BR)
        continue;
      Region R = formRegion(*MI);
      Changed |= processRegion(MBB, R);
    }
  }
  return Changed;
}

char GIEGraphCombiner::ID = 0;
INITIALIZE_PASS(GIEGraphCombiner, "gisel-egraph-combiner",
                "Experimental GlobalISel e-graph combiner", false, false)

GIEGraphCombiner::GIEGraphCombiner() : MachineFunctionPass(ID) {
  initializeGIEGraphCombinerPass(*PassRegistry::getPassRegistry());
}

void GIEGraphCombiner::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesCFG();
  getSelectionDAGFallbackAnalysisUsage(AU);
  MachineFunctionPass::getAnalysisUsage(AU);
}

bool GIEGraphCombiner::runOnMachineFunction(MachineFunction &MF) {
  const MachineFunctionProperties &Props = MF.getProperties();
  if (Props.hasProperty(MachineFunctionProperties::Property::FailedISel))
    return false;
  if (PrintOps) {
    static bool Printed = false;
    if (!Printed)
      printOpPropertiesJSON(outs(), PrintOpSamples);
    Printed = true;
  }
  if (PrintRules) {
    static bool Printed = false;
    if (!Printed) {
      for (const RewriteRule &R : getRules()) {
        R.print(errs());
        errs() << "\n";
      }
      errs() << "# Enforced by canonicalization, not applied as rules:\n";
      for (const RewriteRule &R :
           getImplicitPropertyRules(getAllOpProperties())) {
        R.print(errs());
        errs() << "\n";
      }
      Printed = true;
    }
  }
  if (skipFunction(MF.getFunction()))
    return false;
  // The pass has two positions. Before the legalizer it can use every
  // operation that the target implements. After the legalizer it only
  // creates legal operations and constants (see TargetCostModel). It does
  // not rewrite once registers have a register bank.
  bool IsLegalized =
      Props.hasProperty(MachineFunctionProperties::Property::Legalized);
  if (Stages ==
      (IsLegalized ? EGraphStages::PreLegalizer : EGraphStages::PostLegalizer))
    return false;
  bool CanRewrite =
      Mode == EGraphMode::Rewrite &&
      !Props.hasProperty(MachineFunctionProperties::Property::RegBankSelected);
  return EGraphCombinerImpl(MF, CanRewrite, IsLegalized).run();
}
