//===- llvm/CodeGen/GlobalISel/GIEGraphCombiner.cpp - E-graph combiner ----===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// Experimental equality-saturation combiner for scalar integer gMIR. See
/// GIEGraphCombiner.h and llvm/docs/GlobalISel/GIEGraphCombiner-Design.md.
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/GlobalISel/GIEGraphCombiner.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/CodeGen/GlobalISel/GIEGraph.h"
#include "llvm/CodeGen/GlobalISel/MachineIRBuilder.h"
#include "llvm/CodeGen/GlobalISel/Utils.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/PassTimingInfo.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/raw_ostream.h"

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
} // namespace

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
    MachineInstr::Disjoint;

static cl::opt<bool> PrintRules(
    "gisel-egraph-print-rules", cl::Hidden, cl::init(false),
    cl::desc("Print the rewrite rules of the e-graph combiner (one per line, "
             "'name: LHS => RHS') to stderr when the pass first runs"));

static const char *TimerGroupName = "gisel-egraph";
static const char *TimerGroupDesc = "GlobalISel e-graph combiner";

static const std::vector<RewriteRule> &getRules() {
  static const std::vector<RewriteRule> Rules = getDefaultIntegerRules();
  return Rules;
}

static bool isSupportedOpcode(unsigned Opc) {
  switch (Opc) {
  case TargetOpcode::G_ADD:
  case TargetOpcode::G_SUB:
  case TargetOpcode::G_MUL:
  case TargetOpcode::G_AND:
  case TargetOpcode::G_OR:
  case TargetOpcode::G_XOR:
  case TargetOpcode::G_SHL:
  case TargetOpcode::G_LSHR:
  case TargetOpcode::G_ASHR:
    return true;
  default:
    return false;
  }
}

/// A region instruction: a supported, single-def, pure scalar operation whose
/// operands are all virtual registers.
static bool isCandidate(const MachineInstr &MI,
                        const MachineRegisterInfo &MRI) {
  if (!isSupportedOpcode(MI.getOpcode()) || MI.getNumOperands() != 3)
    return false;
  for (const MachineOperand &MO : MI.operands())
    if (!MO.isReg() || !MO.getReg().isVirtual() || MO.isImplicit())
      return false;
  if (!MI.getOperand(0).isDef())
    return false;
  LLT Ty = MRI.getType(MI.getOperand(0).getReg());
  if (!Ty.isScalar() || Ty.getSizeInBits() > 128)
    return false;
  if (MI.getFlags() & ~SemanticFlags)
    return false;
  return true;
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
struct Region {
  SmallVector<MachineInstr *, 32> Instrs; // In block order.
  SmallVector<MachineInstr *, 4> Roots;   // Instructions with external uses.
};

class EGraphCombinerImpl {
public:
  EGraphCombinerImpl(MachineFunction &MF, bool CanRewrite)
      : MF(MF), MRI(MF.getRegInfo()), CanRewrite(CanRewrite) {
    CM.ConstantCost = ConstantCost;
    CM.MulCost = MulCost;
  }

  bool run();

private:
  void numberBlock(MachineBasicBlock &MBB);
  Region formRegion(MachineInstr &Seed);
  bool processRegion(MachineBasicBlock &MBB, Region &R);

  MachineFunction &MF;
  MachineRegisterInfo &MRI;
  bool CanRewrite;
  DefaultCostModel CM;
  DenseMap<const MachineInstr *, unsigned> Order;
  SmallPtrSet<const MachineInstr *, 32> Visited;
  SmallPtrSet<const MachineInstr *, 32> Erased;
};
} // namespace

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
    for (unsigned I = 1; I < 3; ++I) {
      MachineInstr *Def = MRI.getVRegDef(MI->getOperand(I).getReg());
      if (Eligible(Def))
        Work.push_back(Def);
    }
    for (MachineInstr &User :
         MRI.use_nodbg_instructions(MI->getOperand(0).getReg()))
      if (Eligible(&User))
        Work.push_back(&User);
  }

  Region R;
  R.Instrs.assign(In.begin(), In.end());
  llvm::sort(R.Instrs, [&](const MachineInstr *A, const MachineInstr *B) {
    return Order.lookup(A) < Order.lookup(B);
  });
  for (MachineInstr *MI : R.Instrs) {
    Visited.insert(MI);
    bool External =
        any_of(MRI.use_nodbg_instructions(MI->getOperand(0).getReg()),
               [&](MachineInstr &U) { return !In.contains(&U); });
    if (External)
      R.Roots.push_back(MI);
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
  DenseMap<Register, EClassId> RegClass;
  SmallVector<Register, 8> InputRegs;
  SmallSetVector<MachineInstr *, 4> ConstDefs;
  uint64_t OldCost = 0;
  {
    NamedRegionTimer T("build", "Build e-graph", TimerGroupName, TimerGroupDesc,
                       TimePassesIsEnabled);
    for (MachineInstr *MI : R.Instrs) {
      SmallVector<EClassId, 2> Ops;
      for (unsigned I = 1; I < 3; ++I) {
        Register Reg = MI->getOperand(I).getReg();
        auto It = RegClass.find(Reg);
        if (It != RegClass.end()) {
          Ops.push_back(It->second);
          continue;
        }
        EClassId Id;
        if (std::optional<APInt> C = getIConstantVRegVal(Reg, MRI)) {
          Id = G.addConstant(MRI.getType(Reg), *C);
          ConstDefs.insert(MRI.getVRegDef(Reg));
        } else {
          Id = G.addInput(getInputInfo(Reg, MRI));
          InputRegs.push_back(Reg);
        }
        RegClass[Reg] = Id;
        Ops.push_back(Id);
      }
      Register Dst = MI->getOperand(0).getReg();
      ENode N = ENode::makeOp(MI->getOpcode(), MRI.getType(Dst), Ops,
                              MI->getFlags() & SemanticFlags);
      OldCost += std::max(1u, CM.getNodeCost(N));
      RegClass[Dst] = G.add(std::move(N));
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
  for (MachineInstr *Root : R.Roots)
    RootClasses.push_back(RegClass.lookup(Root->getOperand(0).getReg()));
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
        const MachineInstr *Def = MRI.getVRegDef(InputRegs[N->InputIdx]);
        if (!Def || (Def->getParent() == &MBB && Order.lookup(Def) >= Pos)) {
          Blocker = "dominance";
          return false;
        }
      }
      for (EClassId Op : N->Ops)
        if (!Check(Op, Pos))
          return false;
      OnStack.erase(Rc);
      Done.insert(Rc);
      return true;
    };
    for (unsigned I = 0, End = R.Roots.size(); I != End; ++I)
      if (!Check(RootClasses[I], Order.lookup(R.Roots[I])))
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
    for (MachineInstr *Root : R.Roots)
      if (MRI.getRegClassOrRegBank(Root->getOperand(0).getReg()))
        DoRewrite = false, Blocker = "reg-attrs";

  if (Report) {
    raw_ostream &OS = errs();
    const TargetRegisterInfo *TRI = MF.getSubtarget().getRegisterInfo();
    OS << "GIEGraph: " << MF.getName() << ": " << printMBBReference(MBB)
       << ": instrs=" << R.Instrs.size() << " roots=" << R.Roots.size()
       << " inputs=" << InputRegs.size() << " nodes=" << OrigNodes << "->"
       << G.getNumNodes() << " classes=" << G.getNumClasses()
       << " iters=" << S.Iterations << " "
       << (S.Saturated       ? "saturated"
           : S.HitNodeLimit  ? "node-limit"
           : S.HitMatchLimit ? "match-limit"
                             : "iteration-limit")
       << " merges=" << S.Merges << " ac-merges=" << S.ACMerges
       << " refinements=" << S.Refinements << " unsafe=" << S.RejectedUnsafe
       << " cost=" << OldCost << "->" << NewCost
       << (Profitable ? " profitable" : " not-profitable");
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
        OS << "  root " << printReg(R.Roots[I]->getOperand(0).getReg(), TRI)
           << " = ";
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

  if (!DoRewrite)
    return false;

  // 5. Emit the extracted expressions. Each root's expression is emitted
  // immediately before the original root instruction; classes shared with
  // earlier roots are reused.
  MachineIRBuilder B(MF);
  DenseMap<EClassId, Register> Mat;
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
    case ENodeKind::Constant:
      Res = B.buildConstant(N->Ty, N->Imm).getReg(0);
      break;
    case ENodeKind::Operation: {
      SmallVector<EClassId, 2> Ops(N->Ops.begin(), N->Ops.end());
      // Operands of commutative nodes are ordered by class id; emit them in
      // GlobalISel's canonical form instead (constant on the right).
      const OpProperties *P = getOpProperties(N->Opcode);
      if (P && P->Commutative && Ops.size() == 2 &&
          E.getChosenNode(Ops[0])->isConstant() &&
          !E.getChosenNode(Ops[1])->isConstant())
        std::swap(Ops[0], Ops[1]);
      SmallVector<SrcOp, 2> Srcs;
      for (EClassId Op : Ops)
        Srcs.push_back(Materialize(Op));
      Res = B.buildInstr(N->Opcode, {N->Ty}, Srcs, N->Flags).getReg(0);
      break;
    }
    }
    Mat[Rc] = Res;
    return Res;
  };

  SmallVector<std::pair<Register, Register>, 4> Replacements;
  for (unsigned I = 0, End = R.Roots.size(); I != End; ++I) {
    MachineInstr *Root = R.Roots[I];
    B.setInstrAndDebugLoc(*Root);
    Replacements.push_back(
        {Root->getOperand(0).getReg(), Materialize(RootClasses[I])});
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

  // 6. Erase the old region (users before definitions).
  for (MachineInstr *MI : reverse(R.Instrs)) {
    Register Def = MI->getOperand(0).getReg();
    assert(MRI.use_nodbg_empty(Def) && "region value still used");
    salvageDebugInfo(MRI, *MI);
    MRI.markUsesInDebugValueAsUndef(Def);
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
      if (Erased.count(MI) || Visited.count(MI) || !isCandidate(*MI, MRI))
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
  // Rewriting is only done before legalization: the extracted expression may
  // use operations that are not legal for the target.
  bool CanRewrite =
      Mode == EGraphMode::Rewrite &&
      !Props.hasProperty(MachineFunctionProperties::Property::Legalized) &&
      !Props.hasProperty(MachineFunctionProperties::Property::RegBankSelected);
  return EGraphCombinerImpl(MF, CanRewrite).run();
}
