//===- SynthJointCombiner.cpp - Combiner of the joint region rules --------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// A GlobalISel combiner with the joint region rules of the synthesizer only
// (lib/SynthJointCombiner.td). -gisel-synth-joint-combines inserts it after
// the pre-legalizer combiner of AMDGPU and of AArch64.
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GISynthJoint.h"
#include "GISelEGraphSynth/SynthCombiners.h"
#include "llvm/CodeGen/GlobalISel/CSEInfo.h"
#include "llvm/CodeGen/GlobalISel/Combiner.h"
#include "llvm/CodeGen/GlobalISel/CombinerHelper.h"
#include "llvm/CodeGen/GlobalISel/CombinerInfo.h"
#include "llvm/CodeGen/GlobalISel/GIMatchTableExecutorImpl.h"
#include "llvm/CodeGen/GlobalISel/GISelValueTracking.h"
#include "llvm/CodeGen/GlobalISel/LegalizerInfo.h"
#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Target/TargetMachine.h"

#define DEBUG_TYPE "gisynth-joint-combiner"

// The descriptions and the match / apply functions of the rules.
#include "GISelEGraphSynth/GISynthJointRules.inc"

#define GET_GICOMBINER_DEPS
#include "GISynthJointCombiner.inc"
#undef GET_GICOMBINER_DEPS

using namespace llvm;

static cl::opt<bool> JointScreen(
    "gisel-synth-joint-screen",
    cl::desc("Report each match of the joint rules (-debug-only="
             "gisel-synth-joint); only rules in screen-apply may rewrite "
             "(measurement only)"),
    cl::init(false), cl::Hidden);

static cl::list<std::string> JointScreenApply(
    "gisel-synth-joint-screen-apply",
    cl::desc("Baseline joint rules allowed to apply during screening"),
    cl::CommaSeparated, cl::Hidden);

namespace {

using GISynthJointSubtarget = TargetSubtargetInfo;

#define GET_GICOMBINER_TYPES
#include "GISynthJointCombiner.inc"
#undef GET_GICOMBINER_TYPES

class GISynthJointCombinerImpl : public Combiner {
protected:
  const GISynthJointCombinerImplRuleConfig &RuleConfig;
  const TargetSubtargetInfo &STI;
  const CombinerHelper Helper;
  /// What the matchers of the rules read (GISynthJoint.h): the first virtual
  /// register that this run of the combiner creates, and screening.
  gisynth::joint::MatchEnv JointEnv;

public:
  GISynthJointCombinerImpl(MachineFunction &MF, CombinerInfo &CInfo,
                           GISelValueTracking &VT, GISelCSEInfo *CSEInfo,
                           const GISynthJointCombinerImplRuleConfig &RuleConfig,
                           MachineDominatorTree *MDT, const LegalizerInfo *LI);

  static const char *getName() { return "GISynthJointCombiner"; }

  bool tryCombineAll(MachineInstr &I) const override;

private:
#define GET_GICOMBINER_CLASS_MEMBERS
#include "GISynthJointCombiner.inc"
#undef GET_GICOMBINER_CLASS_MEMBERS
};

#define GET_GICOMBINER_IMPL
#include "GISynthJointCombiner.inc"
#undef GET_GICOMBINER_IMPL

GISynthJointCombinerImpl::GISynthJointCombinerImpl(
    MachineFunction &MF, CombinerInfo &CInfo, GISelValueTracking &VT,
    GISelCSEInfo *CSEInfo, const GISynthJointCombinerImplRuleConfig &RuleConfig,
    MachineDominatorTree *MDT, const LegalizerInfo *LI)
    : Combiner(MF, CInfo, &VT, CSEInfo), RuleConfig(RuleConfig),
      STI(MF.getSubtarget()),
      Helper(Observer, B, /*IsPreLegalize=*/true, &VT, MDT, LI),
#define GET_GICOMBINER_CONSTRUCTOR_INITS
#include "GISynthJointCombiner.inc"
#undef GET_GICOMBINER_CONSTRUCTOR_INITS
{
  JointEnv.FirstNewVReg = MF.getRegInfo().getNumVirtRegs();
  JointEnv.ScreenOnly = JointScreen;
  JointEnv.ScreenApply = JointScreenApply;
}

class GISynthJointCombinerLegacy : public MachineFunctionPass {
public:
  static char ID;

  GISynthJointCombinerLegacy() : MachineFunctionPass(ID) {
    if (!RuleConfig.parseCommandLineOption())
      reportFatalUsageError("invalid rule identifier");
  }

  StringRef getPassName() const override { return "GISynthJointCombiner"; }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<TargetPassConfig>();
    AU.setPreservesCFG();
    getSelectionDAGFallbackAnalysisUsage(AU);
    AU.addRequired<GISelValueTrackingAnalysisLegacy>();
    AU.addPreserved<GISelValueTrackingAnalysisLegacy>();
    AU.addRequired<MachineDominatorTreeWrapperPass>();
    AU.addPreserved<MachineDominatorTreeWrapperPass>();
    AU.addRequired<GISelCSEAnalysisWrapperPass>();
    AU.addPreserved<GISelCSEAnalysisWrapperPass>();
    MachineFunctionPass::getAnalysisUsage(AU);
  }

  bool runOnMachineFunction(MachineFunction &MF) override {
    if (MF.getProperties().hasFailedISel())
      return false;
    const Function &F = MF.getFunction();
    bool EnableOpt = MF.getTarget().getOptLevel() != CodeGenOptLevel::None &&
                     !skipFunction(F);
    if (!EnableOpt)
      return false;
    // The settings of the combiners of the other synthesized rules.
    CombinerInfo CInfo(/*AllowIllegalOps=*/true,
                       /*ShouldLegalizeIllegal=*/false,
                       /*LegalizerInfo=*/nullptr, EnableOpt, F.hasOptSize(),
                       F.hasMinSize());
    CInfo.MaxIterations = 1;
    CInfo.ObserverLvl = CombinerInfo::ObserverLevel::SinglePass;
    CInfo.EnableFullDCE = true;
    GISelCSEAnalysisWrapper &Wrapper =
        getAnalysis<GISelCSEAnalysisWrapperPass>().getCSEWrapper();
    GISelCSEInfo *CSEInfo =
        &Wrapper.get(getAnalysis<TargetPassConfig>().getCSEConfig());
    GISelValueTracking *VT =
        &getAnalysis<GISelValueTrackingAnalysisLegacy>().get(MF);
    MachineDominatorTree *MDT =
        &getAnalysis<MachineDominatorTreeWrapperPass>().getDomTree();
    GISynthJointCombinerImpl Impl(MF, CInfo, *VT, CSEInfo, RuleConfig, MDT,
                                  MF.getSubtarget().getLegalizerInfo());
    return Impl.combineMachineInstrs();
  }

private:
  GISynthJointCombinerImplRuleConfig RuleConfig;
};

} // end anonymous namespace

char GISynthJointCombinerLegacy::ID = 0;

INITIALIZE_PASS_BEGIN(GISynthJointCombinerLegacy, DEBUG_TYPE,
                      "Combine with the joint region rules", false, false)
INITIALIZE_PASS_DEPENDENCY(TargetPassConfig)
INITIALIZE_PASS_DEPENDENCY(GISelValueTrackingAnalysisLegacy)
INITIALIZE_PASS_DEPENDENCY(MachineDominatorTreeWrapperPass)
INITIALIZE_PASS_DEPENDENCY(GISelCSEAnalysisWrapperPass)
INITIALIZE_PASS_END(GISynthJointCombinerLegacy, DEBUG_TYPE,
                    "Combine with the joint region rules", false, false)

const void *llvm::getGISynthJointCombinerID() {
  return &GISynthJointCombinerLegacy::ID;
}
