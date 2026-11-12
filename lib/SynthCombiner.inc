//===- SynthCombiner.inc - Combiner pass of synthesized rules ---*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// The body of a combiner pass that runs the synthesized rules of one target.
// The including file defines:
//   SYNTH_GEN_INC     the file that llvm-tblgen writes for the combiner
//   SYNTH_IMPL        the combiner class name of the GICombiner record
//   SYNTH_RULE_CONFIG SYNTH_IMPL followed by RuleConfig
//   SYNTH_PASS        the class name of the legacy pass
//   SYNTH_PASS_ARG    the pass argument (-run-pass name)
//   SYNTH_PASS_DESC   the pass description
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GISynthPredicates.h"
#include "llvm/CodeGen/GlobalISel/CSEInfo.h"
#include "llvm/CodeGen/GlobalISel/Combiner.h"
#include "llvm/CodeGen/GlobalISel/CombinerHelper.h"
#include "llvm/CodeGen/GlobalISel/CombinerInfo.h"
#include "llvm/CodeGen/GlobalISel/GIMatchTableExecutorImpl.h"
#include "llvm/CodeGen/GlobalISel/GISelValueTracking.h"
#include "llvm/CodeGen/GlobalISel/LegalizerInfo.h"
#include "llvm/CodeGen/GlobalISel/MIPatternMatch.h"
#include "llvm/CodeGen/GlobalISel/Utils.h"
#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/InitializePasses.h"
#include "llvm/Target/TargetMachine.h"

#define GET_GICOMBINER_DEPS
#include SYNTH_GEN_INC
#undef GET_GICOMBINER_DEPS

using namespace llvm;
using namespace MIPatternMatch;

namespace {

// The combiner emitter names the subtarget type after the target record
// (GISynth). The rules have no subtarget predicate.
using GISynthSubtarget = TargetSubtargetInfo;

#define GET_GICOMBINER_TYPES
#include SYNTH_GEN_INC
#undef GET_GICOMBINER_TYPES

class SYNTH_IMPL : public Combiner {
protected:
  const SYNTH_RULE_CONFIG &RuleConfig;
  const TargetSubtargetInfo &STI;
  const CombinerHelper Helper;

public:
  SYNTH_IMPL(MachineFunction &MF, CombinerInfo &CInfo, GISelValueTracking &VT,
             GISelCSEInfo *CSEInfo, const SYNTH_RULE_CONFIG &RuleConfig,
             MachineDominatorTree *MDT, const LegalizerInfo *LI);

  static const char *getName() { return SYNTH_PASS_DESC; }

  bool tryCombineAll(MachineInstr &I) const override;

private:
#define GET_GICOMBINER_CLASS_MEMBERS
#include SYNTH_GEN_INC
#undef GET_GICOMBINER_CLASS_MEMBERS
};

#define GET_GICOMBINER_IMPL
#include SYNTH_GEN_INC
#undef GET_GICOMBINER_IMPL

SYNTH_IMPL::SYNTH_IMPL(MachineFunction &MF, CombinerInfo &CInfo,
                       GISelValueTracking &VT, GISelCSEInfo *CSEInfo,
                       const SYNTH_RULE_CONFIG &RuleConfig,
                       MachineDominatorTree *MDT, const LegalizerInfo *LI)
    : Combiner(MF, CInfo, &VT, CSEInfo), RuleConfig(RuleConfig),
      STI(MF.getSubtarget()),
      Helper(Observer, B, /*IsPreLegalize=*/true, &VT, MDT, LI),
#define GET_GICOMBINER_CONSTRUCTOR_INITS
#include SYNTH_GEN_INC
#undef GET_GICOMBINER_CONSTRUCTOR_INITS
{
}

class SYNTH_PASS : public MachineFunctionPass {
public:
  static char ID;

  SYNTH_PASS() : MachineFunctionPass(ID) {
    if (!RuleConfig.parseCommandLineOption())
      reportFatalUsageError("invalid rule identifier");
  }

  StringRef getPassName() const override { return SYNTH_PASS_DESC; }

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
    // The same settings as the pre-legalizer combiners of AMDGPU and
    // AArch64, which hosted these rules before.
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
    SYNTH_IMPL Impl(MF, CInfo, *VT, CSEInfo, RuleConfig, MDT,
                    MF.getSubtarget().getLegalizerInfo());
    return Impl.combineMachineInstrs();
  }

private:
  SYNTH_RULE_CONFIG RuleConfig;
};

} // end anonymous namespace

char SYNTH_PASS::ID = 0;
