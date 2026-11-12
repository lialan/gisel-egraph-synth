//===- PassRegistration.cpp - Passes of the llc of this project -----------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Linked into bin/llc of this project, which is the stock llc driver of the
// LLVM submodule with these passes added. (The stock llc loads pass plugins
// only after it parses the command line, so the options below could not be
// given to a plugin.) This file registers the passes and adds them to the
// codegen pipeline of a target when an option asks for them. It needs no
// change to LLVM: a TargetPassConfig callback runs before the target adds its
// passes, and TargetPassConfig::insertPass puts a pass after a pass of the
// target.
//
//   AMDGPU, after amdgpu-prelegalizer-combiner, in this order:
//     -amdgpu-gisel-synth-combines   the synthesized rules
//     -amdgpu-gisel-egraph           the e-graph combiner
//     -amdgpu-gisel-synth-corpus     the corpus extractor
//   AMDGPU, after amdgpu-postlegalizer-combiner:
//     -amdgpu-gisel-egraph           the e-graph combiner (legal operations)
//   AArch64, after aarch64-prelegalizer-combiner:
//     -aarch64-gisel-synth-combines  the synthesized rules
//
// The combiners do not run at -O0. The passes are also available to
// -run-pass: gisel-egraph-combiner, gisel-synth-corpus,
// gisynth-amdgpu-combiner and gisynth-aarch64-combiner.
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GIEGraphCombiner.h"
#include "GISelEGraphSynth/GISynthCorpusExtractor.h"
#include "GISelEGraphSynth/SynthCombiners.h"
#include "llvm/CodeGen/TargetPassConfig.h"
#include "llvm/PassRegistry.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Target/RegisterTargetPassConfigCallback.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/TargetParser/Triple.h"

using namespace llvm;

static void registerPassConfigCallback();

/// Each option that adds a pass registers the TargetPassConfig callback when
/// the command line is parsed, in main. A static callback object would not
/// do: the callback list of LLVM is a global that can be constructed after
/// the static objects of this file, and then it drops the entry.
static void onPipelineOption(const bool &Value) {
  if (Value)
    registerPassConfigCallback();
}

static cl::opt<bool> EnableAMDGPUSynthCombines(
    "amdgpu-gisel-synth-combines", cl::Hidden, cl::init(false),
    cl::callback([](const bool &V) { onPipelineOption(V); }),
    cl::desc("Run the synthesized GlobalISel combine rules of AMDGPU after "
             "the pre-legalizer combiner"));

static cl::opt<bool> EnableAArch64SynthCombines(
    "aarch64-gisel-synth-combines", cl::Hidden, cl::init(false),
    cl::callback([](const bool &V) { onPipelineOption(V); }),
    cl::desc("Run the synthesized GlobalISel combine rules of AArch64 after "
             "the pre-legalizer combiner"));

static cl::opt<bool> EnableAMDGPUEGraph(
    "amdgpu-gisel-egraph", cl::Hidden, cl::init(false),
    cl::callback([](const bool &V) { onPipelineOption(V); }),
    cl::desc("Run the experimental GlobalISel e-graph combiner after the "
             "pre-legalizer and the post-legalizer combiners"));

static cl::opt<bool> EnableAMDGPUSynthCorpus(
    "amdgpu-gisel-synth-corpus", cl::Hidden, cl::init(false),
    cl::callback([](const bool &V) { onPipelineOption(V); }),
    cl::desc("Write the GlobalISel rule synthesizer corpus after the "
             "pre-legalizer combiner (see -gisel-synth-corpus-out)"));

/// The ID of the registered pass with the argument \p Arg.
static AnalysisID getPassIDOrFail(StringRef Arg) {
  const PassInfo *PI = PassRegistry::getPassRegistry()->getPassInfo(Arg);
  if (!PI)
    reportFatalUsageError(Twine("gisel-egraph-synth: no pass '") + Arg +
                          "' to insert after");
  return PI->getTypeInfo();
}

static void addPasses(TargetMachine &TM, PassManagerBase &,
                      TargetPassConfig *PassConfig) {
  bool IsOptNone = TM.getOptLevel() == CodeGenOptLevel::None;
  const Triple &TT = TM.getTargetTriple();
  if (TT.isAMDGCN()) {
    bool Synth = EnableAMDGPUSynthCombines && !IsOptNone;
    bool EGraph = EnableAMDGPUEGraph && !IsOptNone;
    if (Synth || EGraph || EnableAMDGPUSynthCorpus) {
      AnalysisID Pre = getPassIDOrFail("amdgpu-prelegalizer-combiner");
      if (Synth)
        PassConfig->insertPass(Pre, getGISynthAMDGPUCombinerID());
      if (EGraph)
        PassConfig->insertPass(Pre, &GIEGraphCombiner::ID);
      if (EnableAMDGPUSynthCorpus)
        PassConfig->insertPass(Pre, &GISynthCorpusExtractor::ID);
    }
    if (EGraph)
      PassConfig->insertPass(getPassIDOrFail("amdgpu-postlegalizer-combiner"),
                             &GIEGraphCombiner::ID);
    return;
  }
  if (TT.isAArch64() && EnableAArch64SynthCombines && !IsOptNone)
    PassConfig->insertPass(getPassIDOrFail("aarch64-prelegalizer-combiner"),
                           getGISynthAArch64CombinerID());
}

namespace {
struct PassRegistration {
  PassRegistration() {
    PassRegistry &Registry = *PassRegistry::getPassRegistry();
    initializeGIEGraphCombinerPass(Registry);
    initializeGISynthCorpusExtractorPass(Registry);
    initializeGISynthAMDGPUCombinerLegacyPass(Registry);
    initializeGISynthAArch64CombinerLegacyPass(Registry);
  }
};
} // end anonymous namespace

static PassRegistration Registration;

static void registerPassConfigCallback() {
  static RegisterTargetPassConfigCallback Callback(addPasses);
}
