//===- GISynthRegionExtractor.cpp - Region DAGs of the joint search -------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Writes one typed SSA region DAG per basic block for the joint region search
// of tools/gisel-rule-synth (girs/joint.py, docs/Joint-Regions.md). A pass of
// its own, next to the corpus extractor (whose records it does not change):
// -gisel-synth-joint-regions inserts it after the pre-legalizer combiner of
// AMDGPU and AArch64, and -gisel-synth-region-out names the output file.
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GISynthRegionExtractor.h"
#include "GISelEGraphSynth/GIEGraph.h"
#include "GISelEGraphSynth/GISynthJoint.h"
#include "GISelEGraphSynth/GISynthPredicates.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/CodeGen/GlobalISel/GISelValueTracking.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"

#define DEBUG_TYPE "gisel-synth-regions"

using namespace llvm;

STATISTIC(NumRegionsWritten, "Number of region DAGs written");

static cl::opt<std::string> RegionOut(
    "gisel-synth-region-out", cl::Hidden, cl::init("-"),
    cl::desc("JSON-lines output file of the region DAGs of the pure scalar "
             "integer instructions of each basic block ('-' = stdout; "
             "tools/gisel-rule-synth/girs/joint.py)"));

static cl::opt<unsigned> RegionMaxInstrs(
    "gisel-synth-region-max-instrs", cl::Hidden, cl::init(256),
    cl::desc("Maximum number of instructions of one region record; a longer "
             "block is written as several records"));

namespace {

std::string hex(const APInt &V) { return "0x" + toString(V, 16, false); }

std::string regName(Register R) { return "%" + utostr(R.virtRegIndex()); }

/// The index of the result \p R of \p MI.
unsigned defIndex(const MachineInstr &MI, Register R) {
  for (unsigned I = 0, E = MI.getNumExplicitDefs(); I != E; ++I)
    if (MI.getOperand(I).getReg() == R)
      return I;
  llvm_unreachable("the register is not a result of the instruction");
}

std::string typeName(LLT Ty) {
  std::string Name;
  raw_string_ostream OS(Name);
  OS << Ty;
  return Name;
}

//===--- Region DAGs (girs/joint.py) ---------------------------------------===//

/// True if \p MI is an instruction of a region DAG: a generic operator on
/// scalar integers of at most 64 bits, without memory, control flow or
/// floating-point semantics, whose only operands are virtual registers, the
/// predicate of a G_ICMP and the immediate of G_SEXT_INREG. The synthesizer
/// decides from its registry which of them it has a model for.
bool isRegionInstr(const MachineRegisterInfo &MRI, const MachineInstr &MI) {
  switch (MI.getOpcode()) {
  case TargetOpcode::G_ADD:
  case TargetOpcode::G_SUB:
  case TargetOpcode::G_MUL:
  case TargetOpcode::G_AND:
  case TargetOpcode::G_OR:
  case TargetOpcode::G_XOR:
  case TargetOpcode::G_SHL:
  case TargetOpcode::G_LSHR:
  case TargetOpcode::G_ASHR:
  case TargetOpcode::G_TRUNC:
  case TargetOpcode::G_ZEXT:
  case TargetOpcode::G_SEXT:
  case TargetOpcode::G_SEXT_INREG:
  case TargetOpcode::G_ICMP:
  case TargetOpcode::G_SELECT:
  case TargetOpcode::G_FREEZE:
  case TargetOpcode::G_SMIN:
  case TargetOpcode::G_SMAX:
  case TargetOpcode::G_UMIN:
  case TargetOpcode::G_UMAX:
  case TargetOpcode::G_ABS:
  case TargetOpcode::G_UMULH:
  case TargetOpcode::G_SMULH:
  case TargetOpcode::G_UADDO:
  case TargetOpcode::G_USUBO:
  case TargetOpcode::G_SADDO:
  case TargetOpcode::G_SSUBO:
    break;
  default:
    return false;
  }
  if (MI.getNumExplicitDefs() == 0)
    return false;
  for (const MachineOperand &MO : MI.operands()) {
    if (MO.isReg()) {
      if (MO.isImplicit() || !MO.getReg().isVirtual())
        return false;
      LLT Ty = MRI.getType(MO.getReg());
      if (!Ty.isValid() || !Ty.isScalar() || Ty.isFloat() ||
          Ty.getSizeInBits() > 64)
        return false;
      continue;
    }
    if (MO.isPredicate() && MI.getOpcode() == TargetOpcode::G_ICMP)
      continue;
    if (MO.isImm() && MI.getOpcode() == TargetOpcode::G_SEXT_INREG)
      continue;
    return false;
  }
  return true;
}

/// Writes the region DAGs of \p MBB: the instructions of isRegionInstr in
/// the order of the block, at most RegionMaxInstrs per record. Each value
/// has an identity: an instruction and a result index (a "node"), or an
/// input of the record (a register that no instruction of the record
/// defines). For each result the record has the number of its users (each
/// operand that reads it; debug uses do not count), so that the synthesizer
/// knows the users outside any part of the region; its known bits; and the
/// fact "defined" of gisynth::joint::isStableValue, the function that the
/// guard of a joint rule calls.
void writeRegions(raw_ostream &OS, const MachineFunction &MF,
                  const MachineBasicBlock &MBB,
                  const MachineRegisterInfo &MRI, GISelValueTracking &VT) {
  bool ArgsNoUndef = !MF.getFunction().isVarArg() &&
                     all_of(MF.getFunction().args(), [](const Argument &A) {
                       return A.hasAttribute(Attribute::NoUndef);
                     });
  DenseMap<const MachineInstr *, int> Pos;
  SmallVector<const MachineInstr *, 64> Instrs;
  int P = 0;
  for (const MachineInstr &MI : MBB) {
    if (MI.isDebugInstr())
      continue;
    Pos[&MI] = P++;
    if (isRegionInstr(MRI, MI))
      Instrs.push_back(&MI);
  }
  auto Opc = [](const MachineInstr &MI) {
    const TargetInstrInfo *TII = MI.getMF()->getSubtarget().getInstrInfo();
    return std::string(TII->getName(MI.getOpcode()));
  };
  auto Value = [&](json::OStream &J, Register R) {
    LLT Ty = MRI.getType(R);
    KnownBits KB = VT.getKnownBits(R);
    J.attribute("reg", regName(R));
    J.attribute("w", int64_t(Ty.getSizeInBits().getFixedValue()));
    J.attribute("type", typeName(Ty));
    J.attribute("zero", hex(KB.Zero));
    J.attribute("one", hex(KB.One));
    J.attribute("defined", gisynth::joint::isStableValue(R, MRI));
    J.attribute("noundef", gisynth::isDefinedValue(R, MRI));
  };
  for (size_t Start = 0, Chunk = 0; Start < Instrs.size();
       Start += RegionMaxInstrs, ++Chunk) {
    ArrayRef<const MachineInstr *> Part =
        ArrayRef(Instrs).slice(Start, std::min<size_t>(RegionMaxInstrs,
                                                       Instrs.size() - Start));
    DenseMap<const MachineInstr *, unsigned> Node;
    for (auto [I, MI] : enumerate(Part))
      Node[MI] = I;
    DenseMap<Register, unsigned> InputIdx;
    SmallVector<Register, 16> Inputs;
    for (const MachineInstr *MI : Part)
      for (const MachineOperand &MO : MI->uses())
        if (MO.isReg()) {
          const MachineInstr *Def = MRI.getVRegDef(MO.getReg());
          if ((!Def || !Node.count(Def)) &&
              InputIdx.try_emplace(MO.getReg(), Inputs.size()).second)
            Inputs.push_back(MO.getReg());
        }
    json::OStream J(OS);
    J.object([&] {
      J.attribute("kind", "region");
      J.attribute("fn", MF.getName());
      J.attribute("bb", MBB.getNumber());
      J.attribute("chunk", int64_t(Chunk));
      J.attribute("args_noundef", ArgsNoUndef);
      J.attributeArray("inputs", [&] {
        for (Register R : Inputs)
          J.object([&] {
            Value(J, R);
            const MachineInstr *Def = MRI.getVRegDef(R);
            J.attribute("def", Def ? Opc(*Def) : std::string("<none>"));
            J.attribute("pos", Def && Def->getParent() == &MBB
                                   ? int64_t(Pos.lookup(Def))
                                   : int64_t(-1));
            J.attribute("uses", int64_t(std::distance(MRI.use_nodbg_begin(R),
                                                      MRI.use_nodbg_end())));
            if (std::optional<APInt> C = gisynth::getConstantBits(R, MRI))
              J.attribute("const", hex(*C));
          });
      });
      J.attributeArray("instrs", [&] {
        for (const MachineInstr *MI : Part)
          J.object([&] {
            J.attribute("op", Opc(*MI));
            if (MI->getOpcode() == TargetOpcode::G_ICMP)
              J.attribute("pred", egraph::getComparePredicateName(
                                      MI->getOperand(1).getPredicate()));
            if (MI->getOpcode() == TargetOpcode::G_SEXT_INREG)
              J.attribute("imm", MI->getOperand(2).getImm());
            J.attribute("pos", int64_t(Pos.lookup(MI)));
            J.attributeArray("flags", [&] {
              if (MI->getFlag(MachineInstr::NoUWrap))
                J.value("nuw");
              if (MI->getFlag(MachineInstr::NoSWrap))
                J.value("nsw");
              if (MI->getFlag(MachineInstr::IsExact))
                J.value("exact");
              if (MI->getFlag(MachineInstr::Disjoint))
                J.value("disjoint");
              if (MI->getFlag(MachineInstr::NonNeg))
                J.value("nneg");
              if (MI->getFlag(MachineInstr::SameSign))
                J.value("samesign");
            });
            J.attributeArray("defs", [&] {
              for (const MachineOperand &MO : MI->defs())
                J.object([&] {
                  Value(J, MO.getReg());
                  J.attribute("uses", int64_t(std::distance(
                                          MRI.use_nodbg_begin(MO.getReg()),
                                          MRI.use_nodbg_end())));
                });
            });
            J.attributeArray("args", [&] {
              for (const MachineOperand &MO : MI->uses()) {
                if (!MO.isReg())
                  continue;
                const MachineInstr *Def = MRI.getVRegDef(MO.getReg());
                J.object([&] {
                  if (Def && Node.count(Def)) {
                    J.attribute("node", Node.lookup(Def));
                    J.attribute("res", int64_t(defIndex(*Def, MO.getReg())));
                  } else {
                    J.attribute("in", InputIdx.lookup(MO.getReg()));
                  }
                });
              }
            });
          });
      });
    });
    OS << "\n";
    ++NumRegionsWritten;
  }
}

raw_ostream &getRegionStream() {
  if (RegionOut == "-")
    return outs();
  static std::unique_ptr<raw_fd_ostream> OS;
  if (!OS) {
    std::error_code EC;
    OS = std::make_unique<raw_fd_ostream>(RegionOut, EC, sys::fs::OF_Text);
    if (EC)
      report_fatal_error("cannot open " + Twine(RegionOut) + ": " +
                         EC.message());
  }
  return *OS;
}

} // end anonymous namespace

char GISynthRegionExtractor::ID = 0;
INITIALIZE_PASS_BEGIN(GISynthRegionExtractor, DEBUG_TYPE,
                      "Region DAGs of the joint region search", false, true)
INITIALIZE_PASS_DEPENDENCY(GISelValueTrackingAnalysisLegacy)
INITIALIZE_PASS_END(GISynthRegionExtractor, DEBUG_TYPE,
                    "Region DAGs of the joint region search", false, true)

GISynthRegionExtractor::GISynthRegionExtractor() : MachineFunctionPass(ID) {
  initializeGISynthRegionExtractorPass(*PassRegistry::getPassRegistry());
}

void GISynthRegionExtractor::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<GISelValueTrackingAnalysisLegacy>();
  MachineFunctionPass::getAnalysisUsage(AU);
}

bool GISynthRegionExtractor::runOnMachineFunction(MachineFunction &MF) {
  if (MF.getProperties().hasFailedISel())
    return false;
  const MachineRegisterInfo &MRI = MF.getRegInfo();
  GISelValueTracking &VT =
      getAnalysis<GISelValueTrackingAnalysisLegacy>().get(MF);
  raw_ostream &OS = getRegionStream();
  for (const MachineBasicBlock &MBB : MF)
    writeRegions(OS, MF, MBB, MRI, VT);
  OS.flush();
  return false;
}
