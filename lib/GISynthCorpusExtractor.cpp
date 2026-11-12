//===- GISynthCorpusExtractor.cpp - Corpus for the rule synthesizer ------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Writes small gMIR expression trees and their GISelValueTracking known bits
// to a JSON-lines file for llvm/utils/gisel-rule-synth. See the header for an
// overview and llvm/utils/gisel-rule-synth/README.md for the record format.
//
//===----------------------------------------------------------------------===//

#include "llvm/CodeGen/GlobalISel/GISynthCorpusExtractor.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/CodeGen/GlobalISel/GIEGraph.h"
#include "llvm/CodeGen/GlobalISel/GISelValueTracking.h"
#include "llvm/CodeGen/GlobalISel/GISynthPredicates.h"
#include "llvm/CodeGen/GlobalISel/LegalizerInfo.h"
#include "llvm/CodeGen/GlobalISel/Utils.h"
#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"

#define DEBUG_TYPE "gisel-synth-corpus"

using namespace llvm;

STATISTIC(NumTreesWritten, "Number of expression trees written");

static cl::opt<std::string>
    CorpusOut("gisel-synth-corpus-out", cl::Hidden, cl::init("-"),
              cl::desc("JSON-lines output file of the GlobalISel rule "
                       "synthesizer corpus extractor ('-' = stdout)"));

static cl::opt<unsigned> MaxDepth(
    "gisel-synth-corpus-max-depth", cl::Hidden, cl::init(2),
    cl::desc("Maximum depth of an extracted expression tree (1 = the root "
             "instruction with leaf operands)"));

static cl::opt<unsigned> MaxTreesPerRoot(
    "gisel-synth-corpus-max-trees", cl::Hidden, cl::init(16),
    cl::desc("Maximum number of expression trees written per root "
             "instruction"));

static cl::opt<unsigned> MaxLanes(
    "gisel-synth-corpus-max-lanes", cl::Hidden, cl::init(16),
    cl::desc("Maximum number of lanes of a fixed vector that is a value of "
             "an extracted expression tree"));

static cl::opt<std::string> LegalityOut(
    "gisel-synth-legality", cl::Hidden,
    cl::desc("Also write the action of the legalizer for each operator of "
             "the e-graph operator table and each combination of scalar "
             "widths to this JSON file"));

namespace {

/// The entry of the operator table of the e-graph combiner for \p Opc, or
/// null if an instruction with this opcode cannot be a node of a tree. The
/// extractor has no list of opcodes of its own: an operator that is added to
/// the table is extracted, and llvm/utils/gisel-rule-synth decides from its
/// own registry which operators it has a model for.
const egraph::OpProperties *getSupportedOp(unsigned Opc) {
  uint32_t Flags;
  const egraph::OpProperties *P = egraph::getOpPropertiesForInstr(Opc, Flags);
  // An operator that only the synthesizer has a model for.
  if (!P)
    P = egraph::getModelOnlyOpProperties(Opc);
  if (!P)
    return nullptr;
  switch (P->Shape) {
  case egraph::OpShape::Phi:
    // The value depends on the control flow.
  case egraph::OpShape::Effect:
    // A terminator has no value.
    return nullptr;
  default:
    return P;
  }
}

/// True if a value of the pointer type \p Ty is its bits for the synthesizer:
/// the address space is integral, and an offset has the width of the pointer
/// (G_PTR_ADD is then the addition of the bits).
bool isSupportedPointer(const DataLayout &DL, LLT Ty) {
  unsigned AS = Ty.getAddressSpace();
  return !DL.isNonIntegralAddressSpace(AS) &&
         DL.getIndexSizeInBits(AS) == Ty.getSizeInBits();
}

/// A value of a tree: a virtual register with a scalar type of at most 64
/// bits, with a pointer type of at most 64 bits (isSupportedPointer), or with
/// the type of a fixed vector of at most MaxLanes such elements.
bool isSupportedValue(const MachineRegisterInfo &MRI, const DataLayout &DL,
                      Register R) {
  if (!R.isVirtual())
    return false;
  LLT Ty = MRI.getType(R);
  if (!Ty.isValid())
    return false;
  if (Ty.isVector()) {
    if (Ty.isScalable() || Ty.getNumElements() > MaxLanes)
      return false;
    Ty = Ty.getElementType();
  }
  if (Ty.getSizeInBits() > 64)
    return false;
  return Ty.isScalar() || (Ty.isPointer() && isSupportedPointer(DL, Ty));
}

/// An instruction that can be an interior node of an extracted tree: an
/// operator of the table whose results and register operands are values of
/// a tree (isSupportedValue). The only other operands are the attribute of the
/// operator: the predicate of a comparison and a trailing immediate.
bool isSupportedInstr(const MachineRegisterInfo &MRI, const MachineInstr &MI) {
  const egraph::OpProperties *P = getSupportedOp(MI.getOpcode());
  if (!P || MI.getNumExplicitDefs() == 0)
    return false;
  // The synthesizer has a value with unspecified bits for integers only: a
  // floating-point or pointer G_IMPLICIT_DEF is an input.
  if (MI.getOpcode() == TargetOpcode::G_IMPLICIT_DEF) {
    LLT Ty = MRI.getType(MI.getOperand(0).getReg()).getScalarType();
    if (Ty.isFloat() || Ty.isPointer())
      return false;
  }
  const DataLayout &DL = MI.getMF()->getDataLayout();
  for (const MachineOperand &MO : MI.operands()) {
    if (MO.isReg()) {
      if (MO.isImplicit() || !isSupportedValue(MRI, DL, MO.getReg()))
        return false;
      continue;
    }
    if (MO.isPredicate() && P->Shape == egraph::OpShape::Compare)
      continue;
    if (MO.isImm() && P->ImmAttr)
      continue;
    if (MO.isShuffleMask() && P->IsVector)
      continue;
    return false;
  }
  return true;
}

/// True if the G_PHI \p MI can be a node of a tree: a rule can read its
/// incoming values (gisynth::hasStablePhiInputs), and they and its result
/// are values of a tree.
bool isSupportedPhi(const MachineRegisterInfo &MRI,
                    const MachineDominatorTree &MDT, const MachineInstr &MI) {
  assert(MI.getOpcode() == TargetOpcode::G_PHI && "not a G_PHI");
  const DataLayout &DL = MI.getMF()->getDataLayout();
  if (!gisynth::hasStablePhiInputs(
          MRI, MI, [&](const MachineInstr &Def, const MachineInstr &Use) {
            return MDT.dominates(&Def, &Use);
          }))
    return false;
  if (!isSupportedValue(MRI, DL, MI.getOperand(0).getReg()))
    return false;
  for (unsigned I = 1, E = MI.getNumOperands(); I < E; I += 2)
    if (!isSupportedValue(MRI, DL, MI.getOperand(I).getReg()))
      return false;
  return true;
}

bool isHint(unsigned Opc) {
  return Opc == TargetOpcode::G_ASSERT_ZEXT ||
         Opc == TargetOpcode::G_ASSERT_SEXT ||
         Opc == TargetOpcode::G_ASSERT_ALIGN;
}

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

/// A tree node. Leaves (MI == nullptr) are tree inputs.
struct TreeNode {
  const MachineInstr *MI = nullptr;
  Register Reg;
  SmallVector<unsigned, 2> Args; // indices into the owning Tree's Nodes.
};

struct Tree {
  SmallVector<TreeNode, 8> Nodes; // Nodes.back() is the root.
};

class Extractor {
  const MachineRegisterInfo &MRI;
  GISelValueTracking &VT;
  const MachineDominatorTree &MDT;
  const MachineBasicBlock &MBB;

public:
  Extractor(const MachineRegisterInfo &MRI, GISelValueTracking &VT,
            const MachineDominatorTree &MDT, const MachineBasicBlock &MBB)
      : MRI(MRI), VT(VT), MDT(MDT), MBB(MBB) {}

  /// True if \p MI is an instruction of a tree in this block.
  bool isNode(const MachineInstr &MI) const {
    if (MI.getOpcode() == TargetOpcode::G_PHI)
      return isSupportedPhi(MRI, MDT, MI);
    return isSupportedInstr(MRI, MI);
  }

  /// All tree shapes for value \p R with at most \p Depth interior levels.
  /// A leaf is always the first variant.
  std::vector<Tree> enumerate(Register R, unsigned Depth) const {
    std::vector<Tree> Out;
    Tree Leaf;
    Leaf.Nodes.push_back({nullptr, R, {}});
    Out.push_back(std::move(Leaf));
    if (Depth == 0)
      return Out;
    const MachineInstr *Def = MRI.getVRegDef(R);
    if (!Def || Def->getParent() != &MBB || !isNode(*Def))
      return Out;

    // Cartesian product of the operand variants. A hint is not an
    // instruction of the final code: it is not a level of the tree. An
    // incoming value of a G_PHI is always an input: its definition is in
    // another block.
    unsigned Below = isHint(Def->getOpcode()) ? Depth : Depth - 1;
    if (Def->getOpcode() == TargetOpcode::G_PHI)
      Below = 0;
    std::vector<std::vector<Tree>> OpVariants;
    for (const MachineOperand &MO : Def->uses())
      if (MO.isReg())
        OpVariants.push_back(enumerate(MO.getReg(), Below));
    SmallVector<unsigned, 2> Idx(OpVariants.size(), 0);
    while (Out.size() < MaxTreesPerRoot + 1) {
      Tree T;
      TreeNode Root{Def, R, {}};
      for (unsigned I = 0; I < OpVariants.size(); ++I) {
        const Tree &Sub = OpVariants[I][Idx[I]];
        unsigned Base = T.Nodes.size();
        for (TreeNode N : Sub.Nodes) {
          for (unsigned &A : N.Args)
            A += Base;
          T.Nodes.push_back(N);
        }
        Root.Args.push_back(T.Nodes.size() - 1);
      }
      T.Nodes.push_back(Root);
      Out.push_back(std::move(T));
      // Advance the odometer.
      unsigned I = 0;
      for (; I < Idx.size(); ++I) {
        if (++Idx[I] < OpVariants[I].size())
          break;
        Idx[I] = 0;
      }
      if (I == Idx.size())
        break;
    }
    return Out;
  }

  void write(raw_ostream &OS, const MachineFunction &MF, const Tree &T) const {
    // Inputs are numbered in order of first (left-to-right) occurrence, and a
    // register that occurs twice is the same input.
    DenseMap<Register, unsigned> InputIdx;
    SmallVector<Register, 4> Inputs;
    unsigned Interior = 0;
    for (const TreeNode &N : T.Nodes) {
      if (N.MI) {
        ++Interior;
        continue;
      }
      if (InputIdx.try_emplace(N.Reg, Inputs.size()).second)
        Inputs.push_back(N.Reg);
    }

    json::OStream J(OS);
    J.object([&] {
      J.attribute("fn", MF.getName());
      J.attribute("bb", MBB.getNumber());
      J.attribute("root", regName(T.Nodes.back().Reg));
      J.attribute("interior", Interior);
      J.attributeBegin("expr");
      writeNode(J, T, T.Nodes.size() - 1, InputIdx);
      J.attributeEnd();
      J.attributeArray("inputs", [&] {
        for (Register R : Inputs) {
          J.object([&] {
            LLT Ty = MRI.getType(R);
            KnownBits KB = VT.getKnownBits(R);
            J.attribute("reg", regName(R));
            // The width of a lane, and the number of lanes of a vector.
            J.attribute("w", Ty.getScalarSizeInBits());
            if (Ty.isVector())
              J.attribute("lanes", Ty.getNumElements());
            J.attribute("type", typeName(Ty));
            J.attribute("zero", hex(KB.Zero));
            J.attribute("one", hex(KB.One));
            // A fact like the known bits: a rule that needs it checks it
            // again where it matches.
            J.attribute("noundef", isGuaranteedNotToBeUndefOrPoison(R, MRI));
            const MachineInstr *Def = MRI.getVRegDef(R);
            J.attribute("def", Def ? std::string(opcodeName(Def))
                                   : std::string("<none>"));
            // A floating-point constant is its bit pattern. A pointer
            // constant is an input like every other: a rule does not match
            // or build a G_CONSTANT with a pointer type.
            if (Ty.getScalarType().isPointer())
              return;
            // A vector constant with the same value in each lane is the
            // value of a lane.
            if (Ty.isVector()) {
              if (auto C = getIConstantSplatVal(R, MRI))
                J.attribute("const", hex(*C));
              else if (auto FC = getFConstantSplat(R, MRI,
                                                   /*AllowUndef=*/false))
                J.attribute("const", hex(FC->Value.bitcastToAPInt()));
              return;
            }
            if (auto C = getIConstantVRegVal(R, MRI))
              J.attribute("const", hex(*C));
            else if (Def && Def->getOpcode() == TargetOpcode::G_FCONSTANT)
              J.attribute("const", hex(Def->getOperand(1)
                                           .getFPImm()
                                           ->getValueAPF()
                                           .bitcastToAPInt()));
          });
        }
      });
    });
    OS << "\n";
    ++NumTreesWritten;
  }

private:
  static std::string opcodeName(const MachineInstr *MI) {
    const TargetInstrInfo *TII = MI->getMF()->getSubtarget().getInstrInfo();
    return std::string(TII->getName(MI->getOpcode()));
  }

  void writeNode(json::OStream &J, const Tree &T, unsigned I,
                 const DenseMap<Register, unsigned> &InputIdx) const {
    const TreeNode &N = T.Nodes[I];
    J.object([&] {
      if (!N.MI) {
        J.attribute("in", InputIdx.lookup(N.Reg));
        return;
      }
      J.attribute("op", opcodeName(N.MI));
      // The attribute of the operator, and the index of the result if the
      // instruction has several results.
      const egraph::OpProperties *P = getSupportedOp(N.MI->getOpcode());
      if (!P) {
        // A G_PHI: no attribute and one result.
      } else if (P->Shape == egraph::OpShape::Compare)
        J.attribute("pred", egraph::getComparePredicateName(
                                N.MI->getOperand(1).getPredicate()));
      else if (P->ImmAttr)
        J.attribute("imm",
                    N.MI->getOperand(N.MI->getNumOperands() - 1).getImm());
      else if (N.MI->getOpcode() == TargetOpcode::G_SHUFFLE_VECTOR)
        // The index of a lane of the two operands, or -1: the lane has no
        // specified value.
        J.attributeArray("mask", [&] {
          for (int M : N.MI->getOperand(3).getShuffleMask())
            J.value(M);
        });
      // The first result names the instruction: two results of one
      // instruction have the same "mi".
      if (N.MI->getNumExplicitDefs() > 1) {
        J.attribute("res", static_cast<int64_t>(defIndex(*N.MI, N.Reg)));
        J.attribute("mi", regName(N.MI->getOperand(0).getReg()));
      }
      LLT Ty = MRI.getType(N.Reg);
      J.attribute("w", static_cast<int64_t>(Ty.getScalarSizeInBits()));
      if (Ty.isVector())
        J.attribute("lanes", Ty.getNumElements());
      J.attribute("type", typeName(Ty));
      J.attribute("reg", regName(N.Reg));
      KnownBits KB = VT.getKnownBits(N.Reg);
      J.attribute("zero", hex(KB.Zero));
      J.attribute("one", hex(KB.One));
      J.attribute("noundef", isGuaranteedNotToBeUndefOrPoison(N.Reg, MRI));
      J.attribute("uses",
                  static_cast<int64_t>(std::distance(MRI.use_nodbg_begin(N.Reg),
                                                     MRI.use_nodbg_end())));
      J.attributeArray("flags", [&] {
        if (N.MI->getFlag(MachineInstr::NoUWrap))
          J.value("nuw");
        if (N.MI->getFlag(MachineInstr::NoSWrap))
          J.value("nsw");
        if (N.MI->getFlag(MachineInstr::IsExact))
          J.value("exact");
        if (N.MI->getFlag(MachineInstr::Disjoint))
          J.value("disjoint");
        if (N.MI->getFlag(MachineInstr::NonNeg))
          J.value("nneg");
      });
      J.attributeArray("args", [&] {
        for (unsigned A : N.Args)
          writeNode(J, T, A, InputIdx);
      });
    });
  }
};

raw_ostream &getCorpusStream() {
  if (CorpusOut == "-")
    return outs();
  static std::unique_ptr<raw_fd_ostream> OS;
  if (!OS) {
    std::error_code EC;
    OS = std::make_unique<raw_fd_ostream>(CorpusOut, EC, sys::fs::OF_Text);
    if (EC)
      report_fatal_error("cannot open " + Twine(CorpusOut) + ": " +
                         EC.message());
  }
  return *OS;
}

/// True if the type index \p TypeIdx of the operator \p Opc is a pointer type.
bool isPointerTypeIdx(unsigned Opc, unsigned TypeIdx) {
  switch (Opc) {
  case TargetOpcode::G_PTR_ADD:
  case TargetOpcode::G_PTRMASK:
  case TargetOpcode::G_INTTOPTR:
    return TypeIdx == 0;
  case TargetOpcode::G_PTRTOINT:
    return TypeIdx == 1;
  default:
    return false;
  }
}

/// The pointer type of the first address space whose pointers have \p Width
/// bits and are values of a tree, if there is one.
std::optional<LLT> getPointerType(const DataLayout &DL, unsigned Width) {
  for (unsigned AS = 0; AS != 16; ++AS) {
    LLT Ty = LLT::pointer(AS, DL.getPointerSizeInBits(AS));
    if (Ty.getSizeInBits() == Width && isSupportedPointer(DL, Ty))
      return Ty;
  }
  return std::nullopt;
}

/// Writes what the legalizer of the target does with each operator of the
/// table: operator -> widths of its type indices -> action. The synthesizer
/// reads it to try the operators that the target has before the others. It is
/// not a cost model: a rule is selected from measurements.
void writeLegality(const MachineFunction &MF) {
  const TargetSubtargetInfo &STI = MF.getSubtarget();
  const LegalizerInfo *LI = STI.getLegalizerInfo();
  const TargetInstrInfo *TII = STI.getInstrInfo();
  if (!LI)
    return;
  std::error_code EC;
  raw_fd_ostream OS(LegalityOut, EC, sys::fs::OF_Text);
  if (EC)
    report_fatal_error("cannot open " + Twine(LegalityOut) + ": " +
                       EC.message());
  static const unsigned Widths[] = {1, 8, 16, 32, 64};
  const DataLayout &DL = MF.getDataLayout();
  json::OStream J(OS, 1);
  J.object([&] {
    J.attribute("version", 1);
    J.attribute("target", MF.getTarget().getTargetTriple().str());
    J.attribute("cpu", STI.getCPU());
    J.attributeObject("operators", [&] {
      for (unsigned Opc = TargetOpcode::PRE_ISEL_GENERIC_OPCODE_START;
           Opc <= TargetOpcode::PRE_ISEL_GENERIC_OPCODE_END; ++Opc) {
        const egraph::OpProperties *P = getSupportedOp(Opc);
        // An operator on a vector has no combination of scalar types.
        if (!P || P->IsVector)
          continue;
        const MCInstrDesc &Desc = TII->get(Opc);
        if (Desc.isVariadic())
          continue;
        unsigned NumIdx = 0;
        for (const MCOperandInfo &Op : Desc.operands())
          if (Op.isGenericType())
            NumIdx = std::max(NumIdx, Op.getGenericTypeIndex() + 1);
        if (NumIdx == 0 || NumIdx > 3)
          continue;
        J.attributeObject(TII->getName(Opc), [&] {
          SmallVector<unsigned, 3> Idx(NumIdx, 0);
          while (true) {
            SmallVector<LLT, 3> Types;
            std::string Key;
            bool HasTypes = true;
            for (unsigned TypeIdx = 0; TypeIdx != NumIdx; ++TypeIdx) {
              unsigned W = Widths[Idx[TypeIdx]];
              Key += (Key.empty() ? "" : ",") + utostr(W);
              if (!isPointerTypeIdx(Opc, TypeIdx)) {
                Types.push_back(LLT::scalar(W));
                continue;
              }
              // The first address space with pointers of this width.
              std::optional<LLT> PtrTy = getPointerType(DL, W);
              if (PtrTy)
                Types.push_back(*PtrTy);
              else
                HasTypes = false;
            }
            std::string Action = "Unsupported";
            if (HasTypes) {
              Action.clear();
              raw_string_ostream AS(Action);
              AS << LI->getAction({Opc, Types}).Action;
            }
            J.attribute(Key, Action);
            unsigned I = 0;
            for (; I < NumIdx; ++I) {
              if (++Idx[I] < std::size(Widths))
                break;
              Idx[I] = 0;
            }
            if (I == NumIdx)
              break;
          }
        });
      }
    });
  });
  OS << "\n";
}

} // end anonymous namespace

char GISynthCorpusExtractor::ID = 0;
INITIALIZE_PASS_BEGIN(GISynthCorpusExtractor, DEBUG_TYPE,
                      "GlobalISel rule synthesizer corpus extractor", false,
                      true)
INITIALIZE_PASS_DEPENDENCY(GISelValueTrackingAnalysisLegacy)
INITIALIZE_PASS_DEPENDENCY(MachineDominatorTreeWrapperPass)
INITIALIZE_PASS_END(GISynthCorpusExtractor, DEBUG_TYPE,
                    "GlobalISel rule synthesizer corpus extractor", false, true)

GISynthCorpusExtractor::GISynthCorpusExtractor() : MachineFunctionPass(ID) {
  initializeGISynthCorpusExtractorPass(*PassRegistry::getPassRegistry());
}

void GISynthCorpusExtractor::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<GISelValueTrackingAnalysisLegacy>();
  AU.addRequired<MachineDominatorTreeWrapperPass>();
  MachineFunctionPass::getAnalysisUsage(AU);
}

bool GISynthCorpusExtractor::runOnMachineFunction(MachineFunction &MF) {
  if (MF.getProperties().hasProperty(
          MachineFunctionProperties::Property::FailedISel))
    return false;
  const MachineRegisterInfo &MRI = MF.getRegInfo();
  GISelValueTracking &VT =
      getAnalysis<GISelValueTrackingAnalysisLegacy>().get(MF);
  const MachineDominatorTree &MDT =
      getAnalysis<MachineDominatorTreeWrapperPass>().getDomTree();
  raw_ostream &OS = getCorpusStream();
  static bool LegalityWritten = false;
  if (!LegalityOut.empty() && !LegalityWritten) {
    LegalityWritten = true;
    writeLegality(MF);
  }
  for (const MachineBasicBlock &MBB : MF) {
    Extractor E(MRI, VT, MDT, MBB);
    for (const MachineInstr &MI : MBB) {
      // An instruction without operands and a hint are nodes of a tree,
      // not roots: no replacement is better than they are.
      if (!E.isNode(MI) || isHint(MI.getOpcode()) ||
          MI.getNumExplicitOperands() == MI.getNumExplicitDefs())
        continue;
      // One set of trees per result of the instruction.
      for (const MachineOperand &DefMO : MI.defs()) {
        std::vector<Tree> Trees = E.enumerate(DefMO.getReg(), MaxDepth);
        // Skip the leaf-only variant.
        for (unsigned I = 1; I < Trees.size(); ++I)
          E.write(OS, MF, Trees[I]);
      }
    }
  }
  OS.flush();
  return false;
}
