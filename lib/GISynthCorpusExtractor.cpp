//===- GISynthCorpusExtractor.cpp - Corpus for the rule synthesizer ------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Writes small gMIR expression trees and their GISelValueTracking known bits
// to a JSON-lines file for tools/gisel-rule-synth. See the header for an
// overview and tools/gisel-rule-synth/README.md for the record format.
//
//===----------------------------------------------------------------------===//

#include "GISelEGraphSynth/GISynthCorpusExtractor.h"
#include "GISelEGraphSynth/GIEGraph.h"
#include "GISelEGraphSynth/GISynthJoint.h"
#include "GISelEGraphSynth/GISynthPredicates.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/CodeGen/GlobalISel/GISelValueTracking.h"
#include "llvm/CodeGen/GlobalISel/GenericMachineInstrs.h"
#include "llvm/CodeGen/GlobalISel/LegalizerInfo.h"
#include "llvm/CodeGen/GlobalISel/Utils.h"
#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/InitializePasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/JSON.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"

#define DEBUG_TYPE "gisel-synth-corpus"

using namespace llvm;

STATISTIC(NumTreesWritten, "Number of expression trees written");
STATISTIC(NumRegionsWritten, "Number of region DAGs written");

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

static cl::list<std::string> ModeledIntrinsics(
    "gisel-synth-corpus-intrinsics", cl::Hidden, cl::CommaSeparated,
    cl::desc("Names of the intrinsics without side effects that the rule "
             "synthesizer has a model for: a G_INTRINSIC with one of these "
             "names is a node of an expression tree"));

static cl::opt<std::string> RegionOut(
    "gisel-synth-region-out", cl::Hidden,
    cl::desc("Also write one SSA region DAG of the pure scalar integer "
             "instructions of each basic block to this JSON-lines file "
             "(tools/gisel-rule-synth/girs/joint.py)"));

static cl::opt<unsigned> RegionMaxInstrs(
    "gisel-synth-region-max-instrs", cl::Hidden, cl::init(256),
    cl::desc("Maximum number of instructions of one region record; a longer "
             "block is written as several records"));

static cl::opt<std::string> LegalityOut(
    "gisel-synth-legality", cl::Hidden,
    cl::desc("Also write the action of the legalizer for each operator of "
             "the e-graph operator table and each combination of scalar "
             "widths, and of fixed vector types, to this JSON file"));

static cl::list<unsigned> LegalityLanes(
    "gisel-synth-legality-lanes", cl::Hidden, cl::CommaSeparated,
    cl::desc("Numbers of lanes of the fixed vector types of the legality "
             "table (default: 2,3,4,8)"));

static cl::list<unsigned> LegalityElems(
    "gisel-synth-legality-elems", cl::Hidden, cl::CommaSeparated,
    cl::desc("Widths of the lanes of the fixed vector types of the legality "
             "table (default: 1,8,16,32,64)"));

namespace {

/// The entry of the operator table of the e-graph combiner for \p Opc, or
/// null if an instruction with this opcode cannot be a node of a tree. The
/// extractor has no list of opcodes of its own: an operator that is added to
/// the table is extracted, and tools/gisel-rule-synth decides from its
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
  // A constant (OpProperties::Leaf) is an input of a tree, not a node.
  if (!P || P->Leaf || MI.getNumExplicitDefs() == 0)
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

/// True if \p ID is an intrinsic of -gisel-synth-corpus-intrinsics. The
/// extractor has no list of intrinsics of its own: the operators of a target
/// are in the registry of tools/gisel-rule-synth.
bool isModeledIntrinsic(Intrinsic::ID ID) {
  static const DenseSet<unsigned> IDs = [] {
    DenseSet<unsigned> Set;
    for (const std::string &Name : ModeledIntrinsics) {
      Intrinsic::ID ID = Intrinsic::lookupIntrinsicID(Name);
      if (ID == Intrinsic::not_intrinsic)
        reportFatalUsageError("-gisel-synth-corpus-intrinsics: no intrinsic "
                              "has the name '" +
                              Twine(Name) + "'");
      Set.insert(ID);
    }
    return Set;
  }();
  return IDs.contains(ID);
}

/// True if the intrinsic call \p MI can be a node of a tree: a G_INTRINSIC
/// (no side effect, not convergent) of the list, with one result, whose
/// result and arguments are values of a tree.
bool isSupportedIntrinsic(const MachineRegisterInfo &MRI,
                          const MachineInstr &MI) {
  if (MI.getOpcode() != TargetOpcode::G_INTRINSIC ||
      MI.getNumExplicitDefs() != 1 ||
      !isModeledIntrinsic(cast<GIntrinsic>(MI).getIntrinsicID()))
    return false;
  const DataLayout &DL = MI.getMF()->getDataLayout();
  for (const MachineOperand &MO : MI.operands()) {
    if (MO.isIntrinsicID())
      continue;
    if (!MO.isReg() || MO.isImplicit() ||
        !isSupportedValue(MRI, DL, MO.getReg()))
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
  /// MI is a load, and the operand of the node is the value of the G_STORE
  /// whose bits the load reads (gisynth::getForwardedStoreValue). A load
  /// without this flag is a fact about its own result.
  bool Forwarded = false;
};

/// The number of bits that the G_ZEXTLOAD or G_SEXTLOAD that defines \p R
/// reads, or 0: the result is the extension of these bits, which is the
/// fact of a G_ASSERT_ZEXT or G_ASSERT_SEXT.
unsigned getExtLoadBits(const MachineRegisterInfo &MRI, Register R) {
  const MachineInstr *Def = MRI.getVRegDef(R);
  if (!Def || (Def->getOpcode() != TargetOpcode::G_ZEXTLOAD &&
               Def->getOpcode() != TargetOpcode::G_SEXTLOAD))
    return 0;
  unsigned Bits = gisynth::getFixedMemBits(cast<GMemOperation>(*Def));
  bool Signed = Def->getOpcode() == TargetOpcode::G_SEXTLOAD;
  return gisynth::isExtLoadOf(MRI, R, Signed, Bits) ? Bits : 0;
}

struct Tree {
  SmallVector<TreeNode, 8> Nodes; // Nodes.back() is the root.
};

class Extractor {
  const MachineRegisterInfo &MRI;
  GISelValueTracking &VT;
  const MachineDominatorTree &MDT;
  const MachineBasicBlock &MBB;
  SmallVector<const MachineBasicBlock *, 8> Blocks;

public:
  Extractor(const MachineRegisterInfo &MRI, GISelValueTracking &VT,
            const MachineDominatorTree &MDT, const MachineBasicBlock &MBB)
      : MRI(MRI), VT(VT), MDT(MDT), MBB(MBB),
        Blocks(gisynth::straightLineBlocks(MBB)) {}

  /// True if \p MI is an instruction of a tree in this block.
  bool isNode(const MachineInstr &MI) const {
    if (MI.getOpcode() == TargetOpcode::G_PHI)
      return isSupportedPhi(MRI, MDT, MI);
    if (isa<GIntrinsic>(MI))
      return isSupportedIntrinsic(MRI, MI);
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
    if (getExtLoadBits(MRI, R) != 0 &&
        isSupportedValue(MRI, Def->getMF()->getDataLayout(), R)) {
      // The result of an extending load is an input with the fact that it
      // is an extension. The fact is a node, like a hint, with the result
      // as its operand.
      Tree T = Out.front();
      T.Nodes.push_back({Def, R, {0}});
      Out.push_back(std::move(T));
      return Out;
    }
    if (!Def || !is_contained(Blocks, Def->getParent()) || !isNode(*Def) ||
        (Def->getParent() != &MBB && !gisynth::isStraightLineRegionInstr(*Def)))
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

  /// Writes the tree of the load \p Load whose bits a G_STORE before it
  /// wrote: the load with the stored value as its operand.
  void writeForwardedLoad(raw_ostream &OS, const MachineFunction &MF,
                          const GAnyLoad &Load) const {
    Register Dst = Load.getDstReg();
    unsigned Bits = gisynth::getFixedMemBits(Load);
    Register Value = gisynth::getForwardedStoreValue(MRI, Dst, Bits);
    if (!Value.isValid())
      return;
    // The helper gives a value only with the types of the model.
    const DataLayout &DL = MF.getDataLayout();
    if (!isSupportedValue(MRI, DL, Dst) || !isSupportedValue(MRI, DL, Value))
      return;
    Tree T;
    T.Nodes.push_back({nullptr, Value, {}});
    T.Nodes.push_back({&Load, Dst, {0}, /*Forwarded=*/true});
    write(OS, MF, T);
  }

  void writeFPFacts(json::OStream &J, Register R) const {
    LLT Ty = MRI.getType(R).getScalarType();
    unsigned W = Ty.getSizeInBits();
    if (Ty.isPointer() || Ty.isInteger() || (W != 16 && W != 32 && W != 64))
      return;
    auto F = gisynth::getFPValueFacts(VT, MRI, R);
    J.attributeObject("fp_facts", [&] {
      J.attribute("classes", unsigned(F.Classes));
      J.attribute("integral", F.Integral);
      if (F.Lower) {
        J.attribute("lower", hex(F.Lower->bitcastToAPInt()));
        J.attribute("upper", hex(F.Upper->bitcastToAPInt()));
      }
    });
  }

  void write(raw_ostream &OS, const MachineFunction &MF, const Tree &T) const {
    // The constrained operations of a tree have one floating-point
    // environment, which is the one of the root: a rule checks the same
    // (gisynth::isSameFPEnvironment).
    const MachineInstr *Root = T.Nodes.back().MI;
    for (const TreeNode &N : T.Nodes)
      if (N.MI && N.MI != Root &&
          gisynth::isConstrainedFPOpcode(N.MI->getOpcode()) &&
          !gisynth::isSameFPEnvironment(*N.MI, *Root))
        return;
    bool Pure = all_of(T.Nodes, [](const TreeNode &N) {
      return !N.MI || gisynth::isStraightLineRegionInstr(*N.MI);
    });
    bool Crosses = any_of(T.Nodes, [&](const TreeNode &N) {
      // An extending-load hint describes a boundary input; it does not
      // import or move the load. Preserve these existing block-local trees
      // even when that input was loaded in another block.
      return N.MI && (N.Forwarded || !isa<GAnyLoad>(N.MI)) &&
             N.MI->getParent() != &MBB;
    });
    if (Crosses && !Pure)
      return;
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
      // An explicit scope certificate, shared by all pure trees of this
      // chain. Old corpora without it remain block-local in sibling.py.
      if (Pure && Blocks.size() > 1)
        J.attributeArray("straight_line", [&] {
          for (const MachineBasicBlock *BB : Blocks)
            J.value(BB->getNumber());
        });
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
            writeFPFacts(J, R);
            // A fact like the known bits: a rule that needs it checks it
            // again where it matches.
            J.attribute("noundef", gisynth::isDefinedValue(R, MRI));
            const MachineInstr *Def = MRI.getVRegDef(R);
            J.attribute("def", Def ? std::string(opcodeName(Def))
                                   : std::string("<none>"));
            // The address of an object: a constant whose bits are not
            // known.
            if (gisynth::isAddressConstant(R, MRI))
              J.attribute("address", true);
            // The bits of a constant: an integer, a pointer, the bit
            // pattern of a floating-point value, or the value of a lane
            // of a vector with the same constant in each lane. A rule
            // reads a constant with the same function.
            if (std::optional<APInt> C =
                    gisynth::getConstantBits(R, MRI, /*AllowSplat=*/true))
              J.attribute("const", hex(*C));
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
      const egraph::OpProperties *P = getSupportedOp(N.MI->getOpcode());
      if (const auto *Load = dyn_cast<GAnyLoad>(N.MI)) {
        // A load that reads the bits of its operand, or the fact that the
        // result of an extending load is an extension.
        if (N.Forwarded)
          J.attribute("op", opcodeName(N.MI));
        else
          J.attribute("op", N.MI->getOpcode() == TargetOpcode::G_SEXTLOAD
                                ? "G_ASSERT_SEXT"
                                : "G_ASSERT_ZEXT");
        J.attribute("imm",
                    static_cast<int64_t>(gisynth::getFixedMemBits(*Load)));
        if (!N.Forwarded)
          J.attribute("load", true);
      } else if (const auto *Call = dyn_cast<GIntrinsic>(N.MI)) {
        // The name of the intrinsic without the types of an overload, as in
        // the registry of the synthesizer.
        J.attribute("op", Intrinsic::getBaseName(Call->getIntrinsicID()));
      } else {
        J.attribute("op", opcodeName(N.MI));
      }
      // The attribute of the operator, and the index of the result if the
      // instruction has several results.
      if (!P) {
        // A G_PHI, a load or an intrinsic: no other attribute and one result.
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
      J.attribute("bb", N.MI->getParent()->getNumber());
      KnownBits KB = VT.getKnownBits(N.Reg);
      J.attribute("zero", hex(KB.Zero));
      J.attribute("one", hex(KB.One));
      writeFPFacts(J, N.Reg);
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
        // The program does not read the exceptions of a constrained
        // operation.
        if (N.MI->getFlag(MachineInstr::NoFPExcept))
          J.value("nofpexcept");
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

/// The largest number of lanes of a vector type of the legality table.
constexpr unsigned MaxVectorLanesOfTable = 16;

std::string lltText(LLT Ty) {
  std::string S;
  raw_string_ostream OS(S);
  OS << Ty;
  return S;
}

/// The combinations of types of the type indices of \p Opc with fixed vectors
/// that the legality table has: the types that a node with vectors of the
/// rule synthesizer gives the instruction. Each combination has one number of
/// lanes \p Lanes for the vectors that the operator computes lane by lane; an
/// operator that moves lanes also has vectors with other numbers of lanes.
void forEachVectorTypes(unsigned Opc, const egraph::OpProperties &P,
                        unsigned NumIdx, unsigned Lanes,
                        ArrayRef<unsigned> Elems,
                        function_ref<void(ArrayRef<LLT>)> Fn) {
  auto V = [](unsigned N, unsigned E) {
    return LLT::fixed_vector(N, LLT::scalar(E));
  };
  // The index of a lane: the index types of the targets.
  static const unsigned IdxWidths[] = {32, 64};
  switch (Opc) {
  case TargetOpcode::G_BUILD_VECTOR:
  case TargetOpcode::G_SPLAT_VECTOR:
    for (unsigned E : Elems)
      Fn({V(Lanes, E), LLT::scalar(E)});
    return;
  case TargetOpcode::G_EXTRACT_VECTOR_ELT:
    for (unsigned E : Elems)
      for (unsigned I : IdxWidths)
        Fn({LLT::scalar(E), V(Lanes, E), LLT::scalar(I)});
    return;
  case TargetOpcode::G_INSERT_VECTOR_ELT:
    for (unsigned E : Elems)
      for (unsigned I : IdxWidths)
        Fn({V(Lanes, E), LLT::scalar(E), LLT::scalar(I)});
    return;
  case TargetOpcode::G_SHUFFLE_VECTOR:
    for (unsigned E : Elems)
      for (unsigned Src : {2u, 3u, 4u, 8u})
        Fn({V(Lanes, E), V(Src, E)});
    return;
  case TargetOpcode::G_CONCAT_VECTORS:
    for (unsigned E : Elems)
      for (unsigned K : {2u, 4u})
        if (Lanes * K <= MaxVectorLanesOfTable)
          Fn({V(Lanes * K, E), V(Lanes, E)});
    return;
  case TargetOpcode::G_EXTRACT_SUBVECTOR:
  case TargetOpcode::G_INSERT_SUBVECTOR:
    for (unsigned E : Elems)
      for (unsigned K : {2u, 4u})
        if (Lanes * K <= MaxVectorLanesOfTable) {
          if (Opc == TargetOpcode::G_EXTRACT_SUBVECTOR)
            Fn({V(Lanes, E), V(Lanes * K, E)});
          else
            Fn({V(Lanes * K, E), V(Lanes, E)});
        }
    return;
  default:
    break;
  }
  if (P.IsVector || NumIdx == 0 || NumIdx > 2)
    return;
  for (unsigned TypeIdx = 0; TypeIdx != NumIdx; ++TypeIdx)
    if (isPointerTypeIdx(Opc, TypeIdx))
      return;
  // An operator that computes each lane from the same lane of its operands:
  // each type index is a vector with \p Lanes lanes. The condition of a
  // G_SELECT can also be one scalar for all lanes.
  for (unsigned A : Elems) {
    if (NumIdx == 1) {
      Fn({V(Lanes, A)});
      continue;
    }
    for (unsigned B : Elems)
      Fn({V(Lanes, A), V(Lanes, B)});
    if (Opc == TargetOpcode::G_SELECT)
      Fn({V(Lanes, A), LLT::scalar(1)});
  }
}

/// A conversion's type indices distinguish integer and FP even at equal
/// widths. Legacy targets deliberately collapse these back to scalar LLTs.
bool setConversionTypes(const egraph::OpProperties &P,
                        SmallVectorImpl<LLT> &Ts) {
  using egraph::CastKind;
  if (!egraph::isFPCast(P.Cast))
    return true;
  if (Ts.size() != 2)
    return false;
  bool FloatResult =
      P.Cast == CastKind::FPExtend || P.Cast == CastKind::FPTruncate ||
      P.Cast == CastKind::SIntToFP || P.Cast == CastKind::UIntToFP;
  bool FloatInput =
      P.Cast != CastKind::SIntToFP && P.Cast != CastKind::UIntToFP;
  for (unsigned I = 0; I < 2; ++I) {
    unsigned W = Ts[I].getScalarSizeInBits();
    bool IsFP = I == 0 ? FloatResult : FloatInput;
    if (IsFP && W != 16 && W != 32 && W != 64)
      return false;
    LLT T = IsFP ? LLT::floatIEEE(W) : LLT::integer(W);
    Ts[I] = Ts[I].isVector() ? LLT::fixed_vector(Ts[I].getNumElements(), T) : T;
  }
  return true;
}

/// Writes what the legalizer of the target does with each operator of the
/// table: operator -> widths of its type indices -> action, and operator ->
/// the types of its type indices (fixed vectors) -> action. The synthesizer
/// reads it to try the operators that the target has before the others, and
/// to propose a replacement with vectors only in operations that the target
/// legalizes. It is not a cost model: a rule is selected from measurements.
/// An action is the action of the legalizer; whether a form that is not
/// Legal is acceptable depends on the stage (before the legalizer, a form
/// that the legalizer can change is acceptable; after it, only Legal).
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
    J.attribute("version", 3);
    J.attribute("typed_fp_casts", LLT::getUseExtended());
    J.attribute("target", MF.getTarget().getTargetTriple().str());
    J.attribute("cpu", STI.getCPU());
    J.attribute("features", STI.getFeatureString());
    // The stage of the pipeline at which the table was written; the actions
    // are those of the LegalizerInfo, which every stage shares.
    J.attribute("stage", "pre-legalizer");
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
            if (HasTypes && setConversionTypes(*P, Types)) {
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
    SmallVector<unsigned, 8> Lanes(LegalityLanes.begin(), LegalityLanes.end());
    if (Lanes.empty())
      Lanes = {2, 3, 4, 8};
    SmallVector<unsigned, 8> Elems(LegalityElems.begin(), LegalityElems.end());
    if (Elems.empty())
      Elems = {1, 8, 16, 32, 64};
    // The MI operand of each type index, so that a node of the synthesizer
    // (operand 0 is the result) can give the types of a query.
    J.attributeObject("type_operands", [&] {
      for (unsigned Opc = TargetOpcode::PRE_ISEL_GENERIC_OPCODE_START;
           Opc <= TargetOpcode::PRE_ISEL_GENERIC_OPCODE_END; ++Opc) {
        if (!getSupportedOp(Opc))
          continue;
        const MCInstrDesc &Desc = TII->get(Opc);
        SmallVector<int, 4> First;
        for (auto [I, Op] : enumerate(Desc.operands())) {
          if (!Op.isGenericType())
            continue;
          unsigned Idx = Op.getGenericTypeIndex();
          if (First.size() <= Idx)
            First.resize(Idx + 1, -1);
          if (First[Idx] < 0)
            First[Idx] = I;
        }
        if (First.empty())
          continue;
        J.attributeArray(TII->getName(Opc), [&] {
          for (int I : First)
            J.value(I);
        });
      }
    });
    J.attributeObject("typed", [&] {
      for (unsigned Opc = TargetOpcode::PRE_ISEL_GENERIC_OPCODE_START;
           Opc <= TargetOpcode::PRE_ISEL_GENERIC_OPCODE_END; ++Opc) {
        const egraph::OpProperties *P = getSupportedOp(Opc);
        if (!P)
          continue;
        const MCInstrDesc &Desc = TII->get(Opc);
        unsigned NumIdx = 0;
        for (const MCOperandInfo &Op : Desc.operands())
          if (Op.isGenericType())
            NumIdx = std::max(NumIdx, Op.getGenericTypeIndex() + 1);
        std::vector<std::pair<std::string, std::string>> Rows;
        for (unsigned N : Lanes)
          forEachVectorTypes(Opc, *P, NumIdx, N, Elems,
                             [&](ArrayRef<LLT> Types) {
                               if (Types.size() != NumIdx)
                                 return;
                               SmallVector<LLT, 4> Typed(Types);
                               if (!setConversionTypes(*P, Typed))
                                 return;
                               Types = Typed;
                               std::string Key;
                               for (LLT T : Types)
                                 Key += (Key.empty() ? "" : ",") + lltText(T);
                               std::string Action;
                               raw_string_ostream AS(Action);
                               AS << LI->getAction({Opc, Types}).Action;
                               Rows.emplace_back(Key, Action);
                             });
        if (Rows.empty())
          continue;
        J.attributeObject(TII->getName(Opc), [&] {
          for (const auto &[Key, Action] : Rows)
            J.attribute(Key, Action);
        });
      }
    });
  });
  OS << "\n";
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
  if (!RegionOut.empty()) {
    raw_ostream &ROS = getRegionStream();
    for (const MachineBasicBlock &MBB : MF)
      writeRegions(ROS, MF, MBB, MRI, VT);
    ROS.flush();
  }
  for (const MachineBasicBlock &MBB : MF) {
    Extractor E(MRI, VT, MDT, MBB);
    for (const MachineInstr &MI : MBB) {
      if (const auto *Load = dyn_cast<GAnyLoad>(&MI)) {
        E.writeForwardedLoad(OS, MF, *Load);
        continue;
      }
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
