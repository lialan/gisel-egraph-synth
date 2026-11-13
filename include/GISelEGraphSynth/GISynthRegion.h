//===- GISynthRegion.h - Straight-line MIR regions -----------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef GISELEGRAPHSYNTH_GISYNTHREGION_H
#define GISELEGRAPHSYNTH_GISYNTHREGION_H

#include "GISelEGraphSynth/GIEGraph.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"

namespace llvm::gisynth {

/// A crossing must execute the successor next, without choosing a path or
/// entering through another edge. In particular, a conditional branch with
/// identical targets is not an unconditional edge (its condition may poison).
inline const MachineBasicBlock *
straightLineSuccessor(const MachineBasicBlock &From) {
  if (From.succ_size() != 1 || From.isEHPad() || From.hasAddressTaken())
    return nullptr;
  const MachineBasicBlock *To = *From.succ_begin();
  if (To == &From || To == &From.getParent()->front() || To->pred_size() != 1 ||
      To->isEHPad() || To->hasAddressTaken())
    return nullptr;
  unsigned Branches = 0;
  for (const MachineInstr &MI : From.terminators()) {
    if (MI.getOpcode() != TargetOpcode::G_BR || ++Branches != 1 ||
        MI.getOperand(0).getMBB() != To)
      return nullptr;
  }
  // A block without a terminator can only fall through to its layout
  // successor. This also rejects an incomplete CFG in a corpus fixture.
  if (!Branches && From.getNextNode() != To)
    return nullptr;
  return To;
}

/// The maximal bounded straight-line chain containing Anchor, in execution
/// order, independent of block layout. Cycles and over-budget chains fall
/// back to the anchor alone. Every anchor of an accepted chain gets the same
/// block list, so corpus grouping and runtime matching agree.
inline SmallVector<const MachineBasicBlock *, 8>
straightLineBlocks(const MachineBasicBlock &Anchor, unsigned MaxBlocks = 16) {
  SmallVector<const MachineBasicBlock *, 8> Seen;
  const MachineBasicBlock *Head = &Anchor;
  while (Head->pred_size() == 1) {
    const MachineBasicBlock *Prev = *Head->pred_begin();
    if (straightLineSuccessor(*Prev) != Head)
      break;
    Seen.push_back(Head);
    if (is_contained(Seen, Prev) || Seen.size() >= MaxBlocks)
      return {&Anchor};
    Head = Prev;
  }
  SmallVector<const MachineBasicBlock *, 8> Blocks;
  for (const MachineBasicBlock *BB = Head; BB;
       BB = straightLineSuccessor(*BB)) {
    if (is_contained(Blocks, BB) || Blocks.size() >= MaxBlocks)
      return {&Anchor};
    Blocks.push_back(BB);
  }
  return Blocks;
}

/// First cross-block subset: deterministic scalar integer operations with
/// no effects or immediate UB. Poison-producing arithmetic is allowed: its
/// existing refinement proof still applies. Freeze, undef, PHIs, memory,
/// intrinsics, pointers and FP stay at the boundary.
inline bool isStraightLineRegionInstr(const MachineInstr &MI) {
  const egraph::OpProperties *P = egraph::getOpProperties(MI.getOpcode());
  if (!P)
    P = egraph::getModelOnlyOpProperties(MI.getOpcode());
  if (!P || P->MayTrap || P->StopsPoison || P->IsFP ||
      P->Shape == egraph::OpShape::Phi || P->Shape == egraph::OpShape::Effect ||
      MI.getOpcode() == TargetOpcode::G_IMPLICIT_DEF ||
      MI.getOpcode() == TargetOpcode::G_ANYEXT || MI.isTerminator() ||
      MI.mayLoadOrStore() || MI.hasUnmodeledSideEffects())
    return false;
  const MachineRegisterInfo &MRI = MI.getMF()->getRegInfo();
  for (const MachineOperand &MO : MI.operands()) {
    if (!MO.isReg())
      continue;
    if (MO.isImplicit() || !MO.getReg().isVirtual())
      return false;
    LLT Ty = MRI.getType(MO.getReg());
    if (!Ty.isScalar() || Ty.isFloat())
      return false;
  }
  return MI.getNumExplicitDefs() != 0;
}

/// Check every matched instruction, not just the outputs. The emitter only
/// permits crossings when the replacement also belongs to the pure subset.
inline bool isRegionScope(const MachineRegisterInfo &MRI, Register Dst,
                          std::initializer_list<Register> Nodes,
                          bool AllowCrossBlock) {
  const MachineInstr *Root = MRI.getVRegDef(Dst);
  if (!Root)
    return false;
  bool Crosses = false;
  for (Register R : Nodes) {
    const MachineInstr *MI = MRI.getVRegDef(R);
    if (!MI)
      return false;
    Crosses |= MI->getParent() != Root->getParent();
  }
  if (!Crosses)
    return true;
  if (!AllowCrossBlock || !isStraightLineRegionInstr(*Root))
    return false;
  auto Blocks = straightLineBlocks(*Root->getParent());
  return all_of(Nodes, [&](Register R) {
    const MachineInstr &MI = *MRI.getVRegDef(R);
    return is_contained(Blocks, MI.getParent()) &&
           isStraightLineRegionInstr(MI);
  });
}

/// Linear instruction order for placement. Branches count against the
/// instruction-distance budget, but are never moved or erased.
inline SmallVector<MachineInstr *, 32>
straightLineInstructions(MachineInstr &Root, unsigned MaxDistance) {
  auto Blocks = straightLineBlocks(*Root.getParent());
  auto RootBB = llvm::find(Blocks, Root.getParent());
  SmallVector<MachineInstr *, 32> Instrs;
  auto BB = RootBB;
  MachineBasicBlock::const_iterator It(&Root);
  for (unsigned I = 0; I < MaxDistance; ++I) {
    while (It == (*BB)->begin() && BB != Blocks.begin())
      It = (*--BB)->end();
    if (It == (*BB)->begin())
      break;
    Instrs.push_back(const_cast<MachineInstr *>(&*--It));
  }
  std::reverse(Instrs.begin(), Instrs.end());
  Instrs.push_back(&Root);
  BB = RootBB;
  It = std::next(MachineBasicBlock::const_iterator(&Root));
  for (unsigned I = 0; I < MaxDistance; ++I) {
    while (It == (*BB)->end() && std::next(BB) != Blocks.end())
      It = (*++BB)->begin();
    if (It == (*BB)->end())
      break;
    Instrs.push_back(const_cast<MachineInstr *>(&*It++));
  }
  return Instrs;
}

} // namespace llvm::gisynth

#endif
