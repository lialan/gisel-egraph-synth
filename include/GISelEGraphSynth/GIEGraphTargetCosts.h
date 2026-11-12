//===- GISelEGraphSynth/GIEGraphTargetCosts.h - Target costs ----*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// The target-specific part of the cost model of the e-graph combiner
/// (TargetCostModel in lib/GIEGraphCombiner.cpp): the costs of nodes and of
/// patterns of nodes that the instruction selection of a target implements,
/// and whether the target keeps uniform values in a register bank of their
/// own. The generic core (GIEGraph.h) only sees the CostModel hooks; it never
/// names an instruction of a target. A target without a model uses the
/// default costs.
//===----------------------------------------------------------------------===//

#ifndef GISELEGRAPHSYNTH_GIEGRAPHTARGETCOSTS_H
#define GISELEGRAPHSYNTH_GIEGRAPHTARGETCOSTS_H

#include "GISelEGraphSynth/GIEGraph.h"
#include <memory>

namespace llvm {
class MachineFunction;
class RegisterBank;
class raw_ostream;

namespace egraph {

class TargetCosts {
public:
  virtual ~TargetCosts();
  /// True if the target keeps uniform values in a register bank of their
  /// own, so that the bank states (BankState::Uniform) apply.
  virtual bool hasUniformBank() const = 0;
  /// After register bank selection: true if \p RB is the bank of uniform
  /// values.
  virtual bool isUniformBank(const RegisterBank &RB) const = 0;
  /// Refine \p Default, the default cost of item \p I of \p D
  /// (CostModel::getItemCost), for this target.
  virtual CostVector getItemCost(const EGraph &G, const CostDag &D, unsigned I,
                                 const CostVector &Default) const = 0;
  /// The covers of \p D that the instruction selection of the target forms
  /// (CostModel::findCovers).
  virtual void findCovers(const EGraph &G, const CostDag &D,
                          SmallVectorImpl<PatternCover> &Covers) const = 0;
  /// What the model decides at this position of the pass, for the report.
  virtual void describe(raw_ostream &OS) const = 0;
};

/// The model of AMDGPU (lib/GIEGraphTargetAMDGPU.cpp). \p IsLegalized is the
/// position after the legalizer, \p IsRegBankSelected a function whose
/// registers have banks (the pass only reports there).
std::unique_ptr<TargetCosts> createAMDGPUTargetCosts(const MachineFunction &MF,
                                                     bool IsLegalized,
                                                     bool IsRegBankSelected);

} // namespace egraph
} // namespace llvm

#endif // GISELEGRAPHSYNTH_GIEGRAPHTARGETCOSTS_H
