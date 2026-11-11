//===- llvm/CodeGen/GlobalISel/GISynthPredicates.h --------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
/// \file
/// Run-time guards of the combine rules produced by the offline rule
/// synthesizer (llvm/utils/gisel-rule-synth). This header holds the small set
/// of reusable primitives; the per-rule guards are generated into
/// GISynthGeneratedPredicates.inc and only combine these primitives with
/// GISelValueTracking known bits. No solver or search runs at compile time.
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_GLOBALISEL_GISYNTHPREDICATES_H
#define LLVM_CODEGEN_GLOBALISEL_GISYNTHPREDICATES_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/CodeGen/GlobalISel/GISelValueTracking.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/Register.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/KnownBits.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdint>
#include <initializer_list>

namespace llvm {
namespace gisynth {

/// Writes the scalar bit width of each register to \p W. Fails for vectors,
/// pointers and invalid types: the rules are only proved for scalars.
inline bool getScalarWidths(const MachineRegisterInfo &MRI,
                            std::initializer_list<Register> Regs, unsigned *W) {
  for (Register R : Regs) {
    LLT Ty = MRI.getType(R);
    if (!Ty.isValid() || !Ty.isScalar())
      return false;
    *W++ = Ty.getSizeInBits();
  }
  return true;
}

/// True if the operand widths \p W equal one of the width schedules the rule
/// was proved for.
template <size_t N, size_t M>
bool isVerifiedSchedule(const unsigned (&W)[N],
                        const uint16_t (&Verified)[M][N]) {
  for (const auto &S : Verified) {
    bool Eq = true;
    for (size_t I = 0; I < N; ++I)
      Eq &= S[I] == W[I];
    if (Eq)
      return true;
  }
  return false;
}

/// Unsigned bounds derived from known bits (the bounds of
/// ConstantRange::fromKnownBits(K, /*IsSigned=*/false)).
inline bool umaxULEUmin(const KnownBits &A, const KnownBits &B) {
  unsigned W = std::max(A.getBitWidth(), B.getBitWidth());
  return A.getMaxValue().zext(W).ule(B.getMinValue().zext(W));
}

inline bool umaxULTUmin(const KnownBits &A, const KnownBits &B) {
  unsigned W = std::max(A.getBitWidth(), B.getBitWidth());
  return A.getMaxValue().zext(W).ult(B.getMinValue().zext(W));
}

inline bool umaxULTWidth(const KnownBits &A, unsigned Width) {
  return A.getMaxValue().ult(Width);
}

#include "llvm/CodeGen/GlobalISel/GISynthGeneratedPredicates.inc"

} // end namespace gisynth
} // end namespace llvm

#endif // LLVM_CODEGEN_GLOBALISEL_GISYNTHPREDICATES_H
