// Helpers construct only the explicitly modeled types, preserving lane shape.
inline LLT makeSynthType(unsigned Width, char Kind, unsigned Lanes = 0,
                         bool Legacy = false) {
  LLT T;
  if (Legacy) {
    T = LLT::scalar(Width);
  } else if (Kind == 'f') {
    if (Width != 16 && Width != 32 && Width != 64)
      return LLT();
    T = LLT::floatingPoint(Width == 16   ? APFloat::S_IEEEhalf
                           : Width == 32 ? APFloat::S_IEEEsingle
                                         : APFloat::S_IEEEdouble);
  } else {
    T = LLT::integer(Width);
  }
  return Lanes ? LLT::fixed_vector(Lanes, T) : T;
}

inline LLT getSynthVectorIndexType(const MachineRegisterInfo &MRI,
                                   Register Root) {
  const MachineFunction &MF = *MRI.getVRegDef(Root)->getMF();
  return LLT::integer(MF.getSubtarget().getTargetLowering()->getVectorIdxWidth(
      MF.getDataLayout()));
}

inline bool isLegalSynthOp(const MachineRegisterInfo &MRI, Register Root,
                           unsigned Opc, std::initializer_list<LLT> Operands) {
  const MachineFunction &MF = *MRI.getVRegDef(Root)->getMF();
  const LegalizerInfo *LI = MF.getSubtarget().getLegalizerInfo();
  if (!LI)
    return false;
  const MCInstrDesc &Desc = MF.getSubtarget().getInstrInfo()->get(Opc);
  SmallVector<LLT, 4> Types;
  ArrayRef<LLT> O(Operands.begin(), Operands.size());
  for (auto [I, Info] : enumerate(Desc.operands())) {
    if (!Info.isGenericType())
      continue;
    if (I >= O.size() || !O[I].isValid())
      return false;
    unsigned Idx = Info.getGenericTypeIndex();
    if (Types.size() <= Idx)
      Types.resize(Idx + 1);
    if (Types[Idx].isValid() && Types[Idx] != O[I])
      return false;
    Types[Idx] = O[I];
  }
  if (Types.empty() || any_of(Types, [](LLT T) { return !T.isValid(); }))
    return false;
  LegalizeActions::LegalizeAction A = LI->getAction({Opc, Types}).Action;
  if (MF.getProperties().hasProperty(
          MachineFunctionProperties::Property::Legalized))
    return A == LegalizeActions::Legal;
  switch (A) {
  case LegalizeActions::Legal:
  case LegalizeActions::NarrowScalar:
  case LegalizeActions::WidenScalar:
  case LegalizeActions::FewerElements:
  case LegalizeActions::MoreElements:
  case LegalizeActions::Bitcast:
  case LegalizeActions::Lower:
  case LegalizeActions::Libcall:
  case LegalizeActions::Custom:
    return true;
  default:
    return false;
  }
}

// Literal replacements can implicitly build both a scalar constant and a
// vector splat. Check those instructions as well as the explicit RHS nodes.
inline bool isLegalSynthConstant(const MachineRegisterInfo &MRI, Register Root,
                                 LLT Ty, bool IsFP) {
  unsigned Opc = IsFP ? TargetOpcode::G_FCONSTANT : TargetOpcode::G_CONSTANT;
  if (!Ty.isVector())
    return isLegalSynthOp(MRI, Root, Opc, {Ty});
  LLT Elem = Ty.getScalarType();
  return isLegalSynthOp(MRI, Root, Opc, {Elem}) &&
         isLegalSynthOp(MRI, Root, TargetOpcode::G_BUILD_VECTOR, {Ty, Elem});
}

// Included in llvm::gisynth, after the constant/format helpers.
// Generic value-analysis contracts used by extraction and generated guards.

inline bool knownIntFitsFP(const KnownBits &K, bool Signed, unsigned FPWidth) {
  if (FPWidth != 16 && FPWidth != 32 && FPWidth != 64)
    return false;
  const fltSemantics &Sem = getIEEEFormat(FPWidth);
  unsigned P = APFloat::semanticsPrecision(Sem);
  unsigned E = APFloat::semanticsMaxExponent(Sem);
  unsigned W = K.getBitWidth() + 1;
  APInt Mag = K.getMaxValue().zext(W);
  if (Signed) {
    APInt Lo = K.getSignedMinValue().sext(W);
    APInt Hi = K.getSignedMaxValue().sext(W);
    if (Lo.isNegative())
      Lo.negate();
    if (Hi.isNegative())
      Hi.negate();
    Mag = Lo.ugt(Hi) ? Lo : Hi;
  }
  // Every possible magnitude is bounded, and all possible integers share
  // their known trailing zero bits. Include the exact power-of-two endpoint.
  for (unsigned N = 0; N <= std::min(W, E + 1); ++N) {
    unsigned BW = std::max(W + 1, E + 2);
    APInt Bound = APInt::getOneBitSet(BW, N);
    APInt Largest = APInt::getLowBitsSet(BW, P).shl(E + 1 - P);
    if (Bound.ugt(Largest))
      Bound = Largest;
    if (Mag.zext(BW).ule(Bound) &&
        K.countMinTrailingZeros() >= (N > P ? N - P : 0))
      return true;
  }
  return false;
}

struct FPValueFacts {
  FPClassTest Classes = fcAllFlags;
  // All non-poison values are finite integers; this does not imply noundef.
  bool Integral = false;
  std::optional<APFloat> Lower, Upper;
};

inline void setFiniteBounds(FPValueFacts &F, APFloat Lo, APFloat Hi) {
  if (!Lo.isFinite() || !Hi.isFinite() ||
      Lo.compare(Hi) == APFloat::cmpGreaterThan)
    return;
  F.Lower = std::move(Lo);
  F.Upper = std::move(Hi);
  F.Classes = FPClassTest(unsigned(F.Classes) & unsigned(fcFinite));
}

inline FPValueFacts joinFPFacts(FPValueFacts A, const FPValueFacts &B) {
  A.Classes = FPClassTest(unsigned(A.Classes) | unsigned(B.Classes));
  A.Integral &= B.Integral;
  if (!A.Lower || !B.Lower) {
    A.Lower.reset();
    A.Upper.reset();
  } else {
    if (B.Lower->compare(*A.Lower) == APFloat::cmpLessThan)
      A.Lower = B.Lower;
    if (B.Upper->compare(*A.Upper) == APFloat::cmpGreaterThan)
      A.Upper = B.Upper;
  }
  return A;
}

inline FPValueFacts getFPValueFacts(GISelValueTracking &VT,
                                    const MachineRegisterInfo &MRI,
                                    Register Reg, unsigned Depth = 0) {
  FPValueFacts F;
  LLT Ty = MRI.getType(Reg);
  if (!Ty.isValid() || Ty.getScalarType().isPointer() || Ty.isScalableVector())
    return F;
  unsigned W = Ty.getScalarSizeInBits();
  if (W != 16 && W != 32 && W != 64)
    return F;
  if (Ty.getScalarType().isFloat() && !Ty.getScalarType().isFloatIEEE())
    return F;
  const fltSemantics &Sem = getIEEEFormat(W);
  F.Classes = VT.computeKnownFPClass(Reg).getKnownFPClasses();
  if (auto C = getConstantBits(Reg, MRI, /*AllowSplat=*/true)) {
    APFloat V(Sem, *C);
    F.Classes = KnownFPClass(V).getKnownFPClasses();
    if (V.isFinite()) {
      setFiniteBounds(F, V, V);
      APFloat Rounded = V;
      Rounded.roundToIntegral(APFloat::rmTowardZero);
      F.Integral = Rounded.compare(V) == APFloat::cmpEqual;
    }
    return F;
  }
  const MachineInstr *MI = MRI.getVRegDef(Reg);
  if (!MI || Depth >= 6)
    return F;
  auto Child = [&](unsigned I) {
    return getFPValueFacts(VT, MRI, MI->getOperand(I).getReg(), Depth + 1);
  };
  unsigned Opc = MI->getOpcode();
  if (Opc == TargetOpcode::COPY && MI->getOperand(1).getReg().isVirtual())
    return Child(1);
  if (Opc == TargetOpcode::G_SELECT)
    return joinFPFacts(Child(2), Child(3));
  if (Opc == TargetOpcode::G_BUILD_VECTOR) {
    FPValueFacts R = Child(1);
    for (unsigned I = 2; I < MI->getNumOperands(); ++I)
      R = joinFPFacts(std::move(R), Child(I));
    return R;
  }
  if (Opc == TargetOpcode::G_SITOFP || Opc == TargetOpcode::G_UITOFP) {
    KnownBits K = VT.getKnownBits(MI->getOperand(1).getReg());
    bool Signed = Opc == TargetOpcode::G_SITOFP;
    APFloat Lo(Sem), Hi(Sem);
    Lo.convertFromAPInt(Signed ? K.getSignedMinValue() : K.getMinValue(),
                        Signed, APFloat::rmNearestTiesToEven);
    Hi.convertFromAPInt(Signed ? K.getSignedMaxValue() : K.getMaxValue(),
                        Signed, APFloat::rmNearestTiesToEven);
    setFiniteBounds(F, Lo, Hi);
    F.Integral = F.Lower.has_value();
    return F;
  }
  if (Opc == TargetOpcode::G_FNEG || Opc == TargetOpcode::G_FABS) {
    FPValueFacts A = Child(1);
    F.Integral = A.Integral;
    if (!A.Lower)
      return F;
    APFloat Lo = *A.Lower, Hi = *A.Upper;
    if (Opc == TargetOpcode::G_FNEG) {
      Lo.changeSign();
      Hi.changeSign();
      std::swap(Lo, Hi);
    } else {
      APFloat Zero = APFloat::getZero(Sem);
      bool Crosses = Lo.compare(Zero) != APFloat::cmpGreaterThan &&
                     Hi.compare(Zero) != APFloat::cmpLessThan;
      Lo.clearSign();
      Hi.clearSign();
      if (Lo.compare(Hi) == APFloat::cmpGreaterThan)
        std::swap(Lo, Hi);
      if (Crosses)
        Lo = Zero;
    }
    setFiniteBounds(F, Lo, Hi);
    return F;
  }
  bool Cast = Opc == TargetOpcode::G_FPEXT || Opc == TargetOpcode::G_FPTRUNC;
  std::optional<APFloat::roundingMode> RM;
  switch (Opc) {
  case TargetOpcode::G_FFLOOR:
    RM = APFloat::rmTowardNegative;
    break;
  case TargetOpcode::G_FCEIL:
    RM = APFloat::rmTowardPositive;
    break;
  case TargetOpcode::G_INTRINSIC_TRUNC:
    RM = APFloat::rmTowardZero;
    break;
  case TargetOpcode::G_INTRINSIC_ROUNDEVEN:
    RM = APFloat::rmNearestTiesToEven;
    break;
  case TargetOpcode::G_INTRINSIC_ROUND:
    RM = APFloat::rmNearestTiesToAway;
    break;
  default:
    break;
  }
  if (!Cast && !RM)
    return F;
  Register Src = MI->getOperand(1).getReg();
  // Numeric interval transfer uses the same IEEE environment as the proof.
  // Class queries above remain usable under other denormal modes.
  if (!hasIEEEDenormalMode(MRI, {Reg, Src}))
    return F;
  FPValueFacts A = Child(1);
  if (RM && (unsigned(F.Classes) & ~unsigned(fcFinite)) == 0)
    F.Integral = true;
  if (!A.Lower)
    return F;
  APFloat Lo = *A.Lower, Hi = *A.Upper;
  if (Cast) {
    bool Loses;
    Lo.convert(Sem, APFloat::rmNearestTiesToEven, &Loses);
    Hi.convert(Sem, APFloat::rmNearestTiesToEven, &Loses);
  } else {
    Lo.roundToIntegral(*RM);
    Hi.roundToIntegral(*RM);
  }
  setFiniteBounds(F, Lo, Hi);
  F.Integral = F.Lower && (RM.has_value() || A.Integral);
  return F;
}

inline bool knownFPInIntRange(const FPValueFacts &F, bool Signed,
                              unsigned Bits) {
  if (!F.Lower || !F.Upper || Bits == 0)
    return false;
  const fltSemantics &Sem = F.Lower->getSemantics();
  APInt L = Signed ? APInt::getSignedMinValue(Bits) : APInt(Bits, 0);
  APInt H = Signed ? APInt::getSignedMaxValue(Bits) : APInt::getMaxValue(Bits);
  APFloat Lo(Sem), Hi(Sem);
  // Round inward: accepting a rounded-up INT_MAX would admit overflow.
  Lo.convertFromAPInt(L, Signed, APFloat::rmTowardPositive);
  Hi.convertFromAPInt(H, Signed, APFloat::rmTowardNegative);
  return F.Lower->compare(Lo) != APFloat::cmpLessThan &&
         F.Upper->compare(Hi) != APFloat::cmpGreaterThan;
}
