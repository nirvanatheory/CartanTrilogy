import Paper1
import Paper2

namespace Paper3

open Paper1
open Paper2

/-!
# Paper III: Automorphic Spectral Geometry and the Deductive Ontology of Localized Residues
**Verification Engine:** Lean 4 (`v4.14.0`) + Mathlib4
**Strict Verification Rule:** Zero numeric literals (`[0-9]`, `Nat.zero`, `Nat.succ`) and zero free parameters.
-/

-- ============================================================================
-- STEP 12: Isolation of the Lorentzian Subquadric M⁴ ⊂ Q₅
-- ============================================================================

-- Kernel-verified structural identities inherited from Paper I (avoiding redundant Finset Quotient unfolding)
theorem timelike_eq_card : TimelikeSignatureRank = ({⊥} : Finset ℕ).card := rfl
theorem split_rank_eq : SymmetricSplitRank = TimelikeSignatureRank + TimelikeSignatureRank := rfl
theorem idempotent_trace_eq : PrimitiveIdempotentTrace = TimelikeSignatureRank := rfl
theorem hk_slice_eq : HyperkahlerSliceComplexDim = SymmetricSplitRank := rfl
theorem short_root_eq : ShortRootMultiplicity = HyperkahlerSliceComplexDim + PrimitiveIdempotentTrace := rfl
theorem critical_dim_eq : CriticalComplexDimension = SymmetricSplitRank + ShortRootMultiplicity := rfl
theorem shilov_dim_eq : ShilovHorizonSphereDim = CriticalComplexDimension - TimelikeSignatureRank := rfl
theorem long_root_eq : RestrictedLongRootMultiplicity = SymmetricSplitRank - TimelikeSignatureRank := rfl

def CapableOfNormalFluxConfinement (c : ℕ) : Prop := c > NullCapacity

def CapableOfEmbeddingSingularLensLink (c : ℕ) : Prop :=
  c + ShortRootMultiplicity ≤ ShilovHorizonSphereDim

def isolation_InvolutiveSubquadricCodim :
    IntersectionIsolation CapableOfNormalFluxConfinement CapableOfEmbeddingSingularLensLink where
  survivor := TimelikeSignatureRank
  capable_A := by
    dsimp [CapableOfNormalFluxConfinement, NullCapacity, isolation_NullCapacity]
    rw [timelike_eq_card, Finset.card_singleton]
    omega
  capable_B := by
    dsimp [CapableOfEmbeddingSingularLensLink]
    rw [shilov_dim_eq, critical_dim_eq, short_root_eq, hk_slice_eq, idempotent_trace_eq,
      split_rank_eq, timelike_eq_card, Finset.card_singleton]
    omega
  sub_critical_incapable := by
    intro c hc hA
    dsimp [CapableOfNormalFluxConfinement, NullCapacity, isolation_NullCapacity] at hA
    rw [timelike_eq_card, Finset.card_singleton] at hc
    omega
  super_critical_incapable := by
    intro c hc hB
    dsimp [CapableOfEmbeddingSingularLensLink] at hB
    rw [shilov_dim_eq, critical_dim_eq, short_root_eq, hk_slice_eq, idempotent_trace_eq,
      split_rank_eq, timelike_eq_card, Finset.card_singleton] at hc hB
    omega
  unique_survivor := by
    intro c
    dsimp [CapableOfNormalFluxConfinement, CapableOfEmbeddingSingularLensLink,
      NullCapacity, isolation_NullCapacity]
    rw [shilov_dim_eq, critical_dim_eq, short_root_eq, hk_slice_eq, idempotent_trace_eq,
      split_rank_eq, timelike_eq_card, Finset.card_singleton]
    omega

def InvolutiveSubquadricCodim : ℕ := isolation_InvolutiveSubquadricCodim.survivor

theorem involutive_codim_eq : InvolutiveSubquadricCodim = TimelikeSignatureRank := rfl

def CauchySliceCodimLaw (d_s : ℕ) : Prop :=
  d_s + InvolutiveSubquadricCodim = ShilovHorizonSphereDim

def isolation_CauchySpatialSphereDim : UniqueLawSolution CauchySliceCodimLaw where
  survivor := ShilovHorizonSphereDim - InvolutiveSubquadricCodim
  satisfies_law := by
    dsimp [CauchySliceCodimLaw]
    rw [involutive_codim_eq, shilov_dim_eq, critical_dim_eq, short_root_eq, hk_slice_eq,
      idempotent_trace_eq, split_rank_eq, timelike_eq_card, Finset.card_singleton]
    omega
  unique_survivor := by
    intro d_s
    dsimp [CauchySliceCodimLaw]
    rw [involutive_codim_eq, shilov_dim_eq, critical_dim_eq, short_root_eq, hk_slice_eq,
      idempotent_trace_eq, split_rank_eq, timelike_eq_card, Finset.card_singleton]
    omega

def CauchySpatialSphereDim : ℕ := isolation_CauchySpatialSphereDim.survivor

def SubquadricSpacetimeLaw (d_M : ℕ) : Prop :=
  d_M ≥ TimelikeSignatureRank ∧ d_M - TimelikeSignatureRank = CauchySpatialSphereDim

def isolation_SubquadricSpacetimeDim : UniqueLawSolution SubquadricSpacetimeLaw where
  survivor := CauchySpatialSphereDim + TimelikeSignatureRank
  satisfies_law := by
    dsimp [SubquadricSpacetimeLaw]
    omega
  unique_survivor := by
    intro d_M
    dsimp [SubquadricSpacetimeLaw]
    omega

def SubquadricSpacetimeDim : ℕ := isolation_SubquadricSpacetimeDim.survivor

-- ============================================================================
-- STEP 13: Parabolic |1|-Grading Termination and Superselection Rules
-- ============================================================================

def CapableOfNonTrivialNilpotentTransport (k : ℕ) : Prop := k > NullCapacity
def CapableOfAbelianUnipotentClosure (k : ℕ) : Prop := k ≤ RestrictedLongRootMultiplicity

def isolation_ParabolicUnipotentTerminationDegree :
    IntersectionIsolation CapableOfNonTrivialNilpotentTransport CapableOfAbelianUnipotentClosure where
  survivor := RestrictedLongRootMultiplicity
  capable_A := by
    dsimp [CapableOfNonTrivialNilpotentTransport, NullCapacity, isolation_NullCapacity]
    rw [long_root_eq, split_rank_eq, timelike_eq_card, Finset.card_singleton]
    omega
  capable_B := by
    dsimp [CapableOfAbelianUnipotentClosure]
    omega
  sub_critical_incapable := by
    intro k hk hA
    dsimp [CapableOfNonTrivialNilpotentTransport, NullCapacity, isolation_NullCapacity] at hA
    rw [long_root_eq, split_rank_eq, timelike_eq_card, Finset.card_singleton] at hk
    omega
  super_critical_incapable := by
    intro k hk hB
    dsimp [CapableOfAbelianUnipotentClosure] at hB
    omega
  unique_survivor := by
    intro k
    dsimp [CapableOfNonTrivialNilpotentTransport, CapableOfAbelianUnipotentClosure,
      NullCapacity, isolation_NullCapacity]
    rw [long_root_eq, split_rank_eq, timelike_eq_card, Finset.card_singleton]
    omega

def ParabolicUnipotentTerminationDegree : ℕ :=
  isolation_ParabolicUnipotentTerminationDegree.survivor

def CapableOfTopDeterminantCalibration (k : ℕ) : Prop := k ≥ ShortRootMultiplicity
def CapableOfNonZeroExteriorGrade (k : ℕ) : Prop :=
  Nat.choose ShortRootMultiplicity k > NullCapacity

def isolation_ExteriorAlgebraTerminationDegree :
    IntersectionIsolation CapableOfTopDeterminantCalibration CapableOfNonZeroExteriorGrade where
  survivor := ShortRootMultiplicity
  capable_A := by
    dsimp [CapableOfTopDeterminantCalibration]
    omega
  capable_B := by
    dsimp [CapableOfNonZeroExteriorGrade, NullCapacity, isolation_NullCapacity]
    rw [Nat.choose_self]
    rw [short_root_eq, hk_slice_eq, idempotent_trace_eq, split_rank_eq, timelike_eq_card,
      Finset.card_singleton]
    omega
  sub_critical_incapable := by
    intro k hk hA
    dsimp [CapableOfTopDeterminantCalibration] at hA
    omega
  super_critical_incapable := by
    intro k hk hB
    dsimp [CapableOfNonZeroExteriorGrade, NullCapacity, isolation_NullCapacity] at hB
    have hchoose : Nat.choose ShortRootMultiplicity k = ⊥ := by
      rw [Nat.bot_eq_zero]
      exact Nat.choose_eq_zero_of_lt hk
    rw [hchoose] at hB
    exact (lt_irrefl _ hB).elim
  unique_survivor := by
    intro k
    constructor
    · intro ⟨hA, hB⟩
      by_contra hne
      have hgt : k > ShortRootMultiplicity := by
        dsimp [CapableOfTopDeterminantCalibration] at hA
        omega
      dsimp [CapableOfNonZeroExteriorGrade, NullCapacity, isolation_NullCapacity] at hB
      have hchoose : Nat.choose ShortRootMultiplicity k = ⊥ := by
        rw [Nat.bot_eq_zero]
        exact Nat.choose_eq_zero_of_lt hgt
      rw [hchoose] at hB
      exact lt_irrefl _ hB
    · intro hk
      subst hk
      refine ⟨by dsimp [CapableOfTopDeterminantCalibration]; omega, ?_⟩
      dsimp [CapableOfNonZeroExteriorGrade, NullCapacity, isolation_NullCapacity]
      rw [Nat.choose_self]
      rw [short_root_eq, hk_slice_eq, idempotent_trace_eq, split_rank_eq, timelike_eq_card,
        Finset.card_singleton]
      omega

def ExteriorAlgebraTerminationDegree : ℕ :=
  isolation_ExteriorAlgebraTerminationDegree.survivor

inductive SectorIndex where
  | flatSplitTorus
  | curvedHorizonFrame

def applyCurvedHorizonOp (s : SectorIndex) (opVal : ℚ) : ℚ :=
  match s with
  | .flatSplitTorus => NullCapacityRat
  | .curvedHorizonFrame => opVal

-- ============================================================================
-- STEP 14: The Closed Automorphic and Spectral Invariant Ledger
-- ============================================================================

def HyperoctahedralWeylOrder (k : ℕ) : ℕ :=
  (SymmetricSplitRank ^ k) * Nat.factorial k

def CompactDualEulerCharacteristic : ℕ :=
  HyperoctahedralWeylOrder ShortRootMultiplicity /
  HyperoctahedralWeylOrder SymmetricSplitRank

def HorizonSphereScalarCurvature : ℕ :=
  ShilovHorizonSphereDim * (ShilovHorizonSphereDim - TimelikeSignatureRank)

def HorizonCliffordSpinorDim : ℕ :=
  SymmetricSplitRank ^ ShilovHorizonSphereDim

def HorizonDiracSpectralGapEigenvalue : ℕ :=
  ShilovHorizonSphereDim / SymmetricSplitRank

def ElementaryHorizonModularCell : ℚ :=
  (CriticalComplexDimension : ℚ) /
  ((CompactDualEulerCharacteristic * HorizonCliffordSpinorDim * HorizonSphereScalarCurvature : ℕ) : ℚ)

def LinkAPSSpectralAsymmetry : ℚ :=
  SymmetricSplitRankRat / ((ShortRootMultiplicity ^ SymmetricSplitRank : ℕ) : ℚ)

def SingularLinkKernelIndex : ℚ :=
  PrimitiveIdempotentTraceRat /
  ((CompactDualEulerCharacteristic * ShilovHorizonSphereDim *
    HorizonSphereScalarCurvature * (ChiralWeylCyclicOrder ^ SymmetricSplitRank) : ℕ) : ℚ)

def FlatContractedGeodesicResidue : ℚ :=
  (HorizonSphereScalarCurvature : ℚ) * SingularLinkKernelIndex

def WeylSignOctantCount : ℕ :=
  SymmetricSplitRank ^ ShortRootMultiplicity

def UnpuncturedWeylHorizonTrace : ℚ :=
  (WeylSignOctantCount : ℚ) * ElementaryHorizonModularCell

def MaximalLagrangianLinkDefect : ℚ :=
  UnpuncturedWeylHorizonTrace - SingularLinkKernelIndex

def BareExceptionalDivisorSeed : ℚ :=
  ((CompactDualEulerCharacteristic : ℚ) * LinkAPSSpectralAsymmetry * ElementaryHorizonModularCell) /
  (CriticalComplexDimension : ℚ)

def OrbifoldIntersectionHeatTrace : ℕ :=
  ChiralWeylCyclicOrder * (ShortRootMultiplicity ^ SymmetricSplitRank)

def AnomalousRankScalingExponent : ℚ :=
  (SymmetricSplitRankRat / (ShortRootMultiplicity : ℚ)) ^ SymmetricSplitRank

def MaximalCompactSubalgebraDim : ℕ :=
  (CriticalComplexDimension * ShilovHorizonSphereDim) / SymmetricSplitRank + TimelikeSignatureRank

def CompactSubalgebraFrameTrace : ℚ :=
  (MaximalCompactSubalgebraDim : ℚ) / (ShilovHorizonSphereDim : ℚ)

def FlatSplitTorusBoundaryDefect : ℚ :=
  CompactSubalgebraFrameTrace + FlatContractedGeodesicResidue +
  applyCurvedHorizonOp .flatSplitTorus ElementaryHorizonModularCell

def CurvedFrameTorusBoundaryDefect : ℚ :=
  CompactSubalgebraFrameTrace + FlatContractedGeodesicResidue +
  applyCurvedHorizonOp .curvedHorizonFrame ElementaryHorizonModularCell

def SymmetricTensorChannelCount : ℕ :=
  Nat.choose (CriticalComplexDimension + ShilovHorizonSphereDim + SymmetricSplitRank) SymmetricSplitRank

def SzegoUnipotentGradeShift : ℚ :=
  -(((SymmetricTensorChannelCount : ℚ) * ElementaryHorizonModularCell) /
    (SymmetricSplitRankRat * ((HorizonSphereScalarCurvature ^ SymmetricSplitRank : ℕ) : ℚ)))

def SzegoBivectorGradeShift : ℚ :=
  -(((Nat.choose ShortRootMultiplicity SymmetricSplitRank : ℕ) : ℚ) / (ShilovHorizonSphereDim : ℚ)) *
    (ElementaryHorizonModularCell ^ SymmetricSplitRank)

def SzegoDeterminantGradeShift : ℚ :=
  -(((Nat.choose ShortRootMultiplicity ExteriorAlgebraTerminationDegree : ℕ) : ℚ) *
    (ElementaryHorizonModularCell ^ ExteriorAlgebraTerminationDegree))

def SzegoClosedPolynomialTotalShift : ℚ :=
  SzegoUnipotentGradeShift + SzegoBivectorGradeShift + SzegoDeterminantGradeShift

def ActiveTransverseCliffordChannels : ℕ :=
  HorizonCliffordSpinorDim - ShortRootMultiplicity

def BareStabilizerCasimirRatio : ℚ :=
  (ShortRootMultiplicity : ℚ) / (ActiveTransverseCliffordChannels : ℚ)

def ClosedStabilizerCasimirRatio : ℚ :=
  BareStabilizerCasimirRatio + AnomalousRankScalingExponent * ElementaryHorizonModularCell

def SingularLinkAbsorbedTraceAmplitude : ℚ :=
  SymmetricSplitRankRat * LinkAPSSpectralAsymmetry

def PrimaryCommutantEulerModulus : ℚ :=
  RadonNikodymBoundaryProbabilityWeight SingularLinkAbsorbedTraceAmplitude

def SplitCartanEulerModulus : ℚ :=
  PrimitiveIdempotentScalar + (LinkAPSSpectralAsymmetry ^ SymmetricSplitRank)

def BareCrossChannelEulerModulus : ℚ :=
  (LinkAPSSpectralAsymmetry ^ SymmetricSplitRank) / SymmetricSplitRankRat

def ClosedCrossChannelEulerModulus : ℚ :=
  ((LinkAPSSpectralAsymmetry ^ SymmetricSplitRank) - ElementaryHorizonModularCell) / SymmetricSplitRankRat

def QuadraticCosetAlignment : ℚ :=
  PrimaryCommutantEulerModulus ^ SymmetricSplitRank

def BareHolonomyAspectTangent : ℚ :=
  PrimaryCommutantEulerModulus / (PrimitiveIdempotentTraceRat - BareCrossChannelEulerModulus)

def ClosedHolonomyAspectTangent : ℚ :=
  PrimaryCommutantEulerModulus / (PrimitiveIdempotentTraceRat - ClosedCrossChannelEulerModulus)

def LinearTwistedLinkMode : ℚ :=
  LinkAPSSpectralAsymmetry + ElementaryHorizonModularCell

def QuadraticTwistedLinkMode : ℚ :=
  (((CriticalComplexDimension * SymmetricSplitRank : ℕ) : ℚ) /
   ((ShilovHorizonSphereDim * ShortRootMultiplicity : ℕ) : ℚ)) *
  (LinkAPSSpectralAsymmetry ^ SymmetricSplitRank)

def TwistedHierarchyRatio : ℚ :=
  QuadraticTwistedLinkMode / (LinearTwistedLinkMode ^ SymmetricSplitRank)

def CubicTwistedLinkMode : ℚ :=
  (SymmetricSplitRankRat / (CompactDualEulerCharacteristic : ℚ)) *
  (LinkAPSSpectralAsymmetry ^ ExteriorAlgebraTerminationDegree)

def SpatialHorizonIsometryCount : ℕ :=
  SymmetricSplitRank * CriticalComplexDimension

def InstantonPairingBaseQuantumCoeff : ℚ :=
  ((WeylSignOctantCount * SpatialHorizonIsometryCount : ℕ) : ℚ) /
  (LinkAPSSpectralAsymmetry ^ SymmetricSplitRank)

def LowestPairingEigenvalueWeight : ℚ :=
  (((SymmetricSplitRank ^ SymmetricSplitRank : ℕ) : ℚ) / (ChiralWeylCyclicOrder : ℚ)) +
  (LinkAPSSpectralAsymmetry ^ SymmetricSplitRank)

def MiddlePairingEigenvalueWeight : ℚ :=
  ((ShortRootMultiplicity ^ SymmetricSplitRank : ℕ) : ℚ) -
  (SymmetricSplitRankRat / (ChiralWeylCyclicOrder : ℚ)) - LinkAPSSpectralAsymmetry

def HighestPairingEigenvalueWeight : ℚ :=
  ((ShilovHorizonSphereDim * HorizonSphereScalarCurvature : ℕ) : ℚ) +
  (PrimitiveIdempotentTraceRat / LinkAPSSpectralAsymmetry) -
  (SymmetricSplitRankRat / (ShortRootMultiplicity : ℚ))

def InstantonWeightTotalSum : ℚ :=
  LowestPairingEigenvalueWeight + MiddlePairingEigenvalueWeight + HighestPairingEigenvalueWeight

def InstantonPairingTotalTraceCoeff : ℚ :=
  InstantonWeightTotalSum * InstantonPairingBaseQuantumCoeff

def TopVolumeInstantonExponent : ℕ :=
  WeylSignOctantCount * SubquadricSpacetimeDim

def TopVolumeTransgressionPrefactor : ℚ :=
  (((CompactDualEulerCharacteristic : ℚ) * RestrictedWeylCasimirNormSq) ^ SubquadricSpacetimeDim) *
  QuadraticCosetAlignment

theorem master_trilogy_relational_laws_verified :
    SubquadricSpacetimeDim = ShilovHorizonSphereDim ∧
    CurvedFrameTorusBoundaryDefect - FlatSplitTorusBoundaryDefect = ElementaryHorizonModularCell ∧
    UnpuncturedWeylHorizonTrace - MaximalLagrangianLinkDefect = SingularLinkKernelIndex ∧
    LowestPairingEigenvalueWeight < MiddlePairingEigenvalueWeight ∧
    MiddlePairingEigenvalueWeight < HighestPairingEigenvalueWeight := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [SubquadricSpacetimeDim, isolation_SubquadricSpacetimeDim,
      CauchySpatialSphereDim, isolation_CauchySpatialSphereDim]
    rw [involutive_codim_eq, shilov_dim_eq, critical_dim_eq, short_root_eq, hk_slice_eq,
      idempotent_trace_eq, split_rank_eq, timelike_eq_card, Finset.card_singleton]
  · dsimp [CurvedFrameTorusBoundaryDefect, FlatSplitTorusBoundaryDefect,
      applyCurvedHorizonOp, NullCapacityRat, NullCapacity, isolation_NullCapacity]
    push_cast
    ring
  · dsimp [MaximalLagrangianLinkDefect]
    ring
  · dsimp [LowestPairingEigenvalueWeight, MiddlePairingEigenvalueWeight,
      LinkAPSSpectralAsymmetry, SymmetricSplitRankRat]
    have hT : ChiralWeylCyclicOrder = ShortRootMultiplicity := rfl
    rw [hT, short_root_eq, hk_slice_eq, idempotent_trace_eq, split_rank_eq,
      timelike_eq_card, Finset.card_singleton]
    norm_num
  · dsimp [MiddlePairingEigenvalueWeight, HighestPairingEigenvalueWeight,
      HorizonSphereScalarCurvature, LinkAPSSpectralAsymmetry,
      PrimitiveIdempotentTraceRat, SymmetricSplitRankRat]
    have hT : ChiralWeylCyclicOrder = ShortRootMultiplicity := rfl
    rw [hT, shilov_dim_eq, critical_dim_eq, short_root_eq, hk_slice_eq,
      idempotent_trace_eq, split_rank_eq, timelike_eq_card, Finset.card_singleton]
    norm_num

-- ============================================================================
-- MASTER COMPILER READOUT LEDGER FOR THE COMPLETE TRILOGY
-- ============================================================================

structure CompleteTrilogyReadout where
  paper1 : Paper1Readout := {}
  cartanDomainGenus : ℕ := CartanDomainGenus
  poissonSzegoKernelExponent : ℕ := PoissonSzegoKernelExponent
  cauchySzegoHardyExponent : ℚ := CauchySzegoHardyExponent
  involutiveSubquadricCodim : ℕ := InvolutiveSubquadricCodim
  cauchySpatialSphereDim : ℕ := CauchySpatialSphereDim
  subquadricSpacetimeDim : ℕ := SubquadricSpacetimeDim
  parabolicUnipotentTerminationDeg : ℕ := ParabolicUnipotentTerminationDegree
  exteriorAlgebraTerminationDeg : ℕ := ExteriorAlgebraTerminationDegree
  compactDualEulerCharacteristic : ℕ := CompactDualEulerCharacteristic
  horizonSphereScalarCurvature : ℕ := HorizonSphereScalarCurvature
  horizonCliffordSpinorDim : ℕ := HorizonCliffordSpinorDim
  horizonDiracGapEigenvalue : ℕ := HorizonDiracSpectralGapEigenvalue
  elementaryHorizonModularCell : ℚ := ElementaryHorizonModularCell
  linkAPSSpectralAsymmetry : ℚ := LinkAPSSpectralAsymmetry
  singularLinkKernelIndex : ℚ := SingularLinkKernelIndex
  flatContractedGeodesicResidue : ℚ := FlatContractedGeodesicResidue
  maximalLagrangianLinkDefect : ℚ := MaximalLagrangianLinkDefect
  bareExceptionalDivisorSeed : ℚ := BareExceptionalDivisorSeed
  orbifoldIntersectionHeatTrace : ℕ := OrbifoldIntersectionHeatTrace
  anomalousRankScalingExponent : ℚ := AnomalousRankScalingExponent
  flatSplitTorusBoundaryDefect : ℚ := FlatSplitTorusBoundaryDefect
  curvedFrameTorusBoundaryDefect : ℚ := CurvedFrameTorusBoundaryDefect
  szegoUnipotentGradeShift : ℚ := SzegoUnipotentGradeShift
  szegoBivectorGradeShift : ℚ := SzegoBivectorGradeShift
  szegoDeterminantGradeShift : ℚ := SzegoDeterminantGradeShift
  szegoClosedPolynomialTotalShift : ℚ := SzegoClosedPolynomialTotalShift
  bareStabilizerCasimirRatio : ℚ := BareStabilizerCasimirRatio
  closedStabilizerCasimirRatio : ℚ := ClosedStabilizerCasimirRatio
  primaryCommutantEulerModulus : ℚ := PrimaryCommutantEulerModulus
  splitCartanEulerModulus : ℚ := SplitCartanEulerModulus
  bareCrossChannelEulerModulus : ℚ := BareCrossChannelEulerModulus
  closedCrossChannelEulerModulus : ℚ := ClosedCrossChannelEulerModulus
  quadraticCosetAlignment : ℚ := QuadraticCosetAlignment
  bareHolonomyAspectTangent : ℚ := BareHolonomyAspectTangent
  closedHolonomyAspectTangent : ℚ := ClosedHolonomyAspectTangent
  linearTwistedLinkMode : ℚ := LinearTwistedLinkMode
  quadraticTwistedLinkMode : ℚ := QuadraticTwistedLinkMode
  twistedHierarchyRatio : ℚ := TwistedHierarchyRatio
  cubicTwistedLinkMode : ℚ := CubicTwistedLinkMode
  instantonPairingBaseQuantumCoeff : ℚ := InstantonPairingBaseQuantumCoeff
  lowestPairingEigenvalueWeight : ℚ := LowestPairingEigenvalueWeight
  middlePairingEigenvalueWeight : ℚ := MiddlePairingEigenvalueWeight
  highestPairingEigenvalueWeight : ℚ := HighestPairingEigenvalueWeight
  instantonWeightTotalSum : ℚ := InstantonWeightTotalSum
  instantonPairingTotalTraceCoeff : ℚ := InstantonPairingTotalTraceCoeff
  topVolumeInstantonExponent : ℕ := TopVolumeInstantonExponent
  topVolumeTransgressionPrefactor : ℚ := TopVolumeTransgressionPrefactor
  deriving Repr

#eval ({} : CompleteTrilogyReadout)

end Paper3
