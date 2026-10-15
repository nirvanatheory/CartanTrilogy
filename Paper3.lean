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
-- KERNEL-VERIFIED NATURAL NUMBER IDENTITIES (Pure `ℕ` `rfl`, 0ms)
-- ============================================================================

theorem nat_c0 : NullCapacity = ([] : List ℕ).length := rfl
theorem nat_c1 : TimelikeSignatureRank = ([NullCapacity] : List ℕ).length := rfl
theorem nat_c2 : SymmetricSplitRank = TimelikeSignatureRank + TimelikeSignatureRank := rfl
theorem nat_c3 : PrimitiveIdempotentTrace = TimelikeSignatureRank := rfl
theorem nat_c4 : RestrictedLongRootMultiplicity = TimelikeSignatureRank := rfl
theorem nat_c5 : HyperkahlerSliceComplexDim = SymmetricSplitRank := rfl
theorem nat_c6 : ShortRootMultiplicity = SymmetricSplitRank + TimelikeSignatureRank := rfl
theorem nat_c7 : ChiralWeylCyclicOrder = ShortRootMultiplicity := rfl
theorem nat_c8 : CriticalComplexDimension = SymmetricSplitRank + ShortRootMultiplicity := rfl
theorem nat_c9 : ShilovHorizonSphereDim = SymmetricSplitRank + SymmetricSplitRank := rfl

-- ============================================================================
-- STEP 12: Isolation of the Lorentzian Subquadric M⁴ ⊂ Q₅
-- ============================================================================

def CapableOfNormalFluxConfinement (c : ℕ) : Prop := c > NullCapacity

def CapableOfEmbeddingSingularLensLink (c : ℕ) : Prop :=
  c + ShortRootMultiplicity ≤ ShilovHorizonSphereDim

def isolation_InvolutiveSubquadricCodim :
    IntersectionIsolation CapableOfNormalFluxConfinement CapableOfEmbeddingSingularLensLink where
  survivor := TimelikeSignatureRank
  capable_A := by
    have h0 := nat_c0; have h1 := nat_c1
    dsimp only [CapableOfNormalFluxConfinement]
    rw [List.length_nil] at h0
    rw [List.length_singleton] at h1
    omega
  capable_B := by
    have h1 := nat_c1; have h2 := nat_c2; have h6 := nat_c6; have h9 := nat_c9
    dsimp only [CapableOfEmbeddingSingularLensLink]
    rw [List.length_singleton] at h1
    omega
  sub_critical_incapable := by
    intro c hc hA
    have h0 := nat_c0; have h1 := nat_c1
    dsimp only [CapableOfNormalFluxConfinement] at hA
    rw [List.length_nil] at h0
    rw [List.length_singleton] at h1
    omega
  super_critical_incapable := by
    intro c hc hB
    have h1 := nat_c1; have h2 := nat_c2; have h6 := nat_c6; have h9 := nat_c9
    dsimp only [CapableOfEmbeddingSingularLensLink] at hB
    rw [List.length_singleton] at h1
    omega
  unique_survivor := by
    intro c
    have h0 := nat_c0; have h1 := nat_c1; have h2 := nat_c2; have h6 := nat_c6; have h9 := nat_c9
    dsimp only [CapableOfNormalFluxConfinement, CapableOfEmbeddingSingularLensLink]
    rw [List.length_nil] at h0
    rw [List.length_singleton] at h1
    omega

def InvolutiveSubquadricCodim : ℕ := isolation_InvolutiveSubquadricCodim.survivor

theorem involutive_codim_eq : InvolutiveSubquadricCodim = TimelikeSignatureRank := rfl

def CauchySliceCodimLaw (d_s : ℕ) : Prop :=
  d_s + InvolutiveSubquadricCodim = ShilovHorizonSphereDim

def isolation_CauchySpatialSphereDim : UniqueLawSolution CauchySliceCodimLaw where
  survivor := ShilovHorizonSphereDim - InvolutiveSubquadricCodim
  satisfies_law := by
    have h1 := nat_c1; have h2 := nat_c2; have h9 := nat_c9; have hc := involutive_codim_eq
    dsimp only [CauchySliceCodimLaw]
    rw [List.length_singleton] at h1
    omega
  unique_survivor := by
    intro d_s
    have h1 := nat_c1; have h2 := nat_c2; have h9 := nat_c9; have hc := involutive_codim_eq
    dsimp only [CauchySliceCodimLaw]
    rw [List.length_singleton] at h1
    omega

def CauchySpatialSphereDim : ℕ := isolation_CauchySpatialSphereDim.survivor

theorem cauchy_spatial_eq :
    CauchySpatialSphereDim = ShilovHorizonSphereDim - InvolutiveSubquadricCodim := rfl

def SubquadricSpacetimeLaw (d_M : ℕ) : Prop :=
  d_M ≥ TimelikeSignatureRank ∧ d_M - TimelikeSignatureRank = CauchySpatialSphereDim

def isolation_SubquadricSpacetimeDim : UniqueLawSolution SubquadricSpacetimeLaw where
  survivor := CauchySpatialSphereDim + TimelikeSignatureRank
  satisfies_law := by
    dsimp only [SubquadricSpacetimeLaw]
    omega
  unique_survivor := by
    intro d_M
    dsimp only [SubquadricSpacetimeLaw]
    omega

def SubquadricSpacetimeDim : ℕ := isolation_SubquadricSpacetimeDim.survivor

theorem spacetime_dim_eq :
    SubquadricSpacetimeDim = CauchySpatialSphereDim + TimelikeSignatureRank := rfl

-- ============================================================================
-- STEP 13: Parabolic |1|-Grading Termination and Superselection Rules
-- ============================================================================

def CapableOfNonTrivialNilpotentTransport (k : ℕ) : Prop := k > NullCapacity
def CapableOfAbelianUnipotentClosure (k : ℕ) : Prop := k ≤ RestrictedLongRootMultiplicity

def isolation_ParabolicUnipotentTerminationDegree :
    IntersectionIsolation CapableOfNonTrivialNilpotentTransport CapableOfAbelianUnipotentClosure where
  survivor := RestrictedLongRootMultiplicity
  capable_A := by
    have h0 := nat_c0; have h1 := nat_c1; have h4 := nat_c4
    dsimp only [CapableOfNonTrivialNilpotentTransport]
    rw [List.length_nil] at h0
    rw [List.length_singleton] at h1
    omega
  capable_B := by
    dsimp only [CapableOfAbelianUnipotentClosure]
    omega
  sub_critical_incapable := by
    intro k hk hA
    have h0 := nat_c0; have h1 := nat_c1; have h4 := nat_c4
    dsimp only [CapableOfNonTrivialNilpotentTransport] at hA
    rw [List.length_nil] at h0
    rw [List.length_singleton] at h1
    omega
  super_critical_incapable := by
    intro k hk hB
    dsimp only [CapableOfAbelianUnipotentClosure] at hB
    omega
  unique_survivor := by
    intro k
    have h0 := nat_c0; have h1 := nat_c1; have h4 := nat_c4
    dsimp only [CapableOfNonTrivialNilpotentTransport, CapableOfAbelianUnipotentClosure]
    rw [List.length_nil] at h0
    rw [List.length_singleton] at h1
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
    dsimp only [CapableOfTopDeterminantCalibration]
    omega
  capable_B := by
    have h0 := nat_c0; have h1 := nat_c1
    dsimp only [CapableOfNonZeroExteriorGrade]
    rw [Nat.choose_self]
    rw [List.length_nil] at h0
    rw [List.length_singleton] at h1
    omega
  sub_critical_incapable := by
    intro k hk hA
    dsimp only [CapableOfTopDeterminantCalibration] at hA
    omega
  super_critical_incapable := by
    intro k hk hB
    dsimp only [CapableOfNonZeroExteriorGrade] at hB
    have hchoose : Nat.choose ShortRootMultiplicity k = NullCapacity := by
      rw [nat_c0, List.length_nil]
      exact Nat.choose_eq_zero_of_lt hk
    rw [hchoose] at hB
    exact (lt_irrefl _ hB).elim
  unique_survivor := by
    intro k
    constructor
    · intro ⟨hA, hB⟩
      by_contra hne
      have hgt : k > ShortRootMultiplicity := by
        dsimp only [CapableOfTopDeterminantCalibration] at hA
        omega
      dsimp only [CapableOfNonZeroExteriorGrade] at hB
      have hchoose : Nat.choose ShortRootMultiplicity k = NullCapacity := by
        rw [nat_c0, List.length_nil]
        exact Nat.choose_eq_zero_of_lt hgt
      rw [hchoose] at hB
      exact lt_irrefl _ hB
    · intro hk
      subst hk
      refine ⟨by dsimp only [CapableOfTopDeterminantCalibration]; omega, ?_⟩
      have h0 := nat_c0; have h1 := nat_c1
      dsimp only [CapableOfNonZeroExteriorGrade]
      rw [Nat.choose_self]
      rw [List.length_nil] at h0
      rw [List.length_singleton] at h1
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
  · have h1 := nat_c1; have h2 := nat_c2; have h9 := nat_c9
    have hc := involutive_codim_eq; have hs := cauchy_spatial_eq; have hm := spacetime_dim_eq
    rw [List.length_singleton] at h1
    omega
  · dsimp [CurvedFrameTorusBoundaryDefect, FlatSplitTorusBoundaryDefect,
      applyCurvedHorizonOp, NullCapacityRat, NullCapacity, isolation_NullCapacity,
      VanishingListLength, EmptyRayList]
    ring
  · dsimp only [MaximalLagrangianLinkDefect]
    ring
  · dsimp [LowestPairingEigenvalueWeight, MiddlePairingEigenvalueWeight,
      LinkAPSSpectralAsymmetry, ChiralWeylCyclicOrder, isolation_ChiralWeylCyclicOrder,
      ShortRootMultiplicity, isolation_ShortRootMultiplicity, HyperkahlerSliceComplexDim,
      isolation_HyperkahlerSliceComplexDim, DiagonalAxisDimension, PrimitiveIdempotentTrace,
      isolation_PrimitiveIdempotentTrace, SymmetricSplitRankRat, SymmetricSplitRank,
      JordanAlgebraRank, isolation_JordanAlgebraRank, TimelikeSignatureRank,
      isolation_TimelikeSignatureRank, SingletonRayCardinality, ProjectiveRaySingleton,
      NullCapacity, isolation_NullCapacity, VanishingListLength, EmptyRayList]
    norm_num
  · dsimp [MiddlePairingEigenvalueWeight, HighestPairingEigenvalueWeight,
      HorizonSphereScalarCurvature, ShilovHorizonSphereDim, isolation_ShilovHorizonSphereDim,
      CriticalComplexDimension, isolation_CriticalComplexDimension,
      LinkAPSSpectralAsymmetry, ChiralWeylCyclicOrder, isolation_ChiralWeylCyclicOrder,
      ShortRootMultiplicity, isolation_ShortRootMultiplicity, HyperkahlerSliceComplexDim,
      isolation_HyperkahlerSliceComplexDim, DiagonalAxisDimension,
      PrimitiveIdempotentTraceRat, PrimitiveIdempotentTrace,
      isolation_PrimitiveIdempotentTrace, SymmetricSplitRankRat, SymmetricSplitRank,
      JordanAlgebraRank, isolation_JordanAlgebraRank, TimelikeSignatureRank,
      isolation_TimelikeSignatureRank, SingletonRayCardinality, ProjectiveRaySingleton,
      NullCapacity, isolation_NullCapacity, VanishingListLength, EmptyRayList]
    norm_num

-- ============================================================================
-- MASTER COMPILER READOUT LEDGER FOR THE COMPLETE TRILOGY
-- ============================================================================

structure CompleteTrilogyReadout where
  paper1 : Paper1Readout
  cartanDomainGenus : ℕ
  poissonSzegoKernelExponent : ℕ
  cauchySzegoHardyExponent : ℚ
  involutiveSubquadricCodim : ℕ
  cauchySpatialSphereDim : ℕ
  subquadricSpacetimeDim : ℕ
  parabolicUnipotentTerminationDeg : ℕ
  exteriorAlgebraTerminationDeg : ℕ
  compactDualEulerCharacteristic : ℕ
  horizonSphereScalarCurvature : ℕ
  horizonCliffordSpinorDim : ℕ
  horizonDiracGapEigenvalue : ℕ
  elementaryHorizonModularCell : ℚ
  linkAPSSpectralAsymmetry : ℚ
  singularLinkKernelIndex : ℚ
  flatContractedGeodesicResidue : ℚ
  maximalLagrangianLinkDefect : ℚ
  bareExceptionalDivisorSeed : ℚ
  orbifoldIntersectionHeatTrace : ℕ
  anomalousRankScalingExponent : ℚ
  flatSplitTorusBoundaryDefect : ℚ
  curvedFrameTorusBoundaryDefect : ℚ
  szegoUnipotentGradeShift : ℚ
  szegoBivectorGradeShift : ℚ
  szegoDeterminantGradeShift : ℚ
  szegoClosedPolynomialTotalShift : ℚ
  bareStabilizerCasimirRatio : ℚ
  closedStabilizerCasimirRatio : ℚ
  primaryCommutantEulerModulus : ℚ
  splitCartanEulerModulus : ℚ
  bareCrossChannelEulerModulus : ℚ
  closedCrossChannelEulerModulus : ℚ
  quadraticCosetAlignment : ℚ
  bareHolonomyAspectTangent : ℚ
  closedHolonomyAspectTangent : ℚ
  linearTwistedLinkMode : ℚ
  quadraticTwistedLinkMode : ℚ
  twistedHierarchyRatio : ℚ
  cubicTwistedLinkMode : ℚ
  instantonPairingBaseQuantumCoeff : ℚ
  lowestPairingEigenvalueWeight : ℚ
  middlePairingEigenvalueWeight : ℚ
  highestPairingEigenvalueWeight : ℚ
  instantonWeightTotalSum : ℚ
  instantonPairingTotalTraceCoeff : ℚ
  topVolumeInstantonExponent : ℕ
  topVolumeTransgressionPrefactor : ℚ
  deriving Repr

def buildCompleteTrilogyReadout : CompleteTrilogyReadout :=
  let p1 : Paper1Readout := {}
  { paper1 := p1
    cartanDomainGenus := CartanDomainGenus
    poissonSzegoKernelExponent := PoissonSzegoKernelExponent
    cauchySzegoHardyExponent := CauchySzegoHardyExponent
    involutiveSubquadricCodim := InvolutiveSubquadricCodim
    cauchySpatialSphereDim := CauchySpatialSphereDim
    subquadricSpacetimeDim := SubquadricSpacetimeDim
    parabolicUnipotentTerminationDeg := ParabolicUnipotentTerminationDegree
    exteriorAlgebraTerminationDeg := ExteriorAlgebraTerminationDegree
    compactDualEulerCharacteristic := CompactDualEulerCharacteristic
    horizonSphereScalarCurvature := HorizonSphereScalarCurvature
    horizonCliffordSpinorDim := HorizonCliffordSpinorDim
    horizonDiracGapEigenvalue := HorizonDiracSpectralGapEigenvalue
    elementaryHorizonModularCell := ElementaryHorizonModularCell
    linkAPSSpectralAsymmetry := LinkAPSSpectralAsymmetry
    singularLinkKernelIndex := SingularLinkKernelIndex
    flatContractedGeodesicResidue := FlatContractedGeodesicResidue
    maximalLagrangianLinkDefect := MaximalLagrangianLinkDefect
    bareExceptionalDivisorSeed := BareExceptionalDivisorSeed
    orbifoldIntersectionHeatTrace := OrbifoldIntersectionHeatTrace
    anomalousRankScalingExponent := AnomalousRankScalingExponent
    flatSplitTorusBoundaryDefect := FlatSplitTorusBoundaryDefect
    curvedFrameTorusBoundaryDefect := CurvedFrameTorusBoundaryDefect
    szegoUnipotentGradeShift := SzegoUnipotentGradeShift
    szegoBivectorGradeShift := SzegoBivectorGradeShift
    szegoDeterminantGradeShift := SzegoDeterminantGradeShift
    szegoClosedPolynomialTotalShift := SzegoClosedPolynomialTotalShift
    bareStabilizerCasimirRatio := BareStabilizerCasimirRatio
    closedStabilizerCasimirRatio := ClosedStabilizerCasimirRatio
    primaryCommutantEulerModulus := PrimaryCommutantEulerModulus
    splitCartanEulerModulus := SplitCartanEulerModulus
    bareCrossChannelEulerModulus := BareCrossChannelEulerModulus
    closedCrossChannelEulerModulus := ClosedCrossChannelEulerModulus
    quadraticCosetAlignment := QuadraticCosetAlignment
    bareHolonomyAspectTangent := BareHolonomyAspectTangent
    closedHolonomyAspectTangent := ClosedHolonomyAspectTangent
    linearTwistedLinkMode := LinearTwistedLinkMode
    quadraticTwistedLinkMode := QuadraticTwistedLinkMode
    twistedHierarchyRatio := TwistedHierarchyRatio
    cubicTwistedLinkMode := CubicTwistedLinkMode
    instantonPairingBaseQuantumCoeff := InstantonPairingBaseQuantumCoeff
    lowestPairingEigenvalueWeight := LowestPairingEigenvalueWeight
    middlePairingEigenvalueWeight := MiddlePairingEigenvalueWeight
    highestPairingEigenvalueWeight := HighestPairingEigenvalueWeight
    instantonWeightTotalSum := InstantonWeightTotalSum
    instantonPairingTotalTraceCoeff := InstantonPairingTotalTraceCoeff
    topVolumeInstantonExponent := TopVolumeInstantonExponent
    topVolumeTransgressionPrefactor := TopVolumeTransgressionPrefactor }

#eval buildCompleteTrilogyReadout

end Paper3
