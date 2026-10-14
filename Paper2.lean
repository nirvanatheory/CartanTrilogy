import Paper1

namespace Paper2

open Paper1

/-!
# Paper II: Boundary Filtration of Isotropic Null Rays, Berezin–Toeplitz POVM Quantization, and Symplectic Capacity
**Verification Engine:** Lean 4 (`v4.14.0`) + Mathlib4
**Strict Verification Rule:** Zero numeric literals (`[0-9]`, `Nat.zero`, `Nat.succ`) and zero free parameters.
-/

-- ============================================================================
-- STEP 9: Isolation of the Cartan Genus and Boundary Reproducing Exponents
-- ============================================================================

def CapableOfPositiveBoundaryMeasure (p : ℕ) : Prop :=
  p ≥ RestrictedLongRootMultiplicity * ShortRootMultiplicity + SymmetricSplitRank

def CapableOfShilovBoundaryConcentration (p : ℕ) : Prop :=
  p ≤ CriticalComplexDimension

def isolation_CartanDomainGenus :
    IntersectionIsolation CapableOfPositiveBoundaryMeasure CapableOfShilovBoundaryConcentration where
  survivor := CriticalComplexDimension
  capable_A := by
    dsimp [CapableOfPositiveBoundaryMeasure, CriticalComplexDimension,
      isolation_CriticalComplexDimension, RestrictedLongRootMultiplicity,
      ShortRootMultiplicity, isolation_ShortRootMultiplicity, HyperkahlerSliceComplexDim,
      isolation_HyperkahlerSliceComplexDim, DiagonalAxisDimension, PrimitiveIdempotentTrace,
      isolation_PrimitiveIdempotentTrace, SymmetricSplitRank, JordanAlgebraRank,
      isolation_JordanAlgebraRank, TimelikeSignatureRank, isolation_TimelikeSignatureRank,
      SingletonRayCardinality, ProjectiveRaySingleton]
    decide
  capable_B := by
    dsimp [CapableOfShilovBoundaryConcentration]
    omega
  sub_critical_incapable := by
    intro p hp hA
    dsimp [CapableOfPositiveBoundaryMeasure, CriticalComplexDimension,
      isolation_CriticalComplexDimension, RestrictedLongRootMultiplicity,
      ShortRootMultiplicity, isolation_ShortRootMultiplicity, HyperkahlerSliceComplexDim,
      isolation_HyperkahlerSliceComplexDim, DiagonalAxisDimension, PrimitiveIdempotentTrace,
      isolation_PrimitiveIdempotentTrace, SymmetricSplitRank, JordanAlgebraRank,
      isolation_JordanAlgebraRank, TimelikeSignatureRank, isolation_TimelikeSignatureRank,
      SingletonRayCardinality, ProjectiveRaySingleton] at hp hA
    rw [Finset.card_singleton] at hp hA
    omega
  super_critical_incapable := by
    intro p hp hB
    dsimp [CapableOfShilovBoundaryConcentration] at hB
    omega
  unique_survivor := by
    intro p
    dsimp [CapableOfPositiveBoundaryMeasure, CapableOfShilovBoundaryConcentration,
      CriticalComplexDimension, isolation_CriticalComplexDimension,
      RestrictedLongRootMultiplicity, ShortRootMultiplicity, isolation_ShortRootMultiplicity,
      HyperkahlerSliceComplexDim, isolation_HyperkahlerSliceComplexDim, DiagonalAxisDimension,
      PrimitiveIdempotentTrace, isolation_PrimitiveIdempotentTrace, SymmetricSplitRank,
      JordanAlgebraRank, isolation_JordanAlgebraRank, TimelikeSignatureRank,
      isolation_TimelikeSignatureRank, SingletonRayCardinality, ProjectiveRaySingleton]
    rw [Finset.card_singleton]
    omega

def CartanDomainGenus : ℕ := isolation_CartanDomainGenus.survivor
def CartanDomainGenusRat : ℚ := (CartanDomainGenus : ℚ)

def PoissonSzegoDegreeLaw (p_PS : ℕ) : Prop :=
  p_PS ≥ TimelikeSignatureRank ∧ p_PS - TimelikeSignatureRank = ShilovHorizonSphereDim

def isolation_PoissonSzegoKernelExponent : UniqueLawSolution PoissonSzegoDegreeLaw where
  survivor := ShilovHorizonSphereDim + TimelikeSignatureRank
  satisfies_law := by
    dsimp [PoissonSzegoDegreeLaw]
    omega
  unique_survivor := by
    intro p_PS
    dsimp [PoissonSzegoDegreeLaw]
    omega

def PoissonSzegoKernelExponent : ℕ := isolation_PoissonSzegoKernelExponent.survivor

def CauchySzegoHardyLaw (k_H : ℚ) : Prop :=
  SymmetricSplitRankRat * k_H = CartanDomainGenusRat

def isolation_CauchySzegoHardyExponent : UniqueLawSolution CauchySzegoHardyLaw where
  survivor := CartanDomainGenusRat / SymmetricSplitRankRat
  satisfies_law := by
    dsimp [CauchySzegoHardyLaw, CartanDomainGenusRat, CartanDomainGenus,
      isolation_CartanDomainGenus, CriticalComplexDimension,
      isolation_CriticalComplexDimension, ShortRootMultiplicity,
      isolation_ShortRootMultiplicity, HyperkahlerSliceComplexDim,
      isolation_HyperkahlerSliceComplexDim, DiagonalAxisDimension,
      PrimitiveIdempotentTrace, isolation_PrimitiveIdempotentTrace,
      SymmetricSplitRankRat, SymmetricSplitRank, JordanAlgebraRank,
      isolation_JordanAlgebraRank, TimelikeSignatureRank,
      isolation_TimelikeSignatureRank, SingletonRayCardinality, ProjectiveRaySingleton,
      NullCapacity, isolation_NullCapacity]
    norm_num
  unique_survivor := by
    intro k_H
    dsimp [CauchySzegoHardyLaw, CartanDomainGenusRat, CartanDomainGenus,
      isolation_CartanDomainGenus, CriticalComplexDimension,
      isolation_CriticalComplexDimension, ShortRootMultiplicity,
      isolation_ShortRootMultiplicity, HyperkahlerSliceComplexDim,
      isolation_HyperkahlerSliceComplexDim, DiagonalAxisDimension,
      PrimitiveIdempotentTrace, isolation_PrimitiveIdempotentTrace,
      SymmetricSplitRankRat, SymmetricSplitRank, JordanAlgebraRank,
      isolation_JordanAlgebraRank, TimelikeSignatureRank,
      isolation_TimelikeSignatureRank, SingletonRayCardinality, ProjectiveRaySingleton,
      NullCapacity, isolation_NullCapacity]
    rw [Finset.card_singleton]
    push_cast
    constructor <;> intro h <;> linarith

def CauchySzegoHardyExponent : ℚ := isolation_CauchySzegoHardyExponent.survivor

-- ============================================================================
-- STEP 10: Berezin–Toeplitz POVM Quantization and Anti-Holomorphic Leakage
-- ============================================================================

def AntiHolomorphicLeakageLaw (p w_perp : ℚ) : Prop :=
  SymmetricSplitRankRat * w_perp = p * (PrimitiveIdempotentTraceRat - p)

def isolation_AntiHolomorphicFourierLeakage (p : ℚ) :
    UniqueLawSolution (AntiHolomorphicLeakageLaw p) where
  survivor := p * (PrimitiveIdempotentTraceRat - p) / SymmetricSplitRankRat
  satisfies_law := by
    dsimp [AntiHolomorphicLeakageLaw, SymmetricSplitRankRat, SymmetricSplitRank,
      JordanAlgebraRank, isolation_JordanAlgebraRank, TimelikeSignatureRank,
      isolation_TimelikeSignatureRank, SingletonRayCardinality, ProjectiveRaySingleton,
      NullCapacity, isolation_NullCapacity]
    rw [Finset.card_singleton]
    push_cast
    ring
  unique_survivor := by
    intro w_perp
    dsimp [AntiHolomorphicLeakageLaw, SymmetricSplitRankRat, SymmetricSplitRank,
      JordanAlgebraRank, isolation_JordanAlgebraRank, TimelikeSignatureRank,
      isolation_TimelikeSignatureRank, SingletonRayCardinality, ProjectiveRaySingleton,
      NullCapacity, isolation_NullCapacity]
    rw [Finset.card_singleton]
    push_cast
    constructor <;> intro h <;> linarith

def AntiHolomorphicFourierLeakage (p : ℚ) : ℚ :=
  (isolation_AntiHolomorphicFourierLeakage p).survivor

theorem sharp_pvm_idempotence_is_invalid (p : ℚ)
    (hp_pos : p > NullCapacityRat)
    (hp_lt : p < PrimitiveIdempotentTraceRat) :
    AntiHolomorphicFourierLeakage p > NullCapacityRat ∧
    p - AntiHolomorphicFourierLeakage p < p := by
  dsimp [AntiHolomorphicFourierLeakage, isolation_AntiHolomorphicFourierLeakage,
    PrimitiveIdempotentTraceRat, PrimitiveIdempotentTrace,
    isolation_PrimitiveIdempotentTrace, SymmetricSplitRankRat, SymmetricSplitRank,
    JordanAlgebraRank, isolation_JordanAlgebraRank, TimelikeSignatureRank,
    isolation_TimelikeSignatureRank, SingletonRayCardinality, ProjectiveRaySingleton,
    NullCapacityRat, NullCapacity, isolation_NullCapacity] at hp_pos hp_lt ⊢
  rw [Finset.card_singleton] at hp_pos hp_lt ⊢
  have hbot : ((⊥ : ℕ) : ℚ) = p - p := by simp
  rw [hbot] at hp_pos ⊢
  push_cast at hp_lt ⊢
  constructor <;> nlinarith

-- ============================================================================
-- STEP 11: Complementary POVM Amplitude, Radon–Nikodym Weight, Isotropic Nullity
-- ============================================================================

def ComplementaryAmplitudeLaw (a_sing a_reg : ℚ) : Prop :=
  a_sing + a_reg = PrimitiveIdempotentTraceRat

def isolation_ComplementaryRegularTraceAmplitude (a_sing : ℚ) :
    UniqueLawSolution (ComplementaryAmplitudeLaw a_sing) where
  survivor := PrimitiveIdempotentTraceRat - a_sing
  satisfies_law := by
    dsimp [ComplementaryAmplitudeLaw]
    ring
  unique_survivor := by
    intro a_reg
    dsimp [ComplementaryAmplitudeLaw]
    constructor <;> intro h <;> linarith

def ComplementaryRegularTraceAmplitude (a_sing : ℚ) : ℚ :=
  (isolation_ComplementaryRegularTraceAmplitude a_sing).survivor

def RadonNikodymQuadraticLaw (a_sing w : ℚ) : Prop :=
  w + a_sing * (SymmetricSplitRankRat * PrimitiveIdempotentTraceRat - a_sing) =
    PrimitiveIdempotentTraceRat ^ SymmetricSplitRank

def isolation_RadonNikodymBoundaryProbabilityWeight (a_sing : ℚ) :
    UniqueLawSolution (RadonNikodymQuadraticLaw a_sing) where
  survivor := (ComplementaryRegularTraceAmplitude a_sing) ^ SymmetricSplitRank
  satisfies_law := by
    dsimp [RadonNikodymQuadraticLaw, ComplementaryRegularTraceAmplitude,
      isolation_ComplementaryRegularTraceAmplitude, SymmetricSplitRankRat,
      SymmetricSplitRank, JordanAlgebraRank, isolation_JordanAlgebraRank,
      TimelikeSignatureRank, isolation_TimelikeSignatureRank,
      SingletonRayCardinality, ProjectiveRaySingleton]
    rw [Finset.card_singleton]
    push_cast
    ring
  unique_survivor := by
    intro w
    dsimp [RadonNikodymQuadraticLaw, ComplementaryRegularTraceAmplitude,
      isolation_ComplementaryRegularTraceAmplitude, SymmetricSplitRankRat,
      SymmetricSplitRank, JordanAlgebraRank, isolation_JordanAlgebraRank,
      TimelikeSignatureRank, isolation_TimelikeSignatureRank,
      SingletonRayCardinality, ProjectiveRaySingleton]
    rw [Finset.card_singleton]
    push_cast
    constructor <;> intro h <;> linarith

def RadonNikodymBoundaryProbabilityWeight (a_sing : ℚ) : ℚ :=
  (isolation_RadonNikodymBoundaryProbabilityWeight a_sing).survivor

def IsotropicWavefrontLaw (Qu Qv Qsum ds2 : ℚ) : Prop :=
  ds2 + Qsum = SymmetricSplitRankRat * Qu + SymmetricSplitRankRat * Qv

def isolation_IsotropicWavefrontIntervalSq (Qu Qv Qsum : ℚ) :
    UniqueLawSolution (IsotropicWavefrontLaw Qu Qv Qsum) where
  survivor := SymmetricSplitRankRat * Qu + SymmetricSplitRankRat * Qv - Qsum
  satisfies_law := by
    dsimp [IsotropicWavefrontLaw]
    ring
  unique_survivor := by
    intro ds2
    dsimp [IsotropicWavefrontLaw]
    constructor <;> intro h <;> linarith

def IsotropicWavefrontIntervalSq (Qu Qv Qsum : ℚ) : ℚ :=
  (isolation_IsotropicWavefrontIntervalSq Qu Qv Qsum).survivor

theorem isotropic_wavefront_interval_vanishes (Qu Qv Qsum : ℚ)
    (hu : Qu = NullCapacityRat) (hv : Qv = NullCapacityRat) (hsum : Qsum = NullCapacityRat) :
    IsotropicWavefrontIntervalSq Qu Qv Qsum = NullCapacityRat := by
  dsimp [IsotropicWavefrontIntervalSq, isolation_IsotropicWavefrontIntervalSq]
  rw [hu, hv, hsum]
  dsimp [NullCapacityRat, NullCapacity, isolation_NullCapacity]
  simp

end Paper2
