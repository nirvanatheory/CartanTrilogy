# The Cartan Trilogy: Machine-Verified Uniqueness of Type IV D5 and Spectral Ontology from the Global Null Condition

**Author:** Anthony Curtis Rivera  
**Verification Engine:** Lean 4 + Mathlib4  

## Overview
This repository contains the complete, machine-verified Lean 4 formalization accompanying the three-part manuscript series:
1. **`Paper1.lean`** — *Synthetic Incidence, Primitive Jordan Idempotents, and the Dimensional Uniqueness Theorem*
2. **`Paper2.lean`** — *Boundary Filtration of Isotropic Null Rays, Berezin–Toeplitz POVM Quantization, and Symplectic Capacity*
3. **`Paper3.lean`** — *Automorphic Spectral Geometry and the Deductive Ontology of Localized Residues*

## Key Verification Properties
* **Zero Free Parameters / Zero Hardcoded Literals:** No numeric literals (`[0-9]`, `Nat.zero`, `Nat.succ`) appear anywhere in the definitions, capability predicates, conservation laws, or proof scripts.
* **Single Origin at Null (`NullCapacity`):** Every discrete and rational invariant across all three papers is isolated deductively starting solely from `NullCapacity` (*Q0).
* **Universal Uniqueness Gateways (`IntersectionIsolation` & `UniqueLawSolution`):** No variable is defined by bare assignment. Every invariant passes a machine-checked uniqueness theorem before being bound to a variable name.
* **Comprehensive Elimination Across All Types and Dimensions (`Paper1.lean`):**
  1. **Isolation of Lorentzian Signature (`isolation_TimelikeSignatureRank`):** Eliminates empty cones (p=0) and non-pointed ultra-hyperbolic cones (p2), isolating the unique pointed signature rank p=1.
  2. **Elimination of Non-Type-IV Families (`isolation_JordanAlgebraRank`):** Across the entire Jordan–von Neumann–Wigner (JNW) and Koecher–Vinberg classification of homogeneous cones and tube domains, requiring non-collinear boundary rays (r>1) and a quadratic null boundary variety (r22r) eliminates all higher-rank matrix algebras (Hr(R,C,H) for r3) and the exceptional Albert algebra H3(O), uniquely isolating the rank-2 Jordan spin factor Vn and its Kantor–Koecher–Tits Type IV domain $\mathcal{D}_n \cong SO_0(n,2)/[SO(n)\times SO(2)]$.
  3. **The Dimensional Uniqueness Theorem (`dimensional_uniqueness_theorem`):** Proves that within the uniquely isolated Type IV family:
     * Every n<5 (`n < CriticalComplexDimension`) is incapable of supporting a Global Null configuration.
     * Every n>5 (`n > CriticalComplexDimension`) is capable of a Global Null configuration, but has a non-isolated singular stratum where all localized residues vanish identically (trivially null throughout).
     * D5 (n=5, `CriticalComplexDimension`) is the strictly unique configuration across all types and dimensions capable of supporting both a Global Null and non-zero localized residues simultaneously.

## How to Verify and Reproduce the Ledger
Install [elan / Lean 4](https://leanprover-community.github.io/get_started.html) and run:
```bash
lake exe cache get
lake build
