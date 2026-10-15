# The Cartan Trilogy: Machine-Verified Deductive Invariant Ledger

[![Lean 4 Formal Verification](https://github.com/nirvanatheory/CartanTrilogy/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/nirvanatheory/CartanTrilogy/actions/workflows/lean_action_ci.yml)

**Verification Engine:** Lean 4 (`leanprover/lean4:v4.14.0`) + `Mathlib4` (`4bbdccd9`)  
**Strict Deductive Constraints:** Zero numeric literals (`[0-9]`, `Nat.zero`, `Nat.succ`), zero free parameters, zero custom `axiom` declarations, and zero `sorry` placeholders.

---

## 1. Overview & Repository Architecture

This repository contains the end-to-end formal verification of the **Cartan Trilogy**, establishing an unbroken deductive chain from the vanishing generator capacity of the empty ray list (`NullCapacity = 0`) to the complete 67-invariant geometric, spectral, holonomy, and instanton ledger.

The codebase is structured as a sequential three-part dependency chain (`Paper1` $\to$ `Paper2` $\to$ `Paper3`):

* **`Paper1.lean` — *Synthetic Incidence, Primitive Jordan Idempotents, and the Dimensional Uniqueness Theorem***
  * Defines the two foundational uniqueness gateways used across the trilogy: `IntersectionIsolation` (opposing capability bounds over $\mathbb{N}$) and `UniqueLawSolution` (algebraic conservation laws over $\mathbb{N}$ and $\mathbb{Q}$).
  * Formalizes the abstract Jordan spin-factor algebra (`SpinFactor W`, `jordanMul`) over an arbitrary $\mathbb{Q}$-module $W$ equipped with a symmetric bilinear form $B$, proving commutativity (`jordan_product_commutative`) and the full cubic Jordan identity $a \circ (a^2 \circ b) = a^2 \circ (a \circ b)$ (`jordan_cubic_identity`).
  * Deductively isolates the pointed Lorentzian signature ($p = 1$), the spin-factor / symmetric split rank ($r = 2$), primitive idempotent pullback nullity (`primitive_idempotent_norm_vanishes` and `ray_metric_degeneracy`), the hyperkähler slice dimension ($k_{\text{HK}} = 2$), chiral short-root multiplicity ($r_2 = 3$), the **Dimensional Uniqueness Theorem** ($n = 5$), the Shilov boundary sphere dimension ($d_S = 4$), and the $B_2$ restricted Weyl Casimir norm $\Vert{}\rho\Vert{}^2 = 17/2$.

* **`Paper2.lean` — *Boundary Filtration of Isotropic Null Rays, Berezin–Toeplitz POVM Quantization, and Symplectic Capacity***
  * Imports the locked invariants of `Paper1` to isolate the Cartan domain genus ($g = 5$) and the Poisson–Szegő ($5$) and Cauchy–Szegő ($5/2$) reproducing kernel exponents.
  * Formally proves the failure of sharp projection-valued measure (PVM) idempotence on the Shilov boundary over the open interval $p \in (0, 1)$ (`sharp_pvm_idempotence_is_invalid`).
  * Isolates the quadratic Radon–Nikodym boundary probability weight $(1 - a_{\text{sing}})^2$ and proves the identical vanishing of the isotropic wavefront interval (`isotropic_wavefront_interval_vanishes`).

* **`Paper3.lean` — *Automorphic Spectral Geometry and the Deductive Ontology of Localized Residues***
  * Imports both `Paper1` and `Paper2` to isolate the involutive Lorentzian subquadric codimension ($1$), the spatial Cauchy sphere dimension ($3$), and the emergent spacetime dimension ($d_M = 4$).
  * Proves the parabolic $\vert{}1\vert{}$-grading termination ($1$) and exterior algebra binomial termination ($\binom{3}{k} > 0 \implies k \le 3$) superselection rules.
  * Evaluates the closed automorphic, Szegő polynomial, stabilizer Casimir, holonomy tangent, twisted link, and instanton transgression invariants, proving the master relational laws (`master_trilogy_relational_laws_verified`) and outputting the complete invariant ledger via `#eval`.

---

## 2. Scope of Formalization: Continuous Literature vs. Formal Algebraic Gateways

To maintain complete methodological transparency, it is important to distinguish between **continuous differential-geometric theorems from the established literature** and the **algebraic capability and conservation gateways** verified by the Lean 4 kernel.

Because `Mathlib4` does not yet contain formalizations of elliptic pseudodifferential operators, Sobolev-space hyperkähler quotients, or multivariable Berezin–Toeplitz microlocal analysis, this repository does **not** introduce unverified placeholder axioms (e.g., `axiom Manifold : Type`). Instead, classical analytical theorems are interfaced at their exact algebraic and Diophantine landing points:

1. **Jordan–von Neumann–Wigner (1934) & Cartan Symmetric Space Classifications *(Paper I, Steps 3–4)*:**
   The spin-factor Jordan product and cubic identity are proven from first principles over any $\mathbb{Q}$-module $W$. Higher-rank tube domains are filtered via Veblen–Young projective incidence (`veblen_young_pasch_incidence`) and the quadratic null-cone boundary capability predicate (`CapableOfQuadraticNullBoundary`).
2. **Kronheimer’s Hyperkähler ALE Classification (1989) *(Paper I, Step 5)*:**
   Rather than formalizing self-dual Einstein PDEs on 4-manifolds, the symplectic holonomy compatibility condition $SU(k) \cap Sp(k/2)$ is encoded via its exact algebraic dimension constraint (`CapableOfCrepantSUHolonomy` and `CapableOfSymplecticHyperkahlerHolonomy`), from which Lean deductively isolates $k_{\text{HK}} = 2$ across all $k \in \mathbb{N}$.
3. **Hua (1963) & Berezin–Toeplitz Microlocal Star-Product Asymptotics *(Paper II, Steps 9–11; Paper III, Step 14)*:**
   The reproducing kernel exponents on $D^{\text{IV}}_5$, second-order anti-holomorphic Fourier leakage, and sub-leading Szegő polynomial shifts are encoded via their algebraic degree and trace conservation laws (`PoissonSzegoDegreeLaw`, `CauchySzegoHardyLaw`, `AntiHolomorphicLeakageLaw`, `RadonNikodymQuadraticLaw`). Lean then proves that any system governed by these conservation laws violates sharp PVM idempotence on $(0,1)$ and uniquely determines the polynomial weights.
4. **Atiyah–Patodi–Singer (1975) Spectral Asymmetry *(Paper III, Step 14)*:**
   The closed Dedekind-sum evaluation of the tangential Dirac $\eta$-invariant on the cyclic lens link $L(3,1) = S^3/\mathbb{Z}_3$ is encoded via its exact rational root-multiplicity ratio (`LinkAPSSpectralAsymmetry`), from which the compiler deterministically derives and verifies all downstream modular, holonomy, and instanton trace identities.

**Division of Labor:** The accompanying manuscripts establish why the continuous differential and complex geometry mandates each capability predicate and conservation law; the Lean 4 compiler guarantees that once those predicates and laws are stated, **zero free parameters or numerical degrees of freedom remain**.

---

## 3. Kernel Axiom Footprint

The formalization introduces **zero custom axioms**, **zero `sorryAx` tokens**, and **zero `Lean.trustCompiler` (`native_decide`) overrides**.

At the level of the Lean 4 C++ kernel, all proofs rely exclusively on the rules of the **Calculus of Inductive Constructions (CIC)** and Lean's three standard foundational axioms of classical mathematics (equiconsistent with ZFC):

* **`propext`** *(Propositional Extensionality)*: $(P \leftrightarrow Q) \implies P = Q$.
* **`Quot.sound`** *(Quotient Soundness)*: $a \sim b \implies [a] = [b]$.
* **`Classical.choice`** *(Classical Excluded Middle)*: Used by `Mathlib4` linear arithmetic tactics (`linarith`, `nlinarith`, `ring`, `omega`) over $\mathbb{Q}$.

All ground-state capability checks and dimensional bridge identities proven via `rfl` or `decide` are verified purely by kernel definitional reduction (`does not depend on any axioms`).

Compiler output from `#print axioms` during `lake build`:

```text
info: ././././Paper3.lean:592:0: 'Paper1.jordan_cubic_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ././././Paper3.lean:593:0: 'Paper1.dimensional_uniqueness_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ././././Paper3.lean:594:0: 'Paper2.sharp_pvm_idempotence_is_invalid' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ././././Paper3.lean:595:0: 'Paper2.isotropic_wavefront_interval_vanishes' depends on axioms: [propext, Classical.choice, Quot.sound]
info: ././././Paper3.lean:596:0: 'Paper3.master_trilogy_relational_laws_verified' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully.
