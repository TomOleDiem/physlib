/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Boson.ConnectingMap
public import PhyslibAlpha.Mathematics.OperatorAlgebra.InverseLimit
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
/-!

# The Buchholz algebra of an infinite-dimensional one-particle space

The bounded inverse limit of the particle-sector algebras.

## i. Overview

For a complex Hilbert space `h` of infinite dimension the sector algebras `𝔎_n` of `n`
particles form an inverse system under the connecting homomorphisms `κ_{n+1} : 𝔎_{n+1} → 𝔎_n`.
The Buchholz algebra `𝔅(h)` is the C*-algebra of bounded sequences `(A_n)` with
`A_n ∈ 𝔎_n` and `κ_{n+1}(A_{n+1}) = A_n`. Its construction needs the choice of an orthonormal
sequence of the one-particle space, which exists exactly because `h` is infinite dimensional.
The connecting homomorphism is defined by the strong asymptotic limit that adds a particle
escaping to infinity.

## ii. Key results

- `Boson.exists_orthonormal_nat`: an infinite-dimensional Hilbert space has an orthonormal sequence.
- `Boson.buchholzAlgebra`: the bounded inverse limit of the sector algebras.

## iii. Table of contents

- A. Orthonormal sequences
- B. The algebra

## iv. References

* D. Buchholz, The resolvent algebra of non-relativistic Bose fields: observables, dynamics and
  states, Commun. Math. Phys. 362 (2018).
* A. Deuchert, J. Lampart and M. Lemm, Dynamics and equilibrium states of infinite systems of
  lattice bosons, arXiv:2505.13170, Proposition 2.4.
-/

@[expose] public section

universe u

open HilbertPower
open scoped ENNReal

noncomputable section

namespace Boson

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]

/-!

## A. Orthonormal sequences

-/

/-- **An infinite-dimensional Hilbert space has an orthonormal sequence.** -/
lemma exists_orthonormal_nat (hinf : ¬ Module.Finite ℂ h) : ∃ φ : ℕ → h, Orthonormal ℂ φ := by
  let b := Module.Free.chooseBasis ℂ h
  have hI : Infinite (Module.Free.ChooseBasisIndex ℂ h) := by
    by_contra hfin
    rw [not_infinite_iff_finite] at hfin
    exact hinf (Module.Finite.of_basis b)
  let e := Infinite.natEmbedding (Module.Free.ChooseBasisIndex ℂ h)
  have hli : LinearIndependent ℂ (fun n : ℕ => b (e n)) :=
    b.linearIndependent.comp _ e.injective
  exact ⟨InnerProductSpace.gramSchmidtNormed ℂ (fun n : ℕ => b (e n)),
    InnerProductSpace.gramSchmidtNormed_orthonormal hli⟩

/-!

## B. The algebra

-/

instance (n : ℕ) [Nontrivial h] : Nontrivial (sym h n) := by
  obtain ⟨z, hz⟩ := exists_ne (0 : h)
  refine ⟨⟨pow z n, pow_mem_sym z n⟩, 0, fun hc => ?_⟩
  have := congrArg Subtype.val hc
  have h1 : ‖pow z n‖ = ‖z‖ ^ n := norm_pow z n
  simp only [ZeroMemClass.coe_zero] at this
  rw [this, norm_zero] at h1
  exact (pow_ne_zero n (norm_ne_zero_iff.mpr hz)) h1.symm

instance (n : ℕ) [Nontrivial h] : Nontrivial (sectorAlgebra h n) :=
  inferInstance

/-- **The Buchholz algebra**: the bounded inverse limit of the particle-sector algebras along the
connecting homomorphisms. -/
abbrev buchholzAlgebra [Nontrivial h] {φ : ℕ → h} (hφ : Orthonormal ℂ φ) :
    StarSubalgebra ℂ (lp (fun n => sectorAlgebra h n) ∞) :=
  InverseLimit.inverseLimit (fun n => kappa hφ n)

/-- **The Buchholz algebra is a C*-algebra.** -/
example [Nontrivial h] {φ : ℕ → h} (hφ : Orthonormal ℂ φ) :
    CStarAlgebra (buchholzAlgebra hφ) := inferInstance

end Boson
