/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.ModelHamiltonians
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.HamiltonianDynamics
/-!

# Domain and dynamics of the Bose-Hubbard Hamiltonian with pairing

The oscillator lattice (quadratic data) and the Bose-Hubbard model share this API.

## i. Overview

Pair creation from the vacuum makes the formal image of a basis state an infinite sum. It lies in
`ℓ²` only if the pairing amplitudes are square summable in the appropriate sense. This is a
condition on the model and appears as an explicit hypothesis `hdom`. Under it the domain of the
Hamiltonian contains all finite vectors and is dense. Under essential self-adjointness the
dynamics is the unitary group `exp(i t H)`. Neither fact is a field of the model data.

## ii. Key results

- `InfiniteBosons.BoseHubbardData.hamOp_dense`: density under the domain hypothesis.
- `InfiniteBosons.BoseHubbardData.dynamics_of_essentiallySelfAdjoint`: the unitary group.
- `InfiniteBosons.BoseHubbardData.isDiagonal_decoupled`, `InfiniteBosons.BoseHubbardData.dynamics_decoupled`:
  the decoupled model (no hopping and no pairing) is diagonal, essentially self-adjoint, and
  generates a unitary group on an arbitrary lattice.

## iii. Table of contents

- A. Density
- B. Dynamics

## iv. References

* O. Bratteli, D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, Section 6.2.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

namespace BoseHubbardData

variable (D : BoseHubbardData L)

/-- **Density of the domain** under the condition that the formal image of every occupation vector
is square summable. -/
theorem hamOp_dense (hdom : ∀ b : Occ L, Memℓp (D.formalHam (single b 1)) 2) :
    D.hamOp.HasDenseDomain :=
  hamPMap_dense D.interaction.Φ D.rowFinite hdom

/-- **Dynamics of the Bose-Hubbard model with pairing** as a theorem: an essentially self-adjoint
Hamiltonian generates a strongly continuous unitary group. -/
theorem dynamics_of_essentiallySelfAdjoint (hess : D.hamOp.IsEssentiallySelfAdjoint) :
    ∃ U : ProbabilisticTheory.QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup
        (HilbertSp (Occ L)),
      (∀ t s, U (t + s) = U t * U s) ∧ U 0 = 1 ∧
      ∀ f : hamDomainAlg D.interaction.Φ D.rowFinite,
        HasDerivAt (fun t : ℝ => U t (embed f.1))
          (Complex.I • (hamVec D.interaction.Φ D.rowFinite f : HilbertSp (Occ L))) 0 :=
  hamPMap_dynamics D.interaction.Φ D.rowFinite hess


/-- The on-site energy of an occupation vector at the site `x`. -/
def siteEnergy (x : L) (b : Occ L) : ℝ :=
  D.U x / 2 * ((b x : ℝ) * ((b x : ℝ) - 1)) - D.μ x * (b x : ℝ)

lemma siteTerm_basis (x : L) (b : Occ L) :
    (D.siteTerm x).1.1 (single b 1) = ((D.siteEnergy x b : ℝ) : ℂ) • single b 1 := by
  have hN : (numberOp x).1.1 (single b 1) = ((b x : ℕ) : ℂ) • single b 1 := numberOp_basis x b
  have hNN : (numberOp x * numberOp x).1.1 (single b 1) =
      (((b x : ℕ) : ℂ) * ((b x : ℕ) : ℂ)) • single b 1 := by
    show (numberOp x).1.1 ((numberOp x).1.1 (single b 1)) = _
    rw [hN, map_smul, hN, smul_smul]
  have e : (D.siteTerm x).1.1 (single b 1) = ((D.U x / 2 : ℝ) : ℂ) •
      ((numberOp x * numberOp x).1.1 (single b 1) - (numberOp x).1.1 (single b 1)) -
      ((D.μ x : ℝ) : ℂ) • (numberOp x).1.1 (single b 1) := rfl
  rw [e, hN, hNN, ← sub_smul, smul_smul, smul_smul, ← sub_smul]
  congr 1
  simp only [siteEnergy]
  push_cast
  ring

lemma siteEnergy_zero {x : L} {b : Occ L} (hx : x ∉ b.support) : D.siteEnergy x b = 0 := by
  have : b x = 0 := by simpa [Finsupp.mem_support_iff] using hx
  simp [siteEnergy, this]


lemma bondTerm_eq_zero (hJ : ∀ x y, D.J x y = 0) (hΔ : ∀ x y, D.Δ x y = 0) (x y : L) :
    D.bondTerm x y = 0 := by
  unfold BoseHubbardData.bondTerm
  split_ifs
  · simp [hJ, hΔ]
  · rfl

/-- **The decoupled Bose-Hubbard Hamiltonian is diagonal** on an arbitrary lattice. -/
theorem isDiagonal_decoupled (hJ : ∀ x y, D.J x y = 0) (hΔ : ∀ x y, D.Δ x y = 0) :
    IsDiagonal D.interaction.Φ D.rowFinite (fun b => ∑ x ∈ b.support, D.siteEnergy x b) := by
  intro b α
  show ∑ᶠ i, (D.interaction.Φ i).1.1 (single b 1) α = _
  have hterm : ∀ i : L ⊕ (L × L), (D.interaction.Φ i).1.1 (single b 1) α =
      Sum.elim (fun x => ((D.siteEnergy x b : ℝ) : ℂ) * (single b (1 : ℂ) : Occ L →₀ ℂ) α)
        (fun _ => 0) i := by
    rintro (x | p)
    · show (D.siteTerm x).1.1 (single b 1) α = _
      rw [D.siteTerm_basis]
      show (((D.siteEnergy x b : ℝ) : ℂ) • (single b (1 : ℂ) : Occ L →₀ ℂ)) α = _
      rw [Finsupp.smul_apply, smul_eq_mul]
      rfl
    · show (D.bondTerm p.1 p.2).1.1 (single b 1) α = _
      rw [D.bondTerm_eq_zero hJ hΔ]
      rfl
  rw [finsum_congr hterm]
  rw [finsum_eq_sum_of_support_subset (s := b.support.map Function.Embedding.inl)]
  · rw [Finset.sum_map]
    simp only [Function.Embedding.inl_apply, Sum.elim_inl]
    rw [← Finset.sum_mul]
    by_cases hα : α = b
    · subst hα; simp
    · simp [hα, Finsupp.single_apply, Ne.symm hα]
  · intro i hi
    rcases i with x | p
    · simp only [Function.mem_support, Sum.elim_inl] at hi
      have : x ∈ b.support := by
        by_contra hx; exact hi (by simp [D.siteEnergy_zero hx])
      simpa using this
    · simp at hi

/-- **The decoupled Bose-Hubbard model is usable**: its Hamiltonian is essentially self-adjoint and
generates a unitary group on an arbitrary lattice. -/
theorem dynamics_decoupled (hJ : ∀ x y, D.J x y = 0) (hΔ : ∀ x y, D.Δ x y = 0) :
    ∃ U : ProbabilisticTheory.QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup
        (HilbertSp (Occ L)),
      (∀ t s, U (t + s) = U t * U s) ∧ U 0 = 1 ∧
      ∀ f : hamDomainAlg D.interaction.Φ D.rowFinite,
        HasDerivAt (fun t : ℝ => U t (embed f.1))
          (Complex.I • (hamVec D.interaction.Φ D.rowFinite f : HilbertSp (Occ L))) 0 :=
  D.dynamics_of_essentiallySelfAdjoint
    (hamPMap_ess_diag _ _ D.interaction.star_eq _ (D.isDiagonal_decoupled hJ hΔ))


end BoseHubbardData

end InfiniteBosons
