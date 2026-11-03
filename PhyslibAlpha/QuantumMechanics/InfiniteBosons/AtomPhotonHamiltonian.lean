/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.ModelHamiltonians
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.AtomPhotonLattice
/-!

# The Jaynes-Cummings-Hubbard Hamiltonian on an infinite lattice

The Hamiltonian of the atom-photon lattice exists as a linear map from the finite vectors to the
formal vectors and acts on `ℓ²(Occ L × Finset L)` as a symmetric operator.

## i. Overview

The terms are the cavity terms `ω a†a + ε σ⁺σ⁻ + g a†σ⁻ + ḡ σ⁺a` and the photon hopping
`-J (a_x† a_y + a_y† a_x)`. A nonzero matrix element of a term involves only cavities that are
occupied by a photon or an excited atom in the source or the target state. Hence for a finite vector
and a fixed output state only terms in a finite set of cavities contribute, and the family is
row finite. The Hamiltonian is a linear map from the finite vectors to the formal vectors and a
symmetric operator on `ℓ²`. There is no particle-number sector and no finite volume.

## ii. Key results

- `InfiniteBosons.sbModes`: the occupied cavities of a basis state.
- `InfiniteBosons.AtomPhotonData.rowFinite`: row finiteness.
- `InfiniteBosons.AtomPhotonData.formalHam`: the formal Hamiltonian.
- `InfiniteBosons.AtomPhotonData.hamOp`: the operator on `ℓ²`.
- `InfiniteBosons.AtomPhotonData.hamOp_isSymmetric`: symmetry.

## iii. Table of contents

- A. Matrix elements of the building blocks
- B. Row finiteness
- C. The Hamiltonian

## iv. References

* B. W. Shore, P. L. Knight, The Jaynes-Cummings model, J. Mod. Opt. 40 (1993) 1195.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

lemma single_apply_ne'' {γ α : SBBasis L} {c : ℂ} (h : (single γ c : SBBasis L →₀ ℂ) α ≠ 0) :
    α = γ ∧ c ≠ 0 := by
  by_cases hα : γ = α
  · subst hα; simpa using h
  · simp [Finsupp.single_apply, hα] at h

/-- modes occupied by an atom-photon basis state. -/
def sbModes (b : SBBasis L) : Finset L := b.1.support ∪ b.2

lemma photonNum_ne {x : L} {b a : SBBasis L}
    (h : (creS x (annS x (single b (1 : ℂ)))) a ≠ 0) : x ∈ sbModes b := by
  rw [annS_single, creS_single] at h
  obtain ⟨rfl, hc⟩ := single_apply_ne'' h
  have : b.1 x ≠ 0 := by
    intro h0; apply hc; simp [h0]
  exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr this)

lemma atomNum_ne {x : L} {b a : SBBasis L}
    (h : (raiseS x (lowS x (single b (1 : ℂ)))) a ≠ 0) : x ∈ sbModes b := by
  rw [lowS_single] at h
  by_cases hx : x ∈ b.2
  · exact Finset.mem_union_right _ hx
  · simp [hx] at h


lemma creLow_ne {x : L} {b a : SBBasis L}
    (h : (creS x (lowS x (single b (1 : ℂ)))) a ≠ 0) : x ∈ sbModes b := by
  rw [lowS_single] at h
  by_cases hx : x ∈ b.2
  · exact Finset.mem_union_right _ hx
  · simp [hx] at h

lemma raiseAnn_ne {x : L} {b a : SBBasis L}
    (h : (raiseS x (annS x (single b (1 : ℂ)))) a ≠ 0) : x ∈ sbModes b := by
  rw [annS_single] at h
  by_cases hx : x ∈ b.2
  · exact Finset.mem_union_right _ hx
  · rw [raiseS_single] at h
    by_cases hb : b.1 x = 0
    · simp [hb] at h
    · exact Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr hb)

lemma creAnnS_ne {x y : L} {b a : SBBasis L}
    (h : (creS x (annS y (single b (1 : ℂ)))) a ≠ 0) : y ∈ b.1.support ∧ x ∈ a.1.support := by
  rw [annS_single, creS_single] at h
  obtain ⟨rfl, hc⟩ := single_apply_ne'' h
  constructor
  · rw [Finsupp.mem_support_iff]; intro hy; apply hc; simp [hy]
  · rw [Finsupp.mem_support_iff]; intro hx; simp at hx

namespace AtomPhotonData

variable (D : AtomPhotonData L)

lemma siteTerm_ne {x : L} {b a : SBBasis L}
    (h : (D.siteTerm x).1.1 (single b 1) a ≠ 0) : x ∈ sbModes b := by
  have e : (D.siteTerm x).1.1 (single b 1) a =
      ((D.ω x : ℝ) : ℂ) * (creS x (annS x (single b (1 : ℂ)))) a +
      ((D.ε x : ℝ) : ℂ) * (raiseS x (lowS x (single b (1 : ℂ)))) a +
      (D.g x * (creS x (lowS x (single b (1 : ℂ)))) a +
        starRingEnd ℂ (D.g x) * (raiseS x (annS x (single b (1 : ℂ)))) a) := by
    unfold AtomPhotonData.siteTerm jaynesCummings
    show (((D.ω x : ℝ) : ℂ) • creS x (annS x (single b (1 : ℂ))) +
      ((D.ε x : ℝ) : ℂ) • raiseS x (lowS x (single b (1 : ℂ))) +
      (D.g x • creS x (lowS x (single b (1 : ℂ))) +
        starRingEnd ℂ (D.g x) • raiseS x (annS x (single b (1 : ℂ))))) a = _
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [e] at h
  by_cases h1 : (creS x (annS x (single b (1 : ℂ)))) a = 0
  · by_cases h2 : (raiseS x (lowS x (single b (1 : ℂ)))) a = 0
    · by_cases h3 : (creS x (lowS x (single b (1 : ℂ)))) a = 0
      · by_cases h4 : (raiseS x (annS x (single b (1 : ℂ)))) a = 0
        · exfalso; apply h; simp [h1, h2, h3, h4]
        · exact raiseAnn_ne h4
      · exact creLow_ne h3
    · exact atomNum_ne h2
  · exact photonNum_ne h1

lemma bondTerm_ne {x y : L} {b a : SBBasis L}
    (h : (D.bondTerm x y).1.1 (single b 1) a ≠ 0) :
    x ∈ a.1.support ∪ b.1.support ∧ y ∈ a.1.support ∪ b.1.support := by
  by_cases hadj : D.graph.Adj x y
  · have e : (D.bondTerm x y).1.1 (single b 1) a =
        ((-D.J x y : ℝ) : ℂ) * ((creS x (annS y (single b (1 : ℂ)))) a +
          (creS y (annS x (single b (1 : ℂ)))) a) := by
      unfold AtomPhotonData.bondTerm
      rw [if_pos hadj]
      show (((-D.J x y : ℝ) : ℂ) • (creS x (annS y (single b (1 : ℂ))) +
        creS y (annS x (single b (1 : ℂ))))) a = _
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [e] at h
    by_cases h1 : (creS x (annS y (single b (1 : ℂ)))) a = 0
    · by_cases h2 : (creS y (annS x (single b (1 : ℂ)))) a = 0
      · exfalso; apply h; simp [h1, h2]
      · have := creAnnS_ne h2
        exact ⟨Finset.mem_union_right _ this.1, Finset.mem_union_left _ this.2⟩
    · have := creAnnS_ne h1
      exact ⟨Finset.mem_union_left _ this.2, Finset.mem_union_right _ this.1⟩
  · exfalso; apply h
    unfold AtomPhotonData.bondTerm
    rw [if_neg hadj]
    rfl


/-- **The Jaynes-Cummings-Hubbard Hamiltonian is row finite** on an arbitrary lattice. -/
theorem rowFinite : RowFinite D.interaction.Φ := by
  refine rowFinite_of_local D.interaction.Φ D.interaction.supp (fun b : SBBasis L => sbModes b) ?_ ?_
  · rintro (x | p) b a h
    · intro z hz
      have : z = x := by simpa [AtomPhotonData.interaction] using hz
      subst this
      exact Finset.mem_union.mpr (Or.inr (D.siteTerm_ne h))
    · have := D.bondTerm_ne (x := p.1) (y := p.2) h
      intro z hz
      have hz' : z = p.1 ∨ z = p.2 := by simpa [AtomPhotonData.interaction] using hz
      have key : ∀ w, w ∈ a.1.support ∪ b.1.support → w ∈ sbModes a ∪ sbModes b := fun w hw => by
        rcases Finset.mem_union.mp hw with h1 | h1
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ h1)
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ h1)
      rcases hz' with rfl | rfl
      · exact key _ this.1
      · exact key _ this.2
  · intro M
    have : {i : L ⊕ (L × L) | D.interaction.supp i ⊆ M} ⊆
        (Sum.inl '' (M : Set L)) ∪ (Sum.inr '' ((M : Set L) ×ˢ (M : Set L))) := by
      rintro (x | p) hi
      · exact Or.inl ⟨x, by simpa [AtomPhotonData.interaction] using hi (by simp [AtomPhotonData.interaction]), rfl⟩
      · exact Or.inr ⟨p, ⟨by simpa [AtomPhotonData.interaction] using hi (by simp [AtomPhotonData.interaction]),
          by simpa [AtomPhotonData.interaction] using hi (by simp [AtomPhotonData.interaction])⟩, rfl⟩
    exact ((M.finite_toSet.image _).union ((M.finite_toSet.prod M.finite_toSet).image _)).subset this

/-- The formal Hamiltonian of the atom-photon lattice. -/
def formalHam : (SBBasis L →₀ ℂ) →ₗ[ℂ] Formal (SBBasis L) := formalH D.interaction.Φ D.rowFinite

/-- **The Hamiltonian as an operator on `ℓ²(Occ L × Finset L)`.** -/
def hamOp : HilbertSp (SBBasis L) →ₗ.[ℂ] HilbertSp (SBBasis L) :=
  hamPMap D.interaction.Φ D.rowFinite

theorem hamOp_isSymmetric : D.hamOp.IsSymmetric :=
  hamPMap_isSymmetric D.interaction.Φ D.rowFinite D.interaction.star_eq

end AtomPhotonData

end InfiniteBosons
