/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.HoppingSelfAdjoint
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.JaynesCummingsSelfAdjoint
public import Physlib.QuantumMechanics.Operators.SpectralTheory.Symmetric
/-!

# Essential self-adjointness of polynomial observables in the sense of Physlib

The density criterion of the resolvent bridge implies essential self-adjointness in the sense of
`Physlib.QuantumMechanics.Operators.SpectralTheory`.

## i. Overview

`Physlib` has the notions of a symmetric operator, the defect numbers and essential self-adjointness
for partially defined operators on a Hilbert space, and the criterion that a symmetric operator with
dense domain and vanishing defect numbers at `±i` is essentially self-adjoint. The polynomial
observable `p` of the algebraic Fock space is a densely defined operator `polyOp p`. It is
symmetric when `p* = p`. The range of `polyOp p ∓ i` contains the range of the shifted map of the
resolvent bridge. Density of that range gives vanishing defect numbers. Hence the density
criterion of the bridge gives `IsEssentiallySelfAdjoint`. The number operator, hopping,
the Jaynes-Cummings coupling and the reference operators satisfy the criterion. Physlib has the
spectral measure as a structure. The spectral theorem and Stone's theorem are marked as open there.

## ii. Key results

- `InfiniteBosons.defectNumber_eq_zero_of_dense`: dense range implies vanishing defect number.
- `InfiniteBosons.polyOp_isEssentiallySelfAdjoint`: the general criterion.
- `InfiniteBosons.numberOp_isEssentiallySelfAdjoint`, `InfiniteBosons.hop_isEssentiallySelfAdjoint`,
  `InfiniteBosons.jaynesCummings_isEssentiallySelfAdjoint`,
  `InfiniteBosons.refOp_isEssentiallySelfAdjoint`: the examples.

## iii. Table of contents

- A. The criterion
- B. Examples

## iv. References

* K. Schmüdgen, Unbounded Self-adjoint Operators on Hilbert Space, Springer (2012), Chapter 3.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {B : Type*} [DecidableEq B]

lemma shiftMap_mem_range_sub (p : Adjointable B) (c : ℝ) (f : B →₀ ℂ) :
    shiftMap p.1.1 c f ∈
      (polyOp p - ((-(Complex.I * c) : ℂ)) • (1 : HilbertSp B →ₗ.[ℂ] HilbertSp B)).toFun.range := by
  have hmem : embed f ∈ (polyOp p - ((-(Complex.I * c) : ℂ)) •
      (1 : HilbertSp B →ₗ.[ℂ] HilbertSp B)).domain := by
    simp only [LinearPMap.sub_domain, LinearPMap.smul_domain, LinearPMap.one_domain]
    exact ⟨LinearMap.mem_range_self embed f, Submodule.mem_top⟩
  refine ⟨⟨embed f, hmem⟩, ?_⟩
  show (polyOp p - ((-(Complex.I * c) : ℂ)) • (1 : HilbertSp B →ₗ.[ℂ] HilbertSp B)) ⟨embed f, hmem⟩ = _
  rw [LinearPMap.sub_apply, LinearPMap.smul_apply]
  have h1 := polyOp_embed p f
  have h2 : (polyOp p) ⟨embed f, _⟩ = embed (p.1.1 f) := h1
  simp only [h2]
  simp [shiftMap, sub_eq_add_neg]
lemma defectNumber_eq_zero_of_dense (p : Adjointable B) (c : ℝ) {z : ℂ} (hz : z = -(Complex.I * c))
    (hd : Dense (LinearMap.range (shiftMap p.1.1 c) : Set (HilbertSp B))) :
    (polyOp p).defectNumber z = 0 := by
  subst hz
  have hle : LinearMap.range (shiftMap p.1.1 c) ≤
      (polyOp p - ((-(Complex.I * c) : ℂ)) • (1 : HilbertSp B →ₗ.[ℂ] HilbertSp B)).toFun.range := by
    rintro _ ⟨f, rfl⟩
    exact shiftMap_mem_range_sub p c f
  have hbot : (polyOp p - ((-(Complex.I * c) : ℂ)) •
      (1 : HilbertSp B →ₗ.[ℂ] HilbertSp B)).toFun.rangeᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : x ∈ (LinearMap.range (shiftMap p.1.1 c))ᗮ := Submodule.orthogonal_le hle hx
    have : (LinearMap.range (shiftMap p.1.1 c))ᗮ = ⊥ := by
      rw [← Submodule.orthogonal_closure,
        Submodule.dense_iff_topologicalClosure_eq_top.mp hd, Submodule.top_orthogonal_eq_bot]
    rwa [this] at hx'
  show Module.rank ℂ ((polyOp p - ((-(Complex.I * c) : ℂ)) •
      (1 : HilbertSp B →ₗ.[ℂ] HilbertSp B)).toFun.rangeᗮ) = 0
  rw [hbot]
  exact rank_bot ℂ _

/-- **Essential self-adjointness of a polynomial observable** in the sense of Physlib: if `p` is
self-adjoint and the ranges of `p + i` and `p - i` are dense then the closure of `polyOp p` is
self-adjoint. -/
theorem polyOp_isEssentiallySelfAdjoint (p : Adjointable B) (hp : star p = p)
    (h1 : Dense (LinearMap.range (shiftMap p.1.1 1) : Set (HilbertSp B)))
    (h2 : Dense (LinearMap.range (shiftMap p.1.1 (-1)) : Set (HilbertSp B))) :
    (polyOp p).IsEssentiallySelfAdjoint := by
  have hsym : (polyOp p).IsSymmetric := by
    have := polyOp_formalAdjoint p
    rwa [hp] at this
  refine LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_defectNumber_eq_zero hsym
    (dense_domain_polyOp p) ?_ ?_
  · exact defectNumber_eq_zero_of_dense p (-1) (by simp) h2
  · exact defectNumber_eq_zero_of_dense p 1 (by simp) h1


section Examples

variable {L : Type*} [DecidableEq L]

/-- The number operator `N_x` is essentially self-adjoint. -/
theorem numberOp_isEssentiallySelfAdjoint (x : L) : (polyOp (numberOp x)).IsEssentiallySelfAdjoint :=
  polyOp_isEssentiallySelfAdjoint _ (by simp [numberOp, star_mul, star_annOp, star_creOp])
    (dense_range_shiftMap_of_diag _ (fun α => (α x : ℝ)) (fun α => by
      rw [numberOp_basis]; simp) one_ne_zero)
    (dense_range_shiftMap_of_diag _ (fun α => (α x : ℝ)) (fun α => by
      rw [numberOp_basis]; simp) (by norm_num))

/-- **The hopping operator is essentially self-adjoint** on the algebraic Fock space of an
arbitrary lattice. -/
theorem hop_isEssentiallySelfAdjoint {x y : L} (hxy : x ≠ y) :
    (polyOp (hop x y)).IsEssentiallySelfAdjoint := by
  have hsym : ∀ f g, pair ((hop x y).1.1 f) g = pair f ((hop x y).1.1 g) := fun f g => by
    have := star_fst_pair (hop x y) f g
    rwa [star_hop] at this
  have hinv := fun α : Occ L => (⟨hopBlock x y α, mem_hopBlock_self α, fun β hβ =>
        hop_support_subset hxy α (Finset.mem_coe.mp hβ)⟩ :
      ∃ F : Finset (Occ L), α ∈ F ∧ ∀ β ∈ F, (((hop x y).1.1 (single β 1)).support : Set (Occ L)) ⊆ F)
  exact polyOp_isEssentiallySelfAdjoint _ (star_hop x y)
    (dense_range_shiftMap_of_finite_invariant _ hsym hinv one_ne_zero)
    (dense_range_shiftMap_of_finite_invariant _ hsym hinv (by norm_num))

/-- **The Jaynes-Cummings coupling is essentially self-adjoint.** -/
theorem jaynesCummings_isEssentiallySelfAdjoint (x : L) (g : ℂ) :
    (polyOp (jaynesCummings x g)).IsEssentiallySelfAdjoint := by
  have hsym : ∀ f h, pair ((jaynesCummings x g).1.1 f) h =
      pair f ((jaynesCummings x g).1.1 h) := fun f h => by
    have := star_fst_pair (jaynesCummings x g) f h
    rwa [star_jaynesCummings] at this
  have hinv := fun b : SBBasis L => (⟨jcBlock x b, mem_jcBlock_self x b, fun β hβ =>
      jc_support_subset x g b (Finset.mem_coe.mp hβ)⟩ :
    ∃ F : Finset (SBBasis L), b ∈ F ∧
      ∀ β ∈ F, (((jaynesCummings x g).1.1 (single β 1)).support : Set (SBBasis L)) ⊆ F)
  exact polyOp_isEssentiallySelfAdjoint _ (star_jaynesCummings x g)
    (dense_range_shiftMap_of_finite_invariant _ hsym hinv one_ne_zero)
    (dense_range_shiftMap_of_finite_invariant _ hsym hinv (by norm_num))

/-- **The reference operator `K_X` is essentially self-adjoint.** -/
theorem refOp_isEssentiallySelfAdjoint (X : Finset L) :
    (polyOp (refOp X)).IsEssentiallySelfAdjoint :=
  polyOp_isEssentiallySelfAdjoint _ (star_refOp X)
    (dense_range_shiftMap_of_diag _ (fun α => 1 + ∑ x ∈ X, (α x : ℝ)) (refOp_basis X) one_ne_zero)
    (dense_range_shiftMap_of_diag _ (fun α => 1 + ∑ x ∈ X, (α x : ℝ)) (refOp_basis X)
      (by norm_num))

end Examples

end InfiniteBosons
