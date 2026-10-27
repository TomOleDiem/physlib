/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.AffineIsometries
public import Mathlib.Algebra.Module.BigOperators

/-!
# Symmorphic groups

A group of affine isometries is symmorphic if its point operations can all be taken about one
common origin.

## i. Overview

Let `S` be a group of affine isometries of a real normed space, for example the space group of a
crystal. Taking the linear part is a homomorphism from `S` onto its point group, with the
translations in `S` as kernel. The group `S` is symmorphic if this extension splits: there is a
homomorphism that sends every point operation to an element of `S` with that linear part.

A finite group of affine isometries fixes a point, the centre of any of its orbits. Hence a
splitting provides a common origin about which every point operation is a symmetry. Conversely, the
elements of `S` that fix a given origin map injectively to the point group, since an isometry that
fixes the origin and has trivial linear part is the identity. So `S` is symmorphic exactly when its
point operations are realised by elements of `S` fixing a common point.

## ii. Key results

- `Crystal.Euclidean.fixing` : the affine isometries that fix a point.
- `Crystal.Euclidean.exists_fixed_point` : a finite group of affine isometries fixes a point.
- `Crystal.Euclidean.IsSymmorphic` : the linear part has a section in the group.
- `Crystal.Euclidean.isSymmorphic_iff_exists_fixing` : a group with finite point group is
  symmorphic exactly when the elements fixing some point realise all its point operations.

## iii. Table of contents

- A. Isometries fixing a point
- B. A finite group fixes a point
- C. Symmorphic groups

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

namespace Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## A. Isometries fixing a point -/

/-- The affine isometries that fix a point. -/
def fixing (p : E) : Subgroup (E ≃ᵃⁱ[ℝ] E) where
  carrier := {ψ | ψ p = p}
  one_mem' := rfl
  mul_mem' {ψ χ} hψ hχ := by
    show ψ (χ p) = p
    rw [hχ, hψ]
  inv_mem' {ψ} hψ := by
    show ψ.symm p = p
    rw [ψ.symm_apply_eq, hψ]

/-- An affine isometry that fixes a point is determined by its linear part. -/
lemma eq_of_linearHom_eq_of_fixing {p : E} {ψ χ : E ≃ᵃⁱ[ℝ] E} (hψ : ψ ∈ fixing p)
    (hχ : χ ∈ fixing p) (h : linearHom ψ = linearHom χ) : ψ = χ := by
  ext x
  have h1 := ψ.map_vsub x p
  have h2 := χ.map_vsub x p
  rw [vsub_eq_sub, vsub_eq_sub, (hψ : ψ p = p)] at h1
  rw [vsub_eq_sub, vsub_eq_sub, (hχ : χ p = p)] at h2
  exact sub_left_injective (h1.symm.trans ((DFunLike.congr_fun h _).trans h2))

/-! ## B. A finite group fixes a point -/

/-- An affine isometry preserves combinations of points with weights summing to one. -/
lemma map_sum_smul {ι : Type*} (s : Finset ι) {w : ι → ℝ} (hw : ∑ i ∈ s, w i = 1) (x : ι → E)
    (ψ : E ≃ᵃⁱ[ℝ] E) : ψ (∑ i ∈ s, w i • x i) = ∑ i ∈ s, w i • ψ (x i) := by
  have h : ∀ y, ψ y = ψ.linearIsometryEquiv y + ψ 0 := fun y => by rw [linear_apply]; abel
  rw [h, map_sum]
  simp only [map_smul, h (x _), smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hw, one_smul]

/-- **A finite group of affine isometries fixes a point**, the centre of the orbit of the
origin. -/
lemma exists_fixed_point {G : Type*} [Group G] [Finite G] (s : G →* E ≃ᵃⁱ[ℝ] E) :
    ∃ p, ∀ g, s g p = p := by
  have := Fintype.ofFinite G
  refine ⟨∑ h, (Fintype.card G : ℝ)⁻¹ • s h 0, fun g => ?_⟩
  rw [map_sum_smul _ (by simp [Finset.sum_const, Fintype.card_ne_zero]) _ (s g)]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun h => by rw [Equiv.coe_mulLeft, map_mul]; rfl

/-! ## C. Symmorphic groups -/

variable (S : Subgroup (E ≃ᵃⁱ[ℝ] E))

/-- A group of affine isometries is symmorphic if its point operations are realised by elements of
the group, chosen compatibly with the product. -/
def IsSymmorphic : Prop := ∃ s : S.map linearHom →* S, ∀ g, linearHom (s g : E ≃ᵃⁱ[ℝ] E) = g

/-- Splitting the linear part gives an origin about which all point operations are symmetries. -/
lemma exists_fixing_of_isSymmorphic [Finite (S.map linearHom)] (h : IsSymmorphic S) :
    ∃ p, (S ⊓ fixing p).map linearHom = S.map linearHom := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨p, hp⟩ := exists_fixed_point (S.subtype.comp s)
  exact ⟨p, le_antisymm (Subgroup.map_mono inf_le_left) fun g hg =>
    ⟨s ⟨g, hg⟩, ⟨(s _).2, hp _⟩, hs _⟩⟩

/-- The elements fixing a point map injectively to the point group. -/
lemma injective_linearHom_fixing (p : E) :
    Function.Injective (linearHom.domRestrict (S ⊓ fixing p)) := fun ψ χ h =>
  Subtype.ext (eq_of_linearHom_eq_of_fixing ψ.2.2 χ.2.2 h)

/-- If the point operations are realised by elements fixing a common point, the group is
symmorphic. -/
lemma isSymmorphic_of_exists_fixing {p : E}
    (h : (S ⊓ fixing p).map linearHom = S.map linearHom) : IsSymmorphic S := by
  have hr := (MonoidHom.domRestrict_range _ _).trans h
  let e := (MulEquiv.subgroupCongr hr.symm).trans
    (MonoidHom.ofInjective (injective_linearHom_fixing S p)).symm
  exact ⟨(Subgroup.inclusion inf_le_left).comp e.toMonoidHom, fun g =>
    MonoidHom.apply_ofInjective_symm (injective_linearHom_fixing S p)
      (MulEquiv.subgroupCongr hr.symm g)⟩

/-- **A group of affine isometries with finite point group is symmorphic exactly when the elements
fixing some point realise all its point operations.** -/
lemma isSymmorphic_iff_exists_fixing [Finite (S.map linearHom)] :
    IsSymmorphic S ↔ ∃ p, (S ⊓ fixing p).map linearHom = S.map linearHom :=
  ⟨exists_fixing_of_isSymmorphic S, fun ⟨_, h⟩ => isSymmorphic_of_exists_fixing S h⟩

end Euclidean

end Physlib.CondensedMatter.Crystal
