/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.GroupTheory.GroupExtension.Basic

/-!
# Subgroups of the affine isometries

A subgroup of the affine isometries of a normed space is an extension of its point group by its
translations.

## i. Overview

A rigid motion of space keeps all distances and straight lines. Every such motion is a rotation
or reflection about the origin, followed by a shift. The rotation or reflection is the linear part
of the motion. Two motions have the same linear part exactly when they differ by a shift, so the
motions with trivial linear part are the shifts.

A crystal in space is invariant under a group of such motions, its space group. Its shifts are the
translations of the lattice. Its linear parts, the rotations and reflections that remain once the
shifts are forgotten, form the point group. For a square lattice with an atom at each site, the
shifts are the integer steps in both directions, and the point group consists of the quarter
turns and the mirrors. Forgetting the shifts is a homomorphism whose kernel is the group of shifts,
so the space group modulo its shifts is the point group.

This file proves this for any group of rigid motions, with no crystal in sight.

## ii. Key results

- `Crystal.Euclidean.linearHom` : the linear part of an affine isometry, a homomorphism.
- `Crystal.Euclidean.translationHom` : translation by a vector, a homomorphism.
- `Crystal.Euclidean.ker_linearHom` : the affine isometries with trivial linear part are the
  translations.
- `Crystal.Euclidean.mul_translationHom_mul_inv` : conjugating a translation by an affine
  isometry translates by the linear part of the vector.
- `Crystal.Euclidean.translations` : the translations in a subgroup.
- `Crystal.Euclidean.extension` : a subgroup is an extension of its point group by its
  translations.
- `Crystal.Euclidean.quotientEquiv` : a subgroup modulo its translations is its point group.

## iii. Table of contents

- A. Linear parts and translations
- B. Subgroups

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

namespace Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Subgroup (E ≃ᵃⁱ[ℝ] E))

/-! ## A. Linear parts and translations -/

/-- The linear part of an affine isometry is the difference of the images of a point and the
origin. -/
lemma linearIsometryEquiv_apply (ψ : E ≃ᵃⁱ[ℝ] E) (v : E) :
    ψ.linearIsometryEquiv v = ψ v - ψ 0 := by
  simpa using ψ.map_vsub v 0

/-- The linear part of an affine isometry, as a homomorphism. -/
noncomputable def linearHom : (E ≃ᵃⁱ[ℝ] E) →* (E ≃ₗᵢ[ℝ] E) where
  toFun ψ := ψ.linearIsometryEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Translation by a vector, as an affine isometry. -/
noncomputable def translationHom : Multiplicative E →* (E ≃ᵃⁱ[ℝ] E) where
  toFun v := AffineIsometryEquiv.constVAdd ℝ E (Multiplicative.toAdd v)
  map_one' := AffineIsometryEquiv.constVAdd_zero
  map_mul' _ _ := by
    ext
    exact add_assoc _ _ _

/-- The linear part of the inverse is the inverse of the linear part. -/
lemma linearIsometryEquiv_inv (ψ : E ≃ᵃⁱ[ℝ] E) :
    ψ⁻¹.linearIsometryEquiv = ψ.linearIsometryEquiv.symm :=
  map_inv linearHom ψ

/-- The linear part of a translation is trivial. -/
lemma linearHom_translationHom (v : E) :
    linearHom (translationHom (Multiplicative.ofAdd v)) = 1 := by
  ext w
  show (translationHom (Multiplicative.ofAdd v)).linearIsometryEquiv w = w
  rw [linearIsometryEquiv_apply]
  show v + w - (v + 0) = w
  simp

/-- An affine isometry with trivial linear part is a translation. -/
lemma eq_translationHom_of_linearHom_eq_one (ψ : E ≃ᵃⁱ[ℝ] E) (h : linearHom ψ = 1) :
    ψ = translationHom (Multiplicative.ofAdd (ψ 0)) := by
  ext v
  have hv : ψ.linearIsometryEquiv v = v := DFunLike.congr_fun h v
  rw [linearIsometryEquiv_apply] at hv
  exact sub_eq_iff_eq_add'.1 hv

/-- The affine isometries with trivial linear part are the translations. -/
lemma ker_linearHom : (linearHom (E := E)).ker = (translationHom (E := E)).range := by
  ext ψ
  constructor
  · intro h
    exact ⟨_, (eq_translationHom_of_linearHom_eq_one ψ h).symm⟩
  · rintro ⟨v, rfl⟩
    exact linearHom_translationHom _

/-- Conjugating a translation by an affine isometry translates by the linear part of the vector. -/
lemma mul_translationHom_mul_inv (ψ : E ≃ᵃⁱ[ℝ] E) (v : E) :
    ψ * translationHom (Multiplicative.ofAdd v) * ψ⁻¹ =
      translationHom (Multiplicative.ofAdd (ψ.linearIsometryEquiv v)) := by
  ext x
  show ψ (v + ψ.symm x) = ψ.linearIsometryEquiv v + x
  simpa using ψ.map_vadd (ψ.symm x) v

/-! ## B. Subgroups -/

/-- The translations in a subgroup of the affine isometries. -/
noncomputable def translations : Subgroup S := (translationHom (E := E)).range.subgroupOf S

/-- The linear part on a subgroup, with values in its point group. -/
noncomputable def toPointGroup : S →* S.map linearHom := linearHom.subgroupMap S

/-- An element of a subgroup has trivial point operation exactly when it is a translation. -/
lemma mem_ker_toPointGroup (ψ : S) : ψ ∈ (toPointGroup S).ker ↔ ψ ∈ translations S := by
  rw [MonoidHom.mem_ker, show ψ ∈ translations S ↔ ψ.1 ∈ (translationHom (E := E)).range from
    Iff.rfl, ← ker_linearHom, MonoidHom.mem_ker]
  simp [toPointGroup, Subtype.ext_iff]

/-- A subgroup of the affine isometries is an extension of its point group by its translations. -/
noncomputable def extension : GroupExtension (translations S) S (S.map linearHom) where
  inl := (translations S).subtype
  rightHom := toPointGroup S
  inl_injective := Subtype.val_injective
  range_inl_eq_ker_rightHom := by
    ext ψ
    rw [Subgroup.range_subtype]
    exact (mem_ker_toPointGroup S ψ).symm
  rightHom_surjective := linearHom.subgroupMap_surjective S

/-- **A subgroup modulo its translations is its point group.** -/
noncomputable def quotientEquiv : S ⧸ (toPointGroup S).ker ≃* S.map linearHom :=
  QuotientGroup.quotientKerEquivOfSurjective _ (linearHom.subgroupMap_surjective S)

end Euclidean

end Physlib.CondensedMatter.Crystal
