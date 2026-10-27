/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Tactic.Abel

/-!
# Linear parts and translations of affine isometries

The group of affine isometries of a normed space, its translations and its linear parts.

## i. Overview

Every affine isometry of a real normed space `E` is a linear isometry followed by a translation.
Taking the linear part is a homomorphism from the affine isometries to the linear isometries, and
translating by a vector is a homomorphism from `E` to the affine isometries. The kernel of the
first is the image of the second: the affine isometries with trivial linear part are exactly the
translations.

These facts are about the Euclidean group alone, with no crystal in sight. They are the
vocabulary for the groups of a crystal in space: its translations are the kernel and its point
group is the image of the linear part.

## ii. Key results

- `Crystal.Euclidean.linearHom` : the linear part of an affine isometry, a homomorphism.
- `Crystal.Euclidean.translationHom` : translation by a vector, a homomorphism.
- `Crystal.Euclidean.ker_linearHom` : the affine isometries with trivial linear part are the
  translations.
- `Crystal.Euclidean.mul_translationHom_mul_inv` : conjugating a translation by an affine
  isometry translates by the linear part of the vector.

## iii. Table of contents

- A. Linear parts and translations

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

namespace Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## A. Linear parts and translations -/

/-- The linear part of an affine isometry is the difference of the images of a point and the
origin. -/
lemma linear_apply (ψ : E ≃ᵃⁱ[ℝ] E) (v : E) : ψ.linearIsometryEquiv v = ψ v - ψ 0 := by
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

/-- The linear part of a translation is trivial. -/
lemma linearHom_translationHom (v : E) :
    linearHom (translationHom (Multiplicative.ofAdd v)) = 1 := by
  ext w
  show (translationHom (Multiplicative.ofAdd v)).linearIsometryEquiv w = w
  rw [linear_apply]
  show v + w - (v + 0) = w
  simp

/-- An affine isometry with trivial linear part is a translation. -/
lemma eq_translationHom_of_linearHom_eq_one (ψ : E ≃ᵃⁱ[ℝ] E) (h : linearHom ψ = 1) :
    ψ = translationHom (Multiplicative.ofAdd (ψ 0)) := by
  ext v
  have hv : ψ.linearIsometryEquiv v = v := DFunLike.congr_fun h v
  rw [linear_apply] at hv
  exact sub_eq_iff_eq_add'.1 hv

/-- The affine isometries with trivial linear part are the translations. -/
lemma ker_linearHom : (linearHom (E := E)).ker = (translationHom (E := E)).range :=
  le_antisymm (fun ψ h => ⟨_, (eq_translationHom_of_linearHom_eq_one ψ h).symm⟩)
    (by rintro _ ⟨v, rfl⟩; exact linearHom_translationHom _)

/-- Conjugating a translation by an affine isometry translates by the linear part of the vector. -/
lemma mul_translationHom_mul_inv (ψ : E ≃ᵃⁱ[ℝ] E) (v : E) :
    ψ * translationHom (Multiplicative.ofAdd v) * ψ⁻¹ =
      translationHom (Multiplicative.ofAdd (ψ.linearIsometryEquiv v)) := by
  ext x
  show ψ (v + ψ.symm x) = ψ.linearIsometryEquiv v + x
  simpa using ψ.map_vadd (ψ.symm x) v

end Euclidean

end Physlib.CondensedMatter.Crystal
