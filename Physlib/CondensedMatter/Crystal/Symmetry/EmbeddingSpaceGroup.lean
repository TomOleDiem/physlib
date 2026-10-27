/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.Tactic.Abel

/-!
# Space group of an embedded crystal

The affine isometries of space that map the positions of an embedded crystal onto themselves.

## i. Overview

An embedding places the sites of a crystal in a real normed space `E`. Its space group consists
of the affine isometries of `E` that map the set of positions onto itself. By the Mazur–Ulam
theorem, these are all the isometries of `E` that preserve the placed crystal.

Every affine isometry has a linear part, and taking it is a homomorphism whose kernel is the group
of translations of `E`. The point group consists of the linear parts of the space group, so the
space group modulo its translations is the point group. The embedding is primitive if its lattice
vectors are exactly the translations that preserve the positions.

This file studies the group in space. Its relation to the symmetries of the abstract crystal is
studied in `Crystal.Symmetry.Rigid`.

## ii. Key results

- `Crystal.Embedding.linearHom` : the linear part of an affine isometry, a homomorphism.
- `Crystal.Embedding.ker_linearHom` : the kernel of the linear part is the group of translations.
- `Crystal.Embedding.spaceGroup` : the affine isometries that preserve the set of positions.
- `Crystal.Embedding.IsPrimitive` : the lattice vectors are exactly the translations that
  preserve the positions.
- `Crystal.Embedding.exists_lattice_vector_eq_linear` : the linear part of an element of the space
  group of a primitive embedding maps lattice vectors to lattice vectors.
- `Crystal.Embedding.pointGroup` : the linear parts of the space group.
- `Crystal.Embedding.spaceGroupQuotientEquiv` : the space group modulo its translations is the
  point group.

## iii. Table of contents

- A. Linear parts and translations
- B. The space group
- C. The point group

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (R : Embedding C E)

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

/-! ## B. The space group -/

/-- The affine isometries that map the set of positions onto itself. By the Mazur–Ulam theorem,
these are all the isometries of `E` that preserve the placed crystal. -/
def spaceGroup : Subgroup (E ≃ᵃⁱ[ℝ] E) where
  carrier := {ψ | ψ '' Set.range R.position = Set.range R.position}
  one_mem' := by simp
  mul_mem' {ψ χ} hψ hχ := by
    show (⇑ψ ∘ ⇑χ) '' Set.range R.position = Set.range R.position
    rw [Set.image_comp, hχ, hψ]
  inv_mem' {ψ} hψ := by
    show ⇑ψ.symm '' Set.range R.position = Set.range R.position
    conv_lhs => rw [← show ψ '' Set.range R.position = Set.range R.position from hψ]
    exact ψ.toEquiv.symm_image_image _

/-- The embedding is primitive if its lattice vectors are exactly the translations that map the set
of positions onto itself. -/
def IsPrimitive : Prop :=
  ∀ v : E, translationHom (Multiplicative.ofAdd v) ∈ R.spaceGroup ↔ v ∈ Set.range R.vector

/-- Conjugating a translation by an affine isometry translates by the linear part of the vector. -/
lemma mul_translationHom_mul_inv (ψ : E ≃ᵃⁱ[ℝ] E) (v : E) :
    ψ * translationHom (Multiplicative.ofAdd v) * ψ⁻¹ =
      translationHom (Multiplicative.ofAdd (ψ.linearIsometryEquiv v)) := by
  ext x
  show ψ (v + ψ.symm x) = ψ.linearIsometryEquiv v + x
  simpa using ψ.map_vadd (ψ.symm x) v

/-- The linear part of an element of the space group of a primitive embedding maps lattice vectors
to lattice vectors. -/
lemma exists_lattice_vector_eq_linear (hprim : R.IsPrimitive) (hψ : ψ ∈ R.spaceGroup) (a : G) :
    ∃ b : G, R.vector b = ψ.linearIsometryEquiv (R.vector a) := by
  refine (hprim _).1 ?_
  rw [← mul_translationHom_mul_inv]
  exact mul_mem (mul_mem hψ ((hprim _).2 ⟨a, rfl⟩)) (inv_mem hψ)

/-! ## C. The point group -/

/-- The point group: the linear parts of the space group. -/
noncomputable def pointGroup : Subgroup (E ≃ₗᵢ[ℝ] E) := R.spaceGroup.map linearHom

/-- The kernel of the linear part on the space group is the group of its translations. -/
lemma ker_domRestrict_linearHom :
    (linearHom.domRestrict R.spaceGroup).ker =
      (translationHom (E := E)).range.subgroupOf R.spaceGroup := by
  rw [MonoidHom.ker_domRestrict, ker_linearHom]

/-- **The space group modulo its translations is the point group.** -/
noncomputable def spaceGroupQuotientEquiv :
    R.spaceGroup ⧸ (linearHom.domRestrict R.spaceGroup).ker ≃* R.pointGroup :=
  (QuotientGroup.quotientKerEquivRange _).trans
    (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range _ _))

end Embedding

end Physlib.CondensedMatter.Crystal
