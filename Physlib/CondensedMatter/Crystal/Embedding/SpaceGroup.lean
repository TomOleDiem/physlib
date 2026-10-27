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
of the affine isometries of `E` that map the set of positions onto itself; by the Mazur–Ulam
theorem these are all the isometries of `E` that preserve the placed crystal.

Each affine isometry has a linear part, and taking it is a homomorphism whose kernel is the
group of translations of `E`. The point group consists of the linear parts of the space group.
The space group modulo its translations is the point group. When the translation vectors of the
embedding are exactly the translations that preserve the positions, the translations in the space
group are exactly the translations by lattice vectors.

## ii. Key results

- `Embedding.linearHom`: The linear part of an affine isometry, as a homomorphism.
- `Embedding.ker_linearHom`: The kernel of the linear part is the group of translations.
- `Embedding.spaceGroup`: The affine isometries that preserve the set of positions.
- `Embedding.pointGroup`: The linear parts of the space group.
- `Embedding.spaceGroupQuotientEquiv`: The space group modulo its translations is the point
  group.
- `Embedding.IsPrimitive`: The lattice vectors are exactly the translations preserving the
  positions.

## iii. Table of contents

- A. The space group
- B. The point group

## iv. References

* N. W. Ashcroft and N. D. Mermin, *Solid State Physics*, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (R : Embedding C E)

/-! ## A. The space group -/

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

/-- An affine isometry with trivial linear part is a translation. -/
lemma eq_translation_of_linear_eq_one (ψ : E ≃ᵃⁱ[ℝ] E) (h : linearHom ψ = 1) :
    ψ = translationHom (Multiplicative.ofAdd (ψ 0)) := by
  ext v
  have hv : ψ.linearIsometryEquiv v = v := DFunLike.congr_fun h v
  rw [linear_apply] at hv
  exact sub_eq_iff_eq_add'.1 hv

/-- The linear part of a translation is trivial. -/
lemma linearHom_translationHom (v : E) :
    linearHom (translationHom (Multiplicative.ofAdd v)) = 1 := by
  ext w
  show (translationHom (Multiplicative.ofAdd v)).linearIsometryEquiv w = w
  rw [linear_apply]
  show v + w - (v + 0) = w
  simp

/-- The kernel of the linear part is the translations. -/
lemma ker_linearHom : (linearHom (E := E)).ker = (translationHom (E := E)).range := by
  ext ψ
  constructor
  · intro h
    exact ⟨_, (eq_translation_of_linear_eq_one ψ h).symm⟩
  · rintro ⟨v, rfl⟩
    exact linearHom_translationHom (Multiplicative.toAdd v)

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
    conv_lhs => rw [← hψ]
    rw [← Set.image_comp]
    simp

/-- A translation is in the space group when it maps the set of positions onto itself. -/
lemma translation_mem_spaceGroup_iff (v : E) :
    translationHom (Multiplicative.ofAdd v) ∈ R.spaceGroup ↔
      (HAdd.hAdd v) '' Set.range R.position = Set.range R.position := Iff.rfl

/-- The lattice is the full translation group of the placed crystal: a translation maps the
positions onto themselves exactly when its vector is a translation vector of the lattice. -/
def IsPrimitive : Prop :=
  ∀ v : E, (HAdd.hAdd v) '' Set.range R.position = Set.range R.position ↔
    v ∈ Set.range R.vector

/-! ## B. The point group -/

/-- The point group: the linear parts of the space group. -/
noncomputable def pointGroup : Subgroup (E ≃ₗᵢ[ℝ] E) := R.spaceGroup.map linearHom

/-- The homomorphism from the space group to the point group. -/
noncomputable def spaceGroupToPointGroup : R.spaceGroup →* R.pointGroup :=
  (linearHom.comp R.spaceGroup.subtype).codRestrict _ (by
    intro ψ
    exact ⟨ψ, ψ.2, rfl⟩)

/-- Every element of the point group is the linear part of an element of the space group. -/
lemma spaceGroupToPointGroup_surjective : Function.Surjective R.spaceGroupToPointGroup := by
  rintro ⟨φ, ψ, hψ, rfl⟩
  exact ⟨⟨ψ, hψ⟩, rfl⟩

/-- **The space group modulo its translations is the point group.** -/
noncomputable def spaceGroupQuotientEquiv :
    R.spaceGroup ⧸ R.spaceGroupToPointGroup.ker ≃* R.pointGroup :=
  QuotientGroup.quotientKerEquivOfSurjective _ R.spaceGroupToPointGroup_surjective

/-- The kernel of the map to the point group consists of translations of the space group. -/
lemma mem_ker_spaceGroupToPointGroup_iff (ψ : R.spaceGroup) :
    ψ ∈ R.spaceGroupToPointGroup.ker ↔ ∃ v : E, (ψ : E ≃ᵃⁱ[ℝ] E) =
      translationHom (Multiplicative.ofAdd v) := by
  constructor
  · intro h
    have h1 : linearHom (ψ : E ≃ᵃⁱ[ℝ] E) = 1 := congrArg Subtype.val h
    exact ⟨_, eq_translation_of_linear_eq_one _ h1⟩
  · rintro ⟨v, hv⟩
    apply Subtype.ext
    show linearHom (ψ : E ≃ᵃⁱ[ℝ] E) = 1
    rw [hv]
    exact linearHom_translationHom v

/-- When the lattice is the full translation group of the crystal, the translations of the space
group are exactly the translations by lattice vectors. -/
lemma mem_ker_spaceGroupToPointGroup_iff_of_isPrimitive (hR : R.IsPrimitive) (ψ : R.spaceGroup) :
    ψ ∈ R.spaceGroupToPointGroup.ker ↔ ∃ a : G,
      (ψ : E ≃ᵃⁱ[ℝ] E) = translationHom (Multiplicative.ofAdd (R.vector a)) := by
  rw [mem_ker_spaceGroupToPointGroup_iff]
  constructor
  · rintro ⟨v, hv⟩
    have hmem : translationHom (Multiplicative.ofAdd v) ∈ R.spaceGroup := hv ▸ ψ.2
    obtain ⟨a, rfl⟩ := (hR v).1 ((R.translation_mem_spaceGroup_iff v).1 hmem)
    exact ⟨a, hv⟩
  · rintro ⟨a, ha⟩
    exact ⟨_, ha⟩


end Embedding

end Physlib.CondensedMatter.Crystal
