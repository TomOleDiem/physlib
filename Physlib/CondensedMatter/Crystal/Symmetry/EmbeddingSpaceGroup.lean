/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding
public import Physlib.CondensedMatter.Crystal.Symmetry.AffineIsometries
public import Mathlib.Analysis.Normed.Affine.MazurUlam

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

- `Crystal.Embedding.spaceGroup` : the affine isometries that preserve the set of positions.
- `Crystal.Embedding.IsPrimitive` : the lattice vectors are exactly the translations that
  preserve the positions.
- `Crystal.Embedding.exists_lattice_vector_eq_linear` : the linear part of an element of the space
  group of a primitive embedding maps lattice vectors to lattice vectors.
- `Crystal.Embedding.pointGroup` : the linear parts of the space group.
- `Crystal.Embedding.spaceGroupQuotientEquiv` : the space group modulo its translations is the
  point group.

## iii. Table of contents

- A. The space group
- B. The point group

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

open Euclidean

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (R : Embedding C E)

/-! ## A. The space group -/

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

/-- The linear part of an element of the space group of a primitive embedding maps lattice vectors
to lattice vectors. -/
lemma exists_lattice_vector_eq_linear (hprim : R.IsPrimitive) (hψ : ψ ∈ R.spaceGroup) (a : G) :
    ∃ b : G, R.vector b = ψ.linearIsometryEquiv (R.vector a) := by
  refine (hprim _).1 ?_
  rw [← mul_translationHom_mul_inv]
  exact mul_mem (mul_mem hψ ((hprim _).2 ⟨a, rfl⟩)) (inv_mem hψ)

/-! ## B. The point group -/

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
