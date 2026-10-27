/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding
public import Physlib.CondensedMatter.Crystal.Symmetry.AffineIsometries

/-!
# Space group of an embedded crystal

The affine isometries of space that map the positions of an embedded crystal onto themselves.

## i. Overview

An embedding places the sites of a crystal in a real normed space. Its space group consists of the
affine isometries of the space that map the set of positions onto itself. It contains the
translations by lattice vectors, and its point group collects the rotations and reflections that
occur.

Whether the space group contains translations beyond the lattice depends on the placement. The
embedding is primitive if it does not, so that the translations in the space group are exactly the
translations by lattice vectors. For a primitive embedding the point group maps lattice vectors to
lattice vectors, since conjugating a lattice translation by an element of the space group gives the
translation by the rotated vector, which is again in the space group.

## ii. Key results

- `Crystal.Embedding.spaceGroup` : the affine isometries that preserve the set of positions.
- `Crystal.Embedding.IsPrimitive` : the lattice vectors are exactly the translations that
  preserve the positions.
- `Crystal.Embedding.exists_lattice_vector_eq_linear` : the linear part of an element of the space
  group of a primitive embedding maps lattice vectors to lattice vectors.
- `Crystal.Embedding.pointGroup` : the linear parts of the space group.

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
  (R : Embedding C E) {ψ : E ≃ᵃⁱ[ℝ] E}

/-! ## A. The space group -/

/-- The affine isometries that map the set of positions onto itself. -/
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

/-- An affine isometry is in the space group when it maps the positions onto themselves. -/
lemma mem_spaceGroup_iff :
    ψ ∈ R.spaceGroup ↔ ψ '' Set.range R.position = Set.range R.position :=
  Iff.rfl

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

end Embedding

end Physlib.CondensedMatter.Crystal
