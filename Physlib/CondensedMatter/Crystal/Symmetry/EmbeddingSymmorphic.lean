/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Bravais.Basic
public import Physlib.CondensedMatter.Crystal.Symmetry.FinitePointGroup
public import Physlib.CondensedMatter.Crystal.Symmetry.Symmorphic

/-!
# Embedded crystals with symmorphic space group

The space group of a crystal whose sites sit at lattice points is symmorphic.

## i. Overview

Suppose the position of every label of the unit cell is a lattice vector, as for a Bravais lattice
with one site per cell placed at the origin. Then the set of positions is the lattice, and the
embedding is primitive: a translation preserves the lattice exactly when its vector is a lattice
vector.

Every element of the point group maps the lattice onto itself, so it is itself an affine isometry
that preserves the positions and fixes the origin. Hence all point operations are realised by
elements of the space group about the origin, and the space group is symmorphic.

## ii. Key results

- `Crystal.Embedding.isSymmorphic_of_basis_mem` : if the positions of the labels are lattice
  vectors, the space group is symmorphic.
- `Crystal.Embedding.isSymmorphic_ofVectors` : the space group of a Bravais lattice is
  symmorphic.

## iii. Table of contents

- A. Sites at lattice points
- B. The space group is symmorphic

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

/-! ## A. Sites at lattice points -/

omit [NormedSpace ℝ E] in
/-- If the positions of the labels are lattice vectors, the positions form the lattice. -/
lemma range_position_eq (hb : ∀ i, R.basis i ∈ R.vector.range) :
    Set.range R.position = R.vector.range := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact add_mem ⟨x.cell, rfl⟩ (hb x.label)
  · rintro _ ⟨a, rfl⟩
    obtain ⟨b, hb'⟩ := hb (Classical.arbitrary C.UnitCell)
    exact ⟨⟨a - b, Classical.arbitrary _⟩, by simp [position, hb']⟩

/-- If the positions of the labels are lattice vectors, the embedding is primitive. -/
lemma isPrimitive_of_basis_mem (hb : ∀ i, R.basis i ∈ R.vector.range) : R.IsPrimitive := by
  intro v
  show (fun x => v + x) '' Set.range R.position = Set.range R.position ↔ _
  rw [R.range_position_eq hb]
  constructor
  · intro h
    simpa using h.subset ⟨0, R.vector.range.zero_mem, rfl⟩
  · intro hv
    simpa only [← Set.image_vadd, vadd_eq_add] using vadd_coe_set hv

/-! ## B. The space group is symmorphic -/

/-- Every element of the point group maps the lattice onto itself. -/
lemma image_lattice_eq (hb : ∀ i, R.basis i ∈ R.vector.range) {L : E ≃ₗᵢ[ℝ] E}
    (hL : L ∈ R.pointGroup) : L '' (R.vector.range : Set E) = R.vector.range := by
  have hprim := R.isPrimitive_of_basis_mem hb
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact R.pointGroup_apply_mem hprim hL a
  · rintro _ ⟨a, rfl⟩
    refine ⟨L.symm (R.vector a), ?_, L.apply_symm_apply _⟩
    exact R.pointGroup_apply_mem hprim (inv_mem hL) a

/-- Every point operation is an element of the space group fixing the origin. -/
lemma toAffineIsometryEquiv_mem_spaceGroup (hb : ∀ i, R.basis i ∈ R.vector.range)
    {L : E ≃ₗᵢ[ℝ] E} (hL : L ∈ R.pointGroup) : L.toAffineIsometryEquiv ∈ R.spaceGroup := by
  rw [mem_spaceGroup_iff, R.range_position_eq hb]
  exact R.image_lattice_eq hb hL

/-- **If the positions of the labels are lattice vectors, the space group is symmorphic.** -/
lemma isSymmorphic_of_basis_mem (hb : ∀ i, R.basis i ∈ R.vector.range) :
    IsSymmorphic R.spaceGroup := by
  refine isSymmorphic_of_map_fixing (p := 0) (le_antisymm (Subgroup.map_mono inf_le_left) ?_)
  intro g hg
  refine Subgroup.mem_map.2 ⟨g.toAffineIsometryEquiv, ⟨?_, g.map_zero⟩, rfl⟩
  exact R.toAffineIsometryEquiv_mem_spaceGroup hb hg

/-- The space group of a Bravais lattice is symmorphic. -/
lemma isSymmorphic_ofVectors {d : ℕ} (v : Fin d → E) : IsSymmorphic (ofVectors v).spaceGroup := by
  refine (ofVectors v).isSymmorphic_of_basis_mem ?_
  intro i
  exact zero_mem _

end Embedding

end Physlib.CondensedMatter.Crystal
