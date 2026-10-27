/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding
public import Physlib.CondensedMatter.Crystal.Symmetries
public import Mathlib.Tactic.Abel

/-!
# Isometries of an embedded crystal

The crystal symmetries that preserve the distances between sites in space.

## i. Overview

An embedding places every site of a crystal at a point of a normed group. A crystal symmetry is an
isometry of the embedded crystal if it preserves the distance between the positions of any two
sites,

`dist (position (φ x)) (position (φ y)) = dist (position x) (position y)`.

These symmetries form a subgroup of the crystal symmetries, and it contains the translations,
which move both sites by the same vector. Since translating a pair of sites does not change its
distance, it suffices to compare the distances from the sites of the reference cell.

## ii. Key results

- `Embedding.isometries`: The crystal symmetries that preserve distances between positions.
- `Embedding.translations_le_isometries`: Translations are isometries.
- `Embedding.norm_vector_lattice`: An isometry preserves the lengths of the translation vectors.
- `Embedding.mem_isometries_iff_components`: A symmetry is an isometry exactly when a condition
  on pairs of labels and cell differences holds.
- `Embedding.mem_isometries_iff_referenceCell`: A symmetry is an isometry exactly when it
  preserves the distances from the sites of the reference cell.

## iii. Table of contents

- A. Distance-preserving symmetries
- B. Lengths of the translation vectors
- C. Coordinates of an isometry
- D. Checking on the reference cell

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] (R : Embedding C E)
  {φ : Symmetry C}

/-! ## A. Distance-preserving symmetries -/

/-- The crystal symmetries that preserve the distance between the positions of any two sites. -/
def isometries : Subgroup (Symmetry C) where
  carrier := {φ | ∀ x y, dist (R.position (φ x)) (R.position (φ y)) =
    dist (R.position x) (R.position y)}
  one_mem' _ _ := rfl
  mul_mem' hφ hψ x y := (hφ _ _).trans (hψ x y)
  inv_mem' {φ} hφ x y := by simpa using (hφ (φ⁻¹ x) (φ⁻¹ y)).symm

/-- A symmetry is an isometry when it preserves the distance between any two sites. -/
lemma mem_isometries_iff : φ ∈ R.isometries ↔
    ∀ x y, dist (R.position (φ x)) (R.position (φ y)) = dist (R.position x) (R.position y) :=
  Iff.rfl

/-- Translations are isometries. -/
lemma translations_le_isometries : Symmetry.translations C ≤ R.isometries := by
  rintro _ ⟨a, rfl⟩ x y
  exact R.dist_position_vadd _ x y

/-! ## B. Lengths of the translation vectors -/

/-- The distance between a site and its translate by `a` is the norm of the vector of `a`. -/
lemma dist_position_vadd_self (a : G) (x : C.Site) :
    dist (R.position (a +ᵥ x)) (R.position x) = ‖R.vector a‖ := by
  rw [R.position_vadd, dist_eq_norm, add_sub_cancel_right]

/-- An isometry acts on the translation vectors by norm-preserving maps: the vector of the
image of a lattice step has the same length as the vector of the step. -/
lemma norm_vector_lattice (hφ : φ ∈ R.isometries) (a : G) :
    ‖R.vector (φ.lattice a)‖ = ‖R.vector a‖ := by
  have h := hφ (a +ᵥ ⟨0, Classical.arbitrary C.UnitCell⟩) ⟨0, Classical.arbitrary C.UnitCell⟩
  rwa [Symmetry.map_vadd, R.dist_position_vadd_self, R.dist_position_vadd_self] at h

/-! ## C. Coordinates of an isometry -/

/-- The distance between the positions of two sites, in terms of their cells and labels. -/
lemma dist_position (x y : C.Site) : dist (R.position x) (R.position y) =
    ‖R.vector (x.cell - y.cell) + R.basis x.label - R.basis y.label‖ := by
  rw [dist_eq_norm, Embedding.position, Embedding.position, map_sub]
  congr 1
  abel

/-- A symmetry moves the position of a site by the vector of the lattice automorphism applied to
its cell, starting from the position of the image of the same label in the reference cell. -/
lemma position_apply (x : C.Site) : R.position (φ x) =
    R.vector (φ.lattice x.cell) + R.position (φ ⟨0, x.label⟩) := by
  conv_lhs => rw [show x = x.cell +ᵥ (⟨0, x.label⟩ : C.Site) from Site.ext (by simp) rfl]
  rw [Symmetry.map_vadd, R.position_vadd]

/-- The distance between the images of two sites depends on their cells only through the
difference of the cells. -/
lemma dist_position_apply (x y : C.Site) : dist (R.position (φ x)) (R.position (φ y)) =
    ‖R.vector (φ.lattice (x.cell - y.cell)) + R.position (φ ⟨0, x.label⟩) -
      R.position (φ ⟨0, y.label⟩)‖ := by
  rw [dist_eq_norm, R.position_apply (φ := φ) x, R.position_apply (φ := φ) y, map_sub, map_sub]
  congr 1
  abel

/-- A symmetry is an isometry exactly when, for every pair of labels and every cell difference `d`,
the vector from the image of `j` to the image of `i` shifted by the lattice step `d` has the
same length as before. -/
lemma mem_isometries_iff_components : φ ∈ R.isometries ↔ ∀ (i j : C.UnitCell) (d : G),
    ‖R.vector (φ.lattice d) + R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)‖ =
      ‖R.vector d + R.basis i - R.basis j‖ := by
  refine ⟨fun h i j d => ?_, fun h x y => ?_⟩
  · have := h ⟨d, i⟩ ⟨0, j⟩
    rw [dist_position_apply, dist_position] at this
    simpa only [sub_zero] using this
  · rw [dist_position_apply, dist_position]
    exact h _ _ _

/-! ## D. Checking on the reference cell -/

/-- A symmetry is an isometry exactly when it preserves the distances from the sites of the
reference cell to all sites. -/
lemma mem_isometries_iff_referenceCell : φ ∈ R.isometries ↔ ∀ (i : C.UnitCell) (y : C.Site),
    dist (R.position (φ ⟨0, i⟩)) (R.position (φ y)) = dist (R.position ⟨0, i⟩) (R.position y) := by
  refine ⟨fun h i y => h _ _, fun h x y => ?_⟩
  have hx : x = x.cell +ᵥ (⟨0, x.label⟩ : C.Site) := Site.ext (by simp) rfl
  have hy : y = x.cell +ᵥ ((-x.cell) +ᵥ y) := by simp
  rw [hx, hy, Symmetry.map_vadd, Symmetry.map_vadd, R.dist_position_vadd, R.dist_position_vadd]
  exact h _ _

end Embedding

end Physlib.CondensedMatter.Crystal
