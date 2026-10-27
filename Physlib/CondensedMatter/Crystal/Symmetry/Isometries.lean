/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding
public import Physlib.CondensedMatter.Crystal.Symmetries

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
- `Embedding.mem_isometries_iff_referenceCell`: A symmetry is an isometry exactly when it
  preserves the distances from the sites of the reference cell.

## iii. Table of contents

- A. Distance-preserving symmetries
- B. Checking on the reference cell

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

/-! ## B. Checking on the reference cell -/

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
