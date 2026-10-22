/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetries
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Placing a crystal in a metric space

Distances between sites come from placing the crystal in a metric space on which translations act by
isometries.

## i. Overview

So far a crystal has no geometry. To measure distances, place its sites in a metric space `M` on
which the translation group `G` acts by isometries, such that translating a site translates its
position: `position (a +ᵥ x) = a +ᵥ position x`. For `ℤᵈ` acting on Euclidean space this is the
usual picture of a lattice with a basis.

## ii. Key results

- `Crystal.Embedding` : positions of the sites in a metric space, compatible with translation.
- `Crystal.Embedding.isometries` : the symmetries that keep the distance between any two sites.
- `Crystal.Embedding.mem_isometries_iff` : this is checked on pairs with first site in the
  reference cell.
- `Crystal.Embedding.translations_le_isometries` : translations keep distances.

## iii. Table of contents

- A. Positions of the sites
- B. Symmetries that keep distances

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

/-! ## A. Positions of the sites -/

/-- Positions of the sites of a crystal in a metric space on which the translation group acts by
isometries, compatible with translation. -/
structure Embedding (C : Crystal G) (M : Type*) [MetricSpace M] [AddAction G M] where
  /-- The position of a site. -/
  position : C.Site → M
  /-- Translating a site translates its position. -/
  position_vadd : ∀ (a : G) (x : C.Site), position (a +ᵥ x) = a +ᵥ position x

namespace Embedding

variable {C : Crystal G} {M : Type*} [MetricSpace M] [AddAction G M] [IsIsometricVAdd G M]
  (R : Embedding C M)

/-- The distance between two sites is the distance between their positions. -/
def dist (x y : C.Site) : ℝ := Dist.dist (R.position x) (R.position y)

/-- Translating two sites does not change their distance. -/
lemma dist_vadd (a : G) (x y : C.Site) : R.dist (a +ᵥ x) (a +ᵥ y) = R.dist x y := by
  simp only [dist, R.position_vadd]
  exact (isometry_vadd M a).dist_eq _ _

/-! ## B. Symmetries that keep distances -/

/-- The symmetries that keep the distance between any two sites. -/
def isometries : Subgroup (Symmetry C) where
  carrier := {φ | ∀ x y, R.dist (φ x) (φ y) = R.dist x y}
  one_mem' _ _ := rfl
  mul_mem' hφ hψ x y := (hφ _ _).trans (hψ x y)
  inv_mem' {φ} hφ x y := by simpa using (hφ (φ⁻¹ x) (φ⁻¹ y)).symm

/-- **A symmetry keeps all distances exactly when it keeps the distances from the sites of the
reference cell to every other site.** -/
lemma mem_isometries_iff (φ : Symmetry C) :
    φ ∈ R.isometries ↔
      ∀ (i : C.UnitCell) (δ : G) (j : C.UnitCell),
        R.dist (φ ⟨0, i⟩) (φ ⟨δ, j⟩) = R.dist ⟨0, i⟩ ⟨δ, j⟩ := by
  constructor
  · intro h i δ j
    exact h _ _
  intro h x y
  have hx : x = x.cell +ᵥ (⟨0, x.label⟩ : C.Site) := Site.ext (by simp) rfl
  have hy : y = x.cell +ᵥ (⟨y.cell - x.cell, y.label⟩ : C.Site) := Site.ext (by simp) rfl
  rw [hx, hy, φ.map_vadd, φ.map_vadd, R.dist_vadd, R.dist_vadd]
  exact h _ _ _

/-- Translations keep distances. -/
lemma translations_le_isometries : Symmetry.translations C ≤ R.isometries := by
  rintro _ ⟨a, rfl⟩ x y
  exact R.dist_vadd (Multiplicative.toAdd a) x y

end Embedding

end Physlib.CondensedMatter.Crystal
