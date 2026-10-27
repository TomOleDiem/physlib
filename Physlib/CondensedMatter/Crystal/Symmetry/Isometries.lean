/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding
public import Physlib.CondensedMatter.Crystal.Symmetry.PointOperations
public import Mathlib.Tactic.Abel

/-!
# Isometries of an embedded crystal

An embedding assigns a position to each crystal site. This file studies the crystal symmetries
that preserve distances between those positions.

## i. Overview

A symmetry `φ` is an isometry of the embedded crystal when, for every pair of sites `x` and `y`,

`dist (R.position (φ x)) (R.position (φ y)) = dist (R.position x) (R.position y)`.

These symmetries form a subgroup. Every translation belongs to it because translating both
sites leaves their distance unchanged.

A site's position is determined by its lattice cell and unit-cell label. Under a symmetry, the
difference between two image positions depends on the cells through their difference `d`.
Consequently, the isometry condition can be checked using a lattice step `d` and two labels
`i` and `j`. This criterion also shows that an isometry preserves the lengths of lattice
translation vectors and the distances between sites in the reference cell.

## ii. Key results

- `Embedding.isometries`: crystal symmetries that preserve distances between site positions.
- `Embedding.translations_le_isometries`: every translation is an isometry.
- `Embedding.mem_isometries_iff_components`: the distance criterion in lattice and unit-cell
  coordinates.
- `Embedding.norm_vector_lattice`: an isometry preserves lengths of lattice translation vectors.
- `Embedding.norm_imageSub`: an isometry preserves distances between reference-cell sites.
- `Embedding.imageSub_ofComponents`: the image-position difference for a symmetry given by its
  lattice automorphism, label permutation, and offsets.

## iii. Table of contents

- A. Distance-preserving symmetries
- B. Distances in lattice and unit-cell coordinates

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] (R : Embedding C E) {φ : Symmetry C}

/-! ## A. Distance-preserving symmetries -/

/-- The crystal symmetries that preserve distances between all pairs of site positions. -/
def isometries : Subgroup (Symmetry C) where
  carrier := {φ | ∀ x y, dist (R.position (φ x)) (R.position (φ y)) =
    dist (R.position x) (R.position y)}
  one_mem' := by
    intro x y
    rfl
  mul_mem' {φ ψ} hφ hψ := by
    intro x y
    rw [Symmetry.mul_apply, Symmetry.mul_apply, hφ, hψ]
  inv_mem' {φ} hφ := by
    intro x y
    simpa using (hφ (φ⁻¹ x) (φ⁻¹ y)).symm

/-- A symmetry is an isometry exactly when it preserves every distance between site positions. -/
lemma mem_isometries_iff : φ ∈ R.isometries ↔
    ∀ x y, dist (R.position (φ x)) (R.position (φ y)) = dist (R.position x) (R.position y) := by
  rfl

/-- Translating both sites by the same lattice vector preserves their distance. -/
lemma translations_le_isometries : Symmetry.translations C ≤ R.isometries := by
  rintro _ ⟨a, rfl⟩ x y
  exact R.dist_position_vadd _ x y

/-! ## B. Distances in lattice and unit-cell coordinates -/

/-- The position of the image of label `i` minus that of the image of label `j`, with both
labels taken in the reference cell. -/
abbrev imageSub (φ : Symmetry C) (i j : C.UnitCell) : E :=
  R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)

/-- The distance between two sites, expressed through their cell difference and basis positions. -/
lemma dist_position (x y : C.Site) : dist (R.position x) (R.position y) =
    ‖R.vector (x.cell - y.cell) + (R.basis x.label - R.basis y.label)‖ := by
  rw [dist_eq_norm, Embedding.position, Embedding.position, map_sub]
  congr 1
  abel

/-- A site is the lattice translate of the site with the same label in the reference cell. -/
lemma site_eq_vadd (x : C.Site) : x = x.cell +ᵥ (⟨0, x.label⟩ : C.Site) :=
  Site.ext (by simp) rfl

/-- The image position of a site is the image position of its reference-cell label, translated
by the image of its cell vector. -/
lemma position_apply (x : C.Site) : R.position (φ x) =
    R.vector (φ.lattice x.cell) + R.position (φ ⟨0, x.label⟩) := by
  conv_lhs => rw [site_eq_vadd x]
  rw [Symmetry.map_vadd, R.position_vadd]

/-- The distance between image sites depends on their cells through their difference. -/
lemma dist_position_apply (x y : C.Site) : dist (R.position (φ x)) (R.position (φ y)) =
    ‖R.vector (φ.lattice (x.cell - y.cell)) + R.imageSub φ x.label y.label‖ := by
  rw [dist_eq_norm, R.position_apply (φ := φ) x, R.position_apply (φ := φ) y, map_sub, map_sub]
  unfold imageSub
  congr 1
  abel

/-- A symmetry is an isometry exactly when it preserves the distance from `(d, i)` to `(0, j)`
for every lattice step `d` and pair of labels `i`, `j`. -/
lemma mem_isometries_iff_components : φ ∈ R.isometries ↔ ∀ (i j : C.UnitCell) (d : G),
    ‖R.vector (φ.lattice d) + R.imageSub φ i j‖ =
      ‖R.vector d + (R.basis i - R.basis j)‖ := by
  constructor
  · intro h i j d
    have := h ⟨d, i⟩ ⟨0, j⟩
    rw [dist_position_apply, dist_position] at this
    simpa only [sub_zero] using this
  · intro h x y
    rw [dist_position_apply, dist_position]
    exact h _ _ _

/-- An isometry preserves the length of each lattice translation vector. -/
lemma norm_vector_lattice (hφ : φ ∈ R.isometries) (a : G) :
    ‖R.vector (φ.lattice a)‖ = ‖R.vector a‖ := by
  simpa using R.mem_isometries_iff_components.1 hφ (Classical.arbitrary _) (Classical.arbitrary _) a

/-- An isometry preserves distances between sites in the reference cell. -/
lemma norm_imageSub (hφ : φ ∈ R.isometries) (i j : C.UnitCell) :
    ‖R.imageSub φ i j‖ = ‖R.basis i - R.basis j‖ := by
  simpa [Embedding.position] using R.mem_isometries_iff_components.1 hφ i j 0

/-- The difference between image positions of reference-cell labels for a symmetry specified by
lattice automorphism `A`, label permutation `σ`, and offsets `b`. -/
lemma imageSub_ofComponents (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) (b : C.UnitCell → G)
    (i j : C.UnitCell) : R.imageSub (Symmetry.ofComponents C A σ b) i j =
      (R.vector (b i) + R.basis (σ i)) - (R.vector (b j) + R.basis (σ j)) := by
  simp [imageSub, Embedding.position]

end Embedding

end Physlib.CondensedMatter.Crystal
