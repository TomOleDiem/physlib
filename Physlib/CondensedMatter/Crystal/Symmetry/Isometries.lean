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

The symmetries of a crystal that preserve the distances between its sites in space.

## i. Overview

An embedding places every site of a crystal at a point of a normed group. A symmetry of the
crystal is an isometry if it preserves the distance between the positions of any two sites,

`dist (position (φ x)) (position (φ y)) = dist (position x) (position y)`.

These symmetries are a subgroup of the symmetries of the crystal. It contains the translations,
which move both sites by the same vector, and it is independent of the bonds and of the species.

A symmetry moves a site `(n, i)` to the translate of the image of `(0, i)` by the image of `n`.
Hence the distance between two image sites depends on the cells only through their difference
`d`, and being an isometry is a condition on pairs of labels `(i, j)` and lattice steps `d`.

## ii. Key results

- `Crystal.Embedding.isometries` : the symmetries that preserve the distances between positions.
- `Crystal.Embedding.translations_le_isometries` : translations are isometries.
- `Crystal.Embedding.mem_isometries_iff_components` : a symmetry is an isometry exactly when a
  condition on pairs of labels and lattice steps holds.
- `Crystal.Embedding.norm_vector_lattice` : an isometry preserves the lengths of the translation
  vectors.
- `Crystal.Embedding.imageSub_ofComponents` : the label position differences of the symmetry with
  given lattice automorphism, label permutation and offsets.

## iii. Table of contents

- A. Isometries
- B. Coordinates of the image sites

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] (R : Embedding C E) {φ : Symmetry C}

/-! ## A. Isometries -/

/-- The symmetries of a crystal that preserve the distance between the positions of any two
sites. -/
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
    have := hφ (φ⁻¹ x) (φ⁻¹ y)
    rw [Symmetry.apply_inv_apply, Symmetry.apply_inv_apply] at this
    exact this.symm

/-- A symmetry is an isometry when it preserves the distance between any two sites. -/
lemma mem_isometries_iff : φ ∈ R.isometries ↔
    ∀ x y, dist (R.position (φ x)) (R.position (φ y)) = dist (R.position x) (R.position y) := by
  rfl

/-- Translations are isometries. -/
lemma translations_le_isometries : Symmetry.translations C ≤ R.isometries := by
  rintro _ ⟨a, rfl⟩ x y
  exact R.dist_position_vadd _ x y

/-! ## B. Coordinates of the image sites -/

/-- The difference of the positions of the images of two labels. -/
abbrev imageSub (φ : Symmetry C) (i j : C.UnitCell) : E :=
  R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)

/-- The distance between the positions of two sites, in terms of their cells and labels. -/
lemma dist_position (x y : C.Site) : dist (R.position x) (R.position y) =
    ‖R.vector (x.cell - y.cell) + (R.basis x.label - R.basis y.label)‖ := by
  rw [dist_eq_norm, Embedding.position, Embedding.position, map_sub]
  congr 1
  abel

/-- A site is the translate of the site with the same label in the reference cell. -/
lemma site_eq_vadd (x : C.Site) : x = x.cell +ᵥ (⟨0, x.label⟩ : C.Site) :=
  Site.ext (by simp) rfl

/-- A symmetry moves the position of a site by the vector of the image of its cell, starting from
the position of the image of the same label in the reference cell. -/
lemma position_apply (x : C.Site) : R.position (φ x) =
    R.vector (φ.lattice x.cell) + R.position (φ ⟨0, x.label⟩) := by
  conv_lhs => rw [site_eq_vadd x]
  rw [Symmetry.map_vadd, R.position_vadd]

/-- The distance between two image sites depends on their cells only through the difference. -/
lemma dist_position_apply (x y : C.Site) : dist (R.position (φ x)) (R.position (φ y)) =
    ‖R.vector (φ.lattice (x.cell - y.cell)) + R.imageSub φ x.label y.label‖ := by
  rw [dist_eq_norm, R.position_apply (φ := φ) x, R.position_apply (φ := φ) y, map_sub, map_sub]
  unfold imageSub
  congr 1
  abel

/-- A symmetry is an isometry exactly when, for every pair of labels `i`, `j` and every lattice
step `d`, the distance between the images of `(d, i)` and `(0, j)` is unchanged. -/
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

/-- An isometry preserves the lengths of the translation vectors. -/
lemma norm_vector_lattice (hφ : φ ∈ R.isometries) (a : G) :
    ‖R.vector (φ.lattice a)‖ = ‖R.vector a‖ := by
  simpa using R.mem_isometries_iff_components.1 hφ (Classical.arbitrary _) (Classical.arbitrary _) a

/-- An isometry preserves the distances between the positions of the labels. -/
lemma norm_imageSub (hφ : φ ∈ R.isometries) (i j : C.UnitCell) :
    ‖R.imageSub φ i j‖ = ‖R.basis i - R.basis j‖ := by
  simpa [Embedding.position] using R.mem_isometries_iff_components.1 hφ i j 0

/-- The label position differences of the symmetry with lattice automorphism `A`, label
permutation `σ` and offsets `b`. -/
lemma imageSub_ofComponents (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) (b : C.UnitCell → G)
    (i j : C.UnitCell) : R.imageSub (Symmetry.ofComponents C A σ b) i j =
      (R.vector (b i) + R.basis (σ i)) - (R.vector (b j) + R.basis (σ j)) := by
  simp [imageSub, Embedding.position]

end Embedding

end Physlib.CondensedMatter.Crystal
