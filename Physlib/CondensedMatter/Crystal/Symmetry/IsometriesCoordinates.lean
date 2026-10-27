/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.Isometries
public import Mathlib.Tactic.Abel

/-!
# Isometries in lattice and unit-cell coordinates

The distance between two image sites of a symmetry, written through the lattice automorphism.

## i. Overview

A site is located by its lattice cell and its unit-cell label, and its position is the vector of
the cell plus the position of the label. A symmetry `φ` moves the site `(n, i)` to the translate
of the image of `(0, i)` by the image of the cell `n`. Consequently the distance between two image
sites depends on their cells only through the difference `d`, and `φ` is an isometry exactly when,
for all labels `i` and `j` and every lattice step `d`, the vector

`R.vector (φ.lattice d) + (R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩))`

has the same length as `R.vector d + (R.basis i - R.basis j)`. In particular an isometry preserves
the lengths of the lattice translation vectors and the distances between the sites of the
reference cell.

## ii. Key results

- `Embedding.mem_isometries_iff_components`: the distance criterion in lattice and unit-cell
  coordinates.
- `Embedding.norm_vector_lattice`: an isometry preserves lengths of lattice translation vectors.
- `Embedding.norm_position_sub`: an isometry preserves distances between reference-cell sites.
- `Embedding.position_sub_ofComponents`: the difference of the image positions of two labels for a
  symmetry given by its lattice automorphism, label permutation, and offsets.

## iii. Table of contents

- A. Image positions
- B. The criterion in coordinates

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] (R : Embedding C E) {φ : Symmetry C}

/-! ## A. Image positions -/

/-- The distance between two sites, expressed through their cell difference and basis positions. -/
lemma dist_position (x y : C.Site) : dist (R.position x) (R.position y) =
    ‖R.vector (x.cell - y.cell) + (R.basis x.label - R.basis y.label)‖ := by
  rw [dist_eq_norm, Embedding.position, Embedding.position, map_sub]
  congr 1
  abel

/-- The image position of a site is the image position of its reference-cell label, translated
by the image of its cell vector. -/
lemma position_apply (x : C.Site) : R.position (φ x) =
    R.vector (φ.lattice x.cell) + R.position (φ ⟨0, x.label⟩) := by
  conv_lhs => rw [site_eq_vadd x]
  rw [Symmetry.map_vadd, R.position_vadd]

/-- The distance between image sites depends on their cells through their difference. -/
lemma dist_position_apply (x y : C.Site) : dist (R.position (φ x)) (R.position (φ y)) =
    ‖R.vector (φ.lattice (x.cell - y.cell)) +
      (R.position (φ ⟨0, x.label⟩) - R.position (φ ⟨0, y.label⟩))‖ := by
  rw [dist_eq_norm, R.position_apply (φ := φ) x, R.position_apply (φ := φ) y, map_sub, map_sub]
  congr 1
  abel

/-! ## B. The criterion in coordinates -/

/-- A symmetry is an isometry exactly when it preserves the length of the vector from `(0, j)` to
`(d, i)` for every lattice step `d` and pair of labels `i`, `j`. -/
lemma mem_isometries_iff_components : φ ∈ R.isometries ↔ ∀ (i j : C.UnitCell) (d : G),
    ‖R.vector (φ.lattice d) + (R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩))‖ =
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
lemma norm_position_sub (hφ : φ ∈ R.isometries) (i j : C.UnitCell) :
    ‖R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)‖ = ‖R.basis i - R.basis j‖ := by
  simpa [Embedding.position] using R.mem_isometries_iff_components.1 hφ i j 0

/-- The difference between the image positions of two labels for the symmetry with lattice
automorphism `A`, label permutation `σ` and offsets `b`. -/
lemma position_sub_ofComponents (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) (b : C.UnitCell → G)
    (i j : C.UnitCell) :
    R.position (Symmetry.ofComponents C A σ b ⟨0, i⟩) -
      R.position (Symmetry.ofComponents C A σ b ⟨0, j⟩) =
        (R.vector (b i) + R.basis (σ i)) - (R.vector (b j) + R.basis (σ j)) := by
  simp [Embedding.position]

end Embedding

end Physlib.CondensedMatter.Crystal
