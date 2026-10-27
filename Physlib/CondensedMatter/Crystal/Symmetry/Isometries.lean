/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding
public import Physlib.CondensedMatter.Crystal.Symmetry.PointOperations
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.InnerProductSpace.Basic

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
- `Embedding.mem_isometries_iff_generators`: In an inner product space, an isometry is
  characterized by finitely many conditions on generators and labels.
- `Embedding.ofComponents_mem_isometries_iff`: The same check for the symmetry with given
  lattice automorphism, label permutation and offsets.
- `Embedding.mem_isometries_iff_referenceCell`: A symmetry is an isometry exactly when it
  preserves the distances from the sites of the reference cell.

## iii. Table of contents

- A. Distance-preserving symmetries
- B. Lengths of the translation vectors
- C. Coordinates of an isometry
- D. Checking on the reference cell
- E. Finite check in an inner product space

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

/-- The position of the image of a reference-cell site is the vector of the offset plus the
position of the permuted label. -/
lemma position_reference (i : C.UnitCell) :
    R.position (φ ⟨0, i⟩) = R.vector (φ.offset i) + R.basis (Symmetry.labelHom C φ i) := rfl

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

/-- An isometry preserves the lengths of the differences of the positions of the labels. -/
lemma norm_position_sub (hφ : φ ∈ R.isometries) (i j : C.UnitCell) :
    ‖R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)‖ = ‖R.basis i - R.basis j‖ := by
  simpa [Embedding.position] using R.mem_isometries_iff_components.1 hφ i j 0

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

/-! ## E. Finite check in an inner product space -/

section InnerProduct

variable [InnerProductSpace ℝ E]

/-- A lattice automorphism that preserves the lengths of the translation vectors preserves their
inner products. -/
lemma inner_vector_lattice_of_norm {A : G ≃+ G} (h : ∀ d, ‖R.vector (A d)‖ = ‖R.vector d‖)
    (d d' : G) :
    inner ℝ (R.vector (A d)) (R.vector (A d')) = inner ℝ (R.vector d) (R.vector d') := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (R.vector d),
    ← map_add, ← map_add, h, h, h, map_add]

/-- The inner products of the translation vectors are preserved on all lattice steps as soon as
they are preserved on a generating set. -/
lemma inner_vector_lattice_of_generators {S : Set G} (hS : AddSubgroup.closure S = ⊤) (A : G ≃+ G)
    (h : ∀ s ∈ S, ∀ s' ∈ S,
      inner ℝ (R.vector (A s)) (R.vector (A s')) = inner ℝ (R.vector s) (R.vector s'))
    (d d' : G) :
    inner ℝ (R.vector (A d)) (R.vector (A d')) = inner ℝ (R.vector d) (R.vector d') := by
  have hd : d ∈ AddSubgroup.closure S := hS ▸ AddSubgroup.mem_top d
  have hd' : d' ∈ AddSubgroup.closure S := hS ▸ AddSubgroup.mem_top d'
  induction hd using AddSubgroup.closure_induction with
  | mem s hs =>
    induction hd' using AddSubgroup.closure_induction with
    | mem s' hs' => exact h s hs s' hs'
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, inner_add_right, hx, hy]
    | neg x _ hx => simp [inner_neg_right, hx]
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, inner_add_left, hx, hy]
  | neg x _ hx => simp [inner_neg_left, hx]
/-- An isometry preserves the inner products of the translation vectors with the differences of
the label positions. -/
lemma inner_lattice_position (hφ : φ ∈ R.isometries) (i j : C.UnitCell) (d : G) :
    inner ℝ (R.vector (φ.lattice d)) (R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)) =
      inner ℝ (R.vector d) (R.basis i - R.basis j) := by
  have := congrArg (· ^ 2) (R.mem_isometries_iff_components.1 hφ i j d)
  simp only [add_sub_assoc, norm_add_sq_real, R.norm_vector_lattice hφ,
    R.norm_position_sub hφ] at this
  simpa [Embedding.position] using this

/-- **Finite check for an isometry.** In an inner product space, a symmetry is an isometry exactly
when it preserves the inner products of the vectors of a generating set of lattice steps, the
lengths of the differences of the label positions, and the inner products of the generator
vectors with these differences. Only finitely many conditions have to be checked. -/
lemma mem_isometries_iff_generators {S : Set G} (hS : AddSubgroup.closure S = ⊤) :
    φ ∈ R.isometries ↔
      (∀ s ∈ S, ∀ s' ∈ S, inner ℝ (R.vector (φ.lattice s)) (R.vector (φ.lattice s')) =
        inner ℝ (R.vector s) (R.vector s')) ∧
      (∀ i j, ‖R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)‖ = ‖R.basis i - R.basis j‖) ∧
      (∀ i j, ∀ s ∈ S, inner ℝ (R.vector (φ.lattice s))
        (R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)) =
          inner ℝ (R.vector s) (R.basis i - R.basis j)) := by
  refine ⟨fun h => ⟨fun s _ s' _ => R.inner_vector_lattice_of_norm (R.norm_vector_lattice h) s s',
    R.norm_position_sub h, fun i j s _ => R.inner_lattice_position h i j s⟩, ?_⟩
  rintro ⟨h₁, h₂, h₃⟩
  rw [mem_isometries_iff_components]
  intro i j d
  have hinner := R.inner_vector_lattice_of_generators hS φ.lattice h₁
  have hn : ∀ d, ‖R.vector (φ.lattice d)‖ = ‖R.vector d‖ := fun d => by
    have := hinner d d
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  have h₃' : ∀ d, inner ℝ (R.vector (φ.lattice d))
      (R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)) =
        inner ℝ (R.vector d) (R.basis i - R.basis j) := by
    intro d
    have hd : d ∈ AddSubgroup.closure S := hS ▸ AddSubgroup.mem_top d
    induction hd using AddSubgroup.closure_induction with
    | mem s hs => exact h₃ i j s hs
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, inner_add_left, hx, hy]
    | neg x _ hx => simp [inner_neg_left, hx]
  rw [add_sub_assoc, add_sub_assoc]
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_add_sq_real, norm_add_sq_real, hn, h₂ i j, h₃' d]

/-- **Finite check in components.** The symmetry with lattice automorphism `A`, label permutation
`σ` and offsets `b` is an isometry exactly when the finitely many conditions of
`mem_isometries_iff_generators` hold for `A`, `σ` and `b`. -/
lemma ofComponents_mem_isometries_iff {S : Set G} (hS : AddSubgroup.closure S = ⊤) (A : G ≃+ G)
    (σ : Equiv.Perm C.UnitCell) (b : C.UnitCell → G) :
    Symmetry.ofComponents C A σ b ∈ R.isometries ↔
      (∀ s ∈ S, ∀ s' ∈ S, inner ℝ (R.vector (A s)) (R.vector (A s')) =
        inner ℝ (R.vector s) (R.vector s')) ∧
      (∀ i j, ‖(R.vector (b i) + R.basis (σ i)) - (R.vector (b j) + R.basis (σ j))‖ =
        ‖R.basis i - R.basis j‖) ∧
      (∀ i j, ∀ s ∈ S, inner ℝ (R.vector (A s))
        ((R.vector (b i) + R.basis (σ i)) - (R.vector (b j) + R.basis (σ j))) =
          inner ℝ (R.vector s) (R.basis i - R.basis j)) := by
  rw [R.mem_isometries_iff_generators hS]
  simp only [R.position_reference, Symmetry.lattice_ofComponents, Symmetry.offset_ofComponents,
    Symmetry.labelHom_ofComponents]

end InnerProduct

end Embedding

end Physlib.CondensedMatter.Crystal
