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

The symmetries of a crystal that preserve the distances between its sites in space.

## i. Overview

An embedding places every site of a crystal at a point of a normed group. A symmetry of the
crystal is an isometry if it preserves the distance between the positions of any two sites,

`dist (position (φ x)) (position (φ y)) = dist (position x) (position y)`.

These symmetries are a subgroup of the symmetries of the crystal. It contains the translations,
which move both sites by the same vector, and it is independent of the bonds and of the species.

A symmetry moves a site `(n, i)` to the translate of the image of `(0, i)` by the image of `n`.
Hence the distance between two image sites depends on the cells only through their difference
`d`, and being an isometry is a condition on pairs of labels `(i, j)` and lattice steps `d`. In an
inner product space the condition is linear in `d` once the lengths are preserved, so it only has
to be checked on a finite generating set of the translation group and on the finitely many pairs
of labels.

## ii. Key results

- `Crystal.Embedding.isometries` : the symmetries that preserve the distances between positions.
- `Crystal.Embedding.translations_le_isometries` : translations are isometries.
- `Crystal.Embedding.mem_isometries_iff_components` : a symmetry is an isometry exactly when a
  condition on pairs of labels and lattice steps holds.
- `Crystal.Embedding.norm_vector_lattice` : an isometry preserves the lengths of the translation
  vectors.
- `Crystal.Embedding.mem_isometries_iff_generators` : in an inner product space, finitely many
  conditions on a generating set and on the labels suffice.
- `Crystal.Embedding.imageSub_ofComponents` : the label position differences of the symmetry with
  given lattice automorphism, label permutation and offsets, to which the finite check applies.

## iii. Table of contents

- A. Isometries
- B. Coordinates of the image sites
- C. Finite check in an inner product space

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

/-! ## B. Coordinates of the image sites -/

/-- The distance between the positions of two sites, in terms of their cells and labels. -/
lemma dist_position (x y : C.Site) : dist (R.position x) (R.position y) =
    ‖R.vector (x.cell - y.cell) + R.basis x.label - R.basis y.label‖ := by
  rw [dist_eq_norm, Embedding.position, Embedding.position, map_sub]
  congr 1
  abel

/-- A symmetry moves the position of a site by the vector of the image of its cell, starting from
the position of the image of the same label in the reference cell. -/
lemma position_apply (x : C.Site) : R.position (φ x) =
    R.vector (φ.lattice x.cell) + R.position (φ ⟨0, x.label⟩) := by
  conv_lhs => rw [show x = x.cell +ᵥ (⟨0, x.label⟩ : C.Site) from Site.ext (by simp) rfl]
  rw [Symmetry.map_vadd, R.position_vadd]

/-- The distance between two image sites depends on their cells only through the difference. -/
lemma dist_position_apply (x y : C.Site) : dist (R.position (φ x)) (R.position (φ y)) =
    ‖R.vector (φ.lattice (x.cell - y.cell)) + R.position (φ ⟨0, x.label⟩) -
      R.position (φ ⟨0, y.label⟩)‖ := by
  rw [dist_eq_norm, R.position_apply (φ := φ) x, R.position_apply (φ := φ) y, map_sub, map_sub]
  congr 1
  abel

/-- A symmetry is an isometry exactly when, for every pair of labels `i`, `j` and every lattice
step `d`, the distance between the images of `(d, i)` and `(0, j)` is unchanged. -/
lemma mem_isometries_iff_components : φ ∈ R.isometries ↔ ∀ (i j : C.UnitCell) (d : G),
    ‖R.vector (φ.lattice d) + R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)‖ =
      ‖R.vector d + R.basis i - R.basis j‖ := by
  refine ⟨fun h i j d => ?_, fun h x y => ?_⟩
  · have := h ⟨d, i⟩ ⟨0, j⟩
    rw [dist_position_apply, dist_position] at this
    simpa only [sub_zero] using this
  · rw [dist_position_apply, dist_position]
    exact h _ _ _

/-- An isometry preserves the lengths of the translation vectors. -/
lemma norm_vector_lattice (hφ : φ ∈ R.isometries) (a : G) :
    ‖R.vector (φ.lattice a)‖ = ‖R.vector a‖ := by
  simpa using R.mem_isometries_iff_components.1 hφ (Classical.arbitrary C.UnitCell)
    (Classical.arbitrary C.UnitCell) a

/-- The difference of the positions of the images of two labels. -/
abbrev imageSub (φ : Symmetry C) (i j : C.UnitCell) : E :=
  R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)

/-- The difference of the positions of two labels. -/
abbrev basisSub (i j : C.UnitCell) : E := R.basis i - R.basis j

/-- An isometry preserves the distances between the positions of the labels. -/
lemma norm_imageSub (hφ : φ ∈ R.isometries) (i j : C.UnitCell) :
    ‖R.imageSub φ i j‖ = ‖R.basisSub i j‖ := by
  simpa [imageSub, basisSub, Embedding.position] using R.mem_isometries_iff_components.1 hφ i j 0

/-! ## C. Finite check in an inner product space -/

section InnerProduct

variable [InnerProductSpace ℝ E]

open RealInnerProductSpace

/-- The lattice automorphism `A` preserves the inner products of the vectors of the steps in `S`. -/
def InnerEqOn (S : Set G) (A : G ≃+ G) : Prop :=
  ∀ s ∈ S, ∀ s' ∈ S, ⟪R.vector (A s), R.vector (A s')⟫ = ⟪R.vector s, R.vector s'⟫

/-- A lattice automorphism that preserves the lengths of the translation vectors preserves their
inner products. -/
lemma inner_vector_lattice_of_norm {A : G ≃+ G} (h : ∀ d, ‖R.vector (A d)‖ = ‖R.vector d‖)
    (d d' : G) : ⟪R.vector (A d), R.vector (A d')⟫ = ⟪R.vector d, R.vector d'⟫ := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (R.vector d),
    ← map_add, ← map_add, h, h, h, map_add]

/-- The inner products of the translation vectors are preserved by a lattice automorphism as soon
as they are preserved on a generating set. -/
lemma inner_vector_lattice_of_generators {S : Set G} (hS : AddSubgroup.closure S = ⊤)
    {A : G ≃+ G} (h : R.InnerEqOn S A) (d d' : G) :
    ⟪R.vector (A d), R.vector (A d')⟫ = ⟪R.vector d, R.vector d'⟫ := by
  refine AddSubgroup.closure_induction₂ (p := fun d d' _ _ =>
    ⟪R.vector (A d), R.vector (A d')⟫ = ⟪R.vector d, R.vector d'⟫)
    (fun x y hx hy => h x hx y hy) (fun _ _ => by simp) (fun _ _ => by simp)
    (fun _ _ _ _ _ _ h₁ h₂ => by simp [inner_add_left, h₁, h₂])
    (fun _ _ _ _ _ _ h₁ h₂ => by simp [inner_add_right, h₁, h₂])
    (fun _ _ _ _ h => by simp [inner_neg_left, h]) (fun _ _ _ _ h => by simp [inner_neg_right, h])
    (hS ▸ AddSubgroup.mem_top d) (hS ▸ AddSubgroup.mem_top d')

/-- A lattice automorphism that preserves the inner products on a generating set preserves the
lengths of all translation vectors. -/
lemma norm_vector_lattice_of_generators {S : Set G} (hS : AddSubgroup.closure S = ⊤)
    {A : G ≃+ G} (h : R.InnerEqOn S A) (d : G) : ‖R.vector (A d)‖ = ‖R.vector d‖ := by
  have := R.inner_vector_lattice_of_generators hS h d d
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

/-- An isometry preserves the inner products of the translation vectors with the differences of
the positions of the labels. -/
lemma inner_lattice_position (hφ : φ ∈ R.isometries) (i j : C.UnitCell) (d : G) :
    ⟪R.vector (φ.lattice d), R.imageSub φ i j⟫ = ⟪R.vector d, R.basisSub i j⟫ := by
  have := congrArg (· ^ 2) (R.mem_isometries_iff_components.1 hφ i j d)
  simp only [add_sub_assoc, norm_add_sq_real, R.norm_vector_lattice hφ, R.norm_imageSub hφ] at this
  simpa [imageSub, basisSub, Embedding.position] using this

/-- The inner products of the translation vectors with fixed vectors are preserved as soon as they
are preserved on a generating set. -/
lemma inner_vector_lattice_of_generators_vec {S : Set G} (hS : AddSubgroup.closure S = ⊤)
    (A : G ≃+ G) {P Q : E} (h : ∀ s ∈ S, ⟪R.vector (A s), P⟫ = ⟪R.vector s, Q⟫) (d : G) :
    ⟪R.vector (A d), P⟫ = ⟪R.vector d, Q⟫ := by
  refine AddSubgroup.closure_induction (p := fun d _ => ⟪R.vector (A d), P⟫ = ⟪R.vector d, Q⟫)
    h (by simp) (fun _ _ _ _ h₁ h₂ => by simp [inner_add_left, h₁, h₂])
    (fun _ _ h => by simp [inner_neg_left, h]) (hS ▸ AddSubgroup.mem_top d)

/-- **Finite check for an isometry.** In an inner product space, a symmetry is an isometry exactly
when its lattice automorphism preserves the inner products on a generating set, and the
differences of the label positions have the right lengths and inner products with the generators.
Only finitely many conditions have to be checked. -/
lemma mem_isometries_iff_generators {S : Set G} (hS : AddSubgroup.closure S = ⊤) :
    φ ∈ R.isometries ↔ R.InnerEqOn S φ.lattice ∧ (∀ i j, ‖R.imageSub φ i j‖ = ‖R.basisSub i j‖) ∧
      ∀ i j, ∀ s ∈ S, ⟪R.vector (φ.lattice s), R.imageSub φ i j⟫ =
        ⟪R.vector s, R.basisSub i j⟫ := by
  refine ⟨fun h => ⟨fun s _ s' _ => R.inner_vector_lattice_of_norm (R.norm_vector_lattice h) s s',
    R.norm_imageSub h, fun i j s _ => R.inner_lattice_position h i j s⟩, ?_⟩
  rintro ⟨h₁, h₂, h₃⟩
  rw [mem_isometries_iff_components]
  intro i j d
  rw [add_sub_assoc, add_sub_assoc]
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_add_sq_real, norm_add_sq_real, R.norm_vector_lattice_of_generators hS h₁, h₂ i j,
    R.inner_vector_lattice_of_generators_vec hS φ.lattice (h₃ i j) d]

end InnerProduct

/-- The label position differences of the symmetry with lattice automorphism `A`, label
permutation `σ` and offsets `b`. -/
lemma imageSub_ofComponents (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) (b : C.UnitCell → G)
    (i j : C.UnitCell) : R.imageSub (Symmetry.ofComponents C A σ b) i j =
      (R.vector (b i) + R.basis (σ i)) - (R.vector (b j) + R.basis (σ j)) := by
  simp [imageSub, Embedding.position]

end Embedding

end Physlib.CondensedMatter.Crystal
