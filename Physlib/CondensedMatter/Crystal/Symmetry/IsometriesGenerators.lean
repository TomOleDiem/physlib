/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.IsometriesCoordinates
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Checking isometries on generators

In an inner product space, a symmetry of an embedded crystal is an isometry as soon as it is
checked on generators of the translation group and on the labels.

## i. Overview

The condition that a symmetry of an embedded crystal preserves distances quantifies over all pairs of
sites. Periodicity reduces it to finitely many conditions. In an inner product space, a symmetry
with lattice automorphism `A` is an isometry exactly when `A` preserves the inner products of the
translation vectors of a generating set of the translation group, the differences of the images of
the label positions have the lengths of the differences of the labels, and their inner products
with the generators agree. The proof squares the length condition of the coordinate criterion,
which is additive in the lattice step once the lengths of the translation vectors are preserved.
For a symmetry given by its lattice automorphism, label permutation and offsets, being an isometry
is therefore a finite computation.

## ii. Key results

- `Crystal.Embedding.InnerEqOn` : a lattice automorphism preserves the inner products of the
  translation vectors of a set of steps.
- `Crystal.Embedding.GeneratorCheck` : three conditions on a generating set and on the labels.
- `Crystal.Embedding.mem_isometries_iff_generators` : a symmetry is an isometry exactly when it
  satisfies the check on generators.

## iii. Table of contents

- A. Inner products of the translation vectors
- B. The check on generators

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

open RealInnerProductSpace

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (R : Embedding C E) {φ : Symmetry C}

/-! ## A. Inner products of the translation vectors -/

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

/-- The inner products of the translation vectors with fixed vectors are preserved as soon as they
are preserved on a generating set. -/
lemma inner_vector_lattice_of_generators_vec {S : Set G} (hS : AddSubgroup.closure S = ⊤)
    (A : G ≃+ G) {P Q : E} (h : ∀ s ∈ S, ⟪R.vector (A s), P⟫ = ⟪R.vector s, Q⟫) (d : G) :
    ⟪R.vector (A d), P⟫ = ⟪R.vector d, Q⟫ := by
  have hd : d ∈ AddSubgroup.closure S := by
    rw [hS]
    exact AddSubgroup.mem_top d
  induction hd using AddSubgroup.closure_induction with
  | mem s hs => exact h s hs
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
  | neg x _ hx => simp [inner_neg_left, hx]

/-- The inner products of the translation vectors are preserved by a lattice automorphism as soon
as they are preserved on a generating set. -/
lemma inner_vector_lattice_of_generators {S : Set G} (hS : AddSubgroup.closure S = ⊤)
    {A : G ≃+ G} (h : R.InnerEqOn S A) (d d' : G) :
    ⟪R.vector (A d), R.vector (A d')⟫ = ⟪R.vector d, R.vector d'⟫ := by
  refine R.inner_vector_lattice_of_generators_vec hS A ?_ d
  intro s hs
  rw [real_inner_comm (R.vector (A d')) (R.vector (A s)),
    real_inner_comm (R.vector d') (R.vector s)]
  refine R.inner_vector_lattice_of_generators_vec hS A ?_ d'
  intro t ht
  exact h t ht s hs

/-- A lattice automorphism that preserves the inner products on a generating set preserves the
lengths of all translation vectors. -/
lemma norm_vector_lattice_of_generators {S : Set G} (hS : AddSubgroup.closure S = ⊤)
    {A : G ≃+ G} (h : R.InnerEqOn S A) (d : G) : ‖R.vector (A d)‖ = ‖R.vector d‖ := by
  have := R.inner_vector_lattice_of_generators hS h d d
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

/-! ## B. The check on generators -/

/-- An isometry preserves the inner products of the translation vectors with the differences of
the positions of the labels. -/
lemma inner_lattice_position (hφ : φ ∈ R.isometries) (i j : C.UnitCell) (d : G) :
    ⟪R.vector (φ.lattice d), R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)⟫ =
      ⟪R.vector d, R.basis i - R.basis j⟫ := by
  have := congrArg (· ^ 2) (R.mem_isometries_iff_components.1 hφ i j d)
  simp only [norm_add_sq_real, R.norm_vector_lattice hφ, R.norm_position_sub hφ] at this
  simpa using this

/-- The conditions on generators and labels that characterise the isometries: the lattice
automorphism preserves the inner products on the generators, and the differences of the label
positions have the right lengths and inner products with the generators. -/
def GeneratorCheck (S : Set G) (φ : Symmetry C) : Prop :=
  R.InnerEqOn S φ.lattice ∧
    (∀ i j, ‖R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)‖ = ‖R.basis i - R.basis j‖) ∧
    ∀ i j, ∀ s ∈ S, ⟪R.vector (φ.lattice s), R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)⟫ =
      ⟪R.vector s, R.basis i - R.basis j⟫

/-- An isometry satisfies the check on generators. -/
lemma generatorCheck_of_mem (S : Set G) (h : φ ∈ R.isometries) : R.GeneratorCheck S φ := by
  refine ⟨?_, R.norm_position_sub h, ?_⟩
  · intro s _ s' _
    exact R.inner_vector_lattice_of_norm (R.norm_vector_lattice h) s s'
  · intro i j s _
    exact R.inner_lattice_position h i j s

/-- A symmetry that satisfies the check on generators is an isometry. -/
lemma mem_of_generatorCheck {S : Set G} (hS : AddSubgroup.closure S = ⊤)
    (h : R.GeneratorCheck S φ) : φ ∈ R.isometries := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  rw [mem_isometries_iff_components]
  intro i j d
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_add_sq_real, norm_add_sq_real, R.norm_vector_lattice_of_generators hS h₁, h₂ i j,
    R.inner_vector_lattice_of_generators_vec hS φ.lattice (h₃ i j) d]

/-- **A symmetry is an isometry exactly when it satisfies the check on generators.** -/
lemma mem_isometries_iff_generators {S : Set G} (hS : AddSubgroup.closure S = ⊤) :
    φ ∈ R.isometries ↔ R.GeneratorCheck S φ :=
  ⟨R.generatorCheck_of_mem S, R.mem_of_generatorCheck hS⟩

end Embedding

end Physlib.CondensedMatter.Crystal
