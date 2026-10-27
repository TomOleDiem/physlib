/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.EmbeddingSpaceGroup
public import Physlib.CondensedMatter.Crystal.Symmetry.IsometriesGenerators
public import Physlib.Mathematics.InnerProductSpace.GramIsometry

/-!
# Distance-preserving symmetries as elements of the space group

A distance-preserving symmetry of a space-filling embedded crystal is the restriction of an
element of its space group.

## i. Overview

A distance-preserving symmetry of an embedded crystal whose translation vectors span space is
induced by a rigid motion of space. The symmetry preserves the lengths and mutual angles of the
translation vectors, so there is a linear isometry of space that agrees with its lattice
automorphism on them. This isometry carries the differences of the label positions to their images,
so it moves the label positions of the symmetry up to a single common translation. The linear
isometry followed by this translation is an affine isometry that extends the symmetry, and it maps
the sites onto sites.

Together with `Crystal.Symmetry.FromSpaceGroup`, a symmetry of the crystal preserves distances
exactly when it is induced by an element of the space group.

## ii. Key results

- `Crystal.Embedding.exists_affineIsometryEquiv` : a distance-preserving symmetry is the
  restriction of an affine isometry of space.
- `Crystal.Embedding.exists_mem_spaceGroup` : this affine isometry is in the space group.
- `Crystal.Embedding.mem_isometries_iff_exists` : a symmetry preserves distances exactly when it
  is the restriction of an element of the space group.

## iii. Table of contents

- A. The linear isometry and the constant
- B. The affine isometry

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

open RealInnerProductSpace

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (R : Embedding C E) {φ : Symmetry C} {L : E ≃ₗᵢ[ℝ] E}

/-! ## A. The linear isometry and the constant -/

/-- A linear isometry that agrees with a distance-preserving symmetry on the translation vectors
carries the inner products with the images of the translation vectors to those with the vectors,
on all of space. -/
lemma inner_linear_eq (hR : R.IsSpaceFilling) (hL : ∀ a, L (R.vector a) = R.vector (φ.lattice a))
    {P Q : E} (h : ∀ d, ⟪R.vector (φ.lattice d), P⟫ = ⟪R.vector d, Q⟫) (x : E) :
    ⟪L x, P⟫ = ⟪x, Q⟫ := by
  have hext : (innerSL ℝ P).toLinearMap ∘ₗ L.toLinearMap = (innerSL ℝ Q).toLinearMap := by
    refine LinearMap.ext_on hR ?_
    rintro _ ⟨d, rfl⟩
    simpa [real_inner_comm, hL] using h d
  simpa [real_inner_comm] using LinearMap.congr_fun hext x

/-- A linear isometry that agrees with a distance-preserving symmetry on the translation vectors
carries the differences of the label positions to their images. -/
lemma position_sub_eq_linear (hR : R.IsSpaceFilling) (hφ : φ ∈ R.isometries)
    (hL : ∀ a, L (R.vector a) = R.vector (φ.lattice a)) (i j : C.UnitCell) :
    R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩) = L (R.basis i - R.basis j) := by
  set z := R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩) - L (R.basis i - R.basis j)
  have h0 := R.inner_linear_eq hR hL (R.inner_lattice_position hφ i j) (L.symm z)
  have h1 := L.inner_map_map (L.symm z) (R.basis i - R.basis j)
  rw [L.apply_symm_apply] at h0 h1
  rw [← sub_eq_zero]
  refine (inner_self_eq_zero (𝕜 := ℝ)).1 ?_
  rw [inner_sub_right z, h0, h1, sub_self]

/-- The label positions of a distance-preserving symmetry are the images under a linear isometry,
up to a common constant. -/
lemma exists_position_const (hR : R.IsSpaceFilling) (hφ : φ ∈ R.isometries)
    (hL : ∀ a, L (R.vector a) = R.vector (φ.lattice a)) :
    ∃ t : E, ∀ i, R.position (φ ⟨0, i⟩) = L (R.basis i) + t := by
  refine ⟨R.position (φ ⟨0, Classical.arbitrary _⟩) - L (R.basis (Classical.arbitrary _)), ?_⟩
  intro i
  have := R.position_sub_eq_linear hR hφ hL i (Classical.arbitrary _)
  rw [map_sub, sub_eq_iff_eq_add] at this
  rw [this]
  abel

/-! ## B. The affine isometry -/

/-- A distance-preserving symmetry of a space-filling embedding is the restriction of an affine
isometry of space. -/
lemma exists_affineIsometryEquiv (hR : R.IsSpaceFilling) (hφ : φ ∈ R.isometries) :
    ∃ ψ : E ≃ᵃⁱ[ℝ] E, ∀ x, ψ (R.position x) = R.position (φ x) := by
  have := hR.finiteDimensional
  obtain ⟨L, hL⟩ := GramIsometry.exists_linearIsometryEquiv (u := R.vector)
    (w := fun d => R.vector (φ.lattice d)) hR
    (R.inner_vector_lattice_of_norm (R.norm_vector_lattice hφ))
  obtain ⟨t, ht⟩ := R.exists_position_const hR hφ hL
  refine ⟨L.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ E t), ?_⟩
  intro x
  show t + L (R.position x) = R.position (φ x)
  rw [R.position_apply (φ := φ) x, ht x.label, show R.position x = R.vector x.cell + R.basis x.label
    from rfl, map_add, hL]
  abel

/-- A distance-preserving symmetry of a space-filling embedding is the restriction of an element of
the space group. -/
lemma exists_mem_spaceGroup (hR : R.IsSpaceFilling) (hφ : φ ∈ R.isometries) :
    ∃ ψ ∈ R.spaceGroup, ∀ x, ψ (R.position x) = R.position (φ x) := by
  obtain ⟨ψ, h⟩ := R.exists_affineIsometryEquiv hR hφ
  refine ⟨ψ, ?_, h⟩
  rw [mem_spaceGroup_iff, ← Set.range_comp, show ψ ∘ R.position = R.position ∘ φ from funext h,
    Set.range_comp, show Set.range ⇑φ = Set.univ from φ.bijective.surjective.range_eq,
    Set.image_univ]

/-- **A symmetry preserves distances exactly when it is the restriction of an element of the space
group.** -/
lemma mem_isometries_iff_exists (hR : R.IsSpaceFilling) :
    φ ∈ R.isometries ↔ ∃ ψ ∈ R.spaceGroup, ∀ x, ψ (R.position x) = R.position (φ x) := by
  constructor
  · intro hφ
    exact R.exists_mem_spaceGroup hR hφ
  · rintro ⟨ψ, -, h⟩ x y
    rw [← h x, ← h y]
    exact ψ.dist_map _ _

end Embedding

end Physlib.CondensedMatter.Crystal
