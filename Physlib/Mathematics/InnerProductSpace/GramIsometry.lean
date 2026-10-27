/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Isomorphisms

/-!

# Linear isometries from equal inner products

Two families of vectors that span a finite-dimensional real inner product space and have the same
inner products differ by a linear isometry of the space.

## i. Overview

Two lists of vectors that have the same lengths and the same angles between them can be moved
into one another by a rotation or reflection. If the first list spans the space, the rotation or
reflection is unique and is defined on the whole space.

Here this is made precise for families `u` and `w` with the same inner products. Linear
combinations of `w` vanish wherever the same combination of `u` vanishes, so `u a ↦ w a` extends to
a linear map. This map preserves inner products, and a linear map of a finite-dimensional space
that preserves inner products is a linear isometry equivalence.

## ii. Key results

- `GramIsometry.exists_linearIsometryEquiv` : families with the same inner products, one of them
  spanning, differ by a linear isometry.

## iii. Table of contents

- A. Linear combinations
- B. The linear isometry

## iv. References

* None.

-/

@[expose] public section

namespace GramIsometry

open RealInnerProductSpace

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u w : ι → E}

/-! ## A. Linear combinations -/

/-- Linear combinations of families with the same inner products have the same inner products. -/
lemma inner_linearCombination_eq (h : ∀ a b, ⟪w a, w b⟫ = ⟪u a, u b⟫) (c c' : ι →₀ ℝ) :
    ⟪Finsupp.linearCombination ℝ w c, Finsupp.linearCombination ℝ w c'⟫ =
      ⟪Finsupp.linearCombination ℝ u c, Finsupp.linearCombination ℝ u c'⟫ := by
  simp [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
    real_inner_smul_left, real_inner_smul_right, h]

/-- A linear combination of `w` vanishes when the same combination of `u` does. -/
lemma linearCombination_eq_zero (h : ∀ a b, ⟪w a, w b⟫ = ⟪u a, u b⟫) {c : ι →₀ ℝ}
    (hc : Finsupp.linearCombination ℝ u c = 0) : Finsupp.linearCombination ℝ w c = 0 := by
  have := inner_linearCombination_eq h c c
  rwa [hc, inner_zero_left, inner_self_eq_zero] at this

/-- The linear combinations of a spanning family reach every vector. -/
lemma linearCombination_surjective (hu : Submodule.span ℝ (Set.range u) = ⊤) :
    Function.Surjective (Finsupp.linearCombination ℝ u) := by
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  exact hu

/-- A linear map carries the linear combinations of `u` to those of `w`. -/
lemma exists_linearMap_comp (hu : Submodule.span ℝ (Set.range u) = ⊤)
    (h : ∀ a b, ⟪w a, w b⟫ = ⟪u a, u b⟫) : ∃ T : E →ₗ[ℝ] E,
      ∀ c, T (Finsupp.linearCombination ℝ u c) = Finsupp.linearCombination ℝ w c := by
  have hker : LinearMap.ker (Finsupp.linearCombination ℝ u) ≤
      LinearMap.ker (Finsupp.linearCombination ℝ w) := by
    intro c hc
    exact linearCombination_eq_zero h hc
  refine ⟨(Finsupp.linearCombination ℝ u).liftOfSurjective (linearCombination_surjective hu)
    ⟨_, hker⟩, ?_⟩
  intro c
  exact LinearMap.equivOfSurjective_apply (linearCombination_surjective hu) hker

/-! ## B. The linear isometry -/

/-- A linear map from spanning combinations that preserves inner products. -/
lemma inner_map_eq (hu : Submodule.span ℝ (Set.range u) = ⊤) (h : ∀ a b, ⟪w a, w b⟫ = ⟪u a, u b⟫)
    {T : E →ₗ[ℝ] E} (hT : ∀ c, T (Finsupp.linearCombination ℝ u c) =
      Finsupp.linearCombination ℝ w c) (x y : E) : ⟪T x, T y⟫ = ⟪x, y⟫ := by
  obtain ⟨c, rfl⟩ := linearCombination_surjective hu x
  obtain ⟨c', rfl⟩ := linearCombination_surjective hu y
  rw [hT, hT, inner_linearCombination_eq h]

/-- **Two spanning families with the same inner products differ by a linear isometry.** -/
lemma exists_linearIsometryEquiv [FiniteDimensional ℝ E] (hu : Submodule.span ℝ (Set.range u) = ⊤)
    (h : ∀ a b, ⟪w a, w b⟫ = ⟪u a, u b⟫) : ∃ L : E ≃ₗᵢ[ℝ] E, ∀ a, L (u a) = w a := by
  obtain ⟨T, hT⟩ := exists_linearMap_comp hu h
  refine ⟨(T.isometryOfInner (inner_map_eq hu h hT)).toLinearIsometryEquiv rfl, ?_⟩
  intro a
  simpa using hT (Finsupp.single a 1)

end GramIsometry
