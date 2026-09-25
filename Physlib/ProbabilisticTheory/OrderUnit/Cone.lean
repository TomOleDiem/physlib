/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.NNReal.Defs
public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean

/-!
# Ordered positive cones

## i. Overview

`PosCone E` collects the positive elements of `E`. In quantum mechanics, `E` is the real vector
space of self-adjoint matrices, whose spectra are real. Its positive cone consists exactly of
those matrices whose spectra are nonnegative.
These elements form a cone: they are closed under addition and scaling by nonnegative reals.

## ii. Key results

- `PosCone` : the cone of positive observables, `PointedCone.positive ℝ E`. Its carrier is exactly
  `{A | 0 ≤ A}` (`PointedCone.mem_positive`) and it is convex (`PointedCone.convex`).
- `PosCone.isClosed` : the positive cone is closed in the order-unit-norm topology of an
  Archimedean order-unit space.
- `PosCone.nonneg_add_eq_zero` : the positive cone meets its negation only at `0`.
- `PosCone.exists_real_shift_nonneg` : enough copies of the order unit shift any element into the
  cone.

## iii. Table of contents

- A. The positive cone
- B. Topological closedness
- C. The order unit

-/

@[expose] public section

open scoped NNReal

/-!

## A. The positive cone

-/

/-- The positive pointed cone of an ordered real module. -/
abbrev PosCone (E : Type*) [OrderedVectorSpace E] : PointedCone ℝ E :=
  PointedCone.positive ℝ E

namespace PosCone

section OrderedVectorSpace

variable {E : Type*} [OrderedVectorSpace E]

/-- The positive cone carries a nonnegative-real scalar action. -/
instance instModule : Module ℝ≥0 (PosCone E) :=
  inferInstanceAs (Module {c : ℝ // 0 ≤ c} (PointedCone.positive ℝ E))

/-- A nonnegative vector that adds with another nonnegative vector to `0` is itself `0`: the
positive cone meets its negation only at `0`. -/
lemma nonneg_add_eq_zero {A B : E} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A + B = 0) : A = 0 :=
  le_antisymm (hAB ▸ le_add_of_nonneg_right hB) hA

end OrderedVectorSpace

/-!

## B. Topological closedness

-/

section ArchimedeanOrderUnitSpace

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-- The positive cone is closed in the topology induced by the order-unit norm. -/
lemma isClosed : IsClosed (PosCone E : Set E) := ArchimedeanOrderUnitSpace.isClosed_Ici_zero

end ArchimedeanOrderUnitSpace

/-!

## C. The order unit

-/

section OrderUnitSpace

variable {E : Type*} [OrderUnitSpace E]

/-- The order unit, regarded as a point of the positive cone. -/
instance instOne : One (PosCone E) := ⟨⟨1, OrderUnitSpace.one_nonneg⟩⟩

@[simp]
lemma coe_one : ((1 : PosCone E) : E) = (1 : E) := rfl

/-- Every element becomes nonnegative after adding enough copies of the order unit: the positive
cone reaches everywhere, once you're allowed to shift by the unit. -/
lemma exists_real_shift_nonneg (A : E) : ∃ r : ℝ, 0 ≤ r • (1 : E) + A := by
  obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le (-A)
  use n
  rw [← sub_neg_eq_add, sub_nonneg]
  exact_mod_cast hn

end OrderUnitSpace

end PosCone
