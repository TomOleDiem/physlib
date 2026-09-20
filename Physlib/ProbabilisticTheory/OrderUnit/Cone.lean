/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Topology.Order.OrderClosed
public import Physlib.ProbabilisticTheory.OrderUnit.Basic

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
- `PosCone.isClosed` : the positive cone is closed whenever the order itself is topologically
  closed.
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
abbrev PosCone (E : Type*) [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E]
    [Module ℝ E] [PosSMulMono ℝ E] : PointedCone ℝ E :=
  PointedCone.positive ℝ E

namespace PosCone

variable {E : Type*} [AddCommMonoid E] [PartialOrder E] [IsOrderedAddMonoid E]
  [Module ℝ E] [PosSMulMono ℝ E]

/-- The positive cone carries a nonnegative-real scalar action. -/
instance instModule : Module ℝ≥0 (PosCone E) :=
  inferInstanceAs (Module {c : ℝ // 0 ≤ c} (PointedCone.positive ℝ E))

omit [Module ℝ E] [PosSMulMono ℝ E] in
/-- A nonnegative vector that adds with another nonnegative vector to `0` is itself `0`: the
positive cone meets its negation only at `0`. -/
lemma nonneg_add_eq_zero {A B : E} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A + B = 0) : A = 0 :=
  le_antisymm (hAB ▸ le_add_of_nonneg_right hB) hA

/-!

## B. Topological closedness

-/

variable [TopologicalSpace E] [ClosedIciTopology E]

/-- The positive cone is closed whenever the order itself is closed in the topology. -/
lemma isClosed : IsClosed (PosCone E : Set E) := by
  simpa [PosCone, PointedCone.mem_positive] using (isClosed_Ici : IsClosed (Set.Ici (0 : E)))

/-!

## C. The order unit

-/

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [One E] [IsOrderUnit E]

/-- The order unit, as a point of the positive cone. -/
def unit : PosCone E := ⟨1, IsOrderUnit.one_nonneg⟩

@[simp]
lemma coe_unit : ((unit : PosCone E) : E) = (1 : E) := rfl

omit [PosSMulMono ℝ E] in
/-- Every element becomes nonnegative after adding enough copies of the order unit: the positive
cone reaches everywhere, once you're allowed to shift by the unit. -/
lemma exists_real_shift_nonneg (A : E) : ∃ r : ℝ, 0 ≤ r • (1 : E) + A := by
  obtain ⟨n, hn⟩ := IsOrderUnit.exists_nsmul_one_le (-A)
  refine ⟨n, ?_⟩
  rw [← Nat.cast_smul_eq_nsmul ℝ n (1 : E)] at hn
  rw [← sub_neg_eq_add]
  exact sub_nonneg.mpr hn

end PosCone
