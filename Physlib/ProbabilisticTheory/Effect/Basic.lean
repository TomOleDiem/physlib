/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Order.Interval.Set.Defs
public import Physlib.ProbabilisticTheory.OrderUnit.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Cone

/-!
# Effects

## i. Overview

An effect models a yes/no measurement outcome, ranging continuously between the impossible
outcome `0` and the certain outcome `1`. Formally, it is a point of the order interval `[0, 1]`
inside `E`. For self-adjoint matrices, effects are exactly the operators `0 ≤ M ≤ 1` — the
elements of a POVM.

## ii. Key results

- `Effect` : a bounded measurement outcome, the order interval `[0, 1]`.
- `Effect.mem_iff_mem_posCone_and_one_sub_mem_posCone` : an effect is exactly a positive element
  whose complement from the order unit is also positive.
- `Effect.exists_pos_smul_mem` : every positive observable becomes an effect after scaling it down
  enough.

## iii. Table of contents

- A. Effects

## iv. References

- G. Ludwig, *Foundations of Quantum Mechanics I*, Springer, 1983.
  <https://link.springer.com/book/10.1007/978-3-642-86751-4>

-/

@[expose] public section

/-!

## A. Effects

-/

/-- A bounded measurement outcome. -/
abbrev Effect (E : Type*) [PartialOrder E] [One E] [Zero E] := Set.Icc (0 : E) 1

namespace Effect

section OrderedVectorSpace

variable {E : Type*} [OrderedVectorSpace E] [One E]

/-- An effect is a positive element whose complement from the order unit is positive. -/
lemma mem_iff_mem_posCone_and_one_sub_mem_posCone {A : E} :
    A ∈ (Effect E : Set E) ↔ A ∈ PosCone E ∧ 1 - A ∈ PosCone E := by
  simp only [Set.mem_Icc, PointedCone.mem_positive, sub_nonneg]

end OrderedVectorSpace

section OrderUnitSpace

variable {E : Type*} [OrderUnitSpace E]

instance : Zero (Effect E) := ⟨0, le_refl 0, OrderUnitSpace.one_nonneg⟩
instance : One (Effect E) := ⟨1, OrderUnitSpace.one_nonneg, le_refl 1⟩
instance : Nonempty (Effect E) := ⟨0⟩

@[simp] lemma coe_zero : ((0 : Effect E) : E) = 0 := rfl

@[simp] lemma coe_one : ((1 : Effect E) : E) = 1 := rfl

/-- Every nonnegative observable becomes an effect after scaling it down by a large enough
positive real: the effect interval reaches in every direction the positive cone does. -/
lemma exists_pos_smul_mem {B : E} (hB : 0 ≤ B) :
    ∃ r : ℝ, 0 < r ∧ r • B ∈ (Effect E : Set E) := by
  obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le B
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine ⟨((n : ℝ) + 1)⁻¹, by positivity, smul_nonneg (by positivity) hB, ?_⟩
  have hBr : B ≤ ((n : ℝ) + 1) • (1 : E) :=
    calc
      B ≤ n • (1 : E) := hn
      _ = (n : ℝ) • (1 : E) := (Nat.cast_smul_eq_nsmul ℝ n (1 : E)).symm
      _ ≤ ((n : ℝ) + 1) • (1 : E) :=
        smul_le_smul_of_nonneg_right (by linarith) OrderUnitSpace.one_nonneg
  have hs := smul_le_smul_of_nonneg_left hBr (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹)
  simpa [smul_smul, hn1.ne'] using hs

end OrderUnitSpace

end Effect
