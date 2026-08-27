/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!

# Real matrix exponentials

This file supplies two general facts about real matrix exponentials: their determinant is positive,
and the exponential of a skew-symmetric matrix is orthogonal. They are independent of qubits and
three-dimensional cross products.

-/

@[expose] public section

open scoped Matrix.Norms.Operator
open NormedSpace

namespace Matrix

/-! ## A. General facts -/

/-- The determinant of the exponential of a real square matrix is positive. -/
lemma det_exp_pos {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : 0 < (exp A).det := by
  let f : ℝ → ℝ := fun t => (exp (t • A)).det
  have hf : Continuous f := by
    apply Continuous.matrix_det
    exact exp_continuous.comp (continuous_id.smul continuous_const)
  have hne (t : ℝ) : f t ≠ 0 := by
    exact ((isUnit_iff_isUnit_det _).mp (isUnit_exp (t • A))).ne_zero
  have hf0 : f 0 = 1 := by simp [f]
  by_contra hpos
  have hf1le : f 1 ≤ 0 := by simpa [f] using le_of_not_gt hpos
  have hf1 : f 1 < 0 := lt_of_le_of_ne hf1le (hne 1)
  have hzmem : 0 ∈ Set.Icc (f 1) (f 0) := by simp [hf0, hf1.le]
  obtain ⟨t, ht⟩ := (intermediate_value_univ 1 0 hf) hzmem
  exact hne t ht

/-- The exponential of a real skew-symmetric matrix is orthogonal. -/
lemma exp_mul_exp_transpose_of_transpose_eq_neg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : Aᵀ = -A) : exp A * (exp A)ᵀ = 1 := by
  rw [← exp_transpose, hA]
  rw [← exp_add_of_commute A (-A) (Commute.refl A).neg_right]
  simp

end Matrix
