/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!

# Real rotation one-parameter groups

If an element of a real Banach algebra squares to `-1`, its exponential series splits into even
and odd parts that resum to `cos`/`sin`, exactly as `exp(iθ) = cos θ + i sin θ` for the complex
unit `i`: `K` plays the role of `i`. This is the real-linear analogue of
`Mathematics.OneParameterSubgroups.Unitary`'s "square to 1" closed form; without the complex phase
factor there is no degenerate case to handle: `exp(tK) = cos(t) • 1 + sin(t) • K` unconditionally.

Rescaling by the "frequency" `c` in `K² = -c² • 1` turns any such generator into this case, giving
the familiar rotation formula `exp(tK) = cos(ct) • 1 + sin(ct)/c • K`. This is the mechanism
behind harmonic-oscillator-type flows, whether realized by continuous linear maps or by matrices.

## Main results

* `NormedSpace.exp_smul_of_sq_eq_neg_one`: `K² = -1` gives `exp(tK) = cos t • 1 + sin t • K`.
* `NormedSpace.exp_smul_of_sq_eq_neg_smul_one`: `K² = -c² • 1` (`c ≠ 0`) gives
  `exp(tK) = cos(ct) • 1 + sin(ct)/c • K`.

-/

@[expose] public section

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

private lemma neg_one_pow_eq_smul_one (n : ℕ) :
    ((-1 : A)) ^ n = (-1 : ℝ) ^ n • (1 : A) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, smul_mul_assoc, one_mul,
      show (-1 : A) = (-1 : ℝ) • (1 : A) by simp, smul_smul, pow_succ]

/-- If `K² = -1`, then `exp(tK) = cos(t) • 1 + sin(t) • K`. -/
theorem NormedSpace.exp_smul_of_sq_eq_neg_one (K : A) (hK : K * K = -1) (t : ℝ) :
    NormedSpace.exp (t • K) = (Real.cos t) • 1 + (Real.sin t) • K := by
  let x := t • K
  have hexp := NormedSpace.expSeries_hasSum_exp (𝕂 := ℝ) x
  simp_rw [NormedSpace.expSeries_apply_eq] at hexp
  replace hexp := (Nat.divModEquiv 2).symm.hasSum_iff.mpr hexp
  dsimp [Function.comp_def] at hexp
  have hsplit : HasSum
      (fun n : ℕ ↦ ((2 * n).factorial : ℝ)⁻¹ • x ^ (2 * n) +
        ((2 * n + 1).factorial : ℝ)⁻¹ • x ^ (2 * n + 1)) (NormedSpace.exp x) := by
    simpa [Fin.sum_univ_two, Nat.divModEquiv, mul_comm, pow_succ] using
      hexp.prod_fiberwise (fun k ↦ hasSum_fintype (fun j : Fin 2 ↦
        ((Nat.divModEquiv 2).symm (k, j)).factorial.cast⁻¹ •
          x ^ (Nat.divModEquiv 2).symm (k, j)))
  have hKpow : ∀ n : ℕ, K ^ (2 * n) = ((-1 : ℝ) ^ n : ℝ) • (1 : A) := by
    intro n
    rw [pow_mul, sq, hK, neg_one_pow_eq_smul_one]
  have hxpow_even : ∀ n : ℕ, x ^ (2 * n) = ((-1 : ℝ) ^ n * t ^ (2 * n)) • 1 := by
    intro n
    show (t • K) ^ (2 * n) = _
    rw [smul_pow, hKpow, smul_smul, mul_comm]
  have hxpow_odd : ∀ n : ℕ, x ^ (2 * n + 1) = ((-1 : ℝ) ^ n * t ^ (2 * n + 1)) • K := by
    intro n
    rw [pow_succ, hxpow_even]
    show (((-1 : ℝ) ^ n * t ^ (2 * n)) • (1 : A)) * (t • K) = _
    rw [Algebra.smul_mul_assoc, one_mul, smul_smul]
    congr 1
    rw [pow_succ]
    ring
  have heven : HasSum (fun n : ℕ ↦ ((2 * n).factorial : ℝ)⁻¹ • x ^ (2 * n))
      ((Real.cos t) • (1 : A)) := by
    convert (Real.hasSum_cos t).smul_const (1 : A) using 1
    funext n
    rw [hxpow_even, smul_smul]
    congr 1
    simp [div_eq_mul_inv]
    ring_nf
  have hodd : HasSum (fun n : ℕ ↦ ((2 * n + 1).factorial : ℝ)⁻¹ • x ^ (2 * n + 1))
      ((Real.sin t) • K) := by
    have hs := (Real.hasSum_sin t).smul_const K
    convert hs using 1
    funext n
    rw [hxpow_odd, smul_smul]
    congr 1
    simp [div_eq_mul_inv]
    ring_nf
  exact HasSum.unique hsplit (heven.add hodd)

/-- If `K² = -c² • 1` for `c ≠ 0`, then `exp(tK) = cos(ct) • 1 + (sin(ct)/c) • K`. -/
theorem NormedSpace.exp_smul_of_sq_eq_neg_smul_one (K : A) (c : ℝ) (hc : c ≠ 0)
    (hK : K * K = (-(c ^ 2) : ℝ) • 1) (t : ℝ) :
    NormedSpace.exp (t • K) = (Real.cos (c * t)) • 1 + (Real.sin (c * t) / c) • K := by
  set C : A := c⁻¹ • K with hC
  have hCC : C * C = -1 := by
    rw [hC, smul_mul_smul, hK, smul_smul]
    rw [show c⁻¹ * c⁻¹ * -(c ^ 2) = -1 by field_simp]
    simp
  have hrw : t • K = (c * t) • C := by
    rw [hC, smul_smul]
    congr 1
    field_simp
  rw [hrw, NormedSpace.exp_smul_of_sq_eq_neg_one C hCC, hC, smul_smul]
  congr 2
