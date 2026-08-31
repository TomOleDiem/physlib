/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

/-!
# Analytic estimates for bounded product formulas

This file is the analytic layer for bounded irreversible dynamics.  It is deliberately independent
of Hilbert-space domains and of complete positivity.  The first estimate bounds the Banach-algebra
exponential by the scalar exponential of the norm; later product-formula results build on it.
-/

@[expose] public section

namespace OperatorAlgebra

open NormedSpace
open Filter Topology

/-! ### Exponential norm estimates -/

/-- The norm of a Banach-algebra exponential is bounded by the scalar exponential of the norm.

The proof is just the triangle inequality on the exponential series, together with the
submultiplicative estimate for powers.  The explicit `NormOneClass` assumption is needed only for
the zero-th power; it is available for the unital operator algebras used by the dynamics API. -/
theorem norm_exp_le_exp_norm {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormOneClass A] (x : A) :
    ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  refine (norm_tsum_le_tsum_norm (NormedSpace.norm_expSeries_summable' x)).trans ?_
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  apply (NormedSpace.norm_expSeries_summable' x).tsum_le_tsum
  · intro n
    rw [norm_smul, norm_inv]
    simp only [Complex.norm_natCast, smul_eq_mul]
    gcongr
    exact norm_pow_le x n
  · exact NormedSpace.expSeries_summable' ‖x‖

/-! ### Power-difference estimates -/

lemma pow_sub_pow_identity {A : Type*} [Ring A] (x y : A) : ∀ n : ℕ,
    x ^ n - y ^ n = ∑ k ∈ Finset.range n, x ^ k * (x - y) * y ^ (n - 1 - k) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    calc
      x ^ n * x - y ^ n * y = (x ^ n - y ^ n) * y + x ^ n * (x - y) := by
        noncomm_ring
      _ = (∑ k ∈ Finset.range n, x ^ k * (x - y) * y ^ (n - 1 - k)) * y +
          x ^ n * (x - y) := by rw [ih]
      _ = (∑ k ∈ Finset.range n, x ^ k * (x - y) * y ^ (n - k)) +
          x ^ n * (x - y) := by
        rw [Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : k < n := Finset.mem_range.1 hk
        simp only [mul_assoc]
        rw [← pow_succ, show n - 1 - k + 1 = n - k by omega]
      _ = ∑ k ∈ Finset.range (n + 1), x ^ k * (x - y) * y ^ (n + 1 - 1 - k) := by
        rw [Finset.sum_range_succ]
        congr 1
        have hlast : n + 1 - 1 - n = 0 := by omega
        rw [hlast, pow_zero, mul_one]

lemma norm_pow_sub_pow_le_sum {A : Type*} [NormedRing A] [NormOneClass A]
    (x y : A) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤
      ∑ k ∈ Finset.range n, ‖x‖ ^ k * ‖x - y‖ * ‖y‖ ^ (n - 1 - k) := by
  rw [pow_sub_pow_identity]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  calc
    ‖x ^ k * (x - y) * y ^ (n - 1 - k)‖ ≤
        ‖x ^ k‖ * ‖x - y‖ * ‖y ^ (n - 1 - k)‖ := by
          exact (norm_mul_le _ _).trans (mul_le_mul
            (norm_mul_le _ _) le_rfl (by positivity) (by positivity))
    _ ≤ ‖x‖ ^ k * ‖x - y‖ * ‖y‖ ^ (n - 1 - k) := by
          gcongr
          exact norm_pow_le x k
          exact norm_pow_le y (n - 1 - k)

/-! ### The one-generator Euler formula -/

/-- The `k`th binomial term in the Euler approximation for `exp (t • x)`. -/
noncomputable def eulerTerm {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (x : A) (t : ℝ) (n k : ℕ) : A :=
  if k ≤ n then ((n.choose k : ℝ) * (t / n)^k) • x^k else 0

lemma shifted_tendsto {f : ℕ → ℝ} {a : ℝ} (h : Tendsto f atTop (𝓝 a)) :
    Tendsto (fun n => f (n + 1)) atTop (𝓝 a) := by
  simpa [Function.comp_def] using h.comp (tendsto_add_atTop_nat 1)

lemma choose_euler_coefficient_tendsto {t : ℝ} (k : ℕ) :
    Tendsto (fun n : ℕ => (n + 1).choose k * (t / (n + 1 : ℝ)) ^ k) atTop
      (𝓝 (t ^ k / k.factorial)) := by
  let p : ℕ → ℝ := fun n => t / (n : ℝ)
  have hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 t) := by
    apply Tendsto.congr' (f₁ := fun _ : ℕ => t)
      (f₂ := fun n : ℕ => (n : ℝ) * p n) (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (n : ℝ) ≠ 0 := by positivity
      dsimp [p]
      field_simp [hn'])
    exact tendsto_const_nhds
  have hbase := ProbabilityTheory.tendsto_choose_mul_pow_atTop (p := p) k hp
  simpa [p, Function.comp_def] using shifted_tendsto hbase

lemma euler_pow_eq_sum {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (x : A) (t : ℝ) (n : ℕ) :
    (1 + (t / n : ℝ) • x)^n =
      ∑ k ∈ Finset.range (n + 1), eulerTerm x t n k := by
  calc
    (1 + (t / n : ℝ) • x)^n = ((t / n : ℝ) • x + 1)^n := by rw [add_comm]
    _ = ∑ k ∈ Finset.range (n + 1),
        ((t / n : ℝ) • x)^k * 1^(n - k) * (n.choose k : A) :=
      (Commute.one_right ((t / n : ℝ) • x)).add_pow n
    _ = ∑ k ∈ Finset.range (n + 1), eulerTerm x t n k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [eulerTerm, Finset.mem_range] at *
      have hk' : k ≤ n := Nat.le_of_lt_succ hk
      rw [if_pos hk', one_pow, mul_one, smul_pow]
      let r : ℝ := (t / n) ^ k
      let c : ℝ := n.choose k
      change (r • x ^ k) * (n.choose k : A) = (c * r) • x ^ k
      have hcast : (n.choose k : A) = algebraMap ℝ A c := by simp [c]
      rw [hcast]
      calc
        (r • x ^ k) * algebraMap ℝ A c = algebraMap ℝ A c * (r • x ^ k) := by
          rw [← Algebra.commutes]
        _ = c • (r • x ^ k) := by simp only [Algebra.smul_def]
        _ = (c * r) • x ^ k := by rw [smul_smul]

lemma eulerTerm_tendsto {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (x : A) (t : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => eulerTerm x t (n + 1) k) atTop
      (𝓝 (((k.factorial : ℝ)⁻¹ * t ^ k) • x ^ k)) := by
  let c : ℕ → ℝ := fun n => (n + 1).choose k * (t / (n + 1 : ℝ)) ^ k
  have hc : Tendsto c atTop (𝓝 (t ^ k / k.factorial)) := by
    simpa [c] using choose_euler_coefficient_tendsto (t := t) k
  have hmap : Continuous (fun r : ℝ => r • x ^ k) := by fun_prop
  have hsmul : Tendsto (fun n : ℕ => c n • x ^ k) atTop
      (𝓝 ((t ^ k / k.factorial) • x ^ k)) := by
    simpa [Function.comp_def] using (hmap.tendsto _).comp hc
  apply Tendsto.congr' (f₁ := fun n : ℕ => (c n) • x ^ k)
    (f₂ := fun n : ℕ => eulerTerm x t (n + 1) k) (by
      filter_upwards [eventually_ge_atTop k] with n hn
      have hkn : k ≤ n + 1 := by omega
      simp only [eulerTerm, c, if_pos hkn]
      congr 2
      norm_num)
  simpa [c, div_eq_mul_inv, mul_comm] using hsmul

lemma eulerTerm_norm_le {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [NormOneClass A] (x : A) (t : ℝ) (n k : ℕ) :
    ‖eulerTerm x t (n + 1) k‖ ≤
      (k.factorial : ℝ)⁻¹ * (‖t‖ * ‖x‖) ^ k := by
  by_cases hk : k ≤ n + 1
  · simp only [eulerTerm, if_pos hk, norm_smul, Real.norm_eq_abs]
    rw [abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg _)]
    let N : ℝ := (n + 1 : ℕ)
    have hN : 0 < N := by positivity
    have hchoose : ((Nat.choose (n + 1) k : ℕ) : ℝ) ≤
        N ^ k / k.factorial := by
      simpa [N] using (Nat.choose_le_pow_div (α := ℝ) k (n + 1))
    have hpow : ‖x ^ k‖ ≤ ‖x‖ ^ k := norm_pow_le x k
    have hcoef :
        ((Nat.choose (n + 1) k : ℕ) : ℝ) * |t / N| ^ k ≤
          (k.factorial : ℝ)⁻¹ * ‖t‖ ^ k := by
      rw [abs_div, abs_of_nonneg hN.le]
      have ht : |t| = ‖t‖ := rfl
      rw [ht]
      calc
        ((Nat.choose (n + 1) k : ℕ) : ℝ) * (‖t‖ / N) ^ k =
            (((Nat.choose (n + 1) k : ℕ) : ℝ) * N⁻¹ ^ k) * ‖t‖ ^ k := by
              rw [div_pow]
              ring
        _ ≤ ((N ^ k / k.factorial) * N⁻¹ ^ k) * ‖t‖ ^ k := by
              gcongr
        _ = (k.factorial : ℝ)⁻¹ * ‖t‖ ^ k := by
              have hpowN : N ^ k * N⁻¹ ^ k = 1 := by
                rw [← mul_pow, mul_inv_cancel₀ hN.ne', one_pow]
              rw [div_eq_mul_inv]
              calc
                N ^ k * (k.factorial : ℝ)⁻¹ * N⁻¹ ^ k * ‖t‖ ^ k =
                    (k.factorial : ℝ)⁻¹ * (N ^ k * N⁻¹ ^ k) * ‖t‖ ^ k := by ring
                _ = (k.factorial : ℝ)⁻¹ * ‖t‖ ^ k := by rw [hpowN, mul_one]
    calc
      ((Nat.choose (n + 1) k : ℕ) : ℝ) * |t / N| ^ k * ‖x ^ k‖ ≤
          ((k.factorial : ℝ)⁻¹ * ‖t‖ ^ k) * ‖x‖ ^ k :=
            mul_le_mul hcoef hpow (norm_nonneg _) (by positivity)
      _ = (k.factorial : ℝ)⁻¹ * (‖t‖ * ‖x‖) ^ k := by
            rw [mul_pow]
            ring
  · simp [eulerTerm, hk]
    positivity

lemma eulerTerm_tsum_eq_sum {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (x : A) (t : ℝ) (n : ℕ) :
    ∑' k : ℕ, eulerTerm x t n k =
      ∑ k ∈ Finset.range (n + 1), eulerTerm x t n k := by
  rw [tsum_eq_sum]
  intro k hk
  have hkn : n < k := by simpa [Finset.mem_range, not_lt] using hk
  simp [eulerTerm, Nat.not_le_of_lt hkn]

/-- The Euler powers converge in norm to the exponential of one bounded generator. -/
theorem euler_pow_tendsto {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] [NormOneClass A] (x : A) (t : ℝ) :
    Tendsto (fun n : ℕ => (1 + (t / (n + 1) : ℝ) • x) ^ (n + 1)) atTop
      (𝓝 (NormedSpace.exp (t • x))) := by
  let bound : ℕ → ℝ := fun k => (k.factorial : ℝ)⁻¹ * (‖t‖ * ‖x‖) ^ k
  have hbound : Summable bound := by
    simpa [bound, smul_eq_mul] using
      (NormedSpace.expSeries_summable' (𝕂 := ℝ) (‖t‖ * ‖x‖))
  have hsum := tendsto_tsum_of_dominated_convergence hbound
    (fun k => eulerTerm_tendsto x t k) (by
      filter_upwards [] with n k
      exact eulerTerm_norm_le x t n k)
  have hsumexp : (∑' k : ℕ, ((k.factorial : ℝ)⁻¹ * t ^ k) • x ^ k) =
      NormedSpace.exp (t • x) := by
    rw [NormedSpace.exp_eq_tsum ℝ]
    apply tsum_congr
    intro k
    rw [smul_pow]
    rw [smul_smul]
  have hlim : Tendsto
      (fun n : ℕ => ∑' k : ℕ, eulerTerm x t (n + 1) k) atTop
      (𝓝 (NormedSpace.exp (t • x))) := by
    rw [← hsumexp]
    exact hsum
  refine hlim.congr' ?_
  filter_upwards [] with n
  rw [eulerTerm_tsum_eq_sum]
  simpa [Nat.cast_add, Nat.cast_one] using (euler_pow_eq_sum x t (n + 1)).symm

/-! ### The two-generator Lie product formula -/

section ProductFormula

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [NormOneClass A]

theorem pow_sub_pow_tendsto_of_bound
    (q r : ℕ → A) (C : ℝ)
    (hterm : ∀ (n k : ℕ), k < n + 1 →
      ‖q n‖ ^ k * ‖q n - r n‖ * ‖r n‖ ^ (n - k) ≤ C * ‖q n - r n‖)
    (hdiff : Tendsto (fun n : ℕ => (n + 1 : ℝ) * ‖q n - r n‖)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => q n ^ (n + 1) - r n ^ (n + 1)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _))
  · filter_upwards [] with n
    have hnorm := norm_pow_sub_pow_le_sum (q n) (r n) (n + 1)
    calc
      ‖q n ^ (n + 1) - r n ^ (n + 1)‖ ≤
          ∑ k ∈ Finset.range (n + 1),
            ‖q n‖ ^ k * ‖q n - r n‖ * ‖r n‖ ^ (n + 1 - 1 - k) := hnorm
      _ ≤ ∑ k ∈ Finset.range (n + 1), C * ‖q n - r n‖ := by
        apply Finset.sum_le_sum
        intro k hk
        apply hterm n k
        simp only [Finset.mem_range] at hk
        omega
      _ = C * ((n + 1 : ℝ) * ‖q n - r n‖) := by
        simp only [Finset.sum_const, Finset.card_range]
        ring
  · simpa using hdiff.const_mul C

/-- Lie's product formula for a differentiable bounded step family.

This is the form used by the Lindblad construction: the first factor need not itself be written
as an exponential.  It is enough to know its value and derivative at zero and a uniform
exponential norm bound on the steps. -/
theorem lie_product_formula_of_step
    (a : ℝ → A) (x y : A) (c t : ℝ)
    (ht : 0 ≤ t) (hc : 0 ≤ c) (ha0 : a 0 = 1)
    (ha : HasDerivAt a x 0)
    (hqa : ∀ n : ℕ, ‖a (t / (n + 1 : ℝ)) *
      (1 + (t / (n + 1 : ℝ)) • y)‖ ≤
        Real.exp ((t / (n + 1 : ℝ)) * c))
    (hr : ∀ n : ℕ, ‖(1 : A) + (t / (n + 1 : ℝ)) • (x + y)‖ ≤
      Real.exp ((t / (n + 1 : ℝ)) * c)) :
    Tendsto (fun n : ℕ =>
      (a (t / (n + 1 : ℝ)) *
        (1 + (t / (n + 1 : ℝ)) • y)) ^ (n + 1)) atTop
      (𝓝 (NormedSpace.exp (t • (x + y)))) := by
  by_cases ht0 : t = 0
  · subst t
    simp [ha0]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let q : ℕ → A := fun n =>
    a (t / (n + 1 : ℝ)) * (1 + (t / (n + 1 : ℝ)) • y)
  let r : ℕ → A := fun n =>
    1 + (t / (n + 1 : ℝ)) • (x + y)
  have hdiff : Tendsto (fun n : ℕ => (n + 1 : ℝ) * ‖q n - r n‖)
      atTop (𝓝 0) := by
    let F : ℝ → A := fun s => a s * (1 + s • y)
    have hF : HasDerivAt F (x + y) 0 := by
      have hs : HasDerivAt (fun s : ℝ => s • y) y 0 := by
        simpa only [id_eq, one_smul] using
          (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const y
      have hy : HasDerivAt (fun s : ℝ => (1 : A) + s • y) y 0 := by
        change HasDerivAt ((fun _ : ℝ => (1 : A)) + (fun s : ℝ => s • y)) y 0
        simpa only [zero_add] using (hasDerivAt_const (0 : ℝ) (1 : A)).add hs
      have h := ha.mul hy
      dsimp [F]
      change HasDerivAt (a * (fun s : ℝ => 1 + s • y)) (x + y) 0
      simpa [ha0] using h
    have hlocal : Tendsto (fun s : ℝ => ‖s‖⁻¹ *
        ‖F s - F 0 - s • (x + y)‖) (𝓝 0) (𝓝 0) := by
      simpa using (hasDerivAt_iff_tendsto).mp hF
    have hz : Tendsto (fun n : ℕ => t / (n + 1 : ℝ)) atTop (𝓝 0) := by
      simpa [Nat.cast_add, Nat.cast_one] using
        shifted_tendsto (tendsto_const_div_atTop_nhds_zero_nat t)
    have hratio := hlocal.comp hz
    have hmul := hratio.const_mul t
    convert hmul.congr' ?_ using 1
    · simp
    filter_upwards [] with n
    have hnpos : 0 < (n + 1 : ℝ) := by positivity
    have hstep : 0 < t / (n + 1 : ℝ) := div_pos htpos hnpos
    have habs : |t / (n + 1 : ℝ)| = t / (n + 1 : ℝ) := abs_of_pos hstep
    dsimp [F, q, r]
    simp only [ha0, zero_smul, one_smul, mul_one, one_mul, add_zero]
    rw [habs]
    field_simp
    congr 1
    noncomm_ring
  have hterm : ∀ (n k : ℕ), k < n + 1 →
      ‖q n‖ ^ k * ‖q n - r n‖ * ‖r n‖ ^ (n - k) ≤
        Real.exp (t * c) * ‖q n - r n‖ := by
    intro n k hk
    let h : ℝ := t / (n + 1 : ℝ)
    let K : ℝ := Real.exp (h * c)
    let d : ℝ := ‖q n - r n‖
    have hh : 0 ≤ h := by dsimp [h]; positivity
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hq : ‖q n‖ ≤ K := by simpa [q, h, K] using hqa n
    have hr' : ‖r n‖ ≤ K := by simpa [r, h, K] using hr n
    have hKn : K ^ n ≤ Real.exp (t * c) := by
      rw [show K ^ n = Real.exp (n * (h * c)) by
        dsimp [K]
        rw [Real.exp_nat_mul]]
      apply (Real.exp_le_exp).2
      dsimp [h]
      have hnpos : 0 < (n + 1 : ℝ) := by positivity
      have hnle : (n : ℝ) ≤ n + 1 := by exact_mod_cast Nat.le_succ n
      have hfrac : (n : ℝ) * (t / (n + 1 : ℝ)) ≤ t := by
        calc
          (n : ℝ) * (t / (n + 1 : ℝ)) = t * ((n : ℝ) / (n + 1 : ℝ)) := by ring
          _ ≤ t * 1 := by
            apply mul_le_mul_of_nonneg_left ?_ ht
            apply (div_le_iff₀ hnpos).2
            simpa using hnle
          _ = t := by ring
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hfrac hc
    have hmain : K ^ k * d * K ^ (n - k) ≤ Real.exp (t * c) * d := by
      calc
        K ^ k * d * K ^ (n - k) = K ^ (k + (n - k)) * d := by
          rw [pow_add]
          ring
        _ = K ^ n * d := by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ hk)]
        _ ≤ Real.exp (t * c) * d := by gcongr
    calc
      _ ≤ K ^ k * d * K ^ (n - k) := by
        have hqpow : ‖q n‖ ^ k ≤ K ^ k :=
          pow_le_pow_left₀ (norm_nonneg _) hq k
        have hrpow : ‖r n‖ ^ (n - k) ≤ K ^ (n - k) :=
          pow_le_pow_left₀ (norm_nonneg _) hr' (n - k)
        apply mul_le_mul
        · exact mul_le_mul hqpow le_rfl (by positivity) (by positivity)
        · exact hrpow
        · positivity
        · positivity
      _ ≤ Real.exp (t * c) * d := hmain
      _ = _ := by rfl
  have hpowdiff := pow_sub_pow_tendsto_of_bound q r
    (Real.exp (t * c)) hterm hdiff
  have her := euler_pow_tendsto (x + y) t
  rw [← tendsto_sub_nhds_zero_iff]
  have her' : Tendsto (fun n : ℕ => r n ^ (n + 1) - NormedSpace.exp (t • (x + y)))
      atTop (𝓝 0) := by
    simpa [r] using (her.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => NormedSpace.exp (t • (x + y)))
        atTop (𝓝 (NormedSpace.exp (t • (x + y))))))
  have hsum := hpowdiff.add her'
  convert hsum using 1
  · funext n
    dsimp [q, r]
    abel
  · simp

theorem lie_q_norm_le (x y : A) (t : ℝ) (n : ℕ) (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((t / (n + 1 : ℝ)) • x) *
        (1 + (t / (n + 1 : ℝ)) • y)‖ ≤
      Real.exp ((t / (n + 1 : ℝ)) * (‖x‖ + ‖y‖)) := by
  let h : ℝ := t / (n + 1 : ℝ)
  have hh : 0 ≤ h := by
    dsimp [h]
    positivity
  have hnx : ‖h • x‖ = h * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  have hny : ‖h • y‖ = h * ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  have hlin : ‖(1 : A) + h • y‖ ≤ 1 + h * ‖y‖ := by
    calc
      ‖(1 : A) + h • y‖ ≤ ‖(1 : A)‖ + ‖h • y‖ := norm_add_le _ _
      _ = 1 + h * ‖y‖ := by rw [norm_one, hny]
  have hexp : ‖NormedSpace.exp (h • x)‖ ≤ Real.exp (h * ‖x‖) := by
    simpa [hnx] using norm_exp_le_exp_norm (h • x)
  have hlinexp : 1 + h * ‖y‖ ≤ Real.exp (h * ‖y‖) := by
    simpa [add_comm] using Real.add_one_le_exp (h * ‖y‖)
  calc
    ‖NormedSpace.exp (h • x) * (1 + h • y)‖ ≤
        ‖NormedSpace.exp (h • x)‖ * ‖(1 : A) + h • y‖ := norm_mul_le _ _
    _ ≤ Real.exp (h * ‖x‖) * (1 + h * ‖y‖) :=
      mul_le_mul hexp hlin (norm_nonneg _) (by positivity)
    _ ≤ Real.exp (h * ‖x‖) * Real.exp (h * ‖y‖) :=
      mul_le_mul_of_nonneg_left hlinexp (by positivity)
    _ = Real.exp (h * (‖x‖ + ‖y‖)) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem lie_r_norm_le (x y : A) (t : ℝ) (n : ℕ) (ht : 0 ≤ t) :
    ‖(1 : A) + (t / (n + 1 : ℝ)) • (x + y)‖ ≤
      Real.exp ((t / (n + 1 : ℝ)) * (‖x‖ + ‖y‖)) := by
  let h : ℝ := t / (n + 1 : ℝ)
  have hh : 0 ≤ h := by
    dsimp [h]
    positivity
  have hxy : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
  have hnorm : ‖h • (x + y)‖ ≤ h * (‖x‖ + ‖y‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    gcongr
  have hone : ‖(1 : A)‖ = (1 : ℝ) := norm_one
  have hlin : ‖(1 : A) + h • (x + y)‖ ≤ 1 + h * (‖x‖ + ‖y‖) := by
    calc
      ‖(1 : A) + h • (x + y)‖ ≤ ‖(1 : A)‖ + ‖h • (x + y)‖ := norm_add_le _ _
      _ ≤ 1 + h * (‖x‖ + ‖y‖) := by rw [hone]; gcongr
  have hexp : 1 + h * (‖x‖ + ‖y‖) ≤ Real.exp (h * (‖x‖ + ‖y‖)) := by
    simpa [add_comm] using Real.add_one_le_exp (h * (‖x‖ + ‖y‖))
  calc
    ‖(1 : A) + h • (x + y)‖ ≤ 1 + h * (‖x‖ + ‖y‖) := hlin
    _ ≤ Real.exp (h * (‖x‖ + ‖y‖)) := hexp

theorem lie_term_bound (x y : A) (t : ℝ) (n k : ℕ) (ht : 0 ≤ t)
    (hk : k < n + 1) :
    ‖NormedSpace.exp ((t / (n + 1 : ℝ)) • x) *
        (1 + (t / (n + 1 : ℝ)) • y)‖ ^ k *
        ‖NormedSpace.exp ((t / (n + 1 : ℝ)) • x) *
          (1 + (t / (n + 1 : ℝ)) • y) -
          (1 + (t / (n + 1 : ℝ)) • (x + y))‖ *
        ‖1 + (t / (n + 1 : ℝ)) • (x + y)‖ ^ (n - k) ≤
      Real.exp (t * (‖x‖ + ‖y‖)) *
        ‖NormedSpace.exp ((t / (n + 1 : ℝ)) • x) *
          (1 + (t / (n + 1 : ℝ)) • y) -
          (1 + (t / (n + 1 : ℝ)) • (x + y))‖ := by
  let h : ℝ := t / (n + 1 : ℝ)
  let c : ℝ := ‖x‖ + ‖y‖
  let K : ℝ := Real.exp (h * c)
  let d : ℝ := ‖NormedSpace.exp (h • x) * (1 + h • y) - (1 + h • (x + y))‖
  have hh : 0 ≤ h := by
    dsimp [h]
    positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq : ‖NormedSpace.exp (h • x) * (1 + h • y)‖ ≤ K := by
    simpa [h, c, K] using lie_q_norm_le x y t n ht
  have hr : ‖(1 : A) + h • (x + y)‖ ≤ K := by
    simpa [h, c, K] using lie_r_norm_le x y t n ht
  have hKn : K ^ n ≤ Real.exp (t * c) := by
    rw [show K ^ n = Real.exp (n * (h * c)) by
      dsimp [K]
      rw [Real.exp_nat_mul]]
    apply (Real.exp_le_exp).2
    dsimp [h]
    have hnpos : 0 < (n + 1 : ℝ) := by positivity
    have hnle : (n : ℝ) ≤ n + 1 := by exact_mod_cast Nat.le_succ n
    have hfrac : (n : ℝ) * (t / (n + 1 : ℝ)) ≤ t := by
      calc
        (n : ℝ) * (t / (n + 1 : ℝ)) = t * ((n : ℝ) / (n + 1 : ℝ)) := by ring
        _ ≤ t * 1 := by
          apply mul_le_mul_of_nonneg_left ?_ ht
          apply (div_le_iff₀ hnpos).2
          simpa using hnle
        _ = t := by ring
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hfrac hc
  have hmain : K ^ k * d * K ^ (n - k) ≤ Real.exp (t * c) * d := by
    calc
      K ^ k * d * K ^ (n - k) = K ^ (k + (n - k)) * d := by
        rw [pow_add]
        ring
      _ = K ^ n * d := by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ hk)]
      _ ≤ Real.exp (t * c) * d := by
        gcongr
  calc
    _ ≤ K ^ k * d * K ^ (n - k) := by
      have hqpow : ‖NormedSpace.exp (h • x) * (1 + h • y)‖ ^ k ≤ K ^ k :=
        pow_le_pow_left₀ (norm_nonneg _) hq k
      have hrpow : ‖(1 : A) + h • (x + y)‖ ^ (n - k) ≤ K ^ (n - k) :=
        pow_le_pow_left₀ (norm_nonneg _) hr (n - k)
      apply mul_le_mul
      · exact mul_le_mul hqpow le_rfl (by positivity) (by positivity)
      · exact hrpow
      · positivity
      · positivity
    _ ≤ Real.exp (t * c) * d := hmain
    _ = _ := by simp [d, h, c, K]

theorem lie_difference_tendsto (x y : A) (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) *
      ‖NormedSpace.exp ((t / (n + 1 : ℝ)) • x) *
          (1 + (t / (n + 1 : ℝ)) • y) -
          (1 + (t / (n + 1 : ℝ)) • (x + y))‖) atTop (𝓝 0) := by
  let F : ℝ → A := fun s => NormedSpace.exp (s • x) * (1 + s • y)
  have hF : HasDerivAt F (x + y) 0 := by
    have hx := hasDerivAt_exp_smul_const x (0 : ℝ)
    have hs : HasDerivAt (fun s : ℝ => s • y) y 0 := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const y
    have hy : HasDerivAt (fun s : ℝ => (1 : A) + s • y) y 0 := by
      change HasDerivAt ((fun _ : ℝ => (1 : A)) + (fun s : ℝ => s • y)) y 0
      simpa only [zero_add] using (hasDerivAt_const (0 : ℝ) (1 : A)).add hs
    have h := hx.mul hy
    dsimp [F]
    change HasDerivAt ((fun u : ℝ => NormedSpace.exp (u • x)) *
      (fun s : ℝ => 1 + s • y)) (x + y) 0
    simpa using h
  have hlocal : Tendsto (fun s : ℝ => ‖s‖⁻¹ *
      ‖F s - F 0 - s • (x + y)‖) (𝓝 0) (𝓝 0) := by
    simpa using (hasDerivAt_iff_tendsto).mp hF
  have hz : Tendsto (fun n : ℕ => t / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      shifted_tendsto (tendsto_const_div_atTop_nhds_zero_nat t)
  have hratio := hlocal.comp hz
  have hmul := hratio.const_mul t
  convert hmul.congr' ?_ using 1
  · simp
  filter_upwards [] with n
  have hnpos : 0 < (n + 1 : ℝ) := by positivity
  have hstep : 0 < t / (n + 1 : ℝ) := div_pos ht hnpos
  have habs : |t / (n + 1 : ℝ)| = t / (n + 1 : ℝ) := abs_of_pos hstep
  dsimp [F]
  simp only [zero_smul, NormedSpace.exp_zero, one_smul, mul_one, one_mul]
  rw [habs]
  field_simp
  congr 1
  noncomm_ring

theorem lie_product_formula (x y : A) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ =>
      (NormedSpace.exp ((t / (n + 1 : ℝ)) • x) *
        (1 + (t / (n + 1 : ℝ)) • y)) ^ (n + 1)) atTop
      (𝓝 (NormedSpace.exp (t • (x + y)))) := by
  by_cases ht0 : t = 0
  · subst t
    simp
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  let q : ℕ → A := fun n =>
    NormedSpace.exp ((t / (n + 1 : ℝ)) • x) *
      (1 + (t / (n + 1 : ℝ)) • y)
  let r : ℕ → A := fun n =>
    1 + (t / (n + 1 : ℝ)) • (x + y)
  have hdiff := lie_difference_tendsto x y t htpos
  have hterm : ∀ (n k : ℕ), k < n + 1 →
      ‖q n‖ ^ k * ‖q n - r n‖ * ‖r n‖ ^ (n - k) ≤
        Real.exp (t * (‖x‖ + ‖y‖)) * ‖q n - r n‖ := by
    intro n k hk
    simpa [q, r] using lie_term_bound x y t n k ht hk
  have hpowdiff := pow_sub_pow_tendsto_of_bound q r
    (Real.exp (t * (‖x‖ + ‖y‖))) hterm (by simpa [q, r] using hdiff)
  have her := euler_pow_tendsto (x + y) t
  rw [← tendsto_sub_nhds_zero_iff]
  have her' : Tendsto (fun n : ℕ => r n ^ (n + 1) - NormedSpace.exp (t • (x + y)))
      atTop (𝓝 0) := by
    simpa [r] using (her.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => NormedSpace.exp (t • (x + y)))
        atTop (𝓝 (NormedSpace.exp (t • (x + y))))))
  have hsum := hpowdiff.add her'
  convert hsum using 1
  · funext n
    dsimp [q, r]
    abel
  · simp

end ProductFormula

end OperatorAlgebra
