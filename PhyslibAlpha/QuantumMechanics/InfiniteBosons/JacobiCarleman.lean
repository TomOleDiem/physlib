/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.PSeries
/-!

# Carleman's criterion for Jacobi matrices

An `ℓ²` solution of the eigenvalue equation of a Jacobi matrix at a non-real spectral parameter
vanishes when the sum of the inverse off-diagonal entries diverges.

## i. Overview

Let `b_n > 0` be the off-diagonal entries of a Jacobi matrix `J` with zero diagonal. A sequence
`g` with `(J g)_n = -i c g_n` and `c ≠ 0` real satisfies a conserved-flux identity:
`b_N Im(conj g_N g_{N+1}) = -c Σ_{n ≤ N} |g_n|²`. If `g` is not zero the left side stays away from
zero. Then `|g_N|² + |g_{N+1}|²` is bounded below by a multiple of `1/b_N`. This contradicts
square summability of `g` when `Σ 1/b_n` diverges. This is the deficiency-index argument in
Carleman's criterion for essential self-adjointness. It applies to the quadrature operator
`a + a†` of one mode, whose entries are `b_n = √(n+1)`.

## ii. Key results

- `InfiniteBosons.jacobi_step`, `InfiniteBosons.jacobi_base`: the flux identity step.
- `InfiniteBosons.jacobi_no_l2_solution`: the Carleman argument.

## iii. Table of contents

- A. The flux identity
- B. The Carleman argument

## iv. References

* N. I. Akhiezer, The Classical Moment Problem, Oliver and Boyd (1965).
* M. Reed, B. Simon, Methods of Modern Mathematical Physics II, Section X.6.
-/

@[expose] public section

open Finset

noncomputable section

namespace InfiniteBosons

lemma jacobi_step (B1 B2 c : ℝ) (g0 g1 g2 : ℂ)
    (h : (B2 : ℂ) * g2 + (B1 : ℂ) * g0 = -(Complex.I * c) * g1) :
    B2 * (starRingEnd ℂ g1 * g2).im - B1 * (starRingEnd ℂ g0 * g1).im = -c * ‖g1‖ ^ 2 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [Complex.mul_re, Complex.mul_im] at hre him
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_im]
  linear_combination g1.re * him - g1.im * hre

lemma jacobi_base (B c : ℝ) (g0 g1 : ℂ) (h : (B : ℂ) * g1 = -(Complex.I * c) * g0) :
    B * (starRingEnd ℂ g0 * g1).im = -c * ‖g0‖ ^ 2 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [Complex.mul_re, Complex.mul_im] at hre him
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_im]
  linear_combination g0.re * him - g0.im * hre


/-- Abstract Jacobi-matrix lemma (Carleman). For a positive sequence `b` with divergent `Σ 1/b_n`,
an `ℓ²` solution of `b_n g_{n+1} + b_{n-1} g_{n-1} = -i c g_n` (with `b_{-1} = 0`) vanishes. -/
theorem jacobi_no_l2_solution (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hdiv : ¬ Summable fun n => 1 / b n) (c : ℝ) (hc : c ≠ 0) (g : ℕ → ℂ)
    (hg : Summable fun n => ‖g n‖ ^ 2)
    (h0 : (b 0 : ℂ) * g 1 = -(Complex.I * c) * g 0)
    (hrec : ∀ n, (b (n + 1) : ℂ) * g (n + 2) + (b n : ℂ) * g n = -(Complex.I * c) * g (n + 1)) :
    ∀ n, g n = 0 := by
  have hw : ∀ N, b N * (starRingEnd ℂ (g N) * g (N + 1)).im =
      -c * ∑ n ∈ range (N + 1), ‖g n‖ ^ 2 := by
    intro N
    induction N with
    | zero => simpa using jacobi_base (b 0) c (g 0) (g 1) h0
    | succ N ih =>
      have := jacobi_step (b N) (b (N + 1)) c (g N) (g (N + 1)) (g (N + 2)) (hrec N)
      rw [Finset.sum_range_succ _ (N + 1)]
      linarith
  by_contra hne
  push Not at hne
  obtain ⟨n0, hn0⟩ := hne
  set s : ℝ := ∑ n ∈ range (n0 + 1), ‖g n‖ ^ 2 with hs
  have hspos : 0 < s := by
    have : ‖g n0‖ ^ 2 ≤ s := Finset.single_le_sum (f := fun n => ‖g n‖ ^ 2)
      (fun n _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self n0))
    have : 0 < ‖g n0‖ ^ 2 := by positivity
    linarith
  have hge : ∀ N, n0 ≤ N → s ≤ ∑ n ∈ range (N + 1), ‖g n‖ ^ 2 := fun N hN =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => by positivity)
  have hbound : ∀ N, n0 ≤ N → |c| * s ≤ b N * (‖g N‖ ^ 2 + ‖g (N + 1)‖ ^ 2) / 2 := by
    intro N hN
    have h1 := hw N
    have h2 : |b N * (starRingEnd ℂ (g N) * g (N + 1)).im| ≤ b N * (‖g N‖ * ‖g (N + 1)‖) := by
      rw [abs_mul, abs_of_pos (hb N)]
      refine mul_le_mul_of_nonneg_left ?_ (hb N).le
      calc |(starRingEnd ℂ (g N) * g (N + 1)).im| ≤ ‖starRingEnd ℂ (g N) * g (N + 1)‖ :=
            Complex.abs_im_le_norm _
        _ = ‖g N‖ * ‖g (N + 1)‖ := by rw [norm_mul, RCLike.norm_conj]
    rw [h1, abs_mul] at h2
    have h3 : |c| * s ≤ |c| * ∑ n ∈ range (N + 1), ‖g n‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (hge N hN) (abs_nonneg _)
    have h4 : |∑ n ∈ range (N + 1), ‖g n‖ ^ 2| = ∑ n ∈ range (N + 1), ‖g n‖ ^ 2 :=
      abs_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
    rw [h4, abs_neg] at h2
    nlinarith [mul_nonneg (hb N).le (sq_nonneg (‖g N‖ - ‖g (N + 1)‖))]
  apply hdiv
  have hsum2 : Summable fun N => (‖g N‖ ^ 2 + ‖g (N + 1)‖ ^ 2) := hg.add ((summable_nat_add_iff 1).mpr hg)
  rw [← summable_nat_add_iff n0]
  refine Summable.of_nonneg_of_le (fun N => by have := hb (N + n0); positivity)
    (fun N => ?_) ((hsum2.comp_injective (add_left_injective n0)).mul_left (1 / (2 * (|c| * s))))
  have hb' := hbound (N + n0) (by omega)
  have hbp := hb (N + n0)
  have hcs : 0 < |c| * s := mul_pos (abs_pos.mpr hc) hspos
  rw [div_le_iff₀ hbp]
  simp only [Function.comp]
  have hX : 2 * (|c| * s) ≤ b (N + n0) * (‖g (N + n0)‖ ^ 2 + ‖g (N + n0 + 1)‖ ^ 2) := by linarith
  have h2 : 0 < 2 * (|c| * s) := by positivity
  have key : 1 ≤ ((‖g (N + n0)‖ ^ 2 + ‖g (N + n0 + 1)‖ ^ 2) * b (N + n0)) / (2 * (|c| * s)) := by
    rw [le_div_iff₀ h2]; linarith
  calc (1 : ℝ) ≤ _ := key
    _ = _ := by field_simp


end InfiniteBosons
