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



/-!

## C. Block Jacobi matrices

A Hermitian matrix that only couples neighbouring grades of finite size, with arbitrary diagonal
blocks. The off-diagonal blocks are controlled by their row and column sums (Schur test). The
diagonal blocks do not enter.

-/

section Block

variable {β : Type*} [DecidableEq β]

omit [DecidableEq β] in
/-- **Schur test** in the form used for the flux bound. -/
lemma norm_sum_conj_mul_le (A B : Finset β) (h : β → β → ℂ) (u v : β → ℂ) (r : ℝ)
    (hrow : ∀ a ∈ A, ∑ b ∈ B, ‖h a b‖ ≤ r) (hcol : ∀ b ∈ B, ∑ a ∈ A, ‖h a b‖ ≤ r) :
    ‖∑ a ∈ A, ∑ b ∈ B, starRingEnd ℂ (u a) * h a b * v b‖ ≤
      r * (∑ a ∈ A, ‖u a‖ ^ 2 + ∑ b ∈ B, ‖v b‖ ^ 2) / 2 := by
  have h1 : ‖∑ a ∈ A, ∑ b ∈ B, starRingEnd ℂ (u a) * h a b * v b‖ ≤
      ∑ a ∈ A, ∑ b ∈ B, ‖h a b‖ * ((‖u a‖ ^ 2 + ‖v b‖ ^ 2) / 2) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun b _ => ?_))
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    nlinarith [norm_nonneg (h a b), sq_nonneg (‖u a‖ - ‖v b‖),
      mul_nonneg (norm_nonneg (h a b)) (sq_nonneg (‖u a‖ - ‖v b‖))]
  refine h1.trans ?_
  have e : ∑ a ∈ A, ∑ b ∈ B, ‖h a b‖ * ((‖u a‖ ^ 2 + ‖v b‖ ^ 2) / 2) =
      (∑ a ∈ A, ∑ b ∈ B, ‖u a‖ ^ 2 * ‖h a b‖ + ∑ a ∈ A, ∑ b ∈ B, ‖v b‖ ^ 2 * ‖h a b‖) / 2 := by
    rw [eq_div_iff two_ne_zero, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [e, Finset.sum_comm (s := A) (t := B) (f := fun a b => ‖v b‖ ^ 2 * ‖h a b‖)]
  simp only [← Finset.mul_sum]
  have h2 : ∑ a ∈ A, ‖u a‖ ^ 2 * ∑ b ∈ B, ‖h a b‖ ≤ (∑ a ∈ A, ‖u a‖ ^ 2) * r := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hrow a ha) (by positivity)
  have h3 : ∑ b ∈ B, ‖v b‖ ^ 2 * ∑ a ∈ A, ‖h a b‖ ≤ (∑ b ∈ B, ‖v b‖ ^ 2) * r := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (hcol b hb) (by positivity)
  linarith

variable (gr : β → ℕ) (S : ℕ → Finset β)

/-- The vectors of grade at most `N`. -/
def gradeLe (N : ℕ) : Finset β := (range (N + 1)).biUnion S

variable {gr S}

lemma mem_gradeLe (hS : ∀ a n, a ∈ S n → gr a = n) {a : β} {N : ℕ} (ha : a ∈ gradeLe S N) :
    gr a ≤ N := by
  simp only [gradeLe, Finset.mem_biUnion, Finset.mem_range] at ha
  obtain ⟨n, hn, h⟩ := ha
  rw [hS a n h]; omega

lemma subset_gradeLe {n N : ℕ} (h : n ≤ N) : S n ⊆ gradeLe S N := fun a ha =>
  Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr (by omega), ha⟩

lemma gradeLe_mono {M N : ℕ} (h : M ≤ N) : gradeLe S M ⊆ gradeLe S N := fun a ha => by
  simp only [gradeLe, Finset.mem_biUnion, Finset.mem_range] at ha ⊢
  obtain ⟨n, hn, h'⟩ := ha
  exact ⟨n, by omega, h'⟩

lemma exists_mem_of_mem_gradeLe {a : β} {N : ℕ} (ha : a ∈ gradeLe S N) : ∃ n ≤ N, a ∈ S n := by
  simp only [gradeLe, Finset.mem_biUnion, Finset.mem_range] at ha
  obtain ⟨n, hn, h⟩ := ha
  exact ⟨n, by omega, h⟩

lemma gradeLe_succ (hS : ∀ a n, a ∈ S n → gr a = n) (N : ℕ) :
    gradeLe S (N + 1) = gradeLe S N ∪ S (N + 1) ∧ Disjoint (gradeLe S N) (S (N + 1)) := by
  constructor
  · rw [gradeLe, Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]; rfl
  · rw [Finset.disjoint_left]; intro a h1 h2
    have := mem_gradeLe hS h1; rw [hS a _ h2] at this; omega

omit [DecidableEq β] in
/-- The sum over a Hermitian block is real. -/
lemma im_sum_hermitian_eq_zero (A : Finset β) (h : β → β → ℂ)
    (hherm : ∀ a b, h b a = starRingEnd ℂ (h a b)) (g : β → ℂ) :
    (∑ a ∈ A, ∑ b ∈ A, starRingEnd ℂ (g a) * h a b * g b).im = 0 := by
  set Q := ∑ a ∈ A, ∑ b ∈ A, starRingEnd ℂ (g a) * h a b * g b
  have hQ : starRingEnd ℂ Q = Q := by
    simp only [Q, map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← hherm b a]; ring
  have := congrArg Complex.im hQ
  rw [Complex.conj_im] at this
  linarith

/-- **Flux identity for block Jacobi matrices.** If `H g = i c g` row by row, the weight of the
grades up to `N` times `c` is the imaginary part of the coupling between grades `N` and `N + 1`. -/
lemma blockJacobi_flux (hS : ∀ a n, a ∈ S n → gr a = n) (h : β → β → ℂ)
    (hherm : ∀ a b, h b a = starRingEnd ℂ (h a b))
    (hband : ∀ a b, h a b ≠ 0 → gr b ≤ gr a + 1 ∧ gr a ≤ gr b + 1) (c : ℝ) (g : β → ℂ)
    (heq : ∀ a, a ∈ S (gr a) →
      ∑ b ∈ gradeLe S (gr a + 1), h a b * g b = Complex.I * c * g a) (N : ℕ) :
    c * ∑ a ∈ gradeLe S N, ‖g a‖ ^ 2 =
      (∑ a ∈ S N, ∑ b ∈ S (N + 1), starRingEnd ℂ (g a) * h a b * g b).im := by
  -- each row may be summed over all grades up to `N + 1`
  have hrow : ∀ a ∈ gradeLe S N, ∑ b ∈ gradeLe S (N + 1), h a b * g b = Complex.I * c * g a := by
    intro a ha
    obtain ⟨n, hn, han⟩ := exists_mem_of_mem_gradeLe ha
    have hga := hS a n han
    rw [← heq a (hga ▸ han)]
    refine (Finset.sum_subset (gradeLe_mono (by omega)) fun b hb hb' => ?_).symm
    by_contra hne
    have h1 := (hband a b (left_ne_zero_of_mul hne)).1
    obtain ⟨m, hm, hbm⟩ := exists_mem_of_mem_gradeLe hb
    exact hb' (subset_gradeLe (by rw [← hS b m hbm]; exact h1) hbm)
  have htot : ∑ a ∈ gradeLe S N, ∑ b ∈ gradeLe S (N + 1), starRingEnd ℂ (g a) * h a b * g b =
      Complex.I * c * ∑ a ∈ gradeLe S N, (‖g a‖ ^ 2 : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [mul_assoc, ← Finset.mul_sum, hrow a ha]
    rw [← Complex.conj_mul']; ring
  obtain ⟨hsplit, hdisj⟩ := gradeLe_succ hS N
  simp only [hsplit, Finset.sum_union hdisj, Finset.sum_add_distrib] at htot
  -- only grade `N` couples to grade `N + 1`
  have hbd : ∑ a ∈ gradeLe S N, ∑ b ∈ S (N + 1), starRingEnd ℂ (g a) * h a b * g b =
      ∑ a ∈ S N, ∑ b ∈ S (N + 1), starRingEnd ℂ (g a) * h a b * g b := by
    refine (Finset.sum_subset (subset_gradeLe le_rfl)
      fun a ha haN => Finset.sum_eq_zero fun b hb => ?_).symm
    by_contra hne
    have h1 := (hband a b (right_ne_zero_of_mul (left_ne_zero_of_mul hne))).1
    obtain ⟨n, hn, han⟩ := exists_mem_of_mem_gradeLe ha
    have hn' : n ≠ N := fun h => haN (h ▸ han)
    rw [hS b _ hb, hS a n han] at h1
    omega
  rw [hbd] at htot
  have := congrArg Complex.im htot
  rw [Complex.add_im, im_sum_hermitian_eq_zero _ h hherm g, zero_add] at this
  rw [this]
  simp [← Complex.ofReal_pow, ← Complex.ofReal_sum]

/-- Grade sums of a square-summable vector are summable. -/
lemma summable_gradeSum (hS : ∀ a n, a ∈ S n → gr a = n) (f : β → ℝ) (hf0 : ∀ a, 0 ≤ f a)
    (hf : Summable f) : Summable fun n => ∑ a ∈ S n, f a := by
  refine summable_of_sum_range_le (fun n => Finset.sum_nonneg fun a _ => hf0 a)
    (c := ∑' a, f a) fun M => ?_
  rw [← Finset.sum_biUnion]
  · exact hf.sum_le_tsum _ fun a _ => hf0 a
  · intro n _ m _ hnm
    rw [Function.onFun, Finset.disjoint_left]
    intro a h1 h2
    exact hnm ((hS a n h1).symm.trans (hS a m h2))

/-- **Carleman's criterion for block Jacobi matrices.** Let `H` be a Hermitian matrix coupling only
neighbouring grades, with finite grades, arbitrary diagonal blocks, and off-diagonal blocks between
grades `n` and `n + 1` whose row and column sums are bounded by `r n`. If `Σ 1 / r n` diverges, the
equation `H g = i c g` with `c ≠ 0` has no nonzero square-summable solution. -/
theorem blockJacobi_no_l2_solution (hS : ∀ a n, a ∈ S n → gr a = n) (h : β → β → ℂ)
    (hherm : ∀ a b, h b a = starRingEnd ℂ (h a b))
    (hband : ∀ a b, h a b ≠ 0 → gr b ≤ gr a + 1 ∧ gr a ≤ gr b + 1) (r : ℕ → ℝ)
    (hr : ∀ n, 0 < r n) (hrow : ∀ n, ∀ a ∈ S n, ∑ b ∈ S (n + 1), ‖h a b‖ ≤ r n)
    (hcol : ∀ n, ∀ b ∈ S (n + 1), ∑ a ∈ S n, ‖h a b‖ ≤ r n) (hdiv : ¬ Summable fun n => 1 / r n)
    {c : ℝ} (hc : c ≠ 0) (g : β → ℂ) (hg : Summable fun a => ‖g a‖ ^ 2)
    (hcov : ∀ a, g a ≠ 0 → a ∈ S (gr a))
    (heq : ∀ a, a ∈ S (gr a) →
      ∑ b ∈ gradeLe S (gr a + 1), h a b * g b = Complex.I * c * g a) (a : β) :
    g a = 0 := by
  by_contra ha
  set G : ℕ → ℝ := fun n => ∑ a ∈ S n, ‖g a‖ ^ 2
  set ε := ‖g a‖ ^ 2
  have hε : 0 < ε := by positivity
  -- from grade `gr a` on, the flux is bounded below
  have hbound : ∀ N, gr a ≤ N → 2 * (|c| * ε) / r N ≤ G N + G (N + 1) := by
    intro N hN
    have hflux := blockJacobi_flux hS h hherm hband c g heq N
    have hW : ε ≤ ∑ b ∈ gradeLe S N, ‖g b‖ ^ 2 :=
      Finset.single_le_sum (f := fun b => ‖g b‖ ^ 2) (fun b _ => by positivity)
        (subset_gradeLe hN (hcov a ha))
    have hsch := norm_sum_conj_mul_le (S N) (S (N + 1)) h g g (r N) (hrow N) (hcol N)
    have h1 : |c| * ε ≤ r N * (G N + G (N + 1)) / 2 := by
      calc |c| * ε ≤ |c * ∑ b ∈ gradeLe S N, ‖g b‖ ^ 2| := by
            rw [abs_mul, abs_of_nonneg (a := ∑ b ∈ gradeLe S N, ‖g b‖ ^ 2)
              (Finset.sum_nonneg fun _ _ => by positivity)]
            exact mul_le_mul_of_nonneg_left hW (abs_nonneg c)
        _ ≤ _ := by rw [hflux]; exact (Complex.abs_im_le_norm _).trans hsch
    rw [div_le_iff₀ (hr N)]
    linarith
  apply hdiv
  have hGs := summable_gradeSum hS (fun b => ‖g b‖ ^ 2) (fun _ => by positivity) hg
  have hsum2 : Summable fun N => G N + G (N + 1) := hGs.add ((summable_nat_add_iff 1).mpr hGs)
  rw [← summable_nat_add_iff (gr a)]
  have hcε : 0 < 2 * (|c| * ε) := by have := abs_pos.mpr hc; positivity
  refine Summable.of_nonneg_of_le (fun N => (one_div_pos.mpr (hr _)).le) (fun N => ?_)
    (((summable_nat_add_iff (gr a)).mpr hsum2).mul_left (1 / (2 * (|c| * ε))))
  have := hbound (N + gr a) (by omega)
  rw [div_le_iff₀ (hr _)] at this
  show 1 / r (N + gr a) ≤ 1 / (2 * (|c| * ε)) * (G (N + gr a) + G (N + gr a + 1))
  rw [div_le_iff₀ (hr _)]
  calc (1 : ℝ) = 1 / (2 * (|c| * ε)) * (2 * (|c| * ε)) := by field_simp
    _ ≤ 1 / (2 * (|c| * ε)) * ((G (N + gr a) + G (N + gr a + 1)) * r (N + gr a)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

end Block

end InfiniteBosons
