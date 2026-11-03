/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.QuadratureSelfAdjoint
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FieldOperator
/-!

# Single-mode field operators are essentially self-adjoint

The operator `c₀ a_x + c̄₀ a_x†` is essentially self-adjoint for every `c₀ ≠ 0`.

## i. Overview

The single-mode term of the field operator `φ(f)` has the form `c₀ a_x + c̄₀ a_x†`. It acts on the
occupation line of the mode `x` as a Jacobi matrix with complex off-diagonal entries
`c₀ √(n+1)` and `c̄₀ √(n+1)`. The phase of `c₀` is removed by the gauge transformation
`w_n = λ̄^n u_n` with `λ = c₀/|c₀|`. The result is the real Jacobi matrix with entries
`|c₀| √(n+1)`. Carleman's criterion applies as for the quadrature `a_x + a_x†`. The deficiency
vectors vanish, so the range of the operator shifted by `± i` is dense. Hence the operator is
essentially self-adjoint in the sense of Physlib. The lattice is arbitrary.

## ii. Key results

- `InfiniteBosons.fieldTerm_orth_eq_zero`: the deficiency vectors vanish.
- `InfiniteBosons.fieldTerm_dense_range`: the shifted range is dense.
- `InfiniteBosons.fieldTerm_isEssentiallySelfAdjoint`: essential self-adjointness.
- `InfiniteBosons.fieldTerm_resolvent`: the bounded resolvent.

## iii. Table of contents

- A. The orthogonality equation
- B. Gauge and Carleman
- C. Essential self-adjointness

## iv. References

* M. Reed, B. Simon, Methods of Modern Mathematical Physics II, Section X.6.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

lemma fieldTerm_single (x : L) (c0 : ℂ) (α : Occ L) :
    (fieldTerm x c0).1.1 (single α 1) =
      single (α - single x 1) (c0 * ((Real.sqrt (α x) : ℝ) : ℂ)) +
      single (α + single x 1) (starRingEnd ℂ c0 * ((Real.sqrt (α x + 1) : ℝ) : ℂ)) := by
  show c0 • ann x (single α 1) + starRingEnd ℂ c0 • cre x (single α 1) = _
  rw [ann_single, cre_single]
  simp [Finsupp.smul_single]

lemma orth_eq_field (x : L) (c0 : ℂ) (c : ℝ) (g : HilbertSp (Occ L)) (α : Occ L)
    (h : inner ℂ g (shiftMap (fieldTerm x c0).1.1 c (single α 1)) = 0) :
    (c0 * (Real.sqrt (α x) : ℂ)) * starRingEnd ℂ (g (α - single x 1)) +
      (starRingEnd ℂ c0 * (Real.sqrt (α x + 1) : ℂ)) * starRingEnd ℂ (g (α + single x 1)) +
      (Complex.I * c) * starRingEnd ℂ (g α) = 0 := by
  have hs : shiftMap (fieldTerm x c0).1.1 c (single α 1) =
      (lp.single 2 (α - single x 1) (c0 * ((Real.sqrt (α x) : ℝ) : ℂ)) : HilbertSp (Occ L)) +
      (lp.single 2 (α + single x 1) (starRingEnd ℂ c0 * ((Real.sqrt (α x + 1) : ℝ) : ℂ)) :
        HilbertSp (Occ L)) +
      ((Complex.I * c : ℂ)) • (lp.single 2 α (1 : ℂ) : HilbertSp (Occ L)) := by
    have e1 : shiftMap (fieldTerm x c0).1.1 c (single α 1) =
        embed ((fieldTerm x c0).1.1 (single α 1)) + ((Complex.I * c : ℂ)) • embed (single α 1) := by
      simp only [shiftMap, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_add, map_smul]
    rw [e1, fieldTerm_single, map_add, embed_single, embed_single, embed_single]
  rw [hs, inner_add_right, inner_add_right, inner_smul_right, lp.inner_single_right,
    lp.inner_single_right, lp.inner_single_right] at h
  simp only [RCLike.inner_apply, mul_one] at h
  linear_combination h


lemma not_summable_inv_sqrt : ¬ Summable fun n : ℕ => 1 / Real.sqrt ((n : ℝ) + 1) := by
  intro hs
  have h1 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
    have hle : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have hs1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := Real.one_le_sqrt.mpr this
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (n : ℝ) + 1 by linarith)]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) hle
  have h2 : Summable fun n : ℕ => 1 / (n : ℝ) := by
    rw [← summable_nat_add_iff 1]
    simpa using h1
  exact Real.not_summable_one_div_natCast h2

/-- **Vanishing of the deficiency vectors of `c₀ a_x + c̄₀ a_x†`** for `c₀ ≠ 0`. -/
theorem fieldTerm_orth_eq_zero (x : L) {c0 : ℂ} (hc0 : c0 ≠ 0) {c : ℝ} (hc : c ≠ 0)
    (g : HilbertSp (Occ L))
    (h : ∀ α, inner ℂ g (shiftMap (fieldTerm x c0).1.1 c (single α 1)) = 0) : g = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : ℝ, ‖c0‖ = N := ⟨_, rfl⟩
  have hn0 : 0 < N := hN ▸ norm_pos_iff.mpr hc0
  have hcn : (N : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  obtain ⟨lam, hlam⟩ : ∃ lam : ℂ, c0 = (N : ℂ) * lam := ⟨c0 / N, by field_simp⟩
  have hlam1 : ‖lam‖ = 1 := by
    have : ‖c0‖ = N * ‖lam‖ := by rw [hlam, norm_mul]; simp [abs_of_pos hn0]
    rw [hN] at this
    have := mul_left_cancel₀ hn0.ne' (this.symm.trans (mul_one N).symm)
    exact this
  have hlamc : starRingEnd ℂ lam * lam = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hlam1]; simp
  have hlne : lam ≠ 0 := by intro h0; rw [h0] at hlam1; simp at hlam1
  have hc0c : starRingEnd ℂ c0 = (N : ℂ) * starRingEnd ℂ lam := by
    rw [hlam]; simp [map_mul, Complex.conj_ofReal]
  have hfiber : ∀ (ρ : Occ L) (n : ℕ), g (ρ.update x n) = 0 := by
    intro ρ
    set u : ℕ → ℂ := fun n => starRingEnd ℂ (g (ρ.update x n)) with hu
    set w : ℕ → ℂ := fun n => (starRingEnd ℂ lam) ^ n * u n with hw
    have hsq : Summable fun n => ‖w n‖ ^ 2 := by
      have h1 := sq_summable g
      have hinj : Function.Injective fun n : ℕ => ρ.update x n := fun n m hnm => by
        have := congrArg (fun f : Occ L => f x) hnm
        simpa using this
      have h2 := h1.comp_injective hinj
      refine h2.congr fun n => ?_
      simp only [Function.comp, hw, hu, norm_mul, norm_pow, RCLike.norm_conj, hlam1, one_pow,
        one_mul, Real.rpow_two]
    have huw : ∀ k, u k = lam ^ k * w k := fun k => by
      simp only [hw]
      rw [← mul_assoc, ← mul_pow, mul_comm lam, hlamc, one_pow, one_mul]
    have hcore : ∀ n : ℕ, (N : ℂ) * (Real.sqrt ((n + 1 : ℕ) + 1) : ℝ) * w (n + 2) +
        (N : ℂ) * (Real.sqrt ((n : ℕ) + 1) : ℝ) * w n = -(Complex.I * c) * w (n + 1) := by
      intro n
      have h1 := orth_eq_field x c0 c g (ρ.update x (n + 1)) (h _)
      rw [update_pred, update_succ] at h1
      simp only [update_x] at h1
      have h2 : (c0 * ((Real.sqrt (((n + 1 : ℕ) : ℝ))) : ℂ)) * u n +
          (starRingEnd ℂ c0 * ((Real.sqrt (((n + 1 : ℕ) : ℝ) + 1)) : ℂ)) * u (n + 2) +
          (Complex.I * c) * u (n + 1) = 0 := h1
      rw [hc0c, hlam, huw n, huw (n + 1), huw (n + 2)] at h2
      refine mul_left_cancel₀ (pow_ne_zero (n + 1) hlne) ?_
      push_cast at h2 ⊢
      linear_combination h2 - ((N : ℂ) * (Real.sqrt ((n : ℝ) + 1 + 1) : ℝ) * w (n + 2) *
        lam ^ (n + 1)) * hlamc
    have h0 : ((Real.sqrt ((0 : ℕ) + 1) : ℝ) : ℂ) * w 1 = -(Complex.I * ((c / N : ℝ) : ℂ)) * w 0 := by
      have h1 := orth_eq_field x c0 c g (ρ.update x 0) (h _)
      rw [update_succ] at h1
      simp only [update_x, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, mul_zero,
        zero_mul, zero_add] at h1
      have h2 : (starRingEnd ℂ c0) * u 1 + (Complex.I * c) * u 0 = 0 := by simpa using h1
      rw [hc0c, huw 1, huw 0] at h2
      simp only [Nat.cast_zero, zero_add, Real.sqrt_one, Complex.ofReal_one, one_mul, pow_one,
        pow_zero]
      push_cast at h2 ⊢
      field_simp
      linear_combination h2 - ((N : ℂ) * w 1) * hlamc
    have hrec : ∀ n : ℕ, ((Real.sqrt (((n + 1 : ℕ) : ℝ) + 1) : ℝ) : ℂ) * w (n + 2) +
        ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * w n =
          -(Complex.I * ((c / N : ℝ) : ℂ)) * w (n + 1) := by
      intro n
      have := hcore n
      push_cast at this ⊢
      field_simp
      linear_combination this
    have hres := jacobi_no_l2_solution (fun n => Real.sqrt ((n : ℝ) + 1)) (fun n => by positivity)
      not_summable_inv_sqrt (c / N) (div_ne_zero hc hn0.ne') w hsq h0 hrec
    intro n
    have hw0 := hres n
    have := huw n
    rw [hw0, mul_zero] at this
    simpa [hu] using this
  ext α
  have := hfiber α (α x)
  simpa using this

/-- The range of `c₀ a_x + c̄₀ a_x† + i c` is dense. -/
theorem fieldTerm_dense_range (x : L) {c0 : ℂ} (hc0 : c0 ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    Dense (LinearMap.range (shiftMap (fieldTerm x c0).1.1 c) : Set (HilbertSp (Occ L))) := by
  refine dense_of_orth _ fun g hg => fieldTerm_orth_eq_zero x hc0 hc g fun α => ?_
  exact hg _ ⟨single α 1, rfl⟩

/-- **Every single-mode field operator `c₀ a_x + c̄₀ a_x†` is essentially self-adjoint** on the
algebraic Fock space of an arbitrary lattice. -/
theorem fieldTerm_isEssentiallySelfAdjoint (x : L) {c0 : ℂ} (hc0 : c0 ≠ 0) :
    (polyOp (fieldTerm x c0)).IsEssentiallySelfAdjoint :=
  polyOp_isEssentiallySelfAdjoint _ (star_fieldTerm x c0) (fieldTerm_dense_range x hc0 one_ne_zero)
    (fieldTerm_dense_range x hc0 (by norm_num))

/-- The bounded resolvent of a single-mode field operator. -/
theorem fieldTerm_resolvent (x : L) {c0 : ℂ} (hc0 : c0 ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    ∃ R : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L), ‖R‖ ≤ 1 / |c| ∧
      ∀ f, R (shiftMap (fieldTerm x c0).1.1 c f) = embed f :=
  polyOp_resolvent (fieldTerm x c0) (star_fieldTerm x c0) hc (fieldTerm_dense_range x hc0 hc)

end InfiniteBosons
