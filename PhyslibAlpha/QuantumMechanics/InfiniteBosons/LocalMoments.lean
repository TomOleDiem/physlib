/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FiniteVolume
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.MomentBound
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Analysis.SpecialFunctions.Exp
/-!

# Local occupation moments under hopping and pairing

Estimates on the change of the local moments `(N_x + 1)^p` under one hopping or pairing move.

## i. Overview

A hopping or pairing move on a bond `x ~ y` changes the occupations of `x` and `y` by at most one
each. Its amplitude is a product of two square roots of occupations, hence at most
`(n_x + 1) + (n_y + 1)`. The change of `(n + 1)^p` under `n ↦ n ± 1` is at most
`p 2^{p-1} (n + 1)^{p-1}`. Together with `(X + Y) X^{p-1} ≤ 2 (X^p + Y^p)` the product of the
amplitude and the change of a local moment is at most `p 2^p ((n_x + 1)^p + (n_y + 1)^p)`. These
are the scalar inequalities behind the commutator bound of the moment Grönwall argument
(Deuchert-Lampart-Lemm, eqs. (52)-(53)), extended to pairing.

## ii. Key results

- `InfiniteBosons.mul_pow_le_two_mul`: `(X + Y) X^{p-1} ≤ 2 (X^p + Y^p)`.
- `InfiniteBosons.abs_succ_pow_sub_le`: the change of `(n + 1)^p` under a unit step.
- `InfiniteBosons.amp_mul_diff_le`: the amplitude times the change of a moment.
- `InfiniteBosons.BoseHubbardData.sum_finiteHam_le`: the row bound of `H_Λ` against the weighted
  moment.
- `InfiniteBosons.BoseHubbardData.truncated_moment_le`: Grönwall for the weighted moment.
- `InfiniteBosons.BoseHubbardData.truncated_localMoment_uniform`: the uniform local moment bound.

## iii. Table of contents

- A. Scalar inequalities
- B. The weighted moment
- C. The partners of a basis state under one move
- D. The row bound of one bond
- E. Counting bonds
- F. The row bound of the finite-volume Hamiltonian
- G. The moment bound in a truncated volume
- H. Exponential weights on graphs of polynomial growth
- I. The uniform moment bound in a truncated volume

## iv. References

* A. Deuchert, J. Lampart, M. Lemm, Dynamics and equilibrium states of infinite systems of lattice
  bosons, arXiv:2505.13170, Proposition 4.10.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

/-!

## A. Scalar inequalities

-/

/-- `(X + Y) X^{p-1} ≤ 2 (X^p + Y^p)` for nonnegative `X`, `Y`. -/
lemma mul_pow_le_two_mul {X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (p : ℕ) :
    (X + Y) * X ^ p ≤ 2 * (X ^ (p + 1) + Y ^ (p + 1)) := by
  have e : (X + Y) * X ^ p = X ^ (p + 1) + Y * X ^ p := by ring
  rw [e]
  have hX' := pow_nonneg hX (p + 1)
  have hY' := pow_nonneg hY (p + 1)
  rcases le_total Y X with h | h
  · have : Y * X ^ p ≤ X ^ (p + 1) := by
      rw [pow_succ']; exact mul_le_mul_of_nonneg_right h (by positivity)
    linarith
  · have h1 : Y * X ^ p ≤ Y ^ (p + 1) := by
      rw [pow_succ']; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX h p) hY
    linarith

/-- The change of `(n + 1)^{p+1}` under `n ↦ n + 1` is at most `(p + 1) 2^p (n + 1)^p`. -/
lemma succ_pow_sub_le (n : ℝ) (hn : 0 ≤ n) (p : ℕ) :
    (n + 2) ^ (p + 1) - (n + 1) ^ (p + 1) ≤ (p + 1) * 2 ^ p * (n + 1) ^ p := by
  have hgeo : (n + 2) ^ (p + 1) - (n + 1) ^ (p + 1) ≤ (p + 1) * (n + 2) ^ p := by
    have := Commute.geom_sum₂_mul (Commute.all (n + 2) (n + 1)) (p + 1)
    have hsum : ∑ i ∈ Finset.range (p + 1), (n + 2) ^ i * (n + 1) ^ (p - i) ≤
        ∑ i ∈ Finset.range (p + 1), (n + 2) ^ p := Finset.sum_le_sum fun i hi => by
      have hi' : i ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc (n + 2) ^ i * (n + 1) ^ (p - i) ≤ (n + 2) ^ i * (n + 2) ^ (p - i) :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) _)
              (by positivity)
        _ = (n + 2) ^ p := by rw [← pow_add, Nat.add_sub_cancel' hi']
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    push_cast at hsum
    simp only [Nat.add_sub_cancel, show n + 2 - (n + 1) = (1 : ℝ) by ring, mul_one] at this
    linarith
  have h2 : (n + 2) ^ p ≤ 2 ^ p * (n + 1) ^ p := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) p
  nlinarith [h2]

/-- **The amplitude times the change of a moment.** If the amplitude is at most `X + Y` and the
moment changes by at most `(p + 1) 2^p X^p`, their product is at most
`(p + 1) 2^{p+1} (X^{p+1} + Y^{p+1})`. -/
lemma amp_mul_diff_le {X Y amp δ : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (p : ℕ)
    (hamp : amp ≤ X + Y) (hδ0 : 0 ≤ δ) (hδ : δ ≤ (p + 1) * 2 ^ p * X ^ p) :
    amp * δ ≤ (p + 1) * 2 ^ (p + 1) * (X ^ (p + 1) + Y ^ (p + 1)) := by
  have h1 : amp * δ ≤ (X + Y) * ((p + 1) * 2 ^ p * X ^ p) :=
    mul_le_mul hamp hδ hδ0 (by positivity)
  have h2 := mul_pow_le_two_mul hX hY p
  have hc : (0 : ℝ) ≤ (p + 1) * 2 ^ p := by positivity
  calc amp * δ ≤ (X + Y) * ((p + 1) * 2 ^ p * X ^ p) := h1
    _ = (p + 1) * 2 ^ p * ((X + Y) * X ^ p) := by ring
    _ ≤ (p + 1) * 2 ^ p * (2 * (X ^ (p + 1) + Y ^ (p + 1))) := mul_le_mul_of_nonneg_left h2 hc
    _ = _ := by ring


/-- The change of `(n + 1)^{p+1}` under `n ↦ n - 1` is at most `(p + 1) 2^p (n + 1)^p`. -/
lemma pow_sub_pred_pow_le (n : ℝ) (hn : 1 ≤ n) (p : ℕ) :
    (n + 1) ^ (p + 1) - n ^ (p + 1) ≤ (p + 1) * 2 ^ p * (n + 1) ^ p := by
  have h := succ_pow_sub_le (n - 1) (by linarith) p
  have e1 : n - 1 + 2 = n + 1 := by ring
  have e2 : n - 1 + 1 = n := by ring
  rw [e1, e2] at h
  have h2 : n ^ p ≤ (n + 1) ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
  have hc : (0 : ℝ) ≤ (p + 1) * 2 ^ p := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hc]

/-- A product of two square roots of occupations is at most the sum of the shifted occupations. -/
lemma sqrt_mul_sqrt_le_add {a b X Y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haX : a ≤ X) (hbY : b ≤ Y) :
    Real.sqrt a * Real.sqrt b ≤ X + Y := by
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]


/-- The change of `(n + 1)^{p+1}` under a step of size at most one. -/
lemma abs_moment_step_le {n m : ℕ} (h1 : m ≤ n + 1) (h2 : n ≤ m + 1) (p : ℕ) :
    |((m : ℝ) + 1) ^ (p + 1) - ((n : ℝ) + 1) ^ (p + 1)| ≤ (p + 1) * 2 ^ p * ((n : ℝ) + 1) ^ p := by
  have hc : (0 : ℝ) ≤ (p + 1) * 2 ^ p * ((n : ℝ) + 1) ^ p := by positivity
  rcases (show m = n + 1 ∨ m = n ∨ m + 1 = n by omega) with h | h | h
  · subst h
    have := succ_pow_sub_le (n : ℝ) (by positivity) p
    have hle : ((n : ℝ) + 1) ^ (p + 1) ≤ ((n : ℝ) + 2) ^ (p + 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    push_cast
    rw [show ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 by ring, abs_of_nonneg (by linarith)]
    linarith
  · subst h; simpa using hc
  · subst h
    have := pow_sub_pred_pow_le ((m : ℝ) + 1) (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]) p
    have hle : ((m : ℝ) + 1) ^ (p + 1) ≤ ((m : ℝ) + 1 + 1) ^ (p + 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    rw [abs_sub_comm, abs_of_nonneg (by push_cast; linarith)]
    push_cast
    linarith

/-!

## B. The weighted moment

-/

variable {L : Type*} [DecidableEq L]

/-- The local moment `(N_z + 1)^{p+1}` of a basis state. -/
def localMoment (p : ℕ) (z : L) (α : Occ L) : ℝ := ((α z : ℝ) + 1) ^ (p + 1)

/-- The weighted moment `Σ_{z∈Λ} w_z (N_z + 1)^{p+1}` of a basis state. -/
def weightedMoment (Λ : Finset L) (w : L → ℝ) (p : ℕ) (α : Occ L) : ℝ :=
  ∑ z ∈ Λ, w z * localMoment p z α

/-- If two states differ only at `x` and `y`, so do their weighted moments. -/
lemma weightedMoment_sub {Λ : Finset L} (w : L → ℝ) (p : ℕ) {x y : L} (hxy : x ≠ y) (hx : x ∈ Λ)
    (hy : y ∈ Λ) {α β : Occ L} (hout : ∀ z, z ≠ x → z ≠ y → β z = α z) :
    weightedMoment Λ w p β - weightedMoment Λ w p α =
      w x * (localMoment p x β - localMoment p x α) +
        w y * (localMoment p y β - localMoment p y α) := by
  unfold weightedMoment
  rw [← Finset.sum_sub_distrib, ← Finset.add_sum_erase _ _ hx,
    ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩),
    Finset.sum_eq_zero fun z hz => ?_]
  · ring
  · obtain ⟨hzy, hz'⟩ := Finset.mem_erase.mp hz
    obtain ⟨hzx, -⟩ := Finset.mem_erase.mp hz'
    simp [localMoment, hout z hzx hzy]

/-- **One move changes the weighted moment by a controlled amount.** For a move on `x ~ y` that
changes each occupation by at most one and has amplitude at most `(n_x + 1) + (n_y + 1)`, the
amplitude times the change of the weighted moment is at most
`(p + 1) 2^{p+1} (w_x + w_y) ((n_x + 1)^{p+1} + (n_y + 1)^{p+1})`. -/
lemma move_mul_le {Λ : Finset L} (w : L → ℝ) (hw : ∀ z, 0 ≤ w z) (p : ℕ) {x y : L} (hxy : x ≠ y)
    (hx : x ∈ Λ) (hy : y ∈ Λ) {α β : Occ L} (hout : ∀ z, z ≠ x → z ≠ y → β z = α z)
    (hsx : β x ≤ α x + 1 ∧ α x ≤ β x + 1) (hsy : β y ≤ α y + 1 ∧ α y ≤ β y + 1) {amp : ℝ}
    (hamp : amp ≤ ((α x : ℝ) + 1) + ((α y : ℝ) + 1)) :
    amp * |weightedMoment Λ w p β - weightedMoment Λ w p α| ≤
      (p + 1) * 2 ^ (p + 1) * (w x + w y) * (localMoment p x α + localMoment p y α) := by
  rw [weightedMoment_sub w p hxy hx hy hout]
  have hδx := abs_moment_step_le hsx.1 hsx.2 p
  have hδy := abs_moment_step_le hsy.1 hsy.2 p
  have hXY : (0 : ℝ) ≤ ((α x : ℝ) + 1) := by positivity
  have hYX : (0 : ℝ) ≤ ((α y : ℝ) + 1) := by positivity
  have ex := amp_mul_diff_le (amp := amp) hXY hYX p hamp (abs_nonneg _) hδx
  have ey := amp_mul_diff_le (amp := amp) hYX hXY p (by linarith) (abs_nonneg _) hδy
  have habs : |w x * (localMoment p x β - localMoment p x α) +
      w y * (localMoment p y β - localMoment p y α)| ≤
      w x * |localMoment p x β - localMoment p x α| +
        w y * |localMoment p y β - localMoment p y α| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (hw x), abs_of_nonneg (hw y)]
  by_cases hamp0 : amp ≤ 0
  · have : amp * |w x * (localMoment p x β - localMoment p x α) +
        w y * (localMoment p y β - localMoment p y α)| ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hamp0 (abs_nonneg _)
    refine this.trans ?_
    unfold localMoment; have := hw x; have := hw y; positivity
  push Not at hamp0
  calc _ ≤ amp * (w x * |localMoment p x β - localMoment p x α| +
        w y * |localMoment p y β - localMoment p y α|) :=
        mul_le_mul_of_nonneg_left habs hamp0.le
    _ = w x * (amp * |localMoment p x β - localMoment p x α|) +
        w y * (amp * |localMoment p y β - localMoment p y α|) := by ring
    _ ≤ w x * ((p + 1) * 2 ^ (p + 1) * (((α x : ℝ) + 1) ^ (p + 1) + ((α y : ℝ) + 1) ^ (p + 1))) +
        w y * ((p + 1) * 2 ^ (p + 1) * (((α y : ℝ) + 1) ^ (p + 1) + ((α x : ℝ) + 1) ^ (p + 1))) :=
        add_le_add (mul_le_mul_of_nonneg_left (by simpa [localMoment] using ex) (hw x))
          (mul_le_mul_of_nonneg_left (by simpa [localMoment] using ey) (hw y))
    _ = _ := by unfold localMoment; ring


/-!

## C. The partners of a basis state under one move

-/

/-- The properties of a move from `β` to `α` on the bond `x ~ y` used in `move_mul_le`. -/
structure IsMove (x y : L) (α β : Occ L) (amp : ℝ) : Prop where
  out : ∀ z, z ≠ x → z ≠ y → β z = α z
  step_x : β x ≤ α x + 1 ∧ α x ≤ β x + 1
  step_y : β y ≤ α y + 1 ∧ α y ≤ β y + 1
  amp_le : amp ≤ ((α x : ℝ) + 1) + ((α y : ℝ) + 1)

lemma norm_sqrt_mul_sqrt (a b : ℝ) :
    ‖((Real.sqrt a : ℝ) : ℂ) * (((Real.sqrt b : ℝ) : ℂ) * 1)‖ = Real.sqrt a * Real.sqrt b := by
  rw [mul_one, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

/-- Hopping from `y` to `x`: the partner is `α + e_y - e_x`. -/
lemma isMove_cre_ann {x y : L} (hxy : x ≠ y) {α β : Occ L}
    (h : cre x (ann y (single β (1 : ℂ))) α ≠ 0) :
    β = α + single y 1 - single x 1 ∧ IsMove x y α β ‖cre x (ann y (single β (1 : ℂ))) α‖ := by
  have hval := h
  rw [ann_single, cre_single] at h
  obtain ⟨hα, hc⟩ := single_apply_ne' h
  have hby : 1 ≤ β y := by
    by_contra h0; apply hc; simp [show β y = 0 by omega]
  have e : α + single y 1 = β + single x 1 := by
    rw [hα, add_right_comm, tsub_add_cancel_of_le ((single_le_iff' y β).mpr hby)]
  have hz : ∀ z, α z + (if y = z then 1 else 0) = β z + (if x = z then 1 else 0) := fun z => by
    have := congrArg (· z) e
    simpa [Finsupp.single_apply] using this
  have hx := hz x; have hy := hz y
  simp only [hxy, Ne.symm hxy, if_true, if_false, add_zero] at hx hy
  refine ⟨by rw [e, add_tsub_cancel_right], fun z hzx hzy => ?_, by omega, by omega, ?_⟩
  · have := hz z; simp [Ne.symm hzx, Ne.symm hzy] at this; omega
  · rw [ann_single, cre_single, ← hα, Finsupp.single_eq_same,
      norm_sqrt_mul_sqrt]
    have hbx : (β - single y 1 : Occ L) x = β x := by simp [hxy.symm]
    rw [hbx]
    apply sqrt_mul_sqrt_le_add (by positivity) (by positivity)
    · have : (β x : ℝ) + 1 = α x := by exact_mod_cast (show β x + 1 = α x by omega)
      linarith
    · have : (β y : ℝ) = α y + 1 := by exact_mod_cast (show β y = α y + 1 by omega)
      linarith


/-- Pair creation on `x`, `y`: the partner is `α - e_x - e_y`. -/
lemma isMove_cre_cre {x y : L} (hxy : x ≠ y) {α β : Occ L}
    (h : cre x (cre y (single β (1 : ℂ))) α ≠ 0) :
    β = α - single x 1 - single y 1 ∧ IsMove x y α β ‖cre x (cre y (single β (1 : ℂ))) α‖ := by
  rw [cre_single, cre_single] at h
  obtain ⟨hα, -⟩ := single_apply_ne' h
  have hz : ∀ z, α z = β z + (if y = z then 1 else 0) + (if x = z then 1 else 0) := fun z => by
    rw [hα]; simp [Finsupp.single_apply]
  have hx := hz x; have hy := hz y
  simp only [hxy, Ne.symm hxy, if_true, if_false, add_zero] at hx hy
  refine ⟨?_, fun z hzx hzy => ?_, by omega, by omega, ?_⟩
  · rw [hα, add_tsub_cancel_right, add_tsub_cancel_right]
  · have := hz z; simp [Ne.symm hzx, Ne.symm hzy] at this; omega
  · rw [cre_single, cre_single, ← hα, Finsupp.single_eq_same,
      norm_sqrt_mul_sqrt]
    have hbx : (β + single y 1 : Occ L) x = β x := by simp [hxy.symm]
    rw [hbx]
    apply sqrt_mul_sqrt_le_add (by positivity) (by positivity)
    · have : (β x : ℝ) + 1 = α x := by exact_mod_cast (show β x + 1 = α x by omega)
      linarith
    · have : (β y : ℝ) + 1 = α y := by exact_mod_cast (show β y + 1 = α y by omega)
      linarith

/-- Pair annihilation on `x`, `y`: the partner is `α + e_y + e_x`. -/
lemma isMove_ann_ann {x y : L} (hxy : x ≠ y) {α β : Occ L}
    (h : ann y (ann x (single β (1 : ℂ))) α ≠ 0) :
    β = α + single y 1 + single x 1 ∧ IsMove x y α β ‖ann y (ann x (single β (1 : ℂ))) α‖ := by
  have hβ := eq_add_of_ann_ann_ne h
  have hz : ∀ z, β z = α z + (if y = z then 1 else 0) + (if x = z then 1 else 0) := fun z => by
    rw [hβ]; simp [Finsupp.single_apply]
  have hx := hz x; have hy := hz y
  simp only [hxy, Ne.symm hxy, if_true, if_false, add_zero] at hx hy
  refine ⟨hβ, fun z hzx hzy => ?_, by omega, by omega, ?_⟩
  · have := hz z; simp [Ne.symm hzx, Ne.symm hzy] at this; omega
  · rw [ann_ann_single_apply]
    split_ifs
    · rw [norm_sqrt_mul_sqrt]
      have hby : (β - single x 1 : Occ L) y = β y := by simp [hxy]
      rw [hby, add_comm ((α x : ℝ) + 1)]
      apply sqrt_mul_sqrt_le_add (by positivity) (by positivity)
      · have : (β y : ℝ) = α y + 1 := by exact_mod_cast (show β y = α y + 1 by omega)
        linarith
      · have : (β x : ℝ) = α x + 1 := by exact_mod_cast (show β x = α x + 1 by omega)
        linarith
    · simp only [norm_zero]; positivity


omit [DecidableEq L] in
lemma IsMove.symm {x y : L} {α β : Occ L} {amp : ℝ} (h : IsMove y x α β amp) :
    IsMove x y α β amp :=
  ⟨fun z hzx hzy => h.out z hzy hzx, h.step_y, h.step_x, by linarith [h.amp_le]⟩

/-!

## D. The row bound of one bond

-/

/-- A move with a unique partner contributes at most the bound of `move_mul_le` to a row sum. -/
lemma sum_move_le (S : Finset (Occ L)) {Λ : Finset L} (w : L → ℝ) (hw : ∀ z, 0 ≤ w z) (p : ℕ)
    {x y : L} (hxy : x ≠ y) (hx : x ∈ Λ) (hy : y ∈ Λ) (α β0 : Occ L) (f : Occ L → ℂ)
    (hf : ∀ β, f β ≠ 0 → β = β0 ∧ IsMove x y α β ‖f β‖) :
    ∑ β ∈ S, ‖f β‖ * |weightedMoment Λ w p β - weightedMoment Λ w p α| ≤
      (p + 1) * 2 ^ (p + 1) * (w x + w y) * (localMoment p x α + localMoment p y α) := by
  refine (sum_le_of_eq_zero S _ (fun _ => by positivity) β0 fun β _ hβ => ?_).trans ?_
  · by_contra hne
    have : f β ≠ 0 := fun h0 => hne (by rw [h0, norm_zero, zero_mul])
    exact hβ (hf β this).1
  · by_cases h0 : f β0 = 0
    · rw [h0, norm_zero, zero_mul]
      unfold localMoment; have := hw x; have := hw y; positivity
    · obtain ⟨-, hm⟩ := hf β0 h0
      exact move_mul_le w hw p hxy hx hy hm.out hm.step_x hm.step_y hm.amp_le

namespace BoseHubbardData

variable (D : BoseHubbardData L)

/-- **Row bound of one bond.** The matrix elements of a bond term times the change of the weighted
moment sum to at most `4 K (p + 1) 2^{p+1} (w_x + w_y) ((n_x + 1)^{p+1} + (n_y + 1)^{p+1})` along
each row, where `K` bounds the hopping and pairing amplitudes of the bond. -/
lemma sum_bondTerm_le (S : Finset (Occ L)) {Λ : Finset L} (w : L → ℝ) (hw : ∀ z, 0 ≤ w z)
    (p : ℕ) {x y : L} (hx : x ∈ Λ) (hy : y ∈ Λ) {K : ℝ} (hJ : |D.J x y| ≤ K)
    (hΔ : ‖D.Δ x y‖ ≤ K) (α : Occ L) :
    ∑ β ∈ S, ‖matEl (D.bondTerm x y) α β‖ *
        |weightedMoment Λ w p β - weightedMoment Λ w p α| ≤
      4 * K * ((p + 1) * 2 ^ (p + 1) * (w x + w y) * (localMoment p x α + localMoment p y α)) := by
  classical
  set R := (p + 1) * 2 ^ (p + 1) * (w x + w y) * (localMoment p x α + localMoment p y α)
  set dA : Occ L → ℝ := fun β => |weightedMoment Λ w p β - weightedMoment Λ w p α|
  by_cases hadj : D.graph.Adj x y
  swap
  · refine (Finset.sum_eq_zero fun β _ => ?_).le.trans ?_
    · rw [matEl_bondTerm, if_neg hadj, norm_zero, zero_mul]
    · have hK : 0 ≤ K := (abs_nonneg _).trans hJ
      unfold R localMoment; have := hw x; have := hw y; positivity
  have hxy : x ≠ y := hadj.ne
  have hK : 0 ≤ K := (abs_nonneg _).trans hJ
  have hR1 := sum_move_le S w hw p hxy hx hy α _ (fun β => cre x (ann y (single β (1 : ℂ))) α)
    fun β h => isMove_cre_ann hxy h
  have hR2 := sum_move_le S w hw p hxy hx hy α _ (fun β => cre y (ann x (single β (1 : ℂ))) α)
    fun β h => ⟨(isMove_cre_ann hxy.symm h).1, (isMove_cre_ann hxy.symm h).2.symm⟩
  have hR3 := sum_move_le S w hw p hxy hx hy α _ (fun β => cre x (cre y (single β (1 : ℂ))) α)
    fun β h => isMove_cre_cre hxy h
  have hR4 := sum_move_le S w hw p hxy hx hy α _ (fun β => ann y (ann x (single β (1 : ℂ))) α)
    fun β h => isMove_ann_ann hxy h
  have hpt : ∀ β ∈ S, ‖matEl (D.bondTerm x y) α β‖ * dA β ≤
      K * (‖cre x (ann y (single β (1 : ℂ))) α‖ * dA β) +
        K * (‖cre y (ann x (single β (1 : ℂ))) α‖ * dA β) +
        K * (‖cre x (cre y (single β (1 : ℂ))) α‖ * dA β) +
        K * (‖ann y (ann x (single β (1 : ℂ))) α‖ * dA β) := by
    intro β _
    have hd : 0 ≤ dA β := abs_nonneg _
    rw [matEl_bondTerm, if_pos hadj]
    have hn : ‖((-D.J x y : ℝ) : ℂ) * (cre x (ann y (single β (1 : ℂ))) α +
        cre y (ann x (single β 1)) α) + D.Δ x y * cre x (cre y (single β 1)) α +
        starRingEnd ℂ (D.Δ x y) * ann y (ann x (single β 1)) α‖ ≤
        K * ‖cre x (ann y (single β (1 : ℂ))) α‖ + K * ‖cre y (ann x (single β (1 : ℂ))) α‖ +
        K * ‖cre x (cre y (single β (1 : ℂ))) α‖ + K * ‖ann y (ann x (single β (1 : ℂ))) α‖ := by
      refine (norm_add₃_le).trans ?_
      rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_neg]
      have h1 := norm_add_le (cre x (ann y (single β (1 : ℂ))) α) (cre y (ann x (single β 1)) α)
      nlinarith [norm_nonneg (cre x (ann y (single β (1 : ℂ))) α),
        norm_nonneg (cre y (ann x (single β (1 : ℂ))) α),
        norm_nonneg (cre x (cre y (single β (1 : ℂ))) α),
        norm_nonneg (ann y (ann x (single β (1 : ℂ))) α), abs_nonneg (D.J x y),
        norm_nonneg (D.Δ x y)]
    nlinarith [mul_le_mul_of_nonneg_right hn hd]
  refine (Finset.sum_le_sum hpt).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hR1 hK, mul_le_mul_of_nonneg_left hR2 hK,
    mul_le_mul_of_nonneg_left hR3 hK, mul_le_mul_of_nonneg_left hR4 hK]

end BoseHubbardData


/-!

## E. Counting bonds

-/

omit [DecidableEq L] in
lemma sum_ite_adj_le (Λ : Finset L) (G : SimpleGraph L) [DecidableRel G.Adj] {d : ℕ}
    (hd : ∀ x ∈ Λ, (Λ.filter (G.Adj x)).card ≤ d) (f : L → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ Λ, ∑ y ∈ Λ, (if G.Adj x y then f x else 0) ≤ d * ∑ x ∈ Λ, f x := by
  calc ∑ x ∈ Λ, ∑ y ∈ Λ, (if G.Adj x y then f x else 0) =
        ∑ x ∈ Λ, f x * (Λ.filter (G.Adj x)).card := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
          mul_comm]
    _ ≤ ∑ x ∈ Λ, f x * d := Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (by exact_mod_cast hd x hx) (hf x)
    _ = d * ∑ x ∈ Λ, f x := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring

omit [DecidableEq L] in
/-- **Counting the bonds of a region.** If each site has at most `d` neighbours in the region, a
sum over its bonds of `f x + f y` is at most `2 d Σ_x f x`. -/
lemma sum_adj_le (Λ : Finset L) (G : SimpleGraph L) [DecidableRel G.Adj] {d : ℕ}
    (hd : ∀ x ∈ Λ, (Λ.filter (G.Adj x)).card ≤ d) (f : L → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ Λ, ∑ y ∈ Λ, (if G.Adj x y then f x + f y else 0) ≤ 2 * d * ∑ x ∈ Λ, f x := by
  have hsplit : ∀ x y, (if G.Adj x y then f x + f y else 0) =
      (if G.Adj x y then f x else 0) + (if G.Adj y x then f y else 0) := fun x y => by
    by_cases h : G.Adj x y
    · rw [if_pos h, if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg h, if_neg (fun h' => h h'.symm)]; ring
  simp only [hsplit, Finset.sum_add_distrib]
  have h1 := sum_ite_adj_le Λ G hd f hf
  have h2 := sum_ite_adj_le Λ G hd f hf
  rw [Finset.sum_comm] at h2
  linarith


/-!

## F. The row bound of the finite-volume Hamiltonian

-/

namespace BoseHubbardData

variable (D : BoseHubbardData L)

omit [DecidableEq L] in
lemma localMoment_nonneg (p : ℕ) (z : L) (α : Occ L) : 0 ≤ localMoment p z α := by
  unfold localMoment; positivity

/-- Weights comparable on neighbours turn `(w_x + w_y)(G_x + G_y)` into `w_x G_x + w_y G_y`. -/
lemma weight_mul_le {wx wy Gx Gy ρ : ℝ} (hGx : 0 ≤ Gx) (hGy : 0 ≤ Gy) (h1 : wx ≤ ρ * wy)
    (h2 : wy ≤ ρ * wx) : (wx + wy) * (Gx + Gy) ≤ (1 + ρ) * (wx * Gx + wy * Gy) := by
  nlinarith [mul_le_mul_of_nonneg_right h1 hGy, mul_le_mul_of_nonneg_right h2 hGx]

open Classical in
/-- Each bond of the region contributes at most its row bound, and nothing if it is not a bond. -/
lemma sum_bondTerm_le_ite (S : Finset (Occ L)) {Λ : Finset L} (w : L → ℝ) (hw : ∀ z, 0 ≤ w z)
    {ρ : ℝ} (hρ : ∀ x y, D.graph.Adj x y → w x ≤ ρ * w y) {K : ℝ} (hK : 0 ≤ K)
    (hJ : ∀ x y, |D.J x y| ≤ K) (hΔ : ∀ x y, ‖D.Δ x y‖ ≤ K) (p : ℕ) (α : Occ L) {q : L × L}
    (hq : q ∈ Λ ×ˢ Λ) :
    ∑ β ∈ S, ‖matEl (D.bondTerm q.1 q.2) α β‖ *
        |weightedMoment Λ w p β - weightedMoment Λ w p α| ≤
      if D.graph.Adj q.1 q.2 then 4 * K * ((p + 1) * 2 ^ (p + 1) * (1 + ρ)) *
        (w q.1 * localMoment p q.1 α + w q.2 * localMoment p q.2 α) else 0 := by
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hq
  split_ifs with hadj
  · refine (D.sum_bondTerm_le S w hw p hx hy (hJ _ _) (hΔ _ _) α).trans ?_
    have := weight_mul_le (localMoment_nonneg p q.1 α) (localMoment_nonneg p q.2 α)
      (hρ _ _ hadj) (hρ _ _ hadj.symm)
    have hc : 0 ≤ 4 * K * ((p + 1) * 2 ^ (p + 1) : ℝ) := by positivity
    calc _ = 4 * K * ((p + 1) * 2 ^ (p + 1) : ℝ) *
          ((w q.1 + w q.2) * (localMoment p q.1 α + localMoment p q.2 α)) := by ring
      _ ≤ 4 * K * ((p + 1) * 2 ^ (p + 1) : ℝ) *
          ((1 + ρ) * (w q.1 * localMoment p q.1 α + w q.2 * localMoment p q.2 α)) :=
          mul_le_mul_of_nonneg_left this hc
      _ = _ := by ring
  · refine (Finset.sum_eq_zero fun β _ => ?_).le
    rw [matEl_bondTerm, if_neg hadj, norm_zero, zero_mul]

open Classical in
/-- **Row bound of the finite-volume Hamiltonian.** For weights comparable on neighbours, a region
of degree at most `d` and amplitudes bounded by `K`, the matrix elements of `H_Λ` times the change
of the weighted moment sum along a row to at most `c A(α)`, with `c` independent of the on-site
potential `V`. -/
lemma sum_finiteHam_le (V : L → ℕ → ℝ) (Λ : Finset L) (S : Finset (Occ L)) (w : L → ℝ)
    (hw : ∀ z, 0 ≤ w z) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ x y, D.graph.Adj x y → w x ≤ ρ * w y)
    {d : ℕ} (hd : ∀ x ∈ Λ, (Λ.filter (D.graph.Adj x)).card ≤ d) {K : ℝ} (hK : 0 ≤ K)
    (hJ : ∀ x y, |D.J x y| ≤ K) (hΔ : ∀ x y, ‖D.Δ x y‖ ≤ K) (p : ℕ) (α : Occ L) :
    ∑ β ∈ S, ‖matEl (D.finiteHam V Λ) α β‖ *
        |weightedMoment Λ w p β - weightedMoment Λ w p α| ≤
      8 * d * K * ((p + 1) * 2 ^ (p + 1)) * (1 + ρ) * weightedMoment Λ w p α := by
  set dA : Occ L → ℝ := fun β => |weightedMoment Λ w p β - weightedMoment Λ w p α|
  set M : ℝ := 4 * K * ((p + 1) * 2 ^ (p + 1) * (1 + ρ))
  set f : L → ℝ := fun z => w z * localMoment p z α
  have hM : 0 ≤ M := by positivity
  -- the diagonal part does not change the moment
  have hpt : ∀ β ∈ S, ‖matEl (D.finiteHam V Λ) α β‖ * dA β ≤
      ∑ q ∈ Λ ×ˢ Λ, ‖matEl (D.bondTerm q.1 q.2) α β‖ * dA β := by
    intro β _
    by_cases hβ : β = α
    · subst hβ
      simp only [dA, sub_self, abs_zero, mul_zero]
      exact Finset.sum_nonneg fun _ _ => le_rfl
    · unfold finiteHam
      rw [matEl_add, matEl_sum, matEl_diagAdj, if_neg hβ, zero_add, ← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (abs_nonneg _)
  calc ∑ β ∈ S, ‖matEl (D.finiteHam V Λ) α β‖ * dA β
      ≤ ∑ β ∈ S, ∑ q ∈ Λ ×ˢ Λ, ‖matEl (D.bondTerm q.1 q.2) α β‖ * dA β := Finset.sum_le_sum hpt
    _ = ∑ q ∈ Λ ×ˢ Λ, ∑ β ∈ S, ‖matEl (D.bondTerm q.1 q.2) α β‖ * dA β := Finset.sum_comm
    _ ≤ ∑ q ∈ Λ ×ˢ Λ, if D.graph.Adj q.1 q.2 then M * (f q.1 + f q.2) else 0 :=
        Finset.sum_le_sum fun q hq => D.sum_bondTerm_le_ite S w hw hρ hK hJ hΔ p α hq
    _ = M * ∑ x ∈ Λ, ∑ y ∈ Λ, (if D.graph.Adj x y then f x + f y else 0) := by
        rw [Finset.sum_product, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> ring
    _ ≤ M * (2 * d * ∑ x ∈ Λ, f x) :=
        mul_le_mul_of_nonneg_left (sum_adj_le Λ D.graph hd f
          fun z => mul_nonneg (hw z) (localMoment_nonneg p z α)) hM
    _ = _ := by simp only [weightedMoment, f, M]; ring

end BoseHubbardData


/-!

## G. The moment bound in a truncated volume

-/

section Truncated

open Matrix

variable {B : Type*} [Fintype B] [DecidableEq B]

lemma inner_toEuclideanCLM_eq (M : Matrix B B ℂ) (φ : EuclideanSpace ℂ B) :
    inner ℂ φ (toEuclideanCLM (𝕜 := ℂ) M φ) =
      ∑ α, ∑ b, starRingEnd ℂ (φ α) * M α b * φ b := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanCLM, dotProduct]
  simp only [mulVec, dotProduct, Pi.star_apply, RCLike.star_def, Finset.sum_mul]
  exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun b _ => by ring

lemma toEuclideanCLM_selfAdjoint (M : Matrix B B ℂ) (hM : M.IsHermitian)
    (x y : EuclideanSpace ℂ B) :
    inner ℂ (toEuclideanCLM (𝕜 := ℂ) M x) y = inner ℂ x (toEuclideanCLM (𝕜 := ℂ) M y) := by
  have h : star (toEuclideanCLM (𝕜 := ℂ) M) = toEuclideanCLM (𝕜 := ℂ) M := by
    rw [← map_star, hM.star_eq]
  calc inner ℂ (toEuclideanCLM (𝕜 := ℂ) M x) y =
        inner ℂ (ContinuousLinearMap.adjoint (toEuclideanCLM (𝕜 := ℂ) M) x) y := by
        rw [← ContinuousLinearMap.star_eq_adjoint, h]
    _ = _ := ContinuousLinearMap.adjoint_inner_left _ _ _

/-- **Grönwall bound for a Hermitian matrix and a diagonal weight.** If the rows of `M` satisfy
`Σ_b |M_{αb}| |a_b - a_α| ≤ c a_α` with `a ≥ 0`, then the diagonal form of `a` grows at most like
`e^{c t}` along the evolution generated by `M`. -/
theorem expect_diag_le (M : Matrix B B ℂ) (hM : M.IsHermitian) (a : B → ℝ) (c : ℝ)
    (hrow : ∀ α, ∑ b, ‖M α b‖ * |a b - a α| ≤ c * a α) (ψ : EuclideanSpace ℂ B) {t : ℝ}
    (ht : 0 ≤ t) :
    RCLike.re (inner ℂ (schrodinger (toEuclideanCLM (𝕜 := ℂ) M) t ψ)
        (toEuclideanCLM (𝕜 := ℂ) (diagonal fun α => (a α : ℂ))
          (schrodinger (toEuclideanCLM (𝕜 := ℂ) M) t ψ))) ≤
      Real.exp (c * t) * RCLike.re (inner ℂ ψ (toEuclideanCLM (𝕜 := ℂ)
        (diagonal fun α => (a α : ℂ)) ψ)) := by
  refine expect_le_exp_mul _ _ (toEuclideanCLM_selfAdjoint M hM) c (fun φ => ?_) ψ ht
  set A := diagonal fun α => (a α : ℂ)
  have hcomm : Complex.I • (toEuclideanCLM (𝕜 := ℂ) M * toEuclideanCLM (𝕜 := ℂ) A -
      toEuclideanCLM (𝕜 := ℂ) A * toEuclideanCLM (𝕜 := ℂ) M) =
      toEuclideanCLM (𝕜 := ℂ) (Complex.I • (M * A - A * M)) := by
    rw [map_smul, map_sub, map_mul, map_mul]
  rw [hcomm, inner_toEuclideanCLM_eq, inner_toEuclideanCLM_eq]
  have hentry : ∀ α b, (Complex.I • (M * A - A * M)) α b =
      Complex.I * (M α b * ((a b - a α : ℝ) : ℂ)) := fun α b => by
    simp only [A, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      smul_eq_mul]
    push_cast; ring
  have hdiag : ∀ α b, A α b * φ b = if α = b then (a α : ℂ) * φ b else 0 := fun α b => by
    simp only [A, diagonal_apply]; split_ifs <;> simp
  simp only [hentry]
  have hA : ∑ α, ∑ b, starRingEnd ℂ (φ α) * A α b * φ b = ∑ α, ((a α * ‖φ α‖ ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [mul_assoc, hdiag, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    push_cast
    rw [← Complex.conj_mul', mul_comm, mul_assoc, mul_comm (φ α)]
  have hAre : RCLike.re (∑ α, ((a α * ‖φ α‖ ^ 2 : ℝ) : ℂ)) = ∑ α, a α * ‖φ α‖ ^ 2 := by
    rw [map_sum]; exact Finset.sum_congr rfl fun α _ => RCLike.ofReal_re _
  rw [hA, hAre]
  have hn := norm_commutator_diag_le M (fun α b => by rw [← hM.apply b α]; rfl) a
    (fun α => c * a α) hrow φ
  have hre : RCLike.re (∑ α, ∑ b, starRingEnd ℂ (φ α) *
      (Complex.I * (M α b * ((a b - a α : ℝ) : ℂ))) * φ b) ≤
      ‖∑ α, ∑ b, starRingEnd ℂ (φ α) * (M α b * ((a b - a α : ℝ) : ℂ)) * φ b‖ := by
    have e : ∑ α, ∑ b, starRingEnd ℂ (φ α) * (Complex.I * (M α b * ((a b - a α : ℝ) : ℂ))) *
        φ b = Complex.I * ∑ α, ∑ b, starRingEnd ℂ (φ α) * (M α b * ((a b - a α : ℝ) : ℂ)) * φ b := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun α _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    rw [e]
    refine (RCLike.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_I, one_mul]
  refine hre.trans (hn.trans (le_of_eq ?_))
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ => by ring

end Truncated


namespace BoseHubbardData

open Matrix

variable (D : BoseHubbardData L)

/-- The finite-volume Hamiltonian restricted to a finite set `S` of basis states. -/
def truncHam (V : L → ℕ → ℝ) (Λ : Finset L) (S : Finset (Occ L)) : Matrix S S ℂ :=
  fun a b => matEl (D.finiteHam V Λ) a.1 b.1

lemma truncHam_isHermitian (V : L → ℕ → ℝ) (Λ : Finset L) (S : Finset (Occ L)) :
    (D.truncHam V Λ S).IsHermitian := by
  refine Matrix.IsHermitian.ext fun a b => ?_
  simp only [truncHam]
  rw [matEl_conj _ (D.star_finiteHam V Λ) b.1 a.1]
  simp

/-- The weighted moment as a diagonal matrix on `S`. -/
def momentMat (Λ : Finset L) (w : L → ℝ) (p : ℕ) (S : Finset (Occ L)) : Matrix S S ℂ :=
  diagonal fun a => (weightedMoment Λ w p a.1 : ℂ)

open Classical in
/-- **The moment bound in a truncated volume (T1).** Restrict the finite-volume Hamiltonian with
hopping, pairing and an arbitrary on-site potential `V` to a finite set `S` of basis states. Along
the evolution generated by it, the weighted moment `Σ_{x∈Λ} w_x (N_x + 1)^{p+1}` grows at most like
`e^{c t}` with `c = 8 d K (p + 1) 2^{p+1} (1 + ρ)`. The rate depends only on the degree `d`, the
bound `K` on hopping and pairing, the weight ratio `ρ` and `p`. It does not depend on `V`, on `Λ` or
on `S`. -/
theorem truncated_moment_le (V : L → ℕ → ℝ) (Λ : Finset L) (S : Finset (Occ L)) (w : L → ℝ)
    (hw : ∀ z, 0 ≤ w z) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ x y, D.graph.Adj x y → w x ≤ ρ * w y)
    {d : ℕ} (hd : ∀ x ∈ Λ, (Λ.filter (D.graph.Adj x)).card ≤ d) {K : ℝ} (hK : 0 ≤ K)
    (hJ : ∀ x y, |D.J x y| ≤ K) (hΔ : ∀ x y, ‖D.Δ x y‖ ≤ K) (p : ℕ)
    (ψ : EuclideanSpace ℂ S) {t : ℝ} (ht : 0 ≤ t) :
    RCLike.re (inner ℂ (schrodinger (toEuclideanCLM (𝕜 := ℂ) (D.truncHam V Λ S)) t ψ)
        (toEuclideanCLM (𝕜 := ℂ) (momentMat Λ w p S)
          (schrodinger (toEuclideanCLM (𝕜 := ℂ) (D.truncHam V Λ S)) t ψ))) ≤
      Real.exp (8 * d * K * ((p + 1) * 2 ^ (p + 1)) * (1 + ρ) * t) *
        RCLike.re (inner ℂ ψ (toEuclideanCLM (𝕜 := ℂ) (momentMat Λ w p S) ψ)) := by
  refine expect_diag_le _ (D.truncHam_isHermitian V Λ S) (fun a => weightedMoment Λ w p a.1) _
    (fun α => ?_) ψ ht
  have := D.sum_finiteHam_le V Λ S w hw hρ0 hρ hd hK hJ hΔ p α.1
  rw [← Finset.sum_coe_sort S] at this
  exact this

end BoseHubbardData


namespace BoseHubbardData

open Matrix

lemma re_inner_momentMat (Λ : Finset L) (w : L → ℝ) (p : ℕ) (S : Finset (Occ L))
    (ψ : EuclideanSpace ℂ S) :
    RCLike.re (inner ℂ ψ (toEuclideanCLM (𝕜 := ℂ) (momentMat Λ w p S) ψ)) =
      ∑ α, weightedMoment Λ w p α.1 * ‖ψ α‖ ^ 2 := by
  rw [inner_toEuclideanCLM_eq, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have h : ∑ b, starRingEnd ℂ (ψ α) * momentMat Λ w p S α b * ψ b =
      ((weightedMoment Λ w p α.1 * ‖ψ α‖ ^ 2 : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single α (fun b _ hb => by
      simp [momentMat, diagonal_apply_ne _ (Ne.symm hb)]) (by simp)]
    simp only [momentMat, diagonal_apply_eq]
    push_cast
    rw [← Complex.conj_mul']; ring
  rw [h]; exact RCLike.ofReal_re _

omit [DecidableEq L] in
lemma localMoment_le_weightedMoment {Λ : Finset L} (w : L → ℝ) (hw : ∀ z, 0 ≤ w z) (p : ℕ)
    {x₀ : L} (hx₀ : x₀ ∈ Λ) (α : Occ L) :
    w x₀ * localMoment p x₀ α ≤ weightedMoment Λ w p α :=
  Finset.single_le_sum (f := fun z => w z * localMoment p z α)
    (fun z _ => mul_nonneg (hw z) (localMoment_nonneg p z α)) hx₀

variable (D : BoseHubbardData L)

open Classical in
/-- **The local moment at a site along the truncated dynamics.** With `w_{x₀} = 1`, the local moment
`⟨ψ_t, (N_{x₀} + 1)^{p+1} ψ_t⟩` is at most `e^{c t}` times the initial weighted moment
`Σ_{x∈Λ} w_x ⟨ψ, (N_x + 1)^{p+1} ψ⟩`. -/
theorem truncated_localMoment_le (V : L → ℕ → ℝ) (Λ : Finset L) (S : Finset (Occ L)) (w : L → ℝ)
    (hw : ∀ z, 0 ≤ w z) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ x y, D.graph.Adj x y → w x ≤ ρ * w y)
    {d : ℕ} (hd : ∀ x ∈ Λ, (Λ.filter (D.graph.Adj x)).card ≤ d) {K : ℝ} (hK : 0 ≤ K)
    (hJ : ∀ x y, |D.J x y| ≤ K) (hΔ : ∀ x y, ‖D.Δ x y‖ ≤ K) (p : ℕ) {x₀ : L} (hx₀ : x₀ ∈ Λ)
    (hw₀ : w x₀ = 1) (ψ : EuclideanSpace ℂ S) {t : ℝ} (ht : 0 ≤ t) :
    ∑ α, localMoment p x₀ α.1 *
        ‖schrodinger (toEuclideanCLM (𝕜 := ℂ) (D.truncHam V Λ S)) t ψ α‖ ^ 2 ≤
      Real.exp (8 * d * K * ((p + 1) * 2 ^ (p + 1)) * (1 + ρ) * t) *
        ∑ α, weightedMoment Λ w p α.1 * ‖ψ α‖ ^ 2 := by
  have h := D.truncated_moment_le V Λ S w hw hρ0 hρ hd hK hJ hΔ p ψ ht
  rw [re_inner_momentMat, re_inner_momentMat] at h
  refine le_trans (Finset.sum_le_sum fun α _ => ?_) h
  have := localMoment_le_weightedMoment w hw p hx₀ α.1
  rw [hw₀, one_mul] at this
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

end BoseHubbardData


/-!

## H. Exponential weights on graphs of polynomial growth

-/

section Weights

variable (G : SimpleGraph L)

/-- The weight `e^{-μ d(x₀, x)}` centred at `x₀`. -/
def expWeight (x₀ : L) (μ : ℝ) (x : L) : ℝ := Real.exp (-μ * G.dist x₀ x)

omit [DecidableEq L] in
lemma expWeight_nonneg (x₀ : L) (μ : ℝ) (x : L) : 0 ≤ expWeight G x₀ μ x := (Real.exp_pos _).le

omit [DecidableEq L] in
lemma expWeight_self (x₀ : L) (μ : ℝ) : expWeight G x₀ μ x₀ = 1 := by simp [expWeight]

omit [DecidableEq L] in
/-- **Exponential weights are comparable on neighbours.** -/
lemma expWeight_adj_le (x₀ : L) {μ : ℝ} (hμ : 0 ≤ μ) {x y : L} (h : G.Adj x y) :
    expWeight G x₀ μ x ≤ Real.exp μ * expWeight G x₀ μ y := by
  unfold expWeight
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hd : (G.dist x₀ y : ℝ) ≤ G.dist x₀ x + 1 := by
    rcases h.symm.diff_dist_adj (u := x₀) with h1 | h1 | h1
    · rw [h1]; linarith
    · exact_mod_cast (show G.dist x₀ y ≤ G.dist x₀ x + 1 by omega)
    · exact_mod_cast (show G.dist x₀ y ≤ G.dist x₀ x + 1 by omega)
  nlinarith

omit [DecidableEq L] in
lemma summable_growth {μ : ℝ} (hμ : 0 < μ) (C : ℝ) (ν : ℕ) :
    Summable fun n : ℕ => C * ((n : ℝ) + 1) ^ ν * Real.exp (-μ * n) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_pow_mul_exp_neg_nat_mul ν hμ)
  refine (h.mul_left (C * Real.exp μ)).congr fun n => ?_
  push_cast
  rw [show -μ * ((n : ℝ) + 1) = -μ * n + -μ by ring, Real.exp_add, Real.exp_neg μ]
  field_simp

omit [DecidableEq L] in
/-- **The total weight of a region is bounded uniformly on graphs of polynomial growth.** If every
set of vertices within distance `R` of `x₀` has at most `C (R + 1)^ν` elements, then
`Σ_{x∈Λ} e^{-μ d(x₀, x)}` is bounded by a constant independent of the region `Λ`. -/
lemma sum_expWeight_le (x₀ : L) {μ : ℝ} (hμ : 0 < μ) {C : ℝ} {ν : ℕ}
    (hball : ∀ (s : Finset L) (R : ℕ), (∀ x ∈ s, G.dist x₀ x ≤ R) → (s.card : ℝ) ≤ C * (R + 1) ^ ν)
    (Λ : Finset L) :
    ∑ x ∈ Λ, expWeight G x₀ μ x ≤ ∑' n : ℕ, C * ((n : ℝ) + 1) ^ ν * Real.exp (-μ * n) := by
  unfold expWeight
  rw [Finset.sum_comp (fun n : ℕ => Real.exp (-μ * n)) (fun x => G.dist x₀ x)]
  refine le_trans (Finset.sum_le_sum fun n _ => ?_) ((summable_growth hμ C ν).sum_le_tsum _
    fun n _ => ?_)
  · rw [nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact hball _ n fun x hx => (Finset.mem_filter.mp hx).2.le
  · have hC : 0 ≤ C := by
      have := hball ∅ 0 (by simp); simpa using this
    positivity

end Weights


/-!

## I. The uniform moment bound in a truncated volume

-/

namespace BoseHubbardData

variable (D : BoseHubbardData L)

omit [DecidableEq L] in
lemma sum_weightedMoment_le (Λ : Finset L) (w : L → ℝ) (hw : ∀ z, 0 ≤ w z) (p : ℕ)
    (S : Finset (Occ L)) (ψ : EuclideanSpace ℂ S) {M : ℝ}
    (hM : ∀ x ∈ Λ, ∑ α, localMoment p x α.1 * ‖ψ α‖ ^ 2 ≤ M) :
    ∑ α, weightedMoment Λ w p α.1 * ‖ψ α‖ ^ 2 ≤ M * ∑ x ∈ Λ, w x := by
  simp only [weightedMoment, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM x hx) (hw x)

open Classical in
/-- **Uniform local moment bound (T1, truncated volume).** On a graph of polynomial growth with
`#{x : d(x₀, x) ≤ R} ≤ C (R + 1)^ν` and degree at most `d`, with hopping and pairing bounded by `K`
and an arbitrary on-site potential `V`, every local moment along the truncated dynamics satisfies
`⟨ψ_t, (N_{x₀} + 1)^{p+1} ψ_t⟩ ≤ e^{c t} W M` whenever all initial local moments in `Λ` are at most
`M`. The rate `c = 8 d K (p + 1) 2^{p+1} (1 + e^μ)` and the constant
`W = Σ_n C (n + 1)^ν e^{-μ n}` are independent of `Λ`, of the truncation `S` and of `V`. -/
theorem truncated_localMoment_uniform (V : L → ℕ → ℝ) (Λ : Finset L) (S : Finset (Occ L))
    {d : ℕ} (hd : ∀ x ∈ Λ, (Λ.filter (D.graph.Adj x)).card ≤ d) {K : ℝ} (hK : 0 ≤ K)
    (hJ : ∀ x y, |D.J x y| ≤ K) (hΔ : ∀ x y, ‖D.Δ x y‖ ≤ K) (p : ℕ) {x₀ : L} (hx₀ : x₀ ∈ Λ)
    {μ : ℝ} (hμ : 0 < μ) {C : ℝ} {ν : ℕ}
    (hball : ∀ (s : Finset L) (R : ℕ), (∀ x ∈ s, D.graph.dist x₀ x ≤ R) →
      (s.card : ℝ) ≤ C * (R + 1) ^ ν)
    (ψ : EuclideanSpace ℂ S) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Λ, ∑ α, localMoment p x α.1 * ‖ψ α‖ ^ 2 ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ∑ α, localMoment p x₀ α.1 *
        ‖schrodinger (Matrix.toEuclideanCLM (𝕜 := ℂ) (D.truncHam V Λ S)) t ψ α‖ ^ 2 ≤
      Real.exp (8 * d * K * ((p + 1) * 2 ^ (p + 1)) * (1 + Real.exp μ) * t) *
        (M * ∑' n : ℕ, C * ((n : ℝ) + 1) ^ ν * Real.exp (-μ * n)) := by
  set w := expWeight D.graph x₀ μ
  have hw : ∀ z, 0 ≤ w z := expWeight_nonneg D.graph x₀ μ
  have h := D.truncated_localMoment_le V Λ S w hw (Real.exp_pos μ).le
    (fun x y hxy => expWeight_adj_le D.graph x₀ hμ.le hxy) hd hK hJ hΔ p hx₀
    (expWeight_self D.graph x₀ μ) ψ ht
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  exact (sum_weightedMoment_le Λ w hw p S ψ hM).trans
    (mul_le_mul_of_nonneg_left (sum_expWeight_le D.graph x₀ hμ hball Λ) hM0)

end BoseHubbardData


/-!

## J. Plain row sums of the finite-volume Hamiltonian

-/

/-- A move with a unique partner contributes at most its amplitude bound to a plain row sum. -/
lemma sum_move_norm_le (S : Finset (Occ L)) {x y : L} (α β0 : Occ L) (f : Occ L → ℂ)
    (hf : ∀ β, f β ≠ 0 → β = β0 ∧ IsMove x y α β ‖f β‖) :
    ∑ β ∈ S, ‖f β‖ ≤ ((α x : ℝ) + 1) + ((α y : ℝ) + 1) := by
  refine (sum_le_of_eq_zero S _ (fun _ => norm_nonneg _) β0 fun β _ hβ => ?_).trans ?_
  · by_contra hne
    exact hβ (hf β (fun h0 => hne (by rw [h0, norm_zero]))).1
  · by_cases h0 : f β0 = 0
    · rw [h0, norm_zero]; positivity
    · exact (hf β0 h0).2.amp_le

namespace BoseHubbardData

variable (D : BoseHubbardData L)

/-- **Plain row sum of one bond.** -/
lemma sum_norm_bondTerm_le (S : Finset (Occ L)) {x y : L} {K : ℝ} (hJ : |D.J x y| ≤ K)
    (hΔ : ‖D.Δ x y‖ ≤ K) (α : Occ L) :
    ∑ β ∈ S, ‖matEl (D.bondTerm x y) α β‖ ≤ 4 * K * (((α x : ℝ) + 1) + ((α y : ℝ) + 1)) := by
  have hK : 0 ≤ K := (abs_nonneg _).trans hJ
  by_cases hadj : D.graph.Adj x y
  swap
  · refine (Finset.sum_eq_zero fun β _ => ?_).le.trans (by positivity)
    rw [matEl_bondTerm, if_neg hadj, norm_zero]
  have hxy : x ≠ y := hadj.ne
  have hR1 := sum_move_norm_le S α _ (fun β => cre x (ann y (single β (1 : ℂ))) α)
    fun β h => isMove_cre_ann hxy h
  have hR2 := sum_move_norm_le S α _ (fun β => cre y (ann x (single β (1 : ℂ))) α)
    fun β h => ⟨(isMove_cre_ann hxy.symm h).1, (isMove_cre_ann hxy.symm h).2.symm⟩
  have hR3 := sum_move_norm_le S α _ (fun β => cre x (cre y (single β (1 : ℂ))) α)
    fun β h => isMove_cre_cre hxy h
  have hR4 := sum_move_norm_le S α _ (fun β => ann y (ann x (single β (1 : ℂ))) α)
    fun β h => isMove_ann_ann hxy h
  have hpt : ∀ β ∈ S, ‖matEl (D.bondTerm x y) α β‖ ≤
      K * ‖cre x (ann y (single β (1 : ℂ))) α‖ + K * ‖cre y (ann x (single β (1 : ℂ))) α‖ +
        K * ‖cre x (cre y (single β (1 : ℂ))) α‖ + K * ‖ann y (ann x (single β (1 : ℂ))) α‖ := by
    intro β _
    rw [matEl_bondTerm, if_pos hadj]
    refine (norm_add₃_le).trans ?_
    rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_neg]
    have h1 := norm_add_le (cre x (ann y (single β (1 : ℂ))) α) (cre y (ann x (single β 1)) α)
    nlinarith [norm_nonneg (cre x (ann y (single β (1 : ℂ))) α),
      norm_nonneg (cre y (ann x (single β (1 : ℂ))) α),
      norm_nonneg (cre x (cre y (single β (1 : ℂ))) α),
      norm_nonneg (ann y (ann x (single β (1 : ℂ))) α), abs_nonneg (D.J x y),
      norm_nonneg (D.Δ x y)]
  refine (Finset.sum_le_sum hpt).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hR1 hK, mul_le_mul_of_nonneg_left hR2 hK,
    mul_le_mul_of_nonneg_left hR3 hK, mul_le_mul_of_nonneg_left hR4 hK]

/-- **Plain row sum of the finite-volume Hamiltonian off the diagonal.** If every occupation of the
row state in `Λ` is at most `n`, the off-diagonal row sum over any finite set is at most
`8 K |Λ|² (n + 1)`. -/
lemma sum_norm_finiteHam_le (V : L → ℕ → ℝ) (Λ : Finset L) (S : Finset (Occ L)) {K : ℝ}
    (hK : 0 ≤ K) (hJ : ∀ x y, |D.J x y| ≤ K) (hΔ : ∀ x y, ‖D.Δ x y‖ ≤ K) (α : Occ L) {n : ℕ}
    (hn : ∀ x ∈ Λ, α x ≤ n) :
    ∑ β ∈ S.erase α, ‖matEl (D.finiteHam V Λ) α β‖ ≤ 8 * K * (Λ.card : ℝ) ^ 2 * (n + 1) := by
  have hpt : ∀ β ∈ S.erase α, ‖matEl (D.finiteHam V Λ) α β‖ ≤
      ∑ q ∈ Λ ×ˢ Λ, ‖matEl (D.bondTerm q.1 q.2) α β‖ := by
    intro β hβ
    unfold finiteHam
    rw [matEl_add, matEl_sum, matEl_diagAdj, if_neg (Finset.ne_of_mem_erase hβ), zero_add]
    exact norm_sum_le _ _
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_comm]
  calc ∑ q ∈ Λ ×ˢ Λ, ∑ β ∈ S.erase α, ‖matEl (D.bondTerm q.1 q.2) α β‖
      ≤ ∑ q ∈ Λ ×ˢ Λ, 4 * K * (((n : ℝ) + 1) + ((n : ℝ) + 1)) :=
        Finset.sum_le_sum fun q hq => by
          obtain ⟨hx, hy⟩ := Finset.mem_product.mp hq
          refine (D.sum_norm_bondTerm_le _ (hJ _ _) (hΔ _ _) α).trans ?_
          have h1 : (α q.1 : ℝ) ≤ n := by exact_mod_cast hn _ hx
          have h2 : (α q.2 : ℝ) ≤ n := by exact_mod_cast hn _ hy
          nlinarith
    _ = 8 * K * (Λ.card : ℝ) ^ 2 * (n + 1) := by
        rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]; push_cast; ring

end BoseHubbardData

end InfiniteBosons
