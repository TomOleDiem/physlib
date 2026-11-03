/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FiniteVolume
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.MomentBound
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

## iii. Table of contents

- A. Scalar inequalities

## iv. References

* A. Deuchert, J. Lampart, M. Lemm, Dynamics and equilibrium states of infinite systems of lattice
  bosons, arXiv:2505.13170, Proposition 4.10.
-/

@[expose] public section

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

end InfiniteBosons
