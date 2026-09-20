/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Basic
public import Physlib.ProbabilisticTheory.State.Metric
public import Physlib.ProbabilisticTheory.Effect.Complement
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.Module

/-!
# State discrimination

## i. Overview

A system is prepared in state `ω₀` (with probability `p`) or `ω₁` (with probability `1 - p`). We
get to run a single yes/no test on it — an effect `e` — and have to guess which state it was,
based only on whether `e` "clicked". We guess `ω₀` on a click and `ω₁` otherwise; `successProb`
is the probability that guess is right.

Always guessing `ω₁`, without even looking at the system, is already right with probability
`1 - p` — that's our baseline. Running a test can only add to it: its `advantage` is how much
extra success probability it buys over that baseline. The best possible test maximizes this
advantage, giving the classic Helstrom bound (`optimalSuccessProb_eq`).

For equal priors (`p = 1/2`) the bound simplifies to `1/2 + dist ω₀ ω₁ / 4`.
Two equally likely states are easier to tell apart exactly when they sit farther apart.

## ii. Key results

- `UnitalPositiveLinearMap.optimalSuccessProb_eq` : the Helstrom bound.
- `UnitalPositiveLinearMap.optimalSuccessProb_half_half_eq` : for equal priors, the bound is the
  state distance.

## iii. Table of contents

- A. Success probability and the advantage of a test
- B. The Helstrom bound
- C. Equal priors: the bound is the state distance

## iv. References

- C.W. Helstrom, *Quantum Detection and Estimation Theory*, Academic Press, 1976.

-/

@[expose] public section

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [One E] [IsOrderUnit E]

namespace UnitalPositiveLinearMap

/-! ## A. Success probability and the advantage of a test -/

/-- Probability of guessing right between `ω₀` (prior `p`) and `ω₁` (prior `1 - p`) using test
`e`: guess `ω₀` on a click, `ω₁` otherwise. -/
def successProb (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) (e : Effect E) : ℝ :=
  (p : ℝ) * ω₀ (e : E) + (1 - (p : ℝ)) * ω₁ ((Effect.complement e : E))

/-- How much test `e` improves on the baseline of always guessing `ω₁`. -/
def advantage (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) (e : Effect E) : ℝ :=
  (p : ℝ) * ω₀ (e : E) - (1 - (p : ℝ)) * ω₁ (e : E)

omit [PosSMulMono ℝ E] [IsOrderUnit E] in
/-- Success probability equals the baseline `1 - p` plus the advantage of test `e`. -/
lemma successProb_eq_add_advantage (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) (e : Effect E) :
    successProb ω₀ ω₁ p e = (1 - (p : ℝ)) + advantage ω₀ ω₁ p e := by
  show (p : ℝ) * ω₀ (e : E) + (1 - (p : ℝ)) * ω₁ (1 - (e : E))
      = (1 - (p : ℝ)) + ((p : ℝ) * ω₀ (e : E) - (1 - (p : ℝ)) * ω₁ (e : E))
  rw [map_sub, map_one]
  ring

/-! ## B. The Helstrom bound -/

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] in
/-- No test's advantage beats the prior weight `p` of the state it favors. -/
lemma advantage_le (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) (e : Effect E) :
    advantage ω₀ ω₁ p e ≤ (p : ℝ) := by
  show (p : ℝ) * ω₀ (e : E) - (1 - (p : ℝ)) * ω₁ (e : E) ≤ (p : ℝ)
  have h1 : ω₀ (e : E) ≤ 1 := (ω₀.monotone' e.2.2).trans_eq (map_one ω₀)
  have h2 : 0 ≤ ω₁ (e : E) := map_nonneg ω₁ e.2.1
  have h3 : (p : ℝ) * ω₀ (e : E) ≤ (p : ℝ) * 1 := mul_le_mul_of_nonneg_left h1 p.2.1
  have h4 : 0 ≤ (1 - (p : ℝ)) * ω₁ (e : E) := mul_nonneg (by linarith [p.2.2]) h2
  linarith

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] in
lemma bddAbove_advantage (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) :
    BddAbove (Set.range (advantage ω₀ ω₁ p)) :=
  ⟨(p : ℝ), by rintro _ ⟨e, rfl⟩; exact advantage_le ω₀ ω₁ p e⟩

omit [PosSMulMono ℝ E] [IsOrderUnit E] in
lemma bddAbove_successProb (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) :
    BddAbove (Set.range (successProb ω₀ ω₁ p)) := by
  obtain ⟨b, hb⟩ := bddAbove_advantage ω₀ ω₁ p
  exact ⟨(1 - (p : ℝ)) + b, by
    rintro _ ⟨e, rfl⟩
    rw [successProb_eq_add_advantage]
    linarith [hb (Set.mem_range_self e)]⟩

/-- The best a single test can do. -/
noncomputable def optimalSuccessProb (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) : ℝ :=
  ⨆ e : Effect E, successProb ω₀ ω₁ p e

omit [PosSMulMono ℝ E] in
/-- The Helstrom bound: optimal success probability is the baseline `1 - p` plus the best
advantage any test can give. -/
lemma optimalSuccessProb_eq (ω₀ ω₁ : 𝓢[ℝ, E]) (p : unitInterval) :
    optimalSuccessProb ω₀ ω₁ p = (1 - (p : ℝ)) + ⨆ e : Effect E, advantage ω₀ ω₁ p e := by
  have hbdd := bddAbove_advantage ω₀ ω₁ p
  have hbdd' := bddAbove_successProb ω₀ ω₁ p
  unfold optimalSuccessProb
  apply le_antisymm
  · exact ciSup_le fun e => by rw [successProb_eq_add_advantage]; linarith [le_ciSup hbdd e]
  · have hle : (⨆ e : Effect E, advantage ω₀ ω₁ p e) ≤
        (⨆ e : Effect E, successProb ω₀ ω₁ p e) - (1 - (p : ℝ)) := by
      apply ciSup_le
      intro e
      have h1 := le_ciSup hbdd' e
      rw [successProb_eq_add_advantage] at h1
      linarith
    linarith

/-! ## C. Equal priors: the bound is the state distance -/

section Archimedean

variable [IsArchimedeanOrderUnit E]

open IsArchimedeanOrderUnit

omit [PosSMulMono ℝ E] [IsOrderUnit E] [IsArchimedeanOrderUnit E] in
/-- Complementing an effect negates `ω₀ e - ω₁ e`. -/
lemma sub_complement_eq_neg_sub (ω₀ ω₁ : 𝓢[ℝ, E]) (e : Effect E) :
    ω₀ ((Effect.complement e : E)) - ω₁ ((Effect.complement e : E))
      = -(ω₀ (e : E) - ω₁ (e : E)) := by
  show ω₀ (1 - (e : E)) - ω₁ (1 - (e : E)) = _
  simp only [map_sub, map_one]; ring

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [IsArchimedeanOrderUnit E] in
lemma bddAbove_sub (ω₀ ω₁ : 𝓢[ℝ, E]) :
    BddAbove (Set.range fun e : Effect E => ω₀ (e : E) - ω₁ (e : E)) :=
  ⟨1, by
    rintro _ ⟨e, rfl⟩
    have h1 : ω₀ (e : E) ≤ 1 := (ω₀.monotone' e.2.2).trans_eq (map_one ω₀)
    have h2 : (0 : ℝ) ≤ ω₁ (e : E) := map_nonneg ω₁ e.2.1
    linarith⟩

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsOrderUnit E] [IsArchimedeanOrderUnit E] in
lemma bddAbove_abs_advantage (ω₀ ω₁ : 𝓢[ℝ, E]) :
    BddAbove (Set.range fun e : Effect E => |ω₀ (e : E) - ω₁ (e : E)|) :=
  ⟨1, by
    rintro _ ⟨e, rfl⟩
    have h1 : ω₀ (e : E) ≤ 1 := (ω₀.monotone' e.2.2).trans_eq (map_one ω₀)
    have h2 : (0 : ℝ) ≤ ω₁ (e : E) := map_nonneg ω₁ e.2.1
    have h3 : ω₁ (e : E) ≤ 1 := (ω₁.monotone' e.2.2).trans_eq (map_one ω₁)
    have h4 : (0 : ℝ) ≤ ω₀ (e : E) := map_nonneg ω₀ e.2.1
    rw [abs_le]; constructor <;> linarith⟩

omit [PosSMulMono ℝ E] [IsArchimedeanOrderUnit E] in
/-- The best advantage equals its own absolute value: complementing an effect flips its sign. -/
lemma ciSup_advantage_eq_ciSup_abs (ω₀ ω₁ : 𝓢[ℝ, E]) :
    (⨆ e : Effect E, (ω₀ (e : E) - ω₁ (e : E))) = ⨆ e : Effect E, |ω₀ (e : E) - ω₁ (e : E)| := by
  have hbdd := bddAbove_sub ω₀ ω₁
  have hbdd' := bddAbove_abs_advantage ω₀ ω₁
  apply le_antisymm
  · exact ciSup_le fun e => (le_abs_self _).trans (le_ciSup hbdd' e)
  · apply ciSup_le
    intro e
    have h1 := le_ciSup hbdd e
    have h2 := le_ciSup hbdd (Effect.complement e)
    rw [sub_complement_eq_neg_sub] at h2
    exact abs_le.mpr ⟨by linarith, h1⟩

omit [IsOrderUnit E] in
/-- The state distance is the largest `|ω₀ e - ω₁ e|` over unit-ball effects
(`Effect.equivBall`). -/
lemma dist_eq_ciSup_abs_advantage (ω₀ ω₁ : 𝓢[ℝ, E]) :
    dist ω₀ ω₁ =
      ⨆ e : Effect E, |ω₀ ((Effect.equivBall e : E)) - ω₁ ((Effect.equivBall e : E))| := by
  have : Nonempty {A : E // orderUnitNorm A ≤ 1} := ⟨0, by simp⟩
  have hbdd' : BddAbove (Set.range
      fun e : Effect E => |ω₀ ((Effect.equivBall e : E)) - ω₁ ((Effect.equivBall e : E))|) := by
    obtain ⟨b, hb⟩ := dist_bddAbove ω₀ ω₁
    exact ⟨b, by rintro _ ⟨e, rfl⟩; exact hb (Set.mem_range_self (Effect.equivBall e))⟩
  apply le_antisymm
  · apply ciSup_le
    intro A
    rw [← Effect.equivBall.apply_symm_apply A]
    exact le_ciSup hbdd' (Effect.equivBall.symm A)
  · exact ciSup_le fun e => le_ciSup (dist_bddAbove ω₀ ω₁) (Effect.equivBall e)

omit [IsOrderUnit E] in
/-- The state distance is exactly twice the largest advantage a single effect can give. -/
lemma dist_eq_two_mul_ciSup_advantage (ω₀ ω₁ : 𝓢[ℝ, E]) :
    dist ω₀ ω₁ = 2 * ⨆ e : Effect E, (ω₀ (e : E) - ω₁ (e : E)) := by
  rw [ciSup_advantage_eq_ciSup_abs, dist_eq_ciSup_abs_advantage]
  simp_rw [apply_equivBall]
  have hpt : ∀ e : Effect E, |2 * ω₀ (e : E) - 1 - (2 * ω₁ (e : E) - 1)|
      = 2 * |ω₀ (e : E) - ω₁ (e : E)| := fun e => by
    rw [show 2 * ω₀ (e : E) - 1 - (2 * ω₁ (e : E) - 1) = 2 * (ω₀ (e : E) - ω₁ (e : E)) from by ring,
      abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
  simp_rw [hpt]
  rw [show (⨆ e : Effect E, (2 : ℝ) * |ω₀ (e : E) - ω₁ (e : E)|)
      = 2 * ⨆ e : Effect E, |ω₀ (e : E) - ω₁ (e : E)| from by
    rw [← smul_eq_mul, Real.smul_iSup_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; simp [smul_eq_mul]]

omit [IsOrderUnit E] in
/-- For equal priors, the Helstrom bound is `1/2` plus a quarter of the state distance. -/
lemma optimalSuccessProb_half_half_eq (ω₀ ω₁ : 𝓢[ℝ, E]) :
    optimalSuccessProb ω₀ ω₁ ⟨1 / 2, by norm_num, by norm_num⟩ = 1 / 2 + dist ω₀ ω₁ / 4 := by
  rw [optimalSuccessProb_eq, dist_eq_two_mul_ciSup_advantage]
  have hfun : (fun e : Effect E => advantage ω₀ ω₁ ⟨1 / 2, by norm_num, by norm_num⟩ e)
      = fun e : Effect E => (1 / 2 : ℝ) • (ω₀ (e : E) - ω₁ (e : E)) := by
    ext e
    show (1 / 2 : ℝ) * ω₀ (e : E) - (1 - 1 / 2 : ℝ) * ω₁ (e : E) = _
    simp only [smul_eq_mul]; ring
  simp_rw [hfun]
  rw [← Real.smul_iSup_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), smul_eq_mul]
  ring

end Archimedean

end UnitalPositiveLinearMap
