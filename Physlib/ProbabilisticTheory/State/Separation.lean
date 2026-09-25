/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Metric
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Separation by states

## i. Overview

In an Archimedean order-unit space, states determine the entire ordered normed structure. An
element is positive exactly when every state assigns it a nonnegative value, and its order-unit
norm is `‖A‖₁ = sup { |ω A| : ω a state }`. Consequently, states separate points: two elements are
equal whenever every state assigns them the same value.

The main ingredient is Hahn–Banach separation of a point from the positive cone. Applied to an
element `A ≱ 0`, it produces a state `ω` with `ω A < 0`. Everything else follows from this one
separation fact.

## ii. Key results

- `UnitalPositiveLinearMap.exists_apply_neg_of_not_nonneg` : every element outside the positive
  cone is separated from it by a state.
- `UnitalPositiveLinearMap.nonneg_iff_forall_state_nonneg` : states determine the positive cone.
- `UnitalPositiveLinearMap.sSup_abs_apply_eq_orderUnitNorm` : states determine the order-unit norm.
- `UnitalPositiveLinearMap.ext_of_forall_apply_eq` : states separate points.

## iii. Table of contents

- A. Separating points from the cone
- B. The positive cone
- C. The order-unit norm
- D. Separation of points

-/

@[expose] public section

open ArchimedeanOrderUnitSpace

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

namespace UnitalPositiveLinearMap

/-!

## A. Separating points from the cone

-/

/-- A positive functional vanishing at the order unit vanishes everywhere: the unit sandwiches
every element between multiples of it. -/
private lemma apply_eq_zero_of_apply_one_eq_zero {p : E →ₚ[ℝ] ℝ}
    (h1 : p (1 : E) = 0) (A : E) :
    p A = 0 := by
  obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le A
  obtain ⟨m, hm⟩ := OrderUnitSpace.exists_nsmul_one_le (-A)
  have hupper : p A ≤ 0 := by simpa [h1] using p.monotone' hn
  have hlower : 0 ≤ p A := by
    have h := p.monotone' hm
    simp [h1] at h
    linarith
  linarith

/-- Every element outside the positive cone is strictly separated from it by a state. -/
lemma exists_apply_neg_of_not_nonneg {A : E} (hA : ¬ 0 ≤ A) : ∃ ω : 𝓢[ℝ, E], ω A < 0 := by
  obtain ⟨f, u, hfA, hcone⟩ := geometric_hahn_banach_point_closed
    (convex_Ici (0 : E)) isClosed_Ici_zero hA
  have hu : u < 0 := by simpa using hcone 0 le_rfl
  have hf_nonneg : ∀ B : E, 0 ≤ B → 0 ≤ f B := by
    intro B hB
    by_contra hfB
    have hfB' : f B < 0 := lt_of_not_ge hfB
    set t : ℝ := (u - 1) / f B with ht_def
    have ht : 0 ≤ t := div_nonneg_of_nonpos (by linarith) hfB'.le
    have hsep := hcone (t • B) (smul_nonneg ht hB)
    rw [map_smul, smul_eq_mul, ht_def, div_mul_cancel₀ (u - 1) hfB'.ne] at hsep
    linarith
  let p : E →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ f.toLinearMap hf_nonneg
  have hf_one_pos : 0 < f (1 : E) := by
    have hf_one_nonneg : 0 ≤ f (1 : E) := hf_nonneg 1 OrderUnitSpace.one_nonneg
    refine lt_of_le_of_ne hf_one_nonneg fun hf_one => ?_
    have heq : f A = 0 := apply_eq_zero_of_apply_one_eq_zero (p := p) hf_one.symm A
    linarith [hfA.trans hu]
  let ω : 𝓢[ℝ, E] := ofLinearMap ((f (1 : E))⁻¹ • f.toLinearMap)
    (fun B hB => mul_nonneg (inv_nonneg.mpr hf_one_pos.le) (hf_nonneg B hB))
    (by simp [hf_one_pos.ne'])
  refine ⟨ω, ?_⟩
  change (f (1 : E))⁻¹ * f A < 0
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hf_one_pos) (hfA.trans hu)

/-!

## B. The positive cone

-/

/-- An element is positive iff every state assigns it a nonnegative value. -/
lemma nonneg_iff_forall_state_nonneg (A : E) : 0 ≤ A ↔ ∀ ω : 𝓢[ℝ, E], 0 ≤ ω A := by
  constructor
  · exact fun hA ω => map_nonneg ω hA
  · contrapose!
    exact exists_apply_neg_of_not_nonneg

/-!

## C. The order-unit norm

-/

/-- Every nontrivial Archimedean order-unit space has a state. -/
instance instNonemptyState [Nontrivial E] : Nonempty (𝓢[ℝ, E]) := by
  have hone_ne : (1 : E) ≠ 0 := by
    intro hone
    apply not_subsingleton E
    constructor
    intro a b
    have hzero (B : E) : B = 0 := by
      obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le B
      obtain ⟨m, hm⟩ := OrderUnitSpace.exists_nsmul_one_le (-B)
      have hB_nonpos : B ≤ 0 := by simpa [hone] using hn
      have hB_nonneg : 0 ≤ B := neg_nonpos.mp (by simpa [hone] using hm)
      exact le_antisymm hB_nonpos hB_nonneg
    rw [hzero a, hzero b]
  have hnot : ¬ 0 ≤ -(1 : E) := by
    intro h
    exact hone_ne (le_antisymm (neg_nonneg.mp h) OrderUnitSpace.one_nonneg)
  obtain ⟨ω, _⟩ := exists_apply_neg_of_not_nonneg hnot
  exact ⟨ω⟩

/-- Any scalar below the order-unit norm of `A` is exceeded by `|ω A|` for some state `ω`. -/
lemma exists_state_abs_apply_gt_of_lt_orderUnitNorm [Nontrivial E] (A : E) {r : ℝ}
    (hr : r < orderUnitNorm A) : ∃ ω : 𝓢[ℝ, E], r < |ω A| := by
  by_cases hr0 : r < 0
  · obtain ⟨ω⟩ := (inferInstance : Nonempty (𝓢[ℝ, E]))
    exact ⟨ω, hr0.trans_le (abs_nonneg _)⟩
  have hr_nonneg : 0 ≤ r := le_of_not_gt hr0
  have hnot : r ∉ orderUnitBounds A := fun hr_mem =>
    absurd (orderUnitNorm_le hr_mem) (not_le.mpr hr)
  by_cases hu : A ≤ r • (1 : E)
  · have hl : ¬ -(r • (1 : E)) ≤ A := fun hl => hnot ⟨hr_nonneg, hl, hu⟩
    have hnonneg : ¬ 0 ≤ r • (1 : E) + A := by
      simpa [neg_le_iff_add_nonneg, add_comm] using hl
    obtain ⟨ω, hω⟩ := exists_apply_neg_of_not_nonneg hnonneg
    refine ⟨ω, ?_⟩
    rw [map_add, map_smul, smul_eq_mul, map_one, mul_one] at hω
    exact lt_of_lt_of_le (by linarith) (neg_le_abs (ω A))
  · have hnonneg : ¬ 0 ≤ r • (1 : E) - A := by simpa [sub_nonneg] using hu
    obtain ⟨ω, hω⟩ := exists_apply_neg_of_not_nonneg hnonneg
    refine ⟨ω, ?_⟩
    rw [map_sub, map_smul, smul_eq_mul, map_one, mul_one] at hω
    exact lt_of_lt_of_le (by linarith) (le_abs_self (ω A))

/-- The order-unit norm is the supremum of `|ω A|` over all states `ω`. -/
lemma sSup_abs_apply_eq_orderUnitNorm [Nontrivial E] (A : E) :
    sSup (Set.range fun ω : 𝓢[ℝ, E] => |ω A|) = orderUnitNorm A := by
  have hbdd : BddAbove (Set.range fun ω : 𝓢[ℝ, E] => |ω A|) :=
    ⟨orderUnitNorm A, by rintro _ ⟨ω, rfl⟩; exact abs_apply_le_orderUnitNorm ω A⟩
  obtain ⟨ω₀⟩ := (inferInstance : Nonempty (𝓢[ℝ, E]))
  have hne : (Set.range fun ω : 𝓢[ℝ, E] => |ω A|).Nonempty := ⟨|ω₀ A|, Set.mem_range_self ω₀⟩
  apply le_antisymm
  · exact csSup_le hne fun _ h => by
      obtain ⟨ω, rfl⟩ := h
      exact abs_apply_le_orderUnitNorm ω A
  · apply le_of_forall_lt
    intro r hr
    obtain ⟨ω, hω⟩ := exists_state_abs_apply_gt_of_lt_orderUnitNorm A hr
    exact hω.trans_le (le_csSup hbdd (Set.mem_range_self ω))

/-- The order unit has norm exactly `1`. -/
@[simp]
lemma orderUnitNorm_one [Nontrivial E] : orderUnitNorm (1 : E) = 1 := by
  rw [← sSup_abs_apply_eq_orderUnitNorm]
  obtain ⟨ω₀⟩ := (inferInstance : Nonempty (𝓢[ℝ, E]))
  have hrange : (Set.range fun ω : 𝓢[ℝ, E] => |ω (1 : E)|) = {1} := by
    ext y
    constructor
    · rintro ⟨ω, rfl⟩; simp
    · rintro rfl; exact ⟨ω₀, by simp⟩
  rw [hrange, csSup_singleton]

/-!

## D. Separation of points

-/

/-- States separate points: if `ω A = ω B` for every state `ω`, then `A = B`. -/
lemma ext_of_forall_apply_eq [Nontrivial E] {A B : E} (h : ∀ ω : 𝓢[ℝ, E], ω A = ω B) : A = B := by
  have h0 : orderUnitNorm (A - B) = 0 := by
    rw [← sSup_abs_apply_eq_orderUnitNorm]
    have hrange : (Set.range fun ω : 𝓢[ℝ, E] => |ω (A - B)|) = {0} := by
      ext y
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨ω, rfl⟩; rw [map_sub, h ω, sub_self, abs_zero]
      · rintro rfl
        obtain ⟨ω⟩ := (inferInstance : Nonempty (𝓢[ℝ, E]))
        exact ⟨ω, by rw [map_sub, h ω, sub_self, abs_zero]⟩
    rw [hrange, csSup_singleton]
  exact sub_eq_zero.mp (orderUnitNorm_eq_zero_iff.mp h0)

end UnitalPositiveLinearMap
