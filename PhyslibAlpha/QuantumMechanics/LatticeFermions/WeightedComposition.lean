/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!

# Weighted composition operators on `ℓ²`

A map `g` of an index set and a weight `w` bounded by one give the bounded operator
`ψ ↦ (a ↦ w a * ψ (g a))` on `ℓ²`, provided `g` is injective where the weight does not vanish.

## i. Overview

The creation and annihilation operators of fermions, written in the occupation number basis of
the Fock space, move each basis vector to another basis vector and multiply it by a sign, or
send it to zero. On wave functions this is a *weighted composition*: `(T ψ)(a) = w a * ψ (g a)`.
If `|w| ≤ 1` and `g` is injective on the set where `w ≠ 0`, every term of `‖T ψ‖²` is bounded by a
distinct term of `‖ψ‖²`, so `T` is a bounded operator of norm at most one.

## ii. Key results

- `LatticeFermions.weightedComp` : the weighted composition operator.
- `LatticeFermions.weightedComp_apply` : its value at an index.
- `LatticeFermions.norm_weightedCompVec_le` : it does not increase norms.

## iii. Table of contents

- A. Square summability of the composed function
- B. The operator

## iv. References

* None.

-/

@[expose] public section

noncomputable section

namespace LatticeFermions

open scoped ENNReal

variable {α : Type*}

/-!

## A. Square summability of the composed function

-/

/-- The square of the norm of a vector of `ℓ²` is summable. -/
lemma summable_norm_rpow_two (ψ : lp (fun _ : α => ℂ) 2) :
    Summable fun a => ‖ψ a‖ ^ (2 : ℝ) := by
  have hψ := lp.memℓp ψ
  rw [memℓp_gen_iff (by norm_num)] at hψ
  simpa using hψ

/-- The square of the norm of a vector of `ℓ²` is the sum of the squares of its entries. -/
lemma norm_rpow_two_eq_tsum (ψ : lp (fun _ : α => ℂ) 2) :
    ‖ψ‖ ^ (2 : ℝ) = ∑' a, ‖ψ a‖ ^ (2 : ℝ) := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) ψ

variable (g : α → α) (w : α → ℂ)

/-- A summable nonnegative function composed with a map injective on a set, cut off outside the
set, is summable with a smaller sum. -/
lemma summable_indicator_comp {s : Set α} (hg : s.InjOn g) {f : α → ℝ} (hf0 : 0 ≤ f)
    (hf : Summable f) :
    Summable (s.indicator (f ∘ g)) ∧ ∑' a, s.indicator (f ∘ g) a ≤ ∑' b, f b := by
  have hsub : Summable (f ∘ s.domRestrict g) := hf.comp_injective hg.injective
  refine ⟨summable_subtype_iff_indicator.mp hsub, ?_⟩
  rw [← tsum_subtype]
  exact hsub.tsum_le_tsum_of_inj (s.domRestrict g) hg.injective (fun c _ => hf0 c)
    (fun _ => le_rfl) hf

/-- Each term of the squared norm of the composed function is bounded by the corresponding term
of the composed squared norm, cut off where the weight vanishes. -/
lemma norm_mul_rpow_two_le (hw : ∀ a, ‖w a‖ ≤ 1) (ψ : α → ℂ) (a : α) :
    ‖w a * ψ (g a)‖ ^ (2 : ℝ) ≤
      {a | w a ≠ 0}.indicator ((fun b => ‖ψ b‖ ^ (2 : ℝ)) ∘ g) a := by
  by_cases h : w a = 0
  · simp [h]
  rw [Set.indicator_of_mem (show a ∈ {a | w a ≠ 0} from h), norm_mul,
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_of_le_one_left (by positivity) (Real.rpow_le_one (norm_nonneg _) (hw a)
    (by norm_num))

variable {g w}

lemma summable_weightedComp (hw : ∀ a, ‖w a‖ ≤ 1) (hg : {a | w a ≠ 0}.InjOn g)
    (ψ : lp (fun _ : α => ℂ) 2) :
    Summable (fun a => ‖w a * ψ (g a)‖ ^ (2 : ℝ)) ∧
      ∑' a, ‖w a * ψ (g a)‖ ^ (2 : ℝ) ≤ ∑' b, ‖ψ b‖ ^ (2 : ℝ) := by
  obtain ⟨hs, hle⟩ := summable_indicator_comp g hg (fun b => by positivity)
    (summable_norm_rpow_two ψ)
  have hs' : Summable (fun a => ‖w a * ψ (g a)‖ ^ (2 : ℝ)) :=
    Summable.of_nonneg_of_le (fun a => by positivity) (norm_mul_rpow_two_le g w hw ψ) hs
  exact ⟨hs', (hs'.tsum_le_tsum (norm_mul_rpow_two_le g w hw ψ) hs).trans hle⟩

lemma memℓp_weightedComp (hw : ∀ a, ‖w a‖ ≤ 1) (hg : {a | w a ≠ 0}.InjOn g)
    (ψ : lp (fun _ : α => ℂ) 2) : Memℓp (fun a => w a * ψ (g a)) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  simpa using (summable_weightedComp hw hg ψ).1

/-!

## B. The operator

-/

/-- The vector `a ↦ w a * ψ (g a)` of `ℓ²`. -/
def weightedCompVec (hw : ∀ a, ‖w a‖ ≤ 1) (hg : {a | w a ≠ 0}.InjOn g)
    (ψ : lp (fun _ : α => ℂ) 2) : lp (fun _ : α => ℂ) 2 :=
  ⟨fun a => w a * ψ (g a), memℓp_weightedComp hw hg ψ⟩

lemma norm_weightedCompVec_le (hw : ∀ a, ‖w a‖ ≤ 1) (hg : {a | w a ≠ 0}.InjOn g)
    (ψ : lp (fun _ : α => ℂ) 2) : ‖weightedCompVec hw hg ψ‖ ≤ ‖ψ‖ := by
  have h : ‖weightedCompVec hw hg ψ‖ ^ (2 : ℝ) ≤ ‖ψ‖ ^ (2 : ℝ) := by
    rw [norm_rpow_two_eq_tsum, norm_rpow_two_eq_tsum]
    exact (summable_weightedComp hw hg ψ).2
  exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h

/-- The weighted composition operator `ψ ↦ (a ↦ w a * ψ (g a))` on `ℓ²`, for a weight bounded by
one and a map injective where the weight does not vanish. -/
def weightedComp (hw : ∀ a, ‖w a‖ ≤ 1) (hg : {a | w a ≠ 0}.InjOn g) :
    lp (fun _ : α => ℂ) 2 →L[ℂ] lp (fun _ : α => ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := weightedCompVec hw hg
      map_add' := fun ψ φ => lp.ext (funext fun a => by
        simp [weightedCompVec, mul_add]; rfl)
      map_smul' := fun c ψ => lp.ext (funext fun a => by
        simp only [weightedCompVec, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring) }
    1 (fun ψ => by simpa using norm_weightedCompVec_le hw hg ψ)

@[simp]
lemma weightedComp_apply (hw : ∀ a, ‖w a‖ ≤ 1) (hg : {a | w a ≠ 0}.InjOn g)
    (ψ : lp (fun _ : α => ℂ) 2) (a : α) : weightedComp hw hg ψ a = w a * ψ (g a) := rfl

end LatticeFermions
