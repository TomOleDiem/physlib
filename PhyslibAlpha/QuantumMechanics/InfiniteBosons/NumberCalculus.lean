/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.HilbertSpace
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.ContinuousMap.Bounded.Star
/-!

# Bounded functions of the number operator

The spectral calculus of the occupation number of a mode, as a star homomorphism into the bounded
operators of the Fock Hilbert space.

## i. Overview

The occupation number `N_x` of a mode is diagonal in the occupation basis. It is an unbounded
operator on `ℓ²(Occ L)`. A bounded function `f` of the occupation number is the diagonal operator
that multiplies the coordinate `α` by `f(α_x)`. It is bounded by the supremum norm of `f`. The map
`f ↦ f(N_x)` is a star homomorphism of the C*-algebra of bounded functions on `ℕ` into the bounded
operators. On an occupation vector `|α⟩` it acts as the number `f(α_x)`, which is the value of `f`
at the eigenvalue of `N_x`. This is the bridge from the unbounded polynomial observable `N_x`
to bounded observables for this observable.

## ii. Key results

- `InfiniteBosons.diagOp`: the diagonal operator of a bounded sequence.
- `InfiniteBosons.numberCalculus`: the star homomorphism `f ↦ f(N_x)`.
- `InfiniteBosons.numberFunction_embed_single`: `f(N_x)|α⟩ = f(α_x)|α⟩`.

## iii. Table of contents

- A. Diagonal operators
- B. The calculus of the number operator

## iv. References

* K. Schmüdgen, Unbounded Self-adjoint Operators on Hilbert Space, Springer (2012), Chapter 4.
-/

@[expose] public section

open Finsupp BoundedContinuousFunction

noncomputable section

namespace InfiniteBosons

variable {B : Type*}

lemma memℓp_mul_two {c : B → ℂ} {C : ℝ} (hc : ∀ α, ‖c α‖ ≤ C) (f : HilbertSp B) :
    Memℓp (fun α => c α * f α) 2 := by
  have hf := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num)] at hf ⊢
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  rw [h2] at hf ⊢
  refine Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_)
    (hf.mul_left (C ^ (2 : ℝ)))
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) (hc α) (by norm_num))
    (by positivity)


set_option maxHeartbeats 1600000 in
lemma diag_tsum_le {c : B → ℂ} {C : ℝ} (hc : ∀ α, ‖c α‖ ≤ C) (f : HilbertSp B) :
    ∑' α, ‖c α * f α‖ ^ (2 : ℝ) ≤ (max C 0 * ‖f‖) ^ (2 : ℝ) := by
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  have hf := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num), h2] at hf
  have hnorm := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) f
  rw [h2] at hnorm
  have hg : Summable fun α => ‖c α * f α‖ ^ (2 : ℝ) := by
    have := memℓp_mul_two hc f
    rw [memℓp_gen_iff (by norm_num), h2] at this
    exact this
  rw [Real.mul_rpow (by positivity) (norm_nonneg _), hnorm, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun α => ?_) hg (hf.mul_left _)
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) ((hc α).trans (le_max_left _ _)) (by norm_num))
    (by positivity)

/-- The diagonal operator of a bounded sequence on `ℓ²(B)`. -/
def diagOp {c : B → ℂ} {C : ℝ} (hc : ∀ α, ‖c α‖ ≤ C) : HilbertSp B →L[ℂ] HilbertSp B :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun α => c α * f α, memℓp_mul_two hc f⟩
      map_add' := fun f g => Subtype.ext (funext fun α => by
        show c α * ((f + g : HilbertSp B) α) = c α * f α + c α * g α
        rw [lp.coeFn_add]; simp [mul_add])
      map_smul' := fun r f => Subtype.ext (funext fun α => by
        show c α * ((r • f : HilbertSp B) α) = r * (c α * f α)
        rw [lp.coeFn_smul]; simp [mul_left_comm]) }
    (max C 0) (fun f => by
      refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
      have h2 : (2 : ENNReal).toReal = 2 := by norm_num
      rw [h2]
      exact diag_tsum_le hc f)

lemma diagOp_apply {c : B → ℂ} {C : ℝ} (hc : ∀ α, ‖c α‖ ≤ C) (f : HilbertSp B) (α : B) :
    (diagOp hc f : HilbertSp B) α = c α * f α := rfl


lemma diagOp_mul {c d : B → ℂ} {C D : ℝ} (hc : ∀ α, ‖c α‖ ≤ C) (hd : ∀ α, ‖d α‖ ≤ D)
    (hcd : ∀ α, ‖c α * d α‖ ≤ C * D) :
    diagOp hcd = diagOp hc * diagOp hd := by
  refine ContinuousLinearMap.ext fun f => Subtype.ext (funext fun α => ?_)
  show c α * d α * f α = c α * (d α * f α)
  ring

lemma diagOp_add {c d : B → ℂ} {C D : ℝ} (hc : ∀ α, ‖c α‖ ≤ C) (hd : ∀ α, ‖d α‖ ≤ D)
    (hcd : ∀ α, ‖c α + d α‖ ≤ C + D) : diagOp hcd = diagOp hc + diagOp hd := by
  refine ContinuousLinearMap.ext fun f => Subtype.ext (funext fun α => ?_)
  show (c α + d α) * f α = c α * f α + d α * f α
  ring

lemma diagOp_one (h1 : ∀ α : B, ‖(1 : ℂ)‖ ≤ 1) : diagOp (c := fun _ : B => (1 : ℂ)) h1 = 1 := by
  refine ContinuousLinearMap.ext fun f => Subtype.ext (funext fun α => ?_)
  show (1 : ℂ) * f α = f α
  ring


lemma diagOp_adjoint {c : B → ℂ} {C : ℝ} (hc : ∀ α, ‖c α‖ ≤ C)
    (hc' : ∀ α, ‖starRingEnd ℂ (c α)‖ ≤ C) :
    ContinuousLinearMap.adjoint (diagOp hc) = diagOp hc' := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun α => ?_
  show inner ℂ (starRingEnd ℂ (c α) * f α) (g α) = inner ℂ (f α) (c α * g α)
  simp only [RCLike.inner_apply, map_mul, Complex.conj_conj]
  ring


/-- Bounded functions of the occupation number `N_x`, as bounded diagonal operators on `ℓ²`. -/
def numberFunction {L : Type*} [DecidableEq L] (x : L) (f : ℕ →ᵇ ℂ) :
    HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L) :=
  diagOp (c := fun α : Occ L => f (α x)) (C := ‖f‖) (fun α => f.norm_coe_le_norm (α x))

lemma numberFunction_apply {L : Type*} [DecidableEq L] (x : L) (f : ℕ →ᵇ ℂ)
    (g : HilbertSp (Occ L)) (α : Occ L) :
    (numberFunction x f g : HilbertSp (Occ L)) α = f (α x) * g α := rfl

/-- **The functional calculus of the number operator** is a star homomorphism from the bounded
functions on `ℕ` to the bounded operators of `ℓ²(Occ L)`. -/
def numberCalculus {L : Type*} [DecidableEq L] (x : L) :
    (ℕ →ᵇ ℂ) →⋆ₐ[ℂ] (HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L)) where
  toFun := numberFunction x
  map_one' := ContinuousLinearMap.ext fun g => Subtype.ext (funext fun α => by
    rw [numberFunction_apply]; simp)
  map_mul' f h := ContinuousLinearMap.ext fun g => Subtype.ext (funext fun α => by
    show (f * h) (α x) * g α = f (α x) * (h (α x) * g α)
    simp [mul_assoc])
  map_zero' := ContinuousLinearMap.ext fun g => Subtype.ext (funext fun α => by
    rw [numberFunction_apply]; simp)
  map_add' f h := ContinuousLinearMap.ext fun g => Subtype.ext (funext fun α => by
    show (f + h) (α x) * g α = f (α x) * g α + h (α x) * g α
    simp [add_mul])
  commutes' r := ContinuousLinearMap.ext fun g => Subtype.ext (funext fun α => by
    rw [numberFunction_apply]; simp [Algebra.algebraMap_eq_smul_one])
  map_star' f := by
    have := diagOp_adjoint (c := fun α : Occ L => f (α x)) (C := ‖f‖)
      (fun α => f.norm_coe_le_norm (α x))
      (fun α => by simpa using f.norm_coe_le_norm (α x))
    rw [ContinuousLinearMap.star_eq_adjoint]
    refine ContinuousLinearMap.ext fun g => Subtype.ext (funext fun α => ?_)
    have h2 := congrArg (fun T => (T g : HilbertSp (Occ L)) α) this
    simp only at h2
    show (star f) (α x) * g α = ((ContinuousLinearMap.adjoint (numberFunction x f)) g : HilbertSp (Occ L)) α
    rw [show numberFunction x f = diagOp (c := fun α : Occ L => f (α x)) (C := ‖f‖)
      (fun α => f.norm_coe_le_norm (α x)) from rfl, h2]
    rfl


lemma numberOp_basis {L : Type*} [DecidableEq L] (x : L) (α : Occ L) :
    (numberOp x).1.1 (single α 1) = ((α x : ℕ) : ℂ) • single α 1 := by
  show (cre x ∘ₗ ann x) (single α 1) = _
  rw [LinearMap.comp_apply]
  exact cre_ann_single_same x α

/-- **The bounded function of the number operator acts on an occupation vector by its value at the
eigenvalue**: `f(N_x) |α⟩ = f(α_x) |α⟩`. -/
lemma numberFunction_embed_single {L : Type*} [DecidableEq L] (x : L) (f : ℕ →ᵇ ℂ) (α : Occ L)
    (c : ℂ) :
    numberFunction x f (embed (single α c)) = f (α x) • embed (single α c) := by
  refine Subtype.ext (funext fun β => ?_)
  rw [numberFunction_apply, embed_single]
  show _ = f (α x) * (lp.single 2 α c : HilbertSp (Occ L)) β
  by_cases h : β = α
  · subst h; rfl
  · have : ((lp.single 2 α c : HilbertSp (Occ L)) β) = 0 := by
      simp [lp.single_apply, Pi.single_apply, h]
    rw [this]; simp

end InfiniteBosons
