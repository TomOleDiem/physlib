/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.ReferenceOperator
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.HilbertSpace
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.HoppingSelfAdjoint
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.NumberCalculus
/-!

# Graph-norm domination by the reference operator

The annihilation operator of a mode in `X` is controlled by `K_X` in the Hilbert space norm.

## i. Overview

The quadratic form of `K_X` dominates the quadratic form of `N_x` for `x ∈ X`. The quadratic form
of `N_x` is the squared norm of `a_x f`. The quadratic form of `K_X` is bounded by `‖f‖ ‖K_X f‖`.
Hence `‖a_x f‖² ≤ ‖f‖ ‖K_X f‖`. This is a statement in the Hilbert space `ℓ²`, not only in the
algebraic pairing. It shows that the domain of the closure of `K_X` lies in the domain of the
closure of `a_x`.

## ii. Key results

- `InfiniteBosons.qform_refOp_le_norm`: `⟨f, K_X f⟩ ≤ ‖f‖ ‖K_X f‖`.
- `InfiniteBosons.annOp_graph_bound`: `‖a_x f‖² ≤ ‖f‖ ‖K_X f‖` for `x ∈ X`.
- `InfiniteBosons.numberOp_graph_bound`: `‖N_x f‖ ≤ ‖K_X f‖` for `x ∈ X`.
- `InfiniteBosons.quartic_graph_bound`: `‖N_x (N_x - 1) f‖ ≤ ‖K_X² f‖` for `x ∈ X`.

## iii. Table of contents

- A. The bound

## iv. References

* J. Dereziński, C. Gérard, Mathematics of Quantization and Quantum Fields, Cambridge University
  Press (2013), Section 17.1.
-/

@[expose] public section

open Finsupp

noncomputable section
namespace InfiniteBosons
variable {L : Type*} [DecidableEq L]

lemma qform_refOp_le_norm (X : Finset L) (f : FockPre L) :
    (qform (refOp X) f).re ≤ ‖embed f‖ * ‖embed ((refOp X).1.1 f)‖ := by
  have h : qform (refOp X) f = inner ℂ (embed f) (embed ((refOp X).1.1 f)) := by
    rw [inner_embed]; rfl
  rw [h]
  exact (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)

/-- **Graph-norm domination of the annihilation operator by `K_X`.**
`‖a_x f‖² ≤ ‖f‖ ‖K_X f‖` for `x ∈ X`. -/
theorem annOp_graph_bound {X : Finset L} {x : L} (hx : x ∈ X) (f : FockPre L) :
    ‖embed ((annOp x).1.1 f)‖ ^ 2 ≤ ‖embed f‖ * ‖embed ((refOp X).1.1 f)‖ := by
  have h1 : ‖embed ((annOp x).1.1 f)‖ ^ 2 = (qform (numberOp x) f).re := by
    have : numberOp x = star (annOp x) * annOp x := by rw [star_annOp]; rfl
    rw [this, qform_star_mul_self]
    have := inner_embed ((annOp x).1.1 f) ((annOp x).1.1 f)
    have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed ((annOp x).1.1 f))
    rw [this] at h2
    have h3 : (pair ((annOp x).1.1 f) ((annOp x).1.1 f)).re =
        ‖embed ((annOp x).1.1 f)‖ ^ 2 := by
      rw [h2]; simp [pow_two, Complex.mul_re]
    exact h3.symm
  rw [h1]
  exact (qform_numberOp_le_refOp hx f).trans (qform_refOp_le_norm X f)

lemma refOp_apply_coord (X : Finset L) (g : Occ L →₀ ℂ) (α : Occ L) :
    ((refOp X).1.1 g) α = ((1 + ∑ x ∈ X, (α x : ℝ) : ℝ) : ℂ) * g α := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, mul_add]
  | single β d =>
    have : single β d = d • single β (1 : ℂ) := by simp
    rw [this, map_smul, refOp_basis]
    by_cases h : β = α
    · subst h; simp; ring
    · simp [Finsupp.single_apply, h]

lemma coord_support_subset {T : (Occ L →₀ ℂ) →ₗ[ℂ] (Occ L →₀ ℂ)} (c : Occ L → ℂ)
    (hT : ∀ g α, (T g) α = c α * g α) (f : Occ L →₀ ℂ) : (T f).support ⊆ f.support := by
  intro α hα
  rw [Finsupp.mem_support_iff] at hα ⊢
  intro h; apply hα; rw [hT, h, mul_zero]

lemma pair_self_eq_sum {T : (Occ L →₀ ℂ) →ₗ[ℂ] (Occ L →₀ ℂ)} (c : Occ L → ℂ)
    (hT : ∀ g α, (T g) α = c α * g α) (f : Occ L →₀ ℂ) :
    pair (T f) (T f) = ∑ α ∈ f.support, (starRingEnd ℂ (c α * f α)) * (c α * f α) := by
  unfold pair
  rw [Finsupp.sum_of_support_subset _ (coord_support_subset c hT f) _ (fun α _ => by simp)]
  exact Finset.sum_congr rfl fun α _ => by rw [hT]

/-- **Relative bound `‖N_x f‖ ≤ ‖K_X f‖`** for `x ∈ X`, in the Hilbert norm. -/
theorem numberOp_graph_bound {X : Finset L} {x : L} (hx : x ∈ X) (f : Occ L →₀ ℂ) :
    ‖embed ((numberOp x).1.1 f)‖ ≤ ‖embed ((refOp X).1.1 f)‖ := by
  have h1 := pair_self_eq_sum (T := (numberOp x).1.1) (fun α => (α x : ℂ))
    (numberOp_apply_coord x) f
  have h2 := pair_self_eq_sum (T := (refOp X).1.1) (fun α => ((1 + ∑ y ∈ X, (α y : ℝ) : ℝ) : ℂ))
    (refOp_apply_coord X) f
  have hn : ∀ g : Occ L →₀ ℂ, ‖embed g‖ ^ 2 = (pair g g).re := fun g => by
    rw [← inner_embed g g]
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed g)
    rw [this]; simp [pow_two, Complex.mul_re]
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [hn, hn, h1, h2, Complex.re_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun α _ => ?_
  have hle : (α x : ℝ) ≤ 1 + ∑ y ∈ X, (α y : ℝ) := by
    have : (α x : ℝ) ≤ ∑ y ∈ X, (α y : ℝ) :=
      Finset.single_le_sum (f := fun y => (α y : ℝ)) (fun y _ => by positivity) hx
    linarith
  have hnn : (0 : ℝ) ≤ α x := by positivity
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  simp
  have hab := mul_self_le_mul_self hnn hle
  nlinarith [mul_le_mul_of_nonneg_right hab (add_nonneg (sq_nonneg (f α).re) (sq_nonneg (f α).im))]

lemma diag_norm_le {T S : (Occ L →₀ ℂ) →ₗ[ℂ] (Occ L →₀ ℂ)} (c d : Occ L → ℂ)
    (hT : ∀ g α, (T g) α = c α * g α) (hS : ∀ g α, (S g) α = d α * g α)
    (hcd : ∀ α, ‖c α‖ ≤ ‖d α‖) (f : Occ L →₀ ℂ) :
    ‖embed (T f)‖ ≤ ‖embed (S f)‖ := by
  have hn : ∀ g : Occ L →₀ ℂ, ‖embed g‖ ^ 2 = (pair g g).re := fun g => by
    rw [← inner_embed g g]
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed g)
    rw [this]; simp [pow_two, Complex.mul_re]
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [hn, hn, pair_self_eq_sum c hT, pair_self_eq_sum d hS, Complex.re_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun α _ => ?_
  have h1 : (starRingEnd ℂ (c α * f α) * (c α * f α)).re = ‖c α * f α‖ ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
  have h2 : (starRingEnd ℂ (d α * f α) * (d α * f α)).re = ‖d α * f α‖ ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
  rw [h1, h2, norm_mul, norm_mul]
  gcongr
  exact hcd α


/-- **Relative bound of the quartic term**: `‖N_x (N_x - 1) f‖ ≤ ‖K_X² f‖` for `x ∈ X`. -/
theorem quartic_graph_bound {X : Finset L} {x : L} (hx : x ∈ X) (f : Occ L →₀ ℂ) :
    ‖embed ((numberOp x * numberOp x - numberOp x).1.1 f)‖ ≤
      ‖embed ((refOp X * refOp X).1.1 f)‖ := by
  refine diag_norm_le (fun α => (α x : ℂ) * ((α x : ℂ) - 1))
    (fun α => ((1 + ∑ y ∈ X, (α y : ℝ) : ℝ) : ℂ) * ((1 + ∑ y ∈ X, (α y : ℝ) : ℝ) : ℂ))
    (fun g α => ?_) (fun g α => ?_) (fun α => ?_) f
  · show ((numberOp x).1.1 ((numberOp x).1.1 g) - (numberOp x).1.1 g) α = _
    rw [Finsupp.sub_apply, numberOp_apply_coord, numberOp_apply_coord]
    ring
  · show ((refOp X).1.1 ((refOp X).1.1 g)) α = _
    rw [refOp_apply_coord, refOp_apply_coord]
    ring
  · have hle : (α x : ℝ) ≤ 1 + ∑ y ∈ X, (α y : ℝ) := by
      have : (α x : ℝ) ≤ ∑ y ∈ X, (α y : ℝ) :=
        Finset.single_le_sum (f := fun y => (α y : ℝ)) (fun y _ => by positivity) hx
      linarith
    set a : ℝ := (α x : ℝ) with ha
    set b : ℝ := 1 + ∑ y ∈ X, (α y : ℝ) with hb
    have ha0 : 0 ≤ a := by positivity
    have hb1 : 1 ≤ b := by
      have : 0 ≤ ∑ y ∈ X, (α y : ℝ) := Finset.sum_nonneg fun y _ => by positivity
      linarith
    have h1 : ‖(a : ℂ) * ((a : ℂ) - 1)‖ = a * |a - 1| := by
      have : (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [norm_mul, this, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha0]
    have h2 : ‖(b : ℂ) * (b : ℂ)‖ = b * b := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ b)]
    have h3 : |a - 1| ≤ b := abs_le.mpr ⟨by linarith, by linarith⟩
    show ‖(a : ℂ) * ((a : ℂ) - 1)‖ ≤ ‖(b : ℂ) * (b : ℂ)‖
    rw [h1, h2]
    exact mul_le_mul hle h3 (abs_nonneg _) (by linarith)

end InfiniteBosons
