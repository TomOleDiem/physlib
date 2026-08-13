/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!

# One-parameter subgroups of real Banach algebras

## i. Overview

Let `E` be a real Banach algebra. This file proves that every continuous additive character
`U : AddChar ℝ E` has the form `U(t) = exp (t • A)`, where `A = deriv U 0`.

This is the Banach-algebra argument underlying the correspondence between norm-continuous unitary
time evolutions and bounded self-adjoint Hamiltonians. See
`Physlib.QuantumMechanics.UnitaryTimeEvolution`, in
particular `QuantumMechanics.UnitaryTimeEvolution.stoneEquiv`, for the physical statement.

**Proof outline.** Continuity at zero implies that, for sufficiently small `d > 0`, the integral of
`U` over `[0, d]` is close to `d • 1` and therefore invertible. If `I` is the indefinite integral of
`U`, the homomorphism law gives `U(t) * I(d) = I(t + d) - I(t)`. This identity proves that `U` is
differentiable. Setting `A` to the derivative at zero then gives the differential equation
`U'(t) = U(t)A`. Consequently `U(t) * exp (-tA)` has zero derivative and is constant. Uniqueness
follows by differentiating two exponential representations at zero.

## ii. Key results

* `OneParameterSubgroup.apply_eq_exp_smul_deriv`: A continuous one-parameter subgroup is the
  exponential of its derivative at zero.
* `OneParameterSubgroup.generator_unique`: Any exponential generator equals the derivative at zero.

## iii. References

-/

@[expose] public section

open Filter Topology

noncomputable section

namespace OneParameterSubgroup

variable {E : Type*} [NormedRing E]

variable [NormedAlgebra ℝ E] [CompleteSpace E]

/-- `NormedSpace.exp`'s API wants a `ℚ`-algebra structure (for the `1/n!` coefficients), which
isn't automatic from `NormedAlgebra ℝ E` alone; derive it once here rather than at each use site. -/
local instance : NormedAlgebra ℚ E := .restrictScalars ℚ ℝ E

lemma exists_isUnit_intervalIntegral [Nontrivial E] (U : AddChar ℝ E) (hU : Continuous U) :
    ∃ d : ℝ, 0 < d ∧ IsUnit (∫ x in (0 : ℝ)..d, U x) := by
  let c : ℝ := ‖(1 : E)‖⁻¹ / 2
  have hone : 0 < ‖(1 : E)‖ := norm_pos_iff.mpr one_ne_zero
  have hc : 0 < c := by dsimp [c]; positivity
  have hevent : ∀ᶠ x : ℝ in 𝓝 0, ‖U x - 1‖ < c := by
    have hnorm : Continuous (fun x : ℝ => ‖U x - 1‖) :=
      continuous_norm.comp (hU.sub continuous_const)
    have hmem : Set.Iio c ∈ 𝓝 ‖U 0 - 1‖ := by simpa using Iio_mem_nhds hc
    exact hnorm.continuousAt hmem
  rw [Metric.eventually_nhds_iff] at hevent
  obtain ⟨r, hr, hrU⟩ := hevent
  let d := r / 2
  have hd : 0 < d := by dsimp [d]; positivity
  let q : Eˣ := {
    val := d • 1
    inv := d⁻¹ • 1
    val_inv := by rw [smul_mul_smul_comm, mul_inv_cancel₀ hd.ne', one_smul, one_mul]
    inv_val := by rw [smul_mul_smul_comm, inv_mul_cancel₀ hd.ne', one_smul, one_mul] }
  have hnear : ‖(∫ x in (0 : ℝ)..d, U x) - (q : E)‖ < ‖(↑q⁻¹ : E)‖⁻¹ := by
    have hqd : (q : E) = d • 1 := rfl
    have hrewrite : (∫ x in (0 : ℝ)..d, U x) - (q : E) =
        ∫ x in (0 : ℝ)..d, (U x - 1) := by
      rw [hqd]
      calc
        (∫ x in (0 : ℝ)..d, U x) - d • 1 =
            (∫ x in (0 : ℝ)..d, U x) - ∫ _x in (0 : ℝ)..d, (1 : E) := by
              rw [intervalIntegral.integral_const, sub_zero]
        _ = ∫ x in (0 : ℝ)..d, (U x - 1) :=
          (intervalIntegral.integral_sub (hU.intervalIntegrable 0 d)
            (continuous_const.intervalIntegrable 0 d)).symm
    rw [hrewrite]
    have hle : ‖∫ x in (0 : ℝ)..d, (U x - 1)‖ ≤ c * d := by
      calc
        _ ≤ c * |d - 0| := intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
          apply le_of_lt
          apply hrU
          rw [Real.dist_0_eq_abs]
          rw [Set.uIoc_of_le hd.le] at hx
          rw [abs_of_nonneg hx.1.le]
          exact hx.2.trans_lt (by dsimp [d]; linarith))
        _ = c * d := by rw [sub_zero, abs_of_pos hd]
    have hright : ‖(↑q⁻¹ : E)‖⁻¹ = d * ‖(1 : E)‖⁻¹ := by
      have hqinv : (↑q⁻¹ : E) = d⁻¹ • (1 : E) := rfl
      rw [hqinv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hd]
      field_simp
    rw [hright]
    refine hle.trans_lt ?_
    dsimp [c]
    nlinarith [inv_pos.mpr hone]
  exact ⟨d, hd, (Units.ofNearby q _ hnear).isUnit⟩

lemma differentiable [Nontrivial E] (U : AddChar ℝ E) (hU : Continuous U) :
    Differentiable ℝ U := by
  obtain ⟨d, _, hV⟩ := exists_isUnit_intervalIntegral U hU
  let V : E := ∫ x in (0 : ℝ)..d, U x
  let v : Eˣ := hV.unit
  have hv : (v : E) = V := hV.unit_spec
  let F : ℝ → E := fun t => ∫ x in (0 : ℝ)..t, U x
  have hF (t : ℝ) : HasDerivAt F (U t) t :=
    (hU.integral_hasStrictDerivAt 0 t).hasDerivAt
  have htranslate (t : ℝ) : U t * V = F (t + d) - F t := by
    have hmul : U t * V = ∫ x in (0 : ℝ)..d, U (t + x) := by
      let L : E →L[ℝ] E :=
        (LinearMap.mulLeft ℝ (U t)).mkContinuous ‖U t‖
          (fun x => norm_mul_le _ _)
      change U t * (∫ x in (0 : ℝ)..d, U x) = _
      calc
        _ = L (∫ x in (0 : ℝ)..d, U x) := rfl
        _ = ∫ x in (0 : ℝ)..d, L (U x) :=
          (L.intervalIntegral_comp_comm (hU.intervalIntegrable 0 d)).symm
        _ = ∫ x in (0 : ℝ)..d, U (t + x) := by
          apply intervalIntegral.integral_congr
          intro x _
          exact (U.map_add_eq_mul t x).symm
    rw [hmul]
    dsimp only [F]
    rw [intervalIntegral.integral_comp_add_left]
    simp only [add_zero]
    rw [eq_sub_iff_add_eq, add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume) (hU.intervalIntegrable 0 t)
      (hU.intervalIntegrable t (t + d))
  intro t
  have hR : HasDerivAt (fun s : ℝ => F (s + d) - F s)
      (U (t + d) - U t) t := by
    exact (HasDerivAt.comp_add_const t d (hF (t + d))).sub (hF t)
  have heq : U = fun s : ℝ => (F (s + d) - F s) * (↑v⁻¹ : E) := by
    funext s
    calc
      U s = (U s * (v : E)) * (↑v⁻¹ : E) := by simp
      _ = (F (s + d) - F s) * (↑v⁻¹ : E) := by rw [hv, htranslate]
  rw [heq]
  exact (hR.mul_const (↑v⁻¹ : E)).differentiableAt

lemma apply_eq_exp_smul_deriv (U : AddChar ℝ E) (hU : Continuous U) (t : ℝ) :
    U t = NormedSpace.exp (t • deriv U 0) := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
      let : Subsingleton E := h
      exact Subsingleton.elim _ _
  | inr h =>
    let : Nontrivial E := h
    have hdiff : Differentiable ℝ U := differentiable U hU
    let A : E := deriv U 0
    have hUderiv (t : ℝ) : HasDerivAt U (U t * A) t := by
      have ht : HasDerivAt U (deriv U t) t :=
        hdiff.differentiableAt.hasDerivAt
      have h0 : HasDerivAt U (deriv U 0) 0 :=
        hdiff.differentiableAt.hasDerivAt
      have hleft : HasDerivAt (fun s : ℝ => U (t + s)) (deriv U t) 0 :=
        HasDerivAt.comp_const_add t 0 (by simpa using ht)
      have hright : HasDerivAt (fun s : ℝ => U t * U s) (U t * A) 0 := by
        dsimp only [A]
        exact HasDerivAt.const_mul (U t) h0
      have heq : (fun s : ℝ => U (t + s)) = fun s : ℝ => U t * U s := by
        funext s
        exact U.map_add_eq_mul t s
      have hder : deriv U t = U t * A := hleft.unique (heq ▸ hright)
      rwa [← hder]
    have hE (t : ℝ) : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (-A)))
      (NormedSpace.exp (t • (-A)) * (-A)) t := hasDerivAt_exp_smul_const (-A) t
    let G : ℝ → E := fun t => U t * NormedSpace.exp (t • (-A))
    have hG : Differentiable ℝ G := fun t => ((hUderiv t).mul (hE t)).differentiableAt
    have hGder (t : ℝ) : deriv G t = 0 := by
      apply ((hUderiv t).mul (hE t)).deriv.trans
      have hcomm : Commute A (NormedSpace.exp (t • (-A))) := by
        exact ((Commute.refl A).neg_right.smul_right t).exp_right
      rw [mul_assoc, hcomm.eq]
      noncomm_ring
    have hconst (t : ℝ) : G t = G 0 := is_const_of_deriv_eq_zero hG hGder t 0
    have hone : U t * NormedSpace.exp (t • (-A)) = 1 := by
      simpa [G] using hconst t
    have hneg : t • (-A) = -(t • A) := by module
    have hinv : NormedSpace.exp (t • (-A)) = Ring.inverse (NormedSpace.exp (t • A)) := by
      rw [hneg]
      exact (Ring.inverse_exp (t • A)).symm
    rw [hinv] at hone
    have hexp : IsUnit (NormedSpace.exp (t • A)) := NormedSpace.isUnit_exp (t • A)
    let e : Eˣ := hexp.unit
    have he : (e : E) = NormedSpace.exp (t • A) := hexp.unit_spec
    rw [← he, Ring.inverse_unit] at hone
    calc
      U t = (U t * (↑e⁻¹ : E)) * (e : E) := by simp
      _ = NormedSpace.exp (t • A) := by
        rw [hone, one_mul, he]

/-- Any exponential generator of a one-parameter subgroup is its derivative at zero. -/
lemma generator_unique (U : AddChar ℝ E) (A : E)
    (h : ∀ t : ℝ, U t = NormedSpace.exp (t • A)) : A = deriv U 0 := by
  have hfun : U = fun t : ℝ => NormedSpace.exp (t • A) := funext h
  rw [hfun]
  exact (by simpa using (hasDerivAt_exp_smul_const A (0 : ℝ)).deriv.symm)

end OneParameterSubgroup
