/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.HilbertSchmidt

/-!
# Algebraic Hilbert--Schmidt consequences

This module supplies the elementary linear closure of the Hilbert--Schmidt square-sum predicate.
It also connects that predicate to the existing trace-class predicate through `S⋆S`.  These are
the algebraic ingredients for the usual polarization proof that a product of two Hilbert--Schmidt
operators is trace class; no such product theorem is asserted here yet.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace HilbertSchmidt

/-- The zero operator is Hilbert--Schmidt. -/
theorem isHilbertSchmidt_zero : IsHilbertSchmidt (0 : B(H)) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  refine ⟨w, b, ?_⟩
  simpa using (summable_zero : Summable (fun _ : w => (0 : ℝ)))

/-- Hilbert--Schmidt operators are closed under scalar multiplication. -/
@[nolint unusedArguments]
theorem isHilbertSchmidt_smul {S : B(H)} (c : ℂ) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (c • S) := by
  rcases hS with ⟨w, b, hb⟩
  refine ⟨w, b, ?_⟩
  have hmul := hb.mul_left (‖c‖ ^ 2)
  apply hmul.congr
  intro i
  rw [ContinuousLinearMap.smul_apply, norm_smul]
  ring

/-- Hilbert--Schmidt operators are closed under addition. -/
theorem isHilbertSchmidt_add {R S : B(H)}
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (R + S) := by
  rcases hR with ⟨w, b, hbR⟩
  have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hS
  refine ⟨w, b, ?_⟩
  apply Summable.of_nonneg_of_le (fun i => sq_nonneg _)
  · intro i
    have hnorm : ‖R (b i) + S (b i)‖ ≤ ‖R (b i)‖ + ‖S (b i)‖ :=
      norm_add_le _ _
    have hsq : ‖R (b i) + S (b i)‖ ^ 2 ≤
        (‖R (b i)‖ + ‖S (b i)‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
    calc
      ‖(R + S) (b i)‖ ^ 2 = ‖R (b i) + S (b i)‖ ^ 2 := by rfl
      _ ≤ (‖R (b i)‖ + ‖S (b i)‖) ^ 2 := hsq
      _ ≤ 2 * ‖R (b i)‖ ^ 2 + 2 * ‖S (b i)‖ ^ 2 := by
        nlinarith [sq_nonneg (‖R (b i)‖ - ‖S (b i)‖)]
  · exact (hbR.mul_left 2).add (hSb.mul_left 2)

/-- Hilbert--Schmidt operators are closed under subtraction. -/
theorem isHilbertSchmidt_sub {R S : B(H)}
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (R - S) := by
  simpa [sub_eq_add_neg] using isHilbertSchmidt_add hR
    (isHilbertSchmidt_smul (-1 : ℂ) hS)

/-- The adjoint of a Hilbert--Schmidt operator is Hilbert--Schmidt. -/
theorem isHilbertSchmidt_star {S : B(H)} (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (star S) := by
  rcases hS with ⟨w, b, hb⟩
  refine ⟨w, b, ?_⟩
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact summable_norm_sq_adjoint_of_summable_norm_sq b hb

/-! ### Bounded module structure

The two-sided bounded-module closure is kept next to the Hilbert--Schmidt
predicate itself.  It is elementary at the level of the defining square sum,
but it is an important contract for every later trace-ideal construction. -/

/-- Left multiplication by a contraction preserves the Hilbert--Schmidt
square-sum predicate. -/
@[nolint unusedArguments]
theorem isHilbertSchmidt_mul_left_of_opNorm_le_one {U S : B(H)}
    (hU : ‖U‖ ≤ 1) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (U * S) := by
  rcases hS with ⟨w, b, hb⟩
  refine ⟨w, b, ?_⟩
  apply Summable.of_nonneg_of_le (fun i => sq_nonneg _)
    (fun i => ?_) hb
  have hi : ‖U (S (b i))‖ ≤ ‖S (b i)‖ := by
    calc
      ‖U (S (b i))‖ ≤ ‖U‖ * ‖S (b i)‖ := U.le_opNorm _
      _ ≤ ‖S (b i)‖ := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hU (norm_nonneg (S (b i)))
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hi

/-- Right multiplication by a contraction preserves the Hilbert--Schmidt
square-sum predicate. -/
theorem isHilbertSchmidt_mul_right_of_opNorm_le_one {S U : B(H)}
    (hU : ‖U‖ ≤ 1) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (S * U) := by
  have hU' : ‖star U‖ ≤ 1 := by simpa using hU
  have hleft : IsHilbertSchmidt (star U * star S) :=
    isHilbertSchmidt_mul_left_of_opNorm_le_one hU'
      (isHilbertSchmidt_star hS)
  have hdouble : IsHilbertSchmidt (star (star U * star S)) :=
    isHilbertSchmidt_star hleft
  simpa only [star_mul, star_star] using hdouble

/-- The general bounded-module estimates, with the operator norm made explicit
by scaling the bounded factor. -/
theorem isHilbertSchmidt_mul_left {U S : B(H)}
    (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (U * S) := by
  by_cases hU0 : ‖U‖ = 0
  · have hzero : U = 0 := norm_eq_zero.mp hU0
    simpa [hzero] using isHilbertSchmidt_zero (H := H)
  · let V : B(H) := (‖U‖ : ℂ)⁻¹ • U
    have hV : ‖V‖ ≤ 1 := by
      dsimp [V]
      simp [norm_smul, norm_inv, hU0]
    have hVS : IsHilbertSchmidt (V * S) :=
      isHilbertSchmidt_mul_left_of_opNorm_le_one hV hS
    have hscaled : IsHilbertSchmidt ((‖U‖ : ℂ) • (V * S)) :=
      isHilbertSchmidt_smul (‖U‖ : ℂ) hVS
    have hVeq : (‖U‖ : ℂ) • V = U := by
      ext x
      simp [V, hU0]
    rw [show (‖U‖ : ℂ) • (V * S) = ((‖U‖ : ℂ) • V) * S by
      simp [smul_mul_assoc]] at hscaled
    rw [hVeq] at hscaled
    exact hscaled

theorem isHilbertSchmidt_mul_right {S U : B(H)}
    (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (S * U) := by
  have hleft : IsHilbertSchmidt (star U * star S) :=
    isHilbertSchmidt_mul_left (U := star U) (isHilbertSchmidt_star hS)
  have hdouble : IsHilbertSchmidt (star (star U * star S)) :=
    isHilbertSchmidt_star hleft
  simpa only [star_mul, star_star] using hdouble

/-- `S⋆S` is trace class whenever `S` is Hilbert--Schmidt. -/
theorem isTraceClass_star_mul_self_of_isHilbertSchmidt {S : B(H)}
    (hS : IsHilbertSchmidt S) :
    IsTraceClass (star S * S) := by
  apply isTraceClass_iff.mpr
  intro w b
  have hdiag : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hS
  have hpos : 0 ≤ star S * S := star_mul_self_nonneg S
  have habs : CFC.abs (star S * S) = star S * S :=
    CFC.abs_of_nonneg _ hpos
  apply hdiag.congr
  intro i
  rw [habs]
  have hinner : ⟪b i, (star S * S) (b i)⟫_ℂ =
      ⟪S (b i), S (b i)⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
  rw [hinner, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- `S S⋆` is trace class whenever `S` is Hilbert--Schmidt.  This is the
adjoint companion of `S⋆S` and is needed for symmetric trace arguments. -/
theorem isTraceClass_mul_star_of_isHilbertSchmidt {S : B(H)}
    (hS : IsHilbertSchmidt S) :
    IsTraceClass (S * star S) := by
  have hstar : IsHilbertSchmidt (star S) := isHilbertSchmidt_star hS
  simpa only [star_star] using
    (isTraceClass_star_mul_self_of_isHilbertSchmidt hstar)

/-- The trace norm of `S⋆S` is the Hilbert--Schmidt square sum of `S`, in
any Hilbert basis.  This is the quantitative form of
`isTraceClass_star_mul_self_of_isHilbertSchmidt`. -/
theorem traceNorm_star_mul_self_eq_tsum_norm_sq {S : B(H)}
    (hS : IsHilbertSchmidt S) {w : Set H} (b : HilbertBasis w ℂ H) :
    traceNorm (star S * S)
        (isTraceClass_star_mul_self_of_isHilbertSchmidt hS) =
      ∑' i : w, ‖S (b i)‖ ^ 2 := by
  let hT : IsTraceClass (star S * S) :=
    isTraceClass_star_mul_self_of_isHilbertSchmidt hS
  have htrace := traceNorm_eq_of_hilbertBasis hT b
  have hpos : 0 ≤ star S * S := star_mul_self_nonneg S
  have habs : CFC.abs (star S * S) = star S * S :=
    CFC.abs_of_nonneg _ hpos
  have hdiag : ∀ i : w,
      (⟪b i, CFC.abs (star S * S) (b i)⟫_ℂ).re = ‖S (b i)‖ ^ 2 := by
    intro i
    rw [habs]
    have hinner : ⟪b i, (star S * S) (b i)⟫_ℂ =
        ⟪S (b i), S (b i)⟫_ℂ := by
      rw [ContinuousLinearMap.star_eq_adjoint]
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [ContinuousLinearMap.adjoint_inner_right]
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  calc
    traceNorm (star S * S) hT =
        ∑' i : w, (⟪b i, CFC.abs (star S * S) (b i)⟫_ℂ).re := htrace
    _ = ∑' i : w, ‖S (b i)‖ ^ 2 := by
      apply tsum_congr
      exact hdiag

/-- The companion trace-norm formula for `S S⋆`. -/
theorem traceNorm_mul_star_eq_tsum_norm_sq {S : B(H)}
    (hS : IsHilbertSchmidt S) {w : Set H} (b : HilbertBasis w ℂ H) :
    traceNorm (S * star S)
        (isTraceClass_mul_star_of_isHilbertSchmidt hS) =
      ∑' i : w, ‖(star S) (b i)‖ ^ 2 := by
  simpa only [star_star] using
    (traceNorm_star_mul_self_eq_tsum_norm_sq
      (S := star S) (isHilbertSchmidt_star hS) b)

end HilbertSchmidt

end OperatorAlgebra
