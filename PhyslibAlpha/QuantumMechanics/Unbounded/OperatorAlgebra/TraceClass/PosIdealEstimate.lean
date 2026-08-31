/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.GeneralIdeal
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.PositiveIdeal
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.HSEstimate

/-!
# Quantitative positive trace-ideal estimate

The positive conjugation theorem gives trace-classness of `A⋆ P A`.  Here we
export its matching trace-norm estimate.  This is the exact positive-sector
bound needed before the general non-self-adjoint ideal theorem can be used in
the concrete `B(H)` predual construction.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem traceNorm_star_mul_mul_le_of_nonneg {P A : B(H)} (hP : 0 ≤ P)
    (hPclass : IsTraceClass P) :
    traceNorm (star A * P * A) (isTraceClass_star_mul_mul_of_nonneg hP hPclass) ≤
      ‖A‖ ^ 2 * traceNorm P hPclass := by
  let S : B(H) := CFC.sqrt P
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg P)
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP
  have hS : HilbertSchmidt.IsHilbertSchmidt S := by
    have h := TraceClass.isHilbertSchmidt_sqrt_abs_of_isTraceClass hPclass
    rw [CFC.abs_of_nonneg P hP] at h
    simpa only [S] using h
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hPnorm := traceNorm_eq_of_hilbertBasis hPclass b
  have hPdiag : ∀ j : w,
      (⟪b j, CFC.abs P (b j)⟫_ℂ).re = ‖S (b j)‖ ^ 2 := by
    intro j
    rw [CFC.abs_of_nonneg P hP]
    have hSstar : ContinuousLinearMap.adjoint S = S :=
      (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
    have hinner : ⟪b j, P (b j)⟫_ℂ = ⟪S (b j), S (b j)⟫_ℂ := by
      rw [← hSS]
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b j)) (b j), hSstar]
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hPsum : (∑' j : w, ‖S (b j)‖ ^ 2) = traceNorm P hPclass := by
    calc
      (∑' j : w, ‖S (b j)‖ ^ 2) =
          ∑' j : w, (⟪b j, CFC.abs P (b j)⟫_ℂ).re := by
            apply tsum_congr
            intro j
            exact (hPdiag j).symm
      _ = traceNorm P hPclass := hPnorm.symm
  obtain ⟨w', c, _⟩ := exists_hilbertBasis ℂ H
  let Q : B(H) := star A * P * A
  have hQ : IsTraceClass Q := isTraceClass_star_mul_mul_of_nonneg hP hPclass
  have hQnorm := traceNorm_eq_of_hilbertBasis hQ c
  have hQpos : 0 ≤ Q := by
    exact star_left_conjugate_nonneg hP A
  have hQdiag : ∀ i : w',
      (⟪c i, Q (c i)⟫_ℂ).re = ‖(S * A) (c i)‖ ^ 2 := by
    intro i
    have hSstar : ContinuousLinearMap.adjoint S = S :=
      (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
    have hinner : ⟪c i, Q (c i)⟫_ℂ =
        ⟪(S * A) (c i), (S * A) (c i)⟫_ℂ := by
      rw [show Q = star A * (S * S) * A by rw [hSS]]
      rw [ContinuousLinearMap.star_eq_adjoint A]
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [ContinuousLinearMap.adjoint_inner_right A]
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← hSstar, ContinuousLinearMap.adjoint_inner_right S, hSstar,
        ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  calc
    traceNorm Q hQ =
        ∑' i : w', (⟪c i, CFC.abs Q (c i)⟫_ℂ).re := hQnorm
    _ = ∑' i : w', ‖(S * A) (c i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      rw [CFC.abs_of_nonneg Q hQpos]
      exact hQdiag i
    _ ≤ ‖A‖ ^ 2 * (∑' j : w, ‖S (b j)‖ ^ 2) :=
      HilbertSchmidt.tsum_norm_sq_mul_right_le_of_selfAdjoint
        hSself hS b c
    _ = ‖A‖ ^ 2 * traceNorm P hPclass := by rw [hPsum]

theorem traceNorm_mul_mul_star_le_of_nonneg {P A : B(H)} (hP : 0 ≤ P)
    (hPclass : IsTraceClass P) :
    traceNorm (A * P * star A) (isTraceClass_mul_mul_star_of_nonneg hP hPclass) ≤
      ‖A‖ ^ 2 * traceNorm P hPclass := by
  simpa only [star_star, norm_star] using
    (traceNorm_star_mul_mul_le_of_nonneg (P := P) (A := star A) hP hPclass)

end OperatorAlgebra
