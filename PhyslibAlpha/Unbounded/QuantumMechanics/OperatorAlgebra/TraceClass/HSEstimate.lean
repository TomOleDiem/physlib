/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.HSAlgebra

/-!
# Quantitative Hilbert--Schmidt module estimates

The qualitative bounded-module theorem says that `S * A` is Hilbert--Schmidt
when `S` is.  This file exports the corresponding square-sum inequality in a
form useful for quantitative positive trace-class estimates.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace HilbertSchmidt

theorem tsum_norm_sq_mul_right_le_of_selfAdjoint {S A : B(H)}
    (hSself : IsSelfAdjoint S) (hS : IsHilbertSchmidt S)
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H) :
    (∑' i : w', ‖(S * A) (c i)‖ ^ 2) ≤
      ‖A‖ ^ 2 * (∑' j : w, ‖S (b j)‖ ^ 2) := by
  let R : B(H) := S * A
  have hR : IsHilbertSchmidt R := by
    exact isHilbertSchmidt_mul_right hS
  have hRc : Summable (fun i : w' => ‖R (c i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w' c hR
  have hEq : HasSum (fun j : w =>
      ‖(ContinuousLinearMap.adjoint R) (b j)‖ ^ 2)
      (∑' i : w', ‖R (c i)‖ ^ 2) :=
    hasSum_norm_sq_apply_eq_adjoint c b hRc
  have hAdjSummable : Summable (fun j : w =>
      ‖(ContinuousLinearMap.adjoint R) (b j)‖ ^ 2) := hEq.summable
  have hSb : Summable (fun j : w => ‖S (b j)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hS
  have hRstar : ContinuousLinearMap.adjoint R =
      ContinuousLinearMap.adjoint A * S := by
    rw [show R = S ∘SL A by rfl, ContinuousLinearMap.adjoint_comp]
    rw [← ContinuousLinearMap.mul_def]
    rw [(ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself]
  have hpoint : ∀ j : w,
      ‖(ContinuousLinearMap.adjoint R) (b j)‖ ^ 2 ≤
        ‖A‖ ^ 2 * ‖S (b j)‖ ^ 2 := by
    intro j
    rw [hRstar, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    have hnorm : ‖ContinuousLinearMap.adjoint A‖ = ‖A‖ :=
      (ContinuousLinearMap.adjoint).norm_map A
    have hle : ‖ContinuousLinearMap.adjoint A (S (b j))‖ ≤
        ‖A‖ * ‖S (b j)‖ := by
      rw [← hnorm]
      exact ContinuousLinearMap.le_opNorm _ _
    calc
      ‖ContinuousLinearMap.adjoint A (S (b j))‖ ^ 2 ≤
          (‖A‖ * ‖S (b j)‖) ^ 2 := by
            exact (sq_le_sq₀ (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hle
      _ = ‖A‖ ^ 2 * ‖S (b j)‖ ^ 2 := by ring
  have hscaled : Summable (fun j : w => ‖A‖ ^ 2 * ‖S (b j)‖ ^ 2) :=
    hSb.mul_left (‖A‖ ^ 2)
  have hsum : (∑' j : w,
      ‖(ContinuousLinearMap.adjoint R) (b j)‖ ^ 2) ≤
      ∑' j : w, ‖A‖ ^ 2 * ‖S (b j)‖ ^ 2 :=
    hAdjSummable.tsum_le_tsum hpoint hscaled
  calc
    ∑' i : w', ‖(S * A) (c i)‖ ^ 2 =
        ∑' j : w, ‖(ContinuousLinearMap.adjoint R) (b j)‖ ^ 2 :=
      hEq.tsum_eq.symm
    _ ≤ ∑' j : w, ‖A‖ ^ 2 * ‖S (b j)‖ ^ 2 := hsum
    _ = ‖A‖ ^ 2 * (∑' j : w, ‖S (b j)‖ ^ 2) := tsum_mul_left

end HilbertSchmidt

end OperatorAlgebra
