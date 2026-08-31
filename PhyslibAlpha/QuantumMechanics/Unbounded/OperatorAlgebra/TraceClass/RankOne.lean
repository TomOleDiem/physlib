/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.GeneralIdeal

/-!
# Rank-one positive operators in the trace-class API

This file records the rank-one calculation needed by the concrete predual
construction.  It deliberately starts with the positive rank-one operator
`InnerProductSpace.rankOne ℂ x x`: its trace-class proof is just Parseval, so it
does not depend on the still-unfinished general product ideal theorem.

The resulting formula is also the normalization check for vector states and
the lower-bound test used later to identify the predual norm.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TraceClass

@[nolint unusedArguments]
private lemma rankOne_self_diagonal {x : H} {w : Set H}
    (b : HilbertBasis w ℂ H) (i : w) :
    (⟪b i, (InnerProductSpace.rankOne ℂ x x) (b i)⟫_ℂ).re =
      ‖⟪x, b i⟫_ℂ‖ ^ 2 := by
  simp only [InnerProductSpace.rankOne_apply]
  rw [inner_smul_right]
  rw [← inner_conj_symm x (b i), RCLike.conj_mul]
  norm_num [Complex.ofReal, pow_two, Complex.mul_re, norm_inner_symm]

lemma isTraceClass_rankOne_self (x : H) :
    IsTraceClass (InnerProductSpace.rankOne ℂ x x) := by
  apply isTraceClass_iff.mpr
  intro w b
  rw [CFC.abs_of_nonneg _ ((operator_nonneg_iff_isPositive _).mpr
    (InnerProductSpace.isPositive_rankOne_self x))]
  have h := (HilbertSchmidt.hasSum_norm_sq_inner b x).summable
  apply h.congr
  intro i
  simpa only [rankOne_self_diagonal, ← inner_conj_symm x (b i), RCLike.norm_conj]

theorem trace_rankOne_self (x : H) :
    trace (InnerProductSpace.rankOne ℂ x x) (isTraceClass_rankOne_self x) =
      (‖x‖ ^ 2 : ℝ) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [trace_eq_of_hilbertBasis (isTraceClass_rankOne_self x) b]
  have h := HilbertSchmidt.hasSum_norm_sq_inner b x
  have hdiag : (fun i : w =>
      ⟪b i, (InnerProductSpace.rankOne ℂ x x) (b i)⟫_ℂ) =
      (fun i : w => ((‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ)) := by
    funext i
    simp only [InnerProductSpace.rankOne_apply]
    rw [inner_smul_right]
    rw [← inner_conj_symm x (b i), RCLike.conj_mul]
    norm_cast
  rw [hdiag]
  exact (Complex.hasSum_ofReal.mpr h).tsum_eq

theorem traceNorm_rankOne_self (x : H) :
    traceNorm (InnerProductSpace.rankOne ℂ x x) (isTraceClass_rankOne_self x) =
      ‖x‖ ^ 2 := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [traceNorm_eq_of_hilbertBasis (isTraceClass_rankOne_self x) b]
  have h := HilbertSchmidt.hasSum_norm_sq_inner b x
  have hdiag : (fun i : w =>
      (⟪b i, CFC.abs (InnerProductSpace.rankOne ℂ x x) (b i)⟫_ℂ).re) =
      (fun i : w => ‖⟪b i, x⟫_ℂ‖ ^ 2) := by
    funext i
    rw [CFC.abs_of_nonneg _ ((operator_nonneg_iff_isPositive _).mpr
      (InnerProductSpace.isPositive_rankOne_self x))]
    simpa only [rankOne_self_diagonal, ← inner_conj_symm x (b i), RCLike.norm_conj]
  rw [hdiag]
  exact h.tsum_eq

end TraceClass

end OperatorAlgebra
