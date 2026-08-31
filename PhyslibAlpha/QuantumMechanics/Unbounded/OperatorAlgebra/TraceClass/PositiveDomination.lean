/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.PositiveIdeal

/-!
# Domination in the positive trace-class cone

This file exports the elementary order argument that was previously confined
to internal basis calculations: a positive operator dominated by a positive
trace-class operator is itself trace class.  It also gives the corresponding
positive/negative-part consequences for an already trace-class self-adjoint
operator.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma real_inner_nonneg_of_nonneg {T : B(H)} (hT : 0 ≤ T) (x : H) :
    0 ≤ (⟪x, T x⟫_ℂ).re := by
  exact (operator_nonneg_iff_isPositive T).mp hT |>.re_inner_nonneg_right x

private lemma real_inner_mono_of_le {P Q : B(H)} (hPQ : P ≤ Q) (x : H) :
    (⟪x, P x⟫_ℂ).re ≤ (⟪x, Q x⟫_ℂ).re := by
  have hdiff : 0 ≤ Q - P := sub_nonneg.mpr hPQ
  have hpos : (Q - P).IsPositive :=
    (operator_nonneg_iff_isPositive (Q - P)).mp hdiff
  have hx := hpos.re_inner_nonneg_right x
  simpa [ContinuousLinearMap.sub_apply, inner_sub_right] using hx

theorem isTraceClass_of_nonneg_of_le {P Q : B(H)} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hPQ : P ≤ Q) (hQclass : IsTraceClass Q) :
    IsTraceClass P := by
  apply isTraceClass_iff.mpr
  intro w b
  have hQsum : Summable (fun i : w => (⟪b i, Q (b i)⟫_ℂ).re) := by
    have h := isTraceClass_iff.mp hQclass w b
    rw [CFC.abs_of_nonneg Q hQ] at h
    exact h
  rw [CFC.abs_of_nonneg P hP]
  apply Summable.of_nonneg_of_le
  · intro i
    exact real_inner_nonneg_of_nonneg hP (b i)
  · intro i
    exact real_inner_mono_of_le hPQ (b i)
  · exact hQsum

private lemma isTraceClass_abs_of_isTraceClass {T : B(H)}
    (hT : IsTraceClass T) : IsTraceClass (CFC.abs T) := by
  rcases hT with ⟨w, b, hb⟩
  refine ⟨w, b, ?_⟩
  simpa only [CFC.cfcAbs_cfcAbs] using hb

theorem isTraceClass_posPart_of_isSelfAdjoint {T : B(H)}
    (hT : IsSelfAdjoint T) (h : IsTraceClass T) : IsTraceClass T⁺ := by
  have hAbs : IsTraceClass (CFC.abs T) := isTraceClass_abs_of_isTraceClass h
  have hle : T⁺ ≤ CFC.abs T := by
    rw [← CFC.posPart_add_negPart T hT]
    exact le_add_of_nonneg_right (CFC.negPart_nonneg T)
  exact isTraceClass_of_nonneg_of_le (CFC.posPart_nonneg T)
    (CFC.abs_nonneg T) hle hAbs

theorem isTraceClass_negPart_of_isSelfAdjoint {T : B(H)}
    (hT : IsSelfAdjoint T) (h : IsTraceClass T) : IsTraceClass T⁻ := by
  have hAbs : IsTraceClass (CFC.abs T) := isTraceClass_abs_of_isTraceClass h
  have hle : T⁻ ≤ CFC.abs T := by
    rw [← CFC.posPart_add_negPart T hT]
    exact le_add_of_nonneg_left (CFC.posPart_nonneg T)
  exact isTraceClass_of_nonneg_of_le (CFC.negPart_nonneg T)
    (CFC.abs_nonneg T) hle hAbs

end OperatorAlgebra
