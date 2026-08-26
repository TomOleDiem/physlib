/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.TraceClass

/-!
# Positive trace-class ideal estimates

This file isolates an analytic part of the trace-ideal construction which does not require a
polar decomposition: conjugating a positive trace-class operator by a bounded operator remains
trace class.  It is the estimate needed for quadratic-form states and is also a building block for
the eventual general `B(H)` predual.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! These elementary closure lemmas let the positive conjugation estimate be combined by
polarization.  They are stated before the double-sum proof so the latter remains independent of
any general trace-class ideal theorem. -/

theorem isTraceClass_smul {T : B(H)} (c : ℂ) (hT : IsTraceClass T) :
    IsTraceClass (c • T) := by
  apply isTraceClass_iff.mpr
  intro w b
  have h := isTraceClass_iff.mp hT w b
  rw [CFC.abs_smul]
  have hs := h.const_smul ‖c‖
  simpa [smul_eq_mul] using hs

/-- The trace norm is homogeneous.  The proof uses the basis-independent
diagonal formula, so it is independent of the witness proof carried by
`IsTraceClass`. -/
theorem traceNorm_smul {T : B(H)} (c : ℂ) (hT : IsTraceClass T) :
    traceNorm (c • T) (isTraceClass_smul c hT) =
      ‖c‖ * traceNorm T hT := by
  let w : Set H := hT.choose
  let b : HilbertBasis w ℂ H := hT.choose_spec.choose
  have hleft := traceNorm_eq_of_hilbertBasis
    (isTraceClass_smul c hT) b
  have hright := traceNorm_eq_of_hilbertBasis hT b
  rw [hleft, hright]
  rw [CFC.abs_smul]
  have hpoint : (fun i : w =>
      (⟪b i, (‖c‖ : ℝ) • CFC.abs T (b i)⟫_ℂ).re) =
      (fun i : w => ‖c‖ *
        (⟪b i, CFC.abs T (b i)⟫_ℂ).re) := by
    funext i
    simp [smul_eq_mul]
  calc
    (∑' i : w, (⟪b i, (‖c‖ : ℝ) • CFC.abs T (b i)⟫_ℂ).re) =
        ∑' i : w, ‖c‖ * (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
      apply tsum_congr
      exact fun i => congrFun hpoint i
    _ = ‖c‖ * ∑' i : w, (⟪b i, CFC.abs T (b i)⟫_ℂ).re := tsum_mul_left

private lemma summable_inner_of_nonneg' {T : B(H)} (hT : 0 ≤ T) (h : IsTraceClass T)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    Summable (fun i => ⟪b i, T (b i)⟫_ℂ) := by
  have hr : Summable (fun i : w => (⟪b i, CFC.abs T (b i)⟫_ℂ).re) :=
    summable_inner_abs_of_hilbertBasis h b
  have habs : CFC.abs T = T := CFC.abs_of_nonneg T hT
  have heq (i : w) : ⟪b i, T (b i)⟫_ℂ =
      ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ) := by
    rw [habs]
    have hpos : T.IsPositive := (operator_nonneg_iff_isPositive T).mp hT
    have hx := (ContinuousLinearMap.isPositive_iff_complex T).mp hpos (b i)
    have hA : ⟪T (b i), b i⟫_ℂ = ((⟪T (b i), b i⟫_ℂ).re : ℂ) := hx.1.symm
    have hre : (⟪T (b i), b i⟫_ℂ).re = (⟪b i, T (b i)⟫_ℂ).re := by
      rw [← inner_conj_symm (T (b i)) (b i)]
      exact Complex.conj_re _
    have hinner : ⟪b i, T (b i)⟫_ℂ = ((⟪T (b i), b i⟫_ℂ).re : ℂ) := by
      calc
        ⟪b i, T (b i)⟫_ℂ = (starRingEnd ℂ) ⟪T (b i), b i⟫_ℂ :=
          (inner_conj_symm (b i) (T (b i))).symm
        _ = (starRingEnd ℂ) ((⟪T (b i), b i⟫_ℂ).re : ℂ) :=
          congrArg (starRingEnd ℂ) hA
        _ = ((⟪T (b i), b i⟫_ℂ).re : ℂ) := by simp
    exact hinner.trans (congrArg (fun r : ℝ => (r : ℂ)) hre)
  have hs : Summable (fun i : w => ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ)) :=
    Complex.summable_ofReal.mpr hr
  exact hs.congr (fun i => (heq i).symm)

theorem isTraceClass_add_of_nonneg {P Q : B(H)} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hPclass : IsTraceClass P) (hQclass : IsTraceClass Q) :
    IsTraceClass (P + Q) := by
  apply isTraceClass_iff.mpr
  intro w b
  rw [CFC.abs_of_nonneg (P + Q) (add_nonneg hP hQ)]
  have hPsum := summable_inner_of_nonneg' hP hPclass b
  have hQsum := summable_inner_of_nonneg' hQ hQclass b
  have hsum : Summable (fun i : w =>
      ⟪b i, P (b i)⟫_ℂ + ⟪b i, Q (b i)⟫_ℂ) := hPsum.add hQsum
  have heq : (fun i : w => (⟪b i, (P + Q) (b i)⟫_ℂ).re) =
      (fun i : w => (⟪b i, P (b i)⟫_ℂ + ⟪b i, Q (b i)⟫_ℂ).re) := by
    funext i
    simp [map_add, inner_add_right]
  rw [heq]
  exact hsum.map Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous

private lemma hasSum_norm_sq_inner_basis {w : Set H} (b : HilbertBasis w ℂ H) (y : H) :
    HasSum (fun i : w => ‖⟪b i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner y y
  have hpt : ∀ i : w, ⟪y, b i⟫_ℂ * ⟪b i, y⟫_ℂ =
      ((‖⟪b i, y⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← inner_conj_symm y (b i), RCLike.conj_mul]
    norm_cast
  have hval : ⟪y, y⟫_ℂ = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [hpt] at h
  rw [hval] at h
  exact Complex.hasSum_ofReal.mp h

private lemma summable_norm_sq_comp_right_of_selfAdjoint
    {S A : B(H)} (hS : IsSelfAdjoint S) {w w' : Set H}
    (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hb : Summable (fun j : w => ‖S (b j)‖ ^ 2)) :
    Summable (fun i : w' => ‖(S * A) (c i)‖ ^ 2) := by
  classical
  let R : B(H) := S * A
  let F : w → w' → ℝ := fun j i => ‖⟪b j, R (c i)⟫_ℂ‖ ^ 2
  have hRstar : ContinuousLinearMap.adjoint R = ContinuousLinearMap.adjoint A * S := by
    rw [show R = S ∘SL A by rfl, ContinuousLinearMap.adjoint_comp]
    rw [← ContinuousLinearMap.mul_def]
    rw [(ContinuousLinearMap.star_eq_adjoint S).symm.trans hS]
  have hrow : ∀ j : w, HasSum (F j)
      (‖ContinuousLinearMap.adjoint R (b j)‖ ^ 2) := by
    intro j
    have hpoint : (fun i : w' => F j i) = fun i : w' =>
        ‖⟪c i, ContinuousLinearMap.adjoint R (b j)⟫_ℂ‖ ^ 2 := by
      funext i
      have hi := ContinuousLinearMap.adjoint_inner_left R (c i) (b j)
      have hi' : ⟪b j, R (c i)⟫_ℂ =
          ⟪ContinuousLinearMap.adjoint R (b j), c i⟫_ℂ := hi.symm
      change ‖⟪b j, R (c i)⟫_ℂ‖ ^ 2 = _
      rw [hi', ← inner_conj_symm (c i) (ContinuousLinearMap.adjoint R (b j))]
      simp only [RCLike.norm_conj]
    change HasSum (fun i : w' => F j i)
      (‖ContinuousLinearMap.adjoint R (b j)‖ ^ 2)
    rw [hpoint]
    exact hasSum_norm_sq_inner_basis c (ContinuousLinearMap.adjoint R (b j))
  have hstar_bound : ∀ j : w,
      ‖ContinuousLinearMap.adjoint R (b j)‖ ^ 2 ≤
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
  have hstar : Summable (fun j : w =>
      ‖ContinuousLinearMap.adjoint R (b j)‖ ^ 2) := by
    have hmul := hb.mul_left (‖A‖ ^ 2)
    exact Summable.of_nonneg_of_le (fun j => sq_nonneg _) hstar_bound
      (by simpa [mul_comm] using hmul)
  have hFnonneg : 0 ≤ Function.uncurry F := fun _ => sq_nonneg _
  have hjoint : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg hFnonneg]
    refine ⟨fun j => (hrow j).summable, ?_⟩
    have heq : (fun j : w => ∑' i : w', F j i) = fun j : w =>
        ‖ContinuousLinearMap.adjoint R (b j)‖ ^ 2 :=
      funext fun j => (hrow j).tsum_eq
    change Summable (fun j : w => ∑' i : w', F j i)
    rw [heq]
    exact hstar
  have hcol : ∀ i : w', HasSum (fun j : w => F j i) (‖R (c i)‖ ^ 2) := by
    intro i
    have hpoint : (fun j : w => F j i) = fun j : w =>
        ‖⟪b j, R (c i)⟫_ℂ‖ ^ 2 := rfl
    rw [hpoint]
    exact hasSum_norm_sq_inner_basis b (R (c i))
  have hcol_summable : Summable (fun i : w' => ‖R (c i)‖ ^ 2) := by
    let G : w' → w → ℝ := fun i j => F j i
    have hGnonneg : 0 ≤ Function.uncurry G := fun _ => sq_nonneg _
    have hGjoint : Summable (Function.uncurry G) := by
      have hcomp : Function.uncurry G =
          Function.uncurry F ∘ (Equiv.prodComm w' w) := by
        funext p
        simp [Function.uncurry, G, Equiv.prodComm]
      rw [hcomp]
      exact (Equiv.prodComm w' w).summable_iff.mpr hjoint
    have hpair := (summable_prod_of_nonneg hGnonneg).mp hGjoint
    have hcol_sum : Summable (fun i : w' => ∑' j : w, G i j) := hpair.2
    have heq : (fun i : w' => ∑' j : w, G i j) =
        (fun i : w' => ‖R (c i)‖ ^ 2) := by
      funext i
      exact (hcol i).tsum_eq
    rw [heq] at hcol_sum
    exact hcol_sum
  exact hcol_summable

/-- A positive trace-class operator remains trace class after bounded conjugation.  This is the
positive part of the two-sided trace ideal theorem and is sufficient for the standard quadratic
form construction of normal states. -/
theorem isTraceClass_star_mul_mul_of_nonneg {P A : B(H)} (hP : 0 ≤ P)
    (hPclass : IsTraceClass P) : IsTraceClass (star A * P * A) := by
  apply isTraceClass_iff.mpr
  intro w c
  let S : B(H) := CFC.sqrt P
  have hS : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg P)
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP
  obtain ⟨w₀, b, hb⟩ := hPclass
  have hb' : Summable (fun j : w₀ => ‖S (b j)‖ ^ 2) := by
    have habs : CFC.abs P = P := CFC.abs_of_nonneg P hP
    refine hb.congr ?_
    intro j
    have hinner : ⟪b j, P (b j)⟫_ℂ =
        ⟪S (b j), S (b j)⟫_ℂ := by
      calc
        _ = ⟪b j, (S * S) (b j)⟫_ℂ := by rw [hSS]
        _ = _ := by
          rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
          rw [← ContinuousLinearMap.adjoint_inner_left S (S (b j)) (b j),
            (ContinuousLinearMap.star_eq_adjoint S).symm.trans hS]
    rw [habs, hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hcomp := summable_norm_sq_comp_right_of_selfAdjoint
    (S := S) (A := A) hS b c hb'
  have hdiag : ∀ i : w,
      (⟪c i, (star A * P * A) (c i)⟫_ℂ).re =
        ‖(S * A) (c i)‖ ^ 2 := by
    intro i
    have hSstar : ContinuousLinearMap.adjoint S = S :=
      (ContinuousLinearMap.star_eq_adjoint S).symm.trans hS
    have hinner : ⟪c i, (star A * P * A) (c i)⟫_ℂ =
        ⟪(S * A) (c i), (S * A) (c i)⟫_ℂ := by
      rw [← hSS]
      rw [ContinuousLinearMap.star_eq_adjoint A]
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [ContinuousLinearMap.adjoint_inner_right A]
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← hSstar, ContinuousLinearMap.adjoint_inner_right S, hSstar,
        ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hnonneg : 0 ≤ star A * P * A := star_left_conjugate_nonneg hP A
  rw [show (fun i : w => (⟪c i, CFC.abs (star A * P * A) (c i)⟫_ℂ).re) =
      (fun i : w => (⟪c i, (star A * P * A) (c i)⟫_ℂ).re) by
        funext i
        rw [CFC.abs_of_nonneg _ hnonneg]]
  exact hcomp.congr (fun i => (hdiag i).symm)

/-- The opposite conjugation orientation is the same positive ideal estimate, applied to `A⋆`.
This is the form used when a bounded operator is written on the left of a positive trace-class
operator. -/
theorem isTraceClass_mul_mul_star_of_nonneg {P A : B(H)} (hP : 0 ≤ P)
    (hPclass : IsTraceClass P) : IsTraceClass (A * P * star A) := by
  simpa only [star_star] using
    (isTraceClass_star_mul_mul_of_nonneg hP hPclass (A := star A))

end OperatorAlgebra
