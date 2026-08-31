/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.GeneralIdeal
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.PositiveIdeal
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.RankOne
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.PosIdealEstimate
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.PositiveDomination
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.GeneralProduct
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.IdealNorm

/-!
# Elementary algebra of the unconditional trace

The witness proof in `IsTraceClass` is proof-irrelevant, while the diagonal
trace itself is now known to be basis independent.  This file records the
linear scalar law in a form that downstream pairing constructions can use
without reopening the witness basis.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TraceClass

open HilbertSchmidt

/-- Scalar homogeneity of the trace, with the canonical trace-class proof for
the scaled operator. -/
theorem trace_smul {T : B(H)} (c : ℂ) (hT : IsTraceClass T) :
    trace (c • T) (isTraceClass_smul c hT) = c * trace T hT := by
  let hT' : IsTraceClass (c • T) := isTraceClass_smul c hT
  let w : Set H := hT.choose
  let b : HilbertBasis w ℂ H := hT.choose_spec.choose
  have hleft := trace_eq_of_hilbertBasis hT' b
  have hright := trace_eq_of_hilbertBasis hT b
  rw [hleft, hright]
  calc
    (∑' i : w, ⟪b i, (c • T) (b i)⟫_ℂ) =
        ∑' i : w, c * ⟪b i, T (b i)⟫_ℂ := by
      apply tsum_congr
      intro i
      simp
    _ = c * ∑' i : w, ⟪b i, T (b i)⟫_ℂ := tsum_mul_left

/-! ### Additivity and cyclicity -/

/-- Additivity of the unconditional trace. -/
theorem trace_add {T T' : B(H)} (hT : IsTraceClass T) (hT' : IsTraceClass T') :
    trace (T + T') (isTraceClass_add hT hT') = trace T hT + trace T' hT' := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hsum : IsTraceClass (T + T') := isTraceClass_add hT hT'
  rw [trace_eq_of_hilbertBasis hsum b, trace_eq_of_hilbertBasis hT b,
    trace_eq_of_hilbertBasis hT' b]
  calc
    (∑' i : w, ⟪b i, (T + T') (b i)⟫_ℂ) =
        ∑' i : w, (⟪b i, T (b i)⟫_ℂ + ⟪b i, T' (b i)⟫_ℂ) := by
      apply tsum_congr
      intro i
      simp [add_apply, inner_add_right]
    _ = (∑' i : w, ⟪b i, T (b i)⟫_ℂ) +
        ∑' i : w, ⟪b i, T' (b i)⟫_ℂ :=
      (summable_trace_diagonal_of_isTraceClass hT b).tsum_add
        (summable_trace_diagonal_of_isTraceClass hT' b)

/-- Cyclicity of the trace across a bounded factor and a trace-class factor. -/
theorem trace_mul_cycle {A T : B(H)} (hT : IsTraceClass T) :
    trace (A * T) (isTraceClass_mul_mul (A := A) (B := 1) hT) =
      trace (T * A) (isTraceClass_mul_mul (A := 1) (B := A) hT) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  obtain ⟨hR, hS, hfactor⟩ :=
    isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs hT
  let R : B(H) := Polar.polarFactor T * CFC.sqrt (CFC.abs T)
  let S : B(H) := CFC.sqrt (CFC.abs T)
  have hfactor' : R * S = T := by simpa [R, S] using hfactor
  have hAR : IsHilbertSchmidt (A * R) :=
    HilbertSchmidt.isHilbertSchmidt_mul_left hR
  have hSA : IsHilbertSchmidt (S * A) :=
    HilbertSchmidt.isHilbertSchmidt_mul_right hS
  have h₁ := HilbertSchmidt.tsum_diagonal_mul_eq_tsum_diagonal_swap
    (R := A * R) (S := S) b b hAR hS
  have h₂ := HilbertSchmidt.tsum_diagonal_mul_eq_tsum_diagonal_swap
    (R := S * A) (S := R) b b hSA hR
  have h₃ : A * T = (A * R) * S := by
    rw [show T = R * S from hfactor'.symm]
    simp only [mul_assoc]
  have h₄ : T * A = R * (S * A) := by
    rw [show T = R * S from hfactor'.symm]
    simp only [mul_assoc]
  let hAT : IsTraceClass (A * T) := by
    simpa using (isTraceClass_mul_mul (A := A) (B := 1) hT)
  let hTA : IsTraceClass (T * A) := by
    simpa using (isTraceClass_mul_mul (A := 1) (B := A) hT)
  rw [trace_eq_of_hilbertBasis hAT b, trace_eq_of_hilbertBasis hTA b]
  calc
    (∑' i : w, ⟪b i, (A * T) (b i)⟫_ℂ) =
        ∑' i : w, ⟪b i, ((A * R) * S) (b i)⟫_ℂ := by
          rw [h₃]
    _ =
        ∑' i : w, ⟪b i, (S * (A * R)) (b i)⟫_ℂ := h₁
    _ = ∑' i : w, ⟪b i, ((S * A) * R) (b i)⟫_ℂ := by
          apply tsum_congr
          intro i
          simp only [mul_assoc]
    _ = ∑' i : w, ⟪b i, (R * (S * A)) (b i)⟫_ℂ := h₂
    _ = ∑' i : w, ⟪b i, (T * A) (b i)⟫_ℂ := by
          rw [h₄]

/-! ### The Hilbert--Schmidt trace cycle

The bounded-factor cycle above is not enough for square-root arguments: the positive square root
of a trace-class operator is generally Hilbert--Schmidt rather than trace class.  The product
theorem and its basis-independent diagonal sum therefore give the following complementary cycle.
-/

/-- Cyclicity for a product of two Hilbert--Schmidt operators. -/
theorem trace_mul_hilbertSchmidt_cycle {R S : B(H)}
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    trace (R * S) (isTraceClass_mul_of_isHilbertSchmidt hR hS) =
      trace (S * R) (isTraceClass_mul_of_isHilbertSchmidt hS hR) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [trace_eq_of_hilbertBasis (isTraceClass_mul_of_isHilbertSchmidt hR hS) b,
    trace_eq_of_hilbertBasis (isTraceClass_mul_of_isHilbertSchmidt hS hR) b]
  exact HilbertSchmidt.tsum_diagonal_mul_eq_tsum_diagonal_swap b b hR hS

/-- The trace of an adjoint is the complex conjugate of the trace. -/
theorem trace_star {T : B(H)} (hT : IsTraceClass T) :
    trace (star T) (isTraceClass_star hT) = starRingEnd ℂ (trace T hT) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let hTstar : IsTraceClass (star T) := isTraceClass_star hT
  rw [trace_eq_of_hilbertBasis hTstar b, trace_eq_of_hilbertBasis hT b]
  have hdiag : Summable (fun i : w => ⟪b i, T (b i)⟫_ℂ) :=
    summable_trace_diagonal_of_isTraceClass hT b
  have hconj : Summable (fun i : w => starRingEnd ℂ (⟪b i, T (b i)⟫_ℂ)) := by
    apply Summable.of_norm
    convert hdiag.norm using 1
    funext i
    rw [RCLike.norm_conj]
  calc
    (∑' i : w, ⟪b i, (star T) (b i)⟫_ℂ) =
        ∑' i : w, starRingEnd ℂ (⟪b i, T (b i)⟫_ℂ) := by
      apply tsum_congr
      intro i
      rw [ContinuousLinearMap.star_eq_adjoint]
      rw [← inner_conj_symm (b i) (ContinuousLinearMap.adjoint T (b i))]
      rw [ContinuousLinearMap.adjoint_inner_left]
    _ = starRingEnd ℂ (∑' i : w, ⟪b i, T (b i)⟫_ℂ) :=
      (Complex.conj_tsum _).symm

/-- Triangle inequality for the trace norm. -/
theorem traceNorm_add_le_via_diagonal {T T' : B(H)} (hT : IsTraceClass T) (hT' : IsTraceClass T') :
    traceNorm (T + T') (isTraceClass_add hT hT') ≤ traceNorm T hT + traceNorm T' hT' := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  let W : B(H) := Polar.polarFactor (T + T')
  have hW : ‖W‖ ≤ 1 := Polar.polarFactor_opNorm_le (T + T')
  let hsum : IsTraceClass (T + T') := isTraceClass_add hT hT'
  have hdualT := tsum_norm_diagonal_star_mul_le_traceNorm hW hT b
  have hdualT' := tsum_norm_diagonal_star_mul_le_traceNorm hW hT' b
  have hrealT : Summable (fun i : w =>
      (⟪b i, (star W * T) (b i)⟫_ℂ).re) := by
    apply Summable.of_norm_bounded hdualT.1
    intro i
    simpa [Real.norm_eq_abs] using
      (Complex.abs_re_le_norm (⟪b i, (star W * T) (b i)⟫_ℂ))
  have hrealT' : Summable (fun i : w =>
      (⟪b i, (star W * T') (b i)⟫_ℂ).re) := by
    apply Summable.of_norm_bounded hdualT'.1
    intro i
    simpa [Real.norm_eq_abs] using
      (Complex.abs_re_le_norm (⟪b i, (star W * T') (b i)⟫_ℂ))
  have hrealSum : Summable (fun i : w =>
      (⟪b i, (star W * T) (b i)⟫_ℂ).re +
        (⟪b i, (star W * T') (b i)⟫_ℂ).re) := hrealT.add hrealT'
  have habs : CFC.abs (T + T') = star W * (T + T') := by
    dsimp [W]
    exact (Polar.star_polarFactor_mul_self (T + T')).symm
  have htraceSum : traceNorm (T + T') hsum =
      (∑' i : w, ((⟪b i, (star W * T) (b i)⟫_ℂ).re +
        (⟪b i, (star W * T') (b i)⟫_ℂ).re)) := by
    rw [traceNorm_eq_of_hilbertBasis hsum b]
    apply tsum_congr
    intro i
    rw [habs]
    simp [add_apply, inner_add_right]
  have hpoint : ∀ i : w,
      (⟪b i, (star W * T) (b i)⟫_ℂ).re +
        (⟪b i, (star W * T') (b i)⟫_ℂ).re ≤
      ‖⟪b i, (star W * T) (b i)⟫_ℂ‖ +
        ‖⟪b i, (star W * T') (b i)⟫_ℂ‖ := by
    intro i
    have heq : (⟪b i, (star W * (T + T')) (b i)⟫_ℂ) =
        ⟪b i, (star W * T) (b i)⟫_ℂ +
          ⟪b i, (star W * T') (b i)⟫_ℂ := by
      simp [add_apply, inner_add_right]
    have hre : (⟪b i, (star W * (T + T')) (b i)⟫_ℂ).re =
        (⟪b i, (star W * T) (b i)⟫_ℂ).re +
          (⟪b i, (star W * T') (b i)⟫_ℂ).re := by
      rw [heq]
      simp
    rw [← hre]
    calc
      (⟪b i, (star W * (T + T')) (b i)⟫_ℂ).re ≤
          ‖⟪b i, (star W * (T + T')) (b i)⟫_ℂ‖ :=
        Complex.re_le_norm _
      _ ≤ ‖⟪b i, (star W * T) (b i)⟫_ℂ‖ +
          ‖⟪b i, (star W * T') (b i)⟫_ℂ‖ := by
        rw [heq]
        exact norm_add_le _ _
  calc
    traceNorm (T + T') hsum =
        (∑' i : w, ((⟪b i, (star W * T) (b i)⟫_ℂ).re +
          (⟪b i, (star W * T') (b i)⟫_ℂ).re)) := htraceSum
    _ ≤ (∑' i : w, (‖⟪b i, (star W * T) (b i)⟫_ℂ‖ +
          ‖⟪b i, (star W * T') (b i)⟫_ℂ‖)) :=
      hrealSum.tsum_le_tsum hpoint (hdualT.1.add hdualT'.1)
    _ = (∑' i : w, ‖⟪b i, (star W * T) (b i)⟫_ℂ‖) +
          ∑' i : w, ‖⟪b i, (star W * T') (b i)⟫_ℂ‖ :=
      (hdualT.1.tsum_add hdualT'.1)
    _ ≤ traceNorm T hT + traceNorm T' hT' :=
      add_le_add hdualT.2 hdualT'.2

end TraceClass

end OperatorAlgebra
