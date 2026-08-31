/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.GeneralIdeal

/-!
# Positive trace values

The witness definition of `traceNorm` is real-valued, while `trace` is complex-valued.  For a
positive trace-class operator these two quantities are the same after embedding the real number
into `ℂ`.  This is the normalization fact needed by density-operator constructions and is
independent of the still unfinished arbitrary trace-ideal norm structure.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TraceClass

private lemma inner_eq_ofReal_of_nonneg {T : B(H)} (hT : 0 ≤ T) (x : H) :
    ⟪x, T x⟫_ℂ = ((⟪x, T x⟫_ℂ).re : ℂ) := by
  have hpos : T.IsPositive := (operator_nonneg_iff_isPositive T).mp hT
  have hx := (ContinuousLinearMap.isPositive_iff_complex T).mp hpos x
  have hself : ⟪T x, x⟫_ℂ = ((⟪T x, x⟫_ℂ).re : ℂ) := hx.1.symm
  have hre : (⟪T x, x⟫_ℂ).re = (⟪x, T x⟫_ℂ).re := by
    rw [← inner_conj_symm (T x) x]
    exact Complex.conj_re _
  calc
    ⟪x, T x⟫_ℂ = (starRingEnd ℂ) ⟪T x, x⟫_ℂ :=
      (inner_conj_symm x (T x)).symm
    _ = (starRingEnd ℂ) ((⟪T x, x⟫_ℂ).re : ℂ) := congrArg (starRingEnd ℂ) hself
    _ = ((⟪T x, x⟫_ℂ).re : ℂ) := by simp
    _ = ((⟪x, T x⟫_ℂ).re : ℂ) := congrArg (fun r : ℝ => (r : ℂ)) hre

/-- For a positive trace-class operator, the complex trace is the real trace norm. -/
theorem trace_eq_ofReal_traceNorm_of_nonneg {T : B(H)} (hT : 0 ≤ T)
    (h : IsTraceClass T) : trace T h = (traceNorm T h : ℂ) := by
  let w : Set H := h.choose
  let b : HilbertBasis w ℂ H := h.choose_spec.choose
  have hsum : Summable (fun i : w =>
      (⟪b i, CFC.abs T (b i)⟫_ℂ).re) := h.choose_spec.choose_spec
  have habs : CFC.abs T = T := CFC.abs_of_nonneg T hT
  have hpoint (i : w) :
      ⟪b i, T (b i)⟫_ℂ = (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
    rw [habs]
    exact inner_eq_ofReal_of_nonneg hT (b i)
  unfold trace traceNorm
  change (∑' i : w, ⟪b i, T (b i)⟫_ℂ) =
    ((∑' i : w, (⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℝ) : ℂ)
  calc
    (∑' i : w, ⟪b i, T (b i)⟫_ℂ) =
        ∑' i : w, ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ) :=
      tsum_congr (fun i => by rw [hpoint])
    _ = ((∑' i : w, (⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℝ) : ℂ) :=
      (Complex.ofReal_tsum _).symm

/-- The trace of a positive trace-class operator is nonnegative in the complex order. -/
theorem trace_nonneg_of_nonneg {T : B(H)} (hT : 0 ≤ T) (h : IsTraceClass T) :
    0 ≤ trace T h := by
  rw [trace_eq_ofReal_traceNorm_of_nonneg hT h]
  exact RCLike.ofReal_nonneg.mpr (traceNorm_nonneg T h)

end TraceClass

end OperatorAlgebra
