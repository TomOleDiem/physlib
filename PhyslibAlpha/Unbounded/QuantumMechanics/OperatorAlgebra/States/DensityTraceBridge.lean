/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.DensityQuadraticForm
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.PositiveIdeal

/-!
# Trace realization of the positive density-operator quadratic form

The quadratic-form state is already available without the general trace-ideal theorem.  This
file proves the useful positive part of the usual trace formula: if `A ≥ 0`, then

```text
  ωρ(A) = Tr (√ρ A √ρ).
```

The sandwiched operator is positive and trace class.  Consequently the equality is proved using
only the positive trace-class API; no polar decomposition or arbitrary non-self-adjoint ideal
theorem is smuggled in.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DensityOperator

variable (ρ : DensityOperator H)

/-- The bounded positive operator which realizes the density quadratic form by a trace. -/
noncomputable def sandwichedOperator (A : B(H)) : B(H) :=
  ρ.sqrtOperator * A * ρ.sqrtOperator

private lemma sandwiched_nonneg {A : B(H)} (hA : 0 ≤ A) :
    0 ≤ ρ.sandwichedOperator A := by
  unfold sandwichedOperator
  have hS : IsSelfAdjoint ρ.sqrtOperator :=
    .of_nonneg (CFC.sqrt_nonneg ρ.ρ)
  have h := star_left_conjugate_nonneg hA ρ.sqrtOperator
  rw [hS] at h
  exact h

@[nolint unusedArguments]
private lemma sandwiched_diagonal {w : Set H} (b : HilbertBasis w ℂ H)
    {A : B(H)} (i : w) (hA : 0 ≤ A) :
    ⟪b i, ρ.sandwichedOperator A (b i)⟫_ℂ =
      ⟪ρ.sqrtOperator (b i), A (ρ.sqrtOperator (b i))⟫_ℂ := by
  let S : B(H) := ρ.sqrtOperator
  have hSself : IsSelfAdjoint S := by
    dsimp [S]
    exact .of_nonneg (CFC.sqrt_nonneg ρ.ρ)
  have hSstar : ContinuousLinearMap.adjoint S = S :=
    (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
  have hinner :
      ⟪b i, ρ.sandwichedOperator A (b i)⟫_ℂ =
        ⟪S (b i), A (S (b i))⟫_ℂ := by
    unfold sandwichedOperator
    change ⟪b i, ((S * A) * S) (b i)⟫_ℂ = _
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
    calc
      _ = ⟪ContinuousLinearMap.adjoint S (b i), A (S (b i))⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_left S (A (S (b i))) (b i)).symm
      _ = _ := by rw [hSstar]
  exact hinner

private lemma sqrt_root_summable {w : Set H} (b : HilbertBasis w ℂ H) :
    Summable (fun i : w => ‖ρ.sqrtOperator (b i)‖ ^ 2) := by
  have hb := summable_inner_abs_of_hilbertBasis ρ.traceClass b
  have habs : CFC.abs ρ.ρ = ρ.ρ := CFC.abs_of_nonneg ρ.ρ ρ.nonneg
  refine hb.congr ?_
  intro i
  have hS : IsSelfAdjoint ρ.sqrtOperator :=
    .of_nonneg (CFC.sqrt_nonneg ρ.ρ)
  have hSS : ρ.sqrtOperator * ρ.sqrtOperator = ρ.ρ :=
    CFC.sqrt_mul_sqrt_self ρ.ρ ρ.nonneg
  have hinner :
      ⟪b i, ρ.ρ (b i)⟫_ℂ =
        ⟪ρ.sqrtOperator (b i), ρ.sqrtOperator (b i)⟫_ℂ := by
    calc
      _ = ⟪b i,
          (ρ.sqrtOperator * ρ.sqrtOperator)
            (b i)⟫_ℂ := by rw [hSS]
      _ = _ := by
        rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
        rw [← ContinuousLinearMap.adjoint_inner_left ρ.sqrtOperator
          (ρ.sqrtOperator (b i)) (b i),
          (ContinuousLinearMap.star_eq_adjoint ρ.sqrtOperator).symm.trans hS]
  rw [habs, hinner, inner_self_eq_norm_sq_to_K]
  norm_cast

private lemma sandwiched_diagonal_bound {w : Set H} (b : HilbertBasis w ℂ H)
    {A : B(H)} (hA : 0 ≤ A) (i : w) :
    (⟪b i, ρ.sandwichedOperator A (b i)⟫_ℂ).re ≤
      ‖A‖ * ‖ρ.sqrtOperator (b i)‖ ^ 2 := by
  rw [ρ.sandwiched_diagonal b i hA]
  calc
    (⟪ρ.sqrtOperator (b i), A (ρ.sqrtOperator (b i))⟫_ℂ).re ≤
        ‖⟪ρ.sqrtOperator (b i), A (ρ.sqrtOperator (b i))⟫_ℂ‖ :=
      Complex.re_le_norm _
    _ ≤ ‖ρ.sqrtOperator (b i)‖ * ‖A (ρ.sqrtOperator (b i))‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖ρ.sqrtOperator (b i)‖ * (‖A‖ * ‖ρ.sqrtOperator (b i)‖) := by
      gcongr
      exact A.le_opNorm _
    _ = ‖A‖ * ‖ρ.sqrtOperator (b i)‖ ^ 2 := by ring

/-- A positive bounded observable gives a trace-class sandwiched operator. -/
theorem isTraceClass_sandwichedOperator {A : B(H)} (hA : 0 ≤ A) :
    IsTraceClass (ρ.sandwichedOperator A) := by
  apply isTraceClass_iff.mpr
  intro w b
  have hupper : Summable (fun i : w => ‖A‖ *
      ‖ρ.sqrtOperator (b i)‖ ^ 2) := by
    exact (ρ.sqrt_root_summable b).mul_left ‖A‖
  have hpositive := ρ.sandwiched_nonneg hA
  rw [CFC.abs_of_nonneg _ hpositive]
  have hnonneg : ∀ i : w, 0 ≤
      (⟪b i, ρ.sandwichedOperator A (b i)⟫_ℂ).re := by
    intro i
    exact ((Complex.nonneg_iff.mp
      ((operator_nonneg_iff_isPositive _).mp hpositive |>.inner_nonneg_right (b i))).1)
  have hle : ∀ i : w, (⟪b i, ρ.sandwichedOperator A (b i)⟫_ℂ).re ≤
      ‖A‖ * ‖ρ.sqrtOperator (b i)‖ ^ 2 := by
    intro i
    exact ρ.sandwiched_diagonal_bound b hA i
  exact Summable.of_nonneg_of_le hnonneg hle hupper

/-- For positive observables, the quadratic-form state is exactly the trace of the positive
sandwich `√ρ A √ρ`. -/
theorem quadraticForm_eq_trace_sandwichedOperator {A : B(H)} (hA : 0 ≤ A) :
    ρ.quadraticForm A =
      trace (ρ.sandwichedOperator A) (ρ.isTraceClass_sandwichedOperator hA) := by
  let hT := ρ.isTraceClass_sandwichedOperator hA
  have hpositive := ρ.sandwiched_nonneg hA
  have htrace := trace_eq_of_hilbertBasis_of_nonneg
    (T := ρ.sandwichedOperator A) hpositive hT
      ρ.traceClass.choose_spec.choose
  rw [DensityOperator.quadraticForm]
  calc
    (∑' i : ρ.traceClass.choose,
        ⟪ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i),
          A (ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i))⟫_ℂ) =
        ∑' i : ρ.traceClass.choose,
          ⟪ρ.traceClass.choose_spec.choose i,
            ρ.sandwichedOperator A
              (ρ.traceClass.choose_spec.choose i)⟫_ℂ := by
      apply tsum_congr
      intro i
      exact (ρ.sandwiched_diagonal ρ.traceClass.choose_spec.choose i hA).symm
    _ = trace (ρ.sandwichedOperator A) hT := htrace.symm

end DensityOperator

end OperatorAlgebra
