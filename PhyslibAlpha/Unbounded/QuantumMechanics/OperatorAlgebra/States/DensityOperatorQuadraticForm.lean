/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.DensityOperator

/-!
# Density-operator states by quadratic form

The usual formula `A ↦ Tr (ρ A)` requires the trace ideal theorem for the product `ρ A`.
There is a completely rigorous construction that does not form that product: write
`S = √ρ` and define

```text
          ωρ(A) = ∑ᵢ ⟪S eᵢ, A (S eᵢ)⟫.
```

The trace-class witness for `ρ` makes this series absolutely summable.  Positivity and
normalization then follow directly from positivity of `A` and the identity `S² = ρ`.
This is the concrete state API needed by applications even before the full trace-class
predual of `B(H)` is constructed.  It is deliberately separate from `DensityOperator.toState`,
whose product-trace formulation still requires the general trace-ideal boundary.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DensityOperator

variable (ρ : DensityOperator H)

/-- The bounded positive square root of a density operator. -/
noncomputable def sqrtOperator : B(H) := CFC.sqrt ρ.ρ

private lemma root_nonneg : 0 ≤ sqrtOperator ρ := CFC.sqrt_nonneg ρ.ρ

private lemma root_selfAdjoint : IsSelfAdjoint (sqrtOperator ρ) :=
  .of_nonneg (root_nonneg ρ)

private lemma root_sq : sqrtOperator ρ * sqrtOperator ρ = ρ.ρ :=
  CFC.sqrt_mul_sqrt_self ρ.ρ ρ.nonneg

private lemma witness_root_sq_summable :
    Summable (fun i : ρ.traceClass.choose =>
      ‖sqrtOperator ρ (ρ.traceClass.choose_spec.choose i)‖ ^ 2) := by
  have hb := ρ.traceClass.choose_spec.choose_spec
  have habs : CFC.abs ρ.ρ = ρ.ρ := CFC.abs_of_nonneg ρ.ρ ρ.nonneg
  have habs_apply (x : H) : CFC.abs ρ.ρ x = ρ.ρ x :=
    congrArg (fun L : B(H) => L x) habs
  refine hb.congr ?_
  intro i
  have hinner :
      ⟪ρ.traceClass.choose_spec.choose i, ρ.ρ (ρ.traceClass.choose_spec.choose i)⟫_ℂ =
        ⟪sqrtOperator ρ (ρ.traceClass.choose_spec.choose i),
          sqrtOperator ρ (ρ.traceClass.choose_spec.choose i)⟫_ℂ := by
    calc
      _ = ⟪ρ.traceClass.choose_spec.choose i,
          (sqrtOperator ρ * sqrtOperator ρ)
            (ρ.traceClass.choose_spec.choose i)⟫_ℂ := by rw [root_sq ρ]
      _ = _ := by
        rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
        rw [← ContinuousLinearMap.adjoint_inner_left (sqrtOperator ρ)
          (sqrtOperator ρ (ρ.traceClass.choose_spec.choose i))
          (ρ.traceClass.choose_spec.choose i),
          (ContinuousLinearMap.star_eq_adjoint (sqrtOperator ρ)).symm.trans
            (root_selfAdjoint ρ)]
  calc
    (⟪ρ.traceClass.choose_spec.choose i, CFC.abs ρ.ρ
        (ρ.traceClass.choose_spec.choose i)⟫_ℂ).re =
        (⟪ρ.traceClass.choose_spec.choose i,
          ρ.ρ (ρ.traceClass.choose_spec.choose i)⟫_ℂ).re := by
            rw [habs_apply]
    _ = (⟪sqrtOperator ρ (ρ.traceClass.choose_spec.choose i),
          sqrtOperator ρ (ρ.traceClass.choose_spec.choose i)⟫_ℂ).re :=
      congrArg Complex.re hinner
    _ = ‖sqrtOperator ρ (ρ.traceClass.choose_spec.choose i)‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast

private lemma summable_term (A : B(H)) :
    Summable (fun i : ρ.traceClass.choose =>
      ⟪sqrtOperator ρ (ρ.traceClass.choose_spec.choose i),
        A (sqrtOperator ρ (ρ.traceClass.choose_spec.choose i))⟫_ℂ) := by
  apply Summable.of_norm_bounded (witness_root_sq_summable ρ |>.mul_left ‖A‖)
  intro i
  calc
    ‖⟪sqrtOperator ρ (ρ.traceClass.choose_spec.choose i),
        A (sqrtOperator ρ (ρ.traceClass.choose_spec.choose i))⟫_ℂ‖ ≤
      ‖sqrtOperator ρ (ρ.traceClass.choose_spec.choose i)‖ *
        ‖A (sqrtOperator ρ (ρ.traceClass.choose_spec.choose i))‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖sqrtOperator ρ (ρ.traceClass.choose_spec.choose i)‖ *
        (‖A‖ * ‖sqrtOperator ρ (ρ.traceClass.choose_spec.choose i)‖) := by
      gcongr
      exact A.le_opNorm _
    _ = ‖A‖ * ‖sqrtOperator ρ (ρ.traceClass.choose_spec.choose i)‖ ^ 2 := by ring

/-- The square-root quadratic-form functional associated to a density operator. -/
noncomputable def quadraticForm (A : B(H)) : ℂ :=
  ∑' i : ρ.traceClass.choose,
    ⟪sqrtOperator ρ (ρ.traceClass.choose_spec.choose i),
      A (sqrtOperator ρ (ρ.traceClass.choose_spec.choose i))⟫_ℂ

@[simp]
lemma quadraticForm_add (A B : B(H)) :
    ρ.quadraticForm (A + B) = ρ.quadraticForm A + ρ.quadraticForm B := by
  rw [quadraticForm, quadraticForm, quadraticForm]
  have hA := summable_term ρ A
  have hB := summable_term ρ B
  rw [← hA.tsum_add hB]
  apply tsum_congr
  intro i
  simp [inner_add_right]

@[simp]
lemma quadraticForm_smul (c : ℂ) (A : B(H)) :
    ρ.quadraticForm (c • A) = c * ρ.quadraticForm A := by
  rw [quadraticForm, quadraticForm]
  have hA := summable_term ρ A
  have hpoint :
      (fun i : ρ.traceClass.choose =>
        ⟪sqrtOperator ρ (ρ.traceClass.choose_spec.choose i),
          (c • A) (sqrtOperator ρ (ρ.traceClass.choose_spec.choose i))⟫_ℂ) =
        (fun i : ρ.traceClass.choose => c •
          ⟪sqrtOperator ρ (ρ.traceClass.choose_spec.choose i),
            A (sqrtOperator ρ (ρ.traceClass.choose_spec.choose i))⟫_ℂ) := by
    funext i
    simp
  rw [hpoint, hA.tsum_const_smul]
  simp only [smul_eq_mul]

lemma quadraticForm_nonneg {A : B(H)} (hA : 0 ≤ A) :
    0 ≤ ρ.quadraticForm A := by
  apply tsum_nonneg
  intro i
  exact (operator_nonneg_iff_isPositive A).mp hA |>.inner_nonneg_right _

set_option maxHeartbeats 1000000 in
lemma quadraticForm_one : ρ.quadraticForm 1 = 1 := by
  rw [quadraticForm]
  have hdiag : ∀ i : ρ.traceClass.choose,
      ⟪sqrtOperator ρ (ρ.traceClass.choose_spec.choose i),
          sqrtOperator ρ (ρ.traceClass.choose_spec.choose i)⟫_ℂ =
        ⟪ρ.traceClass.choose_spec.choose i,
          ρ.ρ (ρ.traceClass.choose_spec.choose i)⟫_ℂ := by
    intro i
    symm
    calc
      _ = ⟪ρ.traceClass.choose_spec.choose i,
          (sqrtOperator ρ * sqrtOperator ρ)
            (ρ.traceClass.choose_spec.choose i)⟫_ℂ := by rw [root_sq ρ]
      _ = _ := by
        rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
        rw [← ContinuousLinearMap.adjoint_inner_left (sqrtOperator ρ)
          (sqrtOperator ρ (ρ.traceClass.choose_spec.choose i))
          (ρ.traceClass.choose_spec.choose i),
          (ContinuousLinearMap.star_eq_adjoint (sqrtOperator ρ)).symm.trans
            (root_selfAdjoint ρ)]
  calc
    (∑' i : ρ.traceClass.choose,
        ⟪sqrtOperator ρ (ρ.traceClass.choose_spec.choose i),
          (1 : B(H)) (sqrtOperator ρ (ρ.traceClass.choose_spec.choose i))⟫_ℂ) =
        ∑' i : ρ.traceClass.choose,
          ⟪sqrtOperator ρ (ρ.traceClass.choose_spec.choose i),
            sqrtOperator ρ (ρ.traceClass.choose_spec.choose i)⟫_ℂ := by
      apply tsum_congr
      intro i
      simp
    _ = ∑' i : ρ.traceClass.choose,
          ⟪ρ.traceClass.choose_spec.choose i,
            ρ.ρ (ρ.traceClass.choose_spec.choose i)⟫_ℂ := by
      apply tsum_congr
      intro i
      exact hdiag i
    _ = trace ρ.ρ ρ.traceClass := by rfl
    _ = 1 := ρ.trace_eq_one

/-- A state obtained from a density operator without using the trace-ideal product theorem. -/
noncomputable def toStateQuadraticForm : State (B(H)) where
  toPositiveLinearMap := PositiveLinearMap.mk₀
    { toFun := ρ.quadraticForm
      map_add' := ρ.quadraticForm_add
      map_smul' := by
        intro c A
        simpa [smul_eq_mul] using ρ.quadraticForm_smul c A }
    (fun A hA => ρ.quadraticForm_nonneg hA)
  map_one := ρ.quadraticForm_one

@[simp]
lemma toStateQuadraticForm_apply (A : B(H)) :
    ρ.toStateQuadraticForm A = ρ.quadraticForm A := rfl

/-! ## Measurement statistics without the trace-ideal product -/

section BornRule

variable {X : Type*} [MeasurableSpace X]

/-- The Born-rule value obtained from a density operator and a PVM, using the bounded
quadratic-form state.  This is defined for every spectral projection, so it never forms a product
with an unbounded observable and does not require the trace-class right-ideal theorem. -/
noncomputable def bornRuleQuadraticForm (E : PVM X (B(H))) (S : Set X) : ℂ :=
  ρ.toStateQuadraticForm (E S)

@[simp]
lemma bornRuleQuadraticForm_apply (E : PVM X (B(H))) (S : Set X) :
    ρ.bornRuleQuadraticForm E S = ρ.toStateQuadraticForm (E S) := rfl

/-- Born-rule values are nonnegative because every value of a PVM is a positive projection. -/
lemma bornRuleQuadraticForm_nonneg (E : PVM X (B(H))) (S : Set X) :
    0 ≤ ρ.bornRuleQuadraticForm E S := by
  rw [bornRuleQuadraticForm]
  exact ρ.toStateQuadraticForm.toPositiveLinearMap.map_nonneg
    (Projection.nonneg_of_isStarProjection (E.isStarProjection S))

lemma bornRuleQuadraticForm_univ (E : PVM X (B(H))) :
    ρ.bornRuleQuadraticForm E Set.univ = 1 := by
  rw [bornRuleQuadraticForm, E.univ]
  exact ρ.toStateQuadraticForm.map_one

end BornRule

end DensityOperator

end OperatorAlgebra
