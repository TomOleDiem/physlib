/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.FiniteDim.DensityOperator
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.States.Convex

/-!

# State representation by density operators in finite dimensions

On a finite-dimensional complex Hilbert space `H`, every state on the observable algebra `B(H)`
is uniquely represented by a positive trace-one operator `ρ`, through `ω A = Tr(ρ A)`:

```
stateEquivDensityOperator : State (B(H)) ≃ DensityOperator H
```

The density operator is stated without choosing a basis. A density matrix is the coordinate
representation of this operator after choosing an orthonormal basis.

This file proves only the equivalence itself, from nondegeneracy of the trace pairing
(`FiniteDim.Trace`). Compact/convex geometry of the set of density operators lives in
`FiniteDim.DensityOperatorGeometry`; pure states and convex decompositions live in
`FiniteDim.PureStates`.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- The density operator representing a state, obtained from nondegeneracy of the trace pairing. -/
noncomputable def densityOperatorOfState (ω : State (B(H))) : B(H) :=
  (LinearMap.BilinForm.toDual (operatorTracePairing (H := H))
    operatorTracePairing_nondegenerate).symm
    ω.toPositiveLinearMap.toLinearMap

/-- The defining representation formula for the density operator of a state. -/
lemma trace_densityOperatorOfState_mul (ω : State (B(H))) (A : B(H)) :
    operatorTracePairing (densityOperatorOfState ω) A = ω A :=
  LinearMap.BilinForm.apply_toDual_symm_apply ω.toPositiveLinearMap.toLinearMap A

/-- The operator representing a state is positive. -/
lemma densityOperatorOfState_nonneg (ω : State (B(H))) :
    0 ≤ densityOperatorOfState ω := by
  rw [operator_nonneg_iff_isPositive,
    ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hx : 0 ≤ InnerProductSpace.rankOne ℂ x x :=
    (operator_nonneg_iff_isPositive _).mpr
      (InnerProductSpace.isPositive_rankOne_self x)
  have hω := ω.toPositiveLinearMap.map_nonneg hx
  rw [← trace_densityOperatorOfState_mul ω,
    operatorTracePairing_rankOne] at hω
  have hω' : 0 ≤ ⟪densityOperatorOfState ω x, x⟫_ℂ := by
    rw [← inner_conj_symm]
    exact star_nonneg_iff.mpr hω
  refine ⟨?_, (Complex.le_def.mp hω').1⟩
  apply Complex.ext
  · simp
  · simpa using (Complex.le_def.mp hω').2

/-- The operator representing a normalized state has trace one. -/
lemma densityOperatorOfState_trace (ω : State (B(H))) :
    LinearMap.trace ℂ H (densityOperatorOfState ω).toLinearMap = 1 := by
  simpa [operatorTracePairing_apply] using trace_densityOperatorOfState_mul ω 1

/-- Bundle the representing operator of a state as a density operator. -/
noncomputable def stateToDensityOperator (ω : State (B(H))) : DensityOperator H :=
  ⟨densityOperatorOfState ω, densityOperatorOfState_nonneg ω,
    densityOperatorOfState_trace ω⟩

/-- A density operator defines a state by the formula `A ↦ Tr(ρA)`. -/
noncomputable def densityOperatorToState (ρ : DensityOperator H) : State (B(H)) where
  toPositiveLinearMap := PositiveLinearMap.mk₀ (operatorTracePairing ρ.1)
    (fun A hA => operatorTracePairing_nonneg ρ.2.1 hA)
  map_one := by
    change operatorTracePairing ρ.1 1 = 1
    simpa [operatorTracePairing_apply] using ρ.2.2

/-- Evaluating the state represented by `ρ` is `A ↦ Tr(ρA)`. -/
@[simp]
lemma densityOperatorToState_apply (ρ : DensityOperator H) (A : B(H)) :
    densityOperatorToState ρ A = LinearMap.trace ℂ H (ρ.1 * A).toLinearMap :=
  rfl

/-- Recovering the representing operator of a density-operator state returns the original
operator. -/
lemma densityOperatorOfState_densityOperatorToState (ρ : DensityOperator H) :
    densityOperatorOfState (densityOperatorToState ρ) = ρ.1 := by
  let e := LinearMap.BilinForm.toDual (operatorTracePairing (H := H))
    operatorTracePairing_nondegenerate
  change e.symm (e ρ.1) = ρ.1
  exact e.symm_apply_apply ρ.1

/-- States on `B(H)` are equivalent to density operators on the finite-dimensional Hilbert
space `H`. Under this equivalence, `ω A = Tr(ρA)`. -/
noncomputable def stateEquivDensityOperator :
    State (B(H)) ≃ DensityOperator H where
  toFun := stateToDensityOperator
  invFun := densityOperatorToState
  left_inv ω := by
    rw [State.mk.injEq]
    apply PositiveLinearMap.ext
    intro A
    change operatorTracePairing (densityOperatorOfState ω) A = ω A
    exact trace_densityOperatorOfState_mul ω A
  right_inv ρ := by
    apply Subtype.ext
    exact densityOperatorOfState_densityOperatorToState ρ

@[simp]
lemma stateEquivDensityOperator_apply (ω : State (B(H))) :
    stateEquivDensityOperator ω = stateToDensityOperator ω :=
  rfl

@[simp]
lemma stateEquivDensityOperator_symm_apply (ρ : DensityOperator H) :
    stateEquivDensityOperator.symm ρ = densityOperatorToState ρ :=
  rfl

/-- The equivalence sends a state `ω` to the unique density operator `ρ` satisfying
`ω A = Tr(ρA)` for every observable `A`. -/
lemma stateEquivDensityOperator_expectation
    (ω : State (B(H))) (A : B(H)) :
    ω A = LinearMap.trace ℂ H ((stateEquivDensityOperator ω).1 * A).toLinearMap :=
  (trace_densityOperatorOfState_mul ω A).symm

/-- Passing a binary convex mixture through the state–density-operator equivalence gives the
same convex mixture of density operators. -/
lemma densityOperatorOfState_mix (ω φ : State (B(H))) (t : ℝ)
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    densityOperatorOfState (State.mix ω φ t ht₀ ht₁) =
      (t : ℂ) • densityOperatorOfState ω +
        ((1 - t : ℝ) : ℂ) • densityOperatorOfState φ := by
  rw [← sub_eq_zero]
  apply operatorTracePairing_separatingLeft
  intro A
  rw [map_sub, map_add, map_smul, map_smul]
  change operatorTracePairing (densityOperatorOfState (State.mix ω φ t ht₀ ht₁)) A -
    ((t : ℂ) * operatorTracePairing (densityOperatorOfState ω) A +
      ((1 - t : ℝ) : ℂ) * operatorTracePairing (densityOperatorOfState φ) A) = 0
  rw [trace_densityOperatorOfState_mul, trace_densityOperatorOfState_mul,
    trace_densityOperatorOfState_mul, State.mix_apply]
  ring

end OperatorAlgebra
