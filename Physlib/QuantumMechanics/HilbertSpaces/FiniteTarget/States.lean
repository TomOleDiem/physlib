/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.OperatorALgebra
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# States of finite-dimensional quantum systems

This file develops the state space of a finite-dimensional quantum system.

Density operators form a convex state space. Its extreme points are the pure
states, equivalently the rank-one orthogonal projections. Unit vectors define
pure states through their rank-one projectors, with global phase acting
trivially.

Unitary operators act on density operators by conjugation and preserve both
convex combinations and purity.

Finally, density operators are identified with positive normalized linear
functionals on the operator algebra.
-/

@[expose] public section

namespace QuantumMechanics

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Convex structure -/

/-- A convex combination of two density operators. -/
noncomputable def DensityOperator.mix
    (ρ σ : 𝒟[d]) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    𝒟[d] := by
  let A : 𝒪[d] :=
    t • (ρ.1 : 𝒪[d]) + (1 - t) • (σ.1 : 𝒪[d])
  refine ⟨⟨A, ?_⟩, ?_⟩
  · sorry
  · sorry

/-- A density operator is extreme if every nontrivial convex decomposition
of it is trivial. -/
def DensityOperator.IsExtreme (ρ : 𝒟[d]) : Prop :=
  ∀ (σ τ : 𝒟[d]) (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1),
    DensityOperator.mix σ τ t ht₀.le ht₁.le = ρ →
      σ = τ

/-- A pure state is an extreme density operator. -/
abbrev DensityOperator.IsPure (ρ : 𝒟[d]) : Prop :=
  ρ.IsExtreme

/-! ## Pure states and projections -/

/-- A density operator is pure iff its underlying operator is an orthogonal
projection. Since a density operator has trace one, such a projection
necessarily has rank one. -/
theorem DensityOperator.isPure_iff_isProjection
    (ρ : 𝒟[d]) :
    ρ.IsPure ↔ IsStarProjection (ρ : 𝒜[d]) := by
  sorry

/-- A pure density operator regarded as an orthogonal projection. -/
noncomputable def DensityOperator.toProjection
    (ρ : 𝒟[d]) (hρ : ρ.IsPure) :
    𝒫[d] :=
  ⟨ρ, ρ.isPure_iff_isProjection.mp hρ⟩

/-! ## Vector states -/

/-- The rank-one operator `|ψ⟩⟨ψ|`. -/
noncomputable def rankOneOperator
    (ψ : 𝓗[d]) :
    𝒜[d] :=
  (InnerProductSpace.rankOne ℂ ψ) ψ

/-- A unit vector defines an orthogonal rank-one projection. -/
noncomputable def unitVectorProjection
    (ψ : 𝓗[d]) (hψ : ‖ψ‖ = 1) :
    𝒫[d] := by
  refine ⟨rankOneOperator ψ, ?_⟩
  sorry

/-- A unit vector defines a density operator through its rank-one projector. -/
noncomputable def DensityOperator.ofUnitVector
    (ψ : 𝓗[d]) (hψ : ‖ψ‖ = 1) :
    𝒟[d] := by
  refine ⟨⟨⟨rankOneOperator ψ, ?_⟩, ?_⟩, ?_⟩
  · sorry
  · sorry
  · sorry

/-- The density operator associated with a unit vector is pure. -/
theorem DensityOperator.ofUnitVector_isPure
    (ψ : 𝓗[d]) (hψ : ‖ψ‖ = 1) :
    (DensityOperator.ofUnitVector ψ hψ).IsPure := by
  rw [DensityOperator.isPure_iff_isProjection]
  sorry

/-- Multiplication of a unit vector by a global phase does not change the
associated pure state. -/
theorem DensityOperator.ofUnitVector_phase
    (ψ : 𝓗[d]) (hψ : ‖ψ‖ = 1)
    (c : ℂ) (hc : ‖c‖ = 1) :
    DensityOperator.ofUnitVector
        (c • ψ)
        (by simp [norm_smul, hc, hψ]) =
      DensityOperator.ofUnitVector ψ hψ := by
  sorry

/-! ## Unitary action -/

/-- Unitary conjugation preserves density operators. -/
noncomputable def DensityOperator.unitaryConjugate
    (ρ : 𝒟[d]) (U : 𝒰[d]) :
    𝒟[d] := by
  refine
    ⟨⟨⟨(U : 𝒜[d]) * (ρ : 𝒜[d]) * star (U : 𝒜[d]), ?_⟩, ?_⟩, ?_⟩
  · sorry
  · sorry
  · sorry

/-- Successive unitary conjugations compose by multiplication. -/
theorem DensityOperator.unitaryConjugate_mul
    (ρ : 𝒟[d]) (U V : 𝒰[d]) :
    (ρ.unitaryConjugate V).unitaryConjugate U =
      ρ.unitaryConjugate (U * V) := by
  sorry

/-- Unitary conjugation preserves convex combinations. -/
theorem DensityOperator.unitaryConjugate_mix
    (ρ σ : 𝒟[d]) (U : 𝒰[d])
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (ρ.mix σ t ht₀ ht₁).unitaryConjugate U =
      (ρ.unitaryConjugate U).mix
        (σ.unitaryConjugate U) t ht₀ ht₁ := by
  sorry

/-- Purity is invariant under unitary conjugation. -/
theorem DensityOperator.isPure_unitaryConjugate_iff
    (ρ : 𝒟[d]) (U : 𝒰[d]) :
    (ρ.unitaryConjugate U).IsPure ↔ ρ.IsPure := by
  sorry

/-! ## States as positive linear functionals -/

/-- A state on the finite-dimensional operator algebra is a positive
complex-linear functional normalized on the identity. -/
structure OperatorState
    (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The underlying complex-linear functional. -/
  toLinearMap : 𝒜[d] →ₗ[ℂ] ℂ
  /-- Positive operators are mapped to nonnegative real numbers. -/
  map_positive :
    ∀ A : 𝒜⁺[d],
      IsSelfAdjoint (toLinearMap (A : 𝒜[d])) ∧
        0 ≤ (toLinearMap (A : 𝒜[d])).re
  /-- The state is normalized on the identity. -/
  map_one :
    toLinearMap 1 = 1

noncomputable instance : CoeFun (OperatorState d) (fun _ => 𝒜[d] → ℂ) :=
  ⟨fun ω => ω.toLinearMap⟩

/-- A density operator defines a positive normalized functional by
`A ↦ Tr(ρA)`. -/
noncomputable def DensityOperator.toState
    (ρ : 𝒟[d]) :
    OperatorState d where
  toLinearMap :=
    {
      toFun := fun A => operatorTrace ((ρ : 𝒜[d]) * A)
      map_add' := by
        intro A B
        sorry
      map_smul' := by
        intro c A
        sorry
    }
  map_positive := by
    intro A
    sorry
  map_one := by
    sorry

/-- Every positive normalized functional on a finite-dimensional operator
algebra is represented by a unique density operator. -/
noncomputable def OperatorState.toDensityOperator
    (ω : OperatorState d) :
    𝒟[d] := by
  sorry

/-- Density operators are equivalent to positive normalized linear
functionals on the operator algebra. -/
noncomputable def densityOperatorEquivOperatorState :
    𝒟[d] ≃ OperatorState d where
  toFun := DensityOperator.toState
  invFun := OperatorState.toDensityOperator
  left_inv := by
    intro ρ
    sorry
  right_inv := by
    intro ω
    sorry

/-- For a vector state, the density-operator expectation agrees with the
usual Hilbert-space expectation value. -/
theorem DensityOperator.ofUnitVector_toState_apply
    (ψ : 𝓗[d]) (hψ : ‖ψ‖ = 1)
    (A : 𝒜[d]) :
    (DensityOperator.ofUnitVector ψ hψ).toState A =
      ⟪ψ, A ψ⟫_ℂ := by
  sorry

end QuantumMechanics
