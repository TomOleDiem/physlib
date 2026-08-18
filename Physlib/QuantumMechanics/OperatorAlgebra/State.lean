/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OperatorAlgebra.State
public import Physlib.Mathematics.OperatorAlgebra.Unitary
public import Physlib.QuantumMechanics.OperatorAlgebra.Basic
public import Physlib.Meta.Linters.Sorry

/-!

# States of finite-dimensional quantum systems

This file relates the abstract C⋆-algebraic notion of a state to the usual
density-operator description of finite-dimensional quantum mechanics.

For the finite-dimensional operator algebra `𝒜[d]`, every density operator
`ρ : 𝒟[d]` defines a state

`A ↦ Tr(ρ A)`,

and every abstract state on `𝒜[d]` arises uniquely in this way.

Thus

`𝒟[d] ≃ State (𝒜[d])`.

This identification is then used to connect the abstract convex geometry of
states with the usual finite-dimensional notions of pure states, vector
states, and unitary evolution.

-/

@[expose] public section

open InnerProductSpace
open scoped ComplexOrder
open OperatorAlgebra

namespace QuantumMechanics

variable {d : Type*} [Fintype d] [DecidableEq d]


/-!
## Density operators as abstract states
-/

/--
A density operator defines a state on the finite-dimensional operator algebra
by

`A ↦ Tr(ρ A)`.
-/
@[sorryful]
noncomputable def DensityOperator.toState
    (ρ : 𝒟[d]) :
    OperatorAlgebra.State (𝒜[d]) := by
  sorry


/-- Evaluation of the state associated with a density operator. -/
@[sorryful]
lemma DensityOperator.toState_apply
    (ρ : 𝒟[d])
    (A : 𝒜[d]) :
    ρ.toState A =
      operatorTrace ((ρ : 𝒜[d]) * A) := by
  sorry


/--
Every state on a finite-dimensional full operator algebra is represented by a
unique density operator.
-/
@[sorryful]
noncomputable def State.toDensityOperator
    (ω : OperatorAlgebra.State (𝒜[d])) :
    𝒟[d] := by
  sorry


/--
Density operators and abstract states on the finite-dimensional operator
algebra are equivalent.
-/
@[sorryful]
noncomputable def densityOperatorEquivState :
    𝒟[d] ≃ OperatorAlgebra.State (𝒜[d]) where
  toFun := DensityOperator.toState
  invFun := State.toDensityOperator
  left_inv := by
    intro ρ
    sorry
  right_inv := by
    intro ω
    sorry


@[simp]
lemma densityOperatorEquivState_apply
    (ρ : 𝒟[d]) :
    densityOperatorEquivState ρ = ρ.toState :=
  rfl


@[simp]
lemma densityOperatorEquivState_symm_apply
    (ω : OperatorAlgebra.State (𝒜[d])) :
    densityOperatorEquivState.symm ω =
      State.toDensityOperator ω :=
  rfl


/-!
## Convex structure

Density operators inherit their convex structure entirely from the abstract state space, by
transport along `densityOperatorEquivState`: `mix` is *defined* through `State.mix`, not
reconstructed by hand. This is what makes it automatically positive and trace one — no separate
proof obligation — and every one of its structural properties below is inherited for free from
the corresponding (still-to-be-proved) fact about `State.mix`.
-/

/-- A convex combination of two density operators, transported from `State.mix`. -/
noncomputable def DensityOperator.mix
    (ρ σ : 𝒟[d])
    (t : ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    𝒟[d] :=
  densityOperatorEquivState.symm (OperatorAlgebra.State.mix ρ.toState σ.toState t ht₀ ht₁)


/--
Taking the abstract state associated with a convex mixture of density
operators gives the corresponding abstract convex mixture.
-/
@[simp]
lemma DensityOperator.toState_mix
    (ρ σ : 𝒟[d])
    (t : ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    (ρ.mix σ t ht₀ ht₁).toState =
      OperatorAlgebra.State.mix ρ.toState σ.toState t ht₀ ht₁ :=
  densityOperatorEquivState.apply_symm_apply _


@[simp]
lemma DensityOperator.mix_zero
    (ρ σ : 𝒟[d]) :
    ρ.mix σ 0 le_rfl zero_le_one = σ :=
  densityOperatorEquivState.injective (by
    rw [densityOperatorEquivState_apply, toState_mix, OperatorAlgebra.State.mix_zero,
      densityOperatorEquivState_apply])


@[simp]
lemma DensityOperator.mix_one
    (ρ σ : 𝒟[d]) :
    ρ.mix σ 1 zero_le_one le_rfl = ρ :=
  densityOperatorEquivState.injective (by
    rw [densityOperatorEquivState_apply, toState_mix, OperatorAlgebra.State.mix_one,
      densityOperatorEquivState_apply])


@[simp]
lemma DensityOperator.mix_self
    (ρ : 𝒟[d])
    (t : ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    ρ.mix ρ t ht₀ ht₁ = ρ :=
  densityOperatorEquivState.injective (by
    rw [densityOperatorEquivState_apply, toState_mix, OperatorAlgebra.State.mix_self,
      densityOperatorEquivState_apply])


/-!
## Pure density operators

Purity is not defined separately for density operators. A density operator is
pure exactly when the corresponding abstract state is pure.
-/

/--
A density operator is pure when the corresponding abstract state is an
extreme point of the state space.
-/
abbrev DensityOperator.IsPure
    (ρ : 𝒟[d]) : Prop :=
  OperatorAlgebra.State.IsPure ρ.toState


/--
A density operator is pure iff its underlying operator is an orthogonal
projection.

Since a density operator has trace one, such a projection necessarily has
rank one.
-/
@[sorryful]
theorem DensityOperator.isPure_iff_isProjection
    (ρ : 𝒟[d]) :
    ρ.IsPure ↔ IsStarProjection (ρ : 𝒜[d]) := by
  sorry


/-- A pure density operator regarded as an orthogonal projection. -/
@[sorryful]
noncomputable def DensityOperator.toProjection
    (ρ : 𝒟[d])
    (hρ : ρ.IsPure) :
    𝒫[d] :=
  ⟨ρ, ρ.isPure_iff_isProjection.mp hρ⟩


/-!
## Vector states
-/

/-- The rank-one operator `|ψ⟩⟨ψ|`. -/
noncomputable def rankOneOperator
    (ψ : 𝓗[d]) :
    𝒜[d] :=
  (InnerProductSpace.rankOne ℂ ψ) ψ


/-- A unit vector defines an orthogonal rank-one projection. -/
@[sorryful]
noncomputable def unitVectorProjection
    (ψ : 𝓗[d])
    (hψ : ‖ψ‖ = 1) :
    𝒫[d] := by
  refine ⟨rankOneOperator ψ, ?_⟩
  sorry


/--
A unit vector defines a density operator through its rank-one projector.
-/
@[sorryful]
noncomputable def DensityOperator.ofUnitVector
    (ψ : 𝓗[d])
    (hψ : ‖ψ‖ = 1) :
    𝒟[d] := by
  refine ⟨⟨⟨rankOneOperator ψ, ?_⟩, ?_⟩, ?_⟩
  · sorry
  · sorry
  · sorry


/-- The density operator associated with a unit vector is pure. -/
@[sorryful]
theorem DensityOperator.ofUnitVector_isPure
    (ψ : 𝓗[d])
    (hψ : ‖ψ‖ = 1) :
    (DensityOperator.ofUnitVector ψ hψ).IsPure := by
  rw [DensityOperator.isPure_iff_isProjection]
  sorry


/--
Multiplication of a unit vector by a global phase does not change the
associated density operator.
-/
@[sorryful]
theorem DensityOperator.ofUnitVector_phase
    (ψ : 𝓗[d])
    (hψ : ‖ψ‖ = 1)
    (c : ℂ)
    (hc : ‖c‖ = 1) :
    DensityOperator.ofUnitVector
        (c • ψ)
        (by simp [norm_smul, hc, hψ]) =
      DensityOperator.ofUnitVector ψ hψ := by
  sorry


/--
For a vector state, the abstract state associated with its density operator
agrees with the usual Hilbert-space expectation value.
-/
@[sorryful]
theorem DensityOperator.ofUnitVector_toState_apply
    (ψ : 𝓗[d])
    (hψ : ‖ψ‖ = 1)
    (A : 𝒜[d]) :
    (DensityOperator.ofUnitVector ψ hψ).toState A =
      ⟪ψ, A ψ⟫_ℂ := by
  sorry


/-!
## Unitary action

The generic operator-algebra API already knows that a unitary induces an inner
⋆-automorphism (`Unitary.automorphism`). Conjugating a density operator by `U` is *defined* by
transporting the corresponding pullback of its state along `(Unitary.automorphism U).symm` —
states transform contravariantly, so conjugating the operator by `U` pulls the state back along
the inverse automorphism. As with `mix`, positivity and trace one come for free from
`densityOperatorEquivState`, with nothing left to reprove by hand.
-/

/-- Unitary conjugation of a density operator, transported from the pullback action on its
associated state. -/
noncomputable def DensityOperator.unitaryConjugate
    (ρ : 𝒟[d])
    (U : 𝒰[d]) :
    𝒟[d] :=
  densityOperatorEquivState.symm
    (OperatorAlgebra.State.pullback (Unitary.automorphism U).symm.toStarAlgHom ρ.toState)


/--
The state of a unitarily-conjugated density operator is the pullback of the original state
along the inverse automorphism.
-/
@[simp]
lemma DensityOperator.toState_unitaryConjugate
    (ρ : 𝒟[d])
    (U : 𝒰[d]) :
    (ρ.unitaryConjugate U).toState =
      OperatorAlgebra.State.pullback (Unitary.automorphism U).symm.toStarAlgHom ρ.toState :=
  densityOperatorEquivState.apply_symm_apply _


/-- The density operator underlying `ρ.unitaryConjugate U` is `U ρ U⋆`. -/
@[sorryful]
lemma DensityOperator.coe_unitaryConjugate
    (ρ : 𝒟[d])
    (U : 𝒰[d]) :
    (ρ.unitaryConjugate U : 𝒜[d]) =
      (U : 𝒜[d]) * (ρ : 𝒜[d]) * star (U : 𝒜[d]) := by
  sorry


/--
Successive unitary conjugations compose by multiplication.
-/
@[sorryful]
theorem DensityOperator.unitaryConjugate_mul
    (ρ : 𝒟[d])
    (U V : 𝒰[d]) :
    (ρ.unitaryConjugate V).unitaryConjugate U =
      ρ.unitaryConjugate (U * V) := by
  sorry


/--
Unitary conjugation preserves convex combinations of density operators.
-/
@[sorryful]
theorem DensityOperator.unitaryConjugate_mix
    (ρ σ : 𝒟[d])
    (U : 𝒰[d])
    (t : ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    (ρ.mix σ t ht₀ ht₁).unitaryConjugate U =
      (ρ.unitaryConjugate U).mix
        (σ.unitaryConjugate U) t ht₀ ht₁ := by
  sorry


/--
Purity is invariant under unitary conjugation.
-/
@[sorryful]
theorem DensityOperator.isPure_unitaryConjugate_iff
    (ρ : 𝒟[d])
    (U : 𝒰[d]) :
    (ρ.unitaryConjugate U).IsPure ↔
      ρ.IsPure := by
  sorry

end QuantumMechanics
