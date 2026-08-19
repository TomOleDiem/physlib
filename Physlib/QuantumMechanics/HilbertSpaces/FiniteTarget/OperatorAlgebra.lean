/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Operator algebra of a finite-dimensional quantum system

The bounded linear operators on a finite-dimensional Hilbert space form a
C⋆-algebra. For a finite target type `d`, this algebra is `𝓗[d] →L[ℂ] 𝓗[d]`.

This file defines the basic operator-theoretic objects used in finite-dimensional
quantum mechanics:

- the operator C⋆-algebra
- observables
- positive operators
- effects
- density operators
- unitary operators
- orthogonal projections
- POVMs.

-/

@[expose] public section

namespace QuantumMechanics

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The C⋆-algebra of operators on `𝓗[d]`. -/
abbrev OperatorAlgebra
    (d : Type*) [Fintype d] [DecidableEq d] :=
  𝓗[d] →L[ℂ] 𝓗[d]

@[inherit_doc OperatorAlgebra]
scoped notation "𝒜[" d "]" => OperatorAlgebra d

noncomputable instance OperatorAlgebra.instStarModuleReal :
    StarModule ℝ (𝒜[d]) where
  star_smul r A := by
    rw [← Complex.coe_smul r A]
    rw [star_smul]
    simp

/-- The observables on `𝓗[d]`, i.e. its self-adjoint operators. -/
noncomputable abbrev Observable
    (d : Type*) [Fintype d] [DecidableEq d] :=
  selfAdjoint (𝒜[d])

@[inherit_doc Observable]
scoped notation "𝒪[" d "]" => Observable d

/-- The positive operators on `𝓗[d]`. -/
abbrev PositiveOperator
    (d : Type*) [Fintype d] [DecidableEq d] :=
  {A : 𝒪[d] // 0 ≤ (A : 𝒜[d])}

@[inherit_doc PositiveOperator]
scoped notation "𝒜⁺[" d "]" => PositiveOperator d

/-- The trace of an operator on `𝓗[d]`. -/
noncomputable def operatorTrace
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : 𝒜[d]) : ℂ :=
  LinearMap.trace ℂ 𝓗[d] A

/-- A density operator on `𝓗[d]`. -/
noncomputable abbrev DensityOperator
    (d : Type*) [Fintype d] [DecidableEq d] :=
  {ρ : 𝒜⁺[d] // operatorTrace (ρ : 𝒜[d]) = 1}

@[inherit_doc DensityOperator]
scoped notation "𝒟[" d "]" => DensityOperator d

/-- An effect on `𝓗[d]`, i.e. an observable in the interval `[0, 1]`. -/
abbrev Effect
    (d : Type*) [Fintype d] [DecidableEq d] :=
  Set.Icc (0 : 𝒪[d]) 1

@[inherit_doc Effect]
scoped notation "ℰ[" d "]" => Effect d

/-- The unitary operators on `𝓗[d]`. -/
noncomputable abbrev UnitaryOperator
    (d : Type*) [Fintype d] [DecidableEq d] :=
  unitary (𝒜[d])

@[inherit_doc UnitaryOperator]
scoped notation "𝒰[" d "]" => UnitaryOperator d

/-- The orthogonal projections on `𝓗[d]`. -/
abbrev Projection
    (d : Type*) [Fintype d] [DecidableEq d] :=
  {P : 𝒜[d] // IsStarProjection P}

@[inherit_doc Projection]
scoped notation "𝒫[" d "]" => Projection d

/-- A POVM on `𝓗[d]` with outcomes indexed by `X`. -/
structure POVM
    (d : Type*) [Fintype d] [DecidableEq d]
    (X : Type*) [Fintype X] where
  /-- The effect associated with each measurement outcome. -/
  effect : X → ℰ[d]
  /-- The effects resolve the identity. -/
  sum_effect : ∑ x, (effect x : 𝒜[d]) = 1

/-- A first example why these objects can be useful.
The exponential of `i` times an observable is unitary. -/
lemma Observable.exp_mem_unitary
    {d : Type*} [Fintype d] [DecidableEq d]
    (A : 𝒪[d]) :
    NormedSpace.exp (Complex.I • (A : 𝒜[d])) ∈ unitary (𝒜[d]) := by
  exact (selfAdjoint.expUnitary A).property

end QuantumMechanics
