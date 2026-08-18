/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OperatorAlgebra.Basic
public import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic

/-!

# Finite-dimensional quantum systems

A finite-dimensional quantum system with target type `d` is a concrete
Hilbert-space realization whose observable algebra is the full operator
C⋆-algebra on `𝓗[d]`.

Everything in `Physlib.Mathematics.OperatorAlgebra.Basic` specializes directly
to this algebra.

The trace and density operators are genuinely finite-dimensional additions and
therefore live here rather than in the abstract observable-algebra API.

-/

@[expose] public section

open scoped ComplexOrder
open OperatorAlgebra

namespace QuantumMechanics

variable {d : Type*} [Fintype d] [DecidableEq d]


/-- The full C⋆-algebra of bounded operators on the finite-dimensional Hilbert space `𝓗[d]`. -/
abbrev OperatorAlgebra
    (d : Type*) [Fintype d] [DecidableEq d] :=
  𝓗[d] →L[ℂ] 𝓗[d]


@[inherit_doc OperatorAlgebra]
scoped notation "𝒜[" d "]" => OperatorAlgebra d


/-
The self-adjoint part is naturally a real vector space.

This instance is specific to the concrete operator algebra and is useful for
the finite-dimensional observable API.
-/
noncomputable instance OperatorAlgebra.instStarModuleReal :
    StarModule ℝ (𝒜[d]) where
  star_smul r A := by
    rw [← Complex.coe_smul r A]
    rw [star_smul]
    simp


/-- The observables of a finite-dimensional quantum system. -/
noncomputable abbrev FiniteObservable
    (d : Type*) [Fintype d] [DecidableEq d] :=
  Observable (𝒜[d])

@[inherit_doc FiniteObservable]
scoped notation "𝒪[" d "]" => FiniteObservable d


/-- The positive operators of a finite-dimensional quantum system. -/
abbrev PositiveOperator
    (d : Type*) [Fintype d] [DecidableEq d] :=
  PositiveElement (𝒜[d])

@[inherit_doc PositiveOperator]
scoped notation "𝒜⁺[" d "]" => PositiveOperator d


/-- The effects of a finite-dimensional quantum system. -/
abbrev FiniteEffect
    (d : Type*) [Fintype d] [DecidableEq d] :=
  Effect (𝒜[d])

@[inherit_doc FiniteEffect]
scoped notation "ℰ[" d "]" => FiniteEffect d


/-- The unitary operators of a finite-dimensional quantum system. -/
noncomputable abbrev UnitaryOperator
    (d : Type*) [Fintype d] [DecidableEq d] :=
  Unitary (𝒜[d])

@[inherit_doc UnitaryOperator]
scoped notation "𝒰[" d "]" => UnitaryOperator d


/-- The orthogonal projections of a finite-dimensional quantum system. -/
abbrev FiniteProjection
    (d : Type*) [Fintype d] [DecidableEq d] :=
  Projection (𝒜[d])

@[inherit_doc FiniteProjection]
scoped notation "𝒫[" d "]" => FiniteProjection d


/-- The abstract states of the finite-dimensional operator algebra. -/
abbrev FiniteState
    (d : Type*) [Fintype d] [DecidableEq d] :=
  OperatorAlgebra.State (𝒜[d])

@[inherit_doc FiniteState]
scoped notation "𝒮[" d "]" => FiniteState d


/-- A finite POVM on a finite-dimensional quantum system. -/
abbrev FinitePOVM
    (d : Type*) [Fintype d] [DecidableEq d]
    (X : Type*) [Fintype X] :=
  POVM (𝒜[d]) X


/-!
### Trace and density operators

These notions depend on the concrete finite-dimensional Hilbert-space
realization and are not part of the abstract C⋆-algebraic API.
-/

/-- The trace of an operator on `𝓗[d]`. -/
noncomputable def operatorTrace
    (A : 𝒜[d]) : ℂ :=
  LinearMap.trace ℂ 𝓗[d] A


/--
A density operator on the finite-dimensional Hilbert space `𝓗[d]`.

Density operators are the concrete finite-dimensional realization of abstract
states on `𝒜[d]`.
-/
noncomputable abbrev DensityOperator
    (d : Type*) [Fintype d] [DecidableEq d] :=
  {ρ : 𝒜⁺[d] // operatorTrace (ρ : 𝒜[d]) = 1}

@[inherit_doc DensityOperator]
scoped notation "𝒟[" d "]" => DensityOperator d

end QuantumMechanics
