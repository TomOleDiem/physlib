/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!

# Observable algebras

The observable structure of a physical system is described by a unital
complex C⋆-algebra `A`.

The same framework contains both classical and quantum systems:

* a general unital C⋆-algebra describes a quantum observable algebra;
* a commutative unital C⋆-algebra describes a classical observable algebra.

The basic notions of observable, positive element, effect, state, unitary, channel, and finite
POVM depend only on the observable algebra.

This file only defines the vocabulary. Elementary results about each notion live in their own
file (`Observable.lean`, `Effect.lean`, `State.lean`, ...).

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra

namespace OperatorAlgebra


/-!
## Abstract observable algebras

Mathlib's `CStarAlgebra` does not choose a canonical order instance, so notions
using positivity explicitly assume a compatible `PartialOrder` and
`StarOrderedRing`.
-/

section ObservableAlgebra

variable {A : Type*}
  [CStarAlgebra A]
  [PartialOrder A]
  [StarOrderedRing A]


/-- An observable is a self-adjoint element of `A`. -/
noncomputable abbrev Observable (A : Type*)
    [CStarAlgebra A] :=
  selfAdjoint A


/-- A positive element of `A`. -/
@[nolint unusedArguments] -- `StarOrderedRing A` is not used in the statement, but is what
-- makes `≤` the C⋆-algebra order, so that "positive" agrees with the usual notion.
abbrev PositiveElement (A : Type*)
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A] :=
  {a : Observable A // 0 ≤ (a : A)}


/--
An effect is an observable between zero and the identity.

Effects represent yes/no measurement outcomes or, more generally, individual
outcomes of a POVM.
-/
@[nolint unusedArguments] -- see `PositiveElement`
abbrev Effect (A : Type*)
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A] :=
  Set.Icc (0 : Observable A) 1


/-- A finite POVM on `A`. -/
structure POVM
    (A : Type*)
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    (X : Type*) [Fintype X] where
  /-- The effect associated with each measurement outcome. -/
  effect : X → Effect A
  /-- The effects resolve the identity. -/
  sum_effect : ∑ x, (effect x : A) = 1


/-- A unitary element of `A`. -/
noncomputable abbrev Unitary (A : Type*)
    [CStarAlgebra A] :=
  unitary A


/--
A state on `A`.

A state is a positive complex-linear functional normalized by `ω 1 = 1`.
Positivity means that positive elements of `A` are sent to nonnegative real
complex numbers.
-/
structure State (A : Type*)
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A] where
  /-- The positive linear functional underlying the state. -/
  toPositiveLinearMap : A →ₚ[ℂ] ℂ
  /-- A state assigns expectation one to the identity observable. -/
  map_one : toPositiveLinearMap 1 = 1


/--
A channel from `A₁` to `A₂` — physicists' name for a unital completely positive (UCP) map.
The most general notion of dynamics this framework expresses.
-/
abbrev Channel (A₁ A₂ : Type*)
    [CStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁]
    [CStarAlgebra A₂] [PartialOrder A₂] [StarOrderedRing A₂] :=
  {φ : A₁ →CP A₂ // φ 1 = 1}


end ObservableAlgebra


/-!
## Hilbert-space representations

The abstract observable algebra need not initially be presented as operators on
a Hilbert space.

A concrete realization is a unital ⋆-representation into the C⋆-algebra of
bounded operators on a complex Hilbert space.

This is also the target of the GNS construction associated with a state.
-/

section Representation

variable
  {A : Type*}
  {H : Type*}
  [CStarAlgebra A]
  [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
  [CompleteSpace H]


/--
A Hilbert-space representation of `A`.

`Representation A H` is a unital ⋆-homomorphism from `A` into the algebra of
bounded operators on the Hilbert space `H`.
-/
abbrev Representation (A : Type*) (H : Type*)
    [CStarAlgebra A]
    [NormedAddCommGroup H]
    [InnerProductSpace ℂ H]
    [CompleteSpace H] :=
  A →⋆ₐ[ℂ] (H →L[ℂ] H)


end Representation

end OperatorAlgebra
