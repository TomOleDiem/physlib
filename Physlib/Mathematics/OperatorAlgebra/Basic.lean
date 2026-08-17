/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.FiniteTarget.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Algebra.Order.Module.PositiveLinearMap

/-!

# Observable algebras

The observable structure of a physical system is described by a unital
complex C⋆-algebra `A`.

The same framework contains both classical and quantum systems:

* a general C⋆-algebra describes a quantum observable algebra;
* a commutative C⋆-algebra describes a classical observable algebra;
* the bounded operators on a Hilbert space give a concrete realization;
* finite-dimensional quantum systems are the special case
  `𝓗[d] →L[ℂ] 𝓗[d]`.

The basic notions of observable, positive element, effect, state, unitary,
projection, and finite POVM depend only on the observable algebra and should
therefore not be tied to finite-dimensional Hilbert spaces.

A concrete Hilbert-space realization of an abstract observable algebra `A`
is a ⋆-representation

`A →⋆ₐ[ℂ] (H →L[ℂ] H)`.

Density operators are different: they use the trace and are therefore defined
below only for finite-dimensional Hilbert-space realizations. In finite
dimension they provide the concrete realization of abstract states.

This file develops the unital theory. Classical systems on noncompact spaces,
whose natural observable algebra is typically the non-unital C⋆-algebra
`C₀(X)`, should eventually be treated through the corresponding
`NonUnitalCStarAlgebra` API.

-/

@[expose] public section

open scoped ComplexOrder

namespace QuantumMechanics


/-!
## Abstract observable algebras

We do not introduce an additional bundled `QuantumSystem` structure here.
The C⋆-algebra itself is the observable algebra.

Mathlib's `CStarAlgebra` does not choose a canonical order instance, so notions
using positivity explicitly assume a compatible `PartialOrder` and
`StarOrderedRing`.
-/

section ObservableAlgebra

variable {A : Type*}
  [CStarAlgebra A]
  [PartialOrder A]
  [StarOrderedRing A]


/-- An observable is a self-adjoint element of the observable C⋆-algebra. -/
noncomputable abbrev Observable (A : Type*)
    [CStarAlgebra A] :=
  selfAdjoint A


/-- A positive element of an observable C⋆-algebra. -/
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
abbrev Effect (A : Type*)
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A] :=
  Set.Icc (0 : Observable A) 1


/-- A unitary element of an observable C⋆-algebra. -/
noncomputable abbrev Unitary (A : Type*)
    [CStarAlgebra A] :=
  unitary A


/-- An orthogonal projection in an observable C⋆-algebra. -/
abbrev Projection (A : Type*)
    [CStarAlgebra A] :=
  {p : A // IsStarProjection p}

/--
A state on a unital C⋆-algebra.

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


noncomputable instance State.instCoeFun :
    CoeFun (State A) (fun _ => A → ℂ) where
  coe ω := ω.toPositiveLinearMap


@[simp]
lemma State.apply_one (ω : State A) :
    ω 1 = 1 :=
  ω.map_one


/--
A finite POVM on an observable C⋆-algebra.

Only the outcome type is required to be finite; the observable algebra itself
may be infinite-dimensional.
-/
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


end ObservableAlgebra


/-!
## Classical systems

There is deliberately no separate definition of classical observable,
classical state, classical effect, etc.

A classical observable algebra is simply a commutative C⋆-algebra. All of the
definitions above therefore apply unchanged.

Thus the distinction at this level is

* quantum: `CStarAlgebra A`,
* classical: `CommCStarAlgebra A`.

Gelfand duality identifies a commutative unital C⋆-algebra with an algebra of
continuous functions on a compact Hausdorff space.
-/

section Classical

variable {A : Type*}
  [CommCStarAlgebra A]
  [PartialOrder A]
  [StarOrderedRing A]

/--
A marker proposition expressing that an observable algebra is classical.

This is mathematically equivalent here to commutativity. In most theorems it is
preferable simply to assume `[CommCStarAlgebra A]` directly.
-/
def IsClassicalObservableAlgebra : Prop :=
  ∀ a b : A, a * b = b * a


omit [PartialOrder A] [StarOrderedRing A]
@[simp]
lemma isClassicalObservableAlgebra :
    IsClassicalObservableAlgebra (A := A) := by
  intro a b
  exact mul_comm a b

end Classical


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
A Hilbert-space representation of an observable C⋆-algebra.

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


/-!
## Finite-dimensional quantum systems

A finite-dimensional quantum system with target type `d` is a concrete
Hilbert-space realization whose observable algebra is the full operator
C⋆-algebra on `𝓗[d]`.

Everything defined above specializes directly to this algebra.

The trace and density operators are genuinely finite-dimensional additions and
therefore live in this section rather than in the general observable-algebra
API.
-/

section FiniteDimensional

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
  State (𝒜[d])

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


end FiniteDimensional

end QuantumMechanics
