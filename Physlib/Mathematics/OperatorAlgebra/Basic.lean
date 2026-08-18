/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

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
* the bounded operators on a Hilbert space give a concrete realization.

The basic notions of observable, positive element, effect, state, unitary,
projection, and finite POVM depend only on the observable algebra and are
therefore developed here without reference to any Hilbert space.

Density operators, traces, and other genuinely finite-dimensional Hilbert-space
notions are *not* part of this abstract theory. They live in
`QuantumMechanics.OperatorAlgebra`, which specializes this file's definitions
to the concrete algebra `𝓗[d] →L[ℂ] 𝓗[d]` of a finite-dimensional quantum
system.

-/

@[expose] public section

open scoped ComplexOrder

namespace OperatorAlgebra


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


/--
A star-algebra equivalence restricts to a real-linear equivalence of the self-adjoint elements
(observables, when `A` is an observable algebra) on each side.

This is the general fact behind identifying concrete finite-dimensional observables with
self-adjoint matrices: build the star-algebra equivalence once, then get the equivalence of
self-adjoint elements for free. Stated for `selfAdjoint` rather than `Observable` so it applies
even when the codomain, such as a bare matrix algebra, is not itself a `CStarAlgebra`.
-/
def _root_.StarAlgEquiv.selfAdjointCongr {A B : Type*}
    [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℝ A]
    [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℝ B]
    (e : A ≃⋆ₐ[ℂ] B) :
    selfAdjoint A ≃ₗ[ℝ] selfAdjoint B where
  toFun a := ⟨e a, a.property.map e⟩
  invFun b := ⟨e.symm b, b.property.map e.symm⟩
  left_inv a := Subtype.ext (e.symm_apply_apply (a : A))
  right_inv b := Subtype.ext (e.apply_symm_apply (b : B))
  map_add' a b := Subtype.ext (map_add e (a : A) (b : A))
  map_smul' r a := Subtype.ext (by
    show e (r • (a : A)) = r • e (a : A)
    rw [← Complex.coe_smul, map_smul, Complex.coe_smul])


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

end OperatorAlgebra
