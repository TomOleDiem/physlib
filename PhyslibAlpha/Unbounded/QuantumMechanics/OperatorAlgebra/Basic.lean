/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!

# Observable algebras

The observable structure of a physical system is described by a unital complex C⋆-algebra `A`.

The same framework contains both classical and quantum systems, according to which C⋆-algebra is
chosen:

* **quantum**: `B(H)`, the bounded operators on a Hilbert space `H` — generally noncommutative.
  E.g. unitary evolution, `a ↦ U a U⋆`, is how a Hamiltonian moves observables in time.
* **classical**: `C(M)`, continuous functions on phase space `M` — commutative, matching how
  classical observables always commute. E.g. position and momentum are just two such functions.

The basic notions of observable, positive element, effect, unitary, and channel depend only on the
observable algebra. States live in `OperatorAlgebra/States`, while PVMs and POVMs live in
`OperatorAlgebra/Measurement`.

This file only defines the algebraic vocabulary. Elementary results about each notion live in their
own module.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra

/-- A unital complex C⋆-algebra with a compatible order making `≤` the usual positivity order.
Mathlib doesn't pick one canonically, so definitions below that need `≤` take this instead of
just `CStarAlgebra`. -/
class OperatorAlgebra (A : Type*) extends CStarAlgebra A, PartialOrder A, StarOrderedRing A

namespace OperatorAlgebra

section ObservableAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- An observable is a self-adjoint element of `A`: position, momentum, energy, spin, ... .
Self-adjointness is exactly what makes an element a *measurable* quantity — it is what forces its
spectrum, the possible measurement outcomes, to be real. -/
noncomputable abbrev Observable (A : Type*) [OperatorAlgebra A] := selfAdjoint A

/-- A positive element of `A`: an observable whose measurement outcomes are all `≥ 0`.
Positivity is what gives observables a meaningful order (`a ≤ b` meaning `b - a` is positive). -/
abbrev PositiveElement (A : Type*) [OperatorAlgebra A] := {a : Observable A // 0 ≤ (a : A)}

/-- An effect is an observable between zero and the identity, representing a yes/no measurement
outcome. -/
abbrev Effect (A : Type*) [OperatorAlgebra A] := Set.Icc (0 : Observable A) 1

/-- A unitary element of `A`: implements a reversible transformation of the system — a symmetry,
or time evolution under a Hamiltonian — acting on observables by conjugation, `a ↦ U a U⋆`. -/
noncomputable abbrev Unitary (A : Type*) [OperatorAlgebra A] := unitary A

/-- A channel from `A₁` to `A₂` — physicists' name for a unital completely positive (UCP) map,
the most general notion of dynamics this framework expresses. -/
abbrev Channel (A₁ A₂ : Type*) [OperatorAlgebra A₁] [OperatorAlgebra A₂] :=
  {φ : A₁ →CP A₂ // φ 1 = 1}

/-- A `Channel` acts on `A₁` the same way its underlying completely positive map does. Subtype
coercion alone only gets as far as the bundled `A₁ →CP A₂`; this composes it with that map's own
`FunLike` coercion so `φ a` (for `φ : Channel A₁ A₂`) elaborates directly, without every call site
needing an explicit `(φ : A₁ →CP A₂) a` or `φ.1 a`. -/
noncomputable instance instCoeFunChannel {A₁ A₂ : Type*} [OperatorAlgebra A₁]
    [OperatorAlgebra A₂] : CoeFun (Channel A₁ A₂) (fun _ => A₁ → A₂) where
  coe φ := φ.1

end ObservableAlgebra

end OperatorAlgebra
