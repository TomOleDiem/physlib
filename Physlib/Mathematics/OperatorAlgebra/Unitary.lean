/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OperatorAlgebra.Effect
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!

# Unitary transformations of observable algebras

A unitary element `U` of a C⋆-algebra acts on the algebra by the inner
⋆-automorphism

`a ↦ U * a * U⋆`.

Mathlib already provides this automorphism as `Unitary.conjStarAlgAut`,
together with its inverse and composition laws.

This file only packages that existing action for the basic objects of the
observable-algebra API:

* observables;
* effects;
* projections.

No separate notion of unitary conjugation is introduced.

-/

@[expose] public section

namespace QuantumMechanics

open scoped ComplexOrder

variable {A : Type*}
  [CStarAlgebra A]
  [PartialOrder A]
  [StarOrderedRing A]

namespace Unitary


/-!
## Inner automorphism
-/

/--
The ⋆-algebra automorphism induced by a unitary element.

This is Mathlib's `Unitary.conjStarAlgAut`, exposed with the scalar field
specialized to `ℂ`.
-/
noncomputable abbrev automorphism
    (U : Unitary A) :
    A ≃⋆ₐ[ℂ] A :=
  (_root_.Unitary.conjStarAlgAut ℂ A) U


/-- The unitary automorphism acts by `a ↦ U * a * U⋆`. -/
@[simp]
lemma automorphism_apply
    (U : Unitary A)
    (a : A) :
    automorphism U a =
      (U : A) * a * star (U : A) := by
  exact _root_.Unitary.conjStarAlgAut_apply U a


/-!
## Observables
-/

/-- Unitary conjugation preserves observables. -/
noncomputable def observable
    (U : Unitary A)
    (a : Observable A) :
    Observable A :=
  ⟨automorphism U (a : A), by
    sorry⟩


@[simp]
lemma coe_observable
    (U : Unitary A)
    (a : Observable A) :
    (observable U a : A) =
      automorphism U (a : A) :=
  rfl


@[simp]
lemma coe_observable_eq
    (U : Unitary A)
    (a : Observable A) :
    (observable U a : A) =
      (U : A) * (a : A) * star (U : A) := by
  simp [observable]


/-!
## Effects
-/

/-- Unitary conjugation preserves effects. -/
noncomputable def effect
    (U : Unitary A)
    (E : Effect A) :
    Effect A :=
  ⟨observable U (E : Observable A), by
    constructor
    · sorry
    · sorry⟩


@[simp]
lemma coe_effect
    (U : Unitary A)
    (E : Effect A) :
    (effect U E : Observable A) =
      observable U (E : Observable A) :=
  rfl


/-!
## Projections
-/

/-- Unitary conjugation preserves projections. -/
noncomputable def projection
    (U : Unitary A)
    (P : Projection A) :
    Projection A :=
  ⟨automorphism U (P : A), by
    sorry⟩


@[simp]
lemma coe_projection
    (U : Unitary A)
    (P : Projection A) :
    (projection U P : A) =
      automorphism U (P : A) :=
  rfl


end Unitary

end QuantumMechanics
