/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Basic
public import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-!

# Unitary transformations of observable algebras

A unitary element `U` of a C⋆-algebra acts on the algebra by the inner ⋆-automorphism
`a ↦ U * a * U⋆`. Mathlib already provides this automorphism as `Unitary.conjStarAlgAut`,
together with its inverse and composition laws; this file only packages that existing action for
observables.

## Note

This is a deliberately trimmed port: only what the abstract qubit development (`Qubit/`) needs
to act on Pauli vectors — the automorphism itself and its restriction to observables. The
original also packaged the action on effects and projections; add those back (from physlib's
history) if and when something needs them.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder

variable {A : Type*}
  [OperatorAlgebra A]

namespace Unitary

/-!
## Inner automorphism
-/

/--
The ⋆-algebra automorphism induced by a unitary element.

This is Mathlib's `Unitary.conjStarAlgAut`, exposed with the scalar field specialized to `ℂ`.
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
  ⟨automorphism U (a : A), a.property.map (automorphism U)⟩


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

end Unitary

end OperatorAlgebra
