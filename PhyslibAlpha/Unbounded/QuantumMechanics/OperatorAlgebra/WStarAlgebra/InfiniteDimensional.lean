/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.WStarAlgebra
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.WStarAlgebra.TracePairingSurjectivity

/-!
# The infinite-dimensional `B(H)` predual

This module is the public integration point for the concrete infinite-dimensional predual of
`B(H)`. The analytic work is in `TracePairingSurjectivity.lean`: trace-class operators form a
complete normed space, the trace pairing is an isometry, and Hilbert--Schmidt truncation proves
that the pairing is onto. This file only packages that proved equivalence as the `WStarAlgebra`
instance.

Unlike the earlier placeholder implementation, no capability class or unproved surjectivity
certificate is used here.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TraceClass

/- The concrete trace pairing is surjective onto the strong dual of the trace class. -/
theorem tracePairing_surjective :
    Function.Surjective (⇑(tracePairingLinearIsometry (H := H))) :=
  tracePairing_surjective_concrete

/- The isometric identification of `B(H)` with the strong dual of its trace class. -/
def tracePairingEquiv : B(H) ≃ₗᵢ[ℂ] StrongDual ℂ (TraceClass H) :=
  LinearIsometryEquiv.ofSurjective tracePairingLinearIsometry tracePairing_surjective

@[simp] theorem tracePairingEquiv_apply (A : B(H)) :
    tracePairingEquiv A = tracePairing A := rfl

end TraceClass

/-! ## The `WStarAlgebra (B(H))` instance -/

/- `B(H)` with its trace class as predual. -/
noncomputable instance instWStarAlgebraOfInfiniteDimensional : WStarAlgebra (B(H)) where
  Predual := TraceClass H
  predual_normedAddCommGroup := TraceClass.instNormedAddCommGroup
  predual_normedSpace := TraceClass.instNormedSpace
  predual_completeSpace := TraceClass.instCompleteSpace
  toDual := TraceClass.tracePairingEquiv

end OperatorAlgebra
