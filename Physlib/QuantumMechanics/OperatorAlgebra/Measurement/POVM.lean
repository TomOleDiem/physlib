/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Observables.Basic

/-!

# Positive operator-valued measures

A finite positive operator-valued measure (POVM) assigns an effect to each
outcome and requires that the effects sum to the identity. This is the first,
finite-outcome measurement layer; measurable-space POVMs and measurement
instruments belong in later modules.

-/

@[expose] public section

namespace OperatorAlgebra

/-- A finite POVM on `A`, indexed by a finite outcome type `X`. -/
structure POVM (A : Type*) [OperatorAlgebra A] (X : Type*) [Fintype X] where
  /-- The effect associated with each measurement outcome. -/
  effect : X → Effect A
  /-- The effects resolve the identity. -/
  sum_effect : ∑ x, (effect x : A) = 1

end OperatorAlgebra
