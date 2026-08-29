/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Basic

/-!

# States on observable algebras

A state is a normalized positive complex-linear functional. It records the
expectation values of observables in a physical preparation.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- A state on `A`: a positive complex-linear functional normalized at `1`. -/
structure State (A : Type*) [OperatorAlgebra A] where
  /-- The positive linear functional underlying the state. -/
  toPositiveLinearMap : A →ₚ[ℂ] ℂ
  /-- A state assigns expectation one to the identity observable. -/
  map_one : toPositiveLinearMap 1 = 1

namespace State

noncomputable instance : CoeFun (State A) (fun _ => A → ℂ) where
  coe ω := ω.toPositiveLinearMap

@[ext]
lemma ext {ω φ : State A} (h : ∀ a, ω a = φ a) : ω = φ := by
  cases ω
  cases φ
  congr
  exact PositiveLinearMap.ext h

end State

end OperatorAlgebra
