/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# States on observable algebras

This module owns the state vocabulary. A state is a positive normalized complex-linear functional;
it is deliberately independent of any particular measurement model. Measurement statistics are
defined in `Measurement/Statistics`, and normal states are defined in `States/NormalState`.
-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder CStarAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- A state on `A`: a positive complex-linear functional normalized by `ω 1 = 1`. -/
structure State (A : Type*) [OperatorAlgebra A] where
  /-- The positive linear functional underlying the state. -/
  toPositiveLinearMap : A →ₚ[ℂ] ℂ
  /-- A state assigns expectation one to the identity. -/
  map_one : toPositiveLinearMap 1 = 1

namespace State

noncomputable instance : CoeFun (State A) (fun _ => A → ℂ) where
  coe ω := ω.toPositiveLinearMap

end State

end OperatorAlgebra
