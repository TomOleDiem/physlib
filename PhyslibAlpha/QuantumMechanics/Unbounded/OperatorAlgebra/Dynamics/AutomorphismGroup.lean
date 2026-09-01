/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Basic
public import Mathlib.Data.NNReal.Basic

/-!
# One-parameter groups of star automorphisms

`AutomorphismGroup A`: a one-parameter group of star-algebra automorphisms, `α (s + t) = α s ∘
α t`, `α 0 = id`, over all of `ℝ` -- the fully reversible notion of dynamics, matching
Hamiltonian/unitary evolution (`Dynamics/Automorphism.lean`, `Dynamics/Hamiltonian.lean`).

Ported from a separate staging tree's `Physlib.Mathematics.OperatorAlgebra.Dynamics`, trimmed to
just `AutomorphismGroup`; the more general `DynamicalSemigroup`/`Channel` levels of dynamics are
not needed here and already have a PhyslibAlpha-native analogue in
`Dynamics/Semigroup.lean`'s `QuantumDynamicalSemigroup`.
-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder CStarAlgebra NNReal

variable {A : Type*} [OperatorAlgebra A]

/--
A one-parameter group of ⋆-algebra automorphisms: `α (s + t) = α s ∘ α t`, `α 0 = id`, over all
of `ℝ` rather than just `ℝ≥0`.

This is the fully reversible notion of dynamics: every `α t` is invertible (with inverse
`α (-t)`), matching Hamiltonian/unitary evolution.
-/
structure AutomorphismGroup (A : Type*) [OperatorAlgebra A] where
  /-- The ⋆-algebra automorphism driving the system after time `t`. -/
  toFun : ℝ → (A ≃⋆ₐ[ℂ] A)
  /-- At time `0`, nothing has happened. -/
  map_zero_apply : ∀ a : A, (toFun 0) a = a
  /-- The group law: evolving by `s + t` is evolving by `t` then by `s`. -/
  map_add_apply : ∀ (s t : ℝ) (a : A), (toFun (s + t)) a = (toFun s) ((toFun t) a)

/-- An `AutomorphismGroup` is determined by its underlying function. -/
@[ext]
lemma AutomorphismGroup.ext {α β : AutomorphismGroup A} (h : ∀ t a, α.toFun t a = β.toFun t a) :
    α = β := by
  have hfun : α.toFun = β.toFun := funext fun t => StarAlgEquiv.ext (h t)
  cases α
  cases β
  cases hfun
  rfl

end OperatorAlgebra
