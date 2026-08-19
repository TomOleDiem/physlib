/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Basic
public import Physlib.Meta.TODO.Basic
public import Mathlib.Data.NNReal.Basic

/-!

# Levels of dynamics

A `Channel A A` (`Physlib.QuantumMechanics.OperatorAlgebra.Basic`) is a single, timeless unital
completely positive map — the most general notion of "what a physical process can do to
observables" this framework expresses, with no reference to time at all. Actual *dynamics*
comes from indexing channels by time and imposing a compatibility law; how strong a law you
impose is exactly how reversible the dynamics is:

* an arbitrary function `ℝ≥0 → Channel A A`, no law at all: not developed further here, it is
  just "a channel at every time", nothing yet ties different times together;
* `DynamicalSemigroup A`: `T (s + t) = T s ∘ T t`, `T 0 = id` — time-homogeneous, and in general
  irreversible (this is where Lindblad-type generators eventually live);
* `AutomorphismGroup A`: the same law, but over all of `ℝ`, by ⋆-algebra automorphisms rather
  than plain channels — fully time-reversible (this is where unitary/Hamiltonian evolution
  lives; see `Qubit/Unitary.lean`'s `R` and, eventually, `Qubit/Dynamics.lean`).

Every automorphism group is, in particular, a dynamical semigroup (a ⋆-algebra automorphism is
completely positive), and every dynamical semigroup is, in particular, an indexed family of
channels. That inclusion chain is not yet formalized here — see `Dynamics.lean`'s `TODO`s.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder CStarAlgebra NNReal

variable {A : Type*} [OperatorAlgebra A]

/--
A dynamical semigroup: a time-homogeneous one-parameter family of channels satisfying the
semigroup law `T (s + t) = T s ∘ T t`, `T 0 = id`.

This is the general notion of dynamics — in particular it need not be reversible.
-/
structure DynamicalSemigroup (A : Type*)
    [OperatorAlgebra A] where
  /-- The channel driving the system after time `t`. -/
  toFun : ℝ≥0 → Channel A A
  /-- At time `0`, nothing has happened. -/
  map_zero_apply : ∀ a : A, (toFun 0 : A →CP A) a = a
  /-- The semigroup law: evolving by `s + t` is evolving by `t` then by `s`. -/
  map_add_apply : ∀ (s t : ℝ≥0) (a : A),
    (toFun (s + t) : A →CP A) a = (toFun s : A →CP A) ((toFun t : A →CP A) a)


/--
A one-parameter group of ⋆-algebra automorphisms: `α (s + t) = α s ∘ α t`, `α 0 = id`, over all
of `ℝ` rather than just `ℝ≥0`.

This is the fully reversible notion of dynamics: every `α t` is invertible (with inverse
`α (-t)`), matching Hamiltonian/unitary evolution.
-/
structure AutomorphismGroup (A : Type*) [CStarAlgebra A] where
  /-- The ⋆-algebra automorphism driving the system after time `t`. -/
  toFun : ℝ → (A ≃⋆ₐ[ℂ] A)
  /-- At time `0`, nothing has happened. -/
  map_zero_apply : ∀ a : A, (toFun 0) a = a
  /-- The group law: evolving by `s + t` is evolving by `t` then by `s`. -/
  map_add_apply : ∀ (s t : ℝ) (a : A), (toFun (s + t)) a = (toFun s) ((toFun t) a)

TODO "Show `AutomorphismGroup A` embeds into `DynamicalSemigroup A`: a ⋆-algebra automorphism,
  restricted to `t ≥ 0`, gives a `Channel A A` (need: ⋆-algebra automorphisms are completely
  positive and unital — the latter is free, the former does not yet seem to be in Mathlib for
  general C⋆-algebras and may be worth upstreaming). This is what makes 'group ⊂ semigroup ⊂
  channel' an actual inclusion chain rather than just three unrelated structures."

end OperatorAlgebra
