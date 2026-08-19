/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OperatorAlgebra.State

/-!

# Reversible dynamics: one-parameter automorphism groups and state evolution

A classical Hamiltonian flow and quantum unitary evolution (Stone's theorem) both end up producing
a family `α t : A ≃⋆ₐ[ℂ] A` of ⋆-algebra automorphisms with `α 0 = 1` and `α (s + t) = α s * α t` —
the reversible case of a dynamical system, one level more abstract than either: nothing here
refers to a Hilbert space, a phase space, or a Hamiltonian. That data is `RevDynamics A`, i.e.
`AddChar ℝ (A ≃⋆ₐ[ℂ] A)`, since `A ≃⋆ₐ[ℂ] A` is already a group under composition.

`RevDynamics` is the reversible, time-homogeneous special case of the most general dynamics this
framework can express, `EvolutionFamily` (`Channel.lean`): reversible, because every automorphism
is invertible where a general `Channel` need not be; time-homogeneous, because the evolution from
`s` to `t` depends only on `t - s`, which is what lets it be indexed by one real parameter instead
of two.

States transform contravariantly (`Mathematics.OperatorAlgebra.State.pullback`), so such a family
gives a flow on states as well: `evolveState α t ω := pullback (α t) ω`. This is the Schrödinger
picture of the dynamics; `α` itself, acting directly on observables, is the Heisenberg picture.

## Main definitions

* `evolveState`: the flow on states induced by a one-parameter automorphism group.

## Main results

* `evolveState_zero`, `evolveState_add`: `evolveState α` is itself a one-parameter group, acting on
  the right (`evolveState α t` composed after `evolveState α s` is `evolveState α (s + t)`, matching
  the Schrödinger-picture composition order).

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder

variable {A : Type*}
  [CStarAlgebra A]
  [PartialOrder A]
  [StarOrderedRing A]

/--
A one-parameter group of ⋆-algebra automorphisms of `A` — the reversible, time-homogeneous
dynamics produced alike by a classical Hamiltonian flow and quantum unitary (Stone's-theorem)
evolution.
-/
noncomputable abbrev RevDynamics (A : Type*)
    [CStarAlgebra A] :=
  AddChar ℝ (A ≃⋆ₐ[ℂ] A)


/-- The flow on states induced by a one-parameter group of ⋆-algebra automorphisms, by pullback. -/
noncomputable def evolveState
    (α : RevDynamics A)
    (t : ℝ)
    (ω : State A) :
    State A :=
  State.pullback (α t : A ≃⋆ₐ[ℂ] A).toStarAlgHom ω


@[simp]
lemma evolveState_apply
    (α : RevDynamics A)
    (t : ℝ) (ω : State A) (a : A) :
    evolveState α t ω a = ω (α t a) :=
  State.pullback_apply _ _ _


@[simp]
lemma evolveState_zero
    (α : RevDynamics A)
    (ω : State A) :
    evolveState α 0 ω = ω := by
  show State.pullback (α 0 : A ≃⋆ₐ[ℂ] A).toStarAlgHom ω = ω
  rw [α.map_zero_eq_one]
  exact State.pullback_id ω


/-- `evolveState α` is a one-parameter group of state transformations: evolving by `s` and then by
`t` is the same as evolving by `s + t` in one step. -/
lemma evolveState_add
    (α : RevDynamics A)
    (s t : ℝ) (ω : State A) :
    evolveState α (s + t) ω = evolveState α t (evolveState α s ω) := by
  show State.pullback (α (s + t) : A ≃⋆ₐ[ℂ] A).toStarAlgHom ω = _
  rw [α.map_add_eq_mul]
  exact State.pullback_comp (α t : A ≃⋆ₐ[ℂ] A).toStarAlgHom (α s : A ≃⋆ₐ[ℂ] A).toStarAlgHom ω

end OperatorAlgebra
