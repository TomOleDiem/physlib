/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Physlib.ProbabilisticTheory.State.Basic

/-!
# Reversible dynamics and covariant channels

## i. Overview

Time evolution, a spatial symmetry and a change of frame share one property. They map observables
to observables, and a possible outcome stays possible. The certain outcome stays certain. They
can be undone. Such a map is an invertible channel.

A group of invertible channels is a dynamics. Time evolution is the case of the group of real
numbers. A dynamics acts on states by evolving the state backwards in the Heisenberg picture:
the state `φ • ω` assigns to an observable `x` the value `ω (φ⁻¹ x)`.

A channel from one system to another is covariant if it commutes with the dynamics of both. A
measurement that respects a rotation is an example. A covariant channel sends stationary states
to stationary states. A change of description carries a dynamics from one system to another, and
it is the only dynamics for which the change of description is covariant.

## ii. Key results

- `OrderUnitEquiv` : an invertible channel, with its inverse part of the data.
- `OrderUnitEquiv.instMulActionState` : invertible channels act on states.
- `IsIntertwining` : a channel commutes with the dynamics of both systems.
- `IsIntertwining.comap_isInvariant` : a covariant channel sends stationary states to stationary
  states.
- `OrderUnitEquiv.isIntertwining_iff_eq_transport` : a change of description is covariant exactly
  for the transported dynamics.

## iii. Table of contents

- A. Invertible channels
- B. The action on states
- C. Covariant channels
- D. Transport of a dynamics

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

/-!

## A. Invertible channels

-/

/-- An invertible channel from the observables of `E` to those of `F`. It is a linear bijection
that preserves and reflects the order, and it sends the certain outcome to the certain outcome. -/
structure OrderUnitEquiv (E F : Type*) [OrderUnitSpace E] [OrderUnitSpace F]
    extends E ≃ₗ[ℝ] F where
  /-- A possible outcome stays possible, and an impossible one stays impossible. -/
  map_le_map_iff' : ∀ {x y : E}, toLinearEquiv x ≤ toLinearEquiv y ↔ x ≤ y
  /-- The certain outcome stays certain. -/
  map_one' : toLinearEquiv 1 = 1

namespace OrderUnitEquiv

variable {E F G : Type*} [OrderUnitSpace E] [OrderUnitSpace F] [OrderUnitSpace G]

instance : FunLike (OrderUnitEquiv E F) E F where
  coe e := e.toLinearEquiv
  coe_injective e f h := by
    obtain ⟨e, _, _⟩ := e
    obtain ⟨f, _, _⟩ := f
    obtain rfl : e = f := DFunLike.coe_injective h
    rfl

@[ext]
lemma ext {e f : OrderUnitEquiv E F} (h : ∀ x, e x = f x) : e = f := DFunLike.ext _ _ h

/-- Doing nothing. -/
def refl (E : Type*) [OrderUnitSpace E] : OrderUnitEquiv E E where
  toLinearEquiv := .refl ℝ E
  map_le_map_iff' := Iff.rfl
  map_one' := rfl

/-- Undoing an invertible channel. -/
def symm (e : OrderUnitEquiv E F) : OrderUnitEquiv F E where
  toLinearEquiv := e.toLinearEquiv.symm
  map_le_map_iff' {x y} := by
    simpa using (e.map_le_map_iff' (x := e.toLinearEquiv.symm x) (y := e.toLinearEquiv.symm y)).symm
  map_one' := e.toLinearEquiv.symm_apply_eq.2 e.map_one'.symm

/-- Doing `e₁` first and `e₂` second. -/
def trans (e₁ : OrderUnitEquiv E F) (e₂ : OrderUnitEquiv F G) : OrderUnitEquiv E G where
  toLinearEquiv := e₁.toLinearEquiv.trans e₂.toLinearEquiv
  map_le_map_iff' {x y} :=
    (e₂.map_le_map_iff' (x := e₁ x) (y := e₁ y)).trans e₁.map_le_map_iff'
  map_one' := by
    change e₂ (e₁ 1) = 1
    rw [show e₁ 1 = 1 from e₁.map_one', show e₂ 1 = 1 from e₂.map_one']

@[simp] lemma refl_apply (x : E) : refl E x = x := rfl

@[simp] lemma symm_apply_apply (e : OrderUnitEquiv E F) (x : E) : e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x

@[simp] lemma apply_symm_apply (e : OrderUnitEquiv E F) (y : F) : e (e.symm y) = y :=
  e.toLinearEquiv.apply_symm_apply y

@[simp] lemma trans_apply (e₁ : OrderUnitEquiv E F) (e₂ : OrderUnitEquiv F G) (x : E) :
    e₁.trans e₂ x = e₂ (e₁ x) := rfl

/-- The invertible channels of one system form a group. The product `f * g` does `g` first. -/
instance : Group (OrderUnitEquiv E E) where
  mul f g := g.trans f
  one := refl E
  inv := symm
  mul_assoc _ _ _ := by ext; rfl
  one_mul _ := by ext; rfl
  mul_one _ := by ext; rfl
  inv_mul_cancel f := by ext x; exact f.symm_apply_apply x

@[simp] lemma mul_apply (f g : OrderUnitEquiv E E) (x : E) : (f * g) x = f (g x) := rfl

@[simp] lemma one_apply (x : E) : (1 : OrderUnitEquiv E E) x = x := rfl

@[simp] lemma inv_apply (f : OrderUnitEquiv E E) (x : E) : f⁻¹ x = f.symm x := rfl

/-- An invertible channel is a channel. -/
def toChannel (e : OrderUnitEquiv E F) : E →ₚ₁[ℝ] F :=
  .ofLinearMap e.toLinearEquiv.toLinearMap
    (by intro x hx; simpa using (e.map_le_map_iff' (x := 0) (y := x)).2 hx) e.map_one'

@[simp] lemma toChannel_apply (e : OrderUnitEquiv E F) (x : E) : e.toChannel x = e x := rfl

/-!

## B. The action on states

-/

/-- An invertible channel `φ` moves a state `ω` to the state `x ↦ ω (φ⁻¹ x)`. -/
instance instMulActionState : MulAction (OrderUnitEquiv E E) (𝓢[ℝ, E]) where
  smul φ ω := UnitalPositiveLinearMap.comap φ⁻¹.toChannel ω
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl

lemma smul_state_apply (φ : OrderUnitEquiv E E) (ω : 𝓢[ℝ, E]) (x : E) :
    (φ • ω) x = ω (φ.symm x) := rfl

end OrderUnitEquiv

/-!

## C. Covariant channels

-/

section Intertwining

variable {G E F : Type*} [Group G] [OrderUnitSpace E] [OrderUnitSpace F]
  (ρ : G →* OrderUnitEquiv E E) (σ : G →* OrderUnitEquiv F F)

/-- A channel `Φ` from a system with dynamics `ρ` to a system with dynamics `σ` is covariant if
evolving and then applying `Φ` agrees with applying `Φ` and then evolving. -/
def IsIntertwining (Φ : E →ₚ₁[ℝ] F) : Prop := ∀ g x, Φ (ρ g x) = σ g (Φ x)

/-- A state is stationary under a dynamics if the dynamics leaves it unchanged. -/
def IsInvariant (ω : 𝓢[ℝ, E]) : Prop := ∀ g, ρ g • ω = ω

variable {ρ σ}

/-- Doing nothing is covariant. -/
lemma isIntertwining_id : IsIntertwining ρ ρ (.id ℝ E) := by
  intro _ _
  rfl

/-- Covariant channels compose. -/
lemma IsIntertwining.comp {H : Type*} [OrderUnitSpace H] {τ : G →* OrderUnitEquiv H H}
    {Φ : E →ₚ₁[ℝ] F} {Ψ : F →ₚ₁[ℝ] H} (hΦ : IsIntertwining ρ σ Φ)
    (hΨ : IsIntertwining σ τ Ψ) : IsIntertwining ρ τ (Ψ.comp Φ) := by
  intro g x
  simp [hΦ g x, hΨ g (Φ x)]

/-- A covariant channel sends stationary states to stationary states. -/
lemma IsIntertwining.comap_isInvariant {Φ : E →ₚ₁[ℝ] F} (h : IsIntertwining ρ σ Φ)
    {ω : 𝓢[ℝ, F]} (hω : IsInvariant σ ω) :
    IsInvariant ρ (UnitalPositiveLinearMap.comap Φ ω) := by
  intro g
  ext x
  have h1 := h g⁻¹ x
  have h2 := DFunLike.congr_fun (hω g) (Φ x)
  simp only [map_inv, OrderUnitEquiv.inv_apply] at h1
  change ω (Φ ((ρ g).symm x)) = ω (Φ x)
  rw [h1]
  exact h2

end Intertwining

/-!

## D. Transport of a dynamics

-/

namespace OrderUnitEquiv

variable {G E F : Type*} [Group G] [OrderUnitSpace E] [OrderUnitSpace F]

/-- Conjugation by a change of description `e` turns an invertible channel of `E` into one of
`F`. -/
def conj (e : OrderUnitEquiv E F) : OrderUnitEquiv E E →* OrderUnitEquiv F F where
  toFun φ := e.symm.trans (φ.trans e)
  map_one' := by ext y; exact e.apply_symm_apply y
  map_mul' φ ψ := by ext y; simp

/-- The dynamics of `F` that a change of description `e` obtains from the dynamics `ρ` of `E`. -/
def transport (e : OrderUnitEquiv E F) (ρ : G →* OrderUnitEquiv E E) :
    G →* OrderUnitEquiv F F := e.conj.comp ρ

/-- A change of description is covariant for the transported dynamics. -/
lemma isIntertwining_transport (e : OrderUnitEquiv E F) (ρ : G →* OrderUnitEquiv E E) :
    IsIntertwining ρ (e.transport ρ) e.toChannel := by
  intro g x
  simp [transport, conj]

/-- A change of description is covariant for exactly one dynamics of the target, the transported
one. -/
lemma isIntertwining_iff_eq_transport (e : OrderUnitEquiv E F) (ρ : G →* OrderUnitEquiv E E)
    (σ : G →* OrderUnitEquiv F F) :
    IsIntertwining ρ σ e.toChannel ↔ σ = e.transport ρ := by
  constructor
  · intro h
    ext g y
    have := h g (e.symm y)
    simp only [toChannel_apply, apply_symm_apply] at this
    simp [transport, conj, this]
  · rintro rfl
    exact e.isIntertwining_transport ρ

end OrderUnitEquiv

end ProbabilisticTheory
