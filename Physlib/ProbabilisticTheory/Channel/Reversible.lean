/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Physlib.ProbabilisticTheory.State.Basic

/-!
# Reversible transformations of observables

Reversible transformations of observable spaces, their group structure and their action on states.

## i. Overview

Recall that a channel is a unital positive linear map between observable spaces: it sends
observables to observables and keeps the certain outcome certain. Here we single out the channels
that can be undone.

A reversible transformation is a channel that is a linear bijection whose inverse is again a
channel, that is, a unital linear order isomorphism of observable spaces. These form a group under
composition, and they act on states through the inverse transformation. A group representation by
reversible transformations describes symmetries or reversible dynamics. For example, time evolution
is represented by the additive group of real numbers.

## ii. Key results

- `Reversible`: Reversible transformations, i.e. unital linear order isomorphisms of
  observable spaces.
- `Reversible.toChannelHom`: Reversible transformations embed in the monoid of channels.
- `Reversible.instMulActionState`: The induced action on states.

## iii. Table of contents

- A. Reversible transformations
  - A.1. Definition
  - A.2. Group structure
  - A.3. As channels
- B. Action on states

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. Reversible transformations -/

/-! ### A.1. Definition -/

/-- A reversible transformation between observable spaces: a linear bijection that preserves and
reflects the order and preserves the order unit. Both it and its inverse are channels. -/
structure Reversible (E F : Type*) [OrderUnitSpace E] [OrderUnitSpace F]
    extends E ≃ₗ[ℝ] F where
  /-- The equivalence preserves and reflects the order. -/
  map_le_map_iff' : ∀ {x y : E}, toLinearEquiv x ≤ toLinearEquiv y ↔ x ≤ y
  /-- The order unit is preserved. -/
  map_one' : toLinearEquiv 1 = 1

namespace Reversible

variable {E F G : Type*} [OrderUnitSpace E] [OrderUnitSpace F] [OrderUnitSpace G]

instance : FunLike (Reversible E F) E F where
  coe e := e.toLinearEquiv
  coe_injective e f h := by
    obtain ⟨e, _, _⟩ := e
    obtain ⟨f, _, _⟩ := f
    obtain rfl : e = f := DFunLike.coe_injective h
    rfl

@[ext]
lemma ext {e f : Reversible E F} (h : ∀ x, e x = f x) : e = f := DFunLike.ext _ _ h

/-! ### A.2. Group structure -/

/-- The identity reversible transformation. -/
def refl (E : Type*) [OrderUnitSpace E] : Reversible E E where
  toLinearEquiv := .refl ℝ E
  map_le_map_iff' := Iff.rfl
  map_one' := rfl

/-- The inverse of a reversible transformation. -/
def symm (e : Reversible E F) : Reversible F E where
  toLinearEquiv := e.toLinearEquiv.symm
  map_le_map_iff' {x y} := by
    simpa using (e.map_le_map_iff' (x := e.toLinearEquiv.symm x) (y := e.toLinearEquiv.symm y)).symm
  map_one' := e.toLinearEquiv.symm_apply_eq.2 e.map_one'.symm

/-- Composition of reversible transformations, applying `e₁` before `e₂`. -/
def trans (e₁ : Reversible E F) (e₂ : Reversible F G) : Reversible E G where
  toLinearEquiv := e₁.toLinearEquiv.trans e₂.toLinearEquiv
  map_le_map_iff' {x y} :=
    (e₂.map_le_map_iff' (x := e₁ x) (y := e₁ y)).trans e₁.map_le_map_iff'
  map_one' := by
    change e₂ (e₁ 1) = 1
    rw [show e₁ 1 = 1 from e₁.map_one', show e₂ 1 = 1 from e₂.map_one']

@[simp] lemma refl_apply (x : E) : refl E x = x := rfl

@[simp] lemma symm_apply_apply (e : Reversible E F) (x : E) : e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply x

@[simp] lemma apply_symm_apply (e : Reversible E F) (y : F) : e (e.symm y) = y :=
  e.toLinearEquiv.apply_symm_apply y

@[simp] lemma trans_apply (e₁ : Reversible E F) (e₂ : Reversible F G) (x : E) :
    e₁.trans e₂ x = e₂ (e₁ x) := rfl

/-- Reversible transformations of a single space form a group under composition. -/
instance automorphismGroup : Group (Reversible E E) where
  mul f g := g.trans f
  one := refl E
  inv := symm
  mul_assoc _ _ _ := by ext; rfl
  one_mul _ := by ext; rfl
  mul_one _ := by ext; rfl
  inv_mul_cancel f := by ext x; exact f.symm_apply_apply x

@[simp] lemma mul_apply (f g : Reversible E E) (x : E) : (f * g) x = f (g x) := rfl

@[simp] lemma one_apply (x : E) : (1 : Reversible E E) x = x := rfl

@[simp] lemma inv_apply (f : Reversible E E) (x : E) : f⁻¹ x = f.symm x := rfl

/-! ### A.3. As channels -/

/-- A reversible transformation regarded as a channel. -/
def toChannel (e : Reversible E F) : E →ₚ₁[ℝ] F :=
  .ofLinearMap e.toLinearEquiv.toLinearMap
    (by intro x hx; simpa using (e.map_le_map_iff' (x := 0) (y := x)).2 hx) e.map_one'

@[simp] lemma toChannel_apply (e : Reversible E F) (x : E) : e.toChannel x = e x := rfl

end Reversible

namespace Reversible

variable {E : Type*} [OrderUnitSpace E]

/-- Regarding reversible transformations as channels is a homomorphism of monoids. -/
def toChannelHom : Reversible E E →* (E →ₚ₁[ℝ] E) where
  toFun := toChannel
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma toChannelHom_apply (e : Reversible E E) (x : E) : toChannelHom e x = e x := rfl

/-! ## B. Action on states -/

/-- The action on states induced by the inverse of a reversible transformation. -/
instance instMulActionState : MulAction (Reversible E E) (𝓢[ℝ, E]) where
  smul φ ω := UnitalPositiveLinearMap.comap (toChannelHom φ⁻¹) ω
  one_smul _ := by ext; rfl
  mul_smul _ _ _ := by ext; rfl

lemma smul_state_apply (φ : Reversible E E) (ω : 𝓢[ℝ, E]) (x : E) :
    (φ • ω) x = ω (φ.symm x) := rfl

end Reversible

end ProbabilisticTheory
