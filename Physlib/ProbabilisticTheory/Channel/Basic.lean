/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.Basic.NNReal.Defs

/-!
# Positive unital maps

## i. Overview

A channel is a map between the observables of two systems that keeps nonnegative observables
nonnegative and the certain outcome certain. Time evolution, noise, and measurements whose outcomes
are discarded are channels. In quantum theory a physical channel must also be completely positive,
a condition that needs the composite structure of the system and cannot be stated with the
order-unit structure alone.

## ii. Key results

- `UnitalPositiveLinearMap` : a positive linear map preserving `1`, notated `E →ₚ₁[R] F`.
- `PositiveLinearMap` scalar action : positive linear maps can be scaled by nonnegative reals.
- `UnitalPositiveLinearMap.ofLinearMap` : bundle a linear map after checking positivity and
  unitality.
- `UnitalPositiveLinearMap.ofPositiveLinearMap` : bundle a positive linear map after checking
  unitality.
- `UnitalPositiveLinearMap.comp` : composition of positive unital maps.

## iii. Table of contents

- A. Unital positive linear maps
- B. Constructing unital positive linear maps
- C. Scaling positive linear maps
- D. Composition of positive unital maps

## iv. References

-/

@[expose] public section

/-!

## A. Unital positive linear maps

-/

/-- A positive linear map preserving `1`. -/
@[ext]
structure UnitalPositiveLinearMap (R E F : Type*) [Semiring R]
    [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
    [Module R E] [Module R F] [One E] [One F] extends E →ₚ[R] F, OneHom E F

attribute [nolint docBlame] UnitalPositiveLinearMap.toOneHom

/-- Notation for positive unital linear maps. -/
notation:25 E " →ₚ₁[" R:25 "] " F:0 => UnitalPositiveLinearMap R E F

namespace UnitalPositiveLinearMap

variable {R E F : Type*} [Semiring R]
  [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
  [Module R E] [Module R F] [One E] [One F]

instance : FunLike (E →ₚ₁[R] F) E F where
  coe f := f.toFun
  coe_injective _ _ h := UnitalPositiveLinearMap.ext h

instance : LinearMapClass (E →ₚ₁[R] F) R E F where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := map_smul f.toLinearMap

instance : OrderHomClass (E →ₚ₁[R] F) E F where
  map_rel f {_ _} h := f.monotone' h

instance : OneHomClass (E →ₚ₁[R] F) E F where
  map_one f := f.map_one'

instance : Coe (E →ₚ₁[R] F) (E →ₚ[R] F) := ⟨toPositiveLinearMap⟩

@[simp]
lemma toPositiveLinearMap_apply (f : E →ₚ₁[R] F) (x : E) : f.toPositiveLinearMap x = f x := rfl

/-- Unital positive linear maps are determined by their underlying positive linear map. -/
lemma toPositiveLinearMap_injective :
    Function.Injective (toPositiveLinearMap (R := R) (E := E) (F := F)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

/-- Unital positive linear maps are determined by their underlying linear map. -/
lemma toLinearMap_injective : Function.Injective (fun f : E →ₚ₁[R] F => f.toLinearMap) :=
  fun _ _ h ↦ toPositiveLinearMap_injective
    (PositiveLinearMap.toLinearMap_injective h)

end UnitalPositiveLinearMap

namespace UnitalPositiveLinearMap

variable {R E F : Type*} [Semiring R]
  [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E]
  [AddCommGroup F] [PartialOrder F] [IsOrderedAddMonoid F]
  [Module R E] [Module R F] [One E] [One F]

/-!

## B. Constructing unital positive linear maps

-/

/-- Bundle a linear map after proving only positivity and preservation of `1`. -/
def ofLinearMap (f : E →ₗ[R] F) (hpos : ∀ x, 0 ≤ x → 0 ≤ f x) (hone : f 1 = 1) : E →ₚ₁[R] F where
  toPositiveLinearMap := PositiveLinearMap.mk₀ f hpos
  map_one' := hone

/-- Bundle a positive linear map after proving only that it preserves `1`. -/
def ofPositiveLinearMap (f : E →ₚ[R] F) (hone : f 1 = 1) : E →ₚ₁[R] F where
  toPositiveLinearMap := f
  map_one' := hone

omit [IsOrderedAddMonoid E] [IsOrderedAddMonoid F] in
@[simp]
lemma ofPositiveLinearMap_apply (f : E →ₚ[R] F) (hone : f 1 = 1) (x : E) :
    ofPositiveLinearMap f hone x = f x := rfl

end UnitalPositiveLinearMap

/-!

## C. Scaling positive linear maps

Positive linear maps are closed under addition and under scaling by nonnegative reals, but
unital ones are not closed under scaling.

-/

namespace PositiveLinearMap

variable {R E F : Type*} [Semiring R]
  [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
  [Module R E] [Module R F] [Module NNReal F] [SMulCommClass R NNReal F] [PosSMulMono NNReal F]

instance : SMul NNReal (E →ₚ[R] F) where
  smul c f := .mk (c • f.toLinearMap) fun _ _ h ↦ by
    simpa using smul_le_smul_of_nonneg_left (OrderHomClass.mono f h) zero_le

@[simp]
lemma nnreal_smul_apply (c : NNReal) (f : E →ₚ[R] F) (x : E) : (c • f) x = c • f x := rfl

end PositiveLinearMap

namespace UnitalPositiveLinearMap

variable {R E F G : Type*} [Semiring R]
  [AddCommMonoid E] [PartialOrder E] [AddCommMonoid F] [PartialOrder F]
  [AddCommMonoid G] [PartialOrder G] [Module R E] [Module R F] [Module R G]
  [One E] [One F] [One G]

/-! ## D. Composition of positive unital maps -/

variable (R E) in
/-- The identity transformation of an observable system. -/
protected def id : E →ₚ₁[R] E where
  toPositiveLinearMap := .id R E
  map_one' := rfl

@[simp]
lemma id_apply (x : E) : UnitalPositiveLinearMap.id R E x = x := rfl

/-- Compose two positive unital transformations. -/
def comp (g : F →ₚ₁[R] G) (f : E →ₚ₁[R] F) : E →ₚ₁[R] G where
  toPositiveLinearMap := g.toPositiveLinearMap.comp f.toPositiveLinearMap
  map_one' := (congrArg g f.map_one').trans g.map_one'

@[simp]
lemma comp_apply (g : F →ₚ₁[R] G) (f : E →ₚ₁[R] F) (x : E) : g.comp f x = g (f x) := rfl

@[simp]
lemma comp_id (f : E →ₚ₁[R] F) : f.comp (.id R E) = f := rfl

@[simp]
lemma id_comp (f : E →ₚ₁[R] F) : (UnitalPositiveLinearMap.id R F).comp f = f := rfl

lemma comp_assoc {H : Type*} [AddCommMonoid H] [PartialOrder H] [Module R H] [One H]
    (h : G →ₚ₁[R] H) (g : F →ₚ₁[R] G) (f : E →ₚ₁[R] F) :
    h.comp (g.comp f) = (h.comp g).comp f := rfl

end UnitalPositiveLinearMap
