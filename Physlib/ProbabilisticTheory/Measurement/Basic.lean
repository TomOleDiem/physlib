/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Defs
public import Physlib.ProbabilisticTheory.Effect.Complement

/-!
# Effect-valued measures

## i. Overview

The most general notion of measurement: an assignment of an effect to each measurable subset of
an outcome space `Ω`, with the impossible event `∅` given no weight, the certain event `univ`
given full weight, and countable additivity — the partial sums of a pairwise disjoint countable
family of events have least upper bound the effect of their union. Sums are computed in `E`, since
`Effect E` is not itself closed under addition.

Once `E` is the self-adjoint part of an operator algebra, this is exactly what the physics
literature calls a POVM (positive operator-valued measure). Nothing here is an operator, though:
all that's needed is `Effect E` on an order-unit space, which is why the name doesn't mention
operators.

## ii. Key results

- `EffectValuedMeasure Ω E` : an effect-valued measure on `Ω`.

## iii. Table of contents

- A. Effect-valued measures
- B. Basic API

-/

@[expose] public section

variable {Ω E : Type*} [MeasurableSpace Ω] [OrderUnitSpace E]

/-! ## A. Effect-valued measures -/

/-- An effect-valued measure: `∅ ↦ 0`, `univ ↦ 1`, countably additive up to least upper bound. -/
structure EffectValuedMeasure (Ω : Type*) [MeasurableSpace Ω] (E : Type*) [OrderUnitSpace E] where
  /-- The underlying assignment of outcomes to effects. -/
  toFun : ∀ s : Set Ω, MeasurableSet s → Effect E
  /-- The impossible outcome gets no weight. -/
  map_empty' : toFun ∅ MeasurableSet.empty = 0
  /-- The certain outcome gets full weight. -/
  map_univ' : toFun Set.univ MeasurableSet.univ = 1
  /-- The partial sums of a pairwise disjoint countable family have least upper bound the effect
  of their union. -/
  countably_additive' : ∀ s : ℕ → Set Ω, ∀ hsm : ∀ n, MeasurableSet (s n),
    ∀ _hs : ∀ m n, m ≠ n → Disjoint (s m) (s n),
      IsLUB (Set.range fun N : ℕ => ∑ n ∈ Finset.range N, (toFun (s n) (hsm n) : E))
        (toFun (⋃ n, s n) (MeasurableSet.iUnion hsm) : E)

namespace EffectValuedMeasure

/-! ## B. Basic API -/

instance : CoeFun (EffectValuedMeasure Ω E) fun _ => ∀ s : Set Ω, MeasurableSet s → Effect E where
  coe m := m.toFun

@[ext]
lemma ext {μ ν : EffectValuedMeasure Ω E} (h : ∀ s hs, μ s hs = ν s hs) : μ = ν := by
  cases μ
  cases ν
  simp_all only [EffectValuedMeasure.mk.injEq]
  funext s hs
  exact h s hs

@[simp]
lemma map_empty (μ : EffectValuedMeasure Ω E) : μ ∅ MeasurableSet.empty = 0 := μ.map_empty'

@[simp]
lemma map_univ (μ : EffectValuedMeasure Ω E) : μ Set.univ MeasurableSet.univ = 1 := μ.map_univ'

lemma countably_additive (μ : EffectValuedMeasure Ω E) (s : ℕ → Set Ω)
    (hsm : ∀ n, MeasurableSet (s n)) (hs : ∀ m n, m ≠ n → Disjoint (s m) (s n)) :
    IsLUB (Set.range fun N : ℕ => ∑ n ∈ Finset.range N, (μ (s n) (hsm n) : E))
      (μ (⋃ n, s n) (MeasurableSet.iUnion hsm) : E) :=
  μ.countably_additive' s hsm hs

end EffectValuedMeasure
