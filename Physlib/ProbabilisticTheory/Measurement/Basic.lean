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

A measurement with outcomes in `Ω` assigns to each event — a measurable set of outcomes — the
effect testing whether the outcome lands in it. The impossible event gets `0`, the certain event
gets `1`, and the effects of disjoint events add up, countably. This is the most general notion of
measurement: for self-adjoint operators it is exactly a POVM.

Since `Effect E` isn't closed under addition, sums are taken in `E`, and countable additivity says
the partial sums have the effect of the union as their least upper bound.

## ii. Key results

- `EffectValuedMeasure Ω E` : a measurement with outcomes in `Ω`.

## iii. Table of contents

- A. Effect-valued measures

-/

@[expose] public section

open Function

variable {Ω E : Type*} [MeasurableSpace Ω] [OrderUnitSpace E]

/-! ## A. Effect-valued measures -/

/-- An effect-valued measure: `∅ ↦ 0`, `univ ↦ 1`, countably additive. -/
structure EffectValuedMeasure (Ω : Type*) [MeasurableSpace Ω] (E : Type*) [OrderUnitSpace E] where
  /-- The effect assigned to each event. -/
  toFun : ∀ s : Set Ω, MeasurableSet s → Effect E
  /-- The impossible event gets `0`. -/
  map_empty' : toFun ∅ .empty = 0
  /-- The certain event gets `1`. -/
  map_univ' : toFun .univ .univ = 1
  /-- The effects of countably many disjoint events add up to the effect of their union. -/
  countably_additive' : ∀ (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n)),
    Pairwise (Disjoint on s) →
      IsLUB (Set.range fun N => ∑ n ∈ Finset.range N, (toFun (s n) (hs n) : E))
        (toFun (⋃ n, s n) (.iUnion hs) : E)

namespace EffectValuedMeasure

instance : CoeFun (EffectValuedMeasure Ω E) fun _ => ∀ s : Set Ω, MeasurableSet s → Effect E where
  coe μ := μ.toFun

@[ext]
lemma ext {μ ν : EffectValuedMeasure Ω E} (h : ∀ s hs, μ s hs = ν s hs) : μ = ν := by
  cases μ; cases ν; congr; exact funext fun s => funext (h s)

@[simp]
lemma map_empty (μ : EffectValuedMeasure Ω E) : μ ∅ .empty = 0 := μ.map_empty'

@[simp]
lemma map_univ (μ : EffectValuedMeasure Ω E) : μ .univ .univ = 1 := μ.map_univ'

lemma countably_additive (μ : EffectValuedMeasure Ω E) {s : ℕ → Set Ω}
    (hs : ∀ n, MeasurableSet (s n)) (hd : Pairwise (Disjoint on s)) :
    IsLUB (Set.range fun N => ∑ n ∈ Finset.range N, (μ (s n) (hs n) : E))
      (μ (⋃ n, s n) (.iUnion hs) : E) :=
  μ.countably_additive' s hs hd

end EffectValuedMeasure
