/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Channel.Normal
public import Physlib.ProbabilisticTheory.Measurement.Basic
public import Physlib.ProbabilisticTheory.State.Basic

/-!
# Measurable-outcome measurements, pushed forward along a normal channel

## i. Overview

An `EffectValuedMeasure Ω C` is already a measurable-outcome measurement with classical output
`C`: countable additivity is the trace, on indicator functions, of the order-continuity a genuine
channel out of bounded measurable functions on `Ω` would have. This file pushes such a measure
forward along a further, genuinely normal channel `C →ₚ₁[ℝ] E`: it stays an effect-valued measure,
because the channel is linear (so it commutes with finite partial sums) and normal (so it commutes
with their supremum).

Scalarizing by a normal state — the special case `E = ℝ` — turns the measure into an ordinary
real-valued one, the abstract Born rule applied event by event.

## ii. Key results

- `EffectValuedMeasure.map`
- `EffectValuedMeasure.scalarize`

## iii. Table of contents

- A. Pushing forward along a normal channel
- B. Scalarizing by a normal state

-/

@[expose] public section

variable {Ω C E : Type*} [MeasurableSpace Ω] [OrderUnitSpace C] [OrderUnitSpace E]

namespace EffectValuedMeasure

/-! ## A. Pushing forward along a normal channel -/

/-- Nonnegative partial sums are monotone in how many terms are included: adding more nonnegative
terms never decreases the sum. -/
lemma monotone_partialSums {f : ℕ → C} (hf : ∀ n, 0 ≤ f n) :
    Monotone (fun N => ∑ n ∈ Finset.range N, f n) := fun _ _ hNM =>
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNM) fun i _ _ => hf i

/-- The effect assigned to `s` by pushing `μ` forward along `φ`: `φ` composed with `μ`. -/
def mapToFun (μ : EffectValuedMeasure Ω C) (φ : C →ₚ₁[ℝ] E) (s : Set Ω) (hs : MeasurableSet s) :
    Effect E :=
  ⟨φ (μ s hs : C), φ.map_nonneg (μ s hs).2.1, (φ.monotone' (μ s hs).2.2).trans_eq (map_one φ)⟩

@[simp]
lemma coe_mapToFun (μ : EffectValuedMeasure Ω C) (φ : C →ₚ₁[ℝ] E) (s : Set Ω)
    (hs : MeasurableSet s) : (mapToFun μ φ s hs : E) = φ (μ s hs : C) := rfl

lemma mapToFun_empty (μ : EffectValuedMeasure Ω C) (φ : C →ₚ₁[ℝ] E) :
    mapToFun μ φ ∅ MeasurableSet.empty = 0 := by
  refine Subtype.ext ?_
  show φ (μ ∅ MeasurableSet.empty : C) = 0
  rw [μ.map_empty]; exact map_zero φ

lemma mapToFun_univ (μ : EffectValuedMeasure Ω C) (φ : C →ₚ₁[ℝ] E) :
    mapToFun μ φ Set.univ MeasurableSet.univ = 1 := by
  refine Subtype.ext ?_
  show φ (μ Set.univ MeasurableSet.univ : C) = 1
  rw [μ.map_univ]; exact map_one φ

lemma mapToFun_countably_additive (μ : EffectValuedMeasure Ω C) (φ : C →ₚ₁[ℝ] E)
    (hφ : φ.IsNormal) (s : ℕ → Set Ω) (hsm : ∀ n, MeasurableSet (s n))
    (hs' : ∀ m n, m ≠ n → Disjoint (s m) (s n)) :
    IsLUB (Set.range fun N : ℕ => ∑ n ∈ Finset.range N, (mapToFun μ φ (s n) (hsm n) : E))
      (mapToFun μ φ (⋃ n, s n) (MeasurableSet.iUnion hsm) : E) := by
  set D : Set C := Set.range fun N => ∑ n ∈ Finset.range N, (μ (s n) (hsm n) : C) with hD
  have hmono : Monotone (fun N => ∑ n ∈ Finset.range N, (μ (s n) (hsm n) : C)) :=
    monotone_partialSums fun n => (μ (s n) (hsm n)).2.1
  have hdirected : DirectedOn (· ≤ ·) D := hmono.directed_le.directedOn_range
  have hnonempty : D.Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hlub : IsLUB D (μ (⋃ n, s n) (MeasurableSet.iUnion hsm) : C) :=
    μ.countably_additive s hsm hs'
  have hpush := hφ D _ hnonempty hdirected hlub
  change IsLUB (φ '' D) (φ (μ (⋃ n, s n) (MeasurableSet.iUnion hsm) : C)) at hpush
  have himage : φ '' D =
      Set.range fun N => ∑ n ∈ Finset.range N, φ (μ (s n) (hsm n) : C) := by
    rw [hD, ← Set.range_comp]
    congr 1
    funext N
    exact map_sum φ (fun n => (μ (s n) (hsm n) : C)) (Finset.range N)
  rwa [himage] at hpush

/-- Pushing an effect-valued measure forward along a normal channel: composing each assigned
effect with the channel. -/
noncomputable def map (μ : EffectValuedMeasure Ω C) (φ : C →ₚ₁[ℝ] E) (hφ : φ.IsNormal) :
    EffectValuedMeasure Ω E where
  toFun := mapToFun μ φ
  map_empty' := mapToFun_empty μ φ
  map_univ' := mapToFun_univ μ φ
  countably_additive' := mapToFun_countably_additive μ φ hφ

@[simp]
lemma coe_map_apply (μ : EffectValuedMeasure Ω C) (φ : C →ₚ₁[ℝ] E) (hφ : φ.IsNormal)
    (s : Set Ω) (hs : MeasurableSet s) :
    ((μ.map φ hφ) s hs : E) = φ (μ s hs : C) := rfl

/-! ## B. Scalarizing by a normal state -/

/-- Scalarizing an effect-valued measure by a normal state gives its ordinary real-valued
probability law, represented as an effect-valued measure in the classical order-unit space `ℝ`.
For each measurable event this is precisely the abstract Born rule `ω(μ(s))`. -/
noncomputable def scalarize (μ : EffectValuedMeasure Ω C) (ω : 𝓢[ℝ, C]) (hω : ω.IsNormal) :
    EffectValuedMeasure Ω ℝ := μ.map ω hω

@[simp]
lemma coe_scalarize_apply (μ : EffectValuedMeasure Ω C) (ω : 𝓢[ℝ, C]) (hω : ω.IsNormal)
    (s : Set Ω) (hs : MeasurableSet s) :
    ((μ.scalarize ω hω) s hs : ℝ) = ω (μ s hs : C) := rfl

end EffectValuedMeasure
