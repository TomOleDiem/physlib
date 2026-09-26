/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Measurement.Pushforward
public import Physlib.ProbabilisticTheory.State.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The Born rule

## i. Overview

A state is a normal channel `ω : E →ₚ₁[ℝ] ℝ`, so it pushes a measurement `μ` on `E` forward to a
measurement `μ.map ω` on `ℝ`. A measurement on `ℝ` is just a probability measure. So a measurement
sends every state to a probability distribution over its outcomes: `μ.probabilityLaw ω`, giving
event `s` probability `ω (μ s)`.

## ii. Key results

- `EffectValuedMeasure.toProbabilityMeasure` : a measurement on `ℝ` is a probability measure.
- `EffectValuedMeasure.probabilityLaw` : the outcome distribution of `μ` in the state `ω`.

## iii. Table of contents

- A. Measurements on `ℝ` are probability measures
- B. The Born rule

-/

@[expose] public section

open MeasureTheory Function

variable {Ω E : Type*} [MeasurableSpace Ω]

namespace EffectValuedMeasure

/-! ## A. Measurements on `ℝ` are probability measures -/

lemma ofReal_iUnion (ν : EffectValuedMeasure Ω ℝ) ⦃s : ℕ → Set Ω⦄ (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (Disjoint on s)) :
    ENNReal.ofReal (ν (⋃ n, s n) (.iUnion hs)) = ∑' n, ENNReal.ofReal (ν (s n) (hs n)) := by
  have h0 n : 0 ≤ (ν (s n) (hs n) : ℝ) := (ν (s n) (hs n)).2.1
  have hsum := (hasSum_iff_tendsto_nat_of_nonneg h0 _).mpr <| tendsto_atTop_isLUB
    ((Finset.sum_mono_set_of_nonneg h0).comp Finset.range_mono) (ν.countably_additive hs hd)
  rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg h0 hsum.summable]

/-- A measurement on `ℝ` as a measure. -/
noncomputable def toMeasure (ν : EffectValuedMeasure Ω ℝ) : Measure Ω :=
  .ofMeasurable (fun s hs => ENNReal.ofReal (ν s hs)) (by simp) ν.ofReal_iUnion

@[simp]
lemma toMeasure_apply (ν : EffectValuedMeasure Ω ℝ) (s : Set Ω) (hs : MeasurableSet s) :
    ν.toMeasure s = ENNReal.ofReal (ν s hs) :=
  Measure.ofMeasurable_apply _ hs

/-- The certain event gets `1`, so a measurement on `ℝ` is a probability measure. -/
instance isProbabilityMeasure_toMeasure (ν : EffectValuedMeasure Ω ℝ) :
    IsProbabilityMeasure ν.toMeasure :=
  ⟨by simp [toMeasure_apply _ _ .univ]⟩

/-- A measurement on `ℝ` as a probability measure. -/
noncomputable def toProbabilityMeasure (ν : EffectValuedMeasure Ω ℝ) : ProbabilityMeasure Ω :=
  ⟨ν.toMeasure, inferInstance⟩

/-! ## B. The Born rule -/

variable [OrderUnitSpace E]

/-- Scalarizing a measurement by a normal state: pushing it forward along the state, a channel
into `ℝ`. -/
def scalarize (μ : EffectValuedMeasure Ω E) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) :
    EffectValuedMeasure Ω ℝ :=
  μ.map ω hω

@[simp]
lemma coe_scalarize_apply (μ : EffectValuedMeasure Ω E) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal)
    (s : Set Ω) (hs : MeasurableSet s) : (μ.scalarize ω hω s hs : ℝ) = ω (μ s hs) := rfl

/-- The outcome distribution of the measurement `μ` in the normal state `ω`. -/
noncomputable def probabilityLaw (μ : EffectValuedMeasure Ω E) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) :
    ProbabilityMeasure Ω :=
  (μ.scalarize ω hω).toProbabilityMeasure

@[simp]
lemma probabilityLaw_apply (μ : EffectValuedMeasure Ω E) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal)
    (s : Set Ω) (hs : MeasurableSet s) :
    (μ.probabilityLaw ω hω : Measure Ω) s = ENNReal.ofReal (ω (μ s hs)) :=
  toMeasure_apply _ s hs

end EffectValuedMeasure
