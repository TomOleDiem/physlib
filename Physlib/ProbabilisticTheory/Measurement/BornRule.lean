/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Measurement.Pushforward
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The Born rule

## i. Overview

A measurement is an effect-valued measure `μ : EffectValuedMeasure Ω E`. A state is a channel
`E →ₚ₁[ℝ] ℝ`. Composing the two — scalarizing `μ` by the state — gives an effect-valued measure
into `ℝ`, and a real-valued effect-valued measure is exactly a probability measure: its values lie
in `[0, 1]`, and its order-theoretic countable additivity becomes ordinary countable additivity
once cast through `ENNReal.ofReal`.

This is the operational content of a measurement: a state doesn't just assign a number to each
individual effect, it gets carried by the measurement to a genuine probability distribution over
the outcome space `Ω`. `probabilityLaw` is that distribution — the Born rule, stated at the level
of an arbitrary measurement rather than only a fixed finite set of outcomes.

## ii. Key results

- `EffectValuedMeasure.toProbabilityMeasure`
- `EffectValuedMeasure.probabilityLaw`

## iii. Table of contents

- A. Real-valued effect-valued measures are probability measures
- B. The probability law of a measurement in a state

-/

@[expose] public section

open MeasureTheory

variable {Ω E : Type*} [MeasurableSpace Ω]

namespace EffectValuedMeasure

/-! ## A. Real-valued effect-valued measures are probability measures -/

/-- The value a real-valued effect-valued measure assigns to a countable disjoint union is the
`ENNReal`-sum of the values on the pieces: the order-theoretic least-upper-bound additivity of
`ν` becomes ordinary countable additivity once cast through `ENNReal.ofReal`. -/
lemma toMeasure_countably_additive (ν : EffectValuedMeasure Ω ℝ) ⦃s : ℕ → Set Ω⦄
    (hsm : ∀ n, MeasurableSet (s n)) (hs : ∀ m n, m ≠ n → Disjoint (s m) (s n)) :
    ENNReal.ofReal (ν (⋃ n, s n) (MeasurableSet.iUnion hsm) : ℝ) =
      ∑' n, ENNReal.ofReal (ν (s n) (hsm n) : ℝ) := by
  let a : ℕ → ℝ := fun n => (ν (s n) (hsm n) : ℝ)
  let p : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, a n
  have ha : ∀ n, 0 ≤ a n := fun n => (ν (s n) (hsm n)).2.1
  have hpmono : Monotone p := fun _ _ hNM =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNM)
      (fun i _ _ => ha i)
  have hlub : IsLUB (Set.range p) (ν (⋃ n, s n) (MeasurableSet.iUnion hsm) : ℝ) := by
    simpa [p, a] using ν.countably_additive s hsm hs
  have hreal : Filter.Tendsto p Filter.atTop
      (nhds (ν (⋃ n, s n) (MeasurableSet.iUnion hsm) : ℝ)) :=
    tendsto_atTop_isLUB hpmono hlub
  have henn : Filter.Tendsto (fun N => ENNReal.ofReal (p N)) Filter.atTop
      (nhds (ENNReal.ofReal (ν (⋃ n, s n) (MeasurableSet.iUnion hsm) : ℝ))) :=
    ENNReal.tendsto_ofReal hreal
  have hpartial : (fun N => ENNReal.ofReal (p N)) =
      fun N => ∑ n ∈ Finset.range N, ENNReal.ofReal (a n) := by
    funext N
    exact ENNReal.ofReal_sum_of_nonneg fun i _ => ha i
  rw [hpartial] at henn
  exact tendsto_nhds_unique henn (ENNReal.tendsto_nat_tsum fun n => ENNReal.ofReal (a n))

/-- The ordinary measure represented by a real-valued effect-valued measure. -/
noncomputable def toMeasure (ν : EffectValuedMeasure Ω ℝ) : Measure Ω :=
  Measure.ofMeasurable (fun s hs => ENNReal.ofReal (ν s hs : ℝ)) (by simp)
    (fun _ hsm hs => toMeasure_countably_additive ν hsm hs)

@[simp]
lemma toMeasure_apply (ν : EffectValuedMeasure Ω ℝ) (s : Set Ω) (hs : MeasurableSet s) :
    ν.toMeasure s = ENNReal.ofReal (ν s hs : ℝ) :=
  Measure.ofMeasurable_apply _ hs

/-- Every real-valued effect-valued measure has total mass one. -/
instance (ν : EffectValuedMeasure Ω ℝ) : IsProbabilityMeasure ν.toMeasure where
  measure_univ := by simp [toMeasure_apply]

/-- A real-valued effect-valued measure bundled as an ordinary probability measure. -/
noncomputable def toProbabilityMeasure (ν : EffectValuedMeasure Ω ℝ) : ProbabilityMeasure Ω :=
  ⟨ν.toMeasure, inferInstance⟩

/-! ## B. The probability law of a measurement in a state -/

variable [OrderUnitSpace E]

/-- The probability distribution obtained by measuring `μ` in the normal state `ω`. -/
noncomputable def probabilityLaw (μ : EffectValuedMeasure Ω E) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) :
    ProbabilityMeasure Ω := (μ.scalarize ω hω).toProbabilityMeasure

@[simp]
lemma probabilityLaw_apply (μ : EffectValuedMeasure Ω E) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal)
    (s : Set Ω) (hs : MeasurableSet s) :
    (μ.probabilityLaw ω hω : Measure Ω) s = ENNReal.ofReal (ω (μ s hs : E)) := by
  change (μ.scalarize ω hω).toMeasure s = ENNReal.ofReal (ω (μ s hs : E))
  rw [toMeasure_apply _ s hs, coe_scalarize_apply]

end EffectValuedMeasure
