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
# Pushing a measurement forward along a normal channel

## i. Overview

A measurement doesn't have to stay put: composing each of its effects with a further channel
gives another measurement, now valued in the channel's target space. That's `map` — pushing an
`EffectValuedMeasure Ω E` forward along `E →ₚ₁[ℝ] F` — and it needs the channel to be normal, not
just positive, so that countable additivity survives the composition.

The special case `F = ℝ`, scalarizing by a normal state, turns a measurement into the ordinary
probability distribution a state assigns to its outcomes: the abstract Born rule, evaluated event
by event rather than only outcome by outcome.

## ii. Key results

- `EffectValuedMeasure.map`
- `EffectValuedMeasure.scalarize`

## iii. Table of contents

- A. Pushing forward along a normal channel
- B. Scalarizing by a normal state

-/

@[expose] public section

variable {Ω E F : Type*} [MeasurableSpace Ω] [OrderUnitSpace E] [OrderUnitSpace F]

namespace EffectValuedMeasure

/-! ## A. Pushing forward along a normal channel -/

/-- Nonnegative partial sums are monotone in how many terms are included: adding more nonnegative
terms never decreases the sum. -/
lemma monotone_partialSums {f : ℕ → E} (hf : ∀ n, 0 ≤ f n) :
    Monotone (fun N => ∑ n ∈ Finset.range N, f n) := fun _ _ hNM =>
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNM) fun i _ _ => hf i

/-- The effect assigned to `s` by pushing `μ` forward along `φ`: `φ` composed with `μ`. -/
def mapToFun (μ : EffectValuedMeasure Ω E) (φ : E →ₚ₁[ℝ] F) (s : Set Ω) (hs : MeasurableSet s) :
    Effect F :=
  ⟨φ (μ s hs : E), φ.map_nonneg (μ s hs).2.1, (φ.monotone' (μ s hs).2.2).trans_eq (map_one φ)⟩

@[simp]
lemma coe_mapToFun (μ : EffectValuedMeasure Ω E) (φ : E →ₚ₁[ℝ] F) (s : Set Ω)
    (hs : MeasurableSet s) : (mapToFun μ φ s hs : F) = φ (μ s hs : E) := rfl

lemma mapToFun_empty (μ : EffectValuedMeasure Ω E) (φ : E →ₚ₁[ℝ] F) :
    mapToFun μ φ ∅ MeasurableSet.empty = 0 := by
  refine Subtype.ext ?_
  show φ (μ ∅ MeasurableSet.empty : E) = 0
  rw [μ.map_empty]; exact map_zero φ

lemma mapToFun_univ (μ : EffectValuedMeasure Ω E) (φ : E →ₚ₁[ℝ] F) :
    mapToFun μ φ Set.univ MeasurableSet.univ = 1 := by
  refine Subtype.ext ?_
  show φ (μ Set.univ MeasurableSet.univ : E) = 1
  rw [μ.map_univ]; exact map_one φ

/-- The pushed-forward assignment stays countably additive: `φ`'s normality carries the least
upper bound in `E` through to the least upper bound of the pushed-forward partial sums in `F`. -/
lemma mapToFun_isLUB (μ : EffectValuedMeasure Ω E) (φ : E →ₚ₁[ℝ] F) (hφ : φ.IsNormal)
    (s : ℕ → Set Ω) (hsm : ∀ n, MeasurableSet (s n))
    (hs' : ∀ m n, m ≠ n → Disjoint (s m) (s n)) :
    IsLUB (Set.range fun N : ℕ => ∑ n ∈ Finset.range N, (mapToFun μ φ (s n) (hsm n) : F))
      (mapToFun μ φ (⋃ n, s n) (MeasurableSet.iUnion hsm) : F) := by
  set D : Set E := Set.range fun N => ∑ n ∈ Finset.range N, (μ (s n) (hsm n) : E)
  have hlub : IsLUB D (μ (⋃ n, s n) (MeasurableSet.iUnion hsm) : E) :=
    μ.countably_additive s hsm hs'
  have hdirected : DirectedOn (· ≤ ·) D :=
    (monotone_partialSums fun n => (μ (s n) (hsm n)).2.1).directed_le.directedOn_range
  have hnonempty : D.Nonempty := ⟨_, 0, rfl⟩
  have hpush := hφ D _ hnonempty hdirected hlub
  change IsLUB (φ '' D) (φ (μ (⋃ n, s n) (MeasurableSet.iUnion hsm) : E)) at hpush
  rwa [show φ '' D = Set.range fun N => ∑ n ∈ Finset.range N, φ (μ (s n) (hsm n) : E) from
    (Set.range_comp _ _).symm.trans (congrArg Set.range
      (funext fun N => map_sum φ _ (Finset.range N)))] at hpush

/-- Pushing an effect-valued measure forward along a normal channel: composing each assigned
effect with the channel. -/
noncomputable def map (μ : EffectValuedMeasure Ω E) (φ : E →ₚ₁[ℝ] F) (hφ : φ.IsNormal) :
    EffectValuedMeasure Ω F where
  toFun := mapToFun μ φ
  map_empty' := mapToFun_empty μ φ
  map_univ' := mapToFun_univ μ φ
  countably_additive' := mapToFun_isLUB μ φ hφ

@[simp]
lemma coe_map_apply (μ : EffectValuedMeasure Ω E) (φ : E →ₚ₁[ℝ] F) (hφ : φ.IsNormal)
    (s : Set Ω) (hs : MeasurableSet s) :
    ((μ.map φ hφ) s hs : F) = φ (μ s hs : E) := rfl

/-! ## B. Scalarizing by a normal state -/

/-- Scalarizing an effect-valued measure by a normal state gives its ordinary real-valued
probability law, represented as an effect-valued measure in the classical order-unit space `ℝ`.
For each measurable event this is precisely the abstract Born rule `ω(μ(s))`. -/
noncomputable def scalarize (μ : EffectValuedMeasure Ω E) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal) :
    EffectValuedMeasure Ω ℝ := μ.map ω hω

@[simp]
lemma coe_scalarize_apply (μ : EffectValuedMeasure Ω E) (ω : 𝓢[ℝ, E]) (hω : ω.IsNormal)
    (s : Set Ω) (hs : MeasurableSet s) :
    ((μ.scalarize ω hω) s hs : ℝ) = ω (μ s hs : E) := rfl

end EffectValuedMeasure
