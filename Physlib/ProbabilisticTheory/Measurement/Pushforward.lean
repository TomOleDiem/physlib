/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Channel.Normal
public import Physlib.ProbabilisticTheory.Measurement.Basic

/-!
# Pushing a measurement forward along a channel

## i. Overview

A channel sends effects to effects. Applying a normal channel `φ : E →ₚ₁[ℝ] F` to every effect of
a measurement `μ` on `E` therefore gives a measurement `μ.map φ` on `F`, with the same outcomes.

## ii. Key results

- `EffectValuedMeasure.map` : pushing a measurement forward along a normal channel.

## iii. Table of contents

- A. Channels send effects to effects
- B. Pushing a measurement forward

-/

@[expose] public section

variable {Ω E F : Type*} [MeasurableSpace Ω] [OrderUnitSpace E] [OrderUnitSpace F]

/-! ## A. Channels send effects to effects -/

namespace UnitalPositiveLinearMap

/-- A channel sends effects to effects. -/
def mapEffect (φ : E →ₚ₁[ℝ] F) (e : Effect E) : Effect F :=
  ⟨φ e, φ.map_nonneg e.2.1, (φ.monotone' e.2.2).trans_eq (map_one φ)⟩

@[simp]
lemma coe_mapEffect (φ : E →ₚ₁[ℝ] F) (e : Effect E) : (φ.mapEffect e : F) = φ e := rfl

@[simp]
lemma mapEffect_zero (φ : E →ₚ₁[ℝ] F) : φ.mapEffect 0 = 0 := Subtype.ext (map_zero φ)

@[simp]
lemma mapEffect_one (φ : E →ₚ₁[ℝ] F) : φ.mapEffect 1 = 1 := Subtype.ext (map_one φ)

end UnitalPositiveLinearMap

/-! ## B. Pushing a measurement forward -/

namespace EffectValuedMeasure

/-- Pushing a measurement forward along a normal channel. -/
def map (μ : EffectValuedMeasure Ω E) (φ : E →ₚ₁[ℝ] F) (hφ : φ.IsNormal) :
    EffectValuedMeasure Ω F where
  toFun s hs := φ.mapEffect (μ s hs)
  map_empty' := by simp
  map_univ' := by simp
  countably_additive' _ hs hd := hφ.isLUB_partialSums (fun n => (μ _ (hs n)).2.1)
    (μ.countably_additive hs hd)

@[simp]
lemma coe_map_apply (μ : EffectValuedMeasure Ω E) (φ : E →ₚ₁[ℝ] F) (hφ : φ.IsNormal)
    (s : Set Ω) (hs : MeasurableSet s) : (μ.map φ hφ s hs : F) = φ (μ s hs) := rfl

end EffectValuedMeasure
