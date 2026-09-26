/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Channel.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Normal channels

## i. Overview

A channel is normal when it preserves suprema of directed sets. Every channel preserves finite
sums; a normal channel also preserves countable sums of positive elements.

## ii. Key results

- `UnitalPositiveLinearMap.IsNormal`
- `PositiveLinearMap.IsNormal.isLUB_partialSums` : a normal map preserves countable sums of
  positive elements.

## iii. Table of contents

- A. Normal positive maps
- B. Normal channels

-/

@[expose] public section

variable {E F G : Type*} [OrderUnitSpace E] [OrderUnitSpace F] [OrderUnitSpace G]

namespace PositiveLinearMap

/-! ## A. Normal positive maps -/

/-- A positive linear map is normal when it preserves suprema of directed sets. -/
def IsNormal (φ : E →ₚ[ℝ] F) : Prop :=
  ∀ (D : Set E) (x : E), D.Nonempty → DirectedOn (· ≤ ·) D → IsLUB D x → IsLUB (φ '' D) (φ x)

lemma isNormal_id : (PositiveLinearMap.id ℝ E).IsNormal := fun _ _ _ _ h => by simpa using h

lemma IsNormal.comp {φ : E →ₚ[ℝ] F} {ψ : F →ₚ[ℝ] G} (hφ : φ.IsNormal) (hψ : ψ.IsNormal) :
    (ψ.comp φ).IsNormal := fun D x hD hdir hlub => by
  simpa [Set.image_image] using
    hψ _ _ (hD.image φ) (hdir.mono_comp fun _ _ h => φ.monotone' h) (hφ D x hD hdir hlub)

/-- A normal map preserves countable sums of positive elements. -/
lemma IsNormal.isLUB_partialSums {φ : E →ₚ[ℝ] F} (hφ : φ.IsNormal) {f : ℕ → E}
    (hf : ∀ n, 0 ≤ f n) {x : E} (hx : IsLUB (Set.range fun N => ∑ n ∈ Finset.range N, f n) x) :
    IsLUB (Set.range fun N => ∑ n ∈ Finset.range N, φ (f n)) (φ x) := by
  simpa [← Set.range_comp, Function.comp_def, map_sum] using hφ _ x (Set.range_nonempty _)
    ((Finset.sum_mono_set_of_nonneg hf).comp Finset.range_mono).directed_le.directedOn_range hx

end PositiveLinearMap

namespace UnitalPositiveLinearMap

/-! ## B. Normal channels -/

/-- A channel is normal when its underlying positive linear map is. -/
abbrev IsNormal (φ : E →ₚ₁[ℝ] F) : Prop := φ.toPositiveLinearMap.IsNormal

lemma isNormal_id : (UnitalPositiveLinearMap.id ℝ E).IsNormal := PositiveLinearMap.isNormal_id

lemma IsNormal.comp {φ : E →ₚ₁[ℝ] F} {ψ : F →ₚ₁[ℝ] G} (hφ : φ.IsNormal) (hψ : ψ.IsNormal) :
    (ψ.comp φ).IsNormal :=
  PositiveLinearMap.IsNormal.comp hφ hψ

end UnitalPositiveLinearMap
