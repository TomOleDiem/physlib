/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbTheory.Channel.Basic
public import PhyslibAlpha.ProbTheory.OrderUnit.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Normal channels

## i. Overview

A channel is normal when it preserves least upper bounds of increasing sequences. Every channel
preserves finite sums; a normal channel also preserves countable sums of positive elements.

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

/-- A positive linear map is normal when it preserves least upper bounds of increasing
sequences. -/
def IsNormal (φ : E →ₚ[ℝ] F) : Prop :=
  ∀ (f : ℕ → E) (x : E), Monotone f → IsLUB (Set.range f) x → IsLUB (Set.range (φ ∘ f)) (φ x)

lemma isNormal_id : (PositiveLinearMap.id ℝ E).IsNormal := fun _ _ _ h => h

lemma IsNormal.comp {φ : E →ₚ[ℝ] F} {ψ : F →ₚ[ℝ] G} (hφ : φ.IsNormal) (hψ : ψ.IsNormal) :
    (ψ.comp φ).IsNormal := fun f x hf hx =>
  hψ _ _ (φ.monotone'.comp hf) (hφ f x hf hx)

/-- A normal map preserves countable sums of positive elements. -/
lemma IsNormal.isLUB_partialSums {φ : E →ₚ[ℝ] F} (hφ : φ.IsNormal) {f : ℕ → E}
    (hf : ∀ n, 0 ≤ f n) {x : E} (hx : IsLUB (Set.range fun N => ∑ n ∈ Finset.range N, f n) x) :
    IsLUB (Set.range fun N => ∑ n ∈ Finset.range N, φ (f n)) (φ x) := by
  simpa [Function.comp_def, map_sum] using
    hφ _ x ((Finset.sum_mono_set_of_nonneg hf).comp Finset.range_mono) hx

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
