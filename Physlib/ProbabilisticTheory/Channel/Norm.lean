/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Separation

/-!
# Channels do not increase the norm

Every channel is a continuous linear map for the order-unit norms.

## i. Overview

A channel cannot make an observable larger than the certain outcome allows. A state of the output
pulls back to a state of the input, and states bound the order-unit norm. So the norm of the image
is at most the norm of the observable.

## ii. Key results

- `UnitalPositiveLinearMap.norm_apply_le` : a channel does not increase the norm.
- `UnitalPositiveLinearMap.toContinuousLinearMap` : a channel as a continuous linear map.

## iii. Table of contents

- A. The norm bound and continuity

## iv. References

* None.

-/

@[expose] public section

open ProbabilisticTheory ArchimedeanOrderUnitSpace
open scoped ArchimedeanOrderUnitSpace

/-! ## A. The norm bound and continuity -/

namespace UnitalPositiveLinearMap

variable {E F : Type*} [ArchimedeanOrderUnitSpace E] [ArchimedeanOrderUnitSpace F]

/-- A channel does not increase the order-unit norm. A state of the output pulls back to a state of
the input, and states bound the norm. -/
lemma orderUnitNorm_apply_le (T : E →ₚ₁[ℝ] F) (x : E) :
    orderUnitNorm (T x) ≤ orderUnitNorm x := by
  rcases subsingleton_or_nontrivial F with h | h
  · rw [Subsingleton.elim (T x) 0, orderUnitNorm_zero]
    exact orderUnitNorm_nonneg x
  · refine (orderUnitNorm_le_iff_forall_abs_apply_le _ _).2 ?_
    intro ω
    exact abs_apply_le_orderUnitNorm (comap T ω) x

lemma norm_apply_le (T : E →ₚ₁[ℝ] F) (x : E) : ‖T x‖ ≤ ‖x‖ := T.orderUnitNorm_apply_le x

/-- A channel as a continuous linear map for the order-unit norms. -/
noncomputable def toContinuousLinearMap (T : E →ₚ₁[ℝ] F) : E →L[ℝ] F :=
  LinearMap.mkContinuous T.toLinearMap 1 (by simpa using T.norm_apply_le)

@[simp] lemma toContinuousLinearMap_apply (T : E →ₚ₁[ℝ] F) (x : E) :
    T.toContinuousLinearMap x = T x := rfl

end UnitalPositiveLinearMap
