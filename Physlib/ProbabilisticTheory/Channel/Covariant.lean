/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Channel.Reversible

/-!
# Covariant channels

Invariant states and channels that commute with two group actions by reversible transformations.

## i. Overview

A group representation by reversible transformations acts on states. A state is invariant if it is
fixed by this action. For time evolution these are the stationary states.

On a channel between two spaces that each carry such a group action, we want to say that it
respects the symmetry: applying the group element before or after the channel gives the same
result. Such a channel is called covariant, or intertwining. Covariance preserves invariant states
under pullback. A reversible transformation also transports a group action between observable
spaces, giving the unique action for which the transformation is covariant.

## ii. Key results

- `IsInvariant`: A state fixed by every transformation of a group action.
- `IsIntertwining`: Covariance of a channel under two group actions.
- `IsIntertwining.comap_isInvariant`: Pullback of invariant states along covariant channels.
- `Reversible.transport`: Transport of a group action along a reversible transformation.
- `Reversible.isIntertwining_iff_eq_transport`: Characterization of the transported action.

## iii. Table of contents

- A. Invariant states
- B. Covariant channels
  - B.1. Definition and closure properties
  - B.2. Invariant states
- C. Transport of group actions
  - C.1. Conjugation
  - C.2. Transported actions

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

/-! ## A. Invariant states -/

variable {G E F : Type*} [Group G] [OrderUnitSpace E] [OrderUnitSpace F]
  (ρ : G →* Reversible E E) (σ : G →* Reversible F F)

/-- A state is invariant if it is fixed by every transformation of the group action. -/
def IsInvariant (ω : 𝓢[ℝ, E]) : Prop := ∀ g, ρ g • ω = ω

/-! ## B. Covariant channels -/

/-! ### B.1. Definition and closure properties -/

/-- A channel intertwines two group actions if it commutes with their transformations. -/
def IsIntertwining (Φ : E →ₚ₁[ℝ] F) : Prop := ∀ g x, Φ (ρ g x) = σ g (Φ x)

variable {ρ σ}

/-- The identity channel intertwines a group action with itself. -/
lemma isIntertwining_id : IsIntertwining ρ ρ (.id ℝ E) := by
  intro _ _
  rfl

/-- The composition of intertwining channels also intertwines the group actions. -/
lemma IsIntertwining.comp {H : Type*} [OrderUnitSpace H] {τ : G →* Reversible H H}
    {Φ : E →ₚ₁[ℝ] F} {Ψ : F →ₚ₁[ℝ] H} (hΦ : IsIntertwining ρ σ Φ)
    (hΨ : IsIntertwining σ τ Ψ) : IsIntertwining ρ τ (Ψ.comp Φ) := by
  intro g x
  simp [hΦ g x, hΨ g (Φ x)]

/-! ### B.2. Invariant states -/

/-- Pulling back an invariant state along an intertwining channel preserves invariance. -/
lemma IsIntertwining.comap_isInvariant {Φ : E →ₚ₁[ℝ] F} (h : IsIntertwining ρ σ Φ)
    {ω : 𝓢[ℝ, F]} (hω : IsInvariant σ ω) :
    IsInvariant ρ (UnitalPositiveLinearMap.comap Φ ω) := by
  intro g
  ext x
  have h1 := h g⁻¹ x
  have h2 := DFunLike.congr_fun (hω g) (Φ x)
  simp only [map_inv, Reversible.inv_apply] at h1
  change ω (Φ ((ρ g).symm x)) = ω (Φ x)
  rw [h1]
  exact h2

/-! ## C. Transport of group actions -/

variable (ρ σ) (e : Reversible E F)

/-! ### C.1. Conjugation -/

/-- Conjugation by a reversible transformation transports automorphisms from `E` to `F`. -/
def Reversible.conj : Reversible E E →* Reversible F F where
  toFun φ := e.symm.trans (φ.trans e)
  map_one' := by ext y; exact e.apply_symm_apply y
  map_mul' φ ψ := by ext y; simp

/-! ### C.2. Transported actions -/

/-- Transport a group action from `E` to `F` along a reversible transformation. -/
def Reversible.transport : G →* Reversible F F := e.conj.comp ρ

/-- A reversible transformation intertwines an action with its transport. -/
lemma Reversible.isIntertwining_transport :
    IsIntertwining ρ (e.transport ρ) e.toChannel := by
  intro g x
  simp [transport, conj]

/-- A reversible transformation intertwines two actions exactly when the target action
is the transport of the source action. -/
lemma Reversible.isIntertwining_iff_eq_transport :
    IsIntertwining ρ σ e.toChannel ↔ σ = e.transport ρ := by
  constructor
  · intro h
    ext g y
    have := h g (e.symm y)
    simp only [toChannel_apply, apply_symm_apply] at this
    simp [transport, conj, this]
  · rintro rfl
    exact e.isIntertwining_transport ρ

end ProbabilisticTheory
