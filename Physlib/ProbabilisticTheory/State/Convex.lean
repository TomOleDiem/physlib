/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Basic
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.UnitInterval

/-!
# Convex state spaces

## i. Overview

States mix: a probabilistic combination of two states is again a state, and the state space
embeds convexly into the algebraic dual. A pure state is one that's never a genuine mixture of
two others, an extreme point of that convex set. A mixed state is one that is a mixture.

## ii. Key results

- `UnitalPositiveLinearMap.mix` : randomize between two states with a given probability.
- `UnitalPositiveLinearMap.stateSpace_convex` : the state space is convex in the algebraic dual.
- `UnitalPositiveLinearMap.isPure_iff_mem_extremePoints_stateSpace` : a state is pure iff it is an
  extreme point of the state space.

## iii. Table of contents

- A. Mixing states
- B. The state space
- C. Pure and mixed states

## iv. References

-/

@[expose] public section

open ProbabilisticTheory unitInterval

namespace UnitalPositiveLinearMap

variable {E : Type*} [OrderUnitSpace E]

/-!

## A. Mixing states

-/

/-- Randomize between two states with probability `t` of choosing the first, so
`t • ω + σ t • φ` with `σ t = 1 - t`. -/
def mix (ω φ : 𝓢[ℝ, E]) (t : unitInterval) : 𝓢[ℝ, E] :=
  .ofPositiveLinearMap (toNNReal t • ω + toNNReal (σ t) • φ)
    (by simp [NNReal.smul_def])

/-- Evaluation of a mixture is the pointwise convex combination. -/
@[simp]
lemma mix_apply (ω φ : 𝓢[ℝ, E]) (t : unitInterval) (A : E) :
    mix ω φ t A = (t : ℝ) * ω A + (1 - (t : ℝ)) * φ A := by
  simp [mix, NNReal.smul_def]

/-- The underlying linear map of a mixture is the corresponding combination of linear maps. -/
lemma toLinearMap_mix (ω φ : 𝓢[ℝ, E]) (t : unitInterval) :
    (mix ω φ t).toLinearMap = (t : ℝ) • ω.toLinearMap + (1 - (t : ℝ)) • φ.toLinearMap := by
  ext A
  simp

/-- Swapping the two states swaps the weights: `σ` is the symmetry of the interval. -/
lemma mix_symm (ω φ : 𝓢[ℝ, E]) (t : unitInterval) : mix ω φ t = mix φ ω (σ t) := by
  ext A
  simp [mix_apply, add_comm]

/-!

## B. The state space

-/

/-- States embedded into the algebraic dual. -/
def stateSpace : Set (E →ₗ[ℝ] ℝ) :=
  Set.range fun ω : 𝓢[ℝ, E] => ω.toLinearMap

/-- The state space is convex in the algebraic dual. -/
lemma stateSpace_convex : Convex ℝ (stateSpace (E := E)) := by
  rintro x ⟨ω, rfl⟩ y ⟨φ, rfl⟩ t s ht hs hts
  have hst : s = 1 - t := by linarith
  subst hst
  exact ⟨mix ω φ ⟨t, ht, by linarith⟩, toLinearMap_mix _ _ _⟩

/-!

## C. Pure and mixed states

-/

/-- A state is pure when it is not a genuine mixture of two other states. -/
def IsPure (ω : 𝓢[ℝ, E]) : Prop :=
  ∀ φ ψ t, 0 < t → t < 1 → mix φ ψ t = ω → φ = ω ∧ ψ = ω

/-- A state is mixed when it isn't pure. -/
def IsMixed (ω : 𝓢[ℝ, E]) : Prop := ¬ ω.IsPure

/-- A state is mixed exactly when it has a genuine nontrivial binary decomposition. -/
lemma isMixed_iff_exists_mix_ne {ω : 𝓢[ℝ, E]} :
    ω.IsMixed ↔ ∃ φ ψ t, 0 < t ∧ t < 1 ∧ mix φ ψ t = ω ∧ (φ ≠ ω ∨ ψ ≠ ω) := by
  simp only [IsMixed, IsPure]
  push Not
  simp only [imp_iff_not_or]

/-- Purity transported along an injective map sending mixtures to convex combinations: a state
is pure exactly when its image is an extreme point of the image of the state space. -/
lemma isPure_iff_mem_extremePoints {X : Type*} [AddCommGroup X] [Module ℝ X]
    {F : 𝓢[ℝ, E] → X} (hF : Function.Injective F)
    (hmix : ∀ φ ψ t, F (mix φ ψ t) = (t : ℝ) • F φ + (1 - (t : ℝ)) • F ψ) (ω : 𝓢[ℝ, E]) :
    ω.IsPure ↔ F ω ∈ (Set.range F).extremePoints ℝ := by
  rw [IsPure, mem_extremePoints]
  refine ⟨fun h => ⟨⟨ω, rfl⟩, ?_⟩, fun h φ ψ t ht0 ht1 hω => ?_⟩
  · rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩ ⟨t, s, ht, hs, hts, heq⟩
    obtain rfl : s = 1 - t := by linarith
    obtain ⟨rfl, rfl⟩ := h φ ψ ⟨t, ht.le, by linarith⟩ (by exact_mod_cast ht)
      (by exact_mod_cast (by linarith : t < 1)) (hF ((hmix _ _ _).trans heq))
    exact ⟨rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := h.2 _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩ ⟨t, 1 - t, by exact_mod_cast ht0,
      sub_pos.2 (by exact_mod_cast ht1), by ring, by rw [← hmix, hω]⟩
    exact ⟨hF h1, hF h2⟩

/-- A state is pure exactly when it is an extreme point of the state space in the algebraic
dual. -/
lemma isPure_iff_mem_extremePoints_stateSpace (ω : 𝓢[ℝ, E]) :
    ω.IsPure ↔ ω.toLinearMap ∈ stateSpace.extremePoints ℝ :=
  isPure_iff_mem_extremePoints toLinearMap_injective toLinearMap_mix ω
