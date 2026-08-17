/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OperatorAlgebra.Effect
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!

# States on observable C⋆-algebras

A state on a unital C⋆-algebra `A` is a positive normalized complex-linear
functional

`ω : A → ℂ`.

This file develops the basic state API independently of a particular
Hilbert-space representation.

The main structures developed here are:

* positivity of states;
* probabilities associated with effects;
* convex mixtures;
* pure states;
* pullback of states along ⋆-homomorphisms.

The theory itself is not specifically quantum: for a commutative C⋆-algebra
the same definitions describe classical states.

Density operators and traces are not used here. They belong to the
finite-dimensional Hilbert-space realization of this abstract theory.

-/

@[expose] public section

namespace QuantumMechanics

open scoped ComplexOrder

variable {A : Type*}
  [CStarAlgebra A]
  [PartialOrder A]
  [StarOrderedRing A]

namespace State


/-!
## Basic properties
-/

/-- Two states are equal if they agree on every element of the algebra. -/
@[ext]
lemma ext {ω φ : State A}
    (h : ∀ a : A, ω a = φ a) :
    ω = φ := by
  sorry


/-- A state takes positive elements to nonnegative values. -/
lemma apply_nonneg
    (ω : State A) {a : A}
    (ha : 0 ≤ a) :
    0 ≤ ω a := by
  sorry


/-- The expectation value of `a⋆a` is nonnegative. -/
lemma star_mul_self_nonneg
    (ω : State A) (a : A) :
    0 ≤ ω (star a * a) := by
  sorry


/-- The expectation value of a self-adjoint element is real. -/
lemma apply_selfAdjoint_im_eq_zero
    (ω : State A) {a : A}
    (ha : IsSelfAdjoint a) :
    (ω a).im = 0 := by
  sorry


/-- The expectation value of an observable is real. -/
lemma observable_im_eq_zero
    (ω : State A) (a : Observable A) :
    (ω (a : A)).im = 0 := by
  sorry


/-!
## Effects and probabilities

An effect satisfies `0 ≤ E ≤ 1`. A state therefore assigns every effect a
probability in the interval `[0, 1]`.
-/

/-- The expectation value of an effect lies in the real interval `[0, 1]`. -/
lemma effect_expectation_mem_Icc
    (ω : State A) (E : Effect A) :
    0 ≤ (ω (E : A)).re ∧
      (ω (E : A)).re ≤ 1 := by
  sorry


/-- The probability assigned by a state to an effect. -/
noncomputable def probability
    (ω : State A) (E : Effect A) : ℝ :=
  (ω (E : A)).re


lemma probability_nonneg
    (ω : State A) (E : Effect A) :
    0 ≤ probability ω E :=
  (effect_expectation_mem_Icc ω E).1


lemma probability_le_one
    (ω : State A) (E : Effect A) :
    probability ω E ≤ 1 :=
  (effect_expectation_mem_Icc ω E).2


@[simp]
lemma probability_zero
    (ω : State A) :
    probability ω (0 : Effect A) = 0 := by
  sorry


@[simp]
lemma probability_one
    (ω : State A) :
    probability ω (1 : Effect A) = 1 := by
  sorry


/-- Complementary effects have complementary probabilities. -/
lemma probability_complement
    (ω : State A) (E : Effect A) :
    probability ω (Effect.complement E) =
      1 - probability ω E := by
  sorry


/-!
## Convex structure

The state space is convex. Convex combinations describe probabilistic
mixtures of states.
-/

/-- The convex mixture `tω + (1 - t)φ` of two states. -/
noncomputable def mix
    (ω φ : State A)
    (t : ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    State A := by
  sorry


/-- Evaluation of a convex mixture. -/
lemma mix_apply
    (ω φ : State A)
    (t : ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1)
    (a : A) :
    mix ω φ t ht₀ ht₁ a =
      (t : ℂ) * ω a +
        ((1 - t : ℝ) : ℂ) * φ a := by
  sorry


@[simp]
lemma mix_zero
    (ω φ : State A) :
    mix ω φ 0 le_rfl zero_le_one = φ := by
  sorry


@[simp]
lemma mix_one
    (ω φ : State A) :
    mix ω φ 1 zero_le_one le_rfl = ω := by
  sorry


@[simp]
lemma mix_self
    (ω : State A)
    (t : ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    mix ω ω t ht₀ ht₁ = ω := by
  sorry


/-!
## Pure states

Purity is intrinsic to the convex geometry of the state space. It does not
refer to vectors, rays, ranks, or density operators.
-/

/-- A state is pure if every nontrivial convex decomposition is trivial. -/
def IsPure (ω : State A) : Prop :=
  ∀ (φ ψ : State A)
    (t : ℝ)
    (ht₀ : 0 < t)
    (ht₁ : t < 1),
    mix φ ψ t ht₀.le ht₁.le = ω →
      φ = ω ∧ ψ = ω


/-!
## Pullback of states

States transform contravariantly with observables.

A unital ⋆-homomorphism `f : A → B` sends a state on `B` to a state on `A`
by composition.
-/

section Pullback

variable {B : Type*}
  [CStarAlgebra B]
  [PartialOrder B]
  [StarOrderedRing B]


/-- Pull a state back along a unital complex ⋆-homomorphism. -/
noncomputable def pullback
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B) :
    State A := by
  sorry


@[simp]
lemma pullback_apply
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (a : A) :
    pullback f ω a = ω (f a) := by
  sorry


end Pullback

end State

end QuantumMechanics
