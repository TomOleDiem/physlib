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

namespace OperatorAlgebra

open scoped ComplexOrder

variable {A : Type*}
  [CStarAlgebra A]
  [PartialOrder A]
  [StarOrderedRing A]

namespace State


/-!
## Basic properties
-/

noncomputable instance instCoeFun :
    CoeFun (State A) (fun _ => A → ℂ) where
  coe ω := ω.toPositiveLinearMap


@[simp]
lemma apply_one (ω : State A) :
    ω 1 = 1 :=
  ω.map_one


/-- Two states are equal if they agree on every element of the algebra. -/
@[ext]
lemma ext {ω φ : State A}
    (h : ∀ a : A, ω a = φ a) :
    ω = φ := by
  obtain ⟨f, hf⟩ := ω
  obtain ⟨g, hg⟩ := φ
  congr 1
  exact PositiveLinearMap.ext h


/-- A state takes positive elements to nonnegative values. -/
lemma apply_nonneg
    (ω : State A) {a : A}
    (ha : 0 ≤ a) :
    0 ≤ ω a :=
  ω.toPositiveLinearMap.map_nonneg ha


/-- The expectation value of `a⋆a` is nonnegative. -/
lemma star_mul_self_nonneg
    (ω : State A) (a : A) :
    0 ≤ ω (star a * a) :=
  ω.apply_nonneg (_root_.star_mul_self_nonneg a)


/-- The expectation value of a self-adjoint element is real. -/
lemma apply_selfAdjoint_im_eq_zero
    (ω : State A) {a : A}
    (ha : IsSelfAdjoint a) :
    (ω a).im = 0 := by
  have h1 := Complex.le_def.mp (ω.apply_nonneg (CFC.posPart_nonneg a))
  have h2 := Complex.le_def.mp (ω.apply_nonneg (CFC.negPart_nonneg a))
  rw [← CFC.posPart_sub_negPart a ha, map_sub, Complex.sub_im, ← h1.2, ← h2.2]
  simp


/-- The expectation value of an observable is real. -/
lemma observable_im_eq_zero
    (ω : State A) (a : Observable A) :
    (ω (a : A)).im = 0 :=
  ω.apply_selfAdjoint_im_eq_zero a.property


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
  have h0 : (0 : A) ≤ (E : A) := Subtype.coe_le_coe.mpr (Effect.nonneg E)
  have h1 : (E : A) ≤ (1 : A) := Subtype.coe_le_coe.mpr (Effect.le_one E)
  refine ⟨?_, ?_⟩
  · have h := Complex.le_def.mp (ω.apply_nonneg h0)
    simpa using h.1
  · have hsub : (0 : A) ≤ (1 : A) - (E : A) := sub_nonneg.mpr h1
    have h := Complex.le_def.mp (ω.apply_nonneg hsub)
    rw [map_sub, State.apply_one, Complex.sub_re, Complex.one_re, Complex.zero_re] at h
    linarith [h.1]


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
  simp [probability, Effect.coe_zero]


@[simp]
lemma probability_one
    (ω : State A) :
    probability ω (1 : Effect A) = 1 := by
  simp [probability, Effect.coe_one]


/-- Complementary effects have complementary probabilities. -/
lemma probability_complement
    (ω : State A) (E : Effect A) :
    probability ω (Effect.complement E) =
      1 - probability ω E := by
  simp only [probability]
  show (ω ((Effect.complement E : Observable A) : A)).re = 1 - (ω (E : A)).re
  rw [Effect.coe_complement]
  push_cast
  rw [map_sub, State.apply_one, Complex.sub_re, Complex.one_re]


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
    State A where
  toPositiveLinearMap := PositiveLinearMap.mk₀
    { toFun := fun a => (t : ℂ) * ω a + ((1 - t : ℝ) : ℂ) * φ a
      map_add' := fun a b => by
        simp only [map_add]
        ring
      map_smul' := fun c a => by
        simp only [RingHom.id_apply, map_smul, smul_eq_mul]
        ring }
    (fun a ha => by
      show (0 : ℂ) ≤ (t : ℂ) * ω a + ((1 - t : ℝ) : ℂ) * φ a
      have h1 := Complex.le_def.mp (ω.apply_nonneg ha)
      have h2 := Complex.le_def.mp (φ.apply_nonneg ha)
      have ht1 : (0 : ℝ) ≤ 1 - t := by linarith
      rw [Complex.le_def]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im] at h1 h2 ⊢
      exact ⟨by nlinarith [h1.1, h2.1, mul_nonneg ht₀ h1.1, mul_nonneg ht1 h2.1],
        by nlinarith [h1.2, h2.2]⟩)
  map_one := by
    show (t : ℂ) * ω 1 + ((1 - t : ℝ) : ℂ) * φ 1 = 1
    rw [State.apply_one, State.apply_one]
    push_cast
    ring


/-- Evaluation of a convex mixture. -/
lemma mix_apply
    (ω φ : State A)
    (t : ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1)
    (a : A) :
    mix ω φ t ht₀ ht₁ a =
      (t : ℂ) * ω a +
        ((1 - t : ℝ) : ℂ) * φ a :=
  rfl


@[simp]
lemma mix_zero
    (ω φ : State A) :
    mix ω φ 0 le_rfl zero_le_one = φ := by
  ext a
  rw [mix_apply]
  push_cast
  ring


@[simp]
lemma mix_one
    (ω φ : State A) :
    mix ω φ 1 zero_le_one le_rfl = ω := by
  ext a
  rw [mix_apply]
  push_cast
  ring


@[simp]
lemma mix_self
    (ω : State A)
    (t : ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    mix ω ω t ht₀ ht₁ = ω := by
  ext a
  rw [mix_apply]
  push_cast
  ring


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
    State A where
  toPositiveLinearMap := ω.toPositiveLinearMap.comp (PositiveLinearMap.ofClass f)
  map_one := by
    show ω.toPositiveLinearMap ((PositiveLinearMap.ofClass f : A →ₚ[ℂ] B) 1) = 1
    have h1 : (PositiveLinearMap.ofClass f : A →ₚ[ℂ] B) 1 = 1 := _root_.map_one f
    rw [h1]
    exact ω.map_one


@[simp]
lemma pullback_apply
    (f : A →⋆ₐ[ℂ] B)
    (ω : State B)
    (a : A) :
    pullback f ω a = ω (f a) :=
  rfl


@[simp]
lemma pullback_id (ω : State A) :
    pullback (StarAlgHom.id ℂ A) ω = ω := by
  ext a
  simp


lemma pullback_comp
    {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (f : A →⋆ₐ[ℂ] B) (g : B →⋆ₐ[ℂ] C) (ω : State C) :
    pullback (g.comp f) ω = pullback f (pullback g ω) := by
  ext a
  simp


end Pullback

end State

end OperatorAlgebra
