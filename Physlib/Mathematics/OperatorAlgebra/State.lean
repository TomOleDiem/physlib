/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

/-!

# States on observable C⋆-algebras

A state on a unital C⋆-algebra `A` is a positive normalized complex-linear functional
`ω : A → ℂ`.

## Note

This is a deliberately trimmed port: only what the abstract qubit development (`Qubit/`) needs
to state its Bloch-ball and purity results — evaluation, positivity, reality of expectation
values on observables, convex mixtures, and purity. Probabilities of effects and pullback of
states along ⋆-homomorphisms are not included; add them back (from physlib's history) if and
when something needs them.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder

variable {A : Type*} [OperatorAlgebra A]

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


/-- A state takes positive elements to nonnegative values. -/
lemma apply_nonneg
    (ω : State A) {a : A}
    (ha : 0 ≤ a) :
    0 ≤ ω a :=
  ω.toPositiveLinearMap.map_nonneg ha


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
## Convex structure

The state space is convex. Convex combinations describe probabilistic mixtures of states.
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


/-!
## Pure states

Purity is intrinsic to the convex geometry of the state space. It does not refer to vectors,
rays, ranks, or density operators.
-/

/-- A state is pure if every nontrivial convex decomposition is trivial. -/
def IsPure (ω : State A) : Prop :=
  ∀ (φ ψ : State A)
    (t : ℝ)
    (ht₀ : 0 < t)
    (ht₁ : t < 1),
    mix φ ψ t ht₀.le ht₁.le = ω →
      φ = ω ∧ ψ = ω

end State

end OperatorAlgebra
