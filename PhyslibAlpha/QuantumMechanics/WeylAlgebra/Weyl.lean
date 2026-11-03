/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Star.Module

/-!
# The Weyl form of the canonical commutation relations

The canonical commutation relations of bosons in exponentiated form, which needs no unbounded
operators and, unlike the relations of `LadderRep`, can be satisfied by bounded operators.

## i. Overview

No finite matrices satisfy `[a, a†] = 1`, and the annihilation operator of a boson is unbounded.
The Weyl operators `W(f) = exp(i (a(f) + a(f)†))` of a wave function `f` are unitary, and the
canonical commutation relations become `W(f) W(g) = exp(-i σ(f, g) / 2) W(f + g)`, where
`σ(f, g) = Im⟨f, g⟩` is the symplectic form of the wave functions. These relations only involve the
real vector space `V` of wave functions with its alternating form `σ`: the structure behind
bosons is a symplectic space, and the modes play no role. A `WeylRep` is a family of operators
satisfying them in a `*`-algebra. The Weyl operators of wave functions with `σ(f, g) = 0`
commute; in general they commute up to the phase `exp(-i σ(f, g))`.

A linear map `φ` between symplectic spaces that preserves the symplectic form, such as the
one-particle dynamics of a quadratic Hamiltonian or a Bogoliubov transformation, turns
a representation `W` into the representation `W ∘ φ`.

## ii. Key results

- `symplectic`: the symplectic form `Im⟨f, g⟩` of a complex inner product space.
- `WeylRep`: a family of operators satisfying the Weyl relations.
- `WeylRep.star_mul_self`: the Weyl operators are unitary.
- `WeylRep.mul_comm_phase`: `W(f) W(g) = exp(-i σ(f, g)) W(g) W(f)`.
- `WeylRep.comap`: a symplectic linear map acts on representations.

## iii. Table of contents

- A. The symplectic form
- B. Weyl operators
- C. Symplectic maps

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 5.2.

-/

@[expose] public section

namespace WeylAlgebra

open Complex

/-!

## A. The symplectic form

-/

section Symplectic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The symplectic form `σ(f, g) = Im⟨f, g⟩` of a complex inner product space, a real alternating
bilinear form. -/
noncomputable def symplectic : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => (inner ℂ f g).im)
    (fun f g h => by simp [inner_add_left]) (fun c f g => by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c f, inner_smul_left]; simp)
    (fun f g h => by simp [inner_add_right]) (fun c f g => by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ) c g, inner_smul_right]; simp)

end Symplectic

/-!

## B. Weyl operators

-/

variable {V V' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V'] [Module ℝ V']
  {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]

/-- A representation of the canonical commutation relations in Weyl form: operators `W f` of the
wave functions `f` with `W f W g = exp(-i σ(f, g) / 2) W (f + g)`, where `σ` is the symplectic
form. -/
structure WeylRep (σ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (B : Type*) [Ring B] [StarRing B] [Algebra ℂ B] where
  /-- The Weyl operator of a wave function. -/
  W : V → B
  /-- The Weyl operator of the zero wave function is the identity. -/
  W_zero : W 0 = 1
  /-- The adjoint of a Weyl operator is that of the opposite wave function. -/
  star_W : ∀ f, star (W f) = W (-f)
  /-- The Weyl relation. -/
  W_mul : ∀ f g, W f * W g = Complex.exp (-(Complex.I * (σ f g : ℂ)) / 2) • W (f + g)

namespace WeylRep

variable {σ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (R : WeylRep σ B)

/-- **The Weyl operators are unitary**: `W(f)† W(f) = 1`, for an alternating form `σ`. -/
lemma star_mul_self (hσ : ∀ f, σ f f = 0) (f : V) : star (R.W f) * R.W f = 1 := by
  rw [R.star_W, R.W_mul]
  simp [hσ, R.W_zero]

/-- **Weyl operators commute up to a phase**: `W f W g = exp(-i σ(f, g)) W g W f`, for an
alternating form `σ`. -/
lemma mul_comm_phase (hσ : ∀ f, σ f f = 0) (f g : V) :
    R.W f * R.W g = Complex.exp (-(Complex.I * (σ f g : ℂ))) • (R.W g * R.W f) := by
  have h : σ g f = - σ f g := by
    have := hσ (f + g)
    simp only [map_add, LinearMap.add_apply, hσ] at this
    linarith
  rw [R.W_mul, R.W_mul, add_comm g f, h, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-!

## C. Symplectic maps

-/

/-- **A symplectic map acts on representations**: if `φ` is linear and preserves the symplectic
form, `W ∘ φ` satisfies the Weyl relations of the form on the source. -/
def comap {σ' : V' →ₗ[ℝ] V' →ₗ[ℝ] ℝ} (φ : V' →ₗ[ℝ] V) (hφ : ∀ f g, σ (φ f) (φ g) = σ' f g) :
    WeylRep σ' B where
  W f := R.W (φ f)
  W_zero := by simp [R.W_zero]
  star_W f := by simp [R.star_W]
  W_mul f g := by simp [R.W_mul, hφ]

end WeylRep

end WeylAlgebra
