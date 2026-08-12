/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OneParameterSubgroups.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!

# One-parameter subgroups of complex matrices

## i. Overview

A continuous one-parameter subgroup of invertible complex matrices is represented by
`ContinuousMonoidHom (Multiplicative ℝ) (Matrix (Fin n) (Fin n) ℂ)ˣ`. This file proves that every
such subgroup has a unique matrix `A` satisfying `U(t) = exp (tA)`.

The Frobenius norm supplies the required Banach-algebra structure on matrices. The generator
result then follows from `OneParameterSubgroup.existsUnique_generator` after identifying real
scalar multiplication with scalar multiplication by real complex numbers.

## ii. Key results

Definitions:
* `Matrix.OneParameterSubgroup`: Continuous one-parameter subgroups of invertible complex
    matrices.

Lemmas:
* `Matrix.OneParameterSubgroup.existsUnique_generator`: Existence and uniqueness of the matrix
    generator.
* `Matrix.OneParameterSubgroup.generator_eq`: Uniqueness for two given exponential
    representations.

## iii. References

-/

@[expose] public section

open Matrix

noncomputable section

namespace Matrix

/-- The Frobenius normed-ring structure used for matrix one-parameter subgroups. -/
@[instance_reducible, local instance] def oneParameterNormedRing (n : ℕ) :
    NormedRing (Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.frobeniusNormedRing

/-- The topology induced by the Frobenius norm on matrices. -/
@[instance_reducible, local instance] def oneParameterTopologicalSpace (n : ℕ) :
    TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) :=
  (oneParameterNormedRing n).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The Frobenius normed-algebra structure used for matrix one-parameter subgroups. -/
@[instance_reducible, local instance] def oneParameterNormedAlgebraComplex (n : ℕ) :
    NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  Matrix.frobeniusNormedAlgebra

/-- The additive commutative group underlying the Frobenius normed-ring structure. -/
@[instance_reducible, local instance] def oneParameterAddCommGroup (n : ℕ) :
    AddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
  (oneParameterNormedRing n).toAddCommGroup

/-- The complex module underlying the Frobenius normed-algebra structure. -/
@[instance_reducible, local instance] def oneParameterModuleComplex (n : ℕ) :
    Module ℂ (Matrix (Fin n) (Fin n) ℂ) :=
  (oneParameterNormedAlgebraComplex n).toModule

/-- The real module obtained by restricting scalars from the complex matrix module. -/
@[instance_reducible, local instance] def oneParameterModuleReal (n : ℕ) :
    Module ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  NormedSpace.complexToReal.toModule

/-- A continuous one-parameter subgroup of the unit group of complex matrices. -/
abbrev OneParameterSubgroup (n : ℕ) :=
  ContinuousMonoidHom (Multiplicative ℝ) (Matrix (Fin n) (Fin n) ℂ)ˣ

namespace OneParameterSubgroup

variable {n : ℕ}

/-- The value of a matrix one-parameter subgroup as a matrix. -/
def value (U : Matrix.OneParameterSubgroup n) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  U (.ofAdd t)

@[simp] lemma value_zero (U : Matrix.OneParameterSubgroup n) : value U 0 = 1 := by
  simp [value]

@[simp] lemma value_add (U : Matrix.OneParameterSubgroup n) (s t : ℝ) :
    value U (s + t) = value U s * value U t := by
  change (U (.ofAdd (s + t)) : Matrix (Fin n) (Fin n) ℂ) = _
  exact congrArg Units.val (map_mul U (.ofAdd s) (.ofAdd t))

/-- Every continuous matrix one-parameter subgroup has a unique matrix generator. -/
lemma existsUnique_generator (U : Matrix.OneParameterSubgroup n) :
    ∃! A : Matrix (Fin n) (Fin n) ℂ,
      ∀ t : ℝ, value U t = NormedSpace.exp ((t : ℂ) • A) := by
  obtain ⟨A, hA, hA_unique⟩ := _root_.OneParameterSubgroup.existsUnique_generator U
  have hsmul (t : ℝ) (B : Matrix (Fin n) (Fin n) ℂ) : t • B = (t : ℂ) • B := rfl
  refine ⟨A, fun t => by simpa only [value, hsmul] using hA t, ?_⟩
  intro B hB
  apply hA_unique B
  intro t
  simpa only [value, hsmul] using hB t

/-- Two global exponential representations of the same subgroup have equal generators. -/
lemma generator_eq {U : Matrix.OneParameterSubgroup n}
    {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ t : ℝ, value U t = NormedSpace.exp ((t : ℂ) • A))
    (hB : ∀ t : ℝ, value U t = NormedSpace.exp ((t : ℂ) • B)) : A = B := by
  obtain ⟨_, _, h_unique⟩ := existsUnique_generator U
  exact (h_unique A hA).trans (h_unique B hB).symm

end OneParameterSubgroup

end Matrix
