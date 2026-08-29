/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Basic
public import Mathlib.Algebra.Lie.OfAssociative

/-!

# Observables

An observable is a self-adjoint element of an observable algebra. It has real
spectrum; positive observables have nonnegative spectrum. The Jordan and Lie
products are the symmetric and antisymmetric parts of multiplication.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- An observable is a self-adjoint element of `A`: position, momentum, energy, spin, ... . -/
noncomputable abbrev Observable (A : Type*) [OperatorAlgebra A] := selfAdjoint A

/-- A positive observable. Its spectrum is contained in the nonnegative reals. -/
abbrev PositiveElement (A : Type*) [OperatorAlgebra A] := {a : Observable A // 0 ≤ (a : A)}

/-- An effect is an observable between zero and the identity, representing a yes/no measurement
outcome. -/
abbrev Effect (A : Type*) [OperatorAlgebra A] := Set.Icc (0 : Observable A) 1

namespace Observable

/-- The symmetrized product of two observables. -/
noncomputable def jordan (a b : Observable A) : Observable A :=
  realPart ((a : A) * (b : A))

/-- The Jordan product on observables. -/
scoped[OperatorAlgebra] infixl:70 " ⊙ " => Observable.jordan

lemma coe_jordan (a b : Observable A) :
    (a ⊙ b : A) = (2⁻¹ : ℝ) • ((a : A) * b + (b : A) * a) := by
  change (↑(realPart ((a : A) * (b : A))) : A) =
    (2⁻¹ : ℝ) • ((a : A) * b + (b : A) * a)
  rw [realPart_apply_coe, star_mul, a.property.star_eq, b.property.star_eq]

/-- The antisymmetric observable product. -/
noncomputable def lie (a b : Observable A) : Observable A :=
  imaginaryPart ((a : A) * (b : A))

/-- The standard bracket notation for the explicit operation `Observable.lie`. -/
noncomputable instance instBracket : Bracket (Observable A) (Observable A) := ⟨lie⟩

lemma coe_lie (a b : Observable A) :
    (lie a b : A) =
      (-(Complex.I / 2)) • ((a : A) * b - (b : A) * a) := by
  change
    (↑(imaginaryPart ((a : A) * (b : A))) : A) =
      (-(Complex.I / 2)) • ((a : A) * (b : A) - (b : A) * (a : A))
  rw [imaginaryPart_apply_coe, star_mul, a.property.star_eq, b.property.star_eq]
  module

/-- Coercion formula for the bracket notation. -/
lemma coe_bracket (a b : Observable A) :
    ((⁅a, b⁆ : Observable A) : A) =
      (-(Complex.I / 2)) • ((a : A) * b - (b : A) * a) := by
  exact coe_lie a b

/-- Observable multiplication splits into its symmetric and antisymmetric parts. -/
lemma mul_decomposition (a b : Observable A) :
    (a : A) * b =
      (a ⊙ b : A) + Complex.I • ((⁅a, b⁆ : Observable A) : A) := by
  change
    (a : A) * b =
      ↑(realPart ((a : A) * (b : A))) +
        Complex.I • ↑(imaginaryPart ((a : A) * (b : A)))
  exact (realPart_add_I_smul_imaginaryPart ((a : A) * (b : A))).symm

end Observable

end OperatorAlgebra
