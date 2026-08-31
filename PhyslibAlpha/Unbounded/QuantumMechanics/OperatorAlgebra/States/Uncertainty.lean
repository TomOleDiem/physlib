/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.Expectation
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!

# Uncertainty relations

Positivity of a state gives a Cauchy–Schwarz inequality for expectation values.
Applied to centered observables, this yields the Robertson–Schrödinger and
Robertson uncertainty relations.

-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace OperatorAlgebra

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

namespace State

/-! ## Products of observables -/

/-- The product of two observables splits into its symmetric and antisymmetric parts. -/
lemma observable_mul_decomposition (a b : Observable A) :
    (a : A) * b =
      (a ⊙ b : A) + Complex.I • ((⁅a, b⁆ : Observable A) : A) := by
  change
    (a : A) * b =
      ↑(realPart ((a : A) * (b : A))) +
        Complex.I • ↑(imaginaryPart ((a : A) * (b : A)))
  exact (realPart_add_I_smul_imaginaryPart ((a : A) * (b : A))).symm

/-- Centering does not change the antisymmetric part of a product. -/
@[simp]
lemma bracket_centered (ω : State A) (a b : Observable A) :
    ⁅centered ω a, centered ω b⁆ = ⁅a, b⁆ := by
  simp [centered, sub_lie, lie_sub]

/-- The expectation of a centered product splits into its symmetric and antisymmetric parts. -/
lemma apply_centered_mul_centered (ω : State A) (a b : Observable A) :
    ω ((centered ω a : A) * centered ω b) =
      (covariance ω a b : ℂ) + Complex.I * (ω⟨⁅a, b⁆⟩ : ℂ) := by
  rw [observable_mul_decomposition, map_add, map_smul,
    apply_observable_eq_expectation, apply_observable_eq_expectation,
    bracket_centered]
  rfl

/-! ## Cauchy–Schwarz -/

/-- Reversing a product of observables conjugates its state value. -/
lemma apply_mul_comm_eq_star (ω : State A) (a b : Observable A) :
    ω ((b : A) * a) = star (ω ((a : A) * b)) := by
  rw [← map_star, star_mul, a.property.star_eq, b.property.star_eq]

/-- GNS Cauchy–Schwarz for centered observables, before rewriting to variances. -/
lemma centered_gns_cauchy_schwarz (ω : State A) (a b : Observable A) :
    ‖ω ((centered ω a : A) * centered ω b)‖ *
        ‖ω ((centered ω b : A) * centered ω a)‖ ≤
      variance ω a * variance ω b := by
  let φ := ω.toPositiveLinearMap
  have h := inner_mul_inner_self_le (𝕜 := ℂ)
    (φ.toPreGNS (centered ω a : A))
    (φ.toPreGNS (centered ω b : A))
  simp only [PositiveLinearMap.preGNS_inner_def,
    PositiveLinearMap.ofPreGNS_toPreGNS,
    (centered ω a).property.star_eq,
    (centered ω b).property.star_eq] at h
  rw [variance, covariance]
  change
    ‖φ ((centered ω a : A) * centered ω b)‖ *
        ‖φ ((centered ω b : A) * centered ω a)‖ ≤
      (φ ((centered ω a ⊙ centered ω a : Observable A) : A)).re *
        (φ ((centered ω b ⊙ centered ω b : Observable A) : A)).re
  rw [Observable.jordan_self, Observable.jordan_self]
  exact h

/-- Cauchy–Schwarz for centered observables. -/
lemma centered_cauchy_schwarz (ω : State A) (a b : Observable A) :
    Complex.normSq (ω ((centered ω a : A) * centered ω b)) ≤
      variance ω a * variance ω b := by
  calc
    Complex.normSq (ω ((centered ω a : A) * centered ω b)) =
        ‖ω ((centered ω a : A) * centered ω b)‖ *
          ‖ω ((centered ω b : A) * centered ω a)‖ := by
      rw [apply_mul_comm_eq_star]
      simp [Complex.normSq_eq_norm_sq, pow_two]
    _ ≤ _ := centered_gns_cauchy_schwarz ω a b

/-! ## Uncertainty relations -/

/--
The Robertson–Schrödinger uncertainty inequality.

With the chosen normalization of the bracket, the conventional factor `1/4`
is absorbed into the bracket.
-/
lemma robertson_schrodinger (ω : State A) (a b : Observable A) :
    covariance ω a b ^ 2 + ω⟨⁅a, b⁆⟩ ^ 2 ≤
      variance ω a * variance ω b := by
  have h := centered_cauchy_schwarz ω a b
  rw [apply_centered_mul_centered, Complex.normSq_apply] at h
  simpa [pow_two] using h

/-- Covariance satisfies the Cauchy–Schwarz inequality. -/
lemma covariance_cauchy_schwarz (ω : State A) (a b : Observable A) :
    covariance ω a b ^ 2 ≤ variance ω a * variance ω b := by
  nlinarith [robertson_schrodinger ω a b,
    sq_nonneg (ω⟨⁅a, b⁆⟩)]

/-- The Robertson uncertainty inequality. -/
lemma robertson (ω : State A) (a b : Observable A) :
    ω⟨⁅a, b⁆⟩ ^ 2 ≤ variance ω a * variance ω b := by
  nlinarith [robertson_schrodinger ω a b,
    sq_nonneg (covariance ω a b)]

end State

end OperatorAlgebra
