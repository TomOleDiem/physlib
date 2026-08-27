/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Observables.Jordan
public import Physlib.QuantumMechanics.OperatorAlgebra.Observables.Lie

/-!

# States

A state determines the statistical predictions of a quantum system.

For an observable `a`, `ω⟨a⟩` denotes its real expectation value in the state
`ω`. Subtracting this expectation centers the observable. Covariance is the
expectation of the symmetrized product of two centered observables, and variance
is covariance on the diagonal.

More general measurement statistics are obtained by evaluating states on
effects and POVMs.

-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

namespace State

noncomputable instance : CoeFun (State A) (fun _ => A → ℂ) where
  coe ω := ω.toPositiveLinearMap

/-! ## Expectation -/

/-- The real expectation functional obtained by restricting a state to observables. -/
noncomputable def expectation (ω : State A) : Observable A →ₗ[ℝ] ℝ where
  toFun a := (ω.toPositiveLinearMap (a : A)).re
  map_add' a b := by simp
  map_smul' r a := by
    rw [selfAdjoint.val_smul, PositiveLinearMap.map_smul_of_tower]
    simp

@[inherit_doc State.expectation]
scoped[OperatorAlgebra] notation:max ω "⟨" a "⟩" => State.expectation ω a

attribute [nolint docBlame] OperatorAlgebra.«term_⟨_⟩»

lemma apply_observable_eq_expectation (ω : State A) (a : Observable A) :
    ω (a : A) = (ω⟨a⟩ : ℂ) := by
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im]
    have h : star (ω (a : A)) = ω (a : A) := by
      rw [← map_star, a.property.star_eq]
    exact Complex.conj_eq_iff_im.mp
      (by simpa [Complex.star_def] using h)

@[simp]
lemma expectation_one (ω : State A) :
    ω⟨(1 : Observable A)⟩ = 1 := by
  simp [expectation, ω.map_one]

/-- Positive observables have nonnegative expectation. -/
lemma expectation_nonneg (ω : State A) {a : Observable A}
    (ha : 0 ≤ (a : A)) :
    0 ≤ ω⟨a⟩ :=
  (Complex.le_def.mp (ω.toPositiveLinearMap.map_nonneg ha)).1

/-! ## Centering -/

/-- An observable with its expectation value subtracted. -/
noncomputable def centered (ω : State A) (a : Observable A) : Observable A :=
  a - ω⟨a⟩ • 1

@[simp]
lemma expectation_centered (ω : State A) (a : Observable A) :
    ω⟨centered ω a⟩ = 0 := by
  simp [centered]

/-- Centering removes scalar multiples of the identity. -/
@[simp]
lemma centered_add_smul_one (ω : State A) (a : Observable A) (c : ℝ) :
    centered ω (a + c • 1) = centered ω a := by
  simp only [centered, map_add, map_smul, expectation_one]
  module

/-! ## Covariance and variance -/

/-- Covariance is the expectation of the symmetrized product of centered observables. -/
noncomputable def covariance (ω : State A) (a b : Observable A) : ℝ :=
  ω⟨centered ω a ⊙ centered ω b⟩

/-- Variance is covariance on the diagonal. -/
noncomputable def variance (ω : State A) (a : Observable A) : ℝ :=
  covariance ω a a

@[simp]
lemma covariance_self (ω : State A) (a : Observable A) :
    covariance ω a a = variance ω a :=
  rfl

/-- Covariance is symmetric. -/
lemma covariance_comm (ω : State A) (a b : Observable A) :
    covariance ω a b = covariance ω b a := by
  simp only [covariance]
  rw [Observable.jordan_comm]

/-- Adding a scalar multiple of the identity to the left observable does not change covariance. -/
lemma covariance_add_smul_one_left (ω : State A) (a b : Observable A) (c : ℝ) :
    covariance ω (a + c • 1) b = covariance ω a b := by
  simp only [covariance, centered_add_smul_one]

/-- Adding a scalar multiple of the identity to the right observable does not change covariance. -/
lemma covariance_add_smul_one_right (ω : State A) (a b : Observable A) (c : ℝ) :
    covariance ω a (b + c • 1) = covariance ω a b := by
  simp only [covariance, centered_add_smul_one]

/-- Variance is nonnegative. -/
lemma variance_nonneg (ω : State A) (a : Observable A) :
    0 ≤ variance ω a := by
  rw [variance, covariance]
  apply expectation_nonneg
  show 0 ≤ (Observable.jordan (centered ω a) (centered ω a) : A)
  rw [Observable.jordan_self]
  simpa [(centered ω a).property.star_eq] using
    star_mul_self_nonneg (centered ω a : A)

end State

end OperatorAlgebra
