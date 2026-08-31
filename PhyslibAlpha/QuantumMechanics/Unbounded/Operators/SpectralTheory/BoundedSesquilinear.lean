/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.Operators.SpectralTheory.WeakSpectralMeasure
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!

# Riesz realization of bounded sesquilinear spectral forms

The weak-operator PVM layer naturally produces matrix coefficients first.  A
bounded sesquilinear form is the correct intermediate object: Riesz
representation then produces the unique bounded operator whose matrix
coefficients are that form.  This file contains that representation step only;
it does not pretend that weak operator integration is a norm-valued Bochner
integral.

The convention is the one used by
`InnerProductSpace.continuousLinearMapOfBilin`: `form x y` is conjugate-linear
in `x` and linear in `y`, and the represented operator satisfies
`⟪y, operator x⟫ = conj (form x y)`.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder Function InnerProductSpace
open ContinuousLinearMap

namespace QuantumMechanics

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- A bounded sesquilinear form in the orientation expected by Mathlib's
Riesz representation theorem. -/
structure BoundedSesquilinearForm where
  /-- The underlying sesquilinear form. -/
  form : H →ₛₗ[starRingEnd ℂ] H →ₗ[ℂ] ℂ
  bound : ∃ C : ℝ, ∀ x y, ‖form x y‖ ≤ C * ‖x‖ * ‖y‖

namespace BoundedSesquilinearForm

variable (B : BoundedSesquilinearForm (H := H))

/-- A norm bound witnessing `B.bound`. -/
noncomputable def boundConstant : ℝ := Classical.choose B.bound

@[nolint unusedArguments]
lemma boundConstant_spec : ∀ x y, ‖B.form x y‖ ≤ B.boundConstant * ‖x‖ * ‖y‖ :=
  Classical.choose_spec B.bound

/-- The continuous version of a bounded sesquilinear form. -/
noncomputable def continuous : H →L⋆[ℂ] H →L[ℂ] ℂ := by
  exact LinearMap.mkContinuous₂ B.form B.boundConstant B.boundConstant_spec

@[simp]
lemma continuous_apply (x y : H) : B.continuous x y = B.form x y := by
  exact LinearMap.mkContinuous₂_apply B.form B.boundConstant_spec x y

/-- The unique bounded operator represented by `B`. -/
noncomputable def operator : H →L[ℂ] H :=
  InnerProductSpace.continuousLinearMapOfBilin B.continuous

/-- The bounded sesquilinear form associated with a bounded operator.

The conjugation is only an orientation correction: the inner product in this
file is conjugate-linear in its first slot, whereas `BoundedSesquilinearForm`
stores a form that is conjugate-linear in its first argument and linear in its
second argument. -/
noncomputable def ofOperator (T : H →L[ℂ] H) : BoundedSesquilinearForm (H := H) where
  form := {
    toFun := fun x => {
      toFun := fun y => starRingEnd ℂ (⟪y, T x⟫_ℂ)
      map_add' := by intro y z; simp [inner_add_left]
      map_smul' := by intro c y; simp [inner_smul_left] }
    map_add' := by intro x z; ext y; simp [inner_add_right, map_add]
    map_smul' := by intro c x; ext y; simp [inner_smul_right, map_smul] }
  bound := by
    refine ⟨‖T‖, fun x y ↦ ?_⟩
    change ‖starRingEnd ℂ (⟪y, T x⟫_ℂ)‖ ≤ _
    rw [← RCLike.star_def]
    rw [norm_star]
    calc
      ‖⟪y, T x⟫_ℂ‖ ≤ ‖y‖ * ‖T x‖ := norm_inner_le_norm _ _
      _ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
        calc
          ‖y‖ * ‖T x‖ ≤ ‖y‖ * (‖T‖ * ‖x‖) :=
            mul_le_mul_of_nonneg_left (le_opNorm T x) (norm_nonneg y)
          _ = ‖T‖ * ‖x‖ * ‖y‖ := by ring

lemma operator_inner (x y : H) :
    ⟪y, B.operator x⟫_ℂ = starRingEnd ℂ (B.form x y) := by
  have h := InnerProductSpace.continuousLinearMapOfBilin_apply B.continuous x y
  change ⟪B.operator x, y⟫_ℂ = B.form x y at h
  rw [← inner_conj_symm, h]

lemma operator_eq_of_inner {S : H →L[ℂ] H}
    (hS : ∀ x y, ⟪y, S x⟫_ℂ = starRingEnd ℂ (B.form x y)) :
    S = B.operator := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [← inner_conj_symm, hS]
  simp only [map_star, starRingEnd_apply, star_star]
  exact (InnerProductSpace.continuousLinearMapOfBilin_apply B.continuous x y).symm

lemma operator_ofOperator (T : H →L[ℂ] H) :
    (ofOperator T).operator = T := by
  symm
  apply (ofOperator T).operator_eq_of_inner
  intro x y
  simp [ofOperator]

/-- The same Riesz bridge for the weak-operator type used by spectral measures. -/
noncomputable def ofWOT (T : H →WOT[ℂ] H) : BoundedSesquilinearForm (H := H) :=
  ofOperator (ContinuousLinearMapWOT.toCLM T)

lemma operator_ofWOT (T : H →WOT[ℂ] H) :
    (ofWOT T).operator = ContinuousLinearMapWOT.toCLM T :=
  operator_ofOperator _

lemma operator_eq_zero_of_form_eq_zero
    (hB : ∀ x y, B.form x y = 0) : B.operator = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  have h := InnerProductSpace.continuousLinearMapOfBilin_apply B.continuous x y
  change ⟪B.operator x, y⟫_ℂ = B.form x y at h
  simpa [hB] using h

lemma operator_isSelfAdjoint
    (hherm : ∀ x y, B.form y x = starRingEnd ℂ (B.form x y)) :
    IsSelfAdjoint B.operator := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  calc
    ⟪B.operator x, y⟫_ℂ = starRingEnd ℂ ⟪y, B.operator x⟫_ℂ := by
      rw [inner_conj_symm]
    _ = starRingEnd ℂ (starRingEnd ℂ (B.form x y)) := by
      rw [B.operator_inner]
    _ = B.form x y := by simp
    _ = starRingEnd ℂ (B.form y x) := by
      rw [hherm]
    _ = ⟪x, B.operator y⟫_ℂ := (B.operator_inner y x).symm

end BoundedSesquilinearForm

end QuantumMechanics

end
