/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import Physlib.QuantumMechanics.HarmonicOscillator.LadderOperators
public import Physlib.Mathematics.InnerProductSpace.Gaussian
/-!

# A vacuum state for the harmonic oscillator

## i. Overview

The standard Gaussian `stdGaussian (Space d) ℂ` (`x ↦ exp(-‖x‖²/2)`, from
`Physlib.Mathematics.InnerProductSpace.Gaussian`) is annihilated by every `annihilationCLM i`,
*provided* every mode has unit characteristic length (`Q.ξ i = 1`) -- i.e. it is a genuine
`LadderSystem.HasVacuum` witness for `Q.toLadderSystem` in that case. Combined with
`Physlib.Mathematics.LadderSystem.OccupationBasis`/`SymmetricPower`, this makes the occupation-
number basis and the degeneracy formula `(d+n-1).choose n` concrete facts about a real
Schwartz-space state, not just available-but-unused machinery.

**Scope.** The general (anisotropic, arbitrary `m`, `ω`) oscillator's vacuum is the *rescaled*
Gaussian `exp(-∑ᵢ xᵢ²/(2ξᵢ²))`, not the standard one -- constructing that rescaling as a
genuine `ContinuousLinearEquiv` on `Space d` is a real, separate next step, not attempted
here. What's proved here is unconditional and reusable regardless: the derivative identity
for the standard Gaussian itself.

## ii. Key results

- `deriv_stdGaussian` : the coordinate derivative of the standard Gaussian,
    `∂ᵢ Ω = -xᵢ • Ω`.
- `annihilationCLM_stdGaussian_of_xi_eq_one` : every `annihilationCLM i` kills the standard
    Gaussian, provided `Q.ξ i = 1`.
- `hasVacuum_stdGaussian_of_forall_xi_eq_one` : `stdGaussian (Space d) ℂ` is a genuine vacuum for
    `Q.toLadderSystem`, provided `∀ i, Q.ξ i = 1`.

## iii. References

-/

@[expose] public section

namespace QuantumMechanics
namespace HarmonicOscillator
noncomputable section
open Complex Constants InnerProductSpace
open ContinuousLinearMap SchwartzMap

variable {d : ℕ} (Q : HarmonicOscillator d)

/-- The real-valued Gaussian `exp(-‖x‖²/2)`'s coordinate derivative,
`∂ᵢ g = -xᵢ · g`. -/
private theorem deriv_realGaussian (x : Space d) (i : Fin d) :
    Space.deriv i (fun x : Space d => Real.exp (-2⁻¹ * ‖x‖ ^ 2)) x =
      -x i * Real.exp (-2⁻¹ * ‖x‖ ^ 2) := by
  have hsq : DifferentiableAt ℝ (fun x : Space d => ‖x‖ ^ 2) x :=
    Space.norm_sq_differentiable.differentiableAt
  have hdiff2 : DifferentiableAt ℝ Real.exp (-2⁻¹ * ‖x‖ ^ 2) := Real.differentiableAt_exp
  have hdiff3 : DifferentiableAt ℝ (fun x : Space d => -2⁻¹ * ‖x‖ ^ 2) x := hsq.const_mul _
  change Space.deriv i (Real.exp ∘ (fun x : Space d => -2⁻¹ * ‖x‖ ^ 2)) x = _
  rw [Space.deriv_eq, fderiv_comp x hdiff2 hdiff3, fderiv_const_mul hsq (-2⁻¹ : ℝ),
    fderiv_norm_sq_apply]
  simp [Real.deriv_exp]

/-- `stdGaussian (Space d) ℂ`'s pointwise value is the real-valued Gaussian, cast to `ℂ`. -/
private theorem stdGaussian_apply' (x : Space d) :
    (stdGaussian (Space d) ℂ : Space d → ℂ) x = Real.exp (-2⁻¹ * ‖x‖ ^ 2) := by
  simp [stdGaussian, gaussian₀, gaussian_apply]

/-- The coordinate derivative of the standard Gaussian, `∂ᵢ Ω = -xᵢ • Ω`. -/
theorem deriv_stdGaussian (x : Space d) (i : Fin d) :
    Space.deriv i (fun x : Space d => (stdGaussian (Space d) ℂ : Space d → ℂ) x) x =
      (-x i : ℂ) * (stdGaussian (Space d) ℂ : Space d → ℂ) x := by
  have hsq : DifferentiableAt ℝ (fun x : Space d => Real.exp (-2⁻¹ * ‖x‖ ^ 2)) x := by
    have hsq' : DifferentiableAt ℝ (fun x : Space d => ‖x‖ ^ 2) x :=
      Space.norm_sq_differentiable.differentiableAt
    exact Real.differentiableAt_exp.comp x (hsq'.const_mul (-2⁻¹ : ℝ))
  have heq : (fun x : Space d => (stdGaussian (Space d) ℂ : Space d → ℂ) x) =
      Complex.ofRealCLM ∘ (fun x : Space d => Real.exp (-2⁻¹ * ‖x‖ ^ 2)) := by
    funext x
    simp
  rw [heq, Space.deriv_eq, fderiv_comp x Complex.ofRealCLM.differentiableAt hsq]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv]
  rw [show (fderiv ℝ (fun x : Space d => Real.exp (-2⁻¹ * ‖x‖ ^ 2)) x) (Space.basis i) =
      Space.deriv i (fun x => Real.exp (-2⁻¹ * ‖x‖ ^ 2)) x from (Space.deriv_eq i _ x).symm,
    deriv_realGaussian, stdGaussian_apply', Complex.ofRealCLM_apply]
  push_cast
  ring

/-!

## Killing the standard Gaussian

-/

/-- The momentum operator applied to the standard Gaussian,
`𝐩ᵢ Ω = -iℏ·(-xᵢ)Ω = iℏxᵢ·Ω`. -/
theorem momentumCLM_stdGaussian (i : Fin d) (x : Space d) :
    (𝐩[d] i (stdGaussian (Space d) ℂ) : 𝓢(Space d, ℂ)) x =
      (I * ℏ * x i : ℂ) * (stdGaussian (Space d) ℂ : Space d → ℂ) x := by
  rw [momentumCLM_apply]
  show -I * ℏ * Space.deriv i (fun x => (stdGaussian (Space d) ℂ : Space d → ℂ) x) x = _
  rw [deriv_stdGaussian]
  ring

/-- Every `annihilationCLM i` kills the standard Gaussian, provided that mode has unit
characteristic length. -/
theorem annihilationCLM_stdGaussian_of_xi_eq_one (i : Fin d) (hξ : Q.ξ i = 1) :
    Q.annihilationCLM i (stdGaussian (Space d) ℂ) = 0 := by
  have hℏ : (ℏ : ℂ) ≠ 0 := by exact_mod_cast Constants.ℏ_ne_zero
  ext x
  rw [annihilationCLM_apply_fun]
  simp only [smul_apply, add_apply, smul_eq_mul, zero_apply, positionCLM_apply]
  rw [show (𝐩 i) (stdGaussian (Space d) ℂ) x =
      (𝐩[d] i (stdGaussian (Space d) ℂ) : 𝓢(Space d, ℂ)) x from rfl,
    momentumCLM_stdGaussian, hξ]
  field_simp
  norm_num [Complex.I_sq]

/-- **`stdGaussian (Space d) ℂ` is a genuine vacuum** for `Q.toLadderSystem`, provided every
mode has unit characteristic length. -/
theorem hasVacuum_stdGaussian_of_forall_xi_eq_one (hξ : ∀ i, Q.ξ i = 1) :
    Q.toLadderSystem.HasVacuum (stdGaussian (Space d) ℂ) where
  ne_zero := by
    intro h
    have hpt := congrFun (congrArg DFunLike.coe h) (⟨fun _ => 0⟩ : Space d)
    simp at hpt
  ann i := by
    show (Q.annihilationCLM i).toLinearMap (stdGaussian (Space d) ℂ) = 0
    rw [show (Q.annihilationCLM i).toLinearMap (stdGaussian (Space d) ℂ) =
        Q.annihilationCLM i (stdGaussian (Space d) ℂ) from rfl,
      Q.annihilationCLM_stdGaussian_of_xi_eq_one i (hξ i)]

end
end HarmonicOscillator
end QuantumMechanics
