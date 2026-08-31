/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.HarmonicOscillator.Basic
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.Multiplication.Spectral
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Core.RealAnalytic
public import Physlib.Meta.TODO.Basic
/-!

# Essential self-adjointness of the one-dimensional harmonic oscillator Hamiltonian

## i. Overview

This module studies essential self-adjointness of `HarmonicOscillator.hamiltonian` for the
one-dimensional oscillator (`Q : HarmonicOscillator 1`), as a genuine `LinearPMap` on the real
Hilbert space `SpaceDHilbertSpace 1 = QuantumMechanics.HarmonicOscillator.HS Q`.

Recall `Q.hamiltonian = Q.kineticOperator + Q.potentialOperator`, where
`Q.kineticOperator = (2 * Q.m)⁻¹ • momentumSqOperator` has domain the Schwartz submodule
(`momentumSqOperator_domain_eq`) and `Q.potentialOperator = 𝓜 volume (ofReal ∘ Q.potentialFunction)`
is a *maximal* multiplication operator (self-adjoint on its own, large domain,
`mulOperator_isSelfAdjoint_ofReal`).

We establish:
- `hamiltonian_domain_eq` : `Q.hamiltonian.domain = SchwartzSubmodule 1`, i.e. the Hamiltonian's
    domain is exactly the Schwartz submodule (the potential operator's domain is strictly larger,
    but does not constrain the intersection).
- `hamiltonian_isSymmetric` : `Q.hamiltonian.IsSymmetric`, from `momentumSqOperator_isSymmetric`
    (built from `IsSymmetric.pow`/`.sum` applied to the individual symmetric `momentumOperator`s)
    and the self-adjointness (hence symmetry) of the maximal potential multiplication operator.
- `hamiltonian_hasDenseDomain` : `Q.hamiltonian.HasDenseDomain`, since the Schwartz submodule is
    dense.

Given these three genuinely-proved facts, this low-level module exposes essential self-adjointness
through an explicit defect-index certificate.  The concrete proof for the actual differential
operator is supplied downstream in `DifferentialCore.lean`: there the Hermite functions are shown
to be a dense real-eigenvector family for `Q.hamiltonian`, and the reusable
`EssentialSelfAdjointCore.ofDenseRealEigenvectors` theorem discharges both defect spaces.
The certificate remains available here for clients that already have deficiency-index data.

## ii. Key results

- `hamiltonian_domain_eq` : `Q.hamiltonian.domain = SchwartzSubmodule 1`.
- `hamiltonian_isSymmetric` : `Q.hamiltonian.IsSymmetric`.
- `hamiltonian_hasDenseDomain` : `Q.hamiltonian.HasDenseDomain`.
- `HarmonicOscillatorDefectCertificate` : the two analytic deficiency-index inputs.
- `hamiltonian_defectIndexCertificate` : the von Neumann certificate from those inputs.
- `hamiltonian_isEssentiallySelfAdjoint` : `Q.hamiltonian.IsEssentiallySelfAdjoint`, conditional on
    the explicit certificate.

## iii. Table of contents

- A. The potential function is real-analytic (temperate growth)
- B. Domain of the Hamiltonian
- C. Symmetry and density
- D. The von Neumann defect-index criterion

## iv. References

- [Reed and Simon, *Methods of Modern Mathematical Physics, Vol. II: Fourier Analysis,
  Self-Adjointness*][Reed1975]
- [Konrad Schmüdgen, *Unbounded Self-Adjoint Operators on Hilbert Space*][Schmudgen2012]

-/

@[expose] public section

namespace QuantumMechanics
namespace HarmonicOscillator

noncomputable section

open Complex LinearPMap MeasureTheory SpaceDHilbertSpace SchwartzSubmodule

variable (Q : HarmonicOscillator 1)

/-!
## A. The potential function is real-analytic (temperate growth)
-/

/-- Explicit formula for the one-dimensional harmonic oscillator potential in terms of the
  single coordinate `x 0`. -/
lemma potentialFunction_one_eq (x : Space 1) :
    Q.potentialFunction x = (2⁻¹ * Q.m) * (Q.ω 0) ^ 2 * (x 0) ^ 2 := by
  simp only [potentialFunction_eq, Function.comp_apply, potentialQuadraticForm,
    Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', potentialMatrix_mulVec, dotProduct, Fin.sum_univ_one,
    Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  ring

/-- The one-dimensional harmonic oscillator potential, complexified, is a.e. strongly measurable. -/
lemma ofReal_potentialFunction_aestronglyMeasurable :
    AEStronglyMeasurable (ofReal ∘ Q.potentialFunction) volume :=
  (Complex.continuous_ofReal.comp Q.potentialFunction_continuous).aestronglyMeasurable

/-- `Complex.ofReal ∘ coord 0` has temperate growth, being `Complex.ofReal` composed with a
  continuous linear functional on `Space 1`. -/
lemma ofReal_coord_hasTemperateGrowth :
    Function.HasTemperateGrowth (fun x : Space 1 ↦ (ofReal (x 0))) := by
  have h : (fun x : Space 1 ↦ (ofReal (x 0) : ℂ)) = ofReal ∘ (Space.coordCLM (0 : Fin 1)) := by
    funext x
    simp [Space.coordCLM_apply, Space.coord_apply]
  rw [h]
  exact Function.Complex.hasTemperateGrowth_ofReal.comp
    (Space.coordCLM (0 : Fin 1)).hasTemperateGrowth

/-- The complexified potential function has temperate growth: it is a scalar multiple of the
  square of a continuous linear functional composed with `Complex.ofReal`. -/
lemma potentialFunction_hasTemperateGrowth :
    Function.HasTemperateGrowth (ofReal ∘ Q.potentialFunction) := by
  have h : (ofReal ∘ Q.potentialFunction)
      = fun x ↦ ((2⁻¹ * Q.m) * (Q.ω 0) ^ 2 : ℂ) * (ofReal (x 0)) ^ 2 := by
    funext x
    simp [Q.potentialFunction_one_eq]
  rw [h]
  exact (Function.HasTemperateGrowth.const _).mul (ofReal_coord_hasTemperateGrowth.pow 2)

/-!
## B. Domain of the Hamiltonian
-/

/-- The Schwartz submodule is contained in the domain of the potential operator: Schwartz
  functions remain square-integrable after multiplication by a polynomially-bounded function. -/
lemma schwartzSubmodule_le_potentialOperator_domain :
    SchwartzSubmodule 1 ≤ Q.potentialOperator.domain :=
  mulOperator_domain_ge_of_hasTemperateGrowth Q.potentialFunction_hasTemperateGrowth volume

/-- `Q.hamiltonian.domain = SchwartzSubmodule 1`: since `Q.kineticOperator`'s domain is exactly
  the Schwartz submodule and the potential operator's (larger) domain does not further constrain
  the intersection. -/
lemma hamiltonian_domain_eq : Q.hamiltonian.domain = SchwartzSubmodule 1 := by
  rw [hamiltonain_eq, add_domain, kineticOperator, smul_domain, momentumSqOperator_domain_eq]
  exact inf_eq_left.mpr Q.schwartzSubmodule_le_potentialOperator_domain

/-!
## C. Symmetry and density
-/

/-- The squared momentum operator is symmetric: it agrees with `(momentumOperator i) ^ 2`
  (via `compRestricted_eq_comp`), and squares of symmetric operators are symmetric. -/
lemma momentumSqOperator_isSymmetric : (momentumSqOperator (d := 1)).IsSymmetric := by
  refine IsSymmetric.sum fun i ↦ ?_
  rw [← compRestricted_eq_comp (momentumOperator_range i), ← mul_def]
  have h := (momentumOperator_isSymmetric i).pow 2
  rwa [pow_succ, pow_one] at h

/-- The potential operator is symmetric, as a maximal real multiplication operator (hence
  self-adjoint, in particular symmetric). -/
lemma potentialOperator_isSymmetric : Q.potentialOperator.IsSymmetric := by
  have hself : IsSelfAdjoint (𝓜 volume (ofReal ∘ Q.potentialFunction)) :=
    mulOperator_isSelfAdjoint_ofReal Q.ofReal_potentialFunction_aestronglyMeasurable
      (by funext x; simp [Function.comp])
  exact LinearPMap.IsSelfAdjoint.isSymmetric hself

/-- The harmonic oscillator Hamiltonian is symmetric on its (Schwartz) domain. -/
lemma hamiltonian_isSymmetric : Q.hamiltonian.IsSymmetric := by
  rw [hamiltonain_eq]
  exact (momentumSqOperator_isSymmetric.real_smul (2 * Q.m)⁻¹).add Q.potentialOperator_isSymmetric

/-- The harmonic oscillator Hamiltonian has dense domain, since the Schwartz submodule is
  dense in `SpaceDHilbertSpace 1`. -/
lemma hamiltonian_hasDenseDomain : Q.hamiltonian.HasDenseDomain := by
  rw [hasDenseDomain_def, Q.hamiltonian_domain_eq]
  exact SchwartzSubmodule.dense 1 volume

/-!
## D. The von Neumann defect-index criterion
-/

/-- The remaining model-specific input is intentionally a data object.  A proof of this structure
requires the classical deficiency-ODE argument (or an independently established graph-core/
Hermite-density theorem); neither is supplied by the reusable operator-algebra layer. -/
structure HarmonicOscillatorDefectCertificate where
  plus : Q.hamiltonian.defectNumber I = 0
  minus : Q.hamiltonian.defectNumber (-I) = 0

lemma hamiltonian_defectNumber_I_eq_zero
    (C : HarmonicOscillatorDefectCertificate Q) : Q.hamiltonian.defectNumber I = 0 :=
  C.plus

lemma hamiltonian_defectNumber_negI_eq_zero
    (C : HarmonicOscillatorDefectCertificate Q) : Q.hamiltonian.defectNumber (-I) = 0 :=
  C.minus

/-- The von Neumann defect-index certificate for `Q.hamiltonian`, from the explicit analytic input.
The certificate is intentionally an argument rather than an opaque theorem. -/
lemma hamiltonian_defectIndexCertificate
    (C : HarmonicOscillatorDefectCertificate Q) :
    OperatorAlgebra.DefectIndexCertificate Q.hamiltonian where
  symmetric := Q.hamiltonian_isSymmetric
  dense := Q.hamiltonian_hasDenseDomain
  plus := Q.hamiltonian_defectNumber_I_eq_zero C
  minus := Q.hamiltonian_defectNumber_negI_eq_zero C

/-- The harmonic oscillator Hamiltonian (`d = 1`) is essentially self-adjoint, conditional on the
  two explicit analytic facts recorded in `hamiltonian_defectIndexCertificate`. -/
lemma hamiltonian_isEssentiallySelfAdjoint
    (C : HarmonicOscillatorDefectCertificate Q) : Q.hamiltonian.IsEssentiallySelfAdjoint :=
  (Q.hamiltonian_defectIndexCertificate C).essentiallySelfAdjoint

/-!
## E. The quantum-system handoff

The following declarations provide the former top-level handoff API for the oscillator.  The only
model-specific input is the explicit deficiency certificate above; once it is supplied,
the `QuantumSystem` uses the canonical self-adjoint closure, exactly as required by the general
unbounded-operator API.
-/

/-- The one-dimensional harmonic oscillator Hamiltonian is essentially self-adjoint when its
deficiency spaces are discharged by `C`. -/
lemma hamiltonian_essentially_self_adjoint
    (C : HarmonicOscillatorDefectCertificate Q) : Q.hamiltonian.IsEssentiallySelfAdjoint :=
  Q.hamiltonian_isEssentiallySelfAdjoint C

/-- The quantum system determined by the one-dimensional oscillator Hamiltonian and its
self-adjoint closure. -/
def toQuantumSystem (C : HarmonicOscillatorDefectCertificate Q) : QuantumSystem :=
  QuantumSystem.mkESA (Q.hamiltonian_essentially_self_adjoint C)

end
end HarmonicOscillator
end QuantumMechanics
end
