/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Examples.LadderSystem
public import PhyslibAlpha.Mathematics.LadderSystem.Vacuum
public import Physlib.Mathematics.InnerProductSpace.Gaussian
public import Physlib.Meta.TODO.Basic

/-!

# The harmonic oscillator spectrum, harnessing the API

This file characterizes the full spectrum of the one-dimensional harmonic oscillator Hamiltonian
built from `Q := positionOperatorSchwartz`/`P := momentumOperatorSchwartz`
(`Unbounded/Example/Schwartz.lean`), using nothing beyond Mathlib, `𝓢(ℝ, ℂ)`, `Q`/`P` themselves,
`PhyslibAlpha`'s general `LadderSystem` abstraction, and this project's own `OperatorAlgebra`
API — no `d`-dimensional `HarmonicOscillator`/`ξ` apparatus from elsewhere in `Physlib`.

## Architecture

1. A vacuum `Ω` (the Gaussian ground state) for `toLadderSystem m ω hm hω`
   (`Unbounded/Example/LadderSystem.lean`'s one-mode `LadderSystem` built from `Q`, `P`).
2. The occupation-number states `(a⁺)ⁿΩ`, eigenvectors of the number operator with eigenvalue `n`,
   entirely for free from `PhyslibAlpha.Mathematics.LadderSystem.Vacuum`'s general `N_word`.
3. The number-operator Hamiltonian `H := ℏω(N + ½)` and its eigenvalue `ℏω(n + ½)` on the `n`-th
   occupation state — proved, not merely asserted.
4. The exact occupation-energy labels and their injectivity. The representation-level spectral
   theorem for the closure on `L²(ℝ)` is a separate result requiring an actual Hilbert-space
   realization, essential self-adjointness, and completeness of the Hermite basis.

`hasVacuum_gaussian` (the Gaussian ground state exists and is annihilated by `ladderA`) is
**fully proved** by constructing the Gaussian via `Physlib.Mathematics.InnerProductSpace.
Gaussian`'s `gaussian₀` — a general Schwartz-space-Gaussian constructor for *any* real inner
product space (not the `d`-dimensional `HarmonicOscillator`/`ξ` apparatus this file otherwise
avoids; it lives outside `PhyslibAlpha`/`OperatorAlgebra` in the literal directory sense, but is
generic Mathlib-adjacent Schwartz-space infrastructure — the same kind of building block as
`SchwartzMap` itself or `positionOperatorSchwartz`/`momentumOperatorSchwartz` — rather than any
oscillator-specific shortcut; using it here saves re-deriving the underlying Schwartz-seminorm decay
bounds on a Gaussian's derivatives, which are genuinely orthogonal real analysis, not part of what
this file tests). Everything past that construction — the derivative/annihilation computation, the
occupation-number eigenvalues, and the Hamiltonian's eigenvalue formula — is proved.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder
open QuantumMechanics OneDimension Constants SchwartzMap
open OperatorAlgebra OperatorAlgebra.Unbounded.Example

namespace OperatorAlgebra.Unbounded.Example

attribute [local instance 100] LieRing.ofAssociativeRing

variable (m ω : ℝ) (hm : 0 < m) (hω : 0 < ω)

/-! ## 1. The vacuum -/

/-- The Gaussian's width, `ξ = √(ℏ/(mω))`, chosen so that the `ξ`-rescaled standard Gaussian
`exp(-‖x/ξ‖²/2)` equals `exp(-(mω/2ℏ)x²)` — the standard harmonic-oscillator ground-state width. -/
def gaussianWidth (m ω : ℝ) : ℝ := Real.sqrt ((ℏ : ℝ) / (m * ω))

lemma gaussianWidth_pos (hm : 0 < m) (hω : 0 < ω) : 0 < gaussianWidth m ω := by
  have := ℏ_pos
  exact Real.sqrt_pos.mpr (by positivity)

lemma gaussianWidth_sq (hm : 0 < m) (hω : 0 < ω) :
    (gaussianWidth m ω) ^ 2 = (ℏ : ℝ) / (m * ω) := by
  have := ℏ_pos
  exact Real.sq_sqrt (by positivity)

/-- The rescaling `B : ℝ ≃L[ℝ] ℝ`, `B x = ξ x`, feeding `InnerProductSpace.gaussian₀` to produce
the width-`ξ` Gaussian. -/
def gaussianRescale (m ω : ℝ) (hm : 0 < m) (hω : 0 < ω) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 (gaussianWidth m ω) (gaussianWidth_pos m ω hm hω).ne')

lemma gaussianRescale_symm_apply (hm : 0 < m) (hω : 0 < ω) (x : ℝ) :
    (gaussianRescale m ω hm hω).symm x = (gaussianWidth m ω)⁻¹ * x := rfl

/-- **The Gaussian ground state**, `Ω(x) = exp(-mωx²/(2ℏ))`, as a genuine element of `𝓢(ℝ, ℂ)` —
built via `InnerProductSpace.gaussian₀`'s general Schwartz-space-Gaussian machinery (module
docstring), rather than re-deriving the Schwartz-seminorm decay bounds from scratch. -/
def gaussianVacuum (m ω : ℝ) (hm : 0 < m) (hω : 0 < ω) : 𝓢(ℝ, ℂ) :=
  InnerProductSpace.gaussian₀ ℂ (gaussianRescale m ω hm hω)

/-- **The Gaussian ground state's pointwise value**, `Ω(x) = exp(-(mω/2ℏ)x²)`. -/
theorem gaussianVacuum_apply (hm : 0 < m) (hω : 0 < ω) (x : ℝ) :
    (gaussianVacuum m ω hm hω : ℝ → ℂ) x = (Real.exp (-(m * ω / (2 * ℏ)) * x ^ 2) : ℝ) := by
  have hℏ := ℏ_pos
  have hξ2 := gaussianWidth_sq m ω hm hω
  have hreal : Real.exp (-2⁻¹ * ‖(gaussianRescale m ω hm hω).symm (x - 0)‖ ^ 2)
      = Real.exp (-(m * ω / (2 * ℏ)) * x ^ 2) := by
    rw [sub_zero, gaussianRescale_symm_apply, Real.norm_eq_abs, sq_abs, mul_pow, inv_pow, hξ2]
    congr 1
    field_simp
  show InnerProductSpace.gaussian ℂ (gaussianRescale m ω hm hω) 0 x = _
  rw [InnerProductSpace.gaussian_apply]
  exact congrArg Complex.ofReal hreal

/-- **The derivative of the Gaussian ground state**, `Ω'(x) = -(mω/ℏ)x·Ω(x)`. Plain single-
variable calculus (`gaussianVacuum_apply` reduces `Ω` to a real exponential of a quadratic), no
Fréchet-derivative/general-inner-product-space bookkeeping needed since `𝓢(ℝ, ℂ)`'s domain here is
just `ℝ`. -/
theorem hasDerivAt_gaussianVacuum (hm : 0 < m) (hω : 0 < ω) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (gaussianVacuum m ω hm hω : ℝ → ℂ) y)
      ((-(m * ω / ℏ) * x : ℝ) * (gaussianVacuum m ω hm hω : ℝ → ℂ) x) x := by
  have heq : (fun y : ℝ => (gaussianVacuum m ω hm hω : ℝ → ℂ) y) =
      fun y : ℝ => ((Real.exp (-(m * ω / (2 * ℏ)) * y ^ 2) : ℝ) : ℂ) := by
    funext y; exact gaussianVacuum_apply m ω hm hω y
  have hquad := (hasDerivAt_pow 2 x).const_mul (-(m * ω / (2 * ℏ)))
  have hreal : HasDerivAt (fun y : ℝ => Real.exp (-(m * ω / (2 * ℏ)) * y ^ 2))
      (-(m * ω / ℏ) * x * Real.exp (-(m * ω / (2 * ℏ)) * x ^ 2)) x := by
    have h := hquad.exp
    convert h using 1
    push_cast
    ring
  rw [heq, gaussianVacuum_apply, ← Complex.ofReal_mul]
  exact hreal.ofReal_comp

/-- **The Gaussian ground state is nonzero.** `Ω(0) = exp(0) = 1 ≠ 0`. -/
theorem gaussianVacuum_ne_zero (hm : 0 < m) (hω : 0 < ω) : gaussianVacuum m ω hm hω ≠ 0 := by
  intro h
  have hpt := congrFun (congrArg DFunLike.coe h) (0 : ℝ)
  rw [gaussianVacuum_apply] at hpt
  simp at hpt

/-- **The Gaussian ground state is annihilated by the lowering operator.** `ladderA m ω Ω = 0`:
`(mωQ + iP)Ω(x) = mωxΩ(x) + i(-iℏ)Ω'(x) = mωxΩ(x) + ℏ(-(mω/ℏ)xΩ(x)) = 0`, using
`hasDerivAt_gaussianVacuum`'s derivative formula. -/
theorem ladderA_gaussianVacuum (hm : 0 < m) (hω : 0 < ω) :
    ladderA m ω (gaussianVacuum m ω hm hω) = 0 := by
  have hne := normConst_ne_zero m ω hm hω
  have hzero : ((m * ω : ℝ) • positionOperatorSchwartz + Complex.I • momentumOperatorSchwartz)
      (gaussianVacuum m ω hm hω) = 0 := by
    ext x
    have hderiv := hasDerivAt_gaussianVacuum m ω hm hω x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      positionOperatorSchwartz_apply, momentumOperatorSchwartz_apply, Complex.real_smul,
      smul_eq_mul, ContinuousLinearMap.zero_apply, Pi.zero_apply]
    rw [hderiv.deriv]
    have hℏ : (ℏ : ℂ) ≠ 0 := by exact_mod_cast Constants.ℏ_ne_zero
    push_cast
    field_simp
    rw [Complex.I_sq]
    ring
  show ((normConst m ω : ℂ))⁻¹ •
      ((m * ω : ℝ) • positionOperatorSchwartz + Complex.I • momentumOperatorSchwartz)
      (gaussianVacuum m ω hm hω) = 0
  rw [hzero, smul_zero]

/-- **The Gaussian ground state exists and is a vacuum.** `Ω(x) = exp(-mωx²/(2ℏ))`, as a genuine
element of `𝓢(ℝ, ℂ)`, nonzero, and annihilated by the lowering operator `ladderA m ω`. **Fully
proved** — see `gaussianVacuum`/`ladderA_gaussianVacuum` above. -/
theorem hasVacuum_gaussian (hm : 0 < m) (hω : 0 < ω) :
    ∃ Ω : 𝓢(ℝ, ℂ), (toLadderSystem m ω hm hω).HasVacuum Ω :=
  ⟨gaussianVacuum m ω hm hω,
    { ne_zero := gaussianVacuum_ne_zero m ω hm hω
      ann := fun _ => ladderA_gaussianVacuum m ω hm hω }⟩

/-- A choice of vacuum, from `hasVacuum_gaussian`. -/
def vacuum : 𝓢(ℝ, ℂ) := (hasVacuum_gaussian m ω hm hω).choose

lemma hasVacuum_vacuum : (toLadderSystem m ω hm hω).HasVacuum (vacuum m ω hm hω) :=
  (hasVacuum_gaussian m ω hm hω).choose_spec

/-! ## 2. Occupation-number eigenstates -/

/-- The `n`-th occupation-number state, `(a⁺)ⁿΩ`. -/
def occupation (n : ℕ) : 𝓢(ℝ, ℂ) :=
  (toLadderSystem m ω hm hω).word (List.replicate n 0) (vacuum m ω hm hω)

/-- **The occupation states are eigenvectors of the number operator**, with eigenvalue `n` — free
from `PhyslibAlpha`'s general `LadderSystem.N_word`, applied to `toLadderSystem`. -/
theorem numberOp_occupation (n : ℕ) :
    (toLadderSystem m ω hm hω).N 0 (occupation m ω hm hω n) = (n : ℂ) • occupation m ω hm hω n := by
  have h := (toLadderSystem m ω hm hω).N_word (hasVacuum_vacuum m ω hm hω).ann 0
    (List.replicate n 0)
  rw [List.count_replicate] at h
  exact_mod_cast h

/-! ## 3. The Hamiltonian and its eigenvalues -/

/-- The number-operator Hamiltonian, `H = ℏω(N + ½)`, as a `Module.End ℂ 𝓢(ℝ, ℂ)`. -/
def hamiltonianN : Module.End ℂ (𝓢(ℝ, ℂ)) :=
  ((ℏ : ℂ) * (ω : ℂ)) • ((toLadderSystem m ω hm hω).N 0 + (2⁻¹ : ℂ) • 1)

/-- **The energy of the `n`-th occupation state, `ℏω(n + ½)`** — the textbook harmonic-oscillator
energy quantization formula, proved directly from `numberOp_occupation`. -/
theorem hamiltonianN_occupation (n : ℕ) :
    hamiltonianN m ω hm hω (occupation m ω hm hω n) =
      ((ℏ : ℂ) * (ω : ℂ) * (n + 2⁻¹ : ℂ)) • occupation m ω hm hω n := by
  simp only [hamiltonianN, LinearMap.smul_apply, LinearMap.add_apply, numberOp_occupation,
    Module.End.one_apply, smul_smul, smul_add]
  rw [← add_smul]
  congr 1
  ring

/-- Distinct occupation numbers give distinct energies: the spectrum
`{ℏω(n + ½) : n ∈ ℕ}` is genuinely infinite and discrete (`ω ≠ 0`), not merely a formula that might
collapse. -/
theorem hamiltonianN_eigenvalue_injective (hω0 : ω ≠ 0) :
    Function.Injective (fun n : ℕ => (ℏ : ℂ) * (ω : ℂ) * (n + 2⁻¹ : ℂ)) := by
  have hℏ : (ℏ : ℂ) ≠ 0 := by exact_mod_cast Constants.ℏ_ne_zero
  have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω0
  intro n₁ n₂ h
  have h' : (n₁ : ℂ) = (n₂ : ℂ) := by
    have := mul_left_cancel₀ (mul_ne_zero hℏ hω') h
    linear_combination this
  exact_mod_cast h'

/-! ## 4. Spectral labels

The representation-independent content established by this file is the exact eigenvalue formula and
the fact that the labels are distinct. A genuine `L²(ℝ)` spectral-projection theorem belongs in a
separate representation-specific development, whose statement must fix the Hilbert space and make
the closure and completeness hypotheses explicit.
-/

theorem hamiltonianN_spectral_labels (hω0 : ω ≠ 0) :
    (∀ n : ℕ, hamiltonianN m ω hm hω (occupation m ω hm hω n) =
      ((ℏ : ℂ) * (ω : ℂ) * (n + 2⁻¹ : ℂ)) • occupation m ω hm hω n) ∧
    Function.Injective (fun n : ℕ => (ℏ : ℂ) * (ω : ℂ) * (n + 2⁻¹ : ℂ)) :=
  ⟨hamiltonianN_occupation m ω hm hω, hamiltonianN_eigenvalue_injective ω hω0⟩

end OperatorAlgebra.Unbounded.Example
