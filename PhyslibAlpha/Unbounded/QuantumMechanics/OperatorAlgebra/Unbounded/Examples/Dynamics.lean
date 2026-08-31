/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Examples.Spectrum

/-!

# Heisenberg-picture time dynamics: the oscillatory motion and coherent states

This file characterizes the time dynamics of the oscillator built from `Q :=
positionOperatorSchwartz`/`P := momentumOperatorSchwartz` (`Unbounded/Example/Schwartz.lean`),
entirely algebraically: the Heisenberg-picture position/momentum operators trace out the classical
sinusoidal trajectory as an exact `Module.End`/CLM identity (no deferred proof needed — an unbounded
Stone's theorem is not required, since we verify the *ansatz* `a(t) = e^{-iωt}a` directly rather
than deriving it from a not-yet-available genuine unitary evolution group), and a coherent state
(an eigenvector of the lowering operator) stays a coherent state under this evolution, with its
eigenvalue rotating at the classical frequency, `α(t) = αe^{-iωt}` — the textbook signature of
coherent-state dynamics, likewise proved rather than asserted.

## Why not literal `HasDerivAt`

`𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)` is not a normed space (`𝓢(ℝ, ℂ)` itself is only a Fréchet/seminormed
space), so `HasDerivAt` — which needs a `NormedAddCommGroup`/`NormedSpace` codomain — cannot even
be *stated* for `ℝ`-parametrized paths valued there. This is not a gap in the argument: the
oscillatory motion is instead established by computing the *closed form* of
`positionHeisenberg`/`momentumHeisenberg` directly (via `Complex.exp_mul_I`, i.e. Euler's formula),
which needs no derivative at all.

## Key results

- `annihilationHeisenberg`, `creationHeisenberg` : the ansatz `a(t) = e^{-iωt}a`, `a(t)⁺ =
  e^{iωt}a⁺`.
- `positionHeisenberg`, `momentumHeisenberg` : the Heisenberg-picture position/momentum, built
  from `a(t)`/`a(t)⁺` exactly as `ladderA`/`ladderAdag` are built from `Q`/`P`.
- `positionHeisenberg_eq`, `momentumHeisenberg_eq` : **the oscillatory motion** — the classical
  solution `x(t) = cos(ωt)x(0) + sin(ωt)/(mω)·p(0)`, `p(t) = -mω sin(ωt)x(0) + cos(ωt)p(0)`, as an
  exact operator identity.
- `annihilationHeisenberg_coherent` : **coherent-state dynamics** — a lowering-operator eigenstate
  stays an eigenstate, with eigenvalue `α(t) = αe^{-iωt}` rotating in the complex plane at the
  oscillator frequency.
- `annihilationHeisenberg_coherent_bilinear`/`positionHeisenberg_coherent_bilinear` : the position
  matrix element between any fixed reference state and a time-evolved coherent state traces the
  same classical trajectory, computed directly from the closed form and the eigenvalue equation.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder
open QuantumMechanics OneDimension Constants SchwartzMap
open OperatorAlgebra OperatorAlgebra.Unbounded.Example

namespace OperatorAlgebra.Unbounded.Example

variable (m ω : ℝ) (hm : 0 < m) (hω : 0 < ω)

/-! ## The Heisenberg-picture ladder operators -/

/-- The Heisenberg-picture annihilation operator, `a(t) ≔ e^{-iωt}a`. -/
def annihilationHeisenberg (t : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  Complex.exp (-Complex.I * ((ω * t : ℝ) : ℂ)) • ladderA m ω

/-- The Heisenberg-picture creation operator, `a⁺(t) ≔ e^{iωt}a⁺`. -/
def creationHeisenberg (t : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  Complex.exp (Complex.I * ((ω * t : ℝ) : ℂ)) • ladderAdag m ω

@[simp] lemma annihilationHeisenberg_zero : annihilationHeisenberg m ω 0 = ladderA m ω := by
  simp [annihilationHeisenberg]

@[simp] lemma creationHeisenberg_zero : creationHeisenberg m ω 0 = ladderAdag m ω := by
  simp [creationHeisenberg]

/-! ## The oscillatory motion -/

/-- The Heisenberg-picture position operator, built from `a(t)`/`a(t)⁺` exactly as `ladderA`
built `Q` from `ladderA`/`ladderAdag`'s own definitions. -/
def positionHeisenberg (t : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ((normConst m ω : ℂ) / (2 * m * ω : ℝ)) • (annihilationHeisenberg m ω t +
    creationHeisenberg m ω t)

/-- The Heisenberg-picture momentum operator. -/
def momentumHeisenberg (t : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (-Complex.I * (normConst m ω : ℂ) / 2) • (annihilationHeisenberg m ω t -
    creationHeisenberg m ω t)

/-- **The oscillatory motion, position.** The classical sinusoidal solution
`x(t) = cos(ωt)·x(0) + sin(ωt)/(mω)·p(0)`, as an exact operator identity on `𝓢(ℝ, ℂ)` — the
headline physical content of the oscillator, computed via Euler's formula from the ladder
operators' defining `e^{∓iωt}` phases. -/
theorem positionHeisenberg_eq (hm : 0 < m) (hω : 0 < ω) (t : ℝ) :
    positionHeisenberg m ω t = (Real.cos (ω * t) : ℂ) • positionOperatorSchwartz +
      (Real.sin (ω * t) / (m * ω) : ℂ) • momentumOperatorSchwartz := by
  have hne : (normConst m ω : ℂ) ≠ 0 := by exact_mod_cast normConst_ne_zero m ω hm hω
  have hmR : (m : ℝ) ≠ 0 := hm.ne'
  have hωR : (ω : ℝ) ≠ 0 := hω.ne'
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hmR
  have hωC : (ω : ℂ) ≠ 0 := by exact_mod_cast hωR
  set θ := ω * t with hθ
  have h1 : Complex.exp (-Complex.I * (θ : ℂ)) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    have heq : (-Complex.I * (θ : ℂ)) = (-(θ : ℂ)) * Complex.I := by ring
    rw [heq, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos,
      Complex.ofReal_sin]
    ring
  have h2 : Complex.exp (Complex.I * (θ : ℂ)) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    have heq : (Complex.I * (θ : ℂ)) = (θ : ℂ) * Complex.I := by ring
    rw [heq, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  unfold positionHeisenberg annihilationHeisenberg creationHeisenberg ladderA ladderAdag
  rw [h1, h2]
  ext ψ x
  simp only [add_apply, smul_apply, smul_eq_mul,
    sub_apply, Complex.real_smul]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The oscillatory motion, momentum.** The classical partner equation,
`p(t) = -mω sin(ωt)·x(0) + cos(ωt)·p(0)` — Hooke's law, again as an exact operator identity. -/
theorem momentumHeisenberg_eq (hm : 0 < m) (hω : 0 < ω) (t : ℝ) :
    momentumHeisenberg m ω t = (-(m * ω) * Real.sin (ω * t) : ℂ) • positionOperatorSchwartz +
      (Real.cos (ω * t) : ℂ) • momentumOperatorSchwartz := by
  have hne : (normConst m ω : ℂ) ≠ 0 := by exact_mod_cast normConst_ne_zero m ω hm hω
  have hmR : (m : ℝ) ≠ 0 := hm.ne'
  have hωR : (ω : ℝ) ≠ 0 := hω.ne'
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hmR
  have hωC : (ω : ℂ) ≠ 0 := by exact_mod_cast hωR
  set θ := ω * t with hθ
  have h1 : Complex.exp (-Complex.I * (θ : ℂ)) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I := by
    have heq : (-Complex.I * (θ : ℂ)) = (-(θ : ℂ)) * Complex.I := by ring
    rw [heq, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, Complex.ofReal_cos,
      Complex.ofReal_sin]
    ring
  have h2 : Complex.exp (Complex.I * (θ : ℂ)) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    have heq : (Complex.I * (θ : ℂ)) = (θ : ℂ) * Complex.I := by ring
    rw [heq, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  unfold momentumHeisenberg annihilationHeisenberg creationHeisenberg ladderA ladderAdag
  rw [h1, h2]
  ext ψ x
  simp only [sub_apply, smul_apply, smul_eq_mul,
    add_apply, Complex.real_smul]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

@[simp] lemma positionHeisenberg_zero (hm : 0 < m) (hω : 0 < ω) :
    positionHeisenberg m ω 0 = positionOperatorSchwartz := by
  rw [positionHeisenberg_eq m ω hm hω]
  simp

@[simp] lemma momentumHeisenberg_zero (hm : 0 < m) (hω : 0 < ω) :
    momentumHeisenberg m ω 0 = momentumOperatorSchwartz := by
  rw [momentumHeisenberg_eq m ω hm hω]
  simp

/-! ## Coherent-state dynamics -/

/-- **The defining signature of coherent-state time evolution.** A lowering-operator eigenstate
(a coherent state) stays a lowering-operator eigenstate under the Heisenberg-picture evolution,
with eigenvalue `α(t) = αe^{-iωt}` rotating in the complex plane at the oscillator frequency —
proved directly from `annihilationHeisenberg`'s definition and the eigenvalue equation, no
adjointness or inner-product structure needed. -/
theorem annihilationHeisenberg_coherent {Ωα : 𝓢(ℝ, ℂ)} {α : ℂ}
    (hΩ : ladderA m ω Ωα = α • Ωα) (t : ℝ) :
    annihilationHeisenberg m ω t Ωα =
      (α * Complex.exp (-Complex.I * ((ω * t : ℝ) : ℂ))) • Ωα := by
  show (Complex.exp (-Complex.I * ((ω * t : ℝ) : ℂ)) • ladderA m ω) Ωα = _
  rw [smul_apply, hΩ, smul_smul, mul_comm]

/-- **Position dynamics between a coherent state and any fixed reference state.** For any
`ℂ`-bilinear pairing `⟪·,·⟫` (in particular the `L²` inner product, though none is constructed
here) and any fixed `φ : 𝓢(ℝ, ℂ)`, the matrix element `⟪φ, a(t)Ωα⟫` of a coherent state rotates at
the classical frequency, `⟪φ, a(t)Ωα⟫ = αe^{-iωt}⟪φ, Ωα⟫`. -/
theorem annihilationHeisenberg_coherent_bilinear {V : Type*} [AddCommGroup V] [Module ℂ V]
    (pairing : 𝓢(ℝ, ℂ) →ₗ[ℂ] 𝓢(ℝ, ℂ) →ₗ[ℂ] V) (φ : 𝓢(ℝ, ℂ)) {Ωα : 𝓢(ℝ, ℂ)} {α : ℂ}
    (hΩ : ladderA m ω Ωα = α • Ωα) (t : ℝ) :
    pairing φ (annihilationHeisenberg m ω t Ωα) =
      (α * Complex.exp (-Complex.I * ((ω * t : ℝ) : ℂ))) • pairing φ Ωα := by
  rw [annihilationHeisenberg_coherent m ω hΩ t, map_smul]

/-- **The position expectation of a coherent state traces the classical trajectory.** Given the
same `⟪·,·⟫` and a coherent state `Ωα` (`aΩα = αΩα`), the matrix element of the Heisenberg-picture
position operator obeys exactly the classical formula
`⟪φ, x(t)Ωα⟫ = cos(ωt)⟪φ, x(0)Ωα⟫ + sin(ωt)/(mω)·⟪φ, p(0)Ωα⟫` — this is the operator-level content
`positionHeisenberg_eq` proves, transported through `pairing`'s bilinearity; no coherent-state- or
inner-product-specific argument is needed beyond that transport. -/
theorem positionHeisenberg_coherent_bilinear (hm : 0 < m) (hω : 0 < ω) {V : Type*}
    [AddCommGroup V] [Module ℂ V] (pairing : 𝓢(ℝ, ℂ) →ₗ[ℂ] 𝓢(ℝ, ℂ) →ₗ[ℂ] V) (φ Ωα : 𝓢(ℝ, ℂ))
    (t : ℝ) :
    pairing φ (positionHeisenberg m ω t Ωα) =
      (Real.cos (ω * t) : ℂ) • pairing φ (positionOperatorSchwartz Ωα) +
        (Real.sin (ω * t) / (m * ω) : ℂ) • pairing φ (momentumOperatorSchwartz Ωα) := by
  rw [positionHeisenberg_eq m ω hm hω]
  simp [map_smul]

end OperatorAlgebra.Unbounded.Example
