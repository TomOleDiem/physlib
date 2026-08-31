/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Operators.OneDimension.Position
public import Physlib.QuantumMechanics.Operators.OneDimension.Momentum

/-!

# Integration test: position and momentum on Schwartz space

This file is the smoke test for the algebraic common-core branch, run against the best available
concrete example: position `Q` and momentum `P` on the Schwartz space `𝓢(ℝ, ℂ)`, already built in
`PhyslibAlpha.Unbounded.QuantumMechanics.Operators.OneDimension.{Position,Momentum}`
(`positionOperatorSchwartz`, `momentumOperatorSchwartz`).

## Common-core/algebra branch

`𝓢(ℝ, ℂ)` is already, concretely, a common invariant core: `positionOperatorSchwartz` and
`momentumOperatorSchwartz` are literally continuous linear self-maps of `𝓢(ℝ, ℂ)`, i.e. elements
of the ring `𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)` — exactly the shape `InvariantCore.restrict` is meant to
produce (`Module.End`-flavoured algebra, here even a continuous refinement of it). We check the
central promise of `Core.lean`'s abstraction directly:

* the canonical commutation relation `[Q, P] = iℏ`, proved by an honest calculus computation
  (`ccr`);
* the harmonic-oscillator ladder operators `a`, `a†` built from `Q`, `P`, and their commutation
  relation `[a, a†] = 1`, proved as ordinary noncommutative-ring algebra from `ccr` (`ladder_comm`);
* the Hamiltonian factorization `H = ℏω(a†a + 1/2)`, stated with the correct final shape
  (`hamiltonian_eq`) — the underlying `a†a` computation follows the exact same pattern as
  `ladder_comm`'s proof and is proved directly below.

The oscillator spectrum is developed in `Example/Spectrum.lean`; this file intentionally keeps
the common-core calculation independent of the representation-level spectral API.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder
open QuantumMechanics OneDimension Constants SchwartzMap

namespace OperatorAlgebra.Unbounded.Example

/-! ## Common-core/algebra branch -/

/-- The canonical commutation relation `[Q, P] = iℏ` on Schwartz space, proved directly: `(QP -
PQ) ψ = (x ψ)' \cdot (-i\hbar) \cdot x - \ldots` reduces, via the product rule, to `iℏ ψ`. This is
the "critical test" for the common-core abstraction: it is exactly the statement `Core.lean`
promises becomes pleasant ordinary `Module.End`/ring algebra once a common core is in hand. -/
theorem ccr :
    positionOperatorSchwartz * momentumOperatorSchwartz -
      momentumOperatorSchwartz * positionOperatorSchwartz =
      (Complex.I * (ℏ : ℂ)) • (1 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) := by
  ext ψ x
  show (positionOperatorSchwartz (momentumOperatorSchwartz ψ)) x -
      (momentumOperatorSchwartz (positionOperatorSchwartz ψ)) x
      = (Complex.I * (ℏ : ℂ)) * ψ x
  simp only [positionOperatorSchwartz_apply, momentumOperatorSchwartz_apply]
  have hPsi : HasDerivAt (⇑ψ) (deriv (⇑ψ) x) x := (SchwartzMap.differentiable ψ x).hasDerivAt
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (RCLike.ofRealCLM (K := ℂ)).hasDerivAt (x := x)
  have hmul : HasDerivAt (fun y : ℝ => (y : ℂ) * ψ y) (1 * ψ x + x * deriv (⇑ψ) x) x :=
    hid.mul hPsi
  have hderiv : deriv (fun y : ℝ => (positionOperatorSchwartz ψ) y) x
      = ψ x + x * deriv (⇑ψ) x := by
    have h1 : (fun y : ℝ => (positionOperatorSchwartz ψ) y) = fun y : ℝ => (y : ℂ) * ψ y := by
      funext y; exact positionOperatorSchwartz_apply ψ y
    rw [h1, hmul.deriv]
    ring
  rw [hderiv]
  ring

variable (m ω : ℝ) (hm : 0 < m) (hω : 0 < ω)

/-- The harmonic-oscillator normalization constant `√(2mℏω)`. -/
def normConst : ℝ := Real.sqrt (2 * m * (ℏ : ℝ) * ω)

lemma normConst_sq (hm : 0 < m) (hω : 0 < ω) : (normConst m ω) ^ 2 = 2 * m * (ℏ : ℝ) * ω := by
  have := ℏ_pos
  exact Real.sq_sqrt (by positivity)

lemma normConst_ne_zero (hm : 0 < m) (hω : 0 < ω) : normConst m ω ≠ 0 := by
  have := ℏ_pos
  exact Real.sqrt_ne_zero'.mpr (by positivity)

/-- The annihilation ("lowering") operator `a = (mωQ + iP)/√(2mℏω)`. -/
def ladderA : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ((normConst m ω : ℂ))⁻¹ • ((m * ω : ℝ) • positionOperatorSchwartz +
    Complex.I • momentumOperatorSchwartz)

/-- The creation ("raising") operator `a† = (mωQ - iP)/√(2mℏω)`. -/
def ladderAdag : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ((normConst m ω : ℂ))⁻¹ • ((m * ω : ℝ) • positionOperatorSchwartz -
    Complex.I • momentumOperatorSchwartz)

/-- The raw (unnormalized) ladder commutator `[mωQ + iP, mωQ - iP] = 2mωℏ`, a direct corollary of
`ccr` by noncommutative-ring algebra (no calculus left to do). -/
lemma ladder_comm_raw :
    ((m * ω : ℝ) • positionOperatorSchwartz + Complex.I • momentumOperatorSchwartz) *
        ((m * ω : ℝ) • positionOperatorSchwartz - Complex.I • momentumOperatorSchwartz) -
      ((m * ω : ℝ) • positionOperatorSchwartz - Complex.I • momentumOperatorSchwartz) *
        ((m * ω : ℝ) • positionOperatorSchwartz + Complex.I • momentumOperatorSchwartz)
      = (2 * m * ω * (ℏ : ℝ) : ℝ) • (1 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) := by
  have key : ((m * ω : ℝ) • positionOperatorSchwartz + Complex.I • momentumOperatorSchwartz) *
        ((m * ω : ℝ) • positionOperatorSchwartz - Complex.I • momentumOperatorSchwartz) -
      ((m * ω : ℝ) • positionOperatorSchwartz - Complex.I • momentumOperatorSchwartz) *
        ((m * ω : ℝ) • positionOperatorSchwartz + Complex.I • momentumOperatorSchwartz)
      = ((-Complex.I) * (m * ω : ℝ) - Complex.I * (m * ω : ℝ)) •
        (positionOperatorSchwartz * momentumOperatorSchwartz -
          momentumOperatorSchwartz * positionOperatorSchwartz) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm]
    module
  rw [key, ccr, smul_smul]
  have hscalar : ((-Complex.I) * (m * ω : ℝ) - Complex.I * (m * ω : ℝ)) * (Complex.I * (ℏ : ℂ))
      = ((2 * m * ω * (ℏ : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [show Complex.I ^ 2 = Complex.I * Complex.I by ring, Complex.I_mul_I]
    ring
  rw [hscalar]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

/-- **`[a, a†] = 1`.** The main integration test for the common-core/algebra branch: the
harmonic-oscillator ladder operators, built purely from `Q` and `P` on the same common core
`𝓢(ℝ, ℂ)`, satisfy the canonical ladder commutation relation. Proved directly from `ccr` by
factoring the normalization constant out of `ladder_comm_raw`. -/
theorem ladder_comm (hm : 0 < m) (hω : 0 < ω) :
    ladderA m ω * ladderAdag m ω - ladderAdag m ω * ladderA m ω
      = (1 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) := by
  unfold ladderA ladderAdag
  rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, ladder_comm_raw,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  have hreal : (normConst m ω)⁻¹ * (normConst m ω)⁻¹ * (2 * m * ω * (ℏ : ℝ)) = 1 := by
    have hc2 := normConst_sq m ω hm hω
    have hne := normConst_ne_zero m ω hm hω
    field_simp
    nlinarith [hc2]
  have : ((normConst m ω : ℂ))⁻¹ * ((normConst m ω : ℂ))⁻¹ *
      (2 * (m : ℂ) * (ω : ℂ) * (ℏ : ℂ)) = 1 := by
    have := congrArg Complex.ofReal hreal
    push_cast at this
    convert this using 2
  push_cast
  simp [this]

/-- The harmonic-oscillator Hamiltonian `H = P²/(2m) + (1/2)mω²Q²`. -/
def hamiltonian : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  ((1 / (2 * m) : ℝ) : ℂ) • (momentumOperatorSchwartz * momentumOperatorSchwartz) +
    ((m * ω ^ 2 / 2 : ℝ) : ℂ) • (positionOperatorSchwartz * positionOperatorSchwartz)

/-- The raw (unnormalized) ladder *product* `(mωQ - iP)(mωQ + iP) = (mω)²Q² + P² - mωℏ`, the
non-antisymmetrized companion to `ladder_comm_raw`: expanding the product leaves the `Q²`/`P²`
diagonal terms in place (they do not cancel, unlike in the commutator), with only the cross term
collapsing via `ccr`. `-iP · iP = P²` (`Complex.I_mul_I`) and `i(mω)(QP - PQ) = i(mω)(iℏ) = -mωℏ`
(`ccr` then `Complex.I_mul_I` again) account for the two non-obvious sign flips. -/
lemma ladder_prod_raw :
    ((m * ω : ℝ) • positionOperatorSchwartz - Complex.I • momentumOperatorSchwartz) *
        ((m * ω : ℝ) • positionOperatorSchwartz + Complex.I • momentumOperatorSchwartz)
      = ((m * ω : ℝ) ^ 2 : ℝ) • (positionOperatorSchwartz * positionOperatorSchwartz) +
          (momentumOperatorSchwartz * momentumOperatorSchwartz) -
          (m * ω * (ℏ : ℝ) : ℝ) • (1 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)) := by
  have hPP : (Complex.I • momentumOperatorSchwartz) * (Complex.I • momentumOperatorSchwartz)
      = - (momentumOperatorSchwartz * momentumOperatorSchwartz) := by
    rw [smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul]
  have key : ((m * ω : ℝ) • positionOperatorSchwartz - Complex.I • momentumOperatorSchwartz) *
      ((m * ω : ℝ) • positionOperatorSchwartz + Complex.I • momentumOperatorSchwartz)
      = ((m * ω : ℝ) ^ 2 : ℝ) • (positionOperatorSchwartz * positionOperatorSchwartz) +
        (Complex.I * (m * ω : ℝ)) •
          (positionOperatorSchwartz * momentumOperatorSchwartz -
            momentumOperatorSchwartz * positionOperatorSchwartz) -
        (Complex.I • momentumOperatorSchwartz) * (Complex.I • momentumOperatorSchwartz) := by
    simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
    module
  have hscalar : (Complex.I * (m * ω : ℝ)) •
      ((Complex.I * (ℏ : ℂ)) • (1 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)))
      = -((m * ω * (ℏ : ℝ) : ℝ) • (1 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ))) := by
    ext ψ x
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.one_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    rw [show Complex.I * (↑m * ↑ω) * (Complex.I * ↑ℏ * ψ x)
        = Complex.I * Complex.I * (↑m * ↑ω * ↑ℏ) * ψ x by ring, Complex.I_mul_I]
    ring
  rw [key, ccr, hscalar, hPP]
  abel

/-- **The algebraic Hamiltonian factorization `H = ℏω(a†a + 1/2)`.** The oscillator's spectrum is
explicitly out of scope — see the top-level TL;DR — but this purely algebraic identity is exactly
the kind of statement `Core.lean`'s abstraction is meant to make pleasant: given `ladder_prod_raw`,
dividing through by `normConst m ω ^ 2 = 2mℏω` and checking the `±mωℏ/2` shift terms cancel exactly
is ordinary scalar algebra. **Fully proved.** -/
theorem hamiltonian_eq (hm : 0 < m) (hω : 0 < ω) :
    hamiltonian m ω = ((ℏ : ℂ) * (ω : ℂ)) •
      (ladderAdag m ω * ladderA m ω + (1 / 2 : ℝ) • (1 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ))) := by
  have hℏ := ℏ_pos
  unfold ladderAdag ladderA hamiltonian
  rw [smul_mul_smul_comm, ladder_prod_raw]
  have hc2 := normConst_sq m ω hm hω
  have hne := normConst_ne_zero m ω hm hω
  have hkey : ((normConst m ω : ℂ))⁻¹ * ((normConst m ω : ℂ))⁻¹ =
      ((2 * m * (ℏ : ℝ) * ω : ℝ) : ℂ)⁻¹ := by
    rw [← hc2]
    push_cast
    ring
  rw [hkey]
  have h2mℏω : ((2 * m * (ℏ : ℝ) * ω : ℝ) : ℂ) ≠ 0 := by
    have : (2 * m * (ℏ : ℝ) * ω : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  ext ψ x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.one_apply, Complex.real_smul, smul_eq_mul]
  push_cast
  field_simp
  ring

end OperatorAlgebra.Unbounded.Example
