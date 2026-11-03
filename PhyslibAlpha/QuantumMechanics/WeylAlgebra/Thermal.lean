/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.WeylAlgebra.QuasiFree
public import PhyslibAlpha.QuantumMechanics.WeylAlgebra.Weyl
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Dynamics and thermal states of the Weyl relations

The one-particle dynamics of quadratic Hamiltonians as one-parameter groups of symplectic maps,
and the thermal quasi-free states, which satisfy the KMS condition.

## i. Overview

The Heisenberg dynamics of a quadratic Hamiltonian maps a Weyl operator to a Weyl operator,
`α_t(W(f)) = W(U_t f)`, with `U_t` a one-parameter group of linear maps of the wave functions that
preserve the symplectic form. A symplectic map acts on characteristic functions by composition and
preserves positivity (`IsPositive.comp`). A state is stationary if its characteristic function is
invariant.

For finitely many modes with energies `ε`, `U_t` multiplies the amplitude of the mode `k` by
`exp(i t ε_k)`. The thermal state at inverse temperature `β` is the quasi-free state with the
characteristic function `exp(-¼ ∑ coth(β ε_k / 2) |f_k|²)`, and is positive since
`coth ≥ 1` dominates the symplectic form by the Cauchy–Schwarz inequality. It satisfies the KMS
condition `IsKMS` on the Weyl operators: the correlation function `t ↦ ω(W(f) W(U_t g))` is
the boundary value of an entire function bounded on the strip `0 ≤ Im z ≤ β` whose value at
`t + iβ` is `ω(W(U_t g) W(f))`. The function is `exp` of an explicit finite sum of exponentials
`e^{± i z ε_k}`, and the identity behind the boundary condition, mode by mode, is
`c (e^{β ε} - 1) = e^{β ε} + 1` for `c = coth(β ε / 2)`.

## ii. Key results

- `IsPositive.comp`: a symplectic map preserves positivity.
- `IsWeylKMS`: the KMS condition on the Weyl operators.
- `thermalChar_isPositive`: the thermal characteristic function is positive.
- `thermalChar_isKMS`: the thermal state of finitely many modes is a KMS state.

## iii. Table of contents

- A. Symplectic dynamics
- B. Finitely many modes
- C. The KMS condition

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 5.2.

-/

@[expose] public section

namespace WeylAlgebra

open Complex
open scoped ComplexOrder

/-!

## A. Symplectic dynamics

-/

section Dynamics

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {σ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {Φ : V → ℂ}

/-- **A symplectic map preserves positivity**: the characteristic function `Φ ∘ φ` of the state
evolved by a symplectic linear map `φ` is again positive. -/
lemma IsPositive.comp (hΦ : IsPositive σ Φ) (φ : V →ₗ[ℝ] V)
    (hφ : ∀ f g, σ (φ f) (φ g) = σ f g) : IsPositive σ (Φ ∘ φ) := by
  have : charKernel σ (Φ ∘ φ) = (charKernel σ Φ).submatrix φ φ := by
    ext f g
    simp [charKernel, hφ]
  rw [IsPositive, this]
  exact Matrix.PosSemidef.submatrix hΦ φ

end Dynamics


/-!

## B. Finitely many modes

-/

section Modes

variable {ι : Type*}

/-- The one-particle dynamics `g_k ↦ exp(i t ε_k) g_k` with energies `ε`. -/
noncomputable def modeDynamics (ε : ι → ℝ) (t : ℝ) : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) where
  toFun g k := Complex.exp (Complex.I * (t * ε k : ℝ)) * g k
  map_add' f g := by ext k; simp [mul_add]
  map_smul' a g := by ext k; simp [Complex.real_smul]; ring

/-- The Bose–Einstein weight `coth(β ε / 2) = (e^{β ε} + 1) / (e^{β ε} - 1)` of a mode. -/
noncomputable def thermalWeight (β : ℝ) (ε : ι → ℝ) (k : ι) : ℝ :=
  (Real.exp (β * ε k) + 1) / (Real.exp (β * ε k) - 1)

lemma one_le_thermalWeight {β : ℝ} {ε : ι → ℝ} (hε : ∀ k, 0 < β * ε k) (k : ι) :
    1 ≤ thermalWeight β ε k := by
  have h : 1 < Real.exp (β * ε k) := Real.one_lt_exp_iff.2 (hε k)
  rw [thermalWeight, le_div_iff₀ (by linarith)]
  linarith

lemma normSq_dynamics (k : ι) (t : ℝ) (g : ι → ℂ) :
    Complex.normSq (modeDynamics ε t g k) = Complex.normSq (g k) := by
  simp only [modeDynamics, LinearMap.coe_mk, AddHom.coe_mk, map_mul]
  rw [Complex.normSq_eq_norm_sq (Complex.exp _)]
  have : ‖Complex.exp (I * ((t * ε k : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  rw [this]
  simp

variable [Fintype ι]


/-- The symplectic form `Im ∑ conj (f k) g k` of the wave functions of finitely many modes. -/
noncomputable def modeSymplectic : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => (∑ k, star (f k) * g k).im)
    (fun f g h => by simp [Finset.sum_add_distrib, add_mul])
    (fun c f g => by simp [Finset.mul_sum, mul_assoc])
    (fun f g h => by simp [Finset.sum_add_distrib, mul_add])
    (fun c f g => by simp [Finset.mul_sum, mul_left_comm])

/-- The real symmetric form `½ ∑ c k Re (conj (f k) g k)` with the weights `c`. -/
noncomputable def modeForm (c : ι → ℝ) : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => (1 / 2) * ∑ k, c k * (star (f k) * g k).re)
    (fun f g h => by simp [Finset.sum_add_distrib, add_mul, mul_add])
    (fun a f g => by
      simp only [Pi.smul_apply, Complex.real_smul, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [one_div, star_mul', RCLike.star_def, conj_ofReal, mul_re, ofReal_re, conj_re,
        ofReal_im, conj_im, mul_neg, zero_mul, neg_zero, sub_zero, mul_im, add_zero, neg_mul,
        sub_neg_eq_add]
      ring)
    (fun f g h => by simp [Finset.sum_add_distrib, mul_add])
    (fun a f g => by
      simp only [Pi.smul_apply, Complex.real_smul, Finset.mul_sum, smul_eq_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [one_div, RCLike.star_def, mul_re, conj_re, ofReal_re, ofReal_im, zero_mul,
        sub_zero, conj_im, mul_im, add_zero, neg_mul, sub_neg_eq_add]
      ring)

lemma modeSymplectic_self (f : ι → ℂ) : modeSymplectic f f = 0 := by
  have : ∑ k, star (f k) * f k = ((∑ k, Complex.normSq (f k) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun k _ => by simp [Complex.normSq_eq_conj_mul_self]
  simp only [modeSymplectic, LinearMap.mk₂_apply]
  rw [this, Complex.ofReal_im]

lemma modeForm_symm (c : ι → ℝ) (f g : ι → ℂ) : modeForm c f g = modeForm c g f := by
  simp only [modeForm, LinearMap.mk₂_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp [mul_comm]

lemma modeForm_self (c : ι → ℝ) (f : ι → ℂ) :
    modeForm c f f = (1 / 2) * ∑ k, c k * Complex.normSq (f k) := by
  simp only [modeForm, LinearMap.mk₂_apply]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.normSq_apply, mul_comm]

/-- The form dominates the symplectic form if all weights are at least one. -/
lemma modeForm_dom {c : ι → ℝ} (hc : ∀ k, 1 ≤ c k) (f g : ι → ℂ) :
    modeSymplectic f g ^ 2 ≤ 4 * (modeForm c f f * modeForm c g g) := by
  have h1 : modeSymplectic f g ^ 2 ≤ (∑ k, ‖f k‖ * ‖g k‖) ^ 2 := by
    have : |modeSymplectic f g| ≤ ∑ k, ‖f k‖ * ‖g k‖ := by
      simp only [modeSymplectic, LinearMap.mk₂_apply]
      refine (Complex.abs_im_le_norm _).trans ((norm_sum_le _ _).trans ?_)
      exact le_of_eq (Finset.sum_congr rfl fun k _ => by simp)
    exact sq_le_sq' (by linarith [abs_nonneg (modeSymplectic f g), neg_abs_le (modeSymplectic f g)])
      (abs_le.1 this).2
  have h2 : (∑ k, ‖f k‖ * ‖g k‖) ^ 2 ≤ (∑ k, ‖f k‖ ^ 2) * ∑ k, ‖g k‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h3 : ∑ k, ‖f k‖ ^ 2 ≤ ∑ k, c k * Complex.normSq (f k) :=
    Finset.sum_le_sum fun k _ => by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [hc k, sq_nonneg ‖f k‖]
  have h4 : ∑ k, ‖g k‖ ^ 2 ≤ ∑ k, c k * Complex.normSq (g k) :=
    Finset.sum_le_sum fun k _ => by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [hc k, sq_nonneg ‖g k‖]
  rw [modeForm_self, modeForm_self]
  calc modeSymplectic f g ^ 2 ≤ (∑ k, ‖f k‖ ^ 2) * ∑ k, ‖g k‖ ^ 2 := h1.trans h2
    _ ≤ (∑ k, c k * Complex.normSq (f k)) * ∑ k, c k * Complex.normSq (g k) :=
        mul_le_mul h3 h4 (Finset.sum_nonneg fun k _ => by positivity) (le_trans
          (Finset.sum_nonneg fun k _ => by positivity) h3)
    _ = _ := by ring

/-- The characteristic function `exp(-½ ⟨f, coth(β h / 2) f⟩ / 2)` of the thermal quasi-free state
of non-interacting modes with energies `ε`. -/
noncomputable def thermalChar (β : ℝ) (ε : ι → ℝ) (f : ι → ℂ) : ℂ :=
  Complex.exp (-(modeForm (thermalWeight β ε) f f : ℂ) / 2)

/-- **The thermal state is a state of the Weyl relations**: its characteristic function is
positive. -/
lemma thermalChar_isPositive {β : ℝ} {ε : ι → ℝ} (hε : ∀ k, 0 < β * ε k) :
    IsPositive modeSymplectic (thermalChar β ε) := by
  refine quasiFree_isPositive (s := modeForm (thermalWeight β ε)) modeSymplectic_self
    (modeForm_symm _) (fun f => ?_) (modeForm_dom (one_le_thermalWeight hε))
  rw [modeForm_self]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ =>
    mul_nonneg (by linarith [one_le_thermalWeight hε k]) (Complex.normSq_nonneg _))

end Modes


/-!

## C. The KMS condition

-/

/-- **The KMS condition on the Weyl operators** at inverse temperature `β` for the dynamics
`α_t(W(f)) = W(U_t f)`, of a state with characteristic function `Φ`: for all `f` and `g` the
correlation function `t ↦ ω(W(f) W(U_t g))` is the boundary value of a bounded function, continuous
on the strip `0 ≤ Im z ≤ β` and analytic inside it, whose value at `t + iβ` is
`ω(W(U_t g) W(f))`. Here `ω(W(f) W(h)) = exp(-i σ(f, h) / 2) Φ(f + h)`. -/
def IsWeylKMS {V : Type*} [AddCommGroup V] [Module ℝ V] (σ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (U : ℝ → V →ₗ[ℝ] V) (β : ℝ) (Φ : V → ℂ) : Prop :=
  ∀ f g : V, ∃ F : ℂ → ℂ,
    ContinuousOn F {z | 0 ≤ z.im ∧ z.im ≤ β} ∧
    DifferentiableOn ℂ F {z | 0 < z.im ∧ z.im < β} ∧
    (∃ C : ℝ, ∀ z ∈ {z : ℂ | 0 ≤ z.im ∧ z.im ≤ β}, ‖F z‖ ≤ C) ∧
    (∀ t : ℝ, F t = Complex.exp (-(I * (σ f (U t g) : ℝ)) / 2) * Φ (f + U t g)) ∧
    ∀ t : ℝ, F (t + β * I) = Complex.exp (-(I * (σ (U t g) f : ℝ)) / 2) * Φ (U t g + f)

/-- **The mode-by-mode identity of the KMS condition.** -/
lemma kms_mode (x y E c N : ℝ) (hE : 1 < E) (hc : c * (E - 1) = E + 1) :
    -(1 / 4 : ℂ) * (((x : ℂ) + y * I) / E - ((x : ℂ) - y * I) * E) - (1 / 4 : ℂ) * c * N
      - (1 / 4 : ℂ) * c * (((x : ℂ) + y * I) / E + ((x : ℂ) - y * I) * E)
    = (I / 2) * y - (1 / 4 : ℂ) * c * N - (1 / 2 : ℂ) * c * x := by
  have hE0 : (E : ℂ) ≠ 0 := by exact_mod_cast (by linarith : E ≠ 0)
  have hc' : (c : ℂ) * (E - 1) = E + 1 := by exact_mod_cast hc
  field_simp
  linear_combination (-2 * (x : ℂ) * (E - 1) + 2 * (y : ℂ) * I * (E + 1)) * hc'

/-- The mode identity of the KMS condition, for the amplitude `p`. -/
lemma kms_mode' (p : ℂ) (N c E : ℝ) (hE : 1 < E) (hc : c * (E - 1) = E + 1) :
    -(1 / 4 : ℂ) * (p / E - star p * E) - (1 / 4 : ℂ) * c * N -
      (1 / 4 : ℂ) * c * (p / E + star p * E)
      = -(I / 2) * ((star p).im : ℂ) - (1 / 4 : ℂ) * c * ((N + 2 * p.re : ℝ) : ℂ) := by
  obtain ⟨a, b⟩ := p
  have h := kms_mode a b E c N hE hc
  have e1 : (⟨a, b⟩ : ℂ) = (a : ℂ) + b * I := by apply Complex.ext <;> simp
  have e2 : star (⟨a, b⟩ : ℂ) = (a : ℂ) - b * I := by apply Complex.ext <;> simp
  have e3 : (star (⟨a, b⟩ : ℂ)).im = -b := by simp
  have e4 : ((⟨a, b⟩ : ℂ)).re = a := rfl
  rw [e3, e4, e2, e1]
  push_cast
  linear_combination h

section KMS

variable {ι : Type*} (β : ℝ) (ε : ι → ℝ) (f g : ι → ℂ)

/-- The amplitude `conj f g e^{i z ε}` -/
noncomputable def kmsP (k : ι) (z : ℂ) : ℂ := star (f k) * g k * Complex.exp (I * z * ε k)

/-- The amplitude `f conj g e^{-i z ε}` -/
noncomputable def kmsQ (k : ι) (z : ℂ) : ℂ := f k * star (g k) * Complex.exp (-(I * z * ε k))

lemma kmsQ_real (k : ι) (t : ℝ) : kmsQ ε f g k t = star (kmsP ε f g k t) := by
  simp only [kmsQ, kmsP, star_mul', Complex.star_def, ← Complex.exp_conj, map_mul,
    Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj]
  ring_nf

lemma kmsP_real (k : ι) (t : ℝ) :
    kmsP ε f g k t = star (f k) * modeDynamics ε t g k := by
  simp only [kmsP, modeDynamics, LinearMap.coe_mk, AddHom.coe_mk]
  push_cast
  ring_nf

lemma kmsP_shift (k : ι) (t : ℝ) :
    kmsP ε f g k (t + β * I) = kmsP ε f g k t / Real.exp (β * ε k) := by
  have : Complex.exp (I * (t + β * I) * ε k) =
      Complex.exp (I * t * ε k) / Real.exp (β * ε k) := by
    rw [eq_div_iff (by exact_mod_cast Real.exp_ne_zero _), Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination ((β : ℂ) * ε k) * Complex.I_sq
  simp only [kmsP, this]
  ring

lemma kmsQ_shift (k : ι) (t : ℝ) :
    kmsQ ε f g k (t + β * I) = kmsQ ε f g k t * Real.exp (β * ε k) := by
  have : Complex.exp (-(I * (t + β * I) * ε k)) =
      Complex.exp (-(I * t * ε k)) * Real.exp (β * ε k) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (-(β : ℂ) * ε k) * Complex.I_sq
  simp only [kmsQ, this]
  ring

lemma star_dynamics_mul (k : ι) (t : ℝ) :
    star (modeDynamics ε t g k) * f k = star (kmsP ε f g k t) := by
  rw [kmsP_real, star_mul', star_star]
  exact mul_comm _ _

variable [Fintype ι]

/-- The exponent of the analytic correlation function. -/
noncomputable def kmsExponent (z : ℂ) : ℂ :=
  ∑ k, (-(1 / 4 : ℂ) * (kmsP ε f g k z - kmsQ ε f g k z)
    - (1 / 4 : ℂ) * thermalWeight β ε k * (Complex.normSq (f k) + Complex.normSq (g k))
    - (1 / 4 : ℂ) * thermalWeight β ε k * (kmsP ε f g k z + kmsQ ε f g k z))

lemma mode_real (p : ℂ) (nf ng c : ℝ) :
    -(1 / 4 : ℂ) * (p - star p) - (1 / 4 : ℂ) * c * (nf + ng) - (1 / 4 : ℂ) * c * (p + star p)
      = -(I / 2) * (p.im : ℂ) - (1 / 4 : ℂ) * c * ((nf + ng + 2 * p.re : ℝ) : ℂ) := by
  obtain ⟨a, b⟩ := p
  apply Complex.ext <;> simp <;> ring

/-- The weighted norm of the evolved wave function in terms of the amplitudes. -/
lemma modeForm_add_dynamics (c : ι → ℝ) (t : ℝ) :
    ((modeForm c (f + modeDynamics ε t g) (f + modeDynamics ε t g) : ℝ) : ℂ)
      = (1 / 2 : ℂ) * ∑ k, (c k : ℂ) *
        ((Complex.normSq (f k) + Complex.normSq (g k) + 2 * (kmsP ε f g k t).re : ℝ) : ℂ) := by
  rw [modeForm_self]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have : Complex.normSq ((f + modeDynamics ε t g) k) = Complex.normSq (f k) +
      Complex.normSq (g k) + 2 * (kmsP ε f g k t).re := by
    rw [Pi.add_apply, Complex.normSq_add, normSq_dynamics, kmsP_real]
    simp [Complex.mul_re]
  rw [this]
  push_cast
  ring

/-- **The correlation function at real times.** -/
lemma kms_real (t : ℝ) :
    Complex.exp (kmsExponent β ε f g t) =
      Complex.exp (-(I * (modeSymplectic f (modeDynamics ε t g) : ℝ)) / 2) *
        thermalChar β ε (f + modeDynamics ε t g) := by
  rw [thermalChar, ← Complex.exp_add]
  congr 1
  have hσ : ((modeSymplectic f (modeDynamics ε t g) : ℝ) : ℂ) = ∑ k, ((kmsP ε f g k t).im : ℂ) := by
    simp only [modeSymplectic, LinearMap.mk₂_apply, kmsP_real,
      Complex.im_sum, Complex.ofReal_sum]
  have hs := modeForm_add_dynamics ε f g (thermalWeight β ε) t
  rw [hσ, hs, kmsExponent]
  simp only [neg_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [kmsQ_real, mode_real]
  push_cast
  ring

/-- **The correlation function at the shifted times** `t + iβ`. -/
lemma kms_shift (hε : ∀ k, 0 < β * ε k) (t : ℝ) :
    Complex.exp (kmsExponent β ε f g (t + β * I)) =
      Complex.exp (-(I * (modeSymplectic (modeDynamics ε t g) f : ℝ)) / 2) *
        thermalChar β ε (modeDynamics ε t g + f) := by
  rw [thermalChar, ← Complex.exp_add, add_comm (modeDynamics ε t g) f]
  congr 1
  have hσ : ((modeSymplectic (modeDynamics ε t g) f : ℝ) : ℂ) =
      ∑ k, ((star (kmsP ε f g k t)).im : ℂ) := by
    simp only [modeSymplectic, LinearMap.mk₂_apply, star_dynamics_mul, Complex.im_sum,
      Complex.ofReal_sum]
  have hs := modeForm_add_dynamics ε f g (thermalWeight β ε) t
  rw [hσ, hs, kmsExponent]
  simp only [neg_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hE : 1 < Real.exp (β * ε k) := Real.one_lt_exp_iff.2 (hε k)
  have hc : thermalWeight β ε k * (Real.exp (β * ε k) - 1) = Real.exp (β * ε k) + 1 := by
    rw [thermalWeight, div_mul_cancel₀ _ (by linarith)]
  rw [kmsP_shift, kmsQ_shift, kmsQ_real]
  have := kms_mode' (kmsP ε f g k t) (Complex.normSq (f k) + Complex.normSq (g k))
    (thermalWeight β ε k) (Real.exp (β * ε k)) hE hc
  push_cast at this ⊢
  linear_combination this

/-- The exponentials of the analytic continuation are bounded on the strip. -/
lemma norm_exp_strip (e : ℝ) (z : ℂ) (h₀ : 0 ≤ z.im) (h₁ : z.im ≤ β) :
    ‖Complex.exp (I * z * e)‖ ≤ Real.exp (β * |e|) ∧
      ‖Complex.exp (-(I * z * e))‖ ≤ Real.exp (β * |e|) := by
  simp only [Complex.norm_exp, neg_re, mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_sub]
  have h2 : z.im * |e| ≤ β * |e| := mul_le_mul_of_nonneg_right h₁ (abs_nonneg e)
  constructor <;> refine Real.exp_le_exp.2 ?_ <;>
    nlinarith [abs_nonneg e, le_abs_self e, neg_abs_le e, mul_nonneg h₀ (abs_nonneg e)]

/-- The correlation function is differentiable. -/
lemma differentiable_kmsExponent : Differentiable ℂ (kmsExponent β ε f g) := by
  unfold kmsExponent kmsP kmsQ
  refine Differentiable.fun_sum fun k _ => ?_
  have e1 : Differentiable ℂ fun z : ℂ => Complex.exp (I * z * ε k) := by
    have : Differentiable ℂ fun z : ℂ => I * z * ε k := by fun_prop
    exact Differentiable.cexp this
  have e2 : Differentiable ℂ fun z : ℂ => Complex.exp (-(I * z * ε k)) := by
    have : Differentiable ℂ fun z : ℂ => -(I * z * ε k) := by fun_prop
    exact Differentiable.cexp this
  fun_prop

lemma norm_term_le (a b : ℂ) (c N R : ℝ) (hN : 0 ≤ N) (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) :
    ‖-(1 / 4 : ℂ) * (a - b) - (1 / 4 : ℂ) * c * N - (1 / 4 : ℂ) * c * (a + b)‖ ≤
      1 / 4 * (1 + |c|) * (2 * R) + 1 / 4 * |c| * N := by
  have h1 : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by simp
  have hR : 0 ≤ R := (norm_nonneg a).trans ha
  have e1 : ‖-(1 / 4 : ℂ) * (a - b)‖ ≤ 1 / 4 * (2 * R) := by
    rw [norm_mul, norm_neg, h1]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le a b).trans (by linarith)) (by norm_num)
  have e2 : ‖(1 / 4 : ℂ) * c * N‖ ≤ 1 / 4 * |c| * N := by
    simp [abs_of_nonneg hN]
  have e3 : ‖(1 / 4 : ℂ) * c * (a + b)‖ ≤ 1 / 4 * |c| * (2 * R) := by
    rw [norm_mul, norm_mul, h1, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((norm_add_le a b).trans (by linarith))
      (by positivity)
  calc _ ≤ ‖-(1 / 4 : ℂ) * (a - b)‖ + ‖(1 / 4 : ℂ) * c * N‖ + ‖(1 / 4 : ℂ) * c * (a + b)‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by nlinarith

/-- The correlation function is bounded on the strip. -/
lemma exists_bound_kmsExponent :
    ∃ B : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ β → ‖kmsExponent β ε f g z‖ ≤ B := by
  refine ⟨∑ k, (1 / 4 * (1 + |thermalWeight β ε k|) *
    (2 * (‖f k‖ * ‖g k‖ * Real.exp (β * |ε k|))) +
      1 / 4 * |thermalWeight β ε k| * (Complex.normSq (f k) + Complex.normSq (g k))),
    fun z h₀ h₁ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)⟩
  obtain ⟨hp, hq⟩ := norm_exp_strip β (ε k) z h₀ h₁
  have hP : ‖kmsP ε f g k z‖ ≤ ‖f k‖ * ‖g k‖ * Real.exp (β * |ε k|) := by
    rw [kmsP, norm_mul, norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  have hQ : ‖kmsQ ε f g k z‖ ≤ ‖f k‖ * ‖g k‖ * Real.exp (β * |ε k|) := by
    rw [kmsQ, norm_mul, norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  have := norm_term_le (kmsP ε f g k z) (kmsQ ε f g k z) (thermalWeight β ε k)
    (Complex.normSq (f k) + Complex.normSq (g k)) _
    (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) hP hQ
  push_cast at this
  exact this

end KMS

/-- **The thermal state of finitely many modes is a KMS state** for the dynamics
`g_k ↦ exp(i t ε_k) g_k`, at every inverse temperature `β` with `β ε_k > 0`. -/
lemma thermalChar_isKMS {ι : Type*} [Fintype ι] {β : ℝ} {ε : ι → ℝ} (hε : ∀ k, 0 < β * ε k) :
    IsWeylKMS modeSymplectic (modeDynamics ε) β (thermalChar β ε) := by
  intro f g
  have hd : Differentiable ℂ fun z => Complex.exp (kmsExponent β ε f g z) :=
    Differentiable.cexp (differentiable_kmsExponent β ε f g)
  refine ⟨fun z => Complex.exp (kmsExponent β ε f g z), hd.continuous.continuousOn,
    hd.differentiableOn, ?_, fun t => kms_real β ε f g t, fun t => kms_shift β ε f g hε t⟩
  obtain ⟨B, hB⟩ := exists_bound_kmsExponent β ε f g
  refine ⟨Real.exp B, fun z hz => ?_⟩
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.2 ((Complex.re_le_norm _).trans (hB z hz.1 hz.2))

end WeylAlgebra
