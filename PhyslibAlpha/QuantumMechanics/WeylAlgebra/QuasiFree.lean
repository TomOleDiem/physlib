/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Matrix.Order
public import PhyslibAlpha.Mathematics.TauCeti.LinearAlgebra.Matrix.PosSemidef
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Quasi-free states of the Weyl algebra

The Gaussian functionals `ω(W(f)) = exp(-s(f, f) / 2)` that define states of the canonical
commutation relations, and the criterion for their positivity.

## i. Overview

A state of the Weyl relations with symplectic form `σ` is determined by its characteristic function
`Φ(f) = ω(W(f))`, since `W(f)` span the algebra. Positivity `ω(a† a) ≥ 0` for `a = ∑ cᵢ W(fᵢ)`
reads, using `W(f)† W(g) = exp(i σ(f, g) / 2) W(g - f)`, that the matrices
`exp(i σ(fᵢ, fⱼ) / 2) Φ(fⱼ - fᵢ)`, that is the kernel `charKernel`, is positive semidefinite. This
is `IsPositive`.

A quasi-free state has a Gaussian characteristic function, with `s` a real symmetric
positive semidefinite form. It is positive exactly when `s` dominates the symplectic form,
`σ(f, g)² ≤ 4 s(f, f) s(g, g)`. The proof writes the matrix as a Hadamard product of the
rank one matrix `exp(-sᵢᵢ/2) exp(-sⱼⱼ/2)` with the entrywise exponential of the kernel
`s(fᵢ, fⱼ) + i σ(fᵢ, fⱼ) / 2`. The kernel is positive semidefinite since, for `x = a + i b`, it
evaluates to `s(A, A) + s(B, B) - σ(A, B)`, which is nonnegative by the domination, and the
entrywise exponential of a positive semidefinite matrix is positive semidefinite by the Schur
product theorem. For the vacuum `s(f, f) = ‖f‖² / 2` the domination is the Cauchy–Schwarz
inequality.

## ii. Key results

- `posSemidef_exp`: the entrywise exponential of a positive semidefinite matrix is positive
  semidefinite.
- `kernel_posSemidef`: the kernel `s + i σ / 2` is positive semidefinite when `s` dominates `σ`.
- `charKernel`, `IsPositive`: the kernel of a characteristic function and its positivity.
- `posSemidef_of_fin`: positivity of an infinite kernel from its finite submatrices.
- `quasiFree_isPositive`: a Gaussian characteristic function dominating `σ` is positive.

## iii. Table of contents

- A. The entrywise exponential
- B. The kernel of a quasi-free state
- C. Positivity of quasi-free states

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 5.2.
* D. Petz, An Invitation to the Algebra of Canonical Commutation Relations.

-/

@[expose] public section

namespace WeylAlgebra

open Matrix Complex
open scoped ComplexOrder

/-!

## A. The entrywise exponential

-/

variable {n : Type*}

/-- The entrywise exponential of a positive semidefinite matrix is positive semidefinite. -/
lemma posSemidef_exp {K : Matrix n n ℂ} (hK : K.PosSemidef) :
    (Matrix.of fun i j => Complex.exp (K i j)).PosSemidef := by
  have hsum : ∀ N : ℕ,
      (Matrix.of fun i j => ∑ k ∈ Finset.range N, K i j ^ k / k.factorial).PosSemidef := by
    intro N
    induction N with
    | zero => convert PosSemidef.zero (n := n) (R := ℂ); ext; simp
    | succ N ih =>
      have h2 : (Matrix.of fun i j => ∑ k ∈ Finset.range (N + 1), K i j ^ k / k.factorial) =
          (Matrix.of fun i j => ∑ k ∈ Finset.range N, K i j ^ k / k.factorial) +
            ((N.factorial : ℂ)⁻¹) • Matrix.of fun i j => K i j ^ N := by
        ext i j; simp [Finset.sum_range_succ, div_eq_inv_mul, mul_comm]
      rw [h2]
      exact ih.add ((hK.hadamard_pow N).smul (by positivity))
  have ht : Filter.Tendsto (fun N : ℕ => (Matrix.of fun i j =>
      ∑ k ∈ Finset.range N, K i j ^ k / k.factorial : Matrix n n ℂ)) Filter.atTop
      (nhds (Matrix.of fun i j => Complex.exp (K i j))) := by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simpa [Complex.exp_eq_exp_ℂ, div_eq_inv_mul] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (K i j)).tendsto_sum_nat
  exact posSemidef_is_closed.mem_of_tendsto ht (Filter.Eventually.of_forall hsum)

/-!

## B. The kernel of a quasi-free state

-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- An alternating form is antisymmetric. -/
lemma skew_of_alt {σ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hσ : ∀ f, σ f f = 0) (f g : V) : σ g f = - σ f g := by
  have := hσ (f + g)
  simp only [map_add, LinearMap.add_apply, hσ] at this
  linarith

/-- The kernel `s(f_i, f_j) + i σ(f_i, f_j) / 2`. -/
noncomputable def kernel (σ s : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) {ι : Type*} (f : ι → V) : Matrix ι ι ℂ :=
  Matrix.of fun i j => (s (f i) (f j) : ℂ) + I * (σ (f i) (f j) : ℂ) / 2

/-- The quadratic form of the kernel on complex coefficients `x = a + i b` is
`s(A, A) + s(B, B) - σ(A, B)` for `A = ∑ a_i f_i` and `B = ∑ b_i f_i`. -/
lemma kernel_quadForm {σ s : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hσ : ∀ f, σ f f = 0)
    (hs : ∀ f g, s f g = s g f) {ι : Type*} [Fintype ι] (f : ι → V) (x : ι → ℂ) :
    star x ⬝ᵥ (kernel σ s f *ᵥ x) =
      ((s (∑ i, (x i).re • f i) (∑ i, (x i).re • f i) +
        s (∑ i, (x i).im • f i) (∑ i, (x i).im • f i) -
        σ (∑ i, (x i).re • f i) (∑ i, (x i).im • f i) : ℝ) : ℂ) := by
  set a : ι → ℝ := fun i => (x i).re
  set b : ι → ℝ := fun i => (x i).im
  set A : V := ∑ i, a i • f i
  set B : V := ∑ i, b i • f i
  let Z : V →ₗ[ℝ] V →ₗ[ℝ] ℂ :=
    s.compr₂ Complex.ofRealCLM.toLinearMap + (I / 2) • σ.compr₂ Complex.ofRealCLM.toLinearMap
  have lin : ∀ c d : ι → ℝ, Z (∑ i, c i • f i) (∑ j, d j • f j) =
      ∑ i, ∑ j, (c i : ℂ) * d j * Z (f i) (f j) := fun c d => by
    rw [map_sum Z, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, LinearMap.smul_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Complex.real_smul, Complex.real_smul, mul_assoc]
  have hZ : ∀ i j, kernel σ s f i j = Z (f i) (f j) := fun i j => by simp [kernel, Z]; ring
  have h1 : star x ⬝ᵥ (kernel σ s f *ᵥ x) =
      Z A A + Z B B + I * (Z A B - Z B A) := by
    simp only [A, B, lin, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib,
      dotProduct, mulVec, Finset.mul_sum, hZ]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hx : ∀ k, x k = (a k : ℂ) + (b k : ℂ) * I := fun k => (Complex.re_add_im _).symm
    simp only [Pi.star_apply, Complex.star_def, hx, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    linear_combination (-(b i : ℂ) * b j * Z (f i) (f j)) * Complex.I_sq
  have e : Z A B - Z B A = I * (σ A B : ℂ) := by
    simp only [Z, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compr₂_apply]
    rw [hs B A, skew_of_alt hσ A B]
    simp; ring
  rw [h1, e]
  simp only [Z, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.compr₂_apply, hσ]
  push_cast
  simp only [ofRealCLM_apply, ofReal_zero, smul_eq_mul, mul_zero, add_zero]
  linear_combination (σ A B : ℂ) * Complex.I_sq

/-- The kernel is positive semidefinite when the form dominates the symplectic form. -/
lemma kernel_posSemidef {σ s : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hσ : ∀ f, σ f f = 0)
    (hs : ∀ f g, s f g = s g f) (hnn : ∀ f, 0 ≤ s f f)
    (hdom : ∀ f g, σ f g ^ 2 ≤ 4 * (s f f * s g g)) {ι : Type*} [Fintype ι] (f : ι → V) :
    (kernel σ s f).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · ext i j
    show star (kernel σ s f j i) = kernel σ s f i j
    simp only [kernel, of_apply]
    rw [hs (f j) (f i), skew_of_alt hσ (f i) (f j)]
    apply Complex.ext <;> simp
  · -- the real and imaginary parts of the coefficients give two vectors `A` and `B`
    rw [kernel_quadForm hσ hs f x]
    set A : V := ∑ i, (x i).re • f i
    set B : V := ∑ i, (x i).im • f i
    have h1 := hdom A B
    have h2 := hnn A
    have h3 := hnn B
    have h4 : σ A B ^ 2 ≤ (s A A + s B B) ^ 2 := by nlinarith [sq_nonneg (s A A - s B B)]
    have := (abs_le_of_sq_le_sq' h4 (by positivity)).2
    exact_mod_cast (by linarith : (0:ℝ) ≤ s A A + s B B - σ A B)

/-!

## C. Positivity of quasi-free states

-/

/-- The kernel `exp(i σ(f, g) / 2) Φ(g - f)` of a function `Φ` on the wave functions: the matrix
of the inner products `ω(W(f)† W(g))` if `Φ(f) = ω(W(f))`. -/
noncomputable def charKernel (σ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Φ : V → ℂ) : Matrix V V ℂ :=
  Matrix.of fun f g => Complex.exp (I * (σ f g : ℂ) / 2) * Φ (g - f)

/-- A function `Φ` on the wave functions is the characteristic function `ω(W(f))` of a state of
the Weyl relations with symplectic form `σ` only if it is positive: its kernel is positive
semidefinite. -/
def IsPositive (σ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Φ : V → ℂ) : Prop := (charKernel σ Φ).PosSemidef

/-- **A Gaussian characteristic function whose form dominates the symplectic form is positive**:
quasi-free states exist. -/
lemma quasiFree_isPositive {σ s : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (hσ : ∀ f, σ f f = 0)
    (hs : ∀ f g, s f g = s g f) (hnn : ∀ f, 0 ≤ s f f)
    (hdom : ∀ f g, σ f g ^ 2 ≤ 4 * (s f f * s g g)) :
    IsPositive σ fun f => Complex.exp (-(s f f : ℂ) / 2) := by
  refine TauCeti.posSemidef_iff_finite_sum.mpr ⟨fun f g => ?_, fun {ι : Type} _ f x => ?_⟩
  · simp only [charKernel, of_apply, Complex.star_def, map_mul, ← Complex.exp_conj, map_div₀,
      map_neg, Complex.conj_ofReal, Complex.conj_I, map_ofNat, skew_of_alt hσ f g, sub_eq_add_neg]
    rw [show f + -g = -(g + -f) by abel]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
    push_cast
    ring_nf
  · set u : ι → ℂ := fun i => Complex.exp (-(s (f i) (f i) : ℂ) / 2)
    have hu : ∀ j, star (u j) = u j := fun j => by
      simp only [u, Complex.star_def, ← Complex.exp_conj, map_div₀, map_neg,
        Complex.conj_ofReal]
      rw [show (starRingEnd ℂ) 2 = 2 from map_ofNat _ 2]
    have h : (charKernel σ fun f => Complex.exp (-(s f f : ℂ) / 2)).submatrix f f =
        (Matrix.vecMulVec u (star u)) ⊙
          (Matrix.of fun i j => Complex.exp (kernel σ s f i j)) := by
      ext i j
      simp only [charKernel, submatrix_apply, of_apply, hadamard_apply, vecMulVec_apply, kernel,
        u, Pi.star_apply, hu, map_sub, LinearMap.sub_apply, ← Complex.exp_add]
      rw [hs (f j) (f i)]
      congr 1
      push_cast
      ring
    have hP : PosSemidef
        ((charKernel σ fun f => Complex.exp (-(s f f : ℂ) / 2)).submatrix f f) := by
      rw [h]
      exact (posSemidef_vecMulVec_self_star u).hadamard
        (posSemidef_exp (kernel_posSemidef hσ hs hnn hdom f))
    simpa only [dotProduct, mulVec, submatrix_apply, Pi.star_apply, Finset.mul_sum, mul_assoc]
      using hP.dotProduct_mulVec_nonneg x

end WeylAlgebra
