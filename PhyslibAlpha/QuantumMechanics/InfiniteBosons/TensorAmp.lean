/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.WeylRegular
/-!

# Amplification of operators on a Hilbert tensor product

For `H_X = ℓ²(A)` and `H_Y = ℓ²(A × B)` the map `T ↦ T ⊗ 1` is a star homomorphism from
`B(ℓ²(A))` into `B(ℓ²(A × B))`.

## i. Overview

A product basis gives the Hilbert tensor product of two spaces `ℓ²(A)` and `ℓ²(B)` as `ℓ²(A × B)`.
The observable `T` of the first factor acts on the second index as the identity. A vector of
`ℓ²(A × B)` is a family of slices in `ℓ²(A)` indexed by `B`. The squared norm is the sum of the
squared norms of the slices. The amplification applies `T` to each slice. It is bounded by `‖T‖`.
It is multiplicative and compatible with the adjoint. This gives the inclusion maps `A ⊗ 1` of a
local net of observables `B(H_X)`, where the net is specified through finite tensor products and
not through the minimal tensor product of the algebras.

## ii. Key results

- `InfiniteBosons.slice`: the slice of a vector of `ℓ²(A × B)` at `b`.
- `InfiniteBosons.norm_sq_eq_tsum_slices`: Parseval for slices.
- `InfiniteBosons.amp`: the bounded operator `T ⊗ 1`.
- `InfiniteBosons.amp_mul`, `InfiniteBosons.amp_adjoint`: multiplicativity and compatibility with
  the adjoint.
- `InfiniteBosons.ampStar`: the star homomorphism `B(ℓ²(A)) → B(ℓ²(A × B))`.

## iii. Table of contents

- A. Slices
- B. The amplified operator
- C. The star homomorphism

## iv. References

* R. Haag, Local Quantum Physics, Springer (1992), Chapter III.
* O. Bratteli, D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, Section 6.2.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {A B : Type*}

lemma sq_summable_slices (g : A × B → ℝ) (hg0 : 0 ≤ g) :
    Summable g ↔ (∀ b, Summable fun a => g (a, b)) ∧ Summable fun b => ∑' a, g (a, b) := by
  have h := summable_prod_of_nonneg (f := fun q : B × A => g (q.2, q.1)) (fun q => hg0 _)
  rw [← (Equiv.prodComm A B).summable_iff] at h
  simpa [Function.comp_def] using h

lemma tsum_slices {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (g : A × B → E)
    (hg : Summable g) (hb : ∀ b, Summable fun a => g (a, b)) :
    ∑' p, g p = ∑' b, ∑' a, g (a, b) := by
  have h1 : Summable fun q : B × A => g (q.2, q.1) :=
    (Equiv.prodComm B A).summable_iff.mpr (by simpa [Function.comp_def] using hg)
  exact ((Equiv.prodComm B A).tsum_eq g).symm.trans (h1.tsum_prod' hb)

lemma sq_summable (f : HilbertSp A) : Summable fun a => ‖f a‖ ^ (2 : ℝ) := by
  have hf := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num)] at hf
  simpa using hf

lemma norm_sq_eq_tsum (f : HilbertSp A) : ‖f‖ ^ 2 = ∑' a, ‖f a‖ ^ (2 : ℝ) := by
  have := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) f
  simpa [Real.rpow_two] using this

/-- The slice of `ψ ∈ ℓ²(A × B)` at `b`. -/
def slice (b : B) (ψ : HilbertSp (A × B)) : HilbertSp A :=
  ⟨fun a => ψ (a, b), (memℓp_gen_iff (by norm_num)).mpr (by
    have := sq_summable ψ
    have h2 : (2 : ENNReal).toReal = 2 := by norm_num
    simp only [h2]
    exact this.comp_injective (fun a a' h => by simpa using h : Function.Injective
      fun a : A => (a, b)))⟩

lemma slice_apply (b : B) (ψ : HilbertSp (A × B)) (a : A) : slice b ψ a = ψ (a, b) := rfl

lemma slice_add (b : B) (ψ φ : HilbertSp (A × B)) : slice b (ψ + φ) = slice b ψ + slice b φ :=
  Subtype.ext (funext fun a => rfl)

lemma slice_smul (b : B) (c : ℂ) (ψ : HilbertSp (A × B)) : slice b (c • ψ) = c • slice b ψ :=
  Subtype.ext (funext fun a => rfl)

lemma norm_sq_eq_tsum_slices (ψ : HilbertSp (A × B)) :
    ‖ψ‖ ^ 2 = ∑' b, ‖slice b ψ‖ ^ 2 := by
  rw [norm_sq_eq_tsum, tsum_slices _ (sq_summable ψ) (fun b => sq_summable (slice b ψ))]
  exact tsum_congr fun b => (norm_sq_eq_tsum (slice b ψ)).symm

lemma summable_slices (ψ : HilbertSp (A × B)) : Summable fun b => ‖slice b ψ‖ ^ 2 := by
  have := ((sq_summable_slices _ (fun p => by positivity)).mp (sq_summable ψ)).2
  refine this.congr fun b => ?_
  exact (norm_sq_eq_tsum (slice b ψ)).symm

/-- Amplification: the vector `a ↦ T (ψ(·, b))(a)`, as a function. -/
def ampFun (T : HilbertSp A →L[ℂ] HilbertSp A) (ψ : HilbertSp (A × B)) : A × B → ℂ :=
  fun p => T (slice p.2 ψ) p.1

lemma ampFun_mem (T : HilbertSp A →L[ℂ] HilbertSp A) (ψ : HilbertSp (A × B)) :
    Memℓp (ampFun T ψ) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have h0 : 0 ≤ fun p : A × B => ‖ampFun T ψ p‖ ^ ((2 : ENNReal).toReal) := fun p => by positivity
  have h2 : (2 : ENNReal).toReal = 2 := by norm_num
  simp only [h2]
  rw [sq_summable_slices _ (fun p => by simp only [Pi.zero_apply]; positivity)]
  refine ⟨fun b => sq_summable (T (slice b ψ)), ?_⟩
  refine Summable.of_nonneg_of_le (fun b => tsum_nonneg fun a => by positivity) (fun b => ?_)
    ((summable_slices ψ).mul_left (‖T‖ ^ 2))
  have := (norm_sq_eq_tsum (T (slice b ψ))).symm
  show ∑' a, ‖ampFun T ψ (a, b)‖ ^ (2:ℝ) ≤ _
  simp only [ampFun]
  rw [this]
  have hle := T.le_opNorm (slice b ψ)
  calc ‖T (slice b ψ)‖ ^ 2 ≤ (‖T‖ * ‖slice b ψ‖) ^ 2 := by gcongr
    _ = _ := by ring


/-- Amplification `T ↦ T ⊗ 1` as a function on `ℓ²(A × B)`. -/
def ampVec (T : HilbertSp A →L[ℂ] HilbertSp A) (ψ : HilbertSp (A × B)) : HilbertSp (A × B) :=
  ⟨ampFun T ψ, ampFun_mem T ψ⟩

lemma slice_ampVec (T : HilbertSp A →L[ℂ] HilbertSp A) (b : B) (ψ : HilbertSp (A × B)) :
    slice b (ampVec T ψ) = T (slice b ψ) := rfl

lemma norm_ampVec_le (T : HilbertSp A →L[ℂ] HilbertSp A) (ψ : HilbertSp (A × B)) :
    ‖ampVec T ψ‖ ≤ ‖T‖ * ‖ψ‖ := by
  have h : ‖ampVec T ψ‖ ^ 2 ≤ (‖T‖ * ‖ψ‖) ^ 2 := by
    rw [norm_sq_eq_tsum_slices, mul_pow, norm_sq_eq_tsum_slices ψ, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun b => ?_) (summable_slices _) ((summable_slices ψ).mul_left _)
    rw [slice_ampVec]
    calc ‖T (slice b ψ)‖ ^ 2 ≤ (‖T‖ * ‖slice b ψ‖) ^ 2 := by
          gcongr; exact T.le_opNorm _
      _ = _ := by ring
  exact le_of_sq_le_sq h (by positivity) |>.trans_eq rfl


lemma ext_slices {ψ φ : HilbertSp (A × B)} (h : ∀ b, slice b ψ = slice b φ) : ψ = φ :=
  Subtype.ext (funext fun p => by
    have := congrArg (fun f : HilbertSp A => (f : A → ℂ) p.1) (h p.2)
    simpa [slice_apply] using this)

/-- Amplification as a bounded operator. -/
def amp (T : HilbertSp A →L[ℂ] HilbertSp A) : HilbertSp (A × B) →L[ℂ] HilbertSp (A × B) :=
  LinearMap.mkContinuous
    { toFun := ampVec T
      map_add' := fun ψ φ => ext_slices fun b => by
        rw [slice_add, slice_ampVec, slice_ampVec, slice_ampVec, slice_add, map_add]
      map_smul' := fun c ψ => ext_slices fun b => by
        rw [slice_smul, slice_ampVec, slice_ampVec, slice_smul, map_smul]; rfl }
    ‖T‖ (norm_ampVec_le T)

lemma slice_amp (T : HilbertSp A →L[ℂ] HilbertSp A) (b : B) (ψ : HilbertSp (A × B)) :
    slice b (amp T ψ) = T (slice b ψ) := rfl

lemma amp_mul (S T : HilbertSp A →L[ℂ] HilbertSp A) :
    (amp (S * T) : HilbertSp (A × B) →L[ℂ] HilbertSp (A × B)) = amp S * amp T :=
  ContinuousLinearMap.ext fun ψ => ext_slices fun b => by
    rw [ContinuousLinearMap.mul_apply, slice_amp, slice_amp, slice_amp]; rfl

lemma amp_one : (amp (1 : HilbertSp A →L[ℂ] HilbertSp A) : HilbertSp (A × B) →L[ℂ] _) = 1 :=
  ContinuousLinearMap.ext fun ψ => ext_slices fun b => by
    rw [slice_amp]; rfl

lemma amp_add (S T : HilbertSp A →L[ℂ] HilbertSp A) :
    (amp (S + T) : HilbertSp (A × B) →L[ℂ] HilbertSp (A × B)) = amp S + amp T :=
  ContinuousLinearMap.ext fun ψ => ext_slices fun b => by
    rw [ContinuousLinearMap.add_apply, slice_amp, slice_add, slice_amp, slice_amp]; rfl

lemma amp_smul (c : ℂ) (T : HilbertSp A →L[ℂ] HilbertSp A) :
    (amp (c • T) : HilbertSp (A × B) →L[ℂ] HilbertSp (A × B)) = c • amp T :=
  ContinuousLinearMap.ext fun ψ => ext_slices fun b => by
    rw [ContinuousLinearMap.smul_apply, slice_amp, slice_smul, slice_amp]; rfl

lemma inner_eq_tsum_slices (φ ψ : HilbertSp (A × B)) :
    inner ℂ φ ψ = ∑' b, inner ℂ (slice b φ) (slice b ψ) := by
  have h1 : Summable fun p : A × B => inner ℂ (φ p) (ψ p) :=
    lp.summable_inner (G := fun _ : A × B => ℂ) φ ψ
  have h2 : ∀ b, Summable fun a : A => inner ℂ (φ (a, b)) (ψ (a, b)) := fun b =>
    lp.summable_inner (G := fun _ : A => ℂ) (slice b φ) (slice b ψ)
  rw [lp.inner_eq_tsum (G := fun _ : A × B => ℂ) φ ψ, tsum_slices _ h1 h2]
  exact tsum_congr fun b => (lp.inner_eq_tsum (G := fun _ : A => ℂ) (slice b φ) (slice b ψ)).symm

lemma amp_adjoint (T : HilbertSp A →L[ℂ] HilbertSp A) :
    (amp (ContinuousLinearMap.adjoint T) : HilbertSp (A × B) →L[ℂ] HilbertSp (A × B)) =
      ContinuousLinearMap.adjoint (amp T) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro φ ψ
  rw [inner_eq_tsum_slices, inner_eq_tsum_slices]
  refine tsum_congr fun b => ?_
  rw [slice_amp, slice_amp, ContinuousLinearMap.adjoint_inner_left]

lemma amp_zero : (amp (0 : HilbertSp A →L[ℂ] HilbertSp A) : HilbertSp (A × B) →L[ℂ] _) = 0 :=
  ContinuousLinearMap.ext fun ψ => ext_slices fun b => by
    rw [slice_amp]; rfl

/-- The amplification `T ↦ T ⊗ 1` as a star homomorphism. -/
def ampStar : (HilbertSp A →L[ℂ] HilbertSp A) →⋆ₐ[ℂ] (HilbertSp (A × B) →L[ℂ] HilbertSp (A × B)) where
  toFun := amp
  map_one' := amp_one
  map_mul' := amp_mul
  map_zero' := amp_zero
  commutes' c := by
    have := amp_smul (B := B) c (1 : HilbertSp A →L[ℂ] HilbertSp A)
    rw [amp_one] at this
    simpa [Algebra.algebraMap_eq_smul_one] using this
  map_star' T := amp_adjoint T
  map_add' := amp_add

lemma ampStar_apply (T : HilbertSp A →L[ℂ] HilbertSp A) :
    (ampStar T : HilbertSp (A × B) →L[ℂ] HilbertSp (A × B)) = amp T := rfl

end InfiniteBosons
