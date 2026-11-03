/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach
/-!

# Asymptotic intertwiners along an asymptotically isometric sequence

Operators that commute with a sequence of maps up to a vanishing error, and the induced
homomorphism.

## i. Overview

Let `V j : E → F` be a uniformly bounded sequence of maps between Hilbert spaces whose Gram matrix
converges, `⟪V j x, V j z⟫ → ⟪x, z⟫`. An operator `B` on `E` is an asymptotic intertwiner of an
operator `A` on `F` when `A (V j ψ) - V j (B ψ) → 0` for every `ψ`. Such a `B` is unique. The
assignment `A ↦ B` is linear and multiplicative and satisfies `‖B‖ ≤ ‖A‖`. It is compatible with
adjoints when both `A` and `A†` have intertwiners. Norm limits of operators with intertwiners have
intertwiners.

The setting contains the connecting maps of the Buchholz algebra. There `V j` adds a particle
that escapes to infinity, and the intertwiner of an `n`-particle observable is the observable seen
by the remaining `n - 1` particles.

## ii. Key results

- `AsymptoticIntertwiner.Intertwines`: the relation.
- `AsymptoticIntertwiner.Intertwines.unique`: the intertwiner is unique.
- `AsymptoticIntertwiner.Intertwines.mul`: it is multiplicative.
- `AsymptoticIntertwiner.Intertwines.star`: it is compatible with adjoints.
- `AsymptoticIntertwiner.Intertwines.norm_le`: it is contractive.

## iii. Table of contents

- A. The relation and its algebra
- B. Uniqueness and adjoints
- C. Contractivity

## iv. References

* None.
-/

@[expose] public section

open Filter Topology
open scoped InnerProductSpace

namespace AsymptoticIntertwiner

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (V : ℕ → E →L[ℂ] F)

/-- `B` is an asymptotic intertwiner of `A`: `A (V j ψ) - V j (B ψ) → 0`. -/
def Intertwines (A : F →L[ℂ] F) (B : E →L[ℂ] E) : Prop :=
  ∀ ψ, Tendsto (fun j => A (V j ψ) - V j (B ψ)) atTop (𝓝 0)

variable {V}

/-!

## A. The relation and its algebra

-/

lemma Intertwines.add {A A' : F →L[ℂ] F} {B B' : E →L[ℂ] E} (h : Intertwines V A B)
    (h' : Intertwines V A' B') : Intertwines V (A + A') (B + B') := fun ψ => by
  have := (h ψ).add (h' ψ)
  simp only [add_zero] at this
  refine this.congr fun j => ?_
  simp only [ContinuousLinearMap.add_apply, map_add]
  abel

lemma Intertwines.smul (c : ℂ) {A : F →L[ℂ] F} {B : E →L[ℂ] E} (h : Intertwines V A B) :
    Intertwines V (c • A) (c • B) := fun ψ => by
  have := (h ψ).const_smul c
  simp only [smul_zero] at this
  refine this.congr fun j => ?_
  simp [smul_sub]

lemma Intertwines.sub {A A' : F →L[ℂ] F} {B B' : E →L[ℂ] E} (h : Intertwines V A B)
    (h' : Intertwines V A' B') : Intertwines V (A - A') (B - B') := by
  have := h.add (h'.smul (-1))
  simpa [sub_eq_add_neg] using this

lemma Intertwines.one : Intertwines V (1 : F →L[ℂ] F) (1 : E →L[ℂ] E) := fun ψ => by
  simp

lemma Intertwines.mul {A A' : F →L[ℂ] F} {B B' : E →L[ℂ] E} (h : Intertwines V A B)
    (h' : Intertwines V A' B') : Intertwines V (A * A') (B * B') := fun ψ => by
  have h1 : Tendsto (fun j => A (A' (V j ψ) - V j (B' ψ))) atTop (𝓝 0) := by
    have := (A.continuous.tendsto 0).comp (h' ψ)
    rwa [map_zero] at this
  have := h1.add (h (B' ψ))
  simp only [add_zero] at this
  refine this.congr fun j => ?_
  simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply, map_sub]
  abel

/-!

## B. Uniqueness and adjoints

-/

section Pairing

variable {C : ℝ} (hC : ∀ j, ‖V j‖ ≤ C)
  (hiso : ∀ x z, Tendsto (fun j => ⟪V j x, V j z⟫_ℂ) atTop (𝓝 ⟪x, z⟫_ℂ))
include hC hiso

/-- **The pairing with the intertwiner**: `⟪V j x, A (V j ψ)⟫ → ⟪x, B ψ⟫`. -/
lemma Intertwines.tendsto_pairing {A : F →L[ℂ] F} {B : E →L[ℂ] E} (h : Intertwines V A B)
    (x ψ : E) : Tendsto (fun j => ⟪V j x, A (V j ψ)⟫_ℂ) atTop (𝓝 ⟪x, B ψ⟫_ℂ) := by
  have h1 := hiso x (B ψ)
  have h2 : Tendsto (fun j => ⟪V j x, A (V j ψ) - V j (B ψ)⟫_ℂ) atTop (𝓝 0) := by
    have hb : ∀ j, ‖⟪V j x, A (V j ψ) - V j (B ψ)⟫_ℂ‖ ≤ (C * ‖x‖) * ‖A (V j ψ) - V j (B ψ)‖ :=
      fun j => (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
        (((V j).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hC j) (norm_nonneg _)))
        (norm_nonneg _))
    have hn : Tendsto (fun j => ‖A (V j ψ) - V j (B ψ)‖) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mp (h ψ)
    have := hn.const_mul (C * ‖x‖)
    rw [mul_zero] at this
    exact squeeze_zero_norm hb this
  have := h1.add h2
  simp only [add_zero] at this
  refine this.congr fun j => ?_
  rw [← inner_add_right]
  congr 1
  abel

/-- **The intertwiner is unique.** -/
lemma Intertwines.unique {A : F →L[ℂ] F} {B B₂ : E →L[ℂ] E} (h : Intertwines V A B)
    (h₂ : Intertwines V A B₂) : B = B₂ := by
  ext ψ
  refine ext_inner_left ℂ fun x => ?_
  exact tendsto_nhds_unique (h.tendsto_pairing hC hiso x ψ) (h₂.tendsto_pairing hC hiso x ψ)

/-- **Compatibility with adjoints**: if `A` and `A†` both have intertwiners then they are adjoint. -/
lemma Intertwines.star_eq {A : F →L[ℂ] F} {B B' : E →L[ℂ] E} (h : Intertwines V A B)
    (h' : Intertwines V (ContinuousLinearMap.adjoint A) B') :
    B' = ContinuousLinearMap.adjoint B := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x ψ
  have e1 := h.tendsto_pairing hC hiso x ψ
  have e2 := h'.tendsto_pairing hC hiso ψ x
  have e3 : ∀ j, ⟪V j x, A (V j ψ)⟫_ℂ =
      starRingEnd ℂ ⟪V j ψ, ContinuousLinearMap.adjoint A (V j x)⟫_ℂ := fun j => by
    rw [← inner_conj_symm, ContinuousLinearMap.adjoint_inner_right]
  simp only [e3] at e1
  have := (e2.star)
  have h4 := tendsto_nhds_unique e1 this
  simpa [inner_conj_symm] using h4.symm

/-- The sequence is asymptotically isometric on vectors. -/
lemma tendsto_norm (y : E) : Tendsto (fun j => ‖V j y‖) atTop (𝓝 ‖y‖) := by
  have e : ∀ z : E, ‖z‖ ^ 2 = RCLike.re ⟪z, z⟫_ℂ := fun z => norm_sq_eq_re_inner z
  have e' : ∀ z : F, ‖z‖ ^ 2 = RCLike.re ⟪z, z⟫_ℂ := fun z => norm_sq_eq_re_inner z
  have h2 : Tendsto (fun j => ‖V j y‖ ^ 2) atTop (𝓝 (‖y‖ ^ 2)) := by
    simp_rw [e, e']
    exact (RCLike.continuous_re.tendsto _).comp (hiso y y)
  have := (Real.continuous_sqrt.tendsto _).comp h2
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

/-- **The intertwiner is contractive**: `‖B‖ ≤ ‖A‖`. -/
lemma Intertwines.norm_le {A : F →L[ℂ] F} {B : E →L[ℂ] E} (h : Intertwines V A B) :
    ‖B‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ψ => ?_
  have hlim := (h.tendsto_pairing hC hiso (B ψ) ψ).norm
  have hrhs : Tendsto (fun j => ‖A‖ * (‖V j (B ψ)‖ * ‖V j ψ‖)) atTop
      (𝓝 (‖A‖ * (‖B ψ‖ * ‖ψ‖))) :=
    ((tendsto_norm hC hiso (B ψ)).mul (tendsto_norm hC hiso ψ)).const_mul _
  have hbound : ∀ j, ‖⟪V j (B ψ), A (V j ψ)⟫_ℂ‖ ≤ ‖A‖ * (‖V j (B ψ)‖ * ‖V j ψ‖) := fun j =>
    (norm_inner_le_norm _ _).trans (by
      calc ‖V j (B ψ)‖ * ‖A (V j ψ)‖ ≤ ‖V j (B ψ)‖ * (‖A‖ * ‖V j ψ‖) :=
            mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
        _ = _ := by ring)
  have hle : ‖⟪B ψ, B ψ⟫_ℂ‖ ≤ ‖A‖ * (‖B ψ‖ * ‖ψ‖) :=
    le_of_tendsto_of_tendsto hlim hrhs (Eventually.of_forall hbound)
  have hxx : ‖⟪B ψ, B ψ⟫_ℂ‖ = ‖B ψ‖ * ‖B ψ‖ := by
    rw [inner_self_eq_norm_sq_to_K]
    simp [sq]
  rw [hxx] at hle
  by_cases h0 : ‖B ψ‖ = 0
  · rw [h0]; positivity
  · have hpos : 0 < ‖B ψ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have : ‖B ψ‖ * ‖B ψ‖ ≤ (‖A‖ * ‖ψ‖) * ‖B ψ‖ := by nlinarith [hle]
    exact le_of_mul_le_mul_right this hpos


/-- **Norm limits of operators with intertwiners have intertwiners.** -/
lemma Intertwines.of_tendsto {A : ℕ → F →L[ℂ] F} {A₀ : F →L[ℂ] F} {B : ℕ → E →L[ℂ] E}
    (h : ∀ i, Intertwines V (A i) (B i)) (hA : Tendsto A atTop (𝓝 A₀)) :
    ∃ B₀, Intertwines V A₀ B₀ := by
  have hdist : ∀ i l, ‖B i - B l‖ ≤ ‖A i - A l‖ := fun i l =>
    ((h i).sub (h l)).norm_le hC hiso
  have hcauchy : CauchySeq B := by
    rw [Metric.cauchySeq_iff'] at *
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hA.cauchySeq ε hε
    exact ⟨N, fun n hn => by
      rw [dist_eq_norm]
      exact (hdist n N).trans_lt (by simpa [dist_eq_norm] using hN n hn)⟩
  obtain ⟨B₀, hB⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨B₀, fun ψ => ?_⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set δ : ℝ := ε / (4 * (C + 1) * (‖ψ‖ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨i, hi⟩ := (Metric.tendsto_nhds.mp hA δ hδpos).and (Metric.tendsto_nhds.mp hB δ hδpos)
    |>.exists
  filter_upwards [(Metric.tendsto_nhds.mp (h i ψ)) (ε / 2) (by positivity)] with j hj
  rw [dist_zero_right] at hj ⊢
  have e1 : ‖(A₀ - A i) (V j ψ)‖ ≤ δ * (C * ‖ψ‖) := by
    refine ((A₀ - A i).le_opNorm _).trans ?_
    have := hi.1
    rw [dist_comm, dist_eq_norm] at this
    exact mul_le_mul this.le (((V j).le_opNorm ψ).trans (mul_le_mul_of_nonneg_right (hC j)
      (norm_nonneg _))) (norm_nonneg _) hδpos.le
  have e2 : ‖V j ((B i - B₀) ψ)‖ ≤ C * (δ * ‖ψ‖) := by
    refine ((V j).le_opNorm _).trans (mul_le_mul (hC j) ?_ (norm_nonneg _) hC0)
    have := hi.2
    rw [dist_eq_norm] at this
    exact ((B i - B₀).le_opNorm ψ).trans (mul_le_mul_of_nonneg_right this.le (norm_nonneg _))
  have e3 : A₀ (V j ψ) - V j (B₀ ψ) = (A₀ - A i) (V j ψ) + (A i (V j ψ) - V j (B i ψ)) +
      V j ((B i - B₀) ψ) := by
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    abel
  rw [e3]
  have : δ * (C * ‖ψ‖) + C * (δ * ‖ψ‖) < ε / 2 := by
    have : δ * (C * ‖ψ‖) + C * (δ * ‖ψ‖) = 2 * δ * (C * ‖ψ‖) := by ring
    rw [this, hδ]
    rw [show 2 * (ε / (4 * (C + 1) * (‖ψ‖ + 1))) * (C * ‖ψ‖) =
      (ε / 2) * ((C * ‖ψ‖) / ((C + 1) * (‖ψ‖ + 1))) by field_simp; ring]
    have : (C * ‖ψ‖) / ((C + 1) * (‖ψ‖ + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith [norm_nonneg ψ]
    nlinarith [hε]
  calc ‖(A₀ - A i) (V j ψ) + (A i (V j ψ) - V j (B i ψ)) + V j ((B i - B₀) ψ)‖
      ≤ ‖(A₀ - A i) (V j ψ)‖ + ‖A i (V j ψ) - V j (B i ψ)‖ + ‖V j ((B i - B₀) ψ)‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < ε := by linarith

end Pairing

/-!

## C. The algebra of operators with intertwiners

-/

section Algebra

variable (V) in
/-- The operators `A` such that both `A` and `A†` have asymptotic intertwiners. -/
def domain : Set (F →L[ℂ] F) :=
  {A | (∃ B, Intertwines V A B) ∧ ∃ B', Intertwines V (star A) B'}

/-- The star subalgebra of operators with intertwiners (for a bounded asymptotically isometric
sequence). -/
def algebra {C : ℝ} (hC : ∀ j, ‖V j‖ ≤ C)
    (hiso : ∀ x z, Tendsto (fun j => ⟪V j x, V j z⟫_ℂ) atTop (𝓝 ⟪x, z⟫_ℂ)) :
    StarSubalgebra ℂ (F →L[ℂ] F) where
  carrier := domain V
  add_mem' := fun {a b} ha hb =>
    ⟨⟨_, ha.1.choose_spec.add hb.1.choose_spec⟩, ⟨ha.2.choose + hb.2.choose, by
      rw [star_add]; exact ha.2.choose_spec.add hb.2.choose_spec⟩⟩
  zero_mem' := ⟨⟨0, fun ψ => by simp⟩, ⟨0, fun ψ => by simp⟩⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨⟨_, ha.1.choose_spec.mul hb.1.choose_spec⟩, ⟨hb.2.choose * ha.2.choose, by
      rw [star_mul]; exact hb.2.choose_spec.mul ha.2.choose_spec⟩⟩
  one_mem' := ⟨⟨1, Intertwines.one⟩, ⟨1, by rw [star_one]; exact Intertwines.one⟩⟩
  algebraMap_mem' := fun r => by
    refine ⟨⟨r • 1, ?_⟩, ⟨star r • 1, ?_⟩⟩
    · have := (Intertwines.one (V := V)).smul r
      simpa [Algebra.algebraMap_eq_smul_one] using this
    · have := (Intertwines.one (V := V)).smul (star r)
      simpa [Algebra.algebraMap_eq_smul_one, star_smul] using this
  star_mem' := fun {a} ha => ⟨ha.2, ⟨ha.1.choose, by rw [star_star]; exact ha.1.choose_spec⟩⟩

variable {C : ℝ} (hC : ∀ j, ‖V j‖ ≤ C)
  (hiso : ∀ x z, Tendsto (fun j => ⟪V j x, V j z⟫_ℂ) atTop (𝓝 ⟪x, z⟫_ℂ))

/-- **The induced star homomorphism**: an operator with intertwiners is sent to its intertwiner. -/
noncomputable def hom : algebra hC hiso →⋆ₐ[ℂ] (E →L[ℂ] E) where
  toFun A := A.2.1.choose
  map_one' := Intertwines.unique hC hiso (Subtype.property (1 : algebra hC hiso)).1.choose_spec
    Intertwines.one
  map_mul' A A' := Intertwines.unique hC hiso
    (Subtype.property (A * A' : algebra hC hiso)).1.choose_spec
    (A.2.1.choose_spec.mul A'.2.1.choose_spec)
  map_zero' := Intertwines.unique hC hiso
    (Subtype.property (0 : algebra hC hiso)).1.choose_spec (fun ψ => by simp)
  map_add' A A' := Intertwines.unique hC hiso
    (Subtype.property (A + A' : algebra hC hiso)).1.choose_spec
    (A.2.1.choose_spec.add A'.2.1.choose_spec)
  commutes' r := by
    have h1 := Subtype.property (algebraMap ℂ (algebra hC hiso) r)
    have h2 : Intertwines V (algebraMap ℂ (F →L[ℂ] F) r) (algebraMap ℂ (E →L[ℂ] E) r) := by
      have := (Intertwines.one (V := V)).smul r
      simpa [Algebra.algebraMap_eq_smul_one] using this
    exact Intertwines.unique hC hiso h1.1.choose_spec h2
  map_star' A := by
    have h1 := (Subtype.property (star A : algebra hC hiso)).1.choose_spec
    have h2 : Intertwines V (star (A : F →L[ℂ] F)) (star A.2.1.choose) := by
      have := Intertwines.star_eq hC hiso A.2.1.choose_spec A.2.2.choose_spec
      have e : star A.2.1.choose = A.2.2.choose := by
        rw [ContinuousLinearMap.star_eq_adjoint, this]
      rw [e]
      exact A.2.2.choose_spec
    exact Intertwines.unique hC hiso h1 h2

/-- **The algebra of operators with intertwiners is closed.** -/
lemma isClosed_algebra : IsClosed (algebra hC hiso : Set (F →L[ℂ] F)) := by
  refine IsSeqClosed.isClosed fun A A₀ hA hlim => ?_
  refine ⟨?_, ?_⟩
  · obtain ⟨B₀, h⟩ := Intertwines.of_tendsto hC hiso (fun i => (hA i).1.choose_spec) hlim
    exact ⟨B₀, h⟩
  · have hlim' : Tendsto (fun i => star (A i)) atTop (𝓝 (star A₀)) :=
      (continuous_star.tendsto _).comp hlim
    obtain ⟨B₀, h⟩ := Intertwines.of_tendsto hC hiso (fun i => (hA i).2.choose_spec) hlim'
    exact ⟨B₀, h⟩

/-- The homomorphism satisfies the intertwining relation. -/
lemma hom_spec (A : algebra hC hiso) : Intertwines V (A : F →L[ℂ] F) (hom hC hiso A) :=
  A.2.1.choose_spec

/-- The homomorphism is contractive. -/
lemma norm_hom_le (A : algebra hC hiso) : ‖hom hC hiso A‖ ≤ ‖(A : F →L[ℂ] F)‖ :=
  (hom_spec hC hiso A).norm_le hC hiso

end Algebra

end AsymptoticIntertwiner
