/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Operators.SpectralTheory.SpectralMeasure
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.Measure.Complex
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!

# Weak-operator spectral measures

The norm-valued `SpectralMeasure` is useful in finite-dimensional situations, but it is not the
right countable-additivity notion for an infinite-dimensional spectral theorem: a family of
orthogonal projections is generally σ-additive in the weak operator topology, not in operator
norm.  This file supplies the representation-level replacement.

`WOTSpectralMeasure α H` is a projection-valued measure whose values are the type copy
`H →WOT[ℂ] H`.  The underlying `ContinuousLinearMap` is still a bounded operator, so all algebraic
projection statements remain available; only the topology used by `VectorMeasure` changes.

The conversion from the older norm-valued `SpectralMeasure` is intentionally one-way.  A norm
σ-additive spectral measure is automatically WOT σ-additive, while the converse is false in
infinite dimension.

-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace Function
open ContinuousLinearMap ContinuousLinearMapWOT MeasureTheory Set

namespace QuantumMechanics

@[nolint unusedArguments]
instance (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    IsAddTorsionFree (H →WOT[ℂ] H) where
  nsmul_right_injective n hn := by
    refine Function.HasLeftInverse.injective ⟨fun f ↦ (n : ℂ)⁻¹ • f, fun x ↦ ?_⟩
    simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_ne_zero (R := ℂ), hn]

/-- A projection-valued measure with weak-operator σ-additivity. -/
structure WOTSpectralMeasure
    (α : Type*) [MeasurableSpace α]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends VectorMeasure α (H →WOT[ℂ] H) where
  isStarProjection' : ∀ A, IsStarProjection (measureOf' A)
  univ' : measureOf' univ = 1

namespace WOTSpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μS : WOTSpectralMeasure α H)

attribute [coe] toVectorMeasure

instance instCoeVectorMeasure : Coe (WOTSpectralMeasure α H)
    (VectorMeasure α (H →WOT[ℂ] H)) := ⟨toVectorMeasure⟩

instance instCoeFun : CoeFun (WOTSpectralMeasure α H) fun _ ↦ Set α → H →WOT[ℂ] H :=
  ⟨fun μS ↦ ⇑μS.toVectorMeasure⟩

lemma isStarProjection (A : Set α) : IsStarProjection (μS A) := μS.isStarProjection' A

@[simp]
lemma univ : μS univ = 1 := μS.univ'

lemma apply_eq_zero_of_not_measurableSet {A : Set α} (hA : ¬MeasurableSet A) : μS A = 0 :=
  μS.not_measurable' hA

lemma comp_self (A : Set α) : μS A * μS A = μS A :=
  (μS.isStarProjection A).isIdempotentElem

lemma comp_of_disjoint {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A)
    (hB : MeasurableSet B) : μS A * μS B = 0 := by
  have hp : μS A * μS (A ∪ B) = μS A := by
    refine (IsStarProjection.sub_iff_mul_eq_left (μS.isStarProjection A)
      (μS.isStarProjection (A ∪ B))).mp ?_
    simpa [μS.of_union h hA hB] using μS.isStarProjection B
  rw [μS.of_union h hA hB, mul_add, μS.comp_self] at hp
  apply add_left_cancel (a := μS A)
  simpa using hp

lemma comp_eq_of_inter {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μS A * μS B = μS (A ∩ B) := by
  nth_rw 1 [← inter_union_sdiff B A, ← inter_union_sdiff A B]
  simp only [μS.of_union, hA.inter hB, hB.inter hA, hA.diff hB, hB.diff hA,
    disjoint_sdiff_inter.symm, add_mul, mul_add]
  rw [inter_comm B A, μS.comp_of_disjoint disjoint_sdiff_inter (hA.diff hB) (hA.inter hB),
    inter_comm A B, μS.comp_of_disjoint disjoint_sdiff_inter.symm (hB.inter hA) (hB.diff hA)]
  simp [μS.comp_self, μS.comp_of_disjoint disjoint_sdiff_sdiff (hA.diff hB) (hB.diff hA)]

lemma commute (A B : Set α) : Commute (μS A) (μS B) := by
  by_cases hAB : MeasurableSet A ∧ MeasurableSet B
  · simp [commute_iff_eq, comp_eq_of_inter, hAB, inter_comm]
  · rcases not_and_or.mp hAB with hA | hB <;> simp [*]

/-- Push a weak spectral measure forward along a measurable change of spectral variable. -/
def map {β : Type*} [MeasurableSpace β] (f : α → β) (hf : Measurable f) :
    WOTSpectralMeasure β H where
  toVectorMeasure := μS.toVectorMeasure.map f
  isStarProjection' S := by
    change IsStarProjection ((μS.toVectorMeasure.map f) S)
    by_cases hS : MeasurableSet S
    · rw [MeasureTheory.VectorMeasure.map_apply _ hf hS]
      exact μS.isStarProjection _
    · simp [MeasureTheory.VectorMeasure.map, hf, hS]
  univ' := by
    change (μS.toVectorMeasure.map f) Set.univ = 1
    rw [MeasureTheory.VectorMeasure.map_apply _ hf MeasurableSet.univ]
    simp

@[simp]
lemma map_apply {β : Type*} [MeasurableSpace β] (f : α → β) (hf : Measurable f)
    {S : Set β} (hS : MeasurableSet S) :
    μS.map f hf S = μS (f ⁻¹' S) := by
    change (μS.toVectorMeasure.map f) S = μS (f ⁻¹' S)
    exact MeasureTheory.VectorMeasure.map_apply _ hf hS

lemma map_map_apply {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (f : α → β) (g : β → γ) (hf : Measurable f) (hg : Measurable g)
    {S : Set γ} (hS : MeasurableSet S) :
    (μS.map f hf).map g hg S = μS ((g ∘ f) ⁻¹' S) := by
  rw [(μS.map f hf).map_apply g hg hS, μS.map_apply f hf (hg hS)]
  rfl

theorem map_map {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (f : α → β) (g : β → γ) (hf : Measurable f) (hg : Measurable g) :
    (μS.map f hf).map g hg = μS.map (g ∘ f) (hg.comp hf) := by
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  rw [μS.map_map_apply f g hf hg hS, μS.map_apply (g ∘ f) (hg.comp hf) hS]

theorem map_id : μS.map id measurable_id = μS := by
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  rw [μS.map_apply id measurable_id hS]
  rfl

/-! ## Unitary transport -/

/-- Conjugation of a bounded operator by a Hilbert-space unitary, viewed in the WOT type. -/
@[nolint unusedArguments]
def unitaryConj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') (A : H →WOT[ℂ] H) : H' →WOT[ℂ] H' :=
  ContinuousLinearMapWOT.ofCLM
    (u.toLinearIsometry.toContinuousLinearMap.comp
      ((ContinuousLinearMapWOT.toCLM A).comp u.symm.toLinearIsometry.toContinuousLinearMap))

/-- Unitary conjugation is additive on WOT operators. -/
def unitaryConjAddHom {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') :
    (H →WOT[ℂ] H) →+ (H' →WOT[ℂ] H') where
  toFun := unitaryConj u
  map_zero' := by
    apply ContinuousLinearMapWOT.toCLM_injective
    simp [unitaryConj]
  map_add' A B := by
    apply ContinuousLinearMapWOT.toCLM_injective
    simp [unitaryConj]

lemma continuous_unitaryConjAddHom {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') :
    Continuous (unitaryConjAddHom u) := by
  rw [ContinuousLinearMapWOT.continuous_iff]
  intro x y
  change Continuous (fun A : H →WOT[ℂ] H ↦ ⟪y, (unitaryConj u A) x⟫_ℂ)
  dsimp [unitaryConj]
  change Continuous (fun A : H →WOT[ℂ] H ↦
    ⟪y, u ((ContinuousLinearMapWOT.toCLM A) (u.symm x))⟫_ℂ)
  have heq : (fun A : H →WOT[ℂ] H ↦
      ⟪y, u ((ContinuousLinearMapWOT.toCLM A) (u.symm x))⟫_ℂ) =
      fun A ↦ ⟪u.symm y, A (u.symm x)⟫_ℂ := by
    funext A
    exact (u.symm.inner_map_eq_flip y
      ((ContinuousLinearMapWOT.toCLM A) (u.symm x))).symm
  rw [heq]
  fun_prop

@[nolint unusedArguments]
lemma unitaryConj_mul {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') (A B : H →WOT[ℂ] H) :
    unitaryConj u (A * B) = unitaryConj u A * unitaryConj u B := by
  apply ContinuousLinearMapWOT.toCLM_injective
  ext x
  simp [unitaryConj, ContinuousLinearMap.comp_apply]

lemma unitaryConj_star {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') (A : H →WOT[ℂ] H) :
    unitaryConj u (star A) = star (unitaryConj u A) := by
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  change ⟪y, u ((star (ContinuousLinearMapWOT.toCLM A)) (u.symm x))⟫_ℂ =
    ⟪y, (star (ContinuousLinearMapWOT.toCLM (unitaryConj u A))) x⟫_ℂ
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  change ⟪y, u ((ContinuousLinearMap.adjoint
      (ContinuousLinearMapWOT.toCLM A)) (u.symm x))⟫_ℂ =
    ⟪u ((ContinuousLinearMapWOT.toCLM A) (u.symm y)), x⟫_ℂ
  calc
    _ = ⟪u.symm y, (ContinuousLinearMap.adjoint
        (ContinuousLinearMapWOT.toCLM A)) (u.symm x)⟫_ℂ :=
      (u.symm.inner_map_eq_flip y _).symm
    _ = ⟪(ContinuousLinearMapWOT.toCLM A) (u.symm y), u.symm x⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = ⟪u ((ContinuousLinearMapWOT.toCLM A) (u.symm y)), x⟫_ℂ :=
      (u.inner_map_eq_flip _ _).symm

@[nolint unusedArguments]
lemma unitaryConj_one {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') :
    unitaryConj u (1 : H →WOT[ℂ] H) = 1 := by
  apply ContinuousLinearMapWOT.toCLM_injective
  ext x
  simp [unitaryConj]

/-- Transport a WOT spectral measure through a Hilbert-space unitary. -/
def unitaryConjSpectralMeasure {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H') :
    WOTSpectralMeasure α H → WOTSpectralMeasure α H' := fun μS ↦ {
  toVectorMeasure := μS.toVectorMeasure.mapRange (unitaryConjAddHom u)
    (continuous_unitaryConjAddHom u)
  isStarProjection' S := by
    change IsStarProjection (unitaryConj u (μS S))
    refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
    · change unitaryConj u (μS S) * unitaryConj u (μS S) = unitaryConj u (μS S)
      rw [← unitaryConj_mul]
      exact congrArg (unitaryConj u) (μS.comp_self S)
    · change star (unitaryConj u (μS S)) = unitaryConj u (μS S)
      rw [← unitaryConj_star]
      exact congrArg (unitaryConj u) (μS.isStarProjection S).isSelfAdjoint
  univ' := by
    change unitaryConj u (μS Set.univ) = 1
    rw [μS.univ, unitaryConj_one] }

@[simp]
lemma unitaryConjSpectralMeasure_apply {H' : Type*} [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] (u : H ≃ₗᵢ[ℂ] H')
    (μS : WOTSpectralMeasure α H) (S : Set α) :
    unitaryConjSpectralMeasure u μS S = unitaryConj u (μS S) := by
  rfl

/-! ## The WOT test interface -/

/-- The σ-additivity statement seen by vectors and test vectors.  This is often more convenient
than mentioning the `WOT` type directly when proving spectral formulas. -/
lemma hasSum_inner {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i))
    (hdisj : Pairwise (Disjoint on f)) (x y : H) :
    HasSum (fun i ↦ ⟪y, μS (f i) x⟫_ℂ) ⟪y, μS (⋃ i, f i) x⟫_ℂ := by
  have h := μS.toVectorMeasure.m_iUnion hf hdisj
  let g : (H →WOT[ℂ] H) →+ ℂ :=
    { toFun := fun T ↦ ⟪y, T x⟫_ℂ
      map_zero' := by simp
      map_add' := by
        intro T U
        change ⟪y, T x + U x⟫_ℂ = _
        rw [inner_add_right] }
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  change HasSum (fun i ↦ g (μS (f i))) (g (μS (⋃ i, f i)))
  exact h.map g hg

/-! ## Scalar spectral measures and weak moments -/

/-- Evaluation of a WOT operator between two test vectors. -/
def innerEvaluation (x y : H) : (H →WOT[ℂ] H) →+ ℂ where
  toFun A := ⟪y, A x⟫_ℂ
  map_zero' := by simp
  map_add' A B := by
    change ⟪y, (A + B) x⟫_ℂ = _
    rw [ContinuousLinearMapWOT.add_apply, inner_add_right]

lemma continuous_innerEvaluation (x y : H) :
    Continuous (innerEvaluation (H := H) x y) := by
  change Continuous (fun A : H →WOT[ℂ] H ↦ ⟪y, A x⟫_ℂ)
  fun_prop

/-- The complex scalar measure obtained by testing a WOT spectral measure against `x` and `y`.
This is the measure used to state the unbounded reconstruction law weakly. -/
def scalarMeasure (x y : H) : ComplexMeasure α :=
  μS.toVectorMeasure.mapRange (innerEvaluation (H := H) x y)
    (continuous_innerEvaluation x y)

@[simp]
lemma scalarMeasure_apply (x y : H) (S : Set α) :
    μS.scalarMeasure x y S = ⟪y, μS S x⟫_ℂ := by
  simp [scalarMeasure, innerEvaluation]

lemma scalarMeasure_map {β : Type*} [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (x y : H) :
    (μS.map f hf).scalarMeasure x y = (μS.scalarMeasure x y).map f := by
  apply VectorMeasure.ext
  intro S hS
  rw [scalarMeasure_apply]
  change ⟪y, (μS.map f hf) S x⟫_ℂ = _
  rw [μS.map_apply f hf hS]
  rw [MeasureTheory.VectorMeasure.map_apply _ hf hS]
  rw [scalarMeasure_apply]

/-- A weak spectral measure is determined by all of its scalar matrix-coefficient measures.
This is the extensionality principle used when comparing two spectral constructions obtained by
different bounded or unbounded routes. -/
theorem ext_of_scalarMeasure_eq {μS νS : WOTSpectralMeasure α H}
    (h : ∀ x y : H, μS.scalarMeasure x y = νS.scalarMeasure x y) : μS = νS := by
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  change μS.scalarMeasure x y S = νS.scalarMeasure x y S
  rw [h x y]


/-! ## Positive diagonal measures -/

/- A weak PVM gives a positive scalar measure on every vector state.  This is
the measure-theoretic input for the bounded and unbounded spectral integrals;
it is deliberately proved here, before any operator-valued integral is
introduced. -/

lemma re_inner_nonneg (S : Set α) (x : H) :
    0 ≤ (⟪x, μS S x⟫_ℂ).re := by
  let p : H →L[ℂ] H := (ContinuousLinearMapWOT.toCLM (μS S))
  have hp := μS.isStarProjection S
  have hmul : p * p = p := by
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isIdempotentElem
  have hstar : ContinuousLinearMap.adjoint p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isSelfAdjoint
  have hinner : ⟪x, p x⟫_ℂ = ⟪p x, p x⟫_ℂ := by
    calc
      ⟪x, p x⟫_ℂ = ⟪x, p (p x)⟫_ℂ := by
        congr 1
        exact (congrArg (fun q : H →L[ℂ] H => q x) hmul).symm
      _ = ⟪x, ContinuousLinearMap.adjoint p (p x)⟫_ℂ := by rw [hstar]
      _ = ⟪p x, p x⟫_ℂ := ContinuousLinearMap.adjoint_inner_right p x (p x)
  change 0 ≤ (⟪x, p x⟫_ℂ).re
  rw [hinner]
  exact inner_self_nonneg (𝕜 := ℂ) (x := p x)

lemma re_inner_eq_norm_sq (S : Set α) (x : H) :
    (⟪x, μS S x⟫_ℂ).re = ‖μS S x‖ ^ 2 := by
  let p : H →L[ℂ] H := (ContinuousLinearMapWOT.toCLM (μS S))
  have hp := μS.isStarProjection S
  have hmul : p * p = p := by
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isIdempotentElem
  have hstar : ContinuousLinearMap.adjoint p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isSelfAdjoint
  have hinner : ⟪x, p x⟫_ℂ = ⟪p x, p x⟫_ℂ := by
    calc
      ⟪x, p x⟫_ℂ = ⟪x, p (p x)⟫_ℂ := by
        congr 1
        exact (congrArg (fun q : H →L[ℂ] H => q x) hmul).symm
      _ = ⟪x, ContinuousLinearMap.adjoint p (p x)⟫_ℂ := by rw [hstar]
      _ = ⟪p x, p x⟫_ℂ := ContinuousLinearMap.adjoint_inner_right p x (p x)
  change (⟪x, p x⟫_ℂ).re = ‖p x‖ ^ 2
  rw [hinner]
  have hi : (⟪p x, p x⟫_ℂ).re = ‖p x‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (p x)
  exact hi

lemma inner_eq_inner_projection (S : Set α) (x : H) :
    ⟪x, μS S x⟫_ℂ = ⟪μS S x, μS S x⟫_ℂ := by
  let p : H →L[ℂ] H := (ContinuousLinearMapWOT.toCLM (μS S))
  have hp := μS.isStarProjection S
  have hmul : p * p = p := by
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isIdempotentElem
  have hstar : ContinuousLinearMap.adjoint p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isSelfAdjoint
  change ⟪x, p x⟫_ℂ = ⟪p x, p x⟫_ℂ
  calc
    ⟪x, p x⟫_ℂ = ⟪x, p (p x)⟫_ℂ := by
      congr 1
      exact (congrArg (fun q : H →L[ℂ] H => q x) hmul).symm
    _ = ⟪x, ContinuousLinearMap.adjoint p (p x)⟫_ℂ := by rw [hstar]
    _ = ⟪p x, p x⟫_ℂ := ContinuousLinearMap.adjoint_inner_right p x (p x)

lemma inner_eq_zero_of_disjoint {A B : Set α} (h : Disjoint A B)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (x : H) :
    ⟪μS A x, μS B x⟫_ℂ = 0 := by
  let pA : H →L[ℂ] H := (ContinuousLinearMapWOT.toCLM (μS A))
  let pB : H →L[ℂ] H := (ContinuousLinearMapWOT.toCLM (μS B))
  have hcomp : pA * pB = 0 := by
    exact congrArg ContinuousLinearMapWOT.toCLM (μS.comp_of_disjoint h hA hB)
  have hstar : ContinuousLinearMap.adjoint pA = pA := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM (μS.isStarProjection A).isSelfAdjoint
  change ⟪pA x, pB x⟫_ℂ = 0
  calc
    ⟪pA x, pB x⟫_ℂ = ⟪x, ContinuousLinearMap.adjoint pA (pB x)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right pA x (pB x)).symm
    _ = ⟪x, pA (pB x)⟫_ℂ := by rw [hstar]
    _ = ⟪x, (pA * pB) x⟫_ℂ := by rfl
    _ = 0 := by rw [hcomp]; simp

lemma diagonal_tsum {f : ℕ → Set α} (hf : ∀ i, MeasurableSet (f i))
    (hdisj : Pairwise (Disjoint on f)) (x : H) :
    ENNReal.ofReal (⟪x, μS (⋃ i, f i) x⟫_ℂ).re =
      ∑' i, ENNReal.ofReal (⟪x, μS (f i) x⟫_ℂ).re := by
  have hs := μS.hasSum_inner hf hdisj x x
  have hre : HasSum (fun i ↦ (⟪x, μS (f i) x⟫_ℂ).re)
      (⟪x, μS (⋃ i, f i) x⟫_ℂ).re :=
    hs.map Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous
  have hnonneg : ∀ i, 0 ≤ (⟪x, μS (f i) x⟫_ℂ).re :=
    fun i ↦ μS.re_inner_nonneg (f i) x
  calc
    ENNReal.ofReal (⟪x, μS (⋃ i, f i) x⟫_ℂ).re =
        ENNReal.ofReal (∑' i, (⟪x, μS (f i) x⟫_ℂ).re) :=
      congrArg ENNReal.ofReal hre.tsum_eq.symm
    _ = ∑' i, ENNReal.ofReal (⟪x, μS (f i) x⟫_ℂ).re :=
      ENNReal.ofReal_tsum_of_nonneg hnonneg hre.summable

/-- The positive scalar measure obtained by testing a weak PVM on a vector.

Its value on a measurable set is `ofReal (re ⟪x,E(S)x⟫)`.  The projection
identity below shows that this is the usual vector-state spectral measure. -/
noncomputable def diagonalMeasure (x : H) : Measure α := by
  let m : ∀ S : Set α, MeasurableSet S → ENNReal :=
    fun S _ => ENNReal.ofReal (⟪x, μS S x⟫_ℂ).re
  have hm_empty : m ∅ MeasurableSet.empty = 0 := by simp [m]
  have hm_iUnion : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, MeasurableSet (f i)),
      Pairwise (Disjoint on f) →
        m (⋃ i, f i) (MeasurableSet.iUnion hf) = ∑' i, m (f i) (hf i) := by
    intro f hf hdisj
    simpa [m] using μS.diagonal_tsum hf hdisj x
  exact Measure.ofMeasurable m hm_empty hm_iUnion

lemma diagonalMeasure_apply (x : H) (S : Set α) (hS : MeasurableSet S) :
    μS.diagonalMeasure x S = ENNReal.ofReal (⟪x, μS S x⟫_ℂ).re := by
  simp only [diagonalMeasure, Measure.ofMeasurable_apply _ hS]

lemma diagonalMeasure_apply_eq_norm_sq (x : H) (S : Set α) (hS : MeasurableSet S) :
    μS.diagonalMeasure x S = ENNReal.ofReal (‖μS S x‖ ^ 2) := by
  rw [μS.diagonalMeasure_apply x S hS, μS.re_inner_eq_norm_sq S x]

lemma diagonalMeasure_univ (x : H) :
    μS.diagonalMeasure x Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [μS.diagonalMeasure_apply x Set.univ MeasurableSet.univ, μS.univ]
  change ENNReal.ofReal (⟪x, x⟫_ℂ).re = _
  have hi : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [hi]

lemma diagonalMeasure_map {β : Type*} [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (x : H) :
    (μS.map f hf).diagonalMeasure x = Measure.map f (μS.diagonalMeasure x) := by
  apply Measure.ext
  intro S hS
  rw [(μS.map f hf).diagonalMeasure_apply x S hS,
    Measure.map_apply hf hS,
    μS.diagonalMeasure_apply x (f ⁻¹' S) (hS.preimage hf)]
  have hmap : μS.map f hf S = μS (f ⁻¹' S) := μS.map_apply f hf hS
  rw [hmap]

instance diagonalMeasure_isFinite (x : H) : IsFiniteMeasure (μS.diagonalMeasure x) where
  measure_univ_lt_top := by
    rw [μS.diagonalMeasure_univ]
    exact ENNReal.ofReal_lt_top

lemma diagonalMeasure_neg (x : H) :
    μS.diagonalMeasure (-x) = μS.diagonalMeasure x := by
  apply Measure.ext
  intro S hS
  rw [μS.diagonalMeasure_apply _ _ hS, μS.diagonalMeasure_apply _ _ hS]
  simp [inner_neg_left, inner_neg_right]

lemma diagonalMeasure_I_smul (x : H) :
    μS.diagonalMeasure (Complex.I • x) = μS.diagonalMeasure x := by
  apply Measure.ext
  intro S hS
  rw [μS.diagonalMeasure_apply _ _ hS, μS.diagonalMeasure_apply _ _ hS]
  simp [inner_smul_left, inner_smul_right]

lemma diagonalMeasure_smul (c : ℂ) (x : H) :
    μS.diagonalMeasure (c • x) = ENNReal.ofReal (‖c‖ ^ 2) • μS.diagonalMeasure x := by
  apply Measure.ext
  intro S hS
  rw [Measure.smul_apply, μS.diagonalMeasure_apply _ _ hS,
    μS.diagonalMeasure_apply _ _ hS]
  have hinner :
      (⟪c • x, μS S (c • x)⟫_ℂ).re =
        ‖c‖ ^ 2 * (⟪x, μS S x⟫_ℂ).re := by
    simp only [map_smul, inner_smul_left, inner_smul_right]
    simp [Complex.mul_re, Complex.mul_im]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hinner]
  change ENNReal.ofReal (‖c‖ ^ 2 * (⟪x, μS S x⟫_ℂ).re) =
    ENNReal.ofReal (‖c‖ ^ 2) * ENNReal.ofReal (⟪x, μS S x⟫_ℂ).re
  rw [ENNReal.ofReal_mul (sq_nonneg ‖c‖)]

lemma diagonalMeasure_parallelogram (x y : H) :
    μS.diagonalMeasure (x + y) + μS.diagonalMeasure (x - y) =
      (μS.diagonalMeasure x + μS.diagonalMeasure x) +
        (μS.diagonalMeasure y + μS.diagonalMeasure y) := by
  apply Measure.ext
  intro S hS
  rw [Measure.add_apply, Measure.add_apply, Measure.add_apply, Measure.add_apply,
    μS.diagonalMeasure_apply (x + y) S hS, μS.diagonalMeasure_apply (x - y) S hS,
    μS.diagonalMeasure_apply x S hS, μS.diagonalMeasure_apply y S hS]
  have h₁ : 0 ≤ (⟪x + y, μS S (x + y)⟫_ℂ).re := μS.re_inner_nonneg S (x + y)
  have h₂ : 0 ≤ (⟪x - y, μS S (x - y)⟫_ℂ).re := μS.re_inner_nonneg S (x - y)
  have h₃ : 0 ≤ (⟪x, μS S x⟫_ℂ).re := μS.re_inner_nonneg S x
  have h₄ : 0 ≤ (⟪y, μS S y⟫_ℂ).re := μS.re_inner_nonneg S y
  rw [← ENNReal.ofReal_add h₁ h₂]
  have hreal :
      (⟪x + y, μS S (x + y)⟫_ℂ).re +
          (⟪x - y, μS S (x - y)⟫_ℂ).re =
        2 * (⟪x, μS S x⟫_ℂ).re + 2 * (⟪y, μS S y⟫_ℂ).re := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
      inner_sub_right, Complex.add_re, Complex.sub_re,
      inner_neg_left, inner_neg_right]
    ring
  rw [hreal]
  calc
    ENNReal.ofReal (2 * (⟪x, μS S x⟫_ℂ).re + 2 * (⟪y, μS S y⟫_ℂ).re) =
        ENNReal.ofReal (2 * (⟪x, μS S x⟫_ℂ).re) +
          ENNReal.ofReal (2 * (⟪y, μS S y⟫_ℂ).re) :=
      ENNReal.ofReal_add
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h₃)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h₄)
    _ = ENNReal.ofReal (⟪x, μS S x⟫_ℂ).re +
          ENNReal.ofReal (⟪x, μS S x⟫_ℂ).re +
          (ENNReal.ofReal (⟪y, μS S y⟫_ℂ).re +
            ENNReal.ofReal (⟪y, μS S y⟫_ℂ).re) := by
      rw [show 2 * (⟪x, μS S x⟫_ℂ).re =
          (⟪x, μS S x⟫_ℂ).re + (⟪x, μS S x⟫_ℂ).re by ring]
      rw [show 2 * (⟪y, μS S y⟫_ℂ).re =
          (⟪y, μS S y⟫_ℂ).re + (⟪y, μS S y⟫_ℂ).re by ring]
      rw [ENNReal.ofReal_add h₃ h₃, ENNReal.ofReal_add h₄ h₄]

/-! ## The finite/simple bounded integral -/

/-- The operator integral of a measurable simple multiplier.

This is the finite-sum stage of the bounded spectral calculus.  It is defined
in the weak-operator representation because a weak PVM need not have finite
variation in operator norm. -/
noncomputable def simpleIntegral (f : SimpleFunc α ℂ) : H →WOT[ℂ] H :=
  ∑ z ∈ f.range, z • μS (f ⁻¹' {z})

lemma simpleIntegral_inner (f : SimpleFunc α ℂ) (x y : H) :
    ⟪y, simpleIntegral μS f x⟫_ℂ =
      ∑ z ∈ f.range, z * μS.scalarMeasure x y (f ⁻¹' {z}) := by
  change (innerEvaluation (H := H) x y)
      (∑ z ∈ f.range, z • μS (f ⁻¹' {z})) = _
  rw [map_sum]
  simp [innerEvaluation, ContinuousLinearMapWOT.smul_apply, inner_smul_right,
    scalarMeasure_apply]

lemma simpleIntegral_norm_sq (f : SimpleFunc α ℂ) (x : H) :
    ENNReal.ofReal (‖simpleIntegral μS f x‖ ^ 2) =
      ∑ z ∈ f.range, ENNReal.ofReal (‖z‖ ^ 2) *
        (μS.diagonalMeasure x) (f ⁻¹' {z}) := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [simpleIntegral]
  change ENNReal.ofReal (⟪(∑ z ∈ f.range, z • (μS (f ⁻¹' {z}))) x,
      (∑ z ∈ f.range, z • (μS (f ⁻¹' {z}))) x⟫_ℂ).re = _
  have hsum : ∀ (s : Finset ℂ),
      (∑ z ∈ s, z • (μS (f ⁻¹' {z}))) x =
        ∑ z ∈ s, z • (μS (f ⁻¹' {z})) x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert z s hz ih =>
      simp only [Finset.sum_insert hz]
      rw [ContinuousLinearMapWOT.add_apply, ih]
      simp [ContinuousLinearMapWOT.smul_apply]
  rw [hsum]
  simp only [sum_inner, inner_sum]
  simp only [inner_smul_left, inner_smul_right]
  have hRHS :
      (∑ z ∈ f.range, ENNReal.ofReal (‖z‖ ^ 2) *
          (μS.diagonalMeasure x) (f ⁻¹' {z})) =
        ENNReal.ofReal (∑ z ∈ f.range,
          ‖z‖ ^ 2 * (⟪x, μS (f ⁻¹' {z}) x⟫_ℂ).re) := by
    simp_rw [μS.diagonalMeasure_apply x _ (f.measurableSet_fiber _)]
    simp_rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    intro z hz
    exact mul_nonneg (sq_nonneg _) (μS.re_inner_nonneg _ x)
  rw [hRHS]
  have hReSum : ∀ (s : Finset ℂ) (g : ℂ → ℂ),
      (∑ z ∈ s, g z).re = ∑ z ∈ s, (g z).re := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp
    | @insert z s hz ih =>
      simp only [Finset.sum_insert hz, Complex.add_re, ih]
  rw [hReSum]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  rw [Finset.sum_eq_single z]
  · rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
    rw [μS.inner_eq_inner_projection]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    norm_num [pow_two, Complex.mul_re, Complex.mul_im, RCLike.conj_re, RCLike.conj_im,
      RCLike.ofReal_re, RCLike.ofReal_im]
    have hzNorm : ‖z‖ * ‖z‖ = z.re * z.re + z.im * z.im := by
      rw [← pow_two, Complex.sq_norm, Complex.normSq_apply]
    rw [hzNorm]
    ring
  · intro w hw hwz
    have hdisj : Disjoint (f ⁻¹' ({z} : Set ℂ)) (f ⁻¹' ({w} : Set ℂ)) := by
      refine Set.disjoint_left.2 ?_
      intro a ha hb
      have haz : f a = z := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using ha
      have haw : f a = w := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hb
      exact hwz (haw.symm.trans haz)
    rw [inner_eq_zero_of_disjoint μS hdisj.symm (f.measurableSet_fiber _)
      (f.measurableSet_fiber _) x]
    simp
  · intro hznot
    exact (hznot hz).elim

lemma simpleIntegral_norm_sq_eq_lintegral (f : SimpleFunc α ℂ) (x : H) :
    ENNReal.ofReal (‖simpleIntegral μS f x‖ ^ 2) =
      ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μS.diagonalMeasure x := by
  rw [μS.simpleIntegral_norm_sq]
  have hfun : (fun z : α => ENNReal.ofReal (‖f z‖ ^ 2)) =
      (fun z : α => (f.map (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2))) z) := by
    funext z
    rfl
  rw [hfun]
  rw [(f.map (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ 2))).lintegral_eq_lintegral]
  rw [SimpleFunc.map_lintegral]

lemma simpleIntegral_norm_sq_le (f : SimpleFunc α ℂ) (x : H) {C : ℝ}
    (hC : ∀ z ∈ f.range, ‖z‖ ^ 2 ≤ C ^ 2) :
    ENNReal.ofReal (‖simpleIntegral μS f x‖ ^ 2) ≤
      ENNReal.ofReal (C ^ 2 * ‖x‖ ^ 2) := by
  rw [μS.simpleIntegral_norm_sq]
  calc
    (∑ z ∈ f.range, ENNReal.ofReal (‖z‖ ^ 2) *
        (μS.diagonalMeasure x) (f ⁻¹' {z})) ≤
        ∑ z ∈ f.range, ENNReal.ofReal (C ^ 2) *
          (μS.diagonalMeasure x) (f ⁻¹' {z}) := by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hC z hz)) _
    _ = ENNReal.ofReal (C ^ 2) *
          ∑ z ∈ f.range, (μS.diagonalMeasure x) (f ⁻¹' {z}) := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal (C ^ 2) * (μS.diagonalMeasure x) Set.univ := by
      rw [← f.sum_range_measure_preimage_singleton]
    _ = ENNReal.ofReal (C ^ 2 * ‖x‖ ^ 2) := by
      rw [μS.diagonalMeasure_univ, ← ENNReal.ofReal_mul (sq_nonneg C)]

lemma simpleIntegral_norm_le (f : SimpleFunc α ℂ) (x : H) {C : ℝ}
    (hC : 0 ≤ C) (hCf : ∀ z ∈ f.range, ‖z‖ ≤ C) :
    ‖simpleIntegral μS f x‖ ≤ C * ‖x‖ := by
  have hsq : ∀ z ∈ f.range, ‖z‖ ^ 2 ≤ C ^ 2 := by
    intro z hz
    exact (sq_le_sq₀ (norm_nonneg z) hC).mpr (hCf z hz)
  have hENN := μS.simpleIntegral_norm_sq_le f x hsq
  have hreal : ‖simpleIntegral μS f x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg C) (sq_nonneg ‖x‖))).mp hENN
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  calc
    ‖simpleIntegral μS f x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := hreal
    _ = (C * ‖x‖) ^ 2 := by ring

lemma simpleIntegral_const [Nonempty α] (c : ℂ) :
    simpleIntegral μS (SimpleFunc.const α c) = c • (1 : H →WOT[ℂ] H) := by
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  rw [simpleIntegral_inner]
  have hpre : (Function.const α c) ⁻¹' ({c} : Set ℂ) = Set.univ :=
    Set.preimage_const_of_mem (by simp)
  rw [SimpleFunc.range_const, Finset.sum_singleton, SimpleFunc.coe_const, hpre,
    scalarMeasure_apply, μS.univ]
  simp [ContinuousLinearMapWOT.one_apply, ContinuousLinearMapWOT.smul_apply,
    inner_smul_right]

/-! ## Completion of the bounded integral

The WOT type is a topological copy of the bounded-operator space; its underlying normed operator
is still available through `toCLM`. The finite estimate above therefore gives a norm completion
for any explicitly supplied uniformly convergent simple approximation. Keeping the approximation
sequence as an argument makes the analytic hypotheses visible at this low level.
-/

/-- The real-linear map `z ↦ z • μS(S)`, as a bounded operator, for each `z : ℂ`. -/
def spectralCLM (S : Set α) : ℂ →L[ℝ] (H →L[ℂ] H) :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (ContinuousLinearMapWOT.toCLM (μS S))).restrictScalars ℝ

lemma spectralCLM_apply (S : Set α) (z : ℂ) :
    spectralCLM μS S z = z • ContinuousLinearMapWOT.toCLM (μS S) := by
  rfl

private lemma spectralCLM_finMeasAdditive (μ : Measure α) :
    FinMeasAdditive μ (spectralCLM μS) := by
  intro S U hS hU hμS hμU hdisj
  ext z x
  change z • (μS (S ∪ U) x) = z • (μS S x) + z • (μS U x)
  rw [μS.of_union hdisj hS hU]
  simp [smul_add]

private lemma simpleFunc_integrable_dirac (f : SimpleFunc α ℂ) [Nonempty α] :
    Integrable f (Measure.dirac (Classical.choice (inferInstance : Nonempty α))) := by
  obtain ⟨C, hC⟩ := (f.map norm).exists_forall_le
  apply Integrable.of_bound f.measurable.aestronglyMeasurable C
  filter_upwards [] with x
  exact hC x

@[nolint unusedArguments]
lemma simpleIntegral_eq_setToSimpleFunc (f : SimpleFunc α ℂ) (μ : Measure α) :
    ContinuousLinearMapWOT.toCLM (simpleIntegral μS f) = f.setToSimpleFunc (spectralCLM μS) := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [SimpleFunc.setToSimpleFunc, spectralCLM_apply]
  have hsum : ∀ (s : Finset ℂ),
      (∑ z ∈ s, z • μS (f ⁻¹' {z})) x =
        ∑ z ∈ s, z • (μS (f ⁻¹' {z}) x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert z s hz ih =>
      simp only [Finset.sum_insert hz]
      rw [ContinuousLinearMapWOT.add_apply, ih]
      simp [ContinuousLinearMapWOT.smul_apply]
  change (∑ z ∈ f.range, z • μS (f ⁻¹' {z})) x =
    (∑ z ∈ f.range, z • ContinuousLinearMapWOT.toCLM (μS (f ⁻¹' {z}))) x
  rw [hsum]
  simp

/-! The characteristic-function case is the bridge from bounded integration back to the PVM. -/

lemma simpleIntegral_piecewise_indicator {S : Set α} (hS : MeasurableSet S) :
    simpleIntegral μS
        (SimpleFunc.piecewise S hS (SimpleFunc.const α (1 : ℂ))
          (SimpleFunc.const α (0 : ℂ))) = μS S := by
  apply ContinuousLinearMapWOT.toCLM_injective
  rw [simpleIntegral_eq_setToSimpleFunc μS _ (0 : Measure α)]
  have hempty : spectralCLM μS ∅ = 0 := by
    ext z
    simp [spectralCLM, μS.empty]
  rw [SimpleFunc.setToSimpleFunc_indicator (spectralCLM μS) hempty]
  simp [spectralCLM_apply]

lemma simpleIntegral_add [Nonempty α] (f g : SimpleFunc α ℂ) :
    simpleIntegral μS (f + g) = simpleIntegral μS f + simpleIntegral μS g := by
  apply ContinuousLinearMapWOT.toCLM_injective
  let μ : Measure α := Measure.dirac (Classical.choice (inferInstance : Nonempty α))
  rw [ContinuousLinearMapWOT.toCLM_add]
  rw [simpleIntegral_eq_setToSimpleFunc μS (f + g) μ,
    simpleIntegral_eq_setToSimpleFunc μS f μ,
    simpleIntegral_eq_setToSimpleFunc μS g μ]
  exact SimpleFunc.setToSimpleFunc_add (spectralCLM μS) (spectralCLM_finMeasAdditive μS μ)
    (simpleFunc_integrable_dirac f) (simpleFunc_integrable_dirac g)

lemma simpleIntegral_neg [Nonempty α] (f : SimpleFunc α ℂ) :
    simpleIntegral μS (-f) = -simpleIntegral μS f := by
  apply ContinuousLinearMapWOT.toCLM_injective
  let μ : Measure α := Measure.dirac (Classical.choice (inferInstance : Nonempty α))
  rw [ContinuousLinearMapWOT.toCLM_neg]
  rw [simpleIntegral_eq_setToSimpleFunc μS (-f) μ,
    simpleIntegral_eq_setToSimpleFunc μS f μ]
  exact SimpleFunc.setToSimpleFunc_neg (spectralCLM μS) (spectralCLM_finMeasAdditive μS μ)
    (simpleFunc_integrable_dirac f)

lemma simpleIntegral_sub [Nonempty α] (f g : SimpleFunc α ℂ) :
    simpleIntegral μS (f - g) = simpleIntegral μS f - simpleIntegral μS g := by
  rw [sub_eq_add_neg, simpleIntegral_add, simpleIntegral_neg, sub_eq_add_neg]

lemma simpleIntegral_mul [Nonempty α] (f g : SimpleFunc α ℂ) :
    simpleIntegral μS (f * g) = simpleIntegral μS f * simpleIntegral μS g := by
  apply ContinuousLinearMapWOT.toCLM_injective
  let μ : Measure α := Measure.dirac (Classical.choice (inferInstance : Nonempty α))
  let p : SimpleFunc α (ℂ × ℂ) := f.pair g
  have hf : Integrable f μ := simpleFunc_integrable_dirac f
  have hg : Integrable g μ := simpleFunc_integrable_dirac g
  have hp : Integrable p μ := SimpleFunc.integrable_pair hf hg
  have hadd := spectralCLM_finMeasAdditive μS μ
  have hfst : ContinuousLinearMapWOT.toCLM (simpleIntegral μS f) =
      ∑ q ∈ p.range, q.1 • ContinuousLinearMapWOT.toCLM (μS (p ⁻¹' {q})) := by
    rw [simpleIntegral_eq_setToSimpleFunc μS f μ, ← SimpleFunc.map_fst_pair f g]
    rw [SimpleFunc.map_setToSimpleFunc (spectralCLM μS) hadd hp Prod.fst_zero]
    simp only [spectralCLM_apply]
  have hsnd : ContinuousLinearMapWOT.toCLM (simpleIntegral μS g) =
      ∑ q ∈ p.range, q.2 • ContinuousLinearMapWOT.toCLM (μS (p ⁻¹' {q})) := by
    rw [simpleIntegral_eq_setToSimpleFunc μS g μ, ← SimpleFunc.map_snd_pair f g]
    rw [SimpleFunc.map_setToSimpleFunc (spectralCLM μS) hadd hp Prod.snd_zero]
    simp only [spectralCLM_apply]
  have hmul : ContinuousLinearMapWOT.toCLM (simpleIntegral μS (f * g)) =
      ∑ q ∈ p.range, (q.1 * q.2) • ContinuousLinearMapWOT.toCLM (μS (p ⁻¹' {q})) := by
    rw [simpleIntegral_eq_setToSimpleFunc μS (f * g) μ, SimpleFunc.mul_eq_map₂]
    rw [SimpleFunc.map_setToSimpleFunc (spectralCLM μS) hadd hp (by simp)]
    simp only [spectralCLM_apply]
  rw [ContinuousLinearMapWOT.toCLM_mul, hfst, hsnd, hmul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.sum_eq_single q]
  · rw [smul_mul_smul_comm, ← ContinuousLinearMapWOT.toCLM_mul, μS.comp_self]
  · intro r hr hneq
    rw [smul_mul_smul_comm, ← ContinuousLinearMapWOT.toCLM_mul]
    have hdisj : Disjoint (p ⁻¹' {q}) (p ⁻¹' {r}) := by
      refine Set.disjoint_left.2 ?_
      intro a haq har
      have haq' : p a = q := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using haq
      have har' : p a = r := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using har
      exact hneq (har'.symm.trans haq')
    rw [μS.comp_of_disjoint hdisj (p.measurableSet_fiber _)
      (p.measurableSet_fiber _), ContinuousLinearMapWOT.toCLM_zero, smul_zero]
  · intro hq'
    exact (hq' hq).elim

@[nolint unusedArguments]
lemma simpleIntegral_star [Nonempty α] (f : SimpleFunc α ℂ) :
    simpleIntegral μS (star f) = star (simpleIntegral μS f) := by
  classical
  simp only [simpleIntegral, star_sum]
  refine Finset.sum_bij (fun z hz => star z) ?_ ?_ ?_ ?_
  · intro z hz
    rcases SimpleFunc.mem_range.1 hz with ⟨x, hx⟩
    apply SimpleFunc.mem_range.2
    refine ⟨x, ?_⟩
    change f x = star z
    have hx' := congrArg star hx
    change star (star (f x)) = star z at hx'
    simpa using hx'
  · intro z₁ hz₁ z₂ hz₂ h
    exact star_injective h
  · intro z hz
    rcases SimpleFunc.mem_range.1 hz with ⟨x, hx⟩
    refine ⟨star z, ?_, ?_⟩
    · apply SimpleFunc.mem_range.2
      refine ⟨x, ?_⟩
      change star (f x) = star z
      exact congrArg star hx
    · simp
  · intro z hz
    have hfiber : (⇑(star f) : α → ℂ) ⁻¹' {z} =
        (⇑f : α → ℂ) ⁻¹' {star z} := by
      ext x
      change star (f x) = z ↔ f x = star z
      constructor
      · intro h
        simpa using congrArg star h
      · intro h
        exact congrArg star h |>.trans (star_star z)
    rw [hfiber, star_smul, star_star]
    simp only [(μS.isStarProjection _).isSelfAdjoint.star_eq]

lemma simpleIntegral_toCLM_norm_le (f : SimpleFunc α ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hCf : ∀ z ∈ f.range, ‖z‖ ≤ C) :
    ‖ContinuousLinearMapWOT.toCLM (simpleIntegral μS f)‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  exact μS.simpleIntegral_norm_le f x hC hCf

lemma simpleIntegral_toCLM_diff_norm_le [Nonempty α] (f g : SimpleFunc α ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hfg : ∀ x, ‖f x - g x‖ ≤ C) :
    ‖ContinuousLinearMapWOT.toCLM (simpleIntegral μS f) -
        ContinuousLinearMapWOT.toCLM (simpleIntegral μS g)‖ ≤ C := by
  rw [← ContinuousLinearMapWOT.toCLM_sub, ← μS.simpleIntegral_sub]
  apply μS.simpleIntegral_toCLM_norm_le (f - g) hC
  intro z hz
  rcases SimpleFunc.mem_range.1 hz with ⟨x, rfl⟩
  simpa only [SimpleFunc.sub_apply] using hfg x

lemma simpleIntegral_toCLM_cauchySeq [Nonempty α] {f : α → ℂ} {s : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) :
    CauchySeq (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  rcases hs (ε / 4) (by linarith) with ⟨N, hN⟩
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmn : ∀ x, ‖s m x - s n x‖ ≤ ε / 2 := by
    intro x
    apply le_of_lt
    calc
      ‖s m x - s n x‖ ≤ ‖s m x - f x‖ + ‖s n x - f x‖ := by
        calc
          ‖s m x - s n x‖ = ‖(s m x - f x) - (s n x - f x)‖ := by ring_nf
          _ ≤ ‖s m x - f x‖ + ‖s n x - f x‖ := norm_sub_le _ _
      _ < ε / 4 + ε / 4 := add_lt_add (hN m hm x) (hN n hn x)
      _ = ε / 2 := by ring
  have hbound := μS.simpleIntegral_toCLM_diff_norm_le (s m) (s n) (by linarith) hmn
  simpa only [dist_eq_norm] using lt_of_le_of_lt hbound (by linarith)

/-- The bounded operator integral obtained from an explicit uniformly convergent simple
approximation. The limit is taken in the normed space of bounded operators and then viewed in the
WOT copy. -/
@[nolint unusedArguments]
noncomputable def boundedIntegralOfUniformApprox [Nonempty α]
    (f : α → ℂ) (s : ℕ → SimpleFunc α ℂ)
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) :
    H →WOT[ℂ] H :=
  ContinuousLinearMapWOT.ofCLM
    (Filter.atTop.limUnder
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))))

lemma boundedIntegralOfUniformApprox_eq_limUnder
    [Nonempty α]
    (f : α → ℂ) (s : ℕ → SimpleFunc α ℂ)
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) :
    ContinuousLinearMapWOT.toCLM (boundedIntegralOfUniformApprox μS f s hs) =
      Filter.atTop.limUnder
        (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) := by
  rfl

lemma boundedIntegralOfUniformApprox_norm_le
    [Nonempty α]
    (f : α → ℂ) (s : ℕ → SimpleFunc α ℂ)
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    {C : ℝ} (hC : ∀ n x, ‖s n x‖ ≤ C) :
    ‖ContinuousLinearMapWOT.toCLM (boundedIntegralOfUniformApprox μS f s hs)‖ ≤ C := by
  have hC0 : 0 ≤ C := by
    let a₀ : α := Classical.choice (inferInstance : Nonempty α)
    exact (norm_nonneg (s 0 a₀)).trans (hC 0 a₀)
  have hseq : ∀ n,
      ‖ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))‖ ≤ C := by
    intro n
    apply simpleIntegral_toCLM_norm_le μS (s n) hC0
    intro z hz
    rcases SimpleFunc.mem_range.1 hz with ⟨x, rfl⟩
    exact hC n x
  have hlim : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  apply (isClosed_le continuous_norm continuous_const).mem_of_tendsto hlim
  exact Filter.Eventually.of_forall hseq

lemma boundedIntegralOfUniformApprox_eq_of_uniform_approx
    [Nonempty α]
    {f : α → ℂ} {s t : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (ht : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖t n x - f x‖ < ε)
    (hst : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - t n x‖ < ε) :
    boundedIntegralOfUniformApprox μS f s hs =
      boundedIntegralOfUniformApprox μS f t ht := by
  apply ContinuousLinearMapWOT.toCLM_injective
  let S : ℕ → H →L[ℂ] H := fun n =>
    ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))
  let U : ℕ → H →L[ℂ] H := fun n =>
    ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))
  have hdist : Filter.Tendsto (fun n => dist (S n) (U n)) Filter.atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases hst (ε / 2) (by linarith) with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have hnorm : ‖S n - U n‖ < ε := by
      have h := simpleIntegral_toCLM_diff_norm_le μS (s n) (t n)
        (by positivity : (0 : ℝ) ≤ ε / 2) (fun x => le_of_lt (hN n hn x))
      have h' : ‖S n - U n‖ ≤ ε / 2 := by
        simpa only [S, U, ← ContinuousLinearMapWOT.toCLM_sub] using h
      exact h'.trans_lt (by linarith)
    have hdist' : dist (S n) (U n) < ε := by
      simpa only [dist_eq_norm] using hnorm
    change dist (dist (S n) (U n)) 0 < ε
    simpa only [dist_zero_right, Real.norm_of_nonneg (dist_nonneg)] using hdist'
  have hlimS : Filter.Tendsto (fun n => S n) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    change Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop _
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hlimU : Filter.Tendsto (fun n => U n) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f t ht))) := by
    change Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop _
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS ht).tendsto_limUnder
  have hlimU' : Filter.Tendsto (fun n => U n) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) :=
    hlimS.congr_dist hdist
  have heq : ContinuousLinearMapWOT.toCLM
      (boundedIntegralOfUniformApprox μS f s hs) =
      ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f t ht) :=
    tendsto_nhds_unique hlimU' hlimU
  exact heq

lemma boundedIntegralOfUniformApprox_eq_of_same_target
    [Nonempty α]
    {f : α → ℂ} {s t : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (ht : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖t n x - f x‖ < ε) :
    boundedIntegralOfUniformApprox μS f s hs =
      boundedIntegralOfUniformApprox μS f t ht := by
  apply boundedIntegralOfUniformApprox_eq_of_uniform_approx μS hs ht
  intro ε hε
  rcases hs (ε / 2) (by linarith) with ⟨Ns, hNs⟩
  rcases ht (ε / 2) (by linarith) with ⟨Nt, hNt⟩
  refine ⟨max Ns Nt, fun n hn x => ?_⟩
  calc
    ‖s n x - t n x‖ ≤ ‖s n x - f x‖ + ‖t n x - f x‖ := by
      calc
        ‖s n x - t n x‖ = ‖(s n x - f x) - (t n x - f x)‖ := by ring_nf
        _ ≤ ‖s n x - f x‖ + ‖t n x - f x‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add
      (hNs n (le_trans (le_max_left _ _) hn) x)
      (hNt n (le_trans (le_max_right _ _) hn) x)
    _ = ε := by ring

/-! ### Uniform simple approximation and the canonical integral -/

lemma exists_uniform_simple_approx [Nonempty α] {f : α → ℂ} (hf : Measurable f)
    (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ s : ℕ → SimpleFunc α ℂ,
      (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) ∧
      ∃ C, ∀ n x, ‖s n x‖ ≤ C := by
  rcases hbdd with ⟨C, hC⟩
  let a₀ : α := Classical.choice (inferInstance : Nonempty α)
  have hC0 : 0 ≤ C := (norm_nonneg (f a₀)).trans (hC a₀)
  let K : Set ℂ := Metric.closedBall 0 C
  have hKcompact : IsCompact K := isCompact_closedBall 0 C
  letI : TopologicalSpace.SeparableSpace K := hKcompact.isSeparable.separableSpace
  have hK0 : (0 : ℂ) ∈ K := by simp [K, hC0]
  letI : Nonempty K := ⟨⟨0, hK0⟩⟩
  let e : ℕ → ℂ := fun k => Nat.casesOn k 0 ((↑) ∘ TopologicalSpace.denseSeq K)
  let s : ℕ → SimpleFunc α ℂ := fun n => SimpleFunc.approxOn f hf K 0 hK0 n
  refine ⟨s, ?_, ⟨C, ?_⟩⟩
  · intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have hcover : K ⊆ ⋃ k : ℕ, Metric.ball (e k) (ε / 2) := by
      intro y hy
      have hycl : (⟨y, hy⟩ : K) ∈ closure (Set.range (TopologicalSpace.denseSeq K)) := by
        rw [(denseRange_iff_closure_range.mp (TopologicalSpace.denseRange_denseSeq K))]
        exact mem_univ _
      have hy_mem : (⟨y, hy⟩ : K) ∈ Metric.ball (⟨y, hy⟩ : K) (ε / 2) :=
        Metric.mem_ball_self hε2
      rcases (mem_closure_iff.1 hycl) _ Metric.isOpen_ball hy_mem with ⟨z, hz, hzr⟩
      rcases hzr with ⟨k, rfl⟩
      refine mem_iUnion.2 ⟨k + 1, ?_⟩
      have hz' := Metric.mem_ball.mp hz
      rw [Subtype.dist_eq] at hz'
      simpa [e, Function.comp_def, dist_comm] using hz'
    rcases hKcompact.elim_finite_subcover (fun k : ℕ => Metric.ball (e k) (ε / 2))
        (fun _ => Metric.isOpen_ball) hcover with ⟨t, ht⟩
    have ht_ne : t.Nonempty := by
      by_contra ht'
      have ht_empty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht'
      subst ht_empty
      simpa using (ht (show (0 : ℂ) ∈ K from hK0))
    let N : ℕ := t.sup id
    refine ⟨N, ?_⟩
    intro n hn x
    have hfxK : f x ∈ K := by
      rw [Metric.mem_closedBall]
      simpa [dist_eq_norm] using hC x
    rcases Set.mem_iUnion₂.1 (ht hfxK) with ⟨k, hkt, hkx⟩
    have hkn : k ≤ n := (Finset.le_sup hkt).trans hn
    have hnearest : edist (SimpleFunc.nearestPt e n (f x)) (f x) ≤ edist (e k) (f x) :=
      SimpleFunc.edist_nearestPt_le e (f x) hkn
    have hkx' : dist (e k) (f x) < ε / 2 := by
      simpa [dist_comm] using Metric.mem_ball.mp hkx
    have hdist : dist (s n x) (f x) < ε := by
      have hnearest' : edist (s n x) (f x) ≤ edist (e k) (f x) := by
        simpa [s, SimpleFunc.approxOn, e] using hnearest
      have hkxed : edist (e k) (f x) < ENNReal.ofReal ε := by
        rw [edist_dist]
        exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith [hkx'])
      have hlt : edist (s n x) (f x) < ENNReal.ofReal ε := hnearest'.trans_lt hkxed
      rw [edist_dist] at hlt
      exact ENNReal.ofReal_lt_ofReal_iff hε |>.mp hlt
    simpa only [dist_eq_norm] using hdist
  · intro n x
    have hx := SimpleFunc.approxOn_mem hf hK0 n x
    rw [Metric.mem_closedBall] at hx
    simpa [dist_eq_norm] using hx

/-- The weak-operator-topology integral of a bounded measurable `f : α → ℂ` against `μS`,
defined as the limit of simple-function integrals under uniform approximation. -/
noncomputable def boundedIntegral [Nonempty α] (f : α → ℂ) (hf : Measurable f)
    (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) : H →WOT[ℂ] H := by
  let s : ℕ → SimpleFunc α ℂ :=
    Classical.choose (exists_uniform_simple_approx hf hbdd)
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hbdd)).1
  exact boundedIntegralOfUniformApprox μS f s hs

lemma boundedIntegral_eq_of_uniform_approx [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C)
    {s : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) :
    boundedIntegral μS f hf hbdd = boundedIntegralOfUniformApprox μS f s hs := by
  let s₀ : ℕ → SimpleFunc α ℂ :=
    Classical.choose (exists_uniform_simple_approx hf hbdd)
  have hs₀ : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s₀ n x - f x‖ < ε :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hbdd)).1
  unfold boundedIntegral
  dsimp [s₀]
  exact boundedIntegralOfUniformApprox_eq_of_same_target μS hs₀ hs

lemma boundedIntegral_eq_of_same_target [Nonempty α]
    {f : α → ℂ} {s t : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (ht : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖t n x - f x‖ < ε)
    (hf : Measurable f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    boundedIntegralOfUniformApprox μS f s hs = boundedIntegral μS f hf hbdd := by
  symm
  rw [boundedIntegral_eq_of_uniform_approx μS hf hbdd ht]
  exact boundedIntegralOfUniformApprox_eq_of_same_target μS ht hs

lemma boundedIntegral_norm_le [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ C : ℝ, ‖ContinuousLinearMapWOT.toCLM (boundedIntegral μS f hf hbdd)‖ ≤ C := by
  rcases Classical.choose_spec (exists_uniform_simple_approx hf hbdd) with ⟨hs, ⟨C, hC⟩⟩
  refine ⟨C, ?_⟩
  rw [boundedIntegral_eq_of_uniform_approx μS hf hbdd hs]
  exact boundedIntegralOfUniformApprox_norm_le μS _ _ hs hC

lemma boundedIntegral_norm_sq [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) (x : H) :
    ENNReal.ofReal (‖boundedIntegral μS f hf hbdd x‖ ^ 2) =
      ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μS.diagonalMeasure x := by
  let s : ℕ → SimpleFunc α ℂ :=
    Classical.choose (exists_uniform_simple_approx hf hbdd)
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ z, ‖s n z - f z‖ < ε :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hbdd)).1
  have hsBound : ∃ C : ℝ, ∀ n z, ‖s n z‖ ≤ C :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hbdd)).2
  have hclm : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM (boundedIntegral μS f hf hbdd))) := by
    rw [boundedIntegral_eq_of_uniform_approx μS hf hbdd hs]
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hvec : Filter.Tendsto (fun n => simpleIntegral μS (s n) x) Filter.atTop
      (𝓝 (boundedIntegral μS f hf hbdd x)) := by
    have hev : Continuous (fun A : H →L[ℂ] H => A x) := by fun_prop
    exact hev.continuousAt.tendsto.comp hclm
  have hnorm : Filter.Tendsto
      (fun n => ENNReal.ofReal (‖simpleIntegral μS (s n) x‖ ^ 2)) Filter.atTop
      (𝓝 (ENNReal.ofReal (‖boundedIntegral μS f hf hbdd x‖ ^ 2))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((continuous_norm.pow 2).continuousAt.tendsto.comp hvec)
  let μ : Measure α := μS.diagonalMeasure x
  let F : ℕ → α → ENNReal := fun n z => ENNReal.ofReal (‖s n z‖ ^ 2)
  let F₀ : α → ENNReal := fun z => ENNReal.ofReal (‖f z‖ ^ 2)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    dsimp [F]
    fun_prop
  have hC0 : ∃ C : ℝ, 0 ≤ C ∧ ∀ n z, ‖s n z‖ ≤ C := by
    rcases hsBound with ⟨C, hC⟩
    have hC0 : 0 ≤ C := by
      let a₀ : α := Classical.choice (inferInstance : Nonempty α)
      exact (norm_nonneg (s 0 a₀)).trans (hC 0 a₀)
    exact ⟨C, hC0, hC⟩
  rcases hC0 with ⟨C, hC0, hC⟩
  have hbound : ∀ n, F n ≤ᵐ[μ] (fun _ : α => ENNReal.ofReal (C ^ 2)) := by
    intro n
    filter_upwards [] with z
    dsimp [F]
    apply ENNReal.ofReal_le_ofReal
    exact (sq_le_sq₀ (norm_nonneg (s n z)) hC0).mpr (hC n z)
  have hfin : (∫⁻ z, ENNReal.ofReal (C ^ 2) ∂μ) ≠ (⊤ : ENNReal) := by
    rw [lintegral_const, μS.diagonalMeasure_univ]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.ofReal_ne_top
  have hlim : ∀ᵐ z ∂μ, Filter.Tendsto (fun n => F n z) Filter.atTop (𝓝 (F₀ z)) := by
    filter_upwards [] with z
    have hz : Filter.Tendsto (fun n => s n z) Filter.atTop (𝓝 (f z)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      rcases hs ε hε with ⟨N, hN⟩
      exact ⟨N, fun n hn => by simpa only [dist_eq_norm] using hN n hn z⟩
    have hnorm' : Filter.Tendsto (fun n => ‖s n z‖) Filter.atTop (𝓝 ‖f z‖) :=
      continuous_norm.continuousAt.tendsto.comp hz
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((continuous_id.pow 2).continuousAt.tendsto.comp hnorm')
  have hlintegral : Filter.Tendsto (fun n => ∫⁻ z, F n z ∂μ) Filter.atTop
      (𝓝 (∫⁻ z, F₀ z ∂μ)) :=
    MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (fun _ : α => ENNReal.ofReal (C ^ 2)) hFmeas hbound hfin hlim
  have hlintegral' : Filter.Tendsto
      (fun n => ENNReal.ofReal (‖simpleIntegral μS (s n) x‖ ^ 2)) Filter.atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μS.diagonalMeasure x)) := by
    simpa only [F, F₀, μ, μS.simpleIntegral_norm_sq_eq_lintegral] using hlintegral
  exact tendsto_nhds_unique hnorm hlintegral'

lemma boundedIntegral_norm_le_of_bound [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) {C : ℝ} (hC : 0 ≤ C)
    (hCf : ∀ x, ‖f x‖ ≤ C) :
    ‖ContinuousLinearMapWOT.toCLM
      (boundedIntegral μS f hf (⟨C, hCf⟩ : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C))‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_iff hC |>.2
  intro x
  have hsq : ∀ z, ‖f z‖ ^ 2 ≤ C ^ 2 := by
    intro z
    exact (sq_le_sq₀ (norm_nonneg (f z)) hC).mpr (hCf z)
  have hpoint : ∀ z, ENNReal.ofReal (‖f z‖ ^ 2) ≤ ENNReal.ofReal (C ^ 2) := by
    intro z
    exact ENNReal.ofReal_le_ofReal (hsq z)
  have hlin : (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2)
      ∂μS.diagonalMeasure x) ≤ ENNReal.ofReal (C ^ 2 * ‖x‖ ^ 2) := by
    calc
      (∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μS.diagonalMeasure x) ≤
          ∫⁻ _ : α, ENNReal.ofReal (C ^ 2) ∂μS.diagonalMeasure x :=
        lintegral_mono_ae (Filter.Eventually.of_forall hpoint)
      _ = ENNReal.ofReal (C ^ 2 * ‖x‖ ^ 2) := by
        rw [lintegral_const, μS.diagonalMeasure_univ,
          ← ENNReal.ofReal_mul (sq_nonneg C)]
  have hnormsq : ENNReal.ofReal
      (‖boundedIntegral μS f hf (⟨C, hCf⟩ : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) x‖ ^ 2) ≤
      ENNReal.ofReal (C ^ 2 * ‖x‖ ^ 2) := by
    rw [boundedIntegral_norm_sq]
    exact hlin
  have hreal : ‖boundedIntegral μS f hf
      (⟨C, hCf⟩ : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) x‖ ^ 2 ≤
      C ^ 2 * ‖x‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg C) (sq_nonneg ‖x‖))).mp hnormsq
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  calc
    ‖boundedIntegral μS f hf
        (⟨C, hCf⟩ : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) x‖ ^ 2 ≤
        C ^ 2 * ‖x‖ ^ 2 := hreal
    _ = (C * ‖x‖) ^ 2 := by ring

lemma boundedIntegral_norm_sq_eq_integral [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) (hbdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (x : H) :
    ‖boundedIntegral μS f hf hbdd x‖ ^ 2 =
      ∫ z, ‖f z‖ ^ 2 ∂μS.diagonalMeasure x := by
  rcases hbdd with ⟨C, hCf⟩
  let a₀ : α := Classical.choice (inferInstance : Nonempty α)
  have hC : 0 ≤ C := (norm_nonneg (f a₀)).trans (hCf a₀)
  have hfi : Integrable (fun z : α => ‖f z‖ ^ 2) (μS.diagonalMeasure x) := by
    apply Integrable.of_bound (hf.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
    filter_upwards [] with z
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖f z‖))] using
      (sq_le_sq₀ (norm_nonneg (f z)) hC).mpr (hCf z)
  have hpos : 0 ≤ᵐ[μS.diagonalMeasure x] (fun z : α => ‖f z‖ ^ 2) :=
    Filter.Eventually.of_forall (fun z => sq_nonneg _)
  have hconvert : ENNReal.ofReal (∫ z, ‖f z‖ ^ 2 ∂μS.diagonalMeasure x) =
      ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) ∂μS.diagonalMeasure x :=
    ofReal_integral_eq_lintegral_ofReal hfi hpos
  have hmain := boundedIntegral_norm_sq μS hf (⟨C, hCf⟩ : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) x
  rw [← hconvert] at hmain
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _)
    (integral_nonneg (fun z => sq_nonneg (‖f z‖)))).mp hmain

private lemma boundedIntegralOfUniformApprox_add [Nonempty α]
    {f g : α → ℂ} {s t : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (ht : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖t n x - g x‖ < ε)
    (hsg : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(s n + t n) x - (f + g) x‖ < ε) :
    boundedIntegralOfUniformApprox μS (f + g) (fun n => s n + t n) hsg =
      boundedIntegralOfUniformApprox μS f s hs +
        boundedIntegralOfUniformApprox μS g t ht := by
  apply ContinuousLinearMapWOT.toCLM_injective
  have hfs : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hgt : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS g t ht))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS ht).tendsto_limUnder
  have hsum : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)) +
        ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs) +
        ContinuousLinearMapWOT.toCLM
          (boundedIntegralOfUniformApprox μS g t ht))) := hfs.add hgt
  have hsum' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS ((s + t) n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (f + g) (fun n => s n + t n) hsg))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hsg).tendsto_limUnder
  have hsum'' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)) +
        ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (f + g) (fun n => s n + t n) hsg))) := by
    simpa only [Pi.add_apply, simpleIntegral_add, ContinuousLinearMapWOT.toCLM_add] using hsum'
  exact tendsto_nhds_unique hsum'' hsum

private lemma boundedIntegralOfUniformApprox_neg [Nonempty α]
    {f : α → ℂ} {s : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (hneg : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(-s n) x - (-f x)‖ < ε) :
    boundedIntegralOfUniformApprox μS (fun x => -f x) (fun n => -s n) hneg =
      -boundedIntegralOfUniformApprox μS f s hs := by
  apply ContinuousLinearMapWOT.toCLM_injective
  have hfs : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hneg' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS ((-s) n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (fun x => -f x) (fun n => -s n) hneg))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hneg).tendsto_limUnder
  have hneg'' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS ((-s) n))) Filter.atTop
      (𝓝 (-ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    simpa only [Pi.neg_apply, simpleIntegral_neg, ContinuousLinearMapWOT.toCLM_neg] using hfs.neg
  exact tendsto_nhds_unique hneg' hneg''

lemma boundedIntegral_neg [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    boundedIntegral μS (fun x => -f x) (continuous_neg.measurable.comp hf)
        (by
          rcases hbf with ⟨C, hC⟩
          exact ⟨C, fun x => by simpa using hC x⟩) =
      -boundedIntegral μS f hf hbf := by
  classical
  rcases exists_uniform_simple_approx hf hbf with ⟨s, hs, hsB⟩
  have hneg : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(-s n) x - (-(f x))‖ < ε := by
    intro ε hε
    rcases hs ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn x => ?_⟩
    change ‖-s n x - -f x‖ < ε
    calc
      ‖-s n x - -f x‖ = ‖-(s n x - f x)‖ := by congr 1 <;> ring
      _ = ‖s n x - f x‖ := norm_neg _
      _ < ε := hN n hn x
  calc
    boundedIntegral μS (fun x => -f x) (continuous_neg.measurable.comp hf) _ =
        boundedIntegralOfUniformApprox μS (fun x => -f x) (fun n => -s n) hneg :=
      boundedIntegral_eq_of_uniform_approx μS (continuous_neg.measurable.comp hf) _ hneg
    _ = -boundedIntegralOfUniformApprox μS f s hs :=
      boundedIntegralOfUniformApprox_neg μS hs hneg
    _ = -boundedIntegral μS f hf hbf := by
      rw [boundedIntegral_eq_of_uniform_approx μS hf hbf hs]

lemma boundedIntegral_add [Nonempty α]
    {f g : α → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    boundedIntegral μS (f + g) (hf.add hg)
        (by
          rcases hbf with ⟨Cf, hCf⟩
          rcases hbg with ⟨Cg, hCg⟩
          refine ⟨Cf + Cg, fun x => ?_⟩
          exact (norm_add_le _ _).trans (add_le_add (hCf x) (hCg x))) =
      boundedIntegral μS f hf hbf + boundedIntegral μS g hg hbg := by
  classical
  rcases exists_uniform_simple_approx hf hbf with ⟨s, hs, hsB⟩
  rcases exists_uniform_simple_approx hg hbg with ⟨t, ht, htB⟩
  have hsg : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(s n + t n) x - (f + g) x‖ < ε := by
    intro ε hε
    rcases hs (ε / 2) (by linarith) with ⟨Ns, hNs⟩
    rcases ht (ε / 2) (by linarith) with ⟨Nt, hNt⟩
    refine ⟨max Ns Nt, fun n hn x => ?_⟩
    simp only [Pi.add_apply, SimpleFunc.add_apply]
    calc
      ‖(s n x + t n x) - (f x + g x)‖ =
          ‖(s n x - f x) + (t n x - g x)‖ := by ring_nf
      _ ≤ ‖s n x - f x‖ + ‖t n x - g x‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add
        (hNs n (le_trans (le_max_left _ _) hn) x)
        (hNt n (le_trans (le_max_right _ _) hn) x)
      _ = ε := by ring
  rw [boundedIntegral_eq_of_uniform_approx μS (hf.add hg) _ hsg,
    boundedIntegral_eq_of_uniform_approx μS hf hbf hs,
    boundedIntegral_eq_of_uniform_approx μS hg hbg ht]
  exact boundedIntegralOfUniformApprox_add μS hs ht hsg

lemma boundedIntegral_const [Nonempty α] (c : ℂ) :
    boundedIntegral μS (fun _ : α => c) measurable_const
        (⟨‖c‖, fun _ => le_rfl⟩) = c • (1 : H →WOT[ℂ] H) := by
  let s : ℕ → SimpleFunc α ℂ := fun _ => SimpleFunc.const α c
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - (fun _ : α => c) x‖ < ε := by
    intro ε hε
    exact ⟨0, fun n hn x => by simp [s, hε]⟩
  rw [boundedIntegral_eq_of_uniform_approx μS measurable_const
    (⟨‖c‖, fun _ => le_rfl⟩) hs]
  apply ContinuousLinearMapWOT.toCLM_injective
  have hconst := boundedIntegralOfUniformApprox_eq_limUnder μS
    (fun _ : α => c) s hs
  rw [hconst]
  rw [show (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) =
      (fun _ => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s 0))) by
        funext n; rfl]
  have hlim : Filter.Tendsto
      (fun _ : ℕ => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s 0))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s 0)))) := tendsto_const_nhds
  rw [hlim.limUnder_eq]
  change ContinuousLinearMapWOT.toCLM (simpleIntegral μS (SimpleFunc.const α c)) =
    ContinuousLinearMapWOT.toCLM (c • (1 : H →WOT[ℂ] H))
  rw [simpleIntegral_const]

lemma boundedIntegral_congr [Nonempty α]
    {f g : α → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∀ x, f x = g x) :
    boundedIntegral μS f hf hbf = boundedIntegral μS g hg hbg := by
  rcases exists_uniform_simple_approx hf hbf with ⟨s, hs, hsB⟩
  have hs' : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - g x‖ < ε := by
    intro ε hε
    rcases hs ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn x => ?_⟩
    rw [← hfg x]
    exact hN n hn x
  exact (boundedIntegral_eq_of_uniform_approx μS hf hbf hs).trans
    (boundedIntegral_eq_of_uniform_approx μS hg hbg hs').symm

lemma boundedIntegral_indicator [Nonempty α] {S : Set α} (hS : MeasurableSet S) :
    boundedIntegral μS (S.indicator (fun _ : α => (1 : ℂ)))
        (measurable_const.indicator hS)
        (⟨1, fun x => by by_cases hx : x ∈ S <;> simp [hx]⟩) = μS S := by
  let s : ℕ → SimpleFunc α ℂ := fun _ =>
    SimpleFunc.piecewise S hS (SimpleFunc.const α (1 : ℂ))
      (SimpleFunc.const α (0 : ℂ))
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖s n x - S.indicator (fun _ : α => (1 : ℂ)) x‖ < ε := by
    intro ε hε
    refine ⟨0, fun n hn x => ?_⟩
    rw [show s n = SimpleFunc.piecewise S hS
      (SimpleFunc.const α (1 : ℂ)) (SimpleFunc.const α (0 : ℂ)) by rfl]
    rw [SimpleFunc.coe_piecewise hS]
    simp only [SimpleFunc.coe_const, Function.const_zero, Set.piecewise_eq_indicator]
    change ‖S.indicator (fun _ : α => (1 : ℂ)) x -
      S.indicator (fun _ : α => (1 : ℂ)) x‖ < ε
    simp only [sub_self, norm_zero]
    exact hε
  rw [boundedIntegral_eq_of_uniform_approx μS (measurable_const.indicator hS)
    (⟨1, fun x => by by_cases hx : x ∈ S <;> simp [hx]⟩) hs]
  apply ContinuousLinearMapWOT.toCLM_injective
  rw [boundedIntegralOfUniformApprox_eq_limUnder μS _ s hs]
  rw [show (fun n : ℕ => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) =
      (fun _ : ℕ => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s 0))) by
        funext n; rfl]
  rw [tendsto_const_nhds.limUnder_eq]
  change ContinuousLinearMapWOT.toCLM (simpleIntegral μS
      (SimpleFunc.piecewise S hS (SimpleFunc.const α (1 : ℂ))
        (SimpleFunc.const α (0 : ℂ)))) = ContinuousLinearMapWOT.toCLM (μS S)
  rw [simpleIntegral_piecewise_indicator]

/- A bounded spectral integral determines a weak spectral measure.  In particular, this gives a
usable uniqueness principle for any construction which agrees with the canonical integral on
bounded Borel multipliers. -/
theorem ext_of_boundedIntegral_eq [Nonempty α]
    {μS νS : WOTSpectralMeasure α H}
    (h : ∀ (f : α → ℂ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C),
      μS.boundedIntegral f hf hfb = νS.boundedIntegral f hf hfb) :
    μS = νS := by
  apply ext_of_scalarMeasure_eq
  intro x y
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  have h₁ := h (S.indicator (fun _ : α => (1 : ℂ)))
    (measurable_const.indicator hS) (by
      refine ⟨1, fun a => ?_⟩
      by_cases ha : a ∈ S <;> simp [Set.indicator, ha])
  have h₂ := congrArg (fun A : H →WOT[ℂ] H => ⟪y, A x⟫_ℂ) h₁
  simpa [boundedIntegral_indicator μS hS, boundedIntegral_indicator νS hS,
    scalarMeasure_apply] using h₂

lemma boundedIntegral_sub [Nonempty α]
    {f g : α → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    boundedIntegral μS (f - g) (hf.sub hg)
        (by
          rcases hbf with ⟨Cf, hCf⟩
          rcases hbg with ⟨Cg, hCg⟩
          refine ⟨Cf + Cg, fun x => ?_⟩
          exact (norm_sub_le _ _).trans (add_le_add (hCf x) (hCg x))) =
      boundedIntegral μS f hf hbf - boundedIntegral μS g hg hbg := by
  have hsubBound : ∃ C, ∀ x, ‖(f - g) x‖ ≤ C := by
    rcases hbf with ⟨Cf, hCf⟩
    rcases hbg with ⟨Cg, hCg⟩
    refine ⟨Cf + Cg, fun x => ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add (hCf x) (hCg x))
  have hg' : Measurable (fun x => -g x) := continuous_neg.measurable.comp hg
  have hbg' : ∃ C, ∀ x, ‖-g x‖ ≤ C := by
    rcases hbg with ⟨C, hC⟩
    exact ⟨C, fun x => by simpa using hC x⟩
  have hneg := boundedIntegral_neg μS hg hbg
  have hadd := boundedIntegral_add μS hf hg' hbf hbg'
  have haddBound : ∃ C, ∀ x, ‖(f + (fun x => -g x)) x‖ ≤ C := by
    rcases hbf with ⟨Cf, hCf⟩
    rcases hbg' with ⟨Cg, hCg⟩
    refine ⟨Cf + Cg, fun x => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hCf x) (hCg x))
  calc
    boundedIntegral μS (f - g) (hf.sub hg) hsubBound =
        boundedIntegral μS f hf hbf +
          boundedIntegral μS (fun x => -g x) hg' hbg' := by
      calc
        boundedIntegral μS (f - g) (hf.sub hg) hsubBound =
            boundedIntegral μS (f + (fun x => -g x))
              (hf.add hg') haddBound := by
          apply boundedIntegral_congr μS (hf.sub hg) (hf.add hg') hsubBound haddBound
          intro x
          simp [Pi.sub_apply, sub_eq_add_neg]
        _ = boundedIntegral μS f hf hbf +
            boundedIntegral μS (fun x => -g x)
              hg' hbg' := by exact hadd
    _ = boundedIntegral μS f hf hbf - boundedIntegral μS g hg hbg := by rw [hneg, sub_eq_add_neg]

private lemma boundedIntegralOfUniformApprox_mul [Nonempty α]
    {f g : α → ℂ} {s t : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (ht : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖t n x - g x‖ < ε)
    (hprod : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(s n * t n) x - (f * g) x‖ < ε) :
    boundedIntegralOfUniformApprox μS (f * g) (fun n => s n * t n) hprod =
      boundedIntegralOfUniformApprox μS f s hs *
        boundedIntegralOfUniformApprox μS g t ht := by
  apply ContinuousLinearMapWOT.toCLM_injective
  have hfs : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hgt : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS g t ht))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS ht).tendsto_limUnder
  have hmul : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)) *
        ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs) *
        ContinuousLinearMapWOT.toCLM (boundedIntegralOfUniformApprox μS g t ht))) :=
    hfs.mul hgt
  have hprod' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS ((s * t) n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (f * g) (fun n => s n * t n) hprod))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hprod).tendsto_limUnder
  have hprod'' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)) *
        ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (f * g) (fun n => s n * t n) hprod))) := by
    apply hprod'.congr'
    filter_upwards [] with n
    change ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n * t n)) =
      ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)) *
        ContinuousLinearMapWOT.toCLM (simpleIntegral μS (t n))
    rw [simpleIntegral_mul, ContinuousLinearMapWOT.toCLM_mul]
  exact tendsto_nhds_unique hprod'' hmul

lemma boundedIntegral_mul [Nonempty α]
    {f g : α → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    boundedIntegral μS (f * g) (hf.mul hg)
        (by
          rcases hbf with ⟨Cf, hCf⟩
          rcases hbg with ⟨Cg, hCg⟩
          let a₀ : α := Classical.choice (inferInstance : Nonempty α)
          have hCf0 : 0 ≤ Cf := (norm_nonneg (f a₀)).trans (hCf a₀)
          refine ⟨Cf * Cg, fun x => ?_⟩
          rw [Pi.mul_apply, norm_mul]
          exact mul_le_mul (hCf x) (hCg x) (norm_nonneg _) hCf0) =
      boundedIntegral μS f hf hbf * boundedIntegral μS g hg hbg := by
  classical
  rcases hbf with ⟨Cf, hCf⟩
  rcases hbg with ⟨Cg, hCg⟩
  let hbf' : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := ⟨Cf, hCf⟩
  let hbg' : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := ⟨Cg, hCg⟩
  rcases exists_uniform_simple_approx hf hbf' with ⟨sf, hsf, hsfB⟩
  rcases exists_uniform_simple_approx hg hbg' with ⟨sg, hsg, hsgB⟩
  rcases hsfB with ⟨Cs, hCs⟩
  let a₀ : α := Classical.choice (inferInstance : Nonempty α)
  have hCs0 : 0 ≤ Cs := (norm_nonneg (sf 0 a₀)).trans (hCs 0 a₀)
  have hCg0 : 0 ≤ Cg := (norm_nonneg (g a₀)).trans (hCg a₀)
  have hD0 : 0 < Cs + Cg + 1 := by linarith
  have hprod : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(sf n * sg n) x - (f * g) x‖ < ε := by
    intro ε hε
    let δ : ℝ := ε / (2 * (Cs + Cg + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    rcases hsf δ hδ with ⟨Nf, hNf⟩
    rcases hsg δ hδ with ⟨Ng, hNg⟩
    refine ⟨max Nf Ng, fun n hn x => ?_⟩
    simp only [SimpleFunc.mul_apply, Pi.mul_apply]
    have hsferr : ‖sf n x - f x‖ < δ := hNf n (le_trans (le_max_left _ _) hn) x
    have hsgerr : ‖sg n x - g x‖ < δ := hNg n (le_trans (le_max_right _ _) hn) x
    have hdecomp : sf n x * sg n x - f x * g x =
        sf n x * (sg n x - g x) + (sf n x - f x) * g x := by ring
    calc
      ‖sf n x * sg n x - f x * g x‖ =
          ‖sf n x * (sg n x - g x) + (sf n x - f x) * g x‖ := by rw [hdecomp]
      _ ≤ ‖sf n x‖ * ‖sg n x - g x‖ +
          ‖sf n x - f x‖ * ‖g x‖ := by
            calc
              _ ≤ ‖sf n x * (sg n x - g x)‖ +
                  ‖(sf n x - f x) * g x‖ := norm_add_le _ _
              _ = _ := by rw [norm_mul, norm_mul]
      _ ≤ Cs * δ + δ * Cg := by
        exact add_le_add
          (mul_le_mul (hCs n x) (le_of_lt hsgerr) (norm_nonneg _) hCs0)
          (mul_le_mul (le_of_lt hsferr) (hCg x) (norm_nonneg _) hδ.le)
      _ < ε := by
        calc
          Cs * δ + δ * Cg = (Cs + Cg) * δ := by ring
          _ ≤ (Cs + Cg + 1) * δ := by
            exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
          _ = ε / 2 := by dsimp [δ]; field_simp
          _ < ε := by linarith
  rw [boundedIntegral_eq_of_uniform_approx μS (hf.mul hg) _ hprod,
    boundedIntegral_eq_of_uniform_approx μS hf hbf' hsf,
    boundedIntegral_eq_of_uniform_approx μS hg hbg' hsg]
  exact boundedIntegralOfUniformApprox_mul μS hsf hsg hprod

lemma boundedIntegral_smul [Nonempty α] (c : ℂ) {f : α → ℂ} (hf : Measurable f)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    boundedIntegral μS (fun x => c * f x)
        (measurable_const.mul hf)
        (by
          rcases hbf with ⟨C, hC⟩
          refine ⟨‖c‖ * C, fun x => ?_⟩
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg c)) =
      c • boundedIntegral μS f hf hbf := by
  have hmul := boundedIntegral_mul μS measurable_const hf
    (⟨‖c‖, fun _ => le_rfl⟩) hbf
  rw [boundedIntegral_const] at hmul
  change boundedIntegral μS ((fun _ : α => c) * f) _ _ = _
  have hone : (c • (1 : H →WOT[ℂ] H)) * boundedIntegral μS f hf hbf =
      c • boundedIntegral μS f hf hbf := by
    ext x
    simp [ContinuousLinearMapWOT.mul_apply]
  rw [← hone]
  exact hmul

private lemma boundedIntegralOfUniformApprox_star [Nonempty α]
    {f : α → ℂ} {s : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (hstar : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(star (s n)) x - star (f x)‖ < ε) :
    boundedIntegralOfUniformApprox μS (fun x => star (f x)) (fun n => star (s n)) hstar =
      star (boundedIntegralOfUniformApprox μS f s hs) := by
  apply ContinuousLinearMapWOT.toCLM_injective
  have hfs : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hstarlim : Filter.Tendsto
      (fun n => star (ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)))) Filter.atTop
      (𝓝 (star (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs)))) :=
    continuous_star.continuousAt.tendsto.comp hfs
  have hstar' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (star (s n)))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (fun x => star (f x)) (fun n => star (s n))
          hstar))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact (simpleIntegral_toCLM_cauchySeq μS hstar).tendsto_limUnder
  have hstar'' : Filter.Tendsto
      (fun n => star (ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n)))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS (fun x => star (f x)) (fun n => star (s n))
          hstar))) := by
    convert hstar' using 1
    · funext n
      rw [simpleIntegral_star]
      apply ContinuousLinearMap.ext
      intro x
      rfl
  exact tendsto_nhds_unique hstar'' hstarlim

lemma boundedIntegral_star [Nonempty α]
    {f : α → ℂ} (hf : Measurable f) (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    boundedIntegral μS (fun x => star (f x)) (continuous_star.measurable.comp hf)
        (by
          rcases hbf with ⟨C, hC⟩
          exact ⟨C, fun x => by simpa using hC x⟩) =
      star (boundedIntegral μS f hf hbf) := by
  classical
  rcases exists_uniform_simple_approx hf hbf with ⟨s, hs, hsB⟩
  have hstar : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(star (s n)) x - star (f x)‖ < ε := by
    intro ε hε
    rcases hs ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn x => ?_⟩
    change ‖star ((s n) x) - star (f x)‖ < ε
    rw [← star_sub, norm_star]
    exact hN n hn x
  calc
    boundedIntegral μS (fun x => star (f x)) (continuous_star.measurable.comp hf) _ =
        boundedIntegralOfUniformApprox μS (fun x => star (f x)) (fun n => star (s n)) hstar :=
      boundedIntegral_eq_of_uniform_approx μS (continuous_star.measurable.comp hf) _ hstar
    _ = star (boundedIntegralOfUniformApprox μS f s hs) :=
      boundedIntegralOfUniformApprox_star μS hs hstar
    _ = star (boundedIntegral μS f hf hbf) := by
      rw [boundedIntegral_eq_of_uniform_approx μS hf hbf hs]

/-! ## The exponential multiplier and strong continuity

The bounded integral above is already the correct representation-level functional calculus.  The
next definitions record the part of Stone's construction which does not require a domain: the
exponential multiplier is bounded by one, and its strong continuity follows from the vector-state
norm-square identity and dominated convergence.
-/

/-- The exponential multiplier `x ↦ exp(itx)`, at real time `t`. -/
def expFunction (t : ℝ) : ℝ → ℂ :=
  fun x => Complex.exp ((t * x : ℝ) * Complex.I)

lemma expFunction_measurable (t : ℝ) : Measurable (expFunction t) := by
  change Measurable (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I))
  fun_prop

lemma expFunction_bounded (t : ℝ) : ∃ C, ∀ x, ‖expFunction t x‖ ≤ C := by
  refine ⟨1, fun x => ?_⟩
  exact (Complex.norm_exp_ofReal_mul_I (t * x)).le

lemma expFunction_modulus (t : ℝ) : ∀ x, ‖expFunction t x‖ = 1 := by
  intro x
  exact Complex.norm_exp_ofReal_mul_I (t * x)

lemma expFunction_neg_eq_star (t : ℝ) : expFunction (-t) = star (expFunction t) := by
  funext x
  change Complex.exp ((((-t) * x : ℝ) : ℂ) * Complex.I) =
    starRingEnd ℂ (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I))
  rw [← Complex.exp_conj]
  congr 1
  simp

lemma expFunction_diff_bounded (t s : ℝ) :
    ∃ C, ∀ x, ‖expFunction t x - expFunction s x‖ ≤ C := by
  refine ⟨2, fun x => ?_⟩
  calc
    ‖expFunction t x - expFunction s x‖ ≤
        ‖expFunction t x‖ + ‖expFunction s x‖ := norm_sub_le _ _
    _ = 2 := by rw [expFunction_modulus, expFunction_modulus]; norm_num

/-- The unitary group generated by `μS`'s self-adjoint operator: `expIntegral μS t = exp(itT)`. -/
noncomputable def expIntegral (μS : WOTSpectralMeasure ℝ H) (t : ℝ) : H →WOT[ℂ] H :=
  boundedIntegral μS (expFunction t) (expFunction_measurable t) (expFunction_bounded t)

lemma expFunction_add (t s : ℝ) : expFunction (t + s) = expFunction t * expFunction s := by
  funext x
  change Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) =
    Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)
  have harg : (((t + s) * x : ℝ) : ℂ) * Complex.I =
      ((t * x : ℝ) : ℂ) * Complex.I + ((s * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add]

lemma expIntegral_add (μS : WOTSpectralMeasure ℝ H) (t s : ℝ) :
    expIntegral μS (t + s) = expIntegral μS t * expIntegral μS s := by
  change boundedIntegral μS (expFunction (t + s)) (expFunction_measurable (t + s))
      (expFunction_bounded (t + s)) =
    boundedIntegral μS (expFunction t) (expFunction_measurable t) (expFunction_bounded t) *
      boundedIntegral μS (expFunction s) (expFunction_measurable s) (expFunction_bounded s)
  have h := boundedIntegral_mul μS (expFunction_measurable t) (expFunction_measurable s)
    (expFunction_bounded t) (expFunction_bounded s)
  rw [← h]
  apply boundedIntegral_congr μS (expFunction_measurable (t + s))
    ((expFunction_measurable t).mul (expFunction_measurable s))
    (expFunction_bounded (t + s))
    (by
      rcases expFunction_bounded t with ⟨Ct, hCt⟩
      rcases expFunction_bounded s with ⟨Cs, hCs⟩
      refine ⟨Ct * Cs, fun x => ?_⟩
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul (hCt x) (hCs x) (norm_nonneg _) (by
        exact (norm_nonneg (expFunction t 0)).trans (hCt 0)))
    (by
      intro x
      exact congrFun (expFunction_add t s) x)

lemma expIntegral_zero (μS : WOTSpectralMeasure ℝ H) :
    expIntegral μS 0 = (1 : H →WOT[ℂ] H) := by
  change boundedIntegral μS (expFunction 0) (expFunction_measurable 0)
      (expFunction_bounded 0) = (1 : H →WOT[ℂ] H)
  calc
    boundedIntegral μS (expFunction 0) (expFunction_measurable 0)
        (expFunction_bounded 0) =
        boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
          (⟨1, by simp⟩) := by
      apply boundedIntegral_congr μS (expFunction_measurable 0) measurable_const
        (expFunction_bounded 0) (⟨1, by simp⟩)
      intro x
      simp [expFunction]
    _ = 1 := by rw [boundedIntegral_const]; simp

lemma expIntegral_neg_mul (μS : WOTSpectralMeasure ℝ H) (t : ℝ) :
    expIntegral μS (-t) * expIntegral μS t = (1 : H →WOT[ℂ] H) := by
  calc
    expIntegral μS (-t) * expIntegral μS t = expIntegral μS (-t + t) :=
      (expIntegral_add μS (-t) t).symm
    _ = expIntegral μS 0 := by rw [neg_add_cancel]
    _ = 1 := expIntegral_zero μS

lemma expIntegral_mul_neg (μS : WOTSpectralMeasure ℝ H) (t : ℝ) :
    expIntegral μS t * expIntegral μS (-t) = (1 : H →WOT[ℂ] H) := by
  calc
    expIntegral μS t * expIntegral μS (-t) = expIntegral μS (t + -t) :=
      (expIntegral_add μS t (-t)).symm
    _ = expIntegral μS 0 := by rw [add_neg_cancel]
    _ = 1 := expIntegral_zero μS

lemma expIntegral_star (μS : WOTSpectralMeasure ℝ H) (t : ℝ) :
    star (expIntegral μS t) = expIntegral μS (-t) := by
  have h := boundedIntegral_star μS (expFunction_measurable t) (expFunction_bounded t)
  calc
    star (expIntegral μS t) =
        boundedIntegral μS (fun x => star (expFunction t x))
          (continuous_star.measurable.comp (expFunction_measurable t))
          (by
            rcases expFunction_bounded t with ⟨C, hC⟩
            exact ⟨C, fun x => by simpa using hC x⟩) := by
      simpa only [expIntegral] using h.symm
    _ = expIntegral μS (-t) := by
      apply boundedIntegral_congr μS
        (continuous_star.measurable.comp (expFunction_measurable t))
        (expFunction_measurable (-t))
        (by
          rcases expFunction_bounded t with ⟨C, hC⟩
          exact ⟨C, fun x => by simpa using hC x⟩)
        (expFunction_bounded (-t))
      intro x
      exact congrFun (expFunction_neg_eq_star t).symm x

lemma expIntegral_mem_unitary (μS : WOTSpectralMeasure ℝ H) (t : ℝ) :
    expIntegral μS t ∈ unitary (H →WOT[ℂ] H) := by
  let U : (H →WOT[ℂ] H)ˣ :=
    { val := expIntegral μS t
      inv := expIntegral μS (-t)
      val_inv := expIntegral_mul_neg μS t
      inv_val := expIntegral_neg_mul μS t }
  apply IsUnit.mem_unitary_of_star_mul_self ⟨U, rfl⟩
  rw [expIntegral_star]
  exact expIntegral_neg_mul μS t

@[nolint unusedArguments]
lemma expIntegral_sub_eq_boundedIntegral_diff [Nonempty H] (μS : WOTSpectralMeasure ℝ H)
    (t s : ℝ) (x : H) :
    expIntegral μS t x - expIntegral μS s x =
    boundedIntegral μS (fun z => expFunction t z - expFunction s z)
        ((expFunction_measurable t).sub (expFunction_measurable s))
        (expFunction_diff_bounded t s) x := by
  have h := boundedIntegral_sub μS (expFunction_measurable t) (expFunction_measurable s)
    (expFunction_bounded t) (expFunction_bounded s)
  have hx := congrArg (fun A : H →WOT[ℂ] H => A x) h
  change (boundedIntegral μS (expFunction t) (expFunction_measurable t)
      (expFunction_bounded t) x -
    boundedIntegral μS (expFunction s) (expFunction_measurable s)
      (expFunction_bounded s) x) =
    boundedIntegral μS (fun z => expFunction t z - expFunction s z)
      ((expFunction_measurable t).sub (expFunction_measurable s))
      (expFunction_diff_bounded t s) x
  exact hx.symm

lemma expIntegral_continuous (μS : WOTSpectralMeasure ℝ H) (x : H) :
    Continuous (fun t => expIntegral μS t x) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hdiffNormSq : Filter.Tendsto
      (fun t => ENNReal.ofReal
        (‖expIntegral μS t x - expIntegral μS t₀ x‖ ^ 2)) (𝓝 t₀) (𝓝 0) := by
    let μ : Measure ℝ := μS.diagonalMeasure x
    let F : ℝ → ℝ → ENNReal := fun t z =>
      ENNReal.ofReal (‖expFunction t z - expFunction t₀ z‖ ^ 2)
    let F₀ : ℝ → ENNReal := fun _ => 0
    have hFmeas : ∀ t, Measurable (F t) := by
      intro t
      change Measurable (fun z => ENNReal.ofReal
        (‖expFunction t z - expFunction t₀ z‖ ^ 2))
      exact ENNReal.continuous_ofReal.measurable.comp
        (((expFunction_measurable t).sub (expFunction_measurable t₀)).norm.pow_const 2)
    have hbound : ∀ᶠ t in 𝓝 t₀, ∀ᵐ z ∂μ, F t z ≤ ENNReal.ofReal 4 := by
      filter_upwards [] with t
      filter_upwards [] with z
      dsimp [F]
      change ENNReal.ofReal (‖expFunction t z - expFunction t₀ z‖ ^ 2) ≤
        ENNReal.ofReal 4
      apply ENNReal.ofReal_le_ofReal
      have hnorm : ‖expFunction t z - expFunction t₀ z‖ ≤ 2 := by
        calc
          ‖expFunction t z - expFunction t₀ z‖ ≤
              ‖expFunction t z‖ + ‖expFunction t₀ z‖ := norm_sub_le _ _
          _ = 2 := by rw [expFunction_modulus, expFunction_modulus]; norm_num
      have hsq := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr hnorm
      norm_num at hsq ⊢
      exact hsq
    have hfin : (∫⁻ z, ENNReal.ofReal 4 ∂μ) ≠ (⊤ : ENNReal) := by
      rw [lintegral_const, μS.diagonalMeasure_univ]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hlim : ∀ᵐ z ∂μ, Filter.Tendsto (fun t => F t z) (𝓝 t₀) (𝓝 (F₀ z)) := by
      filter_upwards [] with z
      have hcont : Continuous (fun t : ℝ => expFunction t z) := by
        unfold expFunction
        fun_prop
      have hdiff : Filter.Tendsto
          (fun t => expFunction t z - expFunction t₀ z) (𝓝 t₀) (𝓝 0) := by
        convert hcont.continuousAt.tendsto.sub
          (tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => expFunction t₀ z) (𝓝 t₀) (𝓝 (expFunction t₀ z))) using 1
        simp
      have hnorm : Filter.Tendsto
          (fun t => ‖expFunction t z - expFunction t₀ z‖ ^ 2) (𝓝 t₀) (𝓝 (0 ^ 2)) := by
        convert (continuous_norm.pow 2).continuousAt.tendsto.comp hdiff using 1
        · rfl
        · simp
      change Filter.Tendsto
        (fun t => ENNReal.ofReal (‖expFunction t z - expFunction t₀ z‖ ^ 2))
        (𝓝 t₀) (𝓝 0)
      have hout := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm
      convert hout using 1
      · funext t
        rfl
      · simp
    have hlintegral : Filter.Tendsto
        (fun t => ∫⁻ z, F t z ∂μ) (𝓝 t₀) (𝓝 (∫⁻ z, F₀ z ∂μ)) :=
      MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
        (fun _ : ℝ => ENNReal.ofReal 4)
        (by filter_upwards [] with t; exact hFmeas t) hbound hfin hlim
    have hlintegral0 : Filter.Tendsto
        (fun t => ∫⁻ z, F t z ∂μ) (𝓝 t₀) (𝓝 0) := by
      simpa [F₀] using hlintegral
    have hnormsq : ∀ t, ENNReal.ofReal
        (‖expIntegral μS t x - expIntegral μS t₀ x‖ ^ 2) = ∫⁻ z, F t z ∂μ := by
      intro t
      rw [expIntegral_sub_eq_boundedIntegral_diff]
      simpa [F, μ] using
        (boundedIntegral_norm_sq μS (f := fun z => expFunction t z - expFunction t₀ z)
          ((expFunction_measurable t).sub (expFunction_measurable t₀))
          (expFunction_diff_bounded t t₀) x)
    exact hlintegral0.congr' (Filter.Eventually.of_forall fun t => (hnormsq t).symm)
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hevent : ∀ᶠ t in 𝓝 t₀,
      ENNReal.ofReal (‖expIntegral μS t x - expIntegral μS t₀ x‖ ^ 2) <
        ENNReal.ofReal (ε ^ 2) := by
    exact hdiffNormSq.eventually
      (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hεsq))
  filter_upwards [hevent] with t ht
  rw [dist_eq_norm]
  apply (sq_lt_sq₀ (norm_nonneg _) hε.le).mp
  exact (ENNReal.ofReal_lt_ofReal_iff hεsq).mp ht

/-- A strongly continuous one-parameter group of unitary bounded operators.

The continuity is stated in the strong operator sense, pointwise on vectors.  This is the
natural representation-level output of the bounded spectral integral; no unbounded generator is
needed in this interface. -/
structure StrongUnitaryOneParameterGroup
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The unitary at each real time. -/
  toFun : ℝ → H →WOT[ℂ] H
  mem_unitary : ∀ t, toFun t ∈ unitary (H →WOT[ℂ] H)
  map_zero : toFun 0 = 1
  map_add : ∀ t s, toFun (t + s) = toFun t * toFun s
  strong_continuous : ∀ x, Continuous (fun t => toFun t x)

namespace StrongUnitaryOneParameterGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance : CoeFun (StrongUnitaryOneParameterGroup H)
    (fun _ => ℝ → H →WOT[ℂ] H) := ⟨StrongUnitaryOneParameterGroup.toFun⟩

@[simp]
lemma zero (G : StrongUnitaryOneParameterGroup H) : G 0 = 1 := G.map_zero

lemma add (G : StrongUnitaryOneParameterGroup H) (t s : ℝ) : G (t + s) = G t * G s :=
  G.map_add t s

lemma unitary (G : StrongUnitaryOneParameterGroup H) (t : ℝ) : G t ∈ unitary (H →WOT[ℂ] H) :=
  G.mem_unitary t

lemma continuous_apply (G : StrongUnitaryOneParameterGroup H) (x : H) :
    Continuous (fun t => G t x) := G.strong_continuous x

end StrongUnitaryOneParameterGroup

/-- The unitary group obtained by exponentiating a bounded real spectral integral. -/
noncomputable def expUnitaryGroup (μS : WOTSpectralMeasure ℝ H) :
    StrongUnitaryOneParameterGroup H where
  toFun := expIntegral μS
  mem_unitary := expIntegral_mem_unitary μS
  map_zero := expIntegral_zero μS
  map_add := expIntegral_add μS
  strong_continuous := expIntegral_continuous μS

lemma boundedIntegralOfUniformApprox_inner
    [Nonempty α]
    {f : α → ℂ} {s : ℕ → SimpleFunc α ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε)
    (hsBound : ∃ C : ℝ, ∀ n x, ‖s n x‖ ≤ C)
    (x y : H)
    (hfinite : IsFiniteMeasure (μS.scalarMeasure x y).variation) :
    ⟪y, boundedIntegralOfUniformApprox μS f s hs x⟫_ℂ =
      ∫ᵛ z, f z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μS.scalarMeasure x y] := by
  let μ := μS.scalarMeasure x y
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℂ
  letI : IsFiniteMeasure μ.variation := hfinite
  have hmeas : ∀ n, AEStronglyMeasurable (s n) μ.variation := by
    intro n
    exact (s n).measurable.aestronglyMeasurable
  have hbound : ∃ C : ℝ, ∀ᶠ n in Filter.atTop, ∀ᵐ z ∂μ.variation, ‖s n z‖ ≤ C := by
    rcases hsBound with ⟨C, hC⟩
    exact ⟨C, Filter.Eventually.of_forall (fun n => Filter.Eventually.of_forall (hC n))⟩
  have hlim : ∀ᵐ z ∂μ.variation,
      Filter.Tendsto (fun n => s n z) Filter.atTop (𝓝 (f z)) := by
    filter_upwards [] with z
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases hs ε hε with ⟨N, hN⟩
    exact ⟨N, fun n hn => by simpa only [dist_eq_norm] using hN n hn z⟩
  have hint :
      Filter.Tendsto (fun n => ∫ᵛ z, s n z ∂[B; μ]) Filter.atTop
        (𝓝 (∫ᵛ z, f z ∂[B; μ])) := by
    exact MeasureTheory.VectorMeasure.tendsto_integral_filter_of_norm_le_const
      (μ := μ) (B := B) (Filter.Eventually.of_forall hmeas) hbound hlim
  have hsimple : ∀ n,
      ∫ᵛ z, s n z ∂[B; μ] =
        ⟪y, simpleIntegral μS (s n) x⟫_ℂ := by
    intro n
    rcases hsBound with ⟨C, hC⟩
    let a₀ : α := Classical.choice (inferInstance : Nonempty α)
    have hC0 : 0 ≤ C := (norm_nonneg (s n a₀)).trans (hC n a₀)
    have hi : Integrable (s n) μ.variation :=
      Integrable.of_bound (s n).measurable.aestronglyMeasurable C
        (Filter.Eventually.of_forall (hC n))
    rw [VectorMeasure.integral_eq_setToFun]
    rw [setToFun_simpleFunc (dominatedFinMeasAdditive_cbmApplyMeasure μ B) (s n) hi]
    rw [simpleIntegral_inner]
    apply Finset.sum_congr rfl
    intro z hz
    rfl
  have hclm := (simpleIntegral_toCLM_cauchySeq μS hs).tendsto_limUnder
  have hclm' : Filter.Tendsto
      (fun n => ContinuousLinearMapWOT.toCLM (simpleIntegral μS (s n))) Filter.atTop
      (𝓝 (ContinuousLinearMapWOT.toCLM
        (boundedIntegralOfUniformApprox μS f s hs))) := by
    rw [boundedIntegralOfUniformApprox_eq_limUnder]
    exact hclm
  have hoperator :
      Filter.Tendsto
        (fun n => ⟪y, simpleIntegral μS (s n) x⟫_ℂ) Filter.atTop
        (𝓝 (⟪y, boundedIntegralOfUniformApprox μS f s hs x⟫_ℂ)) := by
    have hev : Continuous (fun A : H →L[ℂ] H => ⟪y, A x⟫_ℂ) := by fun_prop
    exact hev.continuousAt.tendsto.comp hclm'
  have hsimple' :
      Filter.Tendsto (fun n => ∫ᵛ z, s n z ∂[B; μ]) Filter.atTop
        (𝓝 (⟪y, boundedIntegralOfUniformApprox μS f s hs x⟫_ℂ)) := by
    simpa only [hsimple] using hoperator
  exact tendsto_nhds_unique hsimple' hint

/-- The pairing is real-scalar multiplication on the complex scalar measure. -/
def weakIntegral (f : α → ℝ) (x y : H) : ℂ :=
  ∫ᵛ z, f z ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ);
    μS.scalarMeasure x y]

/-- The complex weak integral of a complex-valued spectral multiplier.  The real-valued
integral above is retained for the self-adjoint reconstruction API; this companion is the
bounded-unitary side of the Cayley construction. -/
def complexWeakIntegral (f : α → ℂ) (x y : H) : ℂ :=
  ∫ᵛ z, f z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
    μS.scalarMeasure x y]


lemma weakIntegral_map {β : Type*} [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (g : β → ℝ)
    (x y : H) (hgm : AEStronglyMeasurable g ((μS.scalarMeasure x y).variation.map f))
    (hgi : (μS.scalarMeasure x y).Integrable (g ∘ f)) :
    (μS.map f hf).weakIntegral g x y = μS.weakIntegral (g ∘ f) x y := by
  unfold weakIntegral
  rw [scalarMeasure_map]
  exact VectorMeasure.integral_map hf hgm hgi

lemma complexWeakIntegral_map {β : Type*} [MeasurableSpace β]
    (f : α → β) (hf : Measurable f) (g : β → ℂ)
    (x y : H) (hgm : AEStronglyMeasurable g ((μS.scalarMeasure x y).variation.map f))
    (hgi : (μS.scalarMeasure x y).Integrable (g ∘ f)) :
    (μS.map f hf).complexWeakIntegral g x y =
      μS.complexWeakIntegral (g ∘ f) x y := by
  unfold complexWeakIntegral
  rw [scalarMeasure_map]
  exact VectorMeasure.integral_map hf hgm hgi

lemma unitaryConjSpectralMeasure_scalarMeasure_apply
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') (μS : WOTSpectralMeasure α H) (x y : H') (S : Set α) :
    (unitaryConjSpectralMeasure u μS).scalarMeasure x y S =
      μS.scalarMeasure (u.symm x) (u.symm y) S := by
  rw [scalarMeasure_apply, scalarMeasure_apply]
  change ⟪y, u ((ContinuousLinearMapWOT.toCLM (μS S)) (u.symm x))⟫_ℂ = _
  exact (u.symm.inner_map_eq_flip _ _).symm

lemma unitaryConjSpectralMeasure_scalarMeasure
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') (μS : WOTSpectralMeasure α H) (x y : H') :
    (unitaryConjSpectralMeasure u μS).scalarMeasure x y =
      μS.scalarMeasure (u.symm x) (u.symm y) := by
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  exact unitaryConjSpectralMeasure_scalarMeasure_apply u μS x y S

lemma unitaryConjSpectralMeasure_diagonalMeasure
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') (μS : WOTSpectralMeasure α H) (x : H') :
    (unitaryConjSpectralMeasure u μS).diagonalMeasure x =
      μS.diagonalMeasure (u.symm x) := by
  apply Measure.ext
  intro S hS
  rw [(unitaryConjSpectralMeasure u μS).diagonalMeasure_apply_eq_norm_sq x S hS,
    μS.diagonalMeasure_apply_eq_norm_sq (u.symm x) S hS,
    unitaryConjSpectralMeasure_apply]
  change ENNReal.ofReal
      (‖u ((ContinuousLinearMapWOT.toCLM (μS S)) (u.symm x))‖ ^ 2) = _
  rw [u.norm_map]
  rfl

lemma unitaryConjSpectralMeasure_weakIntegral
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') (μS : WOTSpectralMeasure α H) (f : α → ℝ) (x y : H') :
    (unitaryConjSpectralMeasure u μS).weakIntegral f x y =
      μS.weakIntegral f (u.symm x) (u.symm y) := by
  unfold weakIntegral
  rw [unitaryConjSpectralMeasure_scalarMeasure]

end WOTSpectralMeasure

end QuantumMechanics

namespace SpectralMeasure

open QuantumMechanics

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Forgetting norm σ-additivity and retaining weak-operator σ-additivity. -/
def toWOTMap : (H →L[ℂ] H) →+ (H →WOT[ℂ] H) :=
  { toFun := ContinuousLinearMapWOT.ofCLM
    map_zero' := by simp
    map_add' := by intro S T; simp }

@[nolint unusedArguments]
lemma continuous_toWOTMap : Continuous (toWOTMap (H := H)) := by
  change Continuous (ContinuousLinearMapWOT.ofCLM :
    (H →L[ℂ] H) → (H →WOT[ℂ] H))
  exact ContinuousLinearMapWOT.continuous_ofCLM

/-- A `SpectralMeasure`, viewed in the weak-operator-topology type `H →WOT[ℂ] H`. -/
def toWOT (μS : SpectralMeasure α H) : WOTSpectralMeasure α H where
  toVectorMeasure := by
    exact μS.toVectorMeasure.mapRange (toWOTMap (H := H))
      (continuous_toWOTMap (H := H))
  isStarProjection' A := by
    change IsStarProjection (ContinuousLinearMapWOT.ofCLM (μS A))
    refine ⟨?_, ?_⟩
    · change ContinuousLinearMapWOT.ofCLM (μS A) *
        ContinuousLinearMapWOT.ofCLM (μS A) = ContinuousLinearMapWOT.ofCLM (μS A)
      rw [← ContinuousLinearMapWOT.ofCLM_mul]
      exact congrArg ContinuousLinearMapWOT.ofCLM
        (μS.isStarProjection A).isIdempotentElem
    · apply ContinuousLinearMapWOT.toCLM_injective
      change star (μS A) = μS A
      exact (μS.isStarProjection A).isSelfAdjoint
  univ' := by
    change ContinuousLinearMapWOT.ofCLM (μS Set.univ) = 1
    rw [SpectralMeasure.univ μS]
    simp

@[simp]
lemma toWOT_apply (μS : SpectralMeasure α H) (A : Set α) : μS.toWOT A =
    ContinuousLinearMapWOT.ofCLM (μS A) := by
  change (μS.toVectorMeasure.mapRange (toWOTMap (H := H))
      (continuous_toWOTMap (H := H))) A = _
  rw [MeasureTheory.VectorMeasure.mapRange_apply]
  rfl

end SpectralMeasure

end
