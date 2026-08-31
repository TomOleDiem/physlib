/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.SpectralTheory.WeakSpectralMeasure
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!

# Pure-point / absolutely-continuous / singular-continuous spectral type decomposition

This file builds the general (representation-free, infinite-dimensional) decomposition of a
Hilbert space `H` carrying a `WOTSpectralMeasure ℝ H` into its pure-point, absolutely-continuous,
and singular-continuous subspaces.

## Main definitions

* `WOTSpectralMeasure.pointSpectrumSet E` : the (proved countable) set of reals `l` with
  `E {l} ≠ 0`.
* `WOTSpectralMeasure.Hpp E` : the pure-point subspace, the range of `E (pointSpectrumSet E)`.
* `WOTSpectralMeasure.Hcont E` : the orthogonal complement of `Hpp E`; proved to equal the range
  of `E (pointSpectrumSet E)ᶜ`, and every vector state `E.diagonalMeasure x` for `x ∈ Hcont E` is
  proved to be atom-free.
* `WOTSpectralMeasure.IsPureAC`, `WOTSpectralMeasure.IsPureSC` : membership predicates on
  `Hcont E` via the classical Lebesgue decomposition of the diagonal measure against `volume`.
* `WOTSpectralMeasure.Hac E`, `WOTSpectralMeasure.Hsc E` : the corresponding submodules of
  `Hcont E`, proved to be genuine (closed-under-`+`/`smul`) submodules, and proved orthogonal to
  each other.

## Main results

* `WOTSpectralMeasure.norm_inner_le_sqrt_diagonalMeasure_mul_sqrt_diagonalMeasure` : the
  Cauchy-Schwarz domination estimate for the sesquilinear "vector measures"
  `S ↦ ⟪y, E S x⟫`.
* `Measure.countable_setOf_meas_singleton_pos` : a finite measure on `ℝ` has only countably many
  atoms.
* `WOTSpectralMeasure.pointSpectrumSet_countable`, `.measurableSet_pointSpectrumSet` : the point
  spectrum is countable, hence Borel.
* `WOTSpectralMeasure.diagonalMeasure_nullSingletonClass_of_mem_H_cont` : vector states supported
  on `Hcont E` are genuinely atom-free (not merely off the point spectrum).
* `WOTSpectralMeasure.isPureACSubmodule`, `.isPureSCSubmodule` : `Hac`/`Hsc` are honest
  submodules of `Hcont E`.
* `WOTSpectralMeasure.H_ac_isOrtho_H_sc` : `Hac E ⟂ Hsc E`.
* `WOTSpectralMeasure.diagonalMeasure_apply_eq_restrict` : the vector-state measure of `E S x` is
  the restriction to `S` of the vector-state measure of `x`, for every measurable `S`.
* `WOTSpectralMeasure.apply_mem_H_cont_of_mem_H_cont` : `Hcont E` is invariant under every
  spectral projection `E T`.
* `WOTSpectralMeasure.H_cont_eq_sup_H_ac_H_sc` : the completeness of the a.c./s.c. splitting of
  `Hcont E` (Reed-Simon Vol. I, Theorem VII.4), proved in full.

Every theorem in this file is proved without `sorry`.

-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace
open MeasureTheory Set ENNReal TopologicalSpace

namespace MeasureTheory

/-! ## Phase 1, item 2 : the atomic/non-atomic decomposition of a finite measure on `ℝ` -/

namespace Measure

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

/-- A finite measure on `ℝ` has only countably many atoms. This is standard real analysis (not
currently in Mathlib as a general statement): for each `n`, the set of points with mass `> 1/n`
must be finite, since finitely many disjoint atoms of mass `> 1/n` cannot exceed the (finite)
total mass; the atom set is the countable union of these level sets. -/
theorem countable_setOf_meas_singleton_pos : {a : ℝ | 0 < μ {a}}.Countable := by
  have hfin : ∀ n : ℕ, {a : ℝ | (n : ℝ≥0∞)⁻¹ < μ {a}}.Finite := by
    intro n
    by_contra hinf
    rw [Set.not_finite] at hinf
    set f : ℕ → ℝ := fun i => ((hinf.natEmbedding _ i : ℝ))
    have hf_inj : Function.Injective f :=
      Subtype.coe_injective.comp (hinf.natEmbedding _).injective
    have hf_mem : ∀ i, (n : ℝ≥0∞)⁻¹ < μ {f i} := fun i => (hinf.natEmbedding _ i).2
    have hdisj : Pairwise (Function.onFun Disjoint fun i => ({f i} : Set ℝ)) := fun i j hij => by
      simp [Function.onFun, Set.disjoint_singleton, hf_inj.ne hij]
    have hsum : μ (⋃ i, {f i}) = ∑' i, μ ({f i} : Set ℝ) :=
      measure_iUnion hdisj (fun i => measurableSet_singleton _)
    have htop : ∑' _i : ℕ, μ ({f _i} : Set ℝ) = ⊤ := by
      apply top_unique
      calc (⊤ : ℝ≥0∞) = ∑' _ : ℕ, (n : ℝ≥0∞)⁻¹ :=
            (ENNReal.tsum_const_eq_top_of_ne_zero (by simp)).symm
        _ ≤ ∑' i, μ ({f i} : Set ℝ) := ENNReal.tsum_le_tsum (fun i => (hf_mem i).le)
    have htop' : μ (⋃ i, {f i}) = ⊤ := hsum.trans htop
    have hle : μ (⋃ i, {f i}) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    rw [htop'] at hle
    exact absurd hle (by simpa using (measure_lt_top μ Set.univ).ne)
  have hunion : {a : ℝ | 0 < μ {a}} = ⋃ n : ℕ, {a : ℝ | (n : ℝ≥0∞)⁻¹ < μ {a}} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro ha
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt ha.ne'
      exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩
      exact lt_of_le_of_lt (bot_le (a := (n : ℝ≥0∞)⁻¹)) hn
  rw [hunion]
  exact Set.countable_iUnion (fun n => (hfin n).countable)

/-- The atomic part of a finite measure on `ℝ`: the (countable) set of points carrying positive
mass. -/
def atomSet : Set ℝ := {a | μ {a} ≠ 0}

@[nolint unusedArguments]
lemma mem_atomSet_iff {a : ℝ} : a ∈ μ.atomSet ↔ μ {a} ≠ 0 := Iff.rfl

/-- `atomSet` is countable. -/
theorem atomSet_countable : μ.atomSet.Countable := by
  have : μ.atomSet = {a : ℝ | 0 < μ {a}} := by
    ext a; simp [atomSet, pos_iff_ne_zero]
  rw [this]
  exact μ.countable_setOf_meas_singleton_pos

/-- The restriction of a finite measure to the complement of its atom set is atom-free. -/
instance restrict_compl_atomSet_nullSingletonClass :
    NullSingletonClass (μ.restrict μ.atomSetᶜ) where
  measure_singleton a := by
    rw [Measure.restrict_apply (measurableSet_singleton a)]
    by_cases ha : a ∈ μ.atomSet
    · have : ({a} : Set ℝ) ∩ μ.atomSetᶜ = ∅ := by
        ext b; simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_compl_iff]
        constructor
        · rintro ⟨rfl, hb⟩; exact hb ha
        · exact fun h => h.elim
      simp [this]
    · rw [Measure.atomSet, Set.mem_setOf_eq, not_not] at ha
      exact measure_mono_null Set.inter_subset_left ha

end Measure

end MeasureTheory

namespace QuantumMechanics
namespace WOTSpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (E : WOTSpectralMeasure ℝ H)

/-! ## Phase 1, item 1 : the Cauchy-Schwarz domination lemma -/

/-- `E S` moved across the inner product using idempotence and self-adjointness: the
two-vector generalization of `WOTSpectralMeasure.inner_eq_inner_projection`. -/
private lemma inner_eq_inner_proj_proj (S : Set ℝ) (x y : H) :
    ⟪y, E S x⟫_ℂ = ⟪E S y, E S x⟫_ℂ := by
  let p : H →L[ℂ] H := ContinuousLinearMapWOT.toCLM (E S)
  have hp := E.isStarProjection S
  have hmul : p * p = p := congrArg ContinuousLinearMapWOT.toCLM hp.isIdempotentElem
  have hstar : ContinuousLinearMap.adjoint p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isSelfAdjoint
  change ⟪y, p x⟫_ℂ = ⟪p y, p x⟫_ℂ
  calc
    ⟪y, p x⟫_ℂ = ⟪y, p (p x)⟫_ℂ := by
      congr 1; exact (congrArg (fun q : H →L[ℂ] H => q x) hmul).symm
    _ = ⟪ContinuousLinearMap.adjoint p y, p x⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_left p (p x) y).symm
    _ = ⟪p y, p x⟫_ℂ := by rw [hstar]

/-- **Cauchy-Schwarz domination.** For any measurable (or not — the inequality is trivial off the
`σ`-algebra) set `S` and vectors `x y : H`, the matrix-coefficient measure `⟪y, E(S)x⟫` is
dominated by the geometric mean of the two diagonal measures. -/
theorem norm_inner_le_sqrt_diagonalMeasure_mul_sqrt_diagonalMeasure (S : Set ℝ) (x y : H) :
    ‖⟪y, E S x⟫_ℂ‖ ≤
      Real.sqrt (E.diagonalMeasure x S).toReal * Real.sqrt (E.diagonalMeasure y S).toReal := by
  by_cases hS : MeasurableSet S
  · have hxeq : Real.sqrt (E.diagonalMeasure x S).toReal = ‖E S x‖ := by
      rw [E.diagonalMeasure_apply_eq_norm_sq x S hS, ENNReal.toReal_ofReal (sq_nonneg _),
        Real.sqrt_sq (norm_nonneg _)]
    have hyeq : Real.sqrt (E.diagonalMeasure y S).toReal = ‖E S y‖ := by
      rw [E.diagonalMeasure_apply_eq_norm_sq y S hS, ENNReal.toReal_ofReal (sq_nonneg _),
        Real.sqrt_sq (norm_nonneg _)]
    rw [hxeq, hyeq, E.inner_eq_inner_proj_proj S x y]
    calc ‖⟪E S y, E S x⟫_ℂ‖ ≤ ‖E S y‖ * ‖E S x‖ := norm_inner_le_norm _ _
      _ = ‖E S x‖ * ‖E S y‖ := mul_comm _ _
  · have hSz : E S = 0 := E.apply_eq_zero_of_not_measurableSet hS
    simp [hSz]
    positivity

/-! ## A general disjoint-orthogonality lemma (a two-vector generalization of
`WOTSpectralMeasure.inner_eq_zero_of_disjoint`) -/

/-- Two vectors, each in the range of `E` on disjoint measurable sets, are orthogonal. -/
theorem inner_apply_apply_eq_zero_of_disjoint {A B : Set ℝ} (h : Disjoint A B)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (x y : H) :
    ⟪E A x, E B y⟫_ℂ = 0 := by
  let pA : H →L[ℂ] H := ContinuousLinearMapWOT.toCLM (E A)
  let pB : H →L[ℂ] H := ContinuousLinearMapWOT.toCLM (E B)
  have hcomp : pA * pB = 0 := congrArg ContinuousLinearMapWOT.toCLM (E.comp_of_disjoint h hA hB)
  have hstar : ContinuousLinearMap.adjoint pA = pA := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM (E.isStarProjection A).isSelfAdjoint
  change ⟪pA x, pB y⟫_ℂ = 0
  calc
    ⟪pA x, pB y⟫_ℂ = ⟪x, ContinuousLinearMap.adjoint pA (pB y)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right pA x (pB y)).symm
    _ = ⟪x, pA (pB y)⟫_ℂ := by rw [hstar]
    _ = ⟪x, (pA * pB) y⟫_ℂ := rfl
    _ = 0 := by rw [hcomp]; simp

/-- If a vector state vanishes on a measurable set, the projection annihilates the vector. This
is the basic mechanism behind the submodule/orthogonality proofs below: it is often simpler than
routing through the Cauchy-Schwarz domination estimate. -/
theorem apply_eq_zero_iff_diagonalMeasure_eq_zero {S : Set ℝ} (hS : MeasurableSet S) (x : H) :
    E S x = 0 ↔ E.diagonalMeasure x S = 0 := by
  constructor
  · intro h
    rw [E.diagonalMeasure_apply_eq_norm_sq x S hS, h]
    simp
  · intro h
    rw [E.diagonalMeasure_apply_eq_norm_sq x S hS, ENNReal.ofReal_eq_zero] at h
    have h0 : ‖E S x‖ ^ 2 = 0 := le_antisymm h (sq_nonneg _)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp h0)

/-! ## Phase 1, item 3 : the point spectrum and the pure-point subspace -/

variable [SeparableSpace H]

/-- The point spectrum: the reals `l` at which the spectral measure has a nonzero atom. -/
def pointSpectrumSet : Set ℝ := {l | E {l} ≠ 0}

/-- Every point of the point spectrum carries a witness vector not killed by `E {l}`. -/
@[nolint unusedArguments]
theorem exists_apply_ne_zero_of_mem_pointSpectrumSet {l : ℝ} (hl : l ∈ E.pointSpectrumSet) :
    ∃ x : H, E {l} x ≠ 0 := by
  by_contra h
  push_neg at h
  exact hl (ContinuousLinearMapWOT.ext (fun x => by simp [h x]))

open Classical in
/-- A choice of witness vector for `l ∈ pointSpectrumSet E`, and `0` otherwise. -/
private noncomputable def pointWitness (l : ℝ) : H :=
  if h : l ∈ E.pointSpectrumSet then (E.exists_apply_ne_zero_of_mem_pointSpectrumSet h).choose
  else 0

private lemma pointWitness_spec {l : ℝ} (hl : l ∈ E.pointSpectrumSet) :
    E {l} (E.pointWitness l) ≠ 0 := by
  rw [pointWitness, dif_pos hl]
  exact (E.exists_apply_ne_zero_of_mem_pointSpectrumSet hl).choose_spec

open Classical in
/-- A unit vector spanning `E {l} (pointWitness l)`, for `l ∈ pointSpectrumSet E`. -/
private noncomputable def pointUnitVector (l : ℝ) : H :=
  if h : l ∈ E.pointSpectrumSet then
    (‖E {l} (E.pointWitness l)‖⁻¹ : ℂ) • E {l} (E.pointWitness l)
  else 0

private lemma norm_pointUnitVector {l : ℝ} (hl : l ∈ E.pointSpectrumSet) :
    ‖E.pointUnitVector l‖ = 1 := by
  rw [pointUnitVector, dif_pos hl, norm_smul]
  have hne : ‖E {l} (E.pointWitness l)‖ ≠ 0 := norm_ne_zero_iff.mpr (E.pointWitness_spec hl)
  rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hne]

private lemma inner_pointUnitVector_eq_zero {l l' : ℝ} (hl : l ∈ E.pointSpectrumSet)
    (hl' : l' ∈ E.pointSpectrumSet) (hne : l ≠ l') :
    ⟪E.pointUnitVector l, E.pointUnitVector l'⟫_ℂ = 0 := by
  rw [pointUnitVector, pointUnitVector, dif_pos hl, dif_pos hl', inner_smul_left, inner_smul_right]
  have : ⟪E {l} (E.pointWitness l), E {l'} (E.pointWitness l')⟫_ℂ = 0 :=
    E.inner_apply_apply_eq_zero_of_disjoint
      (by simp [Set.disjoint_singleton, hne]) (measurableSet_singleton l)
      (measurableSet_singleton l') _ _
  simp [this]

/-- **The point spectrum is countable.** Pairwise orthogonal unit vectors indexed by
`pointSpectrumSet E` sit at pairwise distance `√2`, so open balls of radius `√2/2` around them are
disjoint; a separable Hilbert space cannot support uncountably many disjoint nonempty open sets. -/
theorem pointSpectrumSet_countable : E.pointSpectrumSet.Countable := by
  have hpairwise : E.pointSpectrumSet.PairwiseDisjoint
      (fun l => Metric.ball (E.pointUnitVector l) (Real.sqrt 2 / 2)) := by
    intro l hl l' hl' hne
    rw [Function.onFun, Set.disjoint_left]
    rintro z hz hz'
    have hdist : ‖E.pointUnitVector l - E.pointUnitVector l'‖ < Real.sqrt 2 := by
      calc ‖E.pointUnitVector l - E.pointUnitVector l'‖
          ≤ ‖E.pointUnitVector l - z‖ + ‖z - E.pointUnitVector l'‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < Real.sqrt 2 / 2 + Real.sqrt 2 / 2 := by
              have h1 : ‖E.pointUnitVector l - z‖ < Real.sqrt 2 / 2 := by
                have := Metric.mem_ball.mp hz
                rw [dist_eq_norm] at this
                simpa [norm_sub_rev] using this
              have h2 : ‖z - E.pointUnitVector l'‖ < Real.sqrt 2 / 2 := by
                have := Metric.mem_ball.mp hz'
                rw [dist_eq_norm] at this
                simpa [norm_sub_rev] using this
              linarith
        _ = Real.sqrt 2 := by ring
    have hsq : ‖E.pointUnitVector l - E.pointUnitVector l'‖ ^ 2 = 2 := by
      rw [norm_sub_sq (𝕜 := ℂ), E.norm_pointUnitVector hl, E.norm_pointUnitVector hl',
        E.inner_pointUnitVector_eq_zero hl hl' hne]
      norm_num
    have heq : ‖E.pointUnitVector l - E.pointUnitVector l'‖ = Real.sqrt 2 := by
      rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
    linarith [heq ▸ hdist]
  refine Set.PairwiseDisjoint.countable_of_isOpen hpairwise ?_ ?_
  · intro l _; exact Metric.isOpen_ball
  · intro l hl
    refine ⟨E.pointUnitVector l, ?_⟩
    simp [Metric.mem_ball, Real.sqrt_pos]

theorem measurableSet_pointSpectrumSet : MeasurableSet E.pointSpectrumSet :=
  E.pointSpectrumSet_countable.measurableSet

/-- The pure-point subspace: the range of the projection onto the point spectrum. -/
def Hpp : Submodule ℂ H := (ContinuousLinearMapWOT.toCLM (E E.pointSpectrumSet)).range

@[nolint unusedArguments]
theorem isClosed_H_pp : IsClosed (E.Hpp : Set H) :=
  ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (congrArg ContinuousLinearMapWOT.toCLM (E.isStarProjection E.pointSpectrumSet).isIdempotentElem)

/-! ## Phase 2, item 4 : the continuous subspace -/

/-- The continuous subspace: the orthogonal complement of the pure-point subspace. -/
def Hcont : Submodule ℂ H := (E.Hpp)ᗮ

/-- `Hcont E` is also the range of the complementary projection. -/
theorem H_cont_eq_range_compl :
    E.Hcont = (ContinuousLinearMapWOT.toCLM (E E.pointSpectrumSetᶜ)).range := by
  set S := E.pointSpectrumSet
  have hSc : MeasurableSet Sᶜ := E.measurableSet_pointSpectrumSet.compl
  set p : H →L[ℂ] H := ContinuousLinearMapWOT.toCLM (E S)
  set q : H →L[ℂ] H := ContinuousLinearMapWOT.toCLM (E Sᶜ)
  have hsum : p + q = 1 := by
    have : E S + E Sᶜ = 1 := by
      rw [← E.of_union disjoint_compl_right E.measurableSet_pointSpectrumSet hSc]
      simpa using E.univ
    simpa [p, q] using congrArg ContinuousLinearMapWOT.toCLM this
  have hqp : q = 1 - p := eq_sub_iff_add_eq.mpr (by rw [add_comm]; exact hsum)
  have hpidem_clm : IsIdempotentElem p :=
    congrArg ContinuousLinearMapWOT.toCLM (E.isStarProjection S).isIdempotentElem
  have hqidem_clm : IsIdempotentElem q :=
    congrArg ContinuousLinearMapWOT.toCLM (E.isStarProjection Sᶜ).isIdempotentElem
  have hSA_clm : IsSelfAdjoint p :=
    congrArg ContinuousLinearMapWOT.toCLM (E.isStarProjection S).isSelfAdjoint
  have hpsym : (p : H →ₗ[ℂ] H).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hSA_clm
  have hpidem : IsIdempotentElem (p : H →ₗ[ℂ] H) :=
    ContinuousLinearMap.IsIdempotentElem.toLinearMap hpidem_clm
  have hqidem : IsIdempotentElem (q : H →ₗ[ℂ] H) :=
    ContinuousLinearMap.IsIdempotentElem.toLinearMap hqidem_clm
  have horth : (LinearMap.range (p : H →ₗ[ℂ] H))ᗮ = LinearMap.ker (p : H →ₗ[ℂ] H) :=
    hpsym.orthogonal_range
  have hrangeq : LinearMap.range (q : H →ₗ[ℂ] H) = LinearMap.ker (p : H →ₗ[ℂ] H) := by
    rw [LinearMap.IsIdempotentElem.range_eq_ker hqidem]
    congr 1
    ext v
    have : (q : H →ₗ[ℂ] H) v = v - (p : H →ₗ[ℂ] H) v := by
      have := congrArg (fun f : H →L[ℂ] H => f v) hqp
      simpa using this
    simp [LinearMap.mem_ker, LinearMap.sub_apply, this, sub_eq_zero, eq_comm]
  show (E.Hpp)ᗮ = _
  show (LinearMap.range (p : H →ₗ[ℂ] H))ᗮ = _
  rw [horth, ← hrangeq]

/-- Every atom of a diagonal measure lies in the point spectrum: if `a ∉ pointSpectrumSet E` then
`E.diagonalMeasure x` has no mass at `{a}`, for *every* `x`. -/
@[nolint unusedArguments]
theorem diagonalMeasure_singleton_eq_zero_of_notMem_pointSpectrumSet
    {a : ℝ} (ha : a ∉ E.pointSpectrumSet) (x : H) : E.diagonalMeasure x {a} = 0 := by
  rw [pointSpectrumSet, Set.mem_setOf_eq, not_not] at ha
  rw [← E.apply_eq_zero_iff_diagonalMeasure_eq_zero (measurableSet_singleton a) x, ha]
  simp

/-- For `x ∈ Hcont E`, the diagonal measure `E.diagonalMeasure x` vanishes on the whole point
spectrum (not merely at points outside it). -/
theorem diagonalMeasure_pointSpectrumSet_eq_zero_of_mem_H_cont
    {x : H} (hx : x ∈ E.Hcont) : E.diagonalMeasure x E.pointSpectrumSet = 0 := by
  rw [E.H_cont_eq_range_compl] at hx
  obtain ⟨y, hy⟩ := hx
  rw [← E.apply_eq_zero_iff_diagonalMeasure_eq_zero E.measurableSet_pointSpectrumSet x, ← hy]
  have : E E.pointSpectrumSet * E E.pointSpectrumSetᶜ = 0 :=
    E.comp_of_disjoint disjoint_compl_right E.measurableSet_pointSpectrumSet
      E.measurableSet_pointSpectrumSet.compl
  have := congrArg ContinuousLinearMapWOT.toCLM this
  exact congrArg (fun f : H →L[ℂ] H => f y) this

/-- **Phase 2, item 5.** For `x ∈ Hcont E`, `E.diagonalMeasure x` is genuinely atom-free as a
measure on all of `ℝ`, not merely off `pointSpectrumSet E`. -/
theorem diagonalMeasure_nullSingletonClass_of_mem_H_cont {x : H} (hx : x ∈ E.Hcont) :
    NullSingletonClass (E.diagonalMeasure x) where
  measure_singleton a := by
    by_cases ha : a ∈ E.pointSpectrumSet
    · have hle : E.diagonalMeasure x {a} ≤ E.diagonalMeasure x E.pointSpectrumSet :=
        measure_mono (Set.singleton_subset_iff.mpr ha)
      rw [E.diagonalMeasure_pointSpectrumSet_eq_zero_of_mem_H_cont hx] at hle
      exact nonpos_iff_eq_zero.mp hle
    · exact E.diagonalMeasure_singleton_eq_zero_of_notMem_pointSpectrumSet ha x

/-! ## Phase 2, items 6-8 : Lebesgue decomposition of the diagonal measure -/

/-- Restriction of `E.diagonalMeasure` to `Hcont E`, as a subtype. -/
abbrev ContVec := (E.Hcont : Submodule ℂ H)

instance : IsFiniteMeasure (E.diagonalMeasure (0 : H)) := E.diagonalMeasure_isFinite 0

/-- Every vector state of `E` has a Lebesgue decomposition against Lebesgue measure on `ℝ`: this
holds automatically since `E.diagonalMeasure x` is finite and `volume` is `σ`-finite. -/
instance haveLebesgueDecomposition (x : H) :
    (E.diagonalMeasure x).HaveLebesgueDecomposition MeasureTheory.volume :=
  MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite
    (E.diagonalMeasure x) MeasureTheory.volume

/-- A vector of the continuous subspace is *purely absolutely continuous* if its vector-state
measure has no singular part with respect to Lebesgue measure. -/
def IsPureAC (x : E.ContVec) : Prop :=
  (E.diagonalMeasure (x : H)).singularPart MeasureTheory.volume = 0

/-- A vector of the continuous subspace is *purely singular continuous* if its vector-state
measure has no absolutely continuous part with respect to Lebesgue measure (combined with
`diagonalMeasure_nullSingletonClass_of_mem_H_cont`, this makes it honestly singular *continuous*,
not merely singular). -/
def IsPureSC (x : E.ContVec) : Prop :=
  MeasureTheory.volume.withDensity ((E.diagonalMeasure (x : H)).rnDeriv MeasureTheory.volume) = 0

@[nolint unusedArguments]
theorem isPureAC_iff_absolutelyContinuous (x : E.ContVec) :
    E.IsPureAC x ↔ E.diagonalMeasure (x : H) ≪ MeasureTheory.volume :=
  MeasureTheory.Measure.singularPart_eq_zero (E.diagonalMeasure (x : H)) MeasureTheory.volume

@[nolint unusedArguments]
theorem isPureSC_iff_mutuallySingular (x : E.ContVec) :
    E.IsPureSC x ↔ E.diagonalMeasure (x : H) ⟂ₘ MeasureTheory.volume :=
  MeasureTheory.Measure.withDensity_rnDeriv_eq_zero (E.diagonalMeasure (x : H)) MeasureTheory.volume

@[nolint unusedArguments]
private theorem diagonalMeasure_eq_zero : E.diagonalMeasure (0 : H) = 0 := by
  apply MeasureTheory.Measure.ext
  intro S hS
  rw [E.diagonalMeasure_apply 0 S hS]
  simp

theorem isPureAC_zero : E.IsPureAC (0 : E.ContVec) := by
  rw [E.isPureAC_iff_absolutelyContinuous]
  show E.diagonalMeasure ((0 : E.ContVec) : H) ≪ _
  rw [show ((0 : E.ContVec) : H) = (0 : H) from rfl, E.diagonalMeasure_eq_zero]
  exact MeasureTheory.Measure.AbsolutelyContinuous.zero _

theorem isPureAC_add {x y : E.ContVec} (hx : E.IsPureAC x) (hy : E.IsPureAC y) :
    E.IsPureAC (x + y) := by
  rw [E.isPureAC_iff_absolutelyContinuous] at hx hy ⊢
  refine MeasureTheory.Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_
  have hx0 : E.diagonalMeasure (x : H) S = 0 := hx hS0
  have hy0 : E.diagonalMeasure (y : H) S = 0 := hy hS0
  have hEx : E S (x : H) = 0 := (E.apply_eq_zero_iff_diagonalMeasure_eq_zero hS _).mpr hx0
  have hEy : E S (y : H) = 0 := (E.apply_eq_zero_iff_diagonalMeasure_eq_zero hS _).mpr hy0
  have : E S ((x : E.ContVec) + y : H) = 0 := by
    show E S ((x : H) + (y : H)) = 0
    rw [map_add, hEx, hEy, add_zero]
  exact (E.apply_eq_zero_iff_diagonalMeasure_eq_zero hS _).mp (by simpa using this)

theorem isPureAC_smul (c : ℂ) {x : E.ContVec} (hx : E.IsPureAC x) : E.IsPureAC (c • x) := by
  rw [E.isPureAC_iff_absolutelyContinuous] at hx ⊢
  show E.diagonalMeasure ((c • x : E.ContVec) : H) ≪ _
  rw [show ((c • x : E.ContVec) : H) = c • (x : H) from rfl, E.diagonalMeasure_smul]
  exact hx.smul_left _

/-- **Phase 2, item 7 (a.c. case).** The purely absolutely continuous vectors form a submodule of
`Hcont E`. -/
def isPureACSubmodule : Submodule ℂ E.ContVec where
  carrier := {x | E.IsPureAC x}
  zero_mem' := E.isPureAC_zero
  add_mem' := E.isPureAC_add
  smul_mem' c _ hx := E.isPureAC_smul c hx

/-- The pure a.c. subspace of `H` (as a submodule of `H`, via `Hcont E`). -/
def Hac : Submodule ℂ H := (E.isPureACSubmodule).map E.Hcont.subtype

theorem isPureSC_zero : E.IsPureSC (0 : E.ContVec) := by
  rw [E.isPureSC_iff_mutuallySingular]
  show E.diagonalMeasure ((0 : E.ContVec) : H) ⟂ₘ _
  rw [show ((0 : E.ContVec) : H) = (0 : H) from rfl, E.diagonalMeasure_eq_zero]
  exact MeasureTheory.Measure.MutuallySingular.zero_left

theorem isPureSC_add {x y : E.ContVec} (hx : E.IsPureSC x) (hy : E.IsPureSC y) :
    E.IsPureSC (x + y) := by
  rw [E.isPureSC_iff_mutuallySingular] at hx hy ⊢
  set Mx := hx.nullSetᶜ with hMx
  set My := hy.nullSetᶜ with hMy
  have hMxmeas : MeasurableSet Mx := hx.measurableSet_nullSet.compl
  have hMymeas : MeasurableSet My := hy.measurableSet_nullSet.compl
  have hMxvol : MeasureTheory.volume Mx = 0 := hx.measure_compl_nullSet
  have hMyvol : MeasureTheory.volume My = 0 := hy.measure_compl_nullSet
  have hMxsupp : E.diagonalMeasure (x : H) Mxᶜ = 0 := by
    rw [hMx, compl_compl]; exact hx.measure_nullSet
  have hMysupp : E.diagonalMeasure (y : H) Myᶜ = 0 := by
    rw [hMy, compl_compl]; exact hy.measure_nullSet
  set S := Mx ∪ My with hS
  have hSmeas : MeasurableSet S := hMxmeas.union hMymeas
  have hSvol : MeasureTheory.volume S = 0 :=
    le_antisymm ((measure_union_le Mx My).trans_eq (by simp [hMxvol, hMyvol])) bot_le
  have hSc_sub_x : Sᶜ ⊆ Mxᶜ := by rw [hS, Set.compl_union]; exact Set.inter_subset_left
  have hSc_sub_y : Sᶜ ⊆ Myᶜ := by rw [hS, Set.compl_union]; exact Set.inter_subset_right
  have hxSc : E.diagonalMeasure (x : H) Sᶜ = 0 :=
    le_antisymm ((measure_mono hSc_sub_x).trans_eq hMxsupp) bot_le
  have hySc : E.diagonalMeasure (y : H) Sᶜ = 0 :=
    le_antisymm ((measure_mono hSc_sub_y).trans_eq hMysupp) bot_le
  have hScmeas : MeasurableSet Sᶜ := hSmeas.compl
  have hEx : E Sᶜ (x : H) = 0 := (E.apply_eq_zero_iff_diagonalMeasure_eq_zero hScmeas _).mpr hxSc
  have hEy : E Sᶜ (y : H) = 0 := (E.apply_eq_zero_iff_diagonalMeasure_eq_zero hScmeas _).mpr hySc
  have hExy : E Sᶜ ((x : E.ContVec) + y : H) = 0 := by
    show E Sᶜ ((x : H) + (y : H)) = 0
    rw [map_add, hEx, hEy, add_zero]
  have hsum0 : E.diagonalMeasure ((x : E.ContVec) + y : H) Sᶜ = 0 :=
    (E.apply_eq_zero_iff_diagonalMeasure_eq_zero hScmeas _).mp (by simpa using hExy)
  exact MeasureTheory.Measure.MutuallySingular.mk hsum0 hSvol (Set.compl_union_self S).symm.subset

theorem isPureSC_smul (c : ℂ) {x : E.ContVec} (hx : E.IsPureSC x) : E.IsPureSC (c • x) := by
  rw [E.isPureSC_iff_mutuallySingular] at hx ⊢
  show E.diagonalMeasure ((c • x : E.ContVec) : H) ⟂ₘ _
  rw [show ((c • x : E.ContVec) : H) = c • (x : H) from rfl, E.diagonalMeasure_smul]
  exact hx.smul _

/-- **Phase 2, item 7 (s.c. case).** The purely singular continuous vectors form a submodule of
`Hcont E`. -/
def isPureSCSubmodule : Submodule ℂ E.ContVec where
  carrier := {x | E.IsPureSC x}
  zero_mem' := E.isPureSC_zero
  add_mem' := E.isPureSC_add
  smul_mem' c _ hx := E.isPureSC_smul c hx

/-- The pure s.c. subspace of `H` (as a submodule of `H`, via `Hcont E`). -/
def Hsc : Submodule ℂ H := (E.isPureSCSubmodule).map E.Hcont.subtype

/-- **Phase 2, item 8.** `Hac E` and `Hsc E` are orthogonal. -/
theorem H_ac_isOrtho_H_sc : E.Hac ⟂ E.Hsc := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro u ⟨x, hx, rfl⟩ v ⟨y, hy, rfl⟩
  have hx' : E.IsPureAC x := hx
  have hy' : E.IsPureSC y := hy
  rw [E.isPureAC_iff_absolutelyContinuous] at hx'
  rw [E.isPureSC_iff_mutuallySingular] at hy'
  clear hx hy
  set N := hy'.nullSetᶜ with hN
  have hNmeas : MeasurableSet N := hy'.measurableSet_nullSet.compl
  have hNvol : MeasureTheory.volume N = 0 := hy'.measure_compl_nullSet
  have hysupp : E.diagonalMeasure (y : H) Nᶜ = 0 := by
    rw [hN, compl_compl]; exact hy'.measure_nullSet
  have hxN : E.diagonalMeasure (x : H) N = 0 := hx' hNvol
  have hENx : E N (x : H) = 0 := (E.apply_eq_zero_iff_diagonalMeasure_eq_zero hNmeas _).mpr hxN
  have hENcy : E Nᶜ (y : H) = 0 :=
    (E.apply_eq_zero_iff_diagonalMeasure_eq_zero hNmeas.compl _).mpr hysupp
  rw [Submodule.subtype_apply, Submodule.subtype_apply]
  show ⟪(x : H), (y : H)⟫_ℂ = 0
  have hEsum : E N + E Nᶜ = 1 := by
    rw [← E.of_union disjoint_compl_right hNmeas hNmeas.compl]
    simpa using E.univ
  have hxdecomp : (x : H) = E N (x : H) + E Nᶜ (x : H) := by
    have h1 := congrArg ContinuousLinearMapWOT.toCLM hEsum
    have h2 := congrArg (fun f : H →L[ℂ] H => f (x : H)) h1
    simpa using h2.symm
  have hydecomp : (y : H) = E N (y : H) + E Nᶜ (y : H) := by
    have h1 := congrArg ContinuousLinearMapWOT.toCLM hEsum
    have h2 := congrArg (fun f : H →L[ℂ] H => f (y : H)) h1
    simpa using h2.symm
  rw [hxdecomp, hydecomp, hENx, zero_add, hENcy, add_zero]
  exact E.inner_apply_apply_eq_zero_of_disjoint disjoint_compl_right.symm hNmeas.compl hNmeas _ _

/-! ## Phase 3 : completeness of the a.c./s.c. splitting -/

omit [SeparableSpace H] in
/-- **The general restriction identity.** The vector-state measure of `E S x` is exactly the
restriction to `S` of the vector-state measure of `x`. For measurable `T`:
`⟪E S x, E T (E S x)⟫ = ⟪x, (E S * E T * E S) x⟫ = ⟪x, E (T ∩ S) x⟫` using self-adjointness of
`E S` and `comp_eq_of_inter` twice, which matches `(E.diagonalMeasure x).restrict S T =
    E.diagonalMeasure x (T ∩ S)`. -/
lemma diagonalMeasure_apply_eq_restrict (S : Set ℝ) (hS : MeasurableSet S) (x : H) :
    E.diagonalMeasure (E S x) = (E.diagonalMeasure x).restrict S := by
  apply MeasureTheory.Measure.ext
  intro T hT
  rw [MeasureTheory.Measure.restrict_apply hT, E.diagonalMeasure_apply (E S x) T hT,
    E.diagonalMeasure_apply x (T ∩ S) (hT.inter hS)]
  let pS : H →L[ℂ] H := ContinuousLinearMapWOT.toCLM (E S)
  let pT : H →L[ℂ] H := ContinuousLinearMapWOT.toCLM (E T)
  have hstar : ContinuousLinearMap.adjoint pS = pS := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM (E.isStarProjection S).isSelfAdjoint
  have hcomp : pS * pT * pS = ContinuousLinearMapWOT.toCLM (E (T ∩ S)) := by
    have h1 : E S * E T = E (S ∩ T) := E.comp_eq_of_inter hS hT
    have h2 : E (S ∩ T) * E S = E (S ∩ T ∩ S) := E.comp_eq_of_inter (hS.inter hT) hS
    have h3 : S ∩ T ∩ S = T ∩ S := by ext a; simp only [Set.mem_inter_iff]; tauto
    calc pS * pT * pS = ContinuousLinearMapWOT.toCLM (E S * E T * E S) := rfl
      _ = ContinuousLinearMapWOT.toCLM (E S * E T) * pS := rfl
      _ = ContinuousLinearMapWOT.toCLM (E (S ∩ T)) * pS := by rw [h1]
      _ = ContinuousLinearMapWOT.toCLM (E (S ∩ T) * E S) := rfl
      _ = ContinuousLinearMapWOT.toCLM (E (S ∩ T ∩ S)) := by rw [h2]
      _ = ContinuousLinearMapWOT.toCLM (E (T ∩ S)) := by rw [h3]
  have hinner : ⟪E S x, E T (E S x)⟫_ℂ = ⟪x, (E (T ∩ S)) x⟫_ℂ := by
    change ⟪pS x, pT (pS x)⟫_ℂ = ⟪x, ContinuousLinearMapWOT.toCLM (E (T ∩ S)) x⟫_ℂ
    rw [← hcomp]
    calc ⟪pS x, pT (pS x)⟫_ℂ
        = ⟪x, ContinuousLinearMap.adjoint pS (pT (pS x))⟫_ℂ :=
          (ContinuousLinearMap.adjoint_inner_right pS x (pT (pS x))).symm
      _ = ⟪x, pS (pT (pS x))⟫_ℂ := by rw [hstar]
      _ = ⟪x, (pS * pT * pS) x⟫_ℂ := rfl
  rw [hinner]

/-- **`Hcont E` is invariant under every spectral projection.** If `x ∈ Hcont E` then
`E T x ∈ Hcont E` for every measurable `T`. Proof: `x ∈ Hcont E` forces `E S x = 0` where
`S = pointSpectrumSet E` (already available as
`diagonalMeasure_pointSpectrumSet_eq_zero_of_mem_H_cont`), hence `E Sᶜ x = x`; then
`E T x = E T (E Sᶜ x) = E (T ∩ Sᶜ) x`, and applying `E Sᶜ` to this again reproduces
`E (Sᶜ ∩ (T ∩ Sᶜ)) x = E (T ∩ Sᶜ) x = E T x`, so `E T x` is fixed by `E Sᶜ`, i.e. lies in its
range, which is `Hcont E` by `H_cont_eq_range_compl`. -/
theorem apply_mem_H_cont_of_mem_H_cont {T : Set ℝ} (hT : MeasurableSet T) {x : H}
    (hx : x ∈ E.Hcont) : E T x ∈ E.Hcont := by
  set S := E.pointSpectrumSet with hSdef
  have hSmeas : MeasurableSet S := E.measurableSet_pointSpectrumSet
  have hxS0 : E S x = 0 :=
    (E.apply_eq_zero_iff_diagonalMeasure_eq_zero hSmeas x).mpr
      (E.diagonalMeasure_pointSpectrumSet_eq_zero_of_mem_H_cont hx)
  have hEsum : E S + E Sᶜ = 1 := by
    rw [← E.of_union disjoint_compl_right hSmeas hSmeas.compl]
    simpa using E.univ
  have hxSc : E Sᶜ x = x := by
    have h1 := congrArg ContinuousLinearMapWOT.toCLM hEsum
    have h2 := congrArg (fun f : H →L[ℂ] H => f x) h1
    have h3 : E S x + E Sᶜ x = x := by simpa using h2
    rwa [hxS0, zero_add] at h3
  have hET : E T x = E (T ∩ Sᶜ) x := by
    conv_lhs => rw [← hxSc]
    have := E.comp_eq_of_inter hT hSmeas.compl
    exact congrArg (fun f : H →L[ℂ] H => f x) (congrArg ContinuousLinearMapWOT.toCLM this)
  rw [E.H_cont_eq_range_compl]
  refine ⟨E T x, ?_⟩
  show E Sᶜ (E T x) = E T x
  rw [hET]
  have hinter : Sᶜ ∩ (T ∩ Sᶜ) = T ∩ Sᶜ := by
    ext a; simp only [Set.mem_inter_iff]; tauto
  have hcomp := E.comp_eq_of_inter hSmeas.compl (hT.inter hSmeas.compl)
  rw [hinter] at hcomp
  exact congrArg (fun f : H →L[ℂ] H => f x) (congrArg ContinuousLinearMapWOT.toCLM hcomp)

/-- **Completeness of the a.c./s.c. splitting (Reed-Simon Vol. I, Theorem VII.4).** Every vector of
the
continuous subspace decomposes as a sum of a purely absolutely continuous vector and a purely
singular continuous vector: `Hcont E = Hac E ⊔ Hsc E`.

Following M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
Theorem VII.4: for `x ∈ Hcont E`, let `N` be the Lebesgue-decomposition singular support of
`E.diagonalMeasure x` against `volume` (`volume N = 0`, and `E.diagonalMeasure x` restricted to
`Nᶜ` is the a.c. part). Set `x_sc := E N x` and `x_ac := E Nᶜ x`; then `x = x_sc + x_ac`, `x_ac` is
purely a.c. and `x_sc` is purely s.c., by `diagonalMeasure_apply_eq_restrict` together with the
elementary fact that any measure restricted to a `volume`-null set is `⟂ₘ volume`, and that the
a.c. part of a measure restricted to the complement of its own singular support stays `≪ volume`. -/
theorem H_cont_eq_sup_H_ac_H_sc : E.Hcont = E.Hac ⊔ E.Hsc := by
  apply le_antisymm
  · intro x hx
    set h := MeasureTheory.Measure.mutuallySingular_singularPart
      (E.diagonalMeasure x) MeasureTheory.volume with hdef
    -- `h.nullSet` is where `singularPart` vanishes and `volume` is concentrated;
    -- `N := h.nullSetᶜ` is the (Lebesgue-null) set carrying the singular part.
    set N := h.nullSetᶜ with hNdef
    have hNmeas : MeasurableSet N := h.measurableSet_nullSet.compl
    have hNvol : MeasureTheory.volume N = 0 := h.measure_compl_nullSet
    have hNsupp : (E.diagonalMeasure x).singularPart MeasureTheory.volume Nᶜ = 0 := by
      rw [hNdef, compl_compl]; exact h.measure_nullSet
    have hEsum : E N + E Nᶜ = 1 := by
      rw [← E.of_union disjoint_compl_right hNmeas hNmeas.compl]
      simpa using E.univ
    -- (a) `x = E N x + E Nᶜ x`
    have hxdecomp : x = E N x + E Nᶜ x := by
      have h1 := congrArg ContinuousLinearMapWOT.toCLM hEsum
      have h2 := congrArg (fun f : H →L[ℂ] H => f x) h1
      simpa using h2.symm
    -- both halves stay in `Hcont E`, since it is invariant under every spectral projection
    have hNc_mem : E Nᶜ x ∈ E.Hcont := E.apply_mem_H_cont_of_mem_H_cont hNmeas.compl hx
    have hN_mem : E N x ∈ E.Hcont := E.apply_mem_H_cont_of_mem_H_cont hNmeas hx
    set x_ac : E.ContVec := ⟨E Nᶜ x, hNc_mem⟩ with hx_ac_def
    set x_sc : E.ContVec := ⟨E N x, hN_mem⟩ with hx_sc_def
    -- (b) `x_ac = E Nᶜ x` is purely a.c.
    have hac : E.IsPureAC x_ac := by
      rw [E.isPureAC_iff_absolutelyContinuous]
      show E.diagonalMeasure (E Nᶜ x) ≪ MeasureTheory.volume
      rw [E.diagonalMeasure_apply_eq_restrict Nᶜ hNmeas.compl x]
      refine MeasureTheory.Measure.AbsolutelyContinuous.mk fun T hT hT0 => ?_
      rw [MeasureTheory.Measure.restrict_apply hT]
      have hrw : E.diagonalMeasure x =
          (E.diagonalMeasure x).singularPart MeasureTheory.volume +
            MeasureTheory.volume.withDensity
              ((E.diagonalMeasure x).rnDeriv MeasureTheory.volume) :=
        (MeasureTheory.Measure.haveLebesgueDecomposition_add
          (E.diagonalMeasure x) MeasureTheory.volume)
      have hac_part_zero :
          MeasureTheory.volume.withDensity
            ((E.diagonalMeasure x).rnDeriv MeasureTheory.volume) (T ∩ Nᶜ) = 0 := by
        apply MeasureTheory.withDensity_absolutelyContinuous
        exact measure_mono_null Set.inter_subset_left hT0
      have hsing_part_zero :
          (E.diagonalMeasure x).singularPart MeasureTheory.volume (T ∩ Nᶜ) = 0 :=
        measure_mono_null (Set.inter_subset_right) hNsupp
      calc E.diagonalMeasure x (T ∩ Nᶜ)
          = (E.diagonalMeasure x).singularPart MeasureTheory.volume (T ∩ Nᶜ) +
              MeasureTheory.volume.withDensity
                ((E.diagonalMeasure x).rnDeriv MeasureTheory.volume) (T ∩ Nᶜ) := by
            rw [← MeasureTheory.Measure.add_apply, ← hrw]
        _ = 0 := by rw [hsing_part_zero, hac_part_zero, add_zero]
    -- (c) `x_sc = E N x` is purely s.c.
    have hsc : E.IsPureSC x_sc := by
      rw [E.isPureSC_iff_mutuallySingular]
      show E.diagonalMeasure (E N x) ⟂ₘ MeasureTheory.volume
      rw [E.diagonalMeasure_apply_eq_restrict N hNmeas x]
      refine MeasureTheory.Measure.MutuallySingular.mk (s := Nᶜ) (t := N) ?_ hNvol
        (by simp [Set.compl_union_self])
      rw [MeasureTheory.Measure.restrict_apply hNmeas.compl]
      simp
    have hac_mem : E Nᶜ x ∈ E.Hac := Submodule.mem_map.mpr ⟨x_ac, hac, rfl⟩
    have hsc_mem : E N x ∈ E.Hsc := Submodule.mem_map.mpr ⟨x_sc, hsc, rfl⟩
    rw [hxdecomp, add_comm (E N x) (E Nᶜ x)]
    exact Submodule.add_mem_sup hac_mem hsc_mem
  · exact sup_le (E.Hcont.map_subtype_le E.isPureACSubmodule)
      (E.Hcont.map_subtype_le E.isPureSCSubmodule)

end WOTSpectralMeasure
end QuantumMechanics
