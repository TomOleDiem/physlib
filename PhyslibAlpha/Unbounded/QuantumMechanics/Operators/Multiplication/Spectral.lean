/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.Basic
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.Fourier
public import Physlib.QuantumMechanics.Operators.Unbounded
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.Core.UnboundedExtras
public import Physlib.QuantumMechanics.Operators.Multiplication
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.Multiplication.BasicExtras
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.Multiplication.Core
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Affiliation.Concrete
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Spectral.Cayley
public import Physlib.QuantumMechanics.PlanckConstant
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.SpectralTheory.WeakSpectralMeasure

/-!

# Bounded indicator multipliers

The first concrete spectral projections are multiplication by measurable indicators.  This file
packages that operation as a bounded operator on `L²`, with norm at most one.  The construction is
independent of any spectral theorem and is the building block for the position PVM.

-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ComplexOrder InnerProductSpace

namespace QuantumMechanics
namespace SpaceDHilbertSpace

variable {d : ℕ} {μ : Measure (Space d)}

/-- Multiplication by the indicator of a measurable set on `L²(Space d, μ)`. -/
def indicatorCLM (s : Set (Space d)) (hs : MeasurableSet s) :
    SpaceDHilbertSpace d μ →L[ℂ] SpaceDHilbertSpace d μ := by
  let L : SpaceDHilbertSpace d μ →ₗ[ℂ] SpaceDHilbertSpace d μ :=
    { toFun := fun ψ ↦ mk (MemHS.indicator hs (memHS_coe ψ))
      map_add' := by
        intro ψ φ
        rw [← mk_add, mk_eq_iff, ← indicator_add']
        filter_upwards [coeFn_add ψ φ] with x h
        by_cases hx : x ∈ s <;> simp [hx, h]
      map_smul' := by
        intro c ψ
        rw [← mk_const_smul, mk_eq_iff, Pi.smul_def, ← indicator_const_smul]
        filter_upwards [coeFn_smul c ψ] with x h
        by_cases hx : x ∈ s <;> simp [hx, h] }
  have hL : ∀ ψ, ‖L ψ‖ ≤ ‖ψ‖ := by
    intro ψ
    dsimp [L]
    refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top ψ) ?_
    refine (eLpNorm_congr_ae (coeFn_mk _)).trans_le ?_
    exact eLpNorm_indicator_le _
  exact
    { toLinearMap := L
      cont := LinearMap.continuous_iff_bounded.mpr ⟨1, by norm_num, by simpa using hL⟩ }

@[simp]
lemma indicatorCLM_apply_ae (s : Set (Space d)) (hs : MeasurableSet s)
    (ψ : SpaceDHilbertSpace d μ) :
    indicatorCLM s hs ψ =ᵐ[μ] s.indicator ψ := by
  change mk (MemHS.indicator hs (memHS_coe ψ)) =ᵐ[μ] s.indicator ψ
  filter_upwards [coeFn_mk (MemHS.indicator hs (memHS_coe ψ))] with x hx
  simp [hx]

@[simp]
lemma indicatorCLM_zero : indicatorCLM (μ := μ) (∅ : Set (Space d)) MeasurableSet.empty = 0 := by
  apply ContinuousLinearMap.ext
  intro ψ
  simp only [ContinuousLinearMap.zero_apply]
  apply SpaceDHilbertSpace.ext_iff.mpr
  filter_upwards [indicatorCLM_apply_ae (μ := μ) ∅ MeasurableSet.empty ψ, coeFn_zero]
    with x hx hz
  rw [hx]
  simpa only [Set.indicator_empty', Pi.zero_apply] using hz.symm

lemma indicatorCLM_inner (s : Set (Space d)) (hs : MeasurableSet s)
    (x y : SpaceDHilbertSpace d μ) :
    ⟪y, indicatorCLM s hs x⟫_ℂ =
      ∫ z in s, starRingEnd ℂ (y z) * x z ∂μ := by
  obtain ⟨f, hf, hfy⟩ := mk_surjective (ψ := y)
  obtain ⟨g, hg, hgx⟩ := mk_surjective (ψ := indicatorCLM s hs x)
  rw [← hfy, ← hgx, inner_mk_mk, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [coeFn_mk hf, coeFn_mk hg, coeFn_mk (memHS_coe x),
    indicatorCLM_apply_ae s hs x] with z hy hz hx hproj
  by_cases h : z ∈ s
  · simp only [Set.indicator_of_mem h]
    rw [← hy, ← hz, hgx, hproj]
    simp [h]
  · rw [← hy, ← hz, hgx, hproj]
    simp [h]

lemma integrable_inner (x y : SpaceDHilbertSpace d μ) :
    Integrable (fun z => starRingEnd ℂ (y z) * x z) μ := by
  convert MemLp.integrable_mul (p := 2) (q := 2)
    (memHS_coe y).star (memHS_coe x) using 1
  funext z
  rfl

lemma indicatorCLM_idempotent (s : Set (Space d)) (hs : MeasurableSet s) :
    IsIdempotentElem (indicatorCLM (μ := μ) s hs) := by
  apply ContinuousLinearMap.ext
  intro x
  change indicatorCLM s hs (indicatorCLM s hs x) = indicatorCLM s hs x
  apply SpaceDHilbertSpace.ext_iff.mpr
  filter_upwards [indicatorCLM_apply_ae s hs (indicatorCLM s hs x),
    indicatorCLM_apply_ae s hs x] with z hz hzx
  rw [hz, hzx]
  by_cases h : z ∈ s
  · simp [h] at hzx ⊢
    exact hzx
  · simp [h]

lemma indicatorCLM_isSelfAdjoint (s : Set (Space d)) (hs : MeasurableSet s) :
    IsSelfAdjoint (indicatorCLM (μ := μ) s hs) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  rw [← inner_conj_symm]
  change (starRingEnd ℂ) ⟪y, indicatorCLM s hs x⟫_ℂ =
    ⟪x, indicatorCLM s hs y⟫_ℂ
  rw [indicatorCLM_inner, indicatorCLM_inner]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (coeFn_mk (memHS_coe x)),
    ae_restrict_of_ae (coeFn_mk (memHS_coe y))] with z hx hy
  by_cases h : z ∈ s <;> simp [h, hx, hy] <;> ac_rfl

lemma indicatorCLM_univ : indicatorCLM (μ := μ) (Set.univ : Set (Space d))
    MeasurableSet.univ = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply SpaceDHilbertSpace.ext_iff.mpr
  filter_upwards [indicatorCLM_apply_ae Set.univ MeasurableSet.univ x] with z hz
  change ⇑(indicatorCLM Set.univ MeasurableSet.univ x) z = x z
  simpa only [Set.indicator_univ] using hz

end SpaceDHilbertSpace

open ContinuousLinearMap ContinuousLinearMapWOT MeasureTheory Set
open scoped Topology Function

variable {d : ℕ} {μ : Measure (Space d)}

/-- The set function underlying the indicator multiplier measure. -/
noncomputable def indicatorMeasureOf (s : Set (Space d)) :
    SpaceDHilbertSpace d μ →WOT[ℂ] SpaceDHilbertSpace d μ := by
  classical
  exact if hs : MeasurableSet s then
    ContinuousLinearMapWOT.ofCLM (SpaceDHilbertSpace.indicatorCLM s hs) else 0

@[simp]
lemma indicatorMeasureOf_apply (s : Set (Space d)) (hs : MeasurableSet s) :
    indicatorMeasureOf (μ := μ) s =
      ContinuousLinearMapWOT.ofCLM (SpaceDHilbertSpace.indicatorCLM s hs) := by
  classical
  simp [indicatorMeasureOf, hs]

/-- The weak-operator vector measure of measurable indicator multipliers. -/
def indicatorVectorMeasure :
    VectorMeasure (Space d)
      (SpaceDHilbertSpace d μ →WOT[ℂ] SpaceDHilbertSpace d μ) where
  measureOf' := indicatorMeasureOf
  empty' := by
    classical
    simp [indicatorMeasureOf, SpaceDHilbertSpace.indicatorCLM_zero]
  not_measurable' s hs := by
    classical
    simp [indicatorMeasureOf, hs]
  m_iUnion' := by
    classical
    intro f hf hdisj
    have happly (i : ℕ) := indicatorMeasureOf_apply (μ := μ) (f i) (hf i)
    simp_rw [happly,
      indicatorMeasureOf_apply (⋃ i, f i) (MeasurableSet.iUnion hf)]
    apply (ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto).2
    intro x y
    have hi : Integrable (fun z => starRingEnd ℂ (y z) * x z) μ :=
      SpaceDHilbertSpace.integrable_inner x y
    have hs := hasSum_integral_iUnion hf hdisj hi.integrableOn
    have hsum (a : Finset ℕ) :
        ⟪y, (∑ i ∈ a, ContinuousLinearMapWOT.ofCLM
          (SpaceDHilbertSpace.indicatorCLM (μ := μ) (f i) (hf i))) x⟫_ℂ =
          ∑ i ∈ a, ∫ z in f i, starRingEnd ℂ (y z) * x z ∂μ := by
      induction a using Finset.induction_on with
      | empty => simp
      | @insert i a hi' ih =>
        rw [Finset.sum_insert hi']
        change ⟪y, ContinuousLinearMapWOT.ofCLM
            (SpaceDHilbertSpace.indicatorCLM (μ := μ) (f i) (hf i)) x +
            (∑ j ∈ a, ContinuousLinearMapWOT.ofCLM
              (SpaceDHilbertSpace.indicatorCLM (μ := μ) (f j) (hf j))) x⟫_ℂ = _
        rw [inner_add_right]
        rw [Finset.sum_insert hi']
        change ⟪y, SpaceDHilbertSpace.indicatorCLM (μ := μ) (f i) (hf i) x⟫_ℂ +
            ⟪y, (∑ j ∈ a, ContinuousLinearMapWOT.ofCLM
              (SpaceDHilbertSpace.indicatorCLM (μ := μ) (f j) (hf j))) x⟫_ℂ = _
        rw [SpaceDHilbertSpace.indicatorCLM_inner, ih]
    change Filter.Tendsto (fun a : Finset ℕ => ∑ i ∈ a,
      ∫ z in f i, starRingEnd ℂ (y z) * x z ∂μ)
      (SummationFilter.unconditional ℕ).filter
        (𝓝 (∫ z in ⋃ i, f i, starRingEnd ℂ (y z) * x z ∂μ)) at hs
    convert hs using 1
    · funext a
      rw [← hsum]
    · change 𝓝 ⟪y, SpaceDHilbertSpace.indicatorCLM (μ := μ)
        (⋃ i, f i) (MeasurableSet.iUnion hf) x⟫_ℂ = _
      rw [SpaceDHilbertSpace.indicatorCLM_inner]

/-- The position projection-valued measure on `L²(Space d, μ)`. -/
def indicatorSpectralMeasure :
    WOTSpectralMeasure (Space d) (SpaceDHilbertSpace d μ) where
  toVectorMeasure := indicatorVectorMeasure
  isStarProjection' s := by
    classical
    change IsStarProjection (indicatorMeasureOf (μ := μ) s)
    by_cases hs : MeasurableSet s
    · let p := SpaceDHilbertSpace.indicatorCLM (μ := μ) s hs
      rw [indicatorMeasureOf_apply s hs]
      refine ⟨?_, ?_⟩
      · change ContinuousLinearMapWOT.ofCLM p * ContinuousLinearMapWOT.ofCLM p =
          ContinuousLinearMapWOT.ofCLM p
        rw [← ContinuousLinearMapWOT.ofCLM_mul]
        exact congrArg ContinuousLinearMapWOT.ofCLM
          (SpaceDHilbertSpace.indicatorCLM_idempotent s hs)
      · apply ContinuousLinearMapWOT.toCLM_injective
        change star p = p
        exact (SpaceDHilbertSpace.indicatorCLM_isSelfAdjoint s hs)
    · simp [indicatorMeasureOf, hs]
  univ' := by
    change indicatorMeasureOf (μ := μ) Set.univ = 1
    rw [indicatorMeasureOf_apply Set.univ MeasurableSet.univ]
    rw [SpaceDHilbertSpace.indicatorCLM_univ]
    rfl

@[simp]
lemma indicatorSpectralMeasure_apply (s : Set (Space d)) (hs : MeasurableSet s) :
    indicatorSpectralMeasure (μ := μ) s =
      ContinuousLinearMapWOT.ofCLM (SpaceDHilbertSpace.indicatorCLM s hs) := by
  change indicatorMeasureOf (μ := μ) s = _
  rw [indicatorMeasureOf_apply s hs]

lemma indicatorSpectralMeasure_scalarMeasure_eq_withDensity
    (x y : SpaceDHilbertSpace d μ) :
    (indicatorSpectralMeasure (μ := μ)).scalarMeasure x y =
      μ.withDensityᵥ (fun z ↦ starRingEnd ℂ (y z) * x z) := by
  apply VectorMeasure.ext
  intro s hs
  rw [WOTSpectralMeasure.scalarMeasure_apply,
    indicatorSpectralMeasure_apply s hs]
  change ⟪y, SpaceDHilbertSpace.indicatorCLM s hs x⟫_ℂ = _
  rw [SpaceDHilbertSpace.indicatorCLM_inner,
    MeasureTheory.withDensityᵥ_apply (SpaceDHilbertSpace.integrable_inner x y) hs]

lemma indicatorSpectralMeasure_diagonalMeasure_eq_withDensity
    (x : SpaceDHilbertSpace d μ) :
    (indicatorSpectralMeasure (μ := μ)).diagonalMeasure x =
      Measure.withDensity μ (fun z ↦ ENNReal.ofReal (‖x z‖ ^ 2)) := by
  apply Measure.ext
  intro s hs
  rw [(indicatorSpectralMeasure (μ := μ)).diagonalMeasure_apply x s hs,
    indicatorSpectralMeasure_apply s hs]
  change ENNReal.ofReal (⟪x, SpaceDHilbertSpace.indicatorCLM s hs x⟫_ℂ).re = _
  rw [SpaceDHilbertSpace.indicatorCLM_inner]
  rw [MeasureTheory.withDensity_apply _ hs]
  have hq : Integrable
      (fun z ↦ starRingEnd ℂ (x z) * x z) μ := by
    simpa using SpaceDHilbertSpace.integrable_inner x x
  have hqs : Integrable
      (fun z ↦ starRingEnd ℂ (x z) * x z) (μ.restrict s) := hq.integrableOn
  have hre : (∫ z in s, starRingEnd ℂ (x z) * x z ∂μ).re =
      ∫ z in s, (starRingEnd ℂ (x z) * x z).re ∂μ := by
    exact (integral_re hqs).symm
  rw [hre]
  have hreal : Integrable (fun z ↦ ‖x z‖ ^ 2) (μ.restrict s) := by
    convert hqs.norm using 1
    funext z
    simp [norm_mul, pow_two]
  have hre_integral :
      (∫ z in s, (starRingEnd ℂ (x z) * x z).re ∂μ) =
        ∫ z in s, ‖x z‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with z
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.mul_re, Complex.mul_im, RCLike.star_def,
      RCLike.conj_re, RCLike.conj_im, RCLike.ofReal_re, RCLike.ofReal_im]
  rw [hre_integral]
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hreal
    (Filter.Eventually.of_forall (fun z ↦ sq_nonneg ‖x z‖))

/-!
## Real multiplication models

The indicator PVM is a PVM on configuration space.  A real measurable function
`f : Space d → ℝ` turns it into a PVM on the real line by pushforward.  The
corresponding maximal multiplication operator is the canonical source model for
the unbounded spectral theorem.
-/

/-- The maximal multiplication operator associated to a real-valued function. -/
def realMultiplicationOperator (f : Space d → ℝ) :
    SpaceDHilbertSpace d μ →ₗ.[ℂ] SpaceDHilbertSpace d μ :=
  SpaceDHilbertSpace.mulOperator μ (fun x ↦ (f x : ℂ))

/-- The explicit square-integrability domain of a real multiplication operator. -/
def realMultiplicationSquareDomain (f : Space d → ℝ) : Set (SpaceDHilbertSpace d μ) :=
  {x | Integrable (fun z ↦ ‖(f z : ℂ) * x z‖ ^ 2) μ}

lemma realMultiplicationOperator_mem_domain_iff_square
    {f : Space d → ℝ} (hf : Measurable f) (x : SpaceDHilbertSpace d μ) :
    x ∈ (realMultiplicationOperator (μ := μ) f).domain ↔
      x ∈ realMultiplicationSquareDomain (μ := μ) f := by
  change SpaceDHilbertSpace.MemHS
      ((fun z ↦ (f z : ℂ)) • (x : Space d → ℂ)) μ ↔ _
  rw [SpaceDHilbertSpace.memHS_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    exact hf.aemeasurable.complex_ofReal.aestronglyMeasurable.mul
      (SpaceDHilbertSpace.memHS_iff.mp
        (SpaceDHilbertSpace.memHS_coe x)).1

lemma realMultiplicationOperator_domain_eq_squareDomain
    {f : Space d → ℝ} (hf : Measurable f) :
    (realMultiplicationOperator (μ := μ) f).domain =
      realMultiplicationSquareDomain (μ := μ) f := by
  ext x
  exact realMultiplicationOperator_mem_domain_iff_square hf x

/-- The spectral measure of a real multiplication operator, obtained by pushing
the indicator PVM forward along the multiplying function. -/
def multiplicationSpectralMeasure (f : Space d → ℝ) (hf : Measurable f) :
    WOTSpectralMeasure ℝ (SpaceDHilbertSpace d μ) :=
  (indicatorSpectralMeasure (μ := μ)).map f hf

lemma indicatorSpectralMeasure_scalarMeasure_integrable
    {f : Space d → ℝ} (hf : AEStronglyMeasurable f μ)
    (x : SpaceDHilbertSpace d μ) (y : SpaceDHilbertSpace d μ)
    (hprod : Integrable (fun z ↦ (f z : ℂ) *
      (starRingEnd ℂ (y z) * x z)) μ) :
    ((indicatorSpectralMeasure (μ := μ)).scalarMeasure x y).Integrable f := by
  let q : Space d → ℂ := fun z ↦ starRingEnd ℂ (y z) * x z
  have hq : Integrable q μ := by
    simpa [q] using SpaceDHilbertSpace.integrable_inner (x := x) y
  have hq_ae : AEMeasurable (fun z ↦ ‖q z‖ₑ) μ := hq.aestronglyMeasurable.enorm
  have hq_lt : ∀ᵐ z ∂μ, ‖q z‖ₑ < ⊤ := by
    filter_upwards with z
    exact (lt_top_iff_ne_top).2 (show ‖q z‖ₑ ≠ ⊤ from enorm_ne_top)
  rw [indicatorSpectralMeasure_scalarMeasure_eq_withDensity]
  rw [VectorMeasure.Integrable, Measure.variation_withDensityᵥ hq]
  apply (integrable_withDensity_iff_integrable_smul₀' hq_ae hq_lt).2
  have habs : Integrable (fun z ↦ ‖(f z : ℂ) * q z‖) μ := hprod.norm
  have habs' : Integrable (fun z ↦ ‖q z‖ * |f z|) μ := by
    apply habs.congr
    filter_upwards with z
    simp [q, norm_mul, ← ofReal_norm, mul_comm]
  have hsign : Integrable (fun z ↦ ‖q z‖ * f z) μ := by
    apply habs'.congr' (hq.aestronglyMeasurable.norm.mul hf)
    filter_upwards with z
    simp [abs_mul]
  apply hsign.congr
  filter_upwards with z
  simp [toReal_enorm, smul_eq_mul, mul_comm]

lemma multiplicationSpectralMeasure_scalarMeasure_integrable
    {f : Space d → ℝ} (hf : Measurable f)
    (x : (realMultiplicationOperator (μ := μ) f).domain)
    (y : SpaceDHilbertSpace d μ) :
    ((multiplicationSpectralMeasure (μ := μ) f hf).scalarMeasure
      (x : SpaceDHilbertSpace d μ) y).Integrable id := by
  let q : Space d → ℂ := fun z ↦ starRingEnd ℂ (y z) * (x : SpaceDHilbertSpace d μ) z
  have hq : Integrable q μ := by
    simpa [q] using SpaceDHilbertSpace.integrable_inner (x := (x : SpaceDHilbertSpace d μ)) y
  have hq_ae : AEMeasurable (fun z ↦ ‖q z‖ₑ) μ :=
    hq.aestronglyMeasurable.enorm
  have hq_lt : ∀ᵐ z ∂μ, ‖q z‖ₑ < ⊤ := by
    filter_upwards with z
    exact (lt_top_iff_ne_top).2 (show ‖q z‖ₑ ≠ ⊤ from enorm_ne_top)
  have hprod : Integrable (fun z ↦ (f z : ℂ) * q z) μ := by
    have htx : Integrable
        (fun z ↦ starRingEnd ℂ (y z) *
          (realMultiplicationOperator (μ := μ) f x) z) μ :=
      SpaceDHilbertSpace.integrable_inner (realMultiplicationOperator (μ := μ) f x) y
    apply htx.congr' (by fun_prop)
    filter_upwards [SpaceDHilbertSpace.mulOperator_apply_ae x] with z hz
    simp [q, realMultiplicationOperator, hz, smul_eq_mul, mul_assoc, norm_mul]
    ring
  have hbase :
      ((indicatorSpectralMeasure (μ := μ)).scalarMeasure
        (x : SpaceDHilbertSpace d μ) y).Integrable f := by
    rw [indicatorSpectralMeasure_scalarMeasure_eq_withDensity]
    rw [VectorMeasure.Integrable, Measure.variation_withDensityᵥ hq]
    apply (integrable_withDensity_iff_integrable_smul₀' hq_ae hq_lt).2
    have habs : Integrable (fun z ↦ ‖(f z : ℂ) * q z‖) μ := hprod.norm
    have habs' : Integrable (fun z ↦ ‖q z‖ * |f z|) μ := by
      apply habs.congr
      filter_upwards with z
      simp [q, norm_mul, ← ofReal_norm, mul_comm]
    have hsign : Integrable (fun z ↦ ‖q z‖ * f z) μ := by
      apply habs'.congr' (by fun_prop)
      filter_upwards with z
      simp [abs_mul]
    apply hsign.congr
    filter_upwards with z
    simp [toReal_enorm, smul_eq_mul, mul_comm]
  change (((indicatorSpectralMeasure (μ := μ)).map f hf).scalarMeasure
      (x : SpaceDHilbertSpace d μ) y).Integrable id
  rw [WOTSpectralMeasure.scalarMeasure_map]
  exact VectorMeasure.Integrable.map measurable_id.aestronglyMeasurable hbase

/-! ### The square-moment domain in the multiplication model -/

lemma realMultiplicationOperator_domain_subset_spectralSquareMomentDomain
    [IsFiniteMeasureOnCompacts μ] {f : Space d → ℝ} (hf : Measurable f)
    (x : (realMultiplicationOperator (μ := μ) f).domain) :
    (x : SpaceDHilbertSpace d μ) ∈
      OperatorAlgebra.spectralSquareMomentDomain
        (multiplicationSpectralMeasure (μ := μ) f hf) := by
  apply (OperatorAlgebra.mem_spectralSquareMomentDomain_iff
    (multiplicationSpectralMeasure (μ := μ) f hf) (x : SpaceDHilbertSpace d μ)).2
  simp only [multiplicationSpectralMeasure]
  rw [(indicatorSpectralMeasure (μ := μ)).diagonalMeasure_map f hf
      (x : SpaceDHilbertSpace d μ)]
  apply (integrable_map_measure (μ :=
    (indicatorSpectralMeasure (μ := μ)).diagonalMeasure
      (x : SpaceDHilbertSpace d μ)) (by fun_prop) hf.aemeasurable).2
  rw [indicatorSpectralMeasure_diagonalMeasure_eq_withDensity]
  have hxmeas : AEMeasurable
      (fun z ↦ ENNReal.ofReal (‖(x : SpaceDHilbertSpace d μ) z‖ ^ 2)) μ := by
    have hxmeas' : AEStronglyMeasurable
        (fun z ↦ (x : SpaceDHilbertSpace d μ) z) μ :=
      (SpaceDHilbertSpace.memHS_iff.mp
        (SpaceDHilbertSpace.memHS_coe (x : SpaceDHilbertSpace d μ))).1
    exact (hxmeas'.norm.pow 2).aemeasurable.ennreal_ofReal
  rw [integrable_withDensity_iff_integrable_smul₀' hxmeas
    (Filter.Eventually.of_forall (fun z ↦ ENNReal.ofReal_lt_top))]
  have hxmem : SpaceDHilbertSpace.MemHS
      ((fun z ↦ (f z : ℂ)) • ⇑(x : SpaceDHilbertSpace d μ)) μ := x.property
  have hnorm : Integrable
      (fun z ↦ ‖((f z : ℂ) * (x : SpaceDHilbertSpace d μ) z)‖ ^ 2) μ := by
    simpa [Pi.smul_apply, smul_eq_mul] using (SpaceDHilbertSpace.memHS_iff.mp hxmem).2
  apply hnorm.congr
  filter_upwards with z
  simp [norm_mul, pow_two, sq_abs]
  ring_nf
  rw [sq_abs]
  ring

lemma spectralSquareMomentDomain_subset_realMultiplicationOperator_domain
    [IsFiniteMeasureOnCompacts μ] {f : Space d → ℝ} (hf : Measurable f)
    {x : SpaceDHilbertSpace d μ}
    (hx : x ∈ OperatorAlgebra.spectralSquareMomentDomain
      (multiplicationSpectralMeasure (μ := μ) f hf)) :
    x ∈ (realMultiplicationOperator (μ := μ) f).domain := by
  apply (realMultiplicationOperator_mem_domain_iff_square hf x).2
  change Integrable (fun z ↦ ‖(f z : ℂ) * x z‖ ^ 2) μ
  have hx' : Integrable (fun r : ℝ ↦ r ^ 2)
      ((multiplicationSpectralMeasure (μ := μ) f hf).diagonalMeasure x) :=
    (OperatorAlgebra.mem_spectralSquareMomentDomain_iff
      (multiplicationSpectralMeasure (μ := μ) f hf) x).1 hx
  have hxmap : Integrable (fun r : ℝ ↦ r ^ 2)
      (Measure.map f ((indicatorSpectralMeasure (μ := μ)).diagonalMeasure x)) := by
    simpa [multiplicationSpectralMeasure,
      (indicatorSpectralMeasure (μ := μ)).diagonalMeasure_map f hf x] using hx'
  have hbase : Integrable (fun z ↦ f z ^ 2)
      ((indicatorSpectralMeasure (μ := μ)).diagonalMeasure x) := by
    have h := (integrable_map_measure
      (μ := (indicatorSpectralMeasure (μ := μ)).diagonalMeasure x)
      (f := f) (g := fun r : ℝ ↦ r ^ 2) (by fun_prop) hf.aemeasurable).1 hxmap
    simpa [Function.comp_def] using h
  rw [indicatorSpectralMeasure_diagonalMeasure_eq_withDensity] at hbase
  have hweight : Integrable (fun z ↦ f z ^ 2 * ‖x z‖ ^ 2) μ := by
    have hxmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (‖x z‖ ^ 2)) μ := by
      have hxmeas' : AEStronglyMeasurable (fun z ↦ x z) μ :=
        (SpaceDHilbertSpace.memHS_iff.mp
          (SpaceDHilbertSpace.memHS_coe x)).1
      exact (hxmeas'.norm.pow 2).aemeasurable.ennreal_ofReal
    have h := (integrable_withDensity_iff_integrable_smul₀'
      (μ := μ) (f := fun z ↦ ENNReal.ofReal (‖x z‖ ^ 2)) hxmeas
      (Filter.Eventually.of_forall (fun z ↦ ENNReal.ofReal_lt_top))).1 hbase
    simpa [mul_comm] using h
  apply hweight.congr
  filter_upwards with z
  simp [norm_mul, pow_two, sq_abs]
  ring_nf
  rw [sq_abs]
  ring

lemma realMultiplicationOperator_domain_eq_spectralSquareMomentDomain
    [IsFiniteMeasureOnCompacts μ] {f : Space d → ℝ} (hf : Measurable f) :
    (realMultiplicationOperator (μ := μ) f).domain =
      (OperatorAlgebra.spectralSquareMomentDomain
        (multiplicationSpectralMeasure (μ := μ) f hf) :
        Set (SpaceDHilbertSpace d μ)) := by
  ext x
  constructor
  · intro hx
    exact realMultiplicationOperator_domain_subset_spectralSquareMomentDomain
      hf ⟨x, hx⟩
  · intro hx
    exact spectralSquareMomentDomain_subset_realMultiplicationOperator_domain
      hf hx

/-!
The following lemma is the vector-valued density formula needed by the weak unbounded integral.
It is deliberately stated independently of `L²`: it is the reusable measure-theoretic fact that
integrating a real function against the vector measure with density `q` agrees with the Bochner
integral of its pointwise scalar multiple.
-/

lemma integral_smul_withDensityᵥ_integrable
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {ν : Measure α} {q : α → E} (hq : Integrable q ν)
    {g : α → ℝ} (hg : Integrable g (ν.withDensity (fun x ↦ ‖q x‖ₑ))) :
    (ν.withDensityᵥ q).Integrable g ∧ Integrable (fun x ↦ g x • q x) ν := by
  have hq_ae : AEMeasurable (fun x ↦ ‖q x‖ₑ) ν := hq.aestronglyMeasurable.enorm
  have hq_lt : ∀ᵐ x ∂ν, ‖q x‖ₑ < ⊤ := by
    filter_upwards with x
    exact (lt_top_iff_ne_top).2 (show ‖q x‖ₑ ≠ ⊤ from enorm_ne_top)
  have hnorm : Integrable (fun x ↦ (‖q x‖ₑ).toReal • g x) ν :=
    (integrable_withDensity_iff_integrable_smul₀' hq_ae hq_lt).1 hg
  have hq_meas : AEStronglyMeasurable q ν := hq.aestronglyMeasurable
  have hq_norm_meas : AEStronglyMeasurable (fun x ↦ ‖q x‖) ν := hq_meas.norm
  have hq_norm_inv_meas : AEStronglyMeasurable (fun x ↦ (‖q x‖ : ℝ)⁻¹) ν :=
    hq_norm_meas.inv₀
  let u : α → E := fun x ↦ (‖q x‖ : ℝ)⁻¹ • q x
  have hu : AEStronglyMeasurable u ν := by
    exact hq_norm_inv_meas.smul hq_meas
  have hnorm_u : ∀ᵐ x ∂ν, ‖u x‖ ≤ 1 := by
    filter_upwards with x
    by_cases hx : q x = 0
    · simp [u, hx]
    · simp only [u, norm_smul, norm_inv]
      have hxn : ‖q x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      rw [Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hx), inv_mul_cancel₀ hxn]
  have htarget_meas : AEStronglyMeasurable (fun x ↦ g x • q x) ν := by
    have hg' : AEStronglyMeasurable
        (fun x ↦ (‖q x‖ₑ).toReal • g x) ν := hnorm.aestronglyMeasurable
    have htarget' : AEStronglyMeasurable
        (fun x ↦ ((‖q x‖ₑ).toReal • g x) • u x) ν := hg'.smul hu
    apply htarget'.congr
    filter_upwards with x
    by_cases hx : q x = 0
    · simp [u, hx]
    · dsimp [u]
      rw [show (‖q x‖ₑ).toReal = ‖q x‖ by simp [enorm_eq_nnnorm]]
      rw [smul_smul]
      have hxn : ‖q x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hs : ‖q x‖ * g x * ‖q x‖⁻¹ = g x := by
        field_simp
      rw [hs]
  have htarget : Integrable (fun x ↦ g x • q x) ν := by
    apply hnorm.norm.mono' htarget_meas
    filter_upwards [hnorm_u] with x hx
    rw [show g x • q x = ((‖q x‖ₑ).toReal • g x) • u x by
      by_cases hqx : q x = 0
      · simp [hqx, u]
      · dsimp [u]
        rw [show (‖q x‖ₑ).toReal = ‖q x‖ by simp [enorm_eq_nnnorm]]
        rw [smul_smul]
        have hxn : ‖q x‖ ≠ 0 := norm_ne_zero_iff.mpr hqx
        have hs : ‖q x‖ * g x * ‖q x‖⁻¹ = g x := by
          field_simp
        rw [hs]]
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) hx
  refine ⟨?_, htarget⟩
  rw [VectorMeasure.Integrable, Measure.variation_withDensityᵥ hq]
  exact hg

set_option maxHeartbeats 1000000 in
lemma integral_smul_withDensityᵥ
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {ν : Measure α} {q : α → E} (hq : Integrable q ν)
    {g : α → ℝ} (hg : Integrable g (ν.withDensity (fun x ↦ ‖q x‖ₑ))) :
    ∫ᵛ x, g x ∂• ν.withDensityᵥ q = ∫ x, g x • q x ∂ν := by
  have bridge : ∀ {k : α → ℝ}, Integrable k (ν.withDensity (fun x ↦ ‖q x‖ₑ)) →
      (ν.withDensityᵥ q).Integrable k ∧ Integrable (fun x ↦ k x • q x) ν := by
    intro k hk
    exact integral_smul_withDensityᵥ_integrable hq hk
  have hν : (ν.withDensityᵥ q).Integrable g := (bridge hg).1
  apply hg.induction (P := fun g ↦
    ∫ᵛ x, g x ∂• ν.withDensityᵥ q = ∫ x, g x • q x ∂ν)
  · intro c s hs hμs
    have hνs : IsFiniteMeasure ((ν.withDensityᵥ q).variation.restrict s) := by
      rw [Measure.variation_withDensityᵥ hq]
      exact MeasureTheory.isFiniteMeasure_restrict.mpr hμs.ne
    letI := hνs
    rw [VectorMeasure.integral_indicator_const c hs]
    have hfun : (fun x ↦ s.indicator (fun _ ↦ c) x • q x) =
        s.indicator (fun x ↦ c • q x) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hfun, integral_indicator hs]
    have hsmul : (∫ x in s, c • q x ∂ν) = c • ∫ x in s, q x ∂ν := by
      change (∫ x, c • q x ∂(ν.restrict s)) = c • ∫ x, q x ∂(ν.restrict s)
      exact integral_smul c q
    rw [hsmul]
    rw [withDensityᵥ_apply hq hs]
    rfl
  · intro f h disj hf hg' hfP hgP
    have hνf := (bridge hf).1
    have hνg := (bridge hg').1
    change (∫ᵛ x, f x + h x ∂•ν.withDensityᵥ q) =
      ∫ x, (f x + h x) • q x ∂ν
    rw [VectorMeasure.integral_fun_add (μ := ν.withDensityᵥ q) hνf hνg]
    simp_rw [add_smul]
    rw [integral_add (bridge hf).2 (bridge hg').2, hfP, hgP]
  · apply isClosed_eq
    · have hleft := MeasureTheory.VectorMeasure.continuous_integral
          (μ := ν.withDensityᵥ q) (B := ContinuousLinearMap.lsmul ℝ ℝ)
      rw [Measure.variation_withDensityᵥ hq] at hleft
      exact hleft
    · have hLip : LipschitzWith 1
          (fun y : (Lp ℝ 1 (ν.withDensity (fun x ↦ ‖q x‖ₑ))) ↦
            ∫ x, y x • q x ∂ν) := by
        rw [lipschitzWith_iff_dist_le_mul]
        intro f k
        have hf := (bridge (L1.integrable_coeFn f)).2
        have hk := (bridge (L1.integrable_coeFn k)).2
        have hdist := MeasureTheory.dist_integral_le_lintegral_edist hf hk
        calc
          dist (∫ x, f x • q x ∂ν) (∫ x, k x • q x ∂ν) ≤
              (∫⁻ x, edist (f x • q x) (k x • q x) ∂ν).toReal := hdist
          _ = (∫⁻ x, ‖f x - k x‖ₑ ∂ν.withDensity (fun x ↦ ‖q x‖ₑ)).toReal := by
            congr 1
            rw [lintegral_withDensity_eq_lintegral_mul₀' hq.aestronglyMeasurable.enorm]
            · apply lintegral_congr_ae
              filter_upwards with x
              rw [edist_dist, dist_eq_norm, ← sub_smul]
              simp [enorm_eq_nnnorm, norm_smul, abs_mul, mul_comm, ← Real.norm_eq_abs,
                ofReal_norm]
            · exact (Lp.aestronglyMeasurable f).sub (Lp.aestronglyMeasurable k) |>.enorm
          _ = (1 : ℝ) * dist f k := by
            have he : eLpNorm (fun x ↦ f x - k x) 1
                (ν.withDensity (fun x ↦ ‖q x‖ₑ)) =
                eLpNorm (⇑(f - k)) 1 (ν.withDensity (fun x ↦ ‖q x‖ₑ)) :=
              eLpNorm_congr_ae (Lp.coeFn_sub f k).symm
            rw [← eLpNorm_one_eq_lintegral_enorm, he, Lp.dist_def]
            rw [eLpNorm_congr_ae (Lp.coeFn_sub f k)]
            simp
      simpa using hLip.continuous
  · intro f g hfg hf hfP
    have hfg' : ∀ᵐ x ∂ν, ‖q x‖ₑ ≠ 0 → f x = g x :=
      (ae_withDensity_iff' hq.aestronglyMeasurable.enorm).1 hfg
    have hfgq : (fun x ↦ f x • q x) =ᵐ[ν] (fun x ↦ g x • q x) := by
      filter_upwards [hfg'] with x hx
      by_cases hqx : q x = 0
      · simp [hqx]
      · rw [hx (by simp [hqx])]
    have hvar : (ν.withDensityᵥ q).variation =
        ν.withDensity (fun x ↦ ‖q x‖ₑ) := Measure.variation_withDensityᵥ hq
    have hfgv : f =ᵐ[(ν.withDensityᵥ q).variation] g := by
      rw [hvar]
      exact hfg
    have hleft : (∫ᵛ x, f x ∂•ν.withDensityᵥ q) =
        ∫ᵛ x, g x ∂•ν.withDensityᵥ q :=
      VectorMeasure.integral_congr_ae (μ := ν.withDensityᵥ q)
        (B := ContinuousLinearMap.lsmul ℝ ℝ) hfgv
    rw [← hleft]
    rw [hfP, integral_congr_ae hfgq]

lemma realMultiplicationOperator_weakSpectralReconstruction
    [IsFiniteMeasureOnCompacts μ] {f : Space d → ℝ} (hf : Measurable f)
    (x : (realMultiplicationOperator (μ := μ) f).domain)
    (y : SpaceDHilbertSpace d μ) :
    ⟪y, realMultiplicationOperator (μ := μ) f x⟫_ℂ =
      (multiplicationSpectralMeasure (μ := μ) f hf).weakIntegral
        id (x : SpaceDHilbertSpace d μ) y := by
  let q : Space d → ℂ := fun z ↦ starRingEnd ℂ (y z) * (x : SpaceDHilbertSpace d μ) z
  have hq : Integrable q μ := by
    simpa [q] using SpaceDHilbertSpace.integrable_inner (x := (x : SpaceDHilbertSpace d μ)) y
  have hprod : Integrable (fun z ↦ (f z : ℂ) * q z) μ := by
    have htx : Integrable
        (fun z ↦ starRingEnd ℂ (y z) *
          (realMultiplicationOperator (μ := μ) f x) z) μ :=
      SpaceDHilbertSpace.integrable_inner (realMultiplicationOperator (μ := μ) f x) y
    apply htx.congr' (by fun_prop)
    filter_upwards [SpaceDHilbertSpace.mulOperator_apply_ae x] with z hz
    simp [q, realMultiplicationOperator, hz, smul_eq_mul]
    ring
  have hbase :
      ((indicatorSpectralMeasure (μ := μ)).scalarMeasure
        (x : SpaceDHilbertSpace d μ) y).Integrable f := by
    apply indicatorSpectralMeasure_scalarMeasure_integrable hf.aestronglyMeasurable
      (x : SpaceDHilbertSpace d μ) y
    simpa [q] using hprod
  have hfdens : Integrable f (μ.withDensity (fun z ↦ ‖q z‖ₑ)) := by
    have hbase' := hbase
    rw [indicatorSpectralMeasure_scalarMeasure_eq_withDensity] at hbase'
    rw [VectorMeasure.Integrable, Measure.variation_withDensityᵥ hq] at hbase'
    exact hbase'
  have hmap := WOTSpectralMeasure.weakIntegral_map
    (μS := indicatorSpectralMeasure (μ := μ)) f hf id
    (x : SpaceDHilbertSpace d μ) y measurable_id.aestronglyMeasurable hbase
  change ⟪y, realMultiplicationOperator (μ := μ) f x⟫_ℂ =
    ((indicatorSpectralMeasure (μ := μ)).map f hf).weakIntegral
      id (x : SpaceDHilbertSpace d μ) y
  rw [hmap]
  unfold WOTSpectralMeasure.weakIntegral
  rw [indicatorSpectralMeasure_scalarMeasure_eq_withDensity]
  have hfdens' : Integrable (id ∘ f) (μ.withDensity (fun z ↦ ‖q z‖ₑ)) := by
    simpa [Function.comp_def] using hfdens
  rw [integral_smul_withDensityᵥ hq hfdens']
  obtain ⟨a, ha, hax⟩ := SpaceDHilbertSpace.mk_surjective
    (ψ := realMultiplicationOperator (μ := μ) f x)
  obtain ⟨b, hb, hby⟩ := SpaceDHilbertSpace.mk_surjective (ψ := y)
  rw [← hby, ← hax, SpaceDHilbertSpace.inner_mk_mk]
  apply integral_congr_ae
  filter_upwards [SpaceDHilbertSpace.coeFn_mk ha, SpaceDHilbertSpace.coeFn_mk hb,
    SpaceDHilbertSpace.mulOperator_apply_ae x] with z hza hzb hzx
  have hza' := hza
  have hzb' := hzb
  rw [hax] at hza'
  rw [hby] at hzb'
  rw [← hza', ← hzb']
  simp only [realMultiplicationOperator] at hzx ⊢
  rw [hzx]
  simp [q, smul_eq_mul]
  ring

lemma realMultiplicationOperator_isSelfAdjoint
    [IsFiniteMeasureOnCompacts μ] (f : Space d → ℝ) (hf : AEStronglyMeasurable f μ) :
    IsSelfAdjoint (realMultiplicationOperator (μ := μ) f) := by
  apply SpaceDHilbertSpace.mulOperator_isSelfAdjoint_ofReal
  · exact hf.aemeasurable.complex_ofReal.aestronglyMeasurable
  · funext x
    simp [realMultiplicationOperator]

lemma realMultiplicationOperator_selfAdjointSpectralTheorem
    [IsFiniteMeasureOnCompacts μ] {f : Space d → ℝ} (hf : Measurable f) :
    OperatorAlgebra.SelfAdjointSpectralTheorem
      (realMultiplicationOperator (μ := μ) f)
      (multiplicationSpectralMeasure (μ := μ) f hf) where
  isSelfAdjoint := realMultiplicationOperator_isSelfAdjoint f hf.aestronglyMeasurable
  reconstruction := by
    intro x
    refine ⟨?_, ?_⟩
    · intro y
      exact multiplicationSpectralMeasure_scalarMeasure_integrable hf x y
    · intro y
      exact realMultiplicationOperator_weakSpectralReconstruction hf x y

/- The multiplication model carries the full domain-aware spectral theorem: its maximal
operator domain is exactly the finite second moment domain of its pushed-forward PVM. -/
def realMultiplicationOperatorDomainAwareSelfAdjointSpectralTheorem
    [IsFiniteMeasureOnCompacts μ] {f : Space d → ℝ} (hf : Measurable f) :
    OperatorAlgebra.DomainAwareSelfAdjointSpectralTheorem
      (realMultiplicationOperator (μ := μ) f)
      (multiplicationSpectralMeasure (μ := μ) f hf) where
  toSelfAdjointSpectralTheorem :=
    realMultiplicationOperator_selfAdjointSpectralTheorem hf
  domain_eq_squareMoment :=
    realMultiplicationOperator_domain_eq_spectralSquareMomentDomain hf

/-- The bounded-unitary spectral measure obtained from the multiplication model by Cayley
transforming its real spectral variable. -/
def realMultiplicationCayleySpectralMeasure
    {f : Space d → ℝ} (hf : Measurable f) :
    WOTSpectralMeasure ℂ (SpaceDHilbertSpace d μ) :=
  WOTSpectralMeasure.cayleyMap
    (multiplicationSpectralMeasure (μ := μ) f hf)

lemma realMultiplicationCayleySpectralMeasure_inverse
    {f : Space d → ℝ} (hf : Measurable f) :
    WOTSpectralMeasure.cayleyInverseMap
      (realMultiplicationCayleySpectralMeasure (μ := μ) hf) =
      multiplicationSpectralMeasure (μ := μ) f hf := by
  exact WOTSpectralMeasure.cayleyInverseMap_cayleyMap _

/-- The multiplication spectral theorem can be recovered from the bounded Cayley-side measure.
The inverse Cayley map is the unbounded spectral variable; the round-trip theorem is what makes
the point at `1` (the point at infinity) harmless for a real spectral measure. -/
lemma realMultiplicationOperator_selfAdjointSpectralTheorem_viaCayley
    [IsFiniteMeasureOnCompacts μ] {f : Space d → ℝ} (hf : Measurable f) :
    OperatorAlgebra.SelfAdjointSpectralTheorem
      (realMultiplicationOperator (μ := μ) f)
      (WOTSpectralMeasure.cayleyInverseMap
        (realMultiplicationCayleySpectralMeasure (μ := μ) hf)) := by
  rw [realMultiplicationCayleySpectralMeasure_inverse hf]
  exact realMultiplicationOperator_selfAdjointSpectralTheorem hf

lemma realMultiplicationOperator_isEssentiallySelfAdjoint
    [IsFiniteMeasureOnCompacts μ] (f : Space d → ℝ) (hf : AEStronglyMeasurable f μ) :
    (realMultiplicationOperator (μ := μ) f).IsEssentiallySelfAdjoint := by
  apply SpaceDHilbertSpace.mulOperator_isEssentiallySelfAdjoint
  · exact hf.aemeasurable.complex_ofReal.aestronglyMeasurable
  · funext x
    simp [realMultiplicationOperator]

lemma realMultiplicationOperator_closure_eq
    [IsFiniteMeasureOnCompacts μ] (f : Space d → ℝ) (hf : AEStronglyMeasurable f μ) :
    (realMultiplicationOperator (μ := μ) f).closure =
      realMultiplicationOperator (μ := μ) f := by
  apply SpaceDHilbertSpace.mulOperator_closure_eq
  · exact hf.aemeasurable.complex_ofReal.aestronglyMeasurable
  · funext x
    simp [realMultiplicationOperator]

/-- All reusable analytic data for the maximal real multiplication operator in one package. -/
def realMultiplicationOperatorSpectralData
    [IsFiniteMeasureOnCompacts μ] {f : Space d → ℝ} (hf : Measurable f) :
    OperatorAlgebra.EssentialSelfAdjointSpectralData
      (realMultiplicationOperator (μ := μ) f) where
  essentiallySelfAdjoint :=
    realMultiplicationOperator_isEssentiallySelfAdjoint f hf.aestronglyMeasurable
  spectralMeasure := multiplicationSpectralMeasure (μ := μ) f hf
  spectralTheorem := by
    rw [realMultiplicationOperator_closure_eq (μ := μ) f hf.aestronglyMeasurable]
    exact realMultiplicationOperatorDomainAwareSelfAdjointSpectralTheorem (μ := μ) hf

/-!
### Momentum as a transported multiplication operator

The old `momentumOperator` is the Schwartz-core differential expression
`-iℏ ∂ᵢ`.  Its maximal self-adjoint realization is most naturally constructed
in Fourier representation, where it is multiplication by the real momentum
coordinate `2πℏ pᵢ`.  The Fourier conjugation below deliberately does not assert
that the two operators are equal yet; that equality is the core/closure theorem
which identifies the existing differential operator with this realization.
-/

/-- The real physical momentum coordinate in Fourier representation.

The Fourier convention used by Mathlib is `exp (-2π i x p)`, hence the physical
momentum is `2πℏ p`, not merely `ℏ p`. -/
def momentumCoordinate (i : Fin d) : Space d → ℝ :=
  fun p ↦ (2 * Real.pi * (Constants.ℏ : ℝ)) * Space.coord i p

lemma momentumCoordinate_measurable (i : Fin d) :
    Measurable (momentumCoordinate i) := by
  unfold momentumCoordinate
  apply Measurable.mul measurable_const
  change Measurable (fun p : Space d ↦ Space.coord i p)
  have hcoord : (fun p : Space d ↦ Space.coord i p) = ⇑(Space.coordCLM i) := by
    funext p
    exact (Space.coordCLM_apply i p).symm
  rw [hcoord]
  exact (Space.coordCLM i).continuous.measurable

/-- The maximal momentum operator obtained by Fourier-conjugating multiplication by `ℏ pᵢ`. -/
def fourierMomentumOperator (i : Fin d) :
    SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d :=
  LinearPMap.unitaryConj (SpaceDHilbertSpace.fourierUnitary d).symm
    (realMultiplicationOperator (μ := volume) (momentumCoordinate i))

/-- The PVM candidate for the Fourier-conjugated maximal momentum operator. -/
def fourierMomentumSpectralMeasure (i : Fin d) :
    WOTSpectralMeasure ℝ (SpaceDHilbertSpace d) :=
  WOTSpectralMeasure.unitaryConjSpectralMeasure
    (SpaceDHilbertSpace.fourierUnitary d).symm
    (multiplicationSpectralMeasure (μ := volume) (momentumCoordinate i)
      (momentumCoordinate_measurable i))

lemma fourierMomentumOperator_isSelfAdjoint [IsFiniteMeasureOnCompacts (volume : Measure (Space d))]
    (i : Fin d) :
    IsSelfAdjoint (fourierMomentumOperator i) := by
  apply LinearPMap.unitaryConj_isSelfAdjoint
  apply realMultiplicationOperator_isSelfAdjoint
  exact (momentumCoordinate_measurable i).aestronglyMeasurable

lemma fourierMomentumOperator_selfAdjointSpectralTheorem
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    OperatorAlgebra.SelfAdjointSpectralTheorem
      (fourierMomentumOperator i) (fourierMomentumSpectralMeasure i) := by
  exact (realMultiplicationOperator_selfAdjointSpectralTheorem
    (μ := volume) (momentumCoordinate_measurable i)).unitaryConj
    (SpaceDHilbertSpace.fourierUnitary d).symm

lemma fourierMomentumOperator_domainAwareSelfAdjointSpectralTheorem
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    OperatorAlgebra.DomainAwareSelfAdjointSpectralTheorem
      (fourierMomentumOperator i) (fourierMomentumSpectralMeasure i) := by
  exact (realMultiplicationOperatorDomainAwareSelfAdjointSpectralTheorem
    (μ := volume) (momentumCoordinate_measurable i)).unitaryConj
    (SpaceDHilbertSpace.fourierUnitary d).symm

lemma fourierMomentumOperator_isEssentiallySelfAdjoint
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    (fourierMomentumOperator i).IsEssentiallySelfAdjoint := by
  exact LinearPMap.IsSelfAdjoint.isEssentiallySelfAdjoint
    (fourierMomentumOperator_isSelfAdjoint i)

def fourierMomentumOperatorSpectralData
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    OperatorAlgebra.EssentialSelfAdjointSpectralData (fourierMomentumOperator i) where
  essentiallySelfAdjoint := fourierMomentumOperator_isEssentiallySelfAdjoint i
  spectralMeasure := fourierMomentumSpectralMeasure i
  spectralTheorem := by
    rw [(fourierMomentumOperator_isSelfAdjoint i).isClosed.closure_eq]
    exact fourierMomentumOperator_domainAwareSelfAdjointSpectralTheorem i

/-- The indicator PVM packaged as general concrete affiliated spectral data. -/
def indicatorConcreteAffiliatedObservable :
    OperatorAlgebra.ConcreteAffiliatedObservable (Space d)
      (SpaceDHilbertSpace d μ) where
  spectralMeasure := indicatorSpectralMeasure

end QuantumMechanics

end
