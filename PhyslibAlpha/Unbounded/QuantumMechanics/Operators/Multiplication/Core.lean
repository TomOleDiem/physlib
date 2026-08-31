/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Operators.Multiplication
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.Multiplication.BasicExtras
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Graph-norm infrastructure for multiplication operators

This file contains the reusable analytic bridge needed for essential self-adjointness of
Schwartz restrictions of multiplication operators.  For a multiplier `f`, the measure

`volume.withDensity (1 + ‖f‖²)`

encodes the graph norm: convergence in its `L²` space controls both convergence of vectors and
convergence after multiplication by `f`.  The resulting graph-core theorem is proved here,
independently of Fourier analysis, so differential-operator modules only need to identify their
Schwartz restriction with a transported multiplication restriction.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal ComplexOrder

namespace QuantumMechanics

variable {d : ℕ} {f : Space d → ℂ}

/-- The scalar weight controlling the graph norm of multiplication by `f`. -/
def graphWeight (f : Space d → ℂ) (x : Space d) : ℝ := 1 + ‖f x‖ ^ 2

/-- The measure whose `L²` norm is the graph norm of multiplication by `f`. -/
def graphMeasure (f : Space d → ℂ) : Measure (Space d) :=
  volume.withDensity (fun x => ENNReal.ofReal (graphWeight f x))

lemma graphWeight_measurable (hf : Measurable f) :
    Measurable (graphWeight f) := by
  unfold graphWeight
  fun_prop

lemma graphMeasure_locallyFinite (hf : Continuous f) :
    IsLocallyFiniteMeasure (graphMeasure f) := by
  unfold graphMeasure
  apply MeasureTheory.IsLocallyFiniteMeasure.withDensity_ofReal
  unfold graphWeight
  fun_prop

lemma graphMeasure_temperate (hf : HasTemperateGrowth f) :
    Measure.HasTemperateGrowth (graphMeasure f) := by
  unfold graphMeasure
  refine { exists_integrable := ?_ }
  obtain ⟨k, C, hC⟩ := hf.norm_iteratedFDeriv_le_uniform 0
  have hbound : ∀ x : Space d, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k := by
    simpa using hC.2 0 le_rfl
  let N : ℕ := 2 * k + Module.finrank ℝ (Space d) + 3
  refine ⟨N, ?_⟩
  have hden : AEMeasurable (fun x : Space d => ENNReal.ofReal (graphWeight f x)) volume := by
    exact (graphWeight_measurable hf.1.continuous.measurable).aemeasurable.ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume : Measure (Space d)),
      ENNReal.ofReal (graphWeight f x) < ⊤ := by
    filter_upwards with x
    exact ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff_integrable_smul₀' hden hlt]
  have hbase := (integrable_one_add_norm (E := Space d)
      (μ := volume (α := Space d))
      (r := (Module.finrank ℝ (Space d) : ℝ) + 1) (by linarith)).const_mul
        (1 + C ^ 2)
  apply hbase.mono'
  · fun_prop
  · filter_upwards with x
    have hnonneg : 0 ≤ 1 + ‖x‖ := by positivity
    have hone : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have hweight : graphWeight f x ≤
        (1 + C ^ 2) * (1 + ‖x‖) ^ (2 * k) := by
      unfold graphWeight
      have hfx : ‖f x‖ ^ 2 ≤ C ^ 2 * (1 + ‖x‖) ^ (2 * k) := by
        calc
          ‖f x‖ ^ 2 ≤ (C * (1 + ‖x‖) ^ k) ^ 2 :=
            (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC.1 (by positivity))).mpr (hbound x)
          _ = C ^ 2 * (1 + ‖x‖) ^ (2 * k) := by
            rw [mul_pow, ← pow_mul]
            congr 2
            omega
      calc
        1 + ‖f x‖ ^ 2 ≤ 1 + C ^ 2 * (1 + ‖x‖) ^ (2 * k) := by gcongr
        _ ≤ (1 + C ^ 2) * (1 + ‖x‖) ^ (2 * k) := by
          nlinarith [sq_nonneg C, one_le_pow₀ (n := 2 * k) hone]
    rw [ENNReal.toReal_ofReal (by unfold graphWeight; positivity)]
    rw [norm_smul, Real.norm_of_nonneg (by unfold graphWeight; positivity),
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    have hpos : 0 < 1 + ‖x‖ := by positivity
    have hpow :
        (1 + ‖x‖) ^ (2 * k) * (1 + ‖x‖) ^ (-(N : ℝ)) =
          (1 + ‖x‖) ^ (-(Module.finrank ℝ (Space d) : ℝ) + (-3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
      congr 1
      dsimp [N]
      push_cast
      ring
    calc
      graphWeight f x * (1 + ‖x‖) ^ (-(N : ℝ)) ≤
          (1 + C ^ 2) * (1 + ‖x‖) ^ (2 * k) *
            (1 + ‖x‖) ^ (-(N : ℝ)) := by gcongr
      _ = (1 + C ^ 2) * (1 + ‖x‖) ^
            (-(Module.finrank ℝ (Space d) : ℝ) + (-3 : ℝ)) := by
          rw [mul_assoc, hpow]
      _ ≤ (1 + C ^ 2) * (1 + ‖x‖) ^
            (-((Module.finrank ℝ (Space d) : ℝ) + 1)) := by
          have hpow_le := Real.rpow_le_rpow_of_exponent_le hone
            (show -(Module.finrank ℝ (Space d) : ℝ) + (-3 : ℝ) ≤
              -(Module.finrank ℝ (Space d) : ℝ) - 1 by linarith)
          have hmul : (1 + C ^ 2) * (1 + ‖x‖) ^
                (-(Module.finrank ℝ (Space d) : ℝ) + (-3 : ℝ)) ≤
              (1 + C ^ 2) * (1 + ‖x‖) ^
                (-(Module.finrank ℝ (Space d) : ℝ) - 1) :=
            mul_le_mul_of_nonneg_left hpow_le (by positivity)
          rw [show -((Module.finrank ℝ (Space d) : ℝ) + 1) =
              -(Module.finrank ℝ (Space d) : ℝ) - 1 by ring]
          exact hmul

lemma graphMeasure_ge_volume : (volume : Measure (Space d)) ≤ graphMeasure f := by
  calc
    (volume : Measure (Space d)) = volume.withDensity 1 :=
      (withDensity_one (μ := (volume : Measure (Space d)))).symm
    _ ≤ volume.withDensity (fun x => ENNReal.ofReal (graphWeight f x)) := by
      apply withDensity_mono
      filter_upwards with x
      change 1 ≤ ENNReal.ofReal (graphWeight f x)
      rw [ENNReal.one_le_ofReal]
      unfold graphWeight
      nlinarith [sq_nonneg (‖f x‖)]

lemma graphMeasure_memLp_mul (hf : Measurable f)
    (u : MeasureTheory.Lp ℂ 2 (graphMeasure f)) :
    MemLp (fun x : Space d => f x * u x) 2 volume := by
  have hu : MemLp (u : Space d → ℂ) 2 (graphMeasure f) := Lp.memLp u
  have hvol : (volume : Measure (Space d)) ≤ graphMeasure f := by
    calc
      (volume : Measure (Space d)) = volume.withDensity 1 :=
        (withDensity_one (μ := (volume : Measure (Space d)))).symm
      _ ≤ volume.withDensity (fun x => ENNReal.ofReal (graphWeight f x)) := by
        apply withDensity_mono
        filter_upwards with x
        change 1 ≤ ENNReal.ofReal (graphWeight f x)
        rw [ENNReal.one_le_ofReal]
        unfold graphWeight
        nlinarith [sq_nonneg (‖f x‖)]
  have hu_vol : AEStronglyMeasurable (u : Space d → ℂ) volume :=
    hu.aestronglyMeasurable.mono_ac (Measure.absolutelyContinuous_of_le hvol)
  have hu2 : Integrable (fun x : Space d => ‖u x‖ ^ (2 : ℝ)) (graphMeasure f) :=
    hu.integrable_norm_rpow (by norm_num) (by norm_num)
  change Integrable (fun x : Space d => ‖u x‖ ^ (2 : ℝ))
    (volume.withDensity (fun x => ENNReal.ofReal (graphWeight f x))) at hu2
  have hden : AEMeasurable (fun x : Space d => ENNReal.ofReal (graphWeight f x)) volume := by
    exact (graphWeight_measurable hf).aemeasurable.ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume : Measure (Space d)),
      ENNReal.ofReal (graphWeight f x) < ⊤ := by
    filter_upwards with x
    exact ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff_integrable_smul₀' hden hlt] at hu2
  have hmul : Integrable (fun x : Space d => ‖f x * u x‖ ^ (2 : ℝ)) volume := by
    refine hu2.mono' ?_ ?_
    · have hfu : AEStronglyMeasurable (fun x : Space d => f x * u x) volume :=
        hf.aestronglyMeasurable.mul hu_vol
      convert hfu.norm.pow 2 using 1 <;>
        ext x <;> simp [Real.rpow_natCast]
    · filter_upwards with x
      have hw : 0 ≤ graphWeight f x := by unfold graphWeight; positivity
      rw [ENNReal.toReal_ofReal hw]
      simp only [smul_eq_mul, norm_mul, Real.rpow_natCast]
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _)]
      unfold graphWeight
      rw [Real.rpow_two, Real.rpow_two]
      calc
        (‖f x‖ * ‖u x‖) ^ 2 = ‖f x‖ ^ 2 * ‖u x‖ ^ 2 := by ring
        _ ≤ (1 + ‖f x‖ ^ 2) * ‖u x‖ ^ 2 := by
          gcongr
          exact le_add_of_nonneg_left (by positivity)
  refine ⟨?_, ?_⟩
  · fun_prop
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  have hfin := hmul.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfin
  simpa [enorm_eq_nnnorm, Real.rpow_natCast, ENNReal.coe_toReal] using hfin

lemma graphMeasure_eLpNorm_mul_le (hf : Measurable f)
    (u : Space d → ℂ) (hu : AEStronglyMeasurable u (graphMeasure f)) :
    eLpNorm (fun x => f x * u x) 2 volume ≤
      eLpNorm u 2 (graphMeasure f) := by
  have hden : AEMeasurable (fun x : Space d => ENNReal.ofReal (graphWeight f x)) volume := by
    exact (graphWeight_measurable hf).aemeasurable.ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume : Measure (Space d)),
      ENNReal.ofReal (graphWeight f x) < ⊤ := by
    filter_upwards with x
    exact ENNReal.ofReal_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  apply ENNReal.rpow_le_rpow ?_ (by positivity)
  rw [show graphMeasure f = volume.withDensity
      (fun x => ENNReal.ofReal (graphWeight f x)) by rfl,
    lintegral_withDensity_eq_lintegral_mul₀' hden]
  · apply lintegral_mono_ae
    filter_upwards with x
    simp only [Pi.mul_apply]
    rw [← ofReal_norm (f x * u x), ← ofReal_norm (u x)]
    norm_num
    rw [← ofReal_norm (f x), ← ofReal_norm (u x)]
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by unfold graphWeight; positivity)]
    apply ENNReal.ofReal_le_ofReal
    unfold graphWeight
    calc
      (‖f x‖ * ‖u x‖) ^ 2 = ‖f x‖ ^ 2 * ‖u x‖ ^ 2 := by ring
      _ ≤ (1 + ‖f x‖ ^ 2) * ‖u x‖ ^ 2 := by
        gcongr
        exact le_add_of_nonneg_left (by positivity)
  · exact hu.enorm.pow_const (2 : ℝ)

lemma graphMeasure_mul_toLp_norm_le (hf : Measurable f)
    (u : MeasureTheory.Lp ℂ 2 (graphMeasure f)) :
    ‖MemLp.toLp (fun x : Space d => f x * u x)
        (graphMeasure_memLp_mul hf u)‖ ≤ ‖u‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  apply ENNReal.toReal_mono
  · exact (Lp.memLp u).eLpNorm_ne_top
  · exact graphMeasure_eLpNorm_mul_le hf (u : Space d → ℂ)
      (Lp.memLp u).aestronglyMeasurable

/-- The multiplier map from graph-norm `L²` to ordinary `L²`. -/
noncomputable def graphMulLm (hf : Measurable f) :
    Lp ℂ 2 (graphMeasure f) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (Space d)) where
  toFun u := MemLp.toLp (fun x : Space d => f x * u x) (graphMeasure_memLp_mul hf u)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (graphMeasure_memLp_mul hf (u + v)),
      (ae_mono graphMeasure_ge_volume) (Lp.coeFn_add u v),
      MemLp.coeFn_toLp (graphMeasure_memLp_mul hf u),
      MemLp.coeFn_toLp (graphMeasure_memLp_mul hf v),
      Lp.coeFn_add
        (MemLp.toLp (fun x : Space d => f x * u x) (graphMeasure_memLp_mul hf u))
        (MemLp.toLp (fun x : Space d => f x * v x) (graphMeasure_memLp_mul hf v))] with
        x hsum huv hu hv hout
    rw [hout]
    simp only [hu, hv, huv, hsum, Pi.add_apply, mul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (graphMeasure_memLp_mul hf (c • u)),
      (ae_mono graphMeasure_ge_volume) (Lp.coeFn_smul c u),
      MemLp.coeFn_toLp (graphMeasure_memLp_mul hf u),
      Lp.coeFn_smul c
        (MemLp.toLp (fun x : Space d => f x * u x) (graphMeasure_memLp_mul hf u))] with
        x hcu hsu hu hout
    change _ = (c • MemLp.toLp (fun x : Space d => f x * u x)
      (graphMeasure_memLp_mul hf u)) x
    rw [hout]
    simp [hcu, hsu, hu, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

/-- Continuous version of `graphMulLm`; its operator norm is at most one. -/
noncomputable def graphMulCLM (hf : Measurable f) :
    Lp ℂ 2 (graphMeasure f) →L[ℂ] Lp ℂ 2 (volume : Measure (Space d)) :=
  LinearMap.mkContinuous (graphMulLm hf) 1 (by
    intro u
    simpa [graphMulLm, one_mul] using graphMeasure_mul_toLp_norm_le hf u)

@[simp]
lemma graphMulCLM_apply_ae (hf : Measurable f)
    (u : MeasureTheory.Lp ℂ 2 (graphMeasure f)) :
    graphMulCLM hf u =ᵐ[volume] fun x => f x * u x := by
  exact MemLp.coeFn_toLp (graphMeasure_memLp_mul hf u)

/-- The canonical inclusion of graph-norm `L²` into ordinary `L²`. -/
noncomputable def graphIdCLM :
    Lp ℂ 2 (graphMeasure f) →L[ℝ] Lp ℂ 2 (volume : Measure (Space d)) :=
  MeasureTheory.Lp.LpToLpOfMeasureLeSMul (p := 2) (c := 1) ENNReal.one_ne_top
    (by simpa only [one_smul] using (graphMeasure_ge_volume (f := f)))

lemma graphIdCLM_apply_ae
    (u : MeasureTheory.Lp ℂ 2 (graphMeasure f)) :
    graphIdCLM u =ᵐ[volume] u := by
  exact MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top
    (by simpa only [one_smul] using (graphMeasure_ge_volume (f := f))) u

/-- The graph-norm realization of multiplication as a continuous map into `L² × L²`. -/
noncomputable def graphPairMap (hf : Measurable f) :
    Lp ℂ 2 (graphMeasure f) → (Lp ℂ 2 (volume : Measure (Space d)) ×
      Lp ℂ 2 (volume : Measure (Space d))) :=
  fun u => (graphIdCLM u, graphMulCLM hf u)

lemma continuous_graphPairMap (hf : Measurable f) :
    Continuous (graphPairMap (f := f) hf) := by
  exact graphIdCLM.continuous.prodMk (graphMulCLM hf).continuous

/-- The Schwartz restriction of a maximal multiplication operator. -/
def schwartzMulOperator (hf : HasTemperateGrowth f) :
    SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d :=
  { domain := SpaceDHilbertSpace.SchwartzSubmodule d volume
    toFun := (𝓜 volume f).toFun.comp
      (Submodule.inclusion
        (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth hf volume)) }

lemma schwartzMulOperator_le_mulOperator (hf : HasTemperateGrowth f) :
    schwartzMulOperator (f := f) hf ≤ 𝓜 volume f := by
  apply LinearPMap.le_of_le_graph
  rintro ⟨x, y⟩ hxy
  rw [LinearPMap.mem_graph_iff] at hxy ⊢
  obtain ⟨z, hz, hzy⟩ := hxy
  obtain ⟨w, hw⟩ := z.property
  have hzS : x ∈ SpaceDHilbertSpace.SchwartzSubmodule d volume := by
    have hxeq : (SpaceDHilbertSpace.schwartzIncl volume) w = x := hw.trans hz
    exact ⟨w, hxeq⟩
  have hzeq : z = ⟨x, hzS⟩ := Subtype.ext hz
  refine ⟨⟨x, (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth hf volume) hzS⟩,
    ?_, ?_⟩
  · simpa using hz
  rw [hzeq] at hzy
  change (𝓜 volume f) ((Submodule.inclusion
      (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth hf volume))
      ⟨x, hzS⟩) = (x, y).2 at hzy
  have heq : (Submodule.inclusion
      (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth hf volume))
      ⟨x, hzS⟩ =
      ⟨x, (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth hf volume) hzS⟩ :=
    Subtype.ext rfl
  rw [heq] at hzy
  exact hzy

lemma schwartzMulOperator_apply_schwartz (hf : HasTemperateGrowth f)
    (q : SchwartzMap (Space d) ℂ) :
    schwartzMulOperator (f := f) hf
        ⟨SpaceDHilbertSpace.schwartzIncl volume q, ⟨q, rfl⟩⟩ =
      SpaceDHilbertSpace.schwartzIncl volume
        (SchwartzMap.smulLeftCLM ℂ f q) := by
  let qv : SpaceDHilbertSpace.SchwartzSubmodule d volume :=
    ⟨SpaceDHilbertSpace.schwartzIncl volume q, ⟨q, rfl⟩⟩
  change schwartzMulOperator (f := f) hf qv = _
  apply Lp.ext
  filter_upwards [SpaceDHilbertSpace.mulOperator_apply_ae
      (Submodule.inclusion
        (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth hf volume)
        qv),
      SchwartzMap.coeFn_toLp q 2 volume,
      SchwartzMap.coeFn_toLp (SchwartzMap.smulLeftCLM ℂ f q) 2 volume] with x hx hq hq'
  change (𝓜 volume f) (Submodule.inclusion
      (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth hf volume)
      qv) x = _
  rw [hx]
  have hqv : (qv : SpaceDHilbertSpace d) x = q x := by
    change (SpaceDHilbertSpace.schwartzIncl volume q) x = q x
    simpa [SpaceDHilbertSpace.schwartzIncl] using hq
  have hqv' : (SpaceDHilbertSpace.schwartzIncl volume
      (SchwartzMap.smulLeftCLM ℂ f q)) x =
      (SchwartzMap.smulLeftCLM ℂ f q) x := by
    simpa [SpaceDHilbertSpace.schwartzIncl] using hq'
  change (f • (fun p : Space d => (qv : SpaceDHilbertSpace d) p)) x =
    (SpaceDHilbertSpace.schwartzIncl volume
      (SchwartzMap.smulLeftCLM ℂ f q)) x
  change f x * (qv : SpaceDHilbertSpace d) x =
    (SpaceDHilbertSpace.schwartzIncl volume
      (SchwartzMap.smulLeftCLM ℂ f q)) x
  rw [hqv, hqv']
  rw [SchwartzMap.smulLeftCLM_apply hf]
  simp only [smul_eq_mul]

lemma memLp_graphMeasure_of_mem_mulOperator_domain
    (hf : Measurable f) (x : (𝓜 volume f).domain) :
    MemLp (x : Space d → ℂ) 2 (graphMeasure f) := by
  have hx : MemLp (x : SpaceDHilbertSpace d) 2 volume := Lp.memLp (x : SpaceDHilbertSpace d)
  have hfx : MemLp (fun p : Space d => f p * (x : SpaceDHilbertSpace d) p) 2 volume := by
    have hm : MemLp ((𝓜 volume f x : SpaceDHilbertSpace d) : Space d → ℂ)
        2 volume := Lp.memLp (𝓜 volume f x)
    have hmf : Integrable (fun p : Space d =>
        ‖f p * (x : SpaceDHilbertSpace d) p‖ ^ (2 : ℝ)) volume := by
      refine (integrable_congr (μ := (volume : Measure (Space d))) ?_).mpr
        (hm.integrable_norm_rpow (by norm_num) (by norm_num))
      filter_upwards [SpaceDHilbertSpace.mulOperator_apply_ae x] with p hp
      simp [hp, Real.rpow_natCast]
    refine ⟨hf.aestronglyMeasurable.mul hx.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    have hfin := hmf.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at hfin
    simpa [enorm_eq_nnnorm, Real.rpow_natCast, ENNReal.coe_toReal] using hfin
  have hden : AEMeasurable (fun p : Space d => ENNReal.ofReal (graphWeight f p)) volume := by
    exact (graphWeight_measurable hf).aemeasurable.ennreal_ofReal
  have hlt : ∀ᵐ p ∂(volume : Measure (Space d)),
      ENNReal.ofReal (graphWeight f p) < ⊤ := by
    filter_upwards with p
    exact ENNReal.ofReal_lt_top
  have hweighted : Integrable (fun p : Space d =>
      ‖(x : SpaceDHilbertSpace d) p‖ ^ (2 : ℝ)) (graphMeasure f) := by
    change Integrable (fun p : Space d => ‖(x : SpaceDHilbertSpace d) p‖ ^ (2 : ℝ))
      (volume.withDensity (fun p => ENNReal.ofReal (graphWeight f p)))
    rw [integrable_withDensity_iff_integrable_smul₀' hden hlt]
    have hsum := hx.integrable_norm_rpow (by norm_num) (by norm_num)
    have hsum' := hfx.integrable_norm_rpow (by norm_num) (by norm_num)
    rw [show (fun p : Space d => (ENNReal.ofReal (graphWeight f p)).toReal •
        ‖(x : SpaceDHilbertSpace d) p‖ ^ (2 : ℝ)) = fun p : Space d =>
          ‖(x : SpaceDHilbertSpace d) p‖ ^ (2 : ℝ) +
            ‖f p * (x : SpaceDHilbertSpace d) p‖ ^ (2 : ℝ) by
      funext p
      rw [ENNReal.toReal_ofReal (by unfold graphWeight; positivity)]
      simp only [smul_eq_mul]
      unfold graphWeight
      rw [Real.rpow_two, Real.rpow_two]
      simp only [norm_mul]
      ring]
    exact hsum.add hsum'
  refine ⟨hx.aestronglyMeasurable.mono_ac
      (MeasureTheory.withDensity_absolutelyContinuous volume
        (fun p : Space d => ENNReal.ofReal (graphWeight f p))), ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  have hfin := hweighted.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hfin
  simpa [enorm_eq_nnnorm, Real.rpow_natCast, ENNReal.coe_toReal] using hfin

lemma mulOperator_le_schwartzMulOperator_closure
    (hf : HasTemperateGrowth f)
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] :
    𝓜 volume f ≤ (schwartzMulOperator (f := f) hf).closure := by
  letI : IsLocallyFiniteMeasure (graphMeasure f) :=
    graphMeasure_locallyFinite hf.1.continuous
  letI : Measure.HasTemperateGrowth (graphMeasure f) := graphMeasure_temperate hf
  have hdense : DenseRange (fun q : SchwartzMap (Space d) ℂ =>
      q.toLp 2 (graphMeasure f)) := by
    change DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (graphMeasure f))
    exact SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  let P : Lp ℂ 2 (graphMeasure f) → Prop := fun u =>
    graphPairMap (f := f) hf.1.continuous.measurable u ∈
    (schwartzMulOperator (f := f) hf).graph.topologicalClosure
  have hPclosed : IsClosed {u | P u} := by
    exact (Submodule.isClosed_topologicalClosure _).preimage
      (continuous_graphPairMap hf.1.continuous.measurable)
  have hP : ∀ u : Lp ℂ 2 (graphMeasure f), P u := by
    intro u
    refine hdense.induction_on u (p := P) hPclosed ?_
    intro q
    let qv : SpaceDHilbertSpace.SchwartzSubmodule d volume :=
      ⟨SpaceDHilbertSpace.schwartzIncl volume q, ⟨q, rfl⟩⟩
    let qvd : (schwartzMulOperator (f := f) hf).domain :=
      ⟨qv, qv.property⟩
    have hfirst : graphIdCLM (q.toLp 2 (graphMeasure f)) = qvd := by
      apply Lp.ext
      filter_upwards [graphIdCLM_apply_ae (q.toLp 2 (graphMeasure f)),
        (ae_mono (graphMeasure_ge_volume (f := f)))
          (SchwartzMap.coeFn_toLp q 2 (graphMeasure f)),
        SchwartzMap.coeFn_toLp q 2 volume] with x h₁ h₂ h₃
      rw [h₁, h₂]
      change q x = (SpaceDHilbertSpace.schwartzIncl volume q) x
      exact h₃.symm
    have hq : SpaceDHilbertSpace.schwartzIncl volume q = q.toLp 2 volume := by
      exact SchwartzMap.toLpCLM_apply
    have hsecond : graphMulCLM hf.1.continuous.measurable (q.toLp 2 (graphMeasure f)) =
        (schwartzMulOperator (f := f) hf) qvd := by
      apply Lp.ext
      filter_upwards [graphMulCLM_apply_ae hf.1.continuous.measurable
          (q.toLp 2 (graphMeasure f)),
        (ae_mono (graphMeasure_ge_volume (f := f)))
          (SchwartzMap.coeFn_toLp q 2 (graphMeasure f)),
        SchwartzMap.coeFn_toLp q 2 volume,
        SpaceDHilbertSpace.mulOperator_apply_ae
          (Submodule.inclusion
            (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth hf volume)
            qv)] with x h₁ h₂ h₃ h₄
      rw [h₁, h₂]
      change f x * q x = (𝓜 volume f)
        (Submodule.inclusion
          (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth hf volume)
          qv) x
      calc
        f x * q x = f x * (SpaceDHilbertSpace.schwartzIncl volume q) x := by
          rw [hq, h₃]
        _ = (f • (fun p : Space d =>
            (((Submodule.inclusion
              (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth hf volume)
              qv : (𝓜 volume f).domain) : SpaceDHilbertSpace d) p))) x := by rfl
        _ = (𝓜 volume f) (Submodule.inclusion
            (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth hf volume)
            qv) x := h₄.symm
    change (graphIdCLM (q.toLp 2 (graphMeasure f)),
        graphMulCLM hf.1.continuous.measurable (q.toLp 2 (graphMeasure f))) ∈
      (schwartzMulOperator (f := f) hf).graph.topologicalClosure
    rw [hfirst, hsecond]
    apply subset_closure
    exact (LinearPMap.mem_graph_iff _).mpr ⟨qvd, rfl, rfl⟩
  apply LinearPMap.le_of_le_graph
  rintro ⟨x, y⟩ hxy
  rw [LinearPMap.mem_graph_iff] at hxy
  obtain ⟨z, hz, hzy⟩ := hxy
  let u : Lp ℂ 2 (graphMeasure f) :=
    MemLp.toLp (z : Space d → ℂ)
      (memLp_graphMeasure_of_mem_mulOperator_domain hf.1.continuous.measurable z)
  have hfirst : graphIdCLM u = x := by
    apply Lp.ext
    filter_upwards [graphIdCLM_apply_ae u,
      (ae_mono (graphMeasure_ge_volume (f := f)))
        (MemLp.coeFn_toLp
          (memLp_graphMeasure_of_mem_mulOperator_domain hf.1.continuous.measurable z)),
      Lp.ext_iff.mp hz] with p h₁ h₂ h₃
    rw [h₁, h₂, h₃]
  have hsecond : graphMulCLM hf.1.continuous.measurable u = y := by
    apply Lp.ext
    filter_upwards [graphMulCLM_apply_ae hf.1.continuous.measurable u,
      (ae_mono (graphMeasure_ge_volume (f := f)))
        (MemLp.coeFn_toLp
          (memLp_graphMeasure_of_mem_mulOperator_domain hf.1.continuous.measurable z)),
      SpaceDHilbertSpace.mulOperator_apply_ae z,
      Lp.ext_iff.mp hz] with p h₁ h₂ h₃ h₄
    rw [h₁, h₂]
    simpa [smul_eq_mul] using h₃.symm.trans (congrArg (fun w : SpaceDHilbertSpace d => w p) hzy)
  have hu := hP u
  change (graphIdCLM u, graphMulCLM hf.1.continuous.measurable u) ∈
    (schwartzMulOperator (f := f) hf).graph.topologicalClosure at hu
  rw [hfirst, hsecond] at hu
  have hsc : (schwartzMulOperator (f := f) hf).IsClosable :=
    LinearPMap.isClosable_iff_exists_closed_extension.mpr
      ⟨𝓜 volume f, SpaceDHilbertSpace.mulOperator_isClosed
        hf.1.continuous.measurable.aestronglyMeasurable,
        schwartzMulOperator_le_mulOperator hf⟩
  rw [← hsc.graph_closure_eq_closure_graph]
  exact hu

/-!
### The reusable closure theorem

The preceding two graph inclusions are the two halves of the same statement: the Schwartz
restriction is a core for the maximal multiplier.  Keeping the equality here, rather than
reproving it for each concrete polynomial multiplier, is the main interface for transported
Fourier differential operators.
-/

/-- A temperate multiplier has the maximal multiplication operator as the closure of its
Schwartz restriction. -/
lemma schwartzMulOperator_closure_eq_mulOperator
    (hf : HasTemperateGrowth f)
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] :
    (schwartzMulOperator (f := f) hf).closure = 𝓜 volume f := by
  apply le_antisymm
  · have hclosed : (𝓜 volume f).IsClosed :=
      SpaceDHilbertSpace.mulOperator_isClosed hf.1.continuous.measurable.aestronglyMeasurable
    have hmono := hclosed.isClosable.closure_mono
      (schwartzMulOperator_le_mulOperator hf)
    rw [hclosed.closure_eq] at hmono
    exact hmono
  · exact mulOperator_le_schwartzMulOperator_closure hf

/-- If a temperate multiplier is real-valued, its Schwartz restriction is essentially
self-adjoint. -/
lemma schwartzMulOperator_isEssentiallySelfAdjoint_ofReal
    (hf : HasTemperateGrowth f) (hf' : starRingEnd ℂ ∘ f = f)
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] :
    (schwartzMulOperator (f := f) hf).IsEssentiallySelfAdjoint := by
  change IsSelfAdjoint (schwartzMulOperator (f := f) hf).closure
  rw [schwartzMulOperator_closure_eq_mulOperator hf]
  exact SpaceDHilbertSpace.mulOperator_isSelfAdjoint_ofReal
    hf.1.continuous.measurable.aestronglyMeasurable hf'

end QuantumMechanics
