/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.Concrete
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-!
# Canonical unbounded spectral integrals

This file starts the truncation construction of the maximal operator associated to a real WOT
spectral measure.  The bounded integral and its vector norm-square identity live in
`WeakSpectralMeasure`; here the spectral variable is approximated by
`r ↦ r 1_{[-n,n]}(r)`.  The construction is deliberately separate from the Cayley theorem so that
the same maximal-domain argument can be reused by multiplication and Schrödinger models.
-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace Function
open ContinuousLinearMap ContinuousLinearMapWOT MeasureTheory Set

namespace QuantumMechanics.WOTSpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded real spectral variable truncated to `[-n,n]`. -/
def truncationFunction (n : ℕ) : ℝ → ℂ :=
  (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator (fun r : ℝ => (r : ℂ))

def realTruncationFunction (n : ℕ) : ℝ → ℝ :=
  (Set.Icc (-(n : ℝ)) (n : ℝ)).indicator id

def spectralCutoffSet (n : ℕ) : Set ℝ := Set.Icc (-(n : ℝ)) (n : ℝ)

lemma spectralCutoffSet_mono : Monotone spectralCutoffSet := by
  intro n m hnm r hr
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  exact ⟨le_trans (neg_le_neg hnmR) hr.1, le_trans hr.2 hnmR⟩

lemma spectralCutoffSet_iUnion : ⋃ n, spectralCutoffSet n = Set.univ := by
  ext r
  simp only [mem_iUnion, mem_Icc, mem_univ, iff_true]
  obtain ⟨n, hn⟩ := exists_nat_ge |r|
  exact ⟨n, neg_le_of_abs_le hn, le_trans (le_abs_self r) hn⟩

lemma truncationFunction_measurable (n : ℕ) : Measurable (truncationFunction n) := by
  exact Complex.measurable_ofReal.indicator measurableSet_Icc

lemma truncationFunction_bounded (n : ℕ) :
    ∃ C : ℝ, ∀ r, ‖truncationFunction n r‖ ≤ C := by
  refine ⟨n, fun r => ?_⟩
  by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
  · rw [truncationFunction, Set.indicator_of_mem hr]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr hr
  · simp [truncationFunction, hr]

lemma realTruncationFunction_measurable (n : ℕ) :
    Measurable (realTruncationFunction n) := by
  exact measurable_id.indicator measurableSet_Icc

lemma realTruncationFunction_bounded (n : ℕ) :
    ∃ C : ℝ, ∀ r, |realTruncationFunction n r| ≤ C := by
  refine ⟨n, fun r => ?_⟩
  by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
  · rw [realTruncationFunction, Set.indicator_of_mem hr]
    exact abs_le.mpr hr
  · simp [realTruncationFunction, hr]

lemma realTruncationFunction_complex_eq (n : ℕ) :
    (fun r => (realTruncationFunction n r : ℂ)) = truncationFunction n := by
  funext r
  by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ) <;>
    simp [realTruncationFunction, truncationFunction, hr]

lemma truncationFunction_eventually_eq (r : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, truncationFunction n r = (r : ℂ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge |r|
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hnr : |r| ≤ (n : ℝ) := le_trans hN (by exact_mod_cast hn)
  rw [truncationFunction, Set.indicator_of_mem]
  exact abs_le.mp hnr

lemma truncationFunction_tendsto (r : ℝ) :
    Filter.Tendsto (fun n : ℕ => truncationFunction n r) Filter.atTop (𝓝 (r : ℂ)) := by
  exact tendsto_nhds_of_eventually_eq (truncationFunction_eventually_eq r)

lemma truncationIntegral_inner_tendsto_complexWeakIntegral
    (μS : WOTSpectralMeasure ℝ H) (x y : H)
    (hfi : (μS.scalarMeasure x y).Integrable id) :
    Filter.Tendsto
      (fun n : ℕ => ∫ᵛ r, truncationFunction n r ∂[
        ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); μS.scalarMeasure x y])
      Filter.atTop (𝓝 (μS.complexWeakIntegral (fun r : ℝ => (r : ℂ)) x y)) := by
  let ν := μS.scalarMeasure x y
  have hbound : Integrable (fun r : ℝ => |r|) ν.variation := by
    simpa [ν, Real.norm_eq_abs] using hfi.norm
  have hdom : Filter.Tendsto
      (fun n : ℕ => ∫ᵛ r, truncationFunction n r ∂[
        ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν])
      Filter.atTop (𝓝 (∫ᵛ r, (r : ℂ) ∂[
        ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); ν])) := by
    apply MeasureTheory.VectorMeasure.tendsto_integral_of_dominated_convergence
      (μ := ν) (B := ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ))
      (fun r : ℝ => |r|)
    · intro n
      exact (truncationFunction_measurable n).aestronglyMeasurable
    · exact hbound
    · intro n
      filter_upwards [] with r
      by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
      · simp [truncationFunction, Set.indicator_of_mem hr, Complex.norm_real,
          Real.norm_eq_abs]
      · simp [truncationFunction, Set.indicator, hr]
    · filter_upwards [] with r
      exact truncationFunction_tendsto r
  convert hdom using 1
  simpa [WOTSpectralMeasure.complexWeakIntegral, ν] using hdom

lemma integral_indicator_real_eq_complex
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.VectorMeasure α ℂ)
    (c : ℝ) (s : Set α) :
    (∫ᵛ x, s.indicator (fun _ => (c : ℂ)) x
      ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ]) =
      ∫ᵛ x, (s.indicator (fun _ => c) x : ℂ)
        ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := by
  have hfun : (fun x => s.indicator (fun _ => (c : ℂ)) x) =
      (fun x => (s.indicator (fun _ => c) x : ℂ)) := by
    simpa [Function.comp_def] using
      (Set.indicator_comp_of_zero (s := s) (f := fun _ : α => c)
        (g := Complex.ofRealCLM) Complex.ofRealCLM.map_zero)
  exact congrArg (fun f : α → ℂ =>
    ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ]) hfun

lemma integral_real_eq_complex
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.VectorMeasure α ℂ)
    {g : α → ℝ} (hg : μ.Integrable g) :
    ∫ᵛ x, g x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ] =
      ∫ᵛ x, (g x : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := by
  apply hg.induction (P := fun f =>
    ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ] =
      ∫ᵛ x, Complex.ofRealCLM (f x)
        ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ])
  · intro c s hs hfinite
    change μ.variation s < ⊤ at hfinite
    have hfinite' : IsFiniteMeasure (μ.variation.restrict s) := by
      exact MeasureTheory.isFiniteMeasure_restrict.mpr hfinite.ne
    letI := hfinite'
    calc
      ∫ᵛ x, s.indicator (fun _ => c) x
          ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ] =
          (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)) c (μ s) :=
        VectorMeasure.integral_indicator_const c hs
      _ = (ContinuousLinearMap.lsmul ℝ ℂ) (c : ℂ) (μ s) := by
        simp [ContinuousLinearMap.lsmul_apply]
      _ = ∫ᵛ x, s.indicator (fun _ => (c : ℂ)) x
          ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] :=
        (VectorMeasure.integral_indicator_const (c : ℂ) hs).symm
      _ = ∫ᵛ x, Complex.ofRealCLM (s.indicator (fun _ => c) x)
          ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := by
        simpa [Function.comp_def] using congrArg (fun f : α → ℂ =>
          ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ])
          (Set.indicator_comp_of_zero (s := s) (f := fun _ : α => c)
            (g := Complex.ofRealCLM) Complex.ofRealCLM.map_zero)
  · intro f k _ hf hk hfP hkP
    change (∫ᵛ x, f x + k x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ]) = _
    rw [VectorMeasure.integral_fun_add (μ := μ)
      (B := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)) hf hk]
    have hfunadd : (fun x => Complex.ofRealCLM ((f + k) x)) =
        (fun x => Complex.ofRealCLM (f x) + Complex.ofRealCLM (k x)) := by
      funext x
      simp [Pi.add_apply, map_add]
    rw [hfunadd]
    have hfC : μ.Integrable (fun x => Complex.ofRealCLM (f x)) := by
      exact hf.norm.mono'
        (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hf.aestronglyMeasurable)
        (by
          filter_upwards with x
          simp [Complex.norm_real, Real.norm_eq_abs])
    have hkC : μ.Integrable (fun x => Complex.ofRealCLM (k x)) := by
      exact hk.norm.mono'
        (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable hk.aestronglyMeasurable)
        (by
          filter_upwards with x
          simp [Complex.norm_real, Real.norm_eq_abs])
    rw [VectorMeasure.integral_fun_add (μ := μ)
      (B := ContinuousLinearMap.lsmul ℝ ℂ) hfC hkC]
    rw [hfP, hkP]
  · apply isClosed_eq
    · exact MeasureTheory.VectorMeasure.continuous_integral
    · have hcont := (MeasureTheory.VectorMeasure.continuous_integral
        (μ := μ) (B := ContinuousLinearMap.lsmul ℝ ℂ)).comp
        (Complex.ofRealCLM.compLpL 1 μ.variation).continuous
      convert hcont using 1
      funext f
      apply VectorMeasure.integral_congr_ae
      exact (Complex.ofRealCLM.coeFn_compLpL f).symm
  · intro f k hfk hf hfP
    calc
      ∫ᵛ x, k x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ] =
          ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ] :=
        VectorMeasure.integral_congr_ae (μ := μ)
          (B := ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)) hfk.symm
      _ = ∫ᵛ x, (f x : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := hfP
      _ = ∫ᵛ x, (k x : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := by
        apply VectorMeasure.integral_congr_ae (μ := μ)
          (B := ContinuousLinearMap.lsmul ℝ ℂ)
        filter_upwards [hfk] with x hx
        exact congrArg Complex.ofReal hx

/-- The bounded operator obtained by integrating the `n`-th truncated spectral variable. -/
noncomputable def truncationIntegral (μS : WOTSpectralMeasure ℝ H) (n : ℕ) : H →WOT[ℂ] H :=
  boundedIntegral μS (truncationFunction n) (truncationFunction_measurable n)
    (truncationFunction_bounded n)

lemma truncationIntegral_sub_apply (μS : WOTSpectralMeasure ℝ H) (n m : ℕ) (x : H) :
    truncationIntegral μS n x - truncationIntegral μS m x =
      boundedIntegral μS (fun r => truncationFunction n r - truncationFunction m r)
        ((truncationFunction_measurable n).sub (truncationFunction_measurable m))
        (by
          rcases truncationFunction_bounded n with ⟨Cn, hCn⟩
          rcases truncationFunction_bounded m with ⟨Cm, hCm⟩
          refine ⟨Cn + Cm, fun r => ?_⟩
          exact (norm_sub_le _ _).trans (add_le_add (hCn r) (hCm r))) x := by
  change truncationIntegral μS n x - truncationIntegral μS m x =
    boundedIntegral μS (truncationFunction n - truncationFunction m) _ _ x
  exact (congrArg (fun A : H →WOT[ℂ] H => A x)
    (boundedIntegral_sub μS (truncationFunction_measurable n)
      (truncationFunction_measurable m) (truncationFunction_bounded n)
      (truncationFunction_bounded m))).symm

lemma diagonalMeasure_add_le (μS : WOTSpectralMeasure ℝ H) (x y : H) :
    μS.diagonalMeasure (x + y) ≤
      (μS.diagonalMeasure x + μS.diagonalMeasure x) +
        (μS.diagonalMeasure y + μS.diagonalMeasure y) := by
  refine (Measure.le_iff').2 (fun S => ?_)
  have h := congrArg (fun ν : Measure ℝ => ν S)
    (μS.diagonalMeasure_parallelogram x y)
  rw [Measure.add_apply, Measure.add_apply, Measure.add_apply, Measure.add_apply] at h
  calc
    μS.diagonalMeasure (x + y) S ≤
        μS.diagonalMeasure (x + y) S + μS.diagonalMeasure (x - y) S :=
      le_add_of_nonneg_right (by positivity)
    _ = ((μS.diagonalMeasure x + μS.diagonalMeasure x) +
        (μS.diagonalMeasure y + μS.diagonalMeasure y)) S := h

lemma spectralSquareMomentDomain_zero (μS : WOTSpectralMeasure ℝ H) :
    (0 : H) ∈ OperatorAlgebra.spectralSquareMomentDomain μS := by
  rw [OperatorAlgebra.mem_spectralSquareMomentDomain_iff]
  have hzero : (0 : H) = (0 : ℂ) • (0 : H) := by simp
  rw [hzero, μS.diagonalMeasure_smul]
  simpa [norm_zero, pow_two] using (integrable_zero_measure :
    Integrable (fun r : ℝ => r ^ 2) (0 : Measure ℝ))

lemma spectralSquareMomentDomain_add (μS : WOTSpectralMeasure ℝ H) {x y : H}
    (hx : x ∈ OperatorAlgebra.spectralSquareMomentDomain μS)
    (hy : y ∈ OperatorAlgebra.spectralSquareMomentDomain μS) :
    x + y ∈ OperatorAlgebra.spectralSquareMomentDomain μS := by
  rw [OperatorAlgebra.mem_spectralSquareMomentDomain_iff] at hx hy ⊢
  apply Integrable.mono_measure
    ((hx.add_measure hx).add_measure (hy.add_measure hy))
  exact diagonalMeasure_add_le μS x y

lemma spectralSquareMomentDomain_smul (μS : WOTSpectralMeasure ℝ H) (c : ℂ) {x : H}
    (hx : x ∈ OperatorAlgebra.spectralSquareMomentDomain μS) :
    c • x ∈ OperatorAlgebra.spectralSquareMomentDomain μS := by
  rw [OperatorAlgebra.mem_spectralSquareMomentDomain_iff, μS.diagonalMeasure_smul]
  apply Integrable.mono_measure (hx.smul_measure ENNReal.ofReal_ne_top)
  exact le_rfl

/-- The square-moment domain is a complex submodule, so the maximal spectral integral can be
defined as a `LinearPMap` rather than merely as a pointwise partial function. -/
def spectralSquareMomentSubmodule (μS : WOTSpectralMeasure ℝ H) : Submodule ℂ H where
  carrier := OperatorAlgebra.spectralSquareMomentDomain μS
  zero_mem' := spectralSquareMomentDomain_zero μS
  add_mem' := spectralSquareMomentDomain_add μS
  smul_mem' := spectralSquareMomentDomain_smul μS

lemma truncationIntegral_sub_norm_sq (μS : WOTSpectralMeasure ℝ H) (n m : ℕ) (x : H) :
    ENNReal.ofReal (‖truncationIntegral μS n x - truncationIntegral μS m x‖ ^ 2) =
      ∫⁻ r, ENNReal.ofReal
        (‖truncationFunction n r - truncationFunction m r‖ ^ 2)
        ∂μS.diagonalMeasure x := by
  rw [truncationIntegral_sub_apply]
  exact boundedIntegral_norm_sq μS
    ((truncationFunction_measurable n).sub (truncationFunction_measurable m))
        (by
      rcases truncationFunction_bounded n with ⟨Cn, hCn⟩
      rcases truncationFunction_bounded m with ⟨Cm, hCm⟩
      exact ⟨Cn + Cm, fun r =>
        (norm_sub_le _ _).trans (add_le_add (hCn r) (hCm r))⟩) x

lemma truncationIntegral_sub_norm_sq_le (μS : WOTSpectralMeasure ℝ H) (n m : ℕ) (x : H) :
    ENNReal.ofReal (‖truncationIntegral μS n x - truncationIntegral μS m x‖ ^ 2) ≤
      2 * (∫⁻ r, ENNReal.ofReal
        (‖truncationFunction n r - (r : ℂ)‖ ^ 2) ∂μS.diagonalMeasure x) +
        2 * (∫⁻ r, ENNReal.ofReal
          (‖truncationFunction m r - (r : ℂ)‖ ^ 2) ∂μS.diagonalMeasure x) := by
  let a : ℝ → ℝ := fun r => ‖truncationFunction n r - (r : ℂ)‖ ^ 2
  let b : ℝ → ℝ := fun r => ‖truncationFunction m r - (r : ℂ)‖ ^ 2
  have ha : Measurable a :=
    (((truncationFunction_measurable n).sub Complex.measurable_ofReal).norm.pow_const 2)
  have hb : Measurable b :=
    (((truncationFunction_measurable m).sub Complex.measurable_ofReal).norm.pow_const 2)
  have hpoint : ∀ r, ENNReal.ofReal
      (‖truncationFunction n r - truncationFunction m r‖ ^ 2) ≤
        ENNReal.ofReal (2 * a r + 2 * b r) := by
    intro r
    apply ENNReal.ofReal_le_ofReal
    have hnorm : ‖truncationFunction n r - truncationFunction m r‖ ≤
        ‖truncationFunction n r - (r : ℂ)‖ +
          ‖truncationFunction m r - (r : ℂ)‖ := by
      calc
        ‖truncationFunction n r - truncationFunction m r‖ =
            ‖(truncationFunction n r - (r : ℂ)) -
              (truncationFunction m r - (r : ℂ))‖ := by
                congr 1 <;> ring
        _ ≤ _ := norm_sub_le _ _
    dsimp [a, b]
    have hc : 0 ≤ ‖truncationFunction n r - truncationFunction m r‖ := norm_nonneg _
    have hab : 0 ≤ ‖truncationFunction n r - (r : ℂ)‖ +
        ‖truncationFunction m r - (r : ℂ)‖ := by positivity
    have hsquare := (sq_le_sq₀ hc hab).2 hnorm
    nlinarith [sq_nonneg
      (‖truncationFunction n r - (r : ℂ)‖ -
        ‖truncationFunction m r - (r : ℂ)‖)]
  calc
    ENNReal.ofReal (‖truncationIntegral μS n x - truncationIntegral μS m x‖ ^ 2) =
        ∫⁻ r, ENNReal.ofReal
          (‖truncationFunction n r - truncationFunction m r‖ ^ 2)
          ∂μS.diagonalMeasure x := truncationIntegral_sub_norm_sq μS n m x
    _ ≤ ∫⁻ r, ENNReal.ofReal (2 * a r + 2 * b r) ∂μS.diagonalMeasure x :=
      lintegral_mono hpoint
    _ = 2 * (∫⁻ r, ENNReal.ofReal (a r) ∂μS.diagonalMeasure x) +
        2 * (∫⁻ r, ENNReal.ofReal (b r) ∂μS.diagonalMeasure x) := by
      have hsplit : ∀ r, ENNReal.ofReal (2 * a r + 2 * b r) =
          2 * ENNReal.ofReal (a r) + 2 * ENNReal.ofReal (b r) := by
        intro r
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        norm_num
      have hameas : Measurable (fun r => ENNReal.ofReal (a r)) :=
        ENNReal.continuous_ofReal.measurable.comp ha
      have hbmeas : Measurable (fun r => ENNReal.ofReal (b r)) :=
        ENNReal.continuous_ofReal.measurable.comp hb
      simp_rw [hsplit]
      rw [lintegral_add_left (by fun_prop), lintegral_const_mul 2 hameas,
        lintegral_const_mul 2 hbmeas]

lemma truncation_error_lintegral_tendsto_zero
    (μS : WOTSpectralMeasure ℝ H) (x : H)
    (hx : Integrable (fun r : ℝ => r ^ 2) (μS.diagonalMeasure x)) :
    Filter.Tendsto
      (fun n : ℕ => ∫⁻ r, ENNReal.ofReal
        (‖truncationFunction n r - (r : ℂ)‖ ^ 2) ∂μS.diagonalMeasure x)
      Filter.atTop (𝓝 0) := by
  let μ : Measure ℝ := μS.diagonalMeasure x
  let F : ℕ → ℝ → ENNReal := fun n r =>
    ENNReal.ofReal (‖truncationFunction n r - (r : ℂ)‖ ^ 2)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    change Measurable (fun r : ℝ => ENNReal.ofReal
      (‖truncationFunction n r - (r : ℂ)‖ ^ 2))
    exact ENNReal.continuous_ofReal.measurable.comp
      (((truncationFunction_measurable n).sub Complex.measurable_ofReal).norm.pow_const 2)
  have hbound : ∀ n, ∀ᵐ r ∂μ, F n r ≤ ENNReal.ofReal (4 * r ^ 2) := by
    intro n
    filter_upwards [] with r
    dsimp [F]
    apply ENNReal.ofReal_le_ofReal
    by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
    · simp [truncationFunction, Set.indicator_of_mem hr]
      positivity
    · simp [truncationFunction, Set.indicator, hr]
      have hsq : ‖(r : ℂ)‖ ^ 2 ≤ 4 * r ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        rw [sq_abs]
        nlinarith [sq_nonneg r]
      simpa [norm_neg] using hsq
  have hdom : Integrable (fun r : ℝ => 4 * r ^ 2) μ := by
    simpa only [smul_eq_mul] using hx.const_mul 4
  have hfin : (∫⁻ r, ENNReal.ofReal (4 * r ^ 2) ∂μ) ≠ (⊤ : ENNReal) := by
    exact (hdom.lintegral_lt_top).ne
  let F₀ : ℝ → ENNReal := fun _ => 0
  have hlim : ∀ᵐ r ∂μ, Filter.Tendsto (fun n : ℕ => F n r) Filter.atTop (𝓝 (F₀ r)) := by
    filter_upwards [] with r
    have htrunc := truncationFunction_tendsto r
    have hdiff : Filter.Tendsto
        (fun n : ℕ => truncationFunction n r - (r : ℂ)) Filter.atTop (𝓝 0) := by
      simpa using htrunc.sub (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (r : ℂ)) Filter.atTop (𝓝 (r : ℂ)))
    have hnorm : Filter.Tendsto
        (fun n : ℕ => ‖truncationFunction n r - (r : ℂ)‖ ^ 2)
          Filter.atTop (𝓝 (0 ^ 2)) := by
      simpa [Function.comp_def] using
        (continuous_norm.pow 2).continuousAt.tendsto.comp hdiff
    change Filter.Tendsto (fun n : ℕ => ENNReal.ofReal
      (‖truncationFunction n r - (r : ℂ)‖ ^ 2)) Filter.atTop (𝓝 (F₀ r))
    have hout := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm
    simpa [F, F₀, Function.comp_def] using hout
  have hmain : Filter.Tendsto (fun n : ℕ => ∫⁻ r, F n r ∂μ) Filter.atTop
      (𝓝 (∫⁻ r, F₀ r ∂μ)) := by
    apply MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
      (fun r => ENNReal.ofReal (4 * r ^ 2))
    · filter_upwards [] with n
      exact hFmeas n
    · filter_upwards [] with n
      exact hbound n
    · exact hfin
    · exact hlim
  simpa [F, F₀, μ] using hmain

lemma truncationIntegral_cauchy (μS : WOTSpectralMeasure ℝ H) {x : H}
    (hx : x ∈ OperatorAlgebra.spectralSquareMomentDomain μS) :
    CauchySeq (fun n : ℕ => truncationIntegral μS n x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let A : ℕ → ENNReal := fun n => ∫⁻ r, ENNReal.ofReal
    (‖truncationFunction n r - (r : ℂ)‖ ^ 2) ∂μS.diagonalMeasure x
  have hA : Filter.Tendsto A Filter.atTop (𝓝 0) := by
    simpa [A] using truncation_error_lintegral_tendsto_zero μS x hx
  have hq : 0 < ε ^ 2 / 8 := by positivity
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, A n < ENNReal.ofReal (ε ^ 2 / 8) := by
    apply hA.eventually
    exact Iio_mem_nhds ((ENNReal.ofReal_pos).2 hq)
  rcases (Filter.eventually_atTop.1 hsmall) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn m hm
  have hnA := hN n hn
  have hmA := hN m hm
  have hsum : 2 * A n + 2 * A m < ENNReal.ofReal (ε ^ 2) := by
    calc
          2 * A n + 2 * A m <
          2 * ENNReal.ofReal (ε ^ 2 / 8) +
            2 * ENNReal.ofReal (ε ^ 2 / 8) := by
              gcongr <;> norm_num
      _ = ENNReal.ofReal (ε ^ 2 / 2) := by
        have htwo (q : ℝ) : (2 : ENNReal) * ENNReal.ofReal q =
            ENNReal.ofReal (2 * q) := by
          calc
            (2 : ENNReal) * ENNReal.ofReal q =
                ENNReal.ofReal 2 * ENNReal.ofReal q := by norm_num
            _ = ENNReal.ofReal (2 * q) :=
              (ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)).symm
        calc
          2 * ENNReal.ofReal (ε ^ 2 / 8) +
              2 * ENNReal.ofReal (ε ^ 2 / 8) =
              ENNReal.ofReal (2 * (ε ^ 2 / 8)) +
                ENNReal.ofReal (2 * (ε ^ 2 / 8)) := by
                  congr 1
                  · exact htwo _
                  · exact htwo _
          _ = ENNReal.ofReal (2 * (ε ^ 2 / 8) + 2 * (ε ^ 2 / 8)) :=
            (ENNReal.ofReal_add (by positivity) (by positivity)).symm
          _ = ENNReal.ofReal (ε ^ 2 / 2) := by congr 1 <;> ring
      _ < ENNReal.ofReal (ε ^ 2) := by
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith)
  have hnormsq : ENNReal.ofReal
      (‖truncationIntegral μS n x - truncationIntegral μS m x‖ ^ 2) <
        ENNReal.ofReal (ε ^ 2) :=
    (truncationIntegral_sub_norm_sq_le μS n m x).trans_lt hsum
  have hnormsq' : ‖truncationIntegral μS n x - truncationIntegral μS m x‖ ^ 2 < ε ^ 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hnormsq
  have hnorm : ‖truncationIntegral μS n x - truncationIntegral μS m x‖ < ε :=
    (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hε)).mp hnormsq'
  simpa [dist_eq_norm] using hnorm

lemma truncation_norm_lintegral_tendsto
    (μS : WOTSpectralMeasure ℝ H) (x : H)
    (hx : Integrable (fun r : ℝ => r ^ 2) (μS.diagonalMeasure x)) :
    Filter.Tendsto
      (fun n : ℕ => ∫⁻ r, ENNReal.ofReal
        (‖truncationFunction n r‖ ^ 2) ∂μS.diagonalMeasure x)
      Filter.atTop
      (𝓝 (∫⁻ r, ENNReal.ofReal (r ^ 2) ∂μS.diagonalMeasure x)) := by
  let μ : Measure ℝ := μS.diagonalMeasure x
  let F : ℕ → ℝ → ENNReal := fun n r =>
    ENNReal.ofReal (‖truncationFunction n r‖ ^ 2)
  let F₀ : ℝ → ENNReal := fun r => ENNReal.ofReal (r ^ 2)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    exact ENNReal.continuous_ofReal.measurable.comp
      ((truncationFunction_measurable n).norm.pow_const 2)
  have hbound : ∀ n, ∀ᵐ r ∂μ, F n r ≤ F₀ r := by
    intro n
    filter_upwards [] with r
    dsimp [F, F₀]
    apply ENNReal.ofReal_le_ofReal
    by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
    · simp [truncationFunction, Set.indicator_of_mem hr, Complex.norm_real,
        Real.norm_eq_abs]
    · simp [truncationFunction, Set.indicator, hr]
      positivity
  have hfin : (∫⁻ r, F₀ r ∂μ) ≠ (⊤ : ENNReal) := by
    exact (hx.lintegral_lt_top).ne
  have hlim : ∀ᵐ r ∂μ, Filter.Tendsto (fun n : ℕ => F n r) Filter.atTop
      (𝓝 (F₀ r)) := by
    filter_upwards [] with r
    exact tendsto_nhds_of_eventually_eq (by
      filter_upwards [truncationFunction_eventually_eq r] with n hn
      have hnormsq : ‖(r : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
        rw [← ofReal_norm_eq_enorm (r : ℂ), pow_two,
          ← ENNReal.ofReal_mul (norm_nonneg (r : ℂ))]
        simp [Complex.norm_real, Real.norm_eq_abs]
        congr 1
        ring
      simp [F, F₀, hn, hnormsq])
  have hmain : Filter.Tendsto (fun n : ℕ => ∫⁻ r, F n r ∂μ) Filter.atTop
      (𝓝 (∫⁻ r, F₀ r ∂μ)) := by
    apply MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
      (fun r => ENNReal.ofReal (r ^ 2))
    · filter_upwards [] with n
      exact hFmeas n
    · filter_upwards [] with n
      exact hbound n
    · exact hfin
    · exact hlim
  simpa [F, F₀, μ] using hmain

noncomputable def truncationLimit (μS : WOTSpectralMeasure ℝ H)
    (x : spectralSquareMomentSubmodule μS) : H :=
  Filter.atTop.limUnder (fun n : ℕ => truncationIntegral μS n x)

lemma truncationLimit_tendsto (μS : WOTSpectralMeasure ℝ H)
    (x : spectralSquareMomentSubmodule μS) :
    Filter.Tendsto (fun n : ℕ => truncationIntegral μS n x) Filter.atTop
      (𝓝 (truncationLimit μS x)) := by
  exact (truncationIntegral_cauchy μS x.property).tendsto_limUnder

lemma truncationLimit_add (μS : WOTSpectralMeasure ℝ H)
    (x y : spectralSquareMomentSubmodule μS) :
    truncationLimit μS (x + y) = truncationLimit μS x + truncationLimit μS y := by
  have hxy := (truncationLimit_tendsto μS x).add (truncationLimit_tendsto μS y)
  exact tendsto_nhds_unique (truncationLimit_tendsto μS (x + y))
    (by
      convert hxy using 1
      funext n
      simpa using (ContinuousLinearMapWOT.toCLM (truncationIntegral μS n)).map_add
        (x : H) (y : H))

lemma truncationLimit_smul (μS : WOTSpectralMeasure ℝ H)
    (c : ℂ) (x : spectralSquareMomentSubmodule μS) :
    truncationLimit μS (c • x) = c • truncationLimit μS x := by
  have hcx := (truncationLimit_tendsto μS x).const_smul c
  exact tendsto_nhds_unique (truncationLimit_tendsto μS (c • x))
    (by
      convert hcx using 1
      funext n
      simpa using (ContinuousLinearMapWOT.toCLM (truncationIntegral μS n)).map_smul c
        (x : H))

lemma truncationIntegral_norm_sq (μS : WOTSpectralMeasure ℝ H) (n : ℕ) (x : H) :
    ENNReal.ofReal (‖truncationIntegral μS n x‖ ^ 2) =
      ∫⁻ r, ENNReal.ofReal (‖truncationFunction n r‖ ^ 2)
        ∂μS.diagonalMeasure x := by
  exact boundedIntegral_norm_sq μS (truncationFunction_measurable n)
    (truncationFunction_bounded n) x

lemma truncationIntegral_star (μS : WOTSpectralMeasure ℝ H) (n : ℕ) :
    star (truncationIntegral μS n) = truncationIntegral μS n := by
  rw [truncationIntegral]
  have h := boundedIntegral_star μS (truncationFunction_measurable n)
    (truncationFunction_bounded n)
  symm
  calc
    boundedIntegral μS (truncationFunction n) (truncationFunction_measurable n)
        (truncationFunction_bounded n) =
        boundedIntegral μS (fun r => star (truncationFunction n r)) _ _ := by
      congr 1
      funext r
      by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
      · simp [truncationFunction, Set.indicator_of_mem hr]
      · simp [truncationFunction, Set.indicator, hr]
    _ = star (boundedIntegral μS (truncationFunction n)
        (truncationFunction_measurable n) (truncationFunction_bounded n)) := h

lemma truncationIntegral_inner_swap (μS : WOTSpectralMeasure ℝ H) (n : ℕ)
    (x y : H) :
    ⟪truncationIntegral μS n x, y⟫_ℂ = ⟪x, truncationIntegral μS n y⟫_ℂ := by
  have hstar := congrArg (fun A : H →WOT[ℂ] H => A y) (truncationIntegral_star μS n)
  rw [ContinuousLinearMapWOT.star_apply] at hstar
  exact (ContinuousLinearMap.adjoint_inner_right
    (ContinuousLinearMapWOT.toCLM (truncationIntegral μS n)) x y).symm.trans
    (by rw [← ContinuousLinearMap.star_eq_adjoint, hstar])

/-- The maximal operator obtained from a real weak spectral measure by norm convergence of bounded
truncations.  Its domain is exactly the square-moment submodule. -/
noncomputable def maximalSpectralIntegral
    (μS : WOTSpectralMeasure ℝ H) : H →ₗ.[ℂ] H :=
  LinearPMap.mk (spectralSquareMomentSubmodule μS)
    { toFun := truncationLimit μS
      map_add' := truncationLimit_add μS
      map_smul' := truncationLimit_smul μS }

lemma maximalSpectralIntegral_isSymmetric (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).IsSymmetric := by
  change (maximalSpectralIntegral μS).IsFormalAdjoint (maximalSpectralIntegral μS)
  intro x y
  have htx : Filter.Tendsto (fun n : ℕ => truncationIntegral μS n x) Filter.atTop
      (𝓝 (truncationLimit μS x)) := truncationLimit_tendsto μS x
  have hty : Filter.Tendsto (fun n : ℕ => truncationIntegral μS n y) Filter.atTop
      (𝓝 (truncationLimit μS y)) := truncationLimit_tendsto μS y
  have hxy := Filter.Tendsto.inner (𝕜 := ℂ) htx
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (y : H)) Filter.atTop
      (𝓝 (y : H)))
  have hyx := Filter.Tendsto.inner (𝕜 := ℂ)
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (x : H)) Filter.atTop
      (𝓝 (x : H))) hty
  have hseq : (fun n : ℕ => ⟪truncationIntegral μS n (x : H), (y : H)⟫_ℂ) =
      (fun n : ℕ => ⟪(x : H), truncationIntegral μS n (y : H)⟫_ℂ) := by
    funext n
    exact truncationIntegral_inner_swap μS n (x : H) (y : H)
  have hyx' := hyx
  rw [← hseq] at hyx'
  exact tendsto_nhds_unique hxy hyx'

lemma spectralCutoff_mem_spectralSquareMomentDomain
    (μS : WOTSpectralMeasure ℝ H) (x : H) {C : ℝ} (hC : 0 ≤ C) :
    μS (Set.Icc (-C) C) x ∈ OperatorAlgebra.spectralSquareMomentDomain μS := by
  let K : Set ℝ := Set.Icc (-C) C
  have hK : MeasurableSet K := measurableSet_Icc
  have hKc : MeasurableSet Kᶜ := hK.compl
  have hzero : μS Kᶜ (μS K x) = 0 := by
    have hmul : μS Kᶜ * μS K = 0 :=
      μS.comp_of_disjoint disjoint_compl_left hKc hK
    exact congrArg (fun A : H →WOT[ℂ] H => A x) hmul
  have hdiagKc : μS.diagonalMeasure (μS K x) Kᶜ = 0 := by
    rw [μS.diagonalMeasure_apply_eq_norm_sq _ _ hKc, hzero]
    simp
  rw [OperatorAlgebra.mem_spectralSquareMomentDomain_iff]
  have hK_ae : ∀ᵐ r ∂μS.diagonalMeasure (μS K x), r ∈ K := by
    rw [ae_iff]
    have hset : {r : ℝ | r ∉ K} = Kᶜ := by rfl
    rw [hset]
    exact hdiagKc
  apply Integrable.of_bound (by fun_prop) (C ^ 2)
  filter_upwards [hK_ae] with r hr
  change |r ^ 2| ≤ C ^ 2
  rw [abs_of_nonneg (sq_nonneg r)]
  exact sq_le_sq' hr.1 hr.2

lemma diagonalMeasure_cutoff_compl_tendsto_zero
    (μS : WOTSpectralMeasure ℝ H) (x : H) :
    Filter.Tendsto
      (fun n : ℕ => μS.diagonalMeasure x (spectralCutoffSet n)ᶜ)
      Filter.atTop (𝓝 0) := by
  have hμ := MeasureTheory.tendsto_measure_iUnion_atTop
    (μ := μS.diagonalMeasure x) spectralCutoffSet_mono
  have hμ' : Filter.Tendsto
      (fun n : ℕ => μS.diagonalMeasure x (spectralCutoffSet n)) Filter.atTop
      (𝓝 (μS.diagonalMeasure x Set.univ)) := by
    simpa [Function.comp_def, spectralCutoffSet_iUnion] using hμ
  have hcomp : ∀ n, μS.diagonalMeasure x (spectralCutoffSet n)ᶜ =
      μS.diagonalMeasure x Set.univ - μS.diagonalMeasure x (spectralCutoffSet n) := by
    intro n
    exact MeasureTheory.measure_compl measurableSet_Icc
      (measure_lt_top (μS.diagonalMeasure x) (spectralCutoffSet n)).ne
  have hpair : Filter.Tendsto
      (fun n : ℕ => (μS.diagonalMeasure x Set.univ,
        μS.diagonalMeasure x (spectralCutoffSet n))) Filter.atTop
      (𝓝 (μS.diagonalMeasure x Set.univ, μS.diagonalMeasure x Set.univ)) := by
    exact tendsto_const_nhds.prodMk_nhds hμ'
  have hsub' := (ENNReal.tendsto_sub
      (Or.inl (μS.diagonalMeasure_isFinite x).measure_univ_lt_top.ne)).comp hpair
  simpa [Function.comp_def, hcomp] using hsub'

lemma spectralCutoff_tendsto (μS : WOTSpectralMeasure ℝ H) (x : H) :
    Filter.Tendsto
      (fun n : ℕ => μS (spectralCutoffSet n) x) Filter.atTop (𝓝 x) := by
  apply (Metric.tendsto_atTop.2)
  intro ε hε
  have htail := (diagonalMeasure_cutoff_compl_tendsto_zero μS x).eventually
    (Iio_mem_nhds ((ENNReal.ofReal_pos).2 (sq_pos_of_pos hε)))
  rcases Filter.eventually_atTop.1 htail with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hdecomp : μS (spectralCutoffSet n) x +
      μS (spectralCutoffSet n)ᶜ x = x := by
    have h := congrArg (fun A : H →WOT[ℂ] H => A x)
      (MeasureTheory.VectorMeasure.of_union
        (v := μS.toVectorMeasure) (A := spectralCutoffSet n)
          (B := (spectralCutoffSet n)ᶜ) disjoint_compl_right measurableSet_Icc
          measurableSet_Icc.compl)
    simpa [Set.union_compl_self, μS.univ] using h.symm
  have hdiff : x - μS (spectralCutoffSet n) x =
      μS (spectralCutoffSet n)ᶜ x := by
    calc
      x - μS (spectralCutoffSet n) x =
          (μS (spectralCutoffSet n) x + μS (spectralCutoffSet n)ᶜ x) -
            μS (spectralCutoffSet n) x := by rw [hdecomp]
      _ = μS (spectralCutoffSet n)ᶜ x := by abel
  have hnormsq : ENNReal.ofReal
      (‖x - μS (spectralCutoffSet n) x‖ ^ 2) =
      μS.diagonalMeasure x (spectralCutoffSet n)ᶜ := by
    rw [hdiff]
    exact (μS.diagonalMeasure_apply_eq_norm_sq x (spectralCutoffSet n)ᶜ
      measurableSet_Icc.compl).symm
  have hlt : ENNReal.ofReal
      (‖x - μS (spectralCutoffSet n) x‖ ^ 2) < ENNReal.ofReal (ε ^ 2) := by
    rw [hnormsq]
    exact hN n hn
  have hsq : ‖x - μS (spectralCutoffSet n) x‖ ^ 2 < ε ^ 2 :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hlt
  simpa [dist_eq_norm, norm_sub_rev] using
    (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hε)).mp hsq

lemma maximalSpectralIntegral_hasDenseDomain (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).HasDenseDomain := by
  rw [LinearPMap.hasDenseDomain_def, Metric.dense_iff]
  intro x ε hε
  rcases (Metric.tendsto_atTop.1 (spectralCutoff_tendsto μS x) ε hε) with ⟨N, hN⟩
  let z := μS (spectralCutoffSet N) x
  refine ⟨z, hN N le_rfl, ?_⟩
  exact spectralCutoff_mem_spectralSquareMomentDomain μS x
    (by positivity)

lemma maximalSpectralIntegral_isClosable (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).IsClosable := by
  apply LinearPMap.isClosable_of_exists_dense_formalAdjoint
    (maximalSpectralIntegral_hasDenseDomain μS)
  exact ⟨maximalSpectralIntegral μS,
    maximalSpectralIntegral_hasDenseDomain μS,
    LinearPMap.isSymmetric_def.mp (maximalSpectralIntegral_isSymmetric μS)⟩

lemma maximalSpectralIntegral_isUnbounded (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).IsUnbounded :=
  ⟨maximalSpectralIntegral_hasDenseDomain μS,
    maximalSpectralIntegral_isClosable μS⟩

lemma maximalSpectralIntegral_closure_isClosed (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).closure.IsClosed :=
  (maximalSpectralIntegral_isClosable μS).closure_isClosed

lemma maximalSpectralIntegral_closure_isSymmetric (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).closure.IsSymmetric :=
  (maximalSpectralIntegral_isSymmetric μS).closure
    (maximalSpectralIntegral_hasDenseDomain μS)

lemma maximalSpectralIntegral_isEssentiallySelfAdjoint_iff (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).IsEssentiallySelfAdjoint ↔
      IsSelfAdjoint (maximalSpectralIntegral μS).closure := Iff.rfl

/-- The Cayley/resolvent endpoint for the canonical PVM realization.

The measure-theoretic construction supplies symmetry and density.  Once a concrete argument proves
that both shifted operators have full range, the standard von Neumann range criterion turns the
canonical realization itself into a self-adjoint operator.  This is the reusable interface for
ODE, Nelson, and multiplication-model proofs of essential self-adjointness. -/
lemma maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top
    (μS : WOTSpectralMeasure ℝ H)
    (hadd : (maximalSpectralIntegral μS + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤)
    (hsub : (maximalSpectralIntegral μS - Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤) :
    IsSelfAdjoint (maximalSpectralIntegral μS) := by
  exact LinearPMap.IsSymmetric.isSelfAdjoint_of_range_eq_top
    (maximalSpectralIntegral_isSymmetric μS)
    (maximalSpectralIntegral_hasDenseDomain μS) hadd hsub

/-- The closure of the canonical PVM realization is self-adjoint under the same resolvent
surjectivity hypotheses.  The stronger conclusion is exposed separately because downstream
models usually start with an operator on a smaller core and identify its closure with this
canonical realization. -/
lemma maximalSpectralIntegral_closure_eq_self
    (μS : WOTSpectralMeasure ℝ H)
    (hadd : (maximalSpectralIntegral μS + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤)
    (hsub : (maximalSpectralIntegral μS - Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤) :
    (maximalSpectralIntegral μS).closure = maximalSpectralIntegral μS := by
  have hself := maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top μS hadd hsub
  exact hself.isClosed.closure_eq

lemma maximalSpectralIntegral_isEssentiallySelfAdjoint_of_range_eq_top
    (μS : WOTSpectralMeasure ℝ H)
    (hadd : (maximalSpectralIntegral μS + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤)
    (hsub : (maximalSpectralIntegral μS - Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤) :
    (maximalSpectralIntegral μS).IsEssentiallySelfAdjoint := by
  rw [maximalSpectralIntegral_isEssentiallySelfAdjoint_iff]
  rw [maximalSpectralIntegral_closure_eq_self μS hadd hsub]
  exact maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top μS hadd hsub

lemma maximalSpectralIntegral_norm_sq (μS : WOTSpectralMeasure ℝ H)
    (x : H) (hx : x ∈ (maximalSpectralIntegral μS).domain) :
    ENNReal.ofReal (‖(maximalSpectralIntegral μS) ⟨x, hx⟩‖ ^ 2) =
      ∫⁻ r, ENNReal.ofReal (r ^ 2) ∂μS.diagonalMeasure x := by
  let xd : spectralSquareMomentSubmodule μS := ⟨x, hx⟩
  have hvec := truncationLimit_tendsto μS xd
  have hnorm : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (‖truncationIntegral μS n x‖ ^ 2))
      Filter.atTop (𝓝 (ENNReal.ofReal (‖truncationLimit μS xd‖ ^ 2))) := by
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((continuous_norm.pow 2).continuousAt.tendsto.comp hvec)
  have hleft : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (‖truncationIntegral μS n x‖ ^ 2))
      Filter.atTop (𝓝 (∫⁻ r, ENNReal.ofReal (r ^ 2) ∂μS.diagonalMeasure x)) := by
    convert truncation_norm_lintegral_tendsto μS x xd.property using 1
    funext n
    exact truncationIntegral_norm_sq μS n x
  have heq := tendsto_nhds_unique hnorm hleft
  simpa [maximalSpectralIntegral, xd] using heq

@[simp] lemma maximalSpectralIntegral_domain (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).domain = spectralSquareMomentSubmodule μS := rfl

lemma maximalSpectralIntegral_apply (μS : WOTSpectralMeasure ℝ H)
    (x : H) (hx : x ∈ (maximalSpectralIntegral μS).domain) :
    (maximalSpectralIntegral μS) ⟨x, hx⟩ = truncationLimit μS ⟨x, hx⟩ := rfl

lemma scalarMeasure_inner_projection (μS : WOTSpectralMeasure ℝ H)
    (x y : H) (S : Set ℝ) (hS : MeasurableSet S) :
    ⟪y, μS S x⟫_ℂ = ⟪μS S y, μS S x⟫_ℂ := by
  let p : H →L[ℂ] H := ContinuousLinearMapWOT.toCLM (μS S)
  have hmul : p * p = p := by
    exact congrArg ContinuousLinearMapWOT.toCLM (μS.isStarProjection S).isIdempotentElem
  have hstar : ContinuousLinearMap.adjoint p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM (μS.isStarProjection S).isSelfAdjoint
  change ⟪y, p x⟫_ℂ = ⟪p y, p x⟫_ℂ
  calc
    ⟪y, p x⟫_ℂ = ⟪ContinuousLinearMap.adjoint p y, x⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_left p x y).symm
    _ = ⟪p y, x⟫_ℂ := by rw [hstar]
    _ = ⟪p y, p x⟫_ℂ := by
      have h := ContinuousLinearMap.adjoint_inner_right p (p y) x
      rw [hstar] at h
      have hpy : p (p y) = p y := by
        exact congrArg (fun q : H →L[ℂ] H => q y) hmul
      rw [hpy] at h
      exact h.symm

lemma scalarMeasure_variation_le_diagonal_add (μS : WOTSpectralMeasure ℝ H)
    (x y : H) :
    (μS.scalarMeasure x y).variation ≤ μS.diagonalMeasure x + μS.diagonalMeasure y := by
  apply MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le
  intro S hS
  rw [μS.scalarMeasure_apply x y S]
  rw [← ofReal_norm]
  rw [MeasureTheory.Measure.add_apply _ _ S, μS.diagonalMeasure_apply_eq_norm_sq x S hS,
    μS.diagonalMeasure_apply_eq_norm_sq y S hS]
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hinner := norm_inner_le_norm (𝕜 := ℂ) (μS S y) (μS S x)
  have hproj := scalarMeasure_inner_projection μS x y S hS
  rw [hproj]
  nlinarith [sq_nonneg ‖μS S y‖, sq_nonneg ‖μS S x‖]

lemma scalarMeasure_isFiniteVariation (μS : WOTSpectralMeasure ℝ H)
    (x y : H) : IsFiniteMeasure (μS.scalarMeasure x y).variation := by
  apply MeasureTheory.isFiniteMeasure_of_le
    (μS.diagonalMeasure x + μS.diagonalMeasure y)
  exact scalarMeasure_variation_le_diagonal_add μS x y

lemma truncationIntegral_inner_tendsto_weakIntegral
    (μS : WOTSpectralMeasure ℝ H) (x y : H)
    (hfi : (μS.scalarMeasure x y).Integrable id) :
    Filter.Tendsto
      (fun n : ℕ => ∫ᵛ r, realTruncationFunction n r ∂[
        ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μS.scalarMeasure x y])
      Filter.atTop (𝓝 (μS.weakIntegral id x y)) := by
  let ν := μS.scalarMeasure x y
  letI := scalarMeasure_isFiniteVariation μS x y
  have hlimit : μS.complexWeakIntegral (fun r : ℝ => (r : ℂ)) x y =
      μS.weakIntegral id x y := by
    unfold WOTSpectralMeasure.complexWeakIntegral WOTSpectralMeasure.weakIntegral
    exact (integral_real_eq_complex ν hfi).symm
  have hcomplex := truncationIntegral_inner_tendsto_complexWeakIntegral μS x y hfi
  rw [hlimit] at hcomplex
  apply hcomplex.congr'
  filter_upwards [] with n
  have htrunc : ν.Integrable (realTruncationFunction n) := by
    rcases realTruncationFunction_bounded n with ⟨C, hC⟩
    apply Integrable.of_bound
      (realTruncationFunction_measurable n).aestronglyMeasurable C
    filter_upwards [] with r
    simpa [Real.norm_eq_abs] using hC r
  have hreal := integral_real_eq_complex ν htrunc
  calc
    ∫ᵛ r, truncationFunction n r ∂[
        ContinuousLinearMap.lsmul ℝ ℂ; ν] =
        ∫ᵛ r, Complex.ofRealCLM (realTruncationFunction n r) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ; ν] := by
      have hfun : (fun r => truncationFunction n r) =
          (fun r => Complex.ofRealCLM (realTruncationFunction n r)) := by
        funext r
        simpa [Complex.ofRealCLM_apply] using
          congrFun (realTruncationFunction_complex_eq n).symm r
      exact congrArg (fun f : ℝ → ℂ =>
        ∫ᵛ r, f r ∂[ContinuousLinearMap.lsmul ℝ ℂ; ν]) hfun
    _ = ∫ᵛ r, realTruncationFunction n r ∂[
        ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); ν] := hreal.symm

lemma boundedIntegral_inner
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μS : WOTSpectralMeasure α H) {f : α → ℂ} (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C) (x y : H)
    (hfinite : IsFiniteMeasure (μS.scalarMeasure x y).variation) :
    ⟪y, boundedIntegral μS f hf hfb x⟫_ℂ =
      ∫ᵛ a, f a ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μS.scalarMeasure x y] := by
  let s : ℕ → SimpleFunc α ℂ :=
    Classical.choose (exists_uniform_simple_approx hf hfb)
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ a, ‖s n a - f a‖ < ε :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hfb)).1
  have hsBound : ∃ C : ℝ, ∀ n a, ‖s n a‖ ≤ C :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hfb)).2
  rw [boundedIntegral_eq_of_uniform_approx μS hf hfb hs]
  exact boundedIntegralOfUniformApprox_inner μS hs hsBound x y hfinite

lemma truncationIntegral_inner (μS : WOTSpectralMeasure ℝ H) (n : ℕ)
    (x y : H) :
    ⟪y, truncationIntegral μS n x⟫_ℂ =
      ∫ᵛ r, truncationFunction n r ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μS.scalarMeasure x y] := by
  exact boundedIntegral_inner μS (truncationFunction_measurable n)
    (truncationFunction_bounded n) x y (scalarMeasure_isFiniteVariation μS x y)

lemma maximalSpectralIntegral_weak_truncation_reconstruction
    (μS : WOTSpectralMeasure ℝ H) (x : H)
    (hx : x ∈ (maximalSpectralIntegral μS).domain) (y : H) :
    Filter.Tendsto
      (fun n : ℕ => ∫ᵛ r, truncationFunction n r ∂[
        ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); μS.scalarMeasure x y])
      Filter.atTop (𝓝 (⟪y, (maximalSpectralIntegral μS) ⟨x, hx⟩⟫_ℂ)) := by
  have hvec := truncationLimit_tendsto μS
    (⟨x, hx⟩ : spectralSquareMomentSubmodule μS)
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ)
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (y : H)) Filter.atTop (𝓝 y)) hvec
  have hinner' : Filter.Tendsto
      (fun n : ℕ => ⟪y, truncationIntegral μS n x⟫_ℂ) Filter.atTop
      (𝓝 (⟪y, (maximalSpectralIntegral μS) ⟨x, hx⟩⟫_ℂ)) := by
    simpa [maximalSpectralIntegral, truncationLimit] using hinner
  apply hinner'.congr'
  filter_upwards [] with n
  exact truncationIntegral_inner μS n x y

/-! ### Measurable real functional calculus

The maximal construction is not tied to the coordinate function.  For a measurable real
multiplier `f`, push the PVM forward along `f` and apply the same construction to the new
spectral variable.  This is the concrete operator realization of the representation-free
`PVM.map` operation used by the affiliated-observable API. -/

/-- The maximal unbounded operator obtained by integrating a measurable real function against a
weak spectral measure.  It is defined by PVM pushforward, so no second truncation construction is
needed for each multiplier. -/
noncomputable def measurableSpectralIntegral (μS : WOTSpectralMeasure ℝ H)
    (f : ℝ → ℝ) (hf : Measurable f) : H →ₗ.[ℂ] H :=
  maximalSpectralIntegral (μS.map f hf)

@[simp]
theorem measurableSpectralIntegral_id (μS : WOTSpectralMeasure ℝ H) :
    measurableSpectralIntegral μS id measurable_id = maximalSpectralIntegral μS := by
  unfold measurableSpectralIntegral
  rw [μS.map_id]

lemma measurableSpectralIntegral_comp
    (μS : WOTSpectralMeasure ℝ H) (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    measurableSpectralIntegral (μS.map f hf) g hg =
      measurableSpectralIntegral μS (g ∘ f) (hg.comp hf) := by
  change maximalSpectralIntegral ((μS.map f hf).map g hg) =
    maximalSpectralIntegral (μS.map (g ∘ f) (hg.comp hf))
  apply congrArg maximalSpectralIntegral
  exact WOTSpectralMeasure.map_map (μS := μS) (f := f) (g := g) hf hg

@[simp]
lemma measurableSpectralIntegral_domain (μS : WOTSpectralMeasure ℝ H)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (measurableSpectralIntegral μS f hf).domain =
      spectralSquareMomentSubmodule (μS.map f hf) := by
  rfl

/-- The domain of `∫ f dE` is exactly the square-integrability domain of `f` against every
vector-state spectral measure. -/
lemma mem_measurableSpectralIntegral_domain_iff (μS : WOTSpectralMeasure ℝ H)
    (f : ℝ → ℝ) (hf : Measurable f) (x : H) :
    x ∈ (measurableSpectralIntegral μS f hf).domain ↔
      Integrable (fun r : ℝ => f r ^ 2) (μS.diagonalMeasure x) := by
  change x ∈ OperatorAlgebra.spectralSquareMomentDomain (μS.map f hf) ↔ _
  rw [OperatorAlgebra.mem_spectralSquareMomentDomain_iff,
    μS.diagonalMeasure_map f hf]
  have h := integrable_map_measure (μ := μS.diagonalMeasure x)
    ((measurable_id.pow_const 2).aestronglyMeasurable) hf.aemeasurable
  simpa [Function.comp_def] using h

/-- A bounded measurable real multiplier has no unbounded domain restriction.  This is the
bounded-to-unbounded boundary in the reusable calculus: the same pushforward construction handles
both cases, and boundedness turns its square-moment domain into `⊤`. -/
lemma measurableSpectralIntegral_domain_eq_top_of_bounded
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |f r| ≤ C) :
    (measurableSpectralIntegral μS f hf).domain = ⊤ := by
  apply Submodule.eq_top_iff'.2
  intro x
  rw [mem_measurableSpectralIntegral_domain_iff μS f hf x]
  rcases hfb with ⟨C, hC, hfb⟩
  apply Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable (C ^ 2)
  filter_upwards [] with r
  simpa [Real.norm_eq_abs, abs_pow] using
    (sq_le_sq₀ (abs_nonneg (f r)) hC).2 (hfb r)

/-- Weak reconstruction for a measurable real multiplier.  The only integrability assumption is
the natural one on the original scalar spectral measure; the pushforward identity transports it
to the coordinate function of the new PVM. -/
lemma measurableSpectralIntegral_inner_eq_complexWeakIntegral
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f)
    (x : H) (hx : x ∈ (measurableSpectralIntegral μS f hf).domain) (y : H)
    (hfi : (μS.scalarMeasure x y).Integrable f) :
    ⟪y, (measurableSpectralIntegral μS f hf) ⟨x, hx⟩⟫_ℂ =
      μS.complexWeakIntegral (fun r : ℝ => (f r : ℂ)) x y := by
  have hfi' : ((μS.map f hf).scalarMeasure x y).Integrable id := by
    rw [μS.scalarMeasure_map f hf]
    have h := VectorMeasure.Integrable.map
      (measurable_id.aestronglyMeasurable) hfi
    simpa [Function.comp_def] using h
  have hmax := maximalSpectralIntegral_weak_truncation_reconstruction
    (μS.map f hf) x hx y
  have hlim := truncationIntegral_inner_tendsto_complexWeakIntegral
    (μS.map f hf) x y hfi'
  have hinner :
      ⟪y, (maximalSpectralIntegral (μS.map f hf)) ⟨x, hx⟩⟫_ℂ =
        (μS.map f hf).complexWeakIntegral (fun r : ℝ => (r : ℂ)) x y :=
    tendsto_nhds_unique hmax hlim
  have hfiC : (μS.scalarMeasure x y).Integrable (fun r : ℝ => (f r : ℂ)) := by
    exact hfi.ofReal
  have hmap := μS.complexWeakIntegral_map f hf
    (fun r : ℝ => (r : ℂ)) x y
    Complex.measurable_ofReal.aestronglyMeasurable hfiC
  simpa [measurableSpectralIntegral, Function.comp_def] using hinner.trans hmap

/-- On bounded real multipliers, the bounded WOT integral and the maximal unbounded
realization are the same operator.  This is the concrete bridge between the bounded Borel
calculus and the square-moment construction; the proof is by matrix coefficients, using the
bounded integral's weak integral formula and the measurable multiplier reconstruction theorem. -/
theorem boundedIntegral_ofReal_eq_measurableSpectralIntegral
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |f r| ≤ C) (x : H) :
    boundedIntegral μS (fun r : ℝ => (f r : ℂ))
        (Complex.measurable_ofReal.comp hf)
        (by
          rcases hfb with ⟨C, hC, hCbound⟩
          exact ⟨C, fun r => by
            simpa [Complex.norm_real, Real.norm_eq_abs] using hCbound r⟩) x =
      (measurableSpectralIntegral μS f hf)
        ⟨x, by
          rw [measurableSpectralIntegral_domain_eq_top_of_bounded μS f hf hfb]
          exact Submodule.mem_top⟩ := by
  apply ext_inner_left ℂ
  intro y
  letI : IsFiniteMeasure (μS.scalarMeasure x y).variation :=
    scalarMeasure_isFiniteVariation μS x y
  have hfi : (μS.scalarMeasure x y).Integrable f := by
    rcases hfb with ⟨C, hC, hCbound⟩
    have hnorm : ∀ r : ℝ, ‖f r‖ ≤ C := by
      intro r
      simpa [Real.norm_eq_abs] using hCbound r
    apply Integrable.of_bound hf.aestronglyMeasurable C
    exact Filter.Eventually.of_forall hnorm
  have hbounded := boundedIntegral_inner μS
    (Complex.measurable_ofReal.comp hf)
    (by
      rcases hfb with ⟨C, hC, hCbound⟩
      exact ⟨C, fun r => by
        simpa [Complex.norm_real, Real.norm_eq_abs] using hCbound r⟩) x y
      (scalarMeasure_isFiniteVariation μS x y)
  have hunbounded := measurableSpectralIntegral_inner_eq_complexWeakIntegral μS f hf x
    (by
      rw [measurableSpectralIntegral_domain_eq_top_of_bounded μS f hf hfb]
      exact Submodule.mem_top) y hfi
  exact hbounded.trans hunbounded.symm

/-! ### Convergence of bounded spectral multipliers

The next lemma is the reusable norm-convergence principle behind the resolvent construction.  It
only uses the PVM norm-square identity, so it is also useful for bounded functional calculus
approximations unrelated to the Cayley transform.
-/

lemma boundedIntegral_tendsto_of_pointwise_tendsto_of_bound
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μS : WOTSpectralMeasure α H)
    {f : α → ℂ} {g : ℕ → α → ℂ} (x : H)
    (hf : Measurable f) (hg : ∀ n, Measurable (g n))
    (hfb : ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C)
    (hgb : ∃ C : ℝ, ∀ n a, ‖g n a‖ ≤ C)
    (hlim : ∀ a, Filter.Tendsto (fun n => g n a) Filter.atTop (𝓝 (f a))) :
    Filter.Tendsto
      (fun n => boundedIntegral μS (g n) (hg n) (by
        rcases hgb with ⟨C, hC⟩
        exact ⟨C, hC n⟩) x)
      Filter.atTop
      (𝓝 (boundedIntegral μS f hf hfb x)) := by
  have hfb_keep := hfb
  rcases hfb with ⟨Cf, hCf⟩
  rcases hgb with ⟨Cg, hCg⟩
  let C : ℝ := max Cf Cg
  have hC0 : 0 ≤ C := by
    let a₀ : α := Classical.choice (inferInstance : Nonempty α)
    exact (norm_nonneg (f a₀)).trans ((hCf a₀).trans (le_max_left _ _))
  have hCfC : ∀ a, ‖f a‖ ≤ C := fun a => (hCf a).trans (le_max_left _ _)
  have hCgC : ∀ n a, ‖g n a‖ ≤ C := fun n a => (hCg n a).trans (le_max_right _ _)
  let μ : Measure α := μS.diagonalMeasure x
  let F : ℕ → α → ENNReal := fun n a =>
    ENNReal.ofReal (‖g n a - f a‖ ^ 2)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    exact ENNReal.continuous_ofReal.measurable.comp
      (((hg n).sub hf).norm.pow_const 2)
  have hbound : ∀ n, ∀ᵐ a ∂μ, F n a ≤ ENNReal.ofReal ((2 * C) ^ 2) := by
    intro n
    filter_upwards [] with a
    dsimp [F]
    apply ENNReal.ofReal_le_ofReal
    have hnorm : ‖g n a - f a‖ ≤ 2 * C := by
      exact (norm_sub_le _ _).trans (by linarith [hCgC n a, hCfC a])
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  have hfin : (∫⁻ a, ENNReal.ofReal ((2 * C) ^ 2) ∂μ) ≠ (⊤ : ENNReal) := by
    rw [lintegral_const, μS.diagonalMeasure_univ]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.ofReal_ne_top
  have hpoint : ∀ᵐ a ∂μ,
      Filter.Tendsto (fun n : ℕ => F n a) Filter.atTop (𝓝 0) := by
    filter_upwards [] with a
    have hdiff : Filter.Tendsto (fun n : ℕ => g n a - f a)
        Filter.atTop (𝓝 0) := by
      simpa using (hlim a).sub (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => f a) Filter.atTop (𝓝 (f a)))
    have hnorm : Filter.Tendsto (fun n : ℕ => ‖g n a - f a‖ ^ 2)
        Filter.atTop (𝓝 (0 ^ 2)) := by
      convert (continuous_norm.pow 2).continuousAt.tendsto.comp hdiff using 1
      congr 1
      norm_num
    change Filter.Tendsto (fun n : ℕ => ENNReal.ofReal
      (‖g n a - f a‖ ^ 2)) Filter.atTop (𝓝 0)
    convert ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm using 1
    simp [Function.comp_def]
    norm_num
  have hlin : Filter.Tendsto (fun n : ℕ => ∫⁻ a, F n a ∂μ)
      Filter.atTop (𝓝 0) := by
    simpa using
      (MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
        (fun _ : α => ENNReal.ofReal ((2 * C) ^ 2))
        (by filter_upwards [] with n; exact hFmeas n)
        (by filter_upwards [] with n; exact hbound n) hfin hpoint)
  have hnormsq : ∀ n, ENNReal.ofReal
      (‖boundedIntegral μS (g n) (hg n) (⟨C, hCgC n⟩) x -
        boundedIntegral μS f hf (⟨C, hCfC⟩) x‖ ^ 2) = ∫⁻ a, F n a ∂μ := by
    intro n
    have hsub := boundedIntegral_sub μS (hg n) hf (⟨C, hCgC n⟩) (⟨C, hCfC⟩)
    have heq := congrArg (fun A : H →WOT[ℂ] H => A x) hsub
    calc
      _ = ENNReal.ofReal
          (‖boundedIntegral μS (g n - f) ((hg n).sub hf) _ x‖ ^ 2) := by
        rw [heq]
        rfl
      _ = ∫⁻ a, ENNReal.ofReal (‖(g n - f) a‖ ^ 2)
          ∂μS.diagonalMeasure x := boundedIntegral_norm_sq μS ((hg n).sub hf) _ x
      _ = ∫⁻ a, F n a ∂μ := by rfl
  have hnorm : Filter.Tendsto (fun n : ℕ =>
      ‖boundedIntegral μS (g n) (hg n) (⟨C, hCgC n⟩) x -
        boundedIntegral μS f hf (⟨C, hCfC⟩) x‖) Filter.atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hsmall := hlin.eventually (Iio_mem_nhds
      ((ENNReal.ofReal_pos).2 (sq_pos_of_pos hε)))
    rcases Filter.eventually_atTop.1 hsmall with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have hlt : ENNReal.ofReal
        (‖boundedIntegral μS (g n) (hg n) (⟨C, hCgC n⟩) x -
          boundedIntegral μS f hf (⟨C, hCfC⟩) x‖ ^ 2) <
        ENNReal.ofReal (ε ^ 2) := by
      rw [hnormsq n]
      exact hN n hn
    have hsq : ‖boundedIntegral μS (g n) (hg n) (⟨C, hCgC n⟩) x -
        boundedIntegral μS f hf (⟨C, hCfC⟩) x‖ ^ 2 < ε ^ 2 :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hlt
    simpa [dist_eq_norm] using
      (sq_lt_sq₀ (norm_nonneg _) (le_of_lt hε)).mp hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  convert hnorm using 1

/-! ### Weighted diagonal measures

Applying a bounded spectral multiplier changes the vector spectral measure by the squared
multiplier.  This is the measure-level statement that turns bounded resolvents into vectors in the
maximal square-moment domain.
-/

lemma diagonalMeasure_boundedIntegral_eq_withDensity
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μS : WOTSpectralMeasure α H) {g : α → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C) (x : H) :
    μS.diagonalMeasure (boundedIntegral μS g hg hgb x) =
      Measure.withDensity (μS.diagonalMeasure x)
        (fun a => ENNReal.ofReal (‖g a‖ ^ 2)) := by
  apply Measure.ext
  intro S hS
  rw [μS.diagonalMeasure_apply_eq_norm_sq _ _ hS]
  let iS : α → ℂ := S.indicator (fun _ => (1 : ℂ))
  have hiS : Measurable iS := measurable_const.indicator hS
  have hiSb : ∃ C : ℝ, ∀ a, ‖iS a‖ ≤ C := by
    refine ⟨1, fun a => ?_⟩
    by_cases ha : a ∈ S <;> simp [iS, ha]
  have hmul := boundedIntegral_mul μS hiS hg hiSb hgb
  have hind := boundedIntegral_indicator μS hS
  have happly : μS S (boundedIntegral μS g hg hgb x) =
      boundedIntegral μS (iS * g) (hiS.mul hg)
        (by
          rcases hiSb with ⟨Ci, hCi⟩
          rcases hgb with ⟨Cg, hCg⟩
          refine ⟨Ci * Cg, fun a => ?_⟩
          rw [Pi.mul_apply, norm_mul]
          exact mul_le_mul (hCi a) (hCg a) (norm_nonneg _) (by
            exact (norm_nonneg (iS (Classical.choice (inferInstance : Nonempty α)))).trans
              (hCi _))) x := by
    rw [← hind]
    have h := congrArg (fun A : H →WOT[ℂ] H => A x) hmul
    simpa [ContinuousLinearMapWOT.mul_apply, iS] using h.symm
  rw [happly]
  rw [boundedIntegral_norm_sq μS (hiS.mul hg) _ x]
  rw [MeasureTheory.withDensity_apply _ hS]
  rw [← lintegral_indicator hS]
  congr 1
  funext a
  by_cases ha : a ∈ S
  · simp [iS, ha]
  · simp [iS, ha]

lemma expIntegral_mem_spectralSquareMomentDomain
    (μS : WOTSpectralMeasure ℝ H) (t : ℝ) (x : H)
    (hx : x ∈ OperatorAlgebra.spectralSquareMomentDomain μS) :
    expIntegral μS t x ∈ OperatorAlgebra.spectralSquareMomentDomain μS := by
  rw [OperatorAlgebra.mem_spectralSquareMomentDomain_iff] at hx ⊢
  have hmeasure : μS.diagonalMeasure (expIntegral μS t x) = μS.diagonalMeasure x := by
    rw [show expIntegral μS t x =
        boundedIntegral μS (expFunction t) (expFunction_measurable t)
          (expFunction_bounded t) x by rfl]
    rw [diagonalMeasure_boundedIntegral_eq_withDensity μS
      (expFunction_measurable t) (expFunction_bounded t) x]
    apply Measure.ext
    intro S hS
    rw [MeasureTheory.withDensity_apply _ hS]
    simp only [expFunction_modulus]
    norm_num [MeasureTheory.setLIntegral_one]
  rw [hmeasure]
  exact hx

lemma boundedMultiplier_mem_spectralSquareMomentDomain
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μS : WOTSpectralMeasure ℝ H) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hcoord : ∀ a : ℝ, ‖(a : ℂ) * g a‖ ≤ 1) (x : H) :
    boundedIntegral μS g hg hgb x ∈ OperatorAlgebra.spectralSquareMomentDomain μS := by
  rw [OperatorAlgebra.mem_spectralSquareMomentDomain_iff]
  rw [diagonalMeasure_boundedIntegral_eq_withDensity μS hg hgb x]
  let d : ℝ → ENNReal := fun a => ENNReal.ofReal (‖g a‖ ^ 2)
  have hd : Measurable d := ENNReal.continuous_ofReal.measurable.comp
    (hg.norm.pow_const 2)
  have hd_top : ∀ᵐ a ∂μS.diagonalMeasure x, d a < (⊤ : ENNReal) := by
    filter_upwards [] with a
    exact (lt_top_iff_ne_top).2 (ENNReal.ofReal_ne_top)
  apply (integrable_withDensity_iff_integrable_smul₀' hd.aemeasurable hd_top).2
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [] with a
  have hsq : ‖(a : ℂ) * g a‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr (hcoord a)
  rw [show d a = ENNReal.ofReal (‖g a‖ ^ 2) by rfl]
  rw [ENNReal.toReal_ofReal (sq_nonneg (‖g a‖))]
  simp only [smul_eq_mul, abs_of_nonneg (sq_nonneg a)]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sq_nonneg (‖g a‖)) (sq_nonneg a))]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hsq
  nlinarith [sq_abs a]

/-! The unit bound used by the first resolvent construction is convenient, but it is not
mathematically essential.  Keeping the finite-bound version separate makes the later general
resolvent API usable at arbitrary non-real parameters without weakening any of the existing
callers. -/

lemma boundedMultiplier_mem_spectralSquareMomentDomain_of_bound
    {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μS : WOTSpectralMeasure ℝ H) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hcoord : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, ‖(a : ℂ) * g a‖ ≤ C) (x : H) :
    boundedIntegral μS g hg hgb x ∈ OperatorAlgebra.spectralSquareMomentDomain μS := by
  rw [OperatorAlgebra.mem_spectralSquareMomentDomain_iff]
  rw [diagonalMeasure_boundedIntegral_eq_withDensity μS hg hgb x]
  let d : ℝ → ENNReal := fun a => ENNReal.ofReal (‖g a‖ ^ 2)
  have hd : Measurable d := ENNReal.continuous_ofReal.measurable.comp
    (hg.norm.pow_const 2)
  have hd_top : ∀ᵐ a ∂μS.diagonalMeasure x, d a < (⊤ : ENNReal) := by
    filter_upwards [] with a
    exact (lt_top_iff_ne_top).2 (ENNReal.ofReal_ne_top)
  apply (integrable_withDensity_iff_integrable_smul₀' hd.aemeasurable hd_top).2
  rcases hcoord with ⟨C, hC0, hC⟩
  apply Integrable.of_bound (by fun_prop) (C ^ 2)
  filter_upwards [] with a
  have hsq : ‖(a : ℂ) * g a‖ ^ 2 ≤ C ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) hC0).mpr (hC a)
  rw [show d a = ENNReal.ofReal (‖g a‖ ^ 2) by rfl]
  rw [ENNReal.toReal_ofReal (sq_nonneg (‖g a‖))]
  simp only [smul_eq_mul, abs_of_nonneg (sq_nonneg a)]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sq_nonneg (‖g a‖)) (sq_nonneg a))]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hsq
  nlinarith [sq_abs a]

lemma maximalSpectralIntegral_apply_boundedMultiplier
    (μS : WOTSpectralMeasure ℝ H) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hcoord : ∀ a : ℝ, ‖(a : ℂ) * g a‖ ≤ 1)
    (hcoord_meas : Measurable (fun a : ℝ => (a : ℂ) * g a))
    (x : H) :
    (maximalSpectralIntegral μS)
        ⟨boundedIntegral μS g hg hgb x,
          boundedMultiplier_mem_spectralSquareMomentDomain (α := ℝ) μS hg hgb hcoord x⟩ =
      boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a) hcoord_meas
        ⟨1, hcoord⟩ x := by
  let y : H := boundedIntegral μS g hg hgb x
  have hy : y ∈ OperatorAlgebra.spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain (α := ℝ) μS hg hgb hcoord x
  let fn : ℕ → ℝ → ℂ := fun n a => truncationFunction n a * g a
  have hfn : ∀ n, Measurable (fn n) := by
    intro n
    exact (truncationFunction_measurable n).mul hg
  have hfn_bound_one : ∀ n a, ‖fn n a‖ ≤ (1 : ℝ) := by
    intro n a
    change ‖truncationFunction n a * g a‖ ≤ 1
    by_cases ha : a ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
    · rw [show truncationFunction n a = (a : ℂ) by
        simp [truncationFunction, Set.indicator_of_mem ha]]
      exact hcoord a
    · simp [truncationFunction, ha]
  have hfn_bound : ∀ n, ∃ C : ℝ, ∀ a, ‖fn n a‖ ≤ C := by
    intro n
    exact ⟨1, hfn_bound_one n⟩
  have hfn_lim : ∀ a : ℝ, Filter.Tendsto (fun n : ℕ => fn n a)
      Filter.atTop (𝓝 ((a : ℂ) * g a)) := by
    intro a
    have htrunc := truncationFunction_tendsto a
    exact htrunc.mul (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => g a) Filter.atTop (𝓝 (g a)))
  have hconv : Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS (fn n) (hfn n) (hfn_bound n) x)
      Filter.atTop
      (𝓝 (boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a)
        hcoord_meas ⟨1, hcoord⟩ x)) :=
    boundedIntegral_tendsto_of_pointwise_tendsto_of_bound μS x hcoord_meas hfn
      ⟨1, hcoord⟩ ⟨1, hfn_bound_one⟩ hfn_lim
  have htrunc : Filter.Tendsto
      (fun n : ℕ => truncationIntegral μS n y) Filter.atTop (𝓝 (truncationLimit μS ⟨y, hy⟩)) :=
    truncationLimit_tendsto μS ⟨y, hy⟩
  have heq : ∀ n, truncationIntegral μS n y = boundedIntegral μS (fn n)
      (hfn n) (hfn_bound n) x := by
    intro n
    have hmul := boundedIntegral_mul μS (truncationFunction_measurable n) hg
      (truncationFunction_bounded n) hgb
    have happly := congrArg (fun A : H →WOT[ℂ] H => A x) hmul
    change truncationIntegral μS n (boundedIntegral μS g hg hgb x) = _
    change truncationIntegral μS n (boundedIntegral μS g hg hgb x) =
      boundedIntegral μS (truncationFunction n * g) (hfn n) (hfn_bound n) x
    convert happly.symm using 1 <;>
      simp [truncationIntegral, fn, ContinuousLinearMapWOT.mul_apply]
  have htrunc' : Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS (fn n) (hfn n) (hfn_bound n) x) Filter.atTop
      (𝓝 (maximalSpectralIntegral μS ⟨y, hy⟩)) := by
    change Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS (fn n) (hfn n) (hfn_bound n) x) Filter.atTop
      (𝓝 (truncationLimit μS ⟨y, hy⟩))
    exact htrunc.congr' (Filter.Eventually.of_forall fun n => heq n)
  exact tendsto_nhds_unique htrunc' hconv

lemma maximalSpectralIntegral_apply_boundedMultiplier_of_bound
    (μS : WOTSpectralMeasure ℝ H) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hcoord : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, ‖(a : ℂ) * g a‖ ≤ C)
    (hcoord_meas : Measurable (fun a : ℝ => (a : ℂ) * g a))
    (x : H) :
    (maximalSpectralIntegral μS)
        ⟨boundedIntegral μS g hg hgb x,
          boundedMultiplier_mem_spectralSquareMomentDomain_of_bound
            (α := ℝ) μS hg hgb hcoord x⟩ =
      boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a) hcoord_meas
        (by
          rcases hcoord with ⟨C, hC0, hC⟩
          exact ⟨C, hC⟩) x := by
  rcases hcoord with ⟨C, hC0, hcoord⟩
  let y : H := boundedIntegral μS g hg hgb x
  have hy : y ∈ OperatorAlgebra.spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain_of_bound (α := ℝ) μS hg hgb
      ⟨C, hC0, hcoord⟩ x
  let fn : ℕ → ℝ → ℂ := fun n a => truncationFunction n a * g a
  have hfn : ∀ n, Measurable (fn n) := by
    intro n
    exact (truncationFunction_measurable n).mul hg
  have hfn_bound_C : ∀ n a, ‖fn n a‖ ≤ C := by
    intro n a
    change ‖truncationFunction n a * g a‖ ≤ C
    by_cases ha : a ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
    · rw [show truncationFunction n a = (a : ℂ) by
        simp [truncationFunction, Set.indicator_of_mem ha]]
      exact hcoord a
    · simp [truncationFunction, ha, hC0]
  have hfn_bound : ∀ n, ∃ C' : ℝ, ∀ a, ‖fn n a‖ ≤ C' := by
    intro n
    exact ⟨C, hfn_bound_C n⟩
  have hfn_lim : ∀ a : ℝ, Filter.Tendsto (fun n : ℕ => fn n a)
      Filter.atTop (𝓝 ((a : ℂ) * g a)) := by
    intro a
    have htrunc := truncationFunction_tendsto a
    exact htrunc.mul (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℕ => g a) Filter.atTop (𝓝 (g a)))
  have hconv : Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS (fn n) (hfn n) (hfn_bound n) x)
      Filter.atTop
      (𝓝 (boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a) hcoord_meas
        ⟨C, hcoord⟩ x)) :=
    boundedIntegral_tendsto_of_pointwise_tendsto_of_bound μS x hcoord_meas hfn
      ⟨C, hcoord⟩ ⟨C, hfn_bound_C⟩ hfn_lim
  have htrunc : Filter.Tendsto
      (fun n : ℕ => truncationIntegral μS n y) Filter.atTop
      (𝓝 (truncationLimit μS ⟨y, hy⟩)) :=
    truncationLimit_tendsto μS ⟨y, hy⟩
  have heq : ∀ n, truncationIntegral μS n y = boundedIntegral μS (fn n)
      (hfn n) (hfn_bound n) x := by
    intro n
    have hmul := boundedIntegral_mul μS (truncationFunction_measurable n) hg
      (truncationFunction_bounded n) hgb
    have happly := congrArg (fun A : H →WOT[ℂ] H => A x) hmul
    change truncationIntegral μS n (boundedIntegral μS g hg hgb x) = _
    change truncationIntegral μS n (boundedIntegral μS g hg hgb x) =
      boundedIntegral μS (truncationFunction n * g) (hfn n) (hfn_bound n) x
    convert happly.symm using 1 <;>
      simp [truncationIntegral, fn, ContinuousLinearMapWOT.mul_apply]
  have htrunc' : Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS (fn n) (hfn n) (hfn_bound n) x) Filter.atTop
      (𝓝 (maximalSpectralIntegral μS ⟨y, hy⟩)) := by
    change Filter.Tendsto
      (fun n : ℕ => boundedIntegral μS (fn n) (hfn n) (hfn_bound n) x) Filter.atTop
      (𝓝 (truncationLimit μS ⟨y, hy⟩))
    exact htrunc.congr' (Filter.Eventually.of_forall fun n => heq n)
  exact tendsto_nhds_unique htrunc' hconv

/-! ### The two Cayley resolvents

These are the bounded multipliers which realize the inverse of the shifts by `± i`.  Their
construction is independent of any pre-existing self-adjoint operator; it is purely the real PVM
calculus applied to the scalar functions `(r ± i)⁻¹`.
-/

def plusResolventMultiplier (r : ℝ) : ℂ := ((r : ℂ) + Complex.I)⁻¹

def minusResolventMultiplier (r : ℝ) : ℂ := ((r : ℂ) - Complex.I)⁻¹

/-- The scalar resolvent multiplier at an arbitrary non-real parameter. -/
def resolventMultiplier (z : ℂ) (r : ℝ) : ℂ := ((r : ℂ) - z)⁻¹

lemma resolventMultiplier_measurable (z : ℂ) :
    Measurable (resolventMultiplier z) := by
  unfold resolventMultiplier
  fun_prop

lemma resolventMultiplier_denom_ne_zero {z : ℂ} (hz : z.im ≠ 0) (r : ℝ) :
    (r : ℂ) - z ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  exact hz (by simpa using hi)

lemma resolventMultiplier_bounded {z : ℂ} (hz : z.im ≠ 0) :
    ∃ C : ℝ, ∀ r, ‖resolventMultiplier z r‖ ≤ C := by
  let d : ℝ := ‖(z.im : ℂ)‖
  have hd : 0 < d := by
    dsimp [d]
    exact norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr hz)
  refine ⟨d⁻¹, fun r => ?_⟩
  have hden : d ≤ ‖(r : ℂ) - z‖ := by
    dsimp [d]
    simpa [Complex.norm_real, abs_neg] using
      (Complex.abs_im_le_norm ((r : ℂ) - z))
  rw [resolventMultiplier, norm_inv]
  exact (inv_le_inv₀ (norm_pos_iff.mpr (resolventMultiplier_denom_ne_zero hz r)) hd).2 hden

lemma resolventMultiplier_coordinate_bounded {z : ℂ} (hz : z.im ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      ‖(r : ℂ) * resolventMultiplier z r‖ ≤ C := by
  let d : ℝ := ‖(z.im : ℂ)‖
  have hd : 0 < d := by
    dsimp [d]
    exact norm_pos_iff.mpr (Complex.ofReal_ne_zero.mpr hz)
  refine ⟨1 + ‖z‖ * d⁻¹, by positivity, fun r => ?_⟩
  have hdenpos : 0 < ‖(r : ℂ) - z‖ :=
    norm_pos_iff.mpr (resolventMultiplier_denom_ne_zero hz r)
  have hden : d ≤ ‖(r : ℂ) - z‖ := by
    dsimp [d]
    simpa [Complex.norm_real, abs_neg] using
      (Complex.abs_im_le_norm ((r : ℂ) - z))
  have hr : ‖(r : ℂ)‖ ≤ ‖(r : ℂ) - z‖ + ‖z‖ := by
    calc
      ‖(r : ℂ)‖ = ‖((r : ℂ) - z) + z‖ := by congr 1 <;> ring
      _ ≤ ‖(r : ℂ) - z‖ + ‖z‖ := norm_add_le _ _
  rw [resolventMultiplier, norm_mul, norm_inv]
  calc
    ‖(r : ℂ)‖ * ‖(↑r - z)‖⁻¹ ≤
        (‖(r : ℂ) - z‖ + ‖z‖) * ‖(↑r - z)‖⁻¹ :=
      mul_le_mul_of_nonneg_right hr (inv_nonneg.mpr (le_of_lt hdenpos))
    _ = 1 + ‖z‖ / ‖(r : ℂ) - z‖ := by
      field_simp
    _ ≤ 1 + ‖z‖ * d⁻¹ := by
      have hterm : ‖z‖ * ‖(r : ℂ) - z‖⁻¹ ≤ ‖z‖ * d⁻¹ :=
        mul_le_mul_of_nonneg_left ((inv_le_inv₀ hdenpos hd).2 hden)
          (norm_nonneg z)
      simpa [div_eq_mul_inv] using add_le_add_left hterm 1

lemma resolventMultiplier_coordinate_measurable (z : ℂ) :
    Measurable (fun r : ℝ => (r : ℂ) * resolventMultiplier z r) := by
  unfold resolventMultiplier
  fun_prop

lemma resolventMultiplier_identity {z : ℂ} (hz : z.im ≠ 0) (r : ℝ) :
    (r : ℂ) * resolventMultiplier z r - z * resolventMultiplier z r = 1 := by
  unfold resolventMultiplier
  rw [← sub_mul]
  have hne := resolventMultiplier_denom_ne_zero hz r
  exact mul_inv_cancel₀ hne

lemma plusResolventMultiplier_measurable :
    Measurable plusResolventMultiplier := by
  unfold plusResolventMultiplier
  fun_prop

lemma minusResolventMultiplier_measurable :
    Measurable minusResolventMultiplier := by
  unfold minusResolventMultiplier
  fun_prop

lemma plusResolventMultiplier_bounded :
    ∃ C : ℝ, ∀ r, ‖plusResolventMultiplier r‖ ≤ C := by
  refine ⟨1, fun r => ?_⟩
  have hne : (r : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hpos : 0 < ‖(r : ℂ) + Complex.I‖ := norm_pos_iff.mpr hne
  have hden : (1 : ℝ) ≤ ‖(r : ℂ) + Complex.I‖ := by
    simpa using Complex.abs_im_le_norm ((r : ℂ) + Complex.I)
  rw [plusResolventMultiplier, norm_inv]
  exact (inv_le_one₀ hpos).2 hden

lemma minusResolventMultiplier_bounded :
    ∃ C : ℝ, ∀ r, ‖minusResolventMultiplier r‖ ≤ C := by
  refine ⟨1, fun r => ?_⟩
  have hne : (r : ℂ) - Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hpos : 0 < ‖(r : ℂ) - Complex.I‖ := norm_pos_iff.mpr hne
  have hden : (1 : ℝ) ≤ ‖(r : ℂ) - Complex.I‖ := by
    simpa using Complex.abs_im_le_norm ((r : ℂ) - Complex.I)
  rw [minusResolventMultiplier, norm_inv]
  exact (inv_le_one₀ hpos).2 hden

lemma plusResolventMultiplier_coordinate_bounded :
    ∀ r : ℝ, ‖(r : ℂ) * plusResolventMultiplier r‖ ≤ 1 := by
  intro r
  have hne : (r : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hpos : 0 < ‖(r : ℂ) + Complex.I‖ := norm_pos_iff.mpr hne
  have hden : ‖(r : ℂ)‖ ≤ ‖(r : ℂ) + Complex.I‖ := by
    simpa using Complex.abs_re_le_norm ((r : ℂ) + Complex.I)
  rw [plusResolventMultiplier, norm_mul, norm_inv]
  apply (div_le_one hpos).2
  exact hden

lemma minusResolventMultiplier_coordinate_bounded :
    ∀ r : ℝ, ‖(r : ℂ) * minusResolventMultiplier r‖ ≤ 1 := by
  intro r
  have hne : (r : ℂ) - Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  have hpos : 0 < ‖(r : ℂ) - Complex.I‖ := norm_pos_iff.mpr hne
  have hden : ‖(r : ℂ)‖ ≤ ‖(r : ℂ) - Complex.I‖ := by
    simpa using Complex.abs_re_le_norm ((r : ℂ) - Complex.I)
  rw [minusResolventMultiplier, norm_mul, norm_inv]
  apply (div_le_one hpos).2
  exact hden

lemma plusResolventMultiplier_coordinate_measurable :
    Measurable (fun r : ℝ => (r : ℂ) * plusResolventMultiplier r) := by
  unfold plusResolventMultiplier
  fun_prop

lemma minusResolventMultiplier_coordinate_measurable :
    Measurable (fun r : ℝ => (r : ℂ) * minusResolventMultiplier r) := by
  unfold minusResolventMultiplier
  fun_prop

lemma maximalSpectralIntegral_shift_range_of_multiplier
    (μS : WOTSpectralMeasure ℝ H) (c : ℂ) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hcoord : ∀ a : ℝ, ‖(a : ℂ) * g a‖ ≤ 1)
    (hcoord_meas : Measurable (fun a : ℝ => (a : ℂ) * g a))
    (hidentity : ∀ a : ℝ, (a : ℂ) * g a + c * g a = 1) :
    (maximalSpectralIntegral μS + c • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro x
  let y : H := boundedIntegral μS g hg hgb x
  have hy : y ∈ OperatorAlgebra.spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain (α := ℝ) μS hg hgb hcoord x
  have haction := maximalSpectralIntegral_apply_boundedMultiplier μS hg hgb hcoord
    hcoord_meas x
  have hgbc : ∃ C : ℝ, ∀ a, ‖c * g a‖ ≤ C := by
    rcases hgb with ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun a => ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC a) (norm_nonneg c)
  have hg_c : Measurable (fun a : ℝ => c * g a) := measurable_const.mul hg
  have hadd := boundedIntegral_add μS hcoord_meas hg_c
    (⟨1, hcoord⟩) hgbc
  have hsmul := boundedIntegral_smul μS c hg hgb
  have hsum_bound : ∃ C : ℝ, ∀ a : ℝ, ‖(a : ℂ) * g a + c * g a‖ ≤ C := by
    rcases hgbc with ⟨C, hC⟩
    refine ⟨1 + C, fun a => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hcoord a) (hC a))
  have hsum : boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a)
      hcoord_meas ⟨1, hcoord⟩ x + c • y = x := by
    calc
      _ = boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a)
          hcoord_meas ⟨1, hcoord⟩ x +
          boundedIntegral μS (fun a : ℝ => c * g a) hg_c hgbc x := by
        rw [hsmul]
        simp [y, ContinuousLinearMapWOT.smul_apply]
      _ = boundedIntegral μS
          ((fun a : ℝ => (a : ℂ) * g a) + (fun a : ℝ => c * g a))
          (hcoord_meas.add hg_c) _ x := by
        rw [hadd]
        simp [ContinuousLinearMapWOT.add_apply]
      _ = boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
          (⟨1, fun _ => by simp⟩) x := by
        have hcongr := boundedIntegral_congr μS (hcoord_meas.add hg_c) measurable_const
          hsum_bound (⟨1, fun _ => norm_one.le⟩)
          (fun a => by simp only [Pi.add_apply]; exact hidentity a)
        exact congrArg (fun A : H →WOT[ℂ] H => A x) hcongr
      _ = x := by
        rw [boundedIntegral_const]
        simp [ContinuousLinearMapWOT.one_apply]
  let yz : (maximalSpectralIntegral μS + c • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨y, Submodule.mem_inf.mpr ⟨hy, Submodule.mem_top⟩⟩
  refine ⟨yz, ?_⟩
  change (maximalSpectralIntegral μS) ⟨y, hy⟩ + c • y = x
  rw [haction]
  exact hsum

lemma maximalSpectralIntegral_shift_range_of_multiplier_of_bound
    (μS : WOTSpectralMeasure ℝ H) (c : ℂ) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C : ℝ, ∀ a, ‖g a‖ ≤ C)
    (hcoord : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, ‖(a : ℂ) * g a‖ ≤ C)
    (hcoord_meas : Measurable (fun a : ℝ => (a : ℂ) * g a))
    (hidentity : ∀ a : ℝ, (a : ℂ) * g a + c * g a = 1) :
    (maximalSpectralIntegral μS + c • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
  rcases hcoord with ⟨C, hC0, hcoord⟩
  rw [LinearMap.range_eq_top]
  intro x
  let y : H := boundedIntegral μS g hg hgb x
  have hy : y ∈ OperatorAlgebra.spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain_of_bound (α := ℝ) μS hg hgb
      ⟨C, hC0, hcoord⟩ x
  have haction := maximalSpectralIntegral_apply_boundedMultiplier_of_bound μS hg hgb
    ⟨C, hC0, hcoord⟩ hcoord_meas x
  have hgbc : ∃ C' : ℝ, ∀ a, ‖c * g a‖ ≤ C' := by
    rcases hgb with ⟨Cg, hCg⟩
    refine ⟨‖c‖ * Cg, fun a => ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hCg a) (norm_nonneg c)
  have hg_c : Measurable (fun a : ℝ => c * g a) := measurable_const.mul hg
  have hadd := boundedIntegral_add μS hcoord_meas hg_c
    (⟨C, hcoord⟩) hgbc
  have hsmul := boundedIntegral_smul μS c hg hgb
  have hsum_bound : ∃ C' : ℝ, ∀ a : ℝ,
      ‖(a : ℂ) * g a + c * g a‖ ≤ C' := by
    rcases hgbc with ⟨Cc, hCc⟩
    refine ⟨C + Cc, fun a => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hcoord a) (hCc a))
  have hsum : boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a)
      hcoord_meas ⟨C, hcoord⟩ x + c • y = x := by
    calc
      _ = boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a)
          hcoord_meas ⟨C, hcoord⟩ x +
          boundedIntegral μS (fun a : ℝ => c * g a) hg_c hgbc x := by
        rw [hsmul]
        simp [y, ContinuousLinearMapWOT.smul_apply]
      _ = boundedIntegral μS
          ((fun a : ℝ => (a : ℂ) * g a) + (fun a : ℝ => c * g a))
          (hcoord_meas.add hg_c) _ x := by
        rw [hadd]
        simp [ContinuousLinearMapWOT.add_apply]
      _ = boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
          (⟨1, fun _ => by simp⟩) x := by
        have hcongr := boundedIntegral_congr μS (hcoord_meas.add hg_c) measurable_const
          hsum_bound (⟨1, fun _ => norm_one.le⟩)
          (fun a => by simp only [Pi.add_apply]; exact hidentity a)
        exact congrArg (fun A : H →WOT[ℂ] H => A x) hcongr
      _ = x := by
        rw [boundedIntegral_const]
        simp [ContinuousLinearMapWOT.one_apply]
  let yz : (maximalSpectralIntegral μS + c • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨y, Submodule.mem_inf.mpr ⟨hy, Submodule.mem_top⟩⟩
  refine ⟨yz, ?_⟩
  change (maximalSpectralIntegral μS) ⟨y, hy⟩ + c • y = x
  rw [haction]
  exact hsum

/-- Every non-real shift of the canonical spectral integral is onto.  This is the concrete range
form of the resolvent theorem, proved directly from the bounded scalar multiplier
`r ↦ (r - z)⁻¹`. -/
lemma maximalSpectralIntegral_resolvent_range {z : ℂ} (hz : z.im ≠ 0) :
    (maximalSpectralIntegral μS - z • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
  have hidentity : ∀ r : ℝ,
      (r : ℂ) * resolventMultiplier z r + (-z) * resolventMultiplier z r = 1 := by
    intro r
    simpa [neg_mul, sub_eq_add_neg] using resolventMultiplier_identity hz r
  have hplus : (maximalSpectralIntegral μS + (-z) • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ :=
    maximalSpectralIntegral_shift_range_of_multiplier_of_bound μS (-z)
      (resolventMultiplier_measurable z) (resolventMultiplier_bounded hz)
      (resolventMultiplier_coordinate_bounded hz)
      (resolventMultiplier_coordinate_measurable z) hidentity
  have heq : maximalSpectralIntegral μS - z • (1 : H →ₗ.[ℂ] H) =
      maximalSpectralIntegral μS + (-z) • (1 : H →ₗ.[ℂ] H) := by
    exact LinearPMap.ext rfl fun x hx₁ hx₂ => by
      simp only [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
      module
  rw [heq]
  exact hplus

/-- The value of the inverse of a general non-real shift is the corresponding bounded spectral
multiplier.  This is the operator-level resolvent formula, including its domain proof. -/
lemma maximalSpectralIntegral_resolvent_inverse_apply {z : ℂ} (hz : z.im ≠ 0) (x : H) :
    (maximalSpectralIntegral μS - z • (1 : H →ₗ.[ℂ] H)).inverse
        ⟨x, by
          rw [LinearPMap.inverse_domain, maximalSpectralIntegral_resolvent_range hz]
          exact Submodule.mem_top⟩ =
      boundedIntegral μS (resolventMultiplier z) (resolventMultiplier_measurable z)
        (resolventMultiplier_bounded hz) x := by
  let M := maximalSpectralIntegral μS
  let g := resolventMultiplier z
  have htarget := maximalSpectralIntegral_resolvent_range (μS := μS) hz
  have hself : IsSelfAdjoint M := by
    apply maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top μS
    · have h := maximalSpectralIntegral_resolvent_range
          (μS := μS) (z := -Complex.I) (by norm_num)
      have heq : M + Complex.I • (1 : H →ₗ.[ℂ] H) =
          M - (-Complex.I) • (1 : H →ₗ.[ℂ] H) := by
        exact LinearPMap.ext rfl fun y hy₁ hy₂ => by
          simp only [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
            neg_smul]
          module
      change (M + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤
      rw [heq]
      exact h
    · simpa [M] using (maximalSpectralIntegral_resolvent_range
        (μS := μS) (z := Complex.I) (by norm_num))
  have hker : (M - z • (1 : H →ₗ.[ℂ] H)).toFun.ker = ⊥ := by
    have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero
      hself hz
    exact hres.1
  have hcoord := resolventMultiplier_coordinate_bounded hz
  have hy : boundedIntegral μS g (resolventMultiplier_measurable z)
      (resolventMultiplier_bounded hz) x ∈
        OperatorAlgebra.spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain_of_bound (α := ℝ) μS
      (resolventMultiplier_measurable z) (resolventMultiplier_bounded hz) hcoord x
  let yM : M.domain :=
    ⟨boundedIntegral μS g (resolventMultiplier_measurable z)
      (resolventMultiplier_bounded hz) x, by
        change boundedIntegral μS g (resolventMultiplier_measurable z)
          (resolventMultiplier_bounded hz) x ∈
            OperatorAlgebra.spectralSquareMomentDomain μS
        exact hy⟩
  let y : (M - z • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨(yM : H), Submodule.mem_inf.mpr ⟨hy, Submodule.mem_top⟩⟩
  have haction := maximalSpectralIntegral_apply_boundedMultiplier_of_bound μS
    (resolventMultiplier_measurable z) (resolventMultiplier_bounded hz) hcoord
    (resolventMultiplier_coordinate_measurable z) x
  have hzg_bound : ∃ C : ℝ, ∀ r : ℝ,
      ‖z * g r‖ ≤ C := by
    rcases resolventMultiplier_bounded hz with ⟨C, hC⟩
    refine ⟨‖z‖ * C, fun r => ?_⟩
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC r) (norm_nonneg z)
  have hsum : (M - z • (1 : H →ₗ.[ℂ] H)) y = x := by
    change M yM - z • (y : H) = x
    have hscaled : z • (y : H) =
        boundedIntegral μS (fun r : ℝ => z * g r)
          (measurable_const.mul (resolventMultiplier_measurable z)) hzg_bound x := by
      have h := congrArg (fun A : H →WOT[ℂ] H => A x)
        (boundedIntegral_smul μS z (resolventMultiplier_measurable z)
          (resolventMultiplier_bounded hz))
      simpa [y, yM, Pi.mul_apply] using h.symm
    rw [haction, hscaled]
    have hsub := boundedIntegral_sub μS
      (f := fun r : ℝ => (r : ℂ) * g r)
      (g := fun r : ℝ => z * g r)
      (resolventMultiplier_coordinate_measurable z)
      (measurable_const.mul (resolventMultiplier_measurable z))
      (by rcases hcoord with ⟨C, hC0, hC⟩; exact ⟨C, hC⟩) hzg_bound
    have hsubx := congrArg (fun A : H →WOT[ℂ] H => A x) hsub
    rw [← ContinuousLinearMapWOT.sub_apply, ← hsubx]
    have hcongr : ∀ r : ℝ,
        (r : ℂ) * g r - z * g r = (1 : ℂ) := by
      intro r
      exact resolventMultiplier_identity hz r
    have hfunit : Measurable (fun r : ℝ => (r : ℂ) * g r - z * g r) := by
      exact (resolventMultiplier_coordinate_measurable z).sub
        (measurable_const.mul (resolventMultiplier_measurable z))
    have hbunit : ∃ C : ℝ, ∀ r : ℝ,
        ‖(r : ℂ) * g r - z * g r‖ ≤ C := by
      rcases hcoord with ⟨C, hC0, hC⟩
      rcases hzg_bound with ⟨Cz, hCz⟩
      refine ⟨C + Cz, fun r => ?_⟩
      exact (norm_sub_le _ _).trans (add_le_add (hC r) (hCz r))
    have hunit : boundedIntegral μS
        ((fun r : ℝ => (r : ℂ) * g r) - (fun r : ℝ => z * g r))
        ((resolventMultiplier_coordinate_measurable z).sub
          (measurable_const.mul (resolventMultiplier_measurable z))) hbunit =
        boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
          ⟨1, fun _ => by simp⟩ := by
      apply boundedIntegral_congr
      intro r
      simpa [Pi.sub_apply] using hcongr r
    have hunitx := congrArg (fun A : H →WOT[ℂ] H => A x) hunit
    convert hunitx using 1 <;> try { apply Subsingleton.elim }
    simp only [boundedIntegral_const]
    simp only [one_smul, ContinuousLinearMapWOT.one_apply]
  let x' : (M - z • (1 : H →ₗ.[ℂ] H)).inverse.domain :=
    ⟨x, by
      rw [LinearPMap.inverse_domain, htarget]
      exact Submodule.mem_top⟩
  have hxy : (M - z • (1 : H →ₗ.[ℂ] H)) y = x' := by
    simpa [x'] using hsum
  exact LinearPMap.inverse_apply_eq hker hxy

lemma maximalSpectralIntegral_plus_resolvent_range :
    (maximalSpectralIntegral μS + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
  have hidentity : ∀ a : ℝ,
      (a : ℂ) * plusResolventMultiplier a + Complex.I * plusResolventMultiplier a = 1 := by
    intro a
    unfold plusResolventMultiplier
    have hne : (a : ℂ) + Complex.I ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      norm_num at hi
    calc
      (a : ℂ) * ((a : ℂ) + Complex.I)⁻¹ + Complex.I *
          ((a : ℂ) + Complex.I)⁻¹ =
          ((a : ℂ) + Complex.I) * ((a : ℂ) + Complex.I)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hne
  exact maximalSpectralIntegral_shift_range_of_multiplier μS Complex.I
    plusResolventMultiplier_measurable plusResolventMultiplier_bounded
    plusResolventMultiplier_coordinate_bounded
    plusResolventMultiplier_coordinate_measurable hidentity

lemma maximalSpectralIntegral_minus_resolvent_range :
    (maximalSpectralIntegral μS - Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ := by
  have hidentity : ∀ a : ℝ,
      (a : ℂ) * minusResolventMultiplier a + (-Complex.I) * minusResolventMultiplier a = 1 := by
    intro a
    unfold minusResolventMultiplier
    have hne : (a : ℂ) - Complex.I ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      norm_num at hi
    calc
      (a : ℂ) * ((a : ℂ) - Complex.I)⁻¹ + (-Complex.I) *
          ((a : ℂ) - Complex.I)⁻¹ =
          ((a : ℂ) - Complex.I) * ((a : ℂ) - Complex.I)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hne
  have hplus : (maximalSpectralIntegral μS + (-Complex.I) •
      (1 : H →ₗ.[ℂ] H)).toFun.range = ⊤ :=
    maximalSpectralIntegral_shift_range_of_multiplier μS (-Complex.I)
      minusResolventMultiplier_measurable minusResolventMultiplier_bounded
      minusResolventMultiplier_coordinate_bounded
      minusResolventMultiplier_coordinate_measurable hidentity
  have heq : maximalSpectralIntegral μS - Complex.I • (1 : H →ₗ.[ℂ] H) =
      maximalSpectralIntegral μS + (-Complex.I) • (1 : H →ₗ.[ℂ] H) := by
    exact LinearPMap.ext rfl fun x hx₁ hx₂ => by
      simp only [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
      module
  rw [heq]
  exact hplus

/-! ### Resolvent values of the maximal realization

The range statements above show that the two shifted maximal realizations are onto.  The
following sharpen them to an actual value formula for their partial inverses.  This is the
operator-level form of the bounded Borel identities

`(λ + i)⁻¹ (λ + i) = 1` and `(λ - i)⁻¹ (λ - i) = 1`.

These lemmas are intentionally stated for `LinearPMap.inverse`: they do not introduce a second
unbounded-operator hierarchy, and they are exactly what the Cayley adapter needs when converting
between a self-adjoint operator and its bounded unitary transform. -/

lemma maximalSpectralIntegral_plus_resolvent_inverse_apply (x : H) :
    (maximalSpectralIntegral μS + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse
        ⟨x, by
          rw [LinearPMap.inverse_domain, maximalSpectralIntegral_plus_resolvent_range]
          exact Submodule.mem_top⟩ =
      boundedIntegral μS plusResolventMultiplier plusResolventMultiplier_measurable
        plusResolventMultiplier_bounded x := by
  let M := maximalSpectralIntegral μS
  let g := plusResolventMultiplier
  have hker : (M + Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.ker = ⊥ := by
    have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero
      (maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top μS
        (maximalSpectralIntegral_plus_resolvent_range (μS := μS))
        (maximalSpectralIntegral_minus_resolvent_range (μS := μS)))
      (z := -Complex.I) (by norm_num)
    have heq : M - (-Complex.I) • (1 : H →ₗ.[ℂ] H) =
        M + Complex.I • (1 : H →ₗ.[ℂ] H) := by
      exact LinearPMap.ext rfl fun y hy₁ hy₂ => by
        simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
          neg_smul]
    rw [← heq]
    exact hres.1
  have hy : boundedIntegral μS g plusResolventMultiplier_measurable
      plusResolventMultiplier_bounded x ∈
        OperatorAlgebra.spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain (α := ℝ) μS
      plusResolventMultiplier_measurable plusResolventMultiplier_bounded
      plusResolventMultiplier_coordinate_bounded x
  let yM : M.domain := ⟨boundedIntegral μS g plusResolventMultiplier_measurable
    plusResolventMultiplier_bounded x, hy⟩
  let y : (M + Complex.I • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨(yM : H), Submodule.mem_inf.mpr ⟨hy, Submodule.mem_top⟩⟩
  have haction := maximalSpectralIntegral_apply_boundedMultiplier μS
    plusResolventMultiplier_measurable plusResolventMultiplier_bounded
    plusResolventMultiplier_coordinate_bounded
    plusResolventMultiplier_coordinate_measurable x
  have hIbound : ∃ C : ℝ, ∀ a : ℝ, ‖Complex.I * g a‖ ≤ C := by
    rcases plusResolventMultiplier_bounded with ⟨C, hC⟩
    refine ⟨C, fun a => ?_⟩
    simpa [norm_mul] using hC a
  have hsum : (M + Complex.I • (1 : H →ₗ.[ℂ] H)) y = x := by
    change M yM + Complex.I • (y : H) = x
    have hscaled : Complex.I • (y : H) =
        boundedIntegral μS (fun a : ℝ => Complex.I * g a)
          (measurable_const.mul plusResolventMultiplier_measurable) hIbound x := by
      have h := congrArg (fun A : H →WOT[ℂ] H => A x)
        (boundedIntegral_smul μS Complex.I plusResolventMultiplier_measurable
          plusResolventMultiplier_bounded)
      simpa [y, yM, Pi.mul_apply] using h.symm
    rw [haction, hscaled]
    have hadd := boundedIntegral_add μS
      (f := fun a : ℝ => (a : ℂ) * g a)
      (g := fun a : ℝ => Complex.I * g a)
      plusResolventMultiplier_coordinate_measurable
      (measurable_const.mul plusResolventMultiplier_measurable)
      (⟨1, plusResolventMultiplier_coordinate_bounded⟩) hIbound
    have haddx := congrArg (fun A : H →WOT[ℂ] H => A x) hadd
    rw [← ContinuousLinearMapWOT.add_apply, ← haddx]
    have hcongr : ∀ a : ℝ, (a : ℂ) * g a + Complex.I * g a = (1 : ℂ) := by
      intro a
      unfold g plusResolventMultiplier
      have hne : (a : ℂ) + Complex.I ≠ 0 := by
        intro h
        have hi := congrArg Complex.im h
        norm_num at hi
      field_simp [hne]
    have hfunit : Measurable (fun a : ℝ => (a : ℂ) * g a + Complex.I * g a) := by
      have heqfun :
          ((fun a : ℝ => (a : ℂ) * plusResolventMultiplier a) +
              (fun a : ℝ => Complex.I * plusResolventMultiplier a)) =
            (fun a : ℝ => (a : ℂ) * plusResolventMultiplier a +
              Complex.I * plusResolventMultiplier a) := by
        funext a
        rfl
      change Measurable (fun a : ℝ => (a : ℂ) * plusResolventMultiplier a +
        Complex.I * plusResolventMultiplier a)
      rw [← heqfun]
      exact plusResolventMultiplier_coordinate_measurable.add
        (measurable_const.mul plusResolventMultiplier_measurable)
    have hbunit : ∃ C : ℝ, ∀ a : ℝ,
        ‖(fun a : ℝ => (a : ℂ) * g a + Complex.I * g a) a‖ ≤ C := by
      rcases plusResolventMultiplier_bounded with ⟨C, hC⟩
      refine ⟨1 + C, fun a => ?_⟩
      exact (norm_add_le _ _).trans (add_le_add
        (by simpa [g] using plusResolventMultiplier_coordinate_bounded a)
        (by simpa [g, norm_mul] using hC a))
    have hunit :
        boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a + Complex.I * g a)
            hfunit hbunit =
          boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
            ⟨1, fun _ => by simp⟩ := by
      apply boundedIntegral_congr
      exact fun a => hcongr a
    have hsumfun :
        (fun a : ℝ => (a : ℂ) * g a) + (fun a : ℝ => Complex.I * g a) =
          (fun a : ℝ => (a : ℂ) * g a + Complex.I * g a) := by
      funext a
      simp [Pi.add_apply]
    have hunitx := congrArg (fun A : H →WOT[ℂ] H => A x) hunit
    convert hunitx using 1 <;>
      simp only [hsumfun, boundedIntegral_const,
        ContinuousLinearMapWOT.one_apply]
    simp [ContinuousLinearMapWOT.one_apply]
  let x' : (M + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse.domain :=
    ⟨x, by
      rw [LinearPMap.inverse_domain, maximalSpectralIntegral_plus_resolvent_range]
      exact Submodule.mem_top⟩
  have hxy : (M + Complex.I • (1 : H →ₗ.[ℂ] H)) y = x' := by
    simpa [x'] using hsum
  exact LinearPMap.inverse_apply_eq hker hxy

lemma maximalSpectralIntegral_minus_resolvent_inverse_apply (x : H) :
    (maximalSpectralIntegral μS - Complex.I • (1 : H →ₗ.[ℂ] H)).inverse
        ⟨x, by
          rw [LinearPMap.inverse_domain, maximalSpectralIntegral_minus_resolvent_range]
          exact Submodule.mem_top⟩ =
      boundedIntegral μS minusResolventMultiplier minusResolventMultiplier_measurable
        minusResolventMultiplier_bounded x := by
  let M := maximalSpectralIntegral μS
  let g := minusResolventMultiplier
  have hker : (M - Complex.I • (1 : H →ₗ.[ℂ] H)).toFun.ker = ⊥ := by
    have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero
      (maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top μS
        (maximalSpectralIntegral_plus_resolvent_range (μS := μS))
        (maximalSpectralIntegral_minus_resolvent_range (μS := μS)))
      (z := Complex.I) (by norm_num)
    exact hres.1
  have hy : boundedIntegral μS g minusResolventMultiplier_measurable
      minusResolventMultiplier_bounded x ∈
        OperatorAlgebra.spectralSquareMomentDomain μS :=
    boundedMultiplier_mem_spectralSquareMomentDomain (α := ℝ) μS
      minusResolventMultiplier_measurable minusResolventMultiplier_bounded
      minusResolventMultiplier_coordinate_bounded x
  let yM : M.domain := ⟨boundedIntegral μS g minusResolventMultiplier_measurable
    minusResolventMultiplier_bounded x, hy⟩
  let y : (M - Complex.I • (1 : H →ₗ.[ℂ] H)).domain :=
    ⟨(yM : H), Submodule.mem_inf.mpr ⟨hy, Submodule.mem_top⟩⟩
  have haction := maximalSpectralIntegral_apply_boundedMultiplier μS
    minusResolventMultiplier_measurable minusResolventMultiplier_bounded
    minusResolventMultiplier_coordinate_bounded
    minusResolventMultiplier_coordinate_measurable x
  have hIbound : ∃ C : ℝ, ∀ a : ℝ, ‖Complex.I * g a‖ ≤ C := by
    rcases minusResolventMultiplier_bounded with ⟨C, hC⟩
    refine ⟨C, fun a => ?_⟩
    simpa [norm_mul] using hC a
  have hsum : (M - Complex.I • (1 : H →ₗ.[ℂ] H)) y = x := by
    change M yM - Complex.I • (y : H) = x
    have hscaled : Complex.I • (y : H) =
        boundedIntegral μS (fun a : ℝ => Complex.I * g a)
          (measurable_const.mul minusResolventMultiplier_measurable) hIbound x := by
      have h := congrArg (fun A : H →WOT[ℂ] H => A x)
        (boundedIntegral_smul μS Complex.I minusResolventMultiplier_measurable
          minusResolventMultiplier_bounded)
      simpa [y, yM, Pi.mul_apply] using h.symm
    rw [haction, hscaled]
    have hadd := boundedIntegral_sub μS
      (f := fun a : ℝ => (a : ℂ) * g a)
      (g := fun a : ℝ => Complex.I * g a)
      minusResolventMultiplier_coordinate_measurable
      (measurable_const.mul minusResolventMultiplier_measurable)
      (⟨1, minusResolventMultiplier_coordinate_bounded⟩) hIbound
    have haddx := congrArg (fun A : H →WOT[ℂ] H => A x) hadd
    rw [← ContinuousLinearMapWOT.sub_apply, ← haddx]
    have hcongr : ∀ a : ℝ, (a : ℂ) * g a - Complex.I * g a = (1 : ℂ) := by
      intro a
      unfold g minusResolventMultiplier
      have hne : (a : ℂ) - Complex.I ≠ 0 := by
        intro h
        have hi := congrArg Complex.im h
        norm_num at hi
      field_simp [hne]
    have hfunit : Measurable (fun a : ℝ => (a : ℂ) * g a - Complex.I * g a) := by
      have heqfun :
          ((fun a : ℝ => (a : ℂ) * minusResolventMultiplier a) -
              (fun a : ℝ => Complex.I * minusResolventMultiplier a)) =
            (fun a : ℝ => (a : ℂ) * minusResolventMultiplier a -
              Complex.I * minusResolventMultiplier a) := by
        funext a
        rfl
      change Measurable (fun a : ℝ => (a : ℂ) * minusResolventMultiplier a -
        Complex.I * minusResolventMultiplier a)
      rw [← heqfun]
      exact minusResolventMultiplier_coordinate_measurable.sub
        (measurable_const.mul minusResolventMultiplier_measurable)
    have hbunit : ∃ C : ℝ, ∀ a : ℝ,
        ‖(fun a : ℝ => (a : ℂ) * g a - Complex.I * g a) a‖ ≤ C := by
      rcases minusResolventMultiplier_bounded with ⟨C, hC⟩
      refine ⟨1 + C, fun a => ?_⟩
      exact (norm_sub_le _ _).trans (add_le_add
        (by simpa [g] using minusResolventMultiplier_coordinate_bounded a)
        (by simpa [g, norm_mul] using hC a))
    have hunit :
        boundedIntegral μS (fun a : ℝ => (a : ℂ) * g a - Complex.I * g a)
            hfunit hbunit =
          boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const
            ⟨1, fun _ => by simp⟩ := by
      apply boundedIntegral_congr
      exact fun a => hcongr a
    have hsubfun :
        (fun a : ℝ => (a : ℂ) * g a) - (fun a : ℝ => Complex.I * g a) =
          (fun a : ℝ => (a : ℂ) * g a - Complex.I * g a) := by
      funext a
      simp [Pi.sub_apply]
    have hunitx := congrArg (fun A : H →WOT[ℂ] H => A x) hunit
    convert hunitx using 1 <;>
      simp only [hsubfun, boundedIntegral_const,
        ContinuousLinearMapWOT.one_apply]
    simp [ContinuousLinearMapWOT.one_apply]
  let x' : (M - Complex.I • (1 : H →ₗ.[ℂ] H)).inverse.domain :=
    ⟨x, by
      rw [LinearPMap.inverse_domain, maximalSpectralIntegral_minus_resolvent_range]
      exact Submodule.mem_top⟩
  have hxy : (M - Complex.I • (1 : H →ₗ.[ℂ] H)) y = x' := by
    simpa [x'] using hsum
  exact LinearPMap.inverse_apply_eq hker hxy

/-! ### The canonical self-adjoint realization

The preceding two range lemmas are the concrete Cayley-resolvent calculation.  They are worth
keeping separate from the abstract range criterion: this theorem is the point at which a real PVM
itself produces a self-adjoint (closed) unbounded operator, with no prior operator or domain datum.
-/

lemma maximalSpectralIntegral_isSelfAdjoint (μS : WOTSpectralMeasure ℝ H) :
    IsSelfAdjoint (maximalSpectralIntegral μS) := by
  apply maximalSpectralIntegral_isSelfAdjoint_of_range_eq_top μS
  · exact maximalSpectralIntegral_plus_resolvent_range (μS := μS)
  · exact maximalSpectralIntegral_minus_resolvent_range (μS := μS)

/-- The canonical maximal realization has a surjective shifted operator at every non-real
spectral parameter.  The preceding explicit `± Complex.I` calculations establish
self-adjointness; this general form then follows from the self-adjoint resolvent theorem. -/
lemma maximalSpectralIntegral_sub_smul_surjective
    (μS : WOTSpectralMeasure ℝ H) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Surjective
      (maximalSpectralIntegral μS - z • (1 : H →ₗ.[ℂ] H)).toFun :=
  LinearPMap.IsSelfAdjoint.sub_smul_surjective
    (maximalSpectralIntegral_isSelfAdjoint μS) hz

/-- Every non-real point belongs to the resolvent set of the canonical maximal spectral
integral.  This is the public `resolventSet` form of the preceding range theorem and the
self-adjoint resolvent criterion; downstream users can therefore use the ordinary resolvent API
without unpacking the Cayley shifts or the spectral multiplier construction. -/
lemma maximalSpectralIntegral_mem_resolventSet
    (μS : WOTSpectralMeasure ℝ H) {z : ℂ} (hz : z.im ≠ 0) :
    z ∈ LinearPMap.resolventSet (maximalSpectralIntegral μS) :=
  LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero
    (maximalSpectralIntegral_isSelfAdjoint μS) hz

/-- Resolvent notation for the canonical spectral integral is exactly the bounded spectral
multiplier `λ ↦ (λ - z)⁻¹`.  The subtype in the left-hand side is the canonical full-domain
element supplied by the resolvent theorem. -/
lemma maximalSpectralIntegral_resolvent_apply {z : ℂ} (hz : z.im ≠ 0) (x : H) :
    LinearPMap.resolvent (maximalSpectralIntegral μS) z
        ⟨x, by
          rw [LinearPMap.inverse_domain, maximalSpectralIntegral_resolvent_range hz]
          exact Submodule.mem_top⟩ =
      boundedIntegral μS (resolventMultiplier z) (resolventMultiplier_measurable z)
        (resolventMultiplier_bounded hz) x :=
  maximalSpectralIntegral_resolvent_inverse_apply hz x

lemma maximalSpectralIntegral_closure_eq_self_adjoint (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).closure = maximalSpectralIntegral μS := by
  exact (maximalSpectralIntegral_isSelfAdjoint μS).isClosed.closure_eq

lemma maximalSpectralIntegral_isEssentiallySelfAdjoint (μS : WOTSpectralMeasure ℝ H) :
    (maximalSpectralIntegral μS).IsEssentiallySelfAdjoint := by
  rw [maximalSpectralIntegral_isEssentiallySelfAdjoint_iff]
  rw [maximalSpectralIntegral_closure_eq_self_adjoint μS]
  exact maximalSpectralIntegral_isSelfAdjoint μS

lemma measurableSpectralIntegral_isSelfAdjoint
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f) :
    _root_.IsSelfAdjoint (measurableSpectralIntegral μS f hf) := by
  exact maximalSpectralIntegral_isSelfAdjoint (μS.map f hf)

lemma measurableSpectralIntegral_closure_eq_self
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f) :
    (measurableSpectralIntegral μS f hf).closure =
      measurableSpectralIntegral μS f hf := by
  exact (measurableSpectralIntegral_isSelfAdjoint μS f hf).isClosed.closure_eq

lemma measurableSpectralIntegral_isEssentiallySelfAdjoint
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f) :
    (measurableSpectralIntegral μS f hf).IsEssentiallySelfAdjoint := by
  exact maximalSpectralIntegral_isEssentiallySelfAdjoint (μS.map f hf)

lemma measurableSpectralIntegral_norm_sq
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f)
    (x : H) (hx : x ∈ (measurableSpectralIntegral μS f hf).domain) :
    ENNReal.ofReal
        (‖(measurableSpectralIntegral μS f hf) ⟨x, hx⟩‖ ^ 2) =
      ∫⁻ r, ENNReal.ofReal ((f r) ^ 2) ∂μS.diagonalMeasure x := by
  have h := maximalSpectralIntegral_norm_sq (μS.map f hf) x hx
  rw [μS.diagonalMeasure_map f hf] at h
  calc
    ENNReal.ofReal
        (‖(measurableSpectralIntegral μS f hf) ⟨x, hx⟩‖ ^ 2) =
        ∫⁻ r, ENNReal.ofReal (r ^ 2) ∂Measure.map f (μS.diagonalMeasure x) := h
    _ = ∫⁻ r, ENNReal.ofReal ((f r) ^ 2) ∂μS.diagonalMeasure x := by
      simpa [Function.comp_def] using
        (lintegral_map (μ := μS.diagonalMeasure x)
          (ENNReal.continuous_ofReal.measurable.comp (measurable_id.pow_const 2)) hf)

lemma measurableSpectralIntegral_norm_sq_eq_integral
    (μS : WOTSpectralMeasure ℝ H) (f : ℝ → ℝ) (hf : Measurable f)
    (x : H) (hx : x ∈ (measurableSpectralIntegral μS f hf).domain) :
    ‖(measurableSpectralIntegral μS f hf) ⟨x, hx⟩‖ ^ 2 =
      ∫ r, f r ^ 2 ∂μS.diagonalMeasure x := by
  have hfi : Integrable (fun r : ℝ => f r ^ 2) (μS.diagonalMeasure x) := by
    exact (mem_measurableSpectralIntegral_domain_iff μS f hf x).mp hx
  have hpos : 0 ≤ᵐ[μS.diagonalMeasure x] (fun r : ℝ => f r ^ 2) :=
    Filter.Eventually.of_forall (fun r => sq_nonneg (f r))
  have hconvert : ENNReal.ofReal (∫ r, f r ^ 2 ∂μS.diagonalMeasure x) =
      ∫⁻ r, ENNReal.ofReal (f r ^ 2) ∂μS.diagonalMeasure x :=
    ofReal_integral_eq_lintegral_ofReal hfi hpos
  have hmain := measurableSpectralIntegral_norm_sq μS f hf x hx
  rw [← hconvert] at hmain
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _)
    (integral_nonneg (fun r => sq_nonneg (f r)))).mp hmain

/-! ### Uniqueness of the domain-aware realization

The next theorem is the reusable endpoint of the PVM layer.  It says that a self-adjoint partial
operator whose matrix elements are reconstructed by a real PVM is necessarily the canonical
square-moment realization of that PVM.  The proof is deliberately here, rather than in a Cayley
adapter: Cayley, multiplication operators, and later concrete models can all use the same
domain-identification theorem.
-/

theorem maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution
    (T : H →ₗ.[ℂ] H) (hT : _root_.IsSelfAdjoint T)
    (hres : OperatorAlgebra.IsWeakSpectralResolution T μS)
    (hdom : ∀ x : T.domain,
      (x : H) ∈ OperatorAlgebra.spectralSquareMomentDomain μS) :
    maximalSpectralIntegral μS = T := by
  let M := maximalSpectralIntegral μS
  have hle : T ≤ M := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact hdom ⟨x, hx⟩
    · intro x z hxz
      have hxM : (x : H) ∈ M.domain := by
        change (x : H) ∈ OperatorAlgebra.spectralSquareMomentDomain μS
        exact hdom x
      let z₀ : M.domain := ⟨(x : H), hxM⟩
      have hz : z = z₀ := by
        apply Subtype.ext
        exact hxz.symm
      apply ext_inner_left ℂ
      intro y
      have hfi : (μS.scalarMeasure (x : H) y).Integrable id := (hres ⟨x, x.property⟩).1 y
      letI := scalarMeasure_isFiniteVariation μS (x : H) y
      have hweak := truncationIntegral_inner_tendsto_weakIntegral μS (x : H) y hfi
      have hcomplex : Filter.Tendsto
          (fun n : ℕ => ∫ᵛ r, truncationFunction n r ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); μS.scalarMeasure (x : H) y])
          Filter.atTop (𝓝 (μS.weakIntegral id (x : H) y)) := by
        apply hweak.congr'
        filter_upwards [] with n
        have htrunc : (μS.scalarMeasure (x : H) y).Integrable (realTruncationFunction n) := by
          rcases realTruncationFunction_bounded n with ⟨C, hC⟩
          apply Integrable.of_bound (realTruncationFunction_measurable n).aestronglyMeasurable C
          filter_upwards [] with r
          simpa [Real.norm_eq_abs] using hC r
        have hreal := integral_real_eq_complex (μS.scalarMeasure (x : H) y) htrunc
        have hfun : (fun r => truncationFunction n r) =
            (fun r => Complex.ofRealCLM (realTruncationFunction n r)) := by
          funext r
          simpa [Complex.ofRealCLM_apply] using congrFun
            (realTruncationFunction_complex_eq n).symm r
        calc
          ∫ᵛ r, realTruncationFunction n r ∂[
              ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μS.scalarMeasure (x : H) y] =
              ∫ᵛ r, Complex.ofRealCLM (realTruncationFunction n r) ∂[
                ContinuousLinearMap.lsmul ℝ ℂ; μS.scalarMeasure (x : H) y] := hreal
          _ = ∫ᵛ r, truncationFunction n r ∂[
              ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); μS.scalarMeasure (x : H) y] :=
            congrArg (fun f : ℝ → ℂ => ∫ᵛ r, f r ∂[
              ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); μS.scalarMeasure (x : H) y]) hfun.symm
      have hmax := maximalSpectralIntegral_weak_truncation_reconstruction μS (x : H) hxM y
      have hinner : ⟪y, M z₀⟫_ℂ = μS.weakIntegral id (x : H) y :=
        tendsto_nhds_unique hmax hcomplex
      calc
        ⟪y, T x⟫_ℂ = μS.weakIntegral id (x : H) y := (hres ⟨x, x.property⟩).2 y
        _ = ⟪y, M z₀⟫_ℂ := hinner.symm
        _ = ⟪y, M z⟫_ℂ := by rw [hz]
  have hmax := maximalSpectralIntegral_isSelfAdjoint μS
  have hTesa : T.IsEssentiallySelfAdjoint :=
    _root_.LinearPMap.IsSelfAdjoint.isEssentiallySelfAdjoint hT
  have hclosure := LinearPMap.IsEssentiallySelfAdjoint.unique_self_adjoint_extension
    hTesa hle hmax
  rw [hT.isClosed.closure_eq] at hclosure
  exact hclosure

/-- Package the reusable PVM realization theorem together with its exact domain statement.

The only model-specific input is the inclusion of the model domain into the square-moment domain;
the reverse inclusion is forced by self-adjoint uniqueness after the canonical maximal realization
has been constructed. -/
theorem domainAwareSelfAdjointSpectralTheorem_of_isWeakSpectralResolution
    (T : H →ₗ.[ℂ] H) (hT : _root_.IsSelfAdjoint T)
    (hres : OperatorAlgebra.IsWeakSpectralResolution T μS)
    (hdom : ∀ x : T.domain,
      (x : H) ∈ OperatorAlgebra.spectralSquareMomentDomain μS) :
    OperatorAlgebra.DomainAwareSelfAdjointSpectralTheorem T μS := by
  have heq := maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution
    T hT hres hdom
  refine
    { toSelfAdjointSpectralTheorem :=
        { isSelfAdjoint := hT
          reconstruction := hres }
      domain_eq_squareMoment := ?_ }
  have hdomains : (T.domain : Set H) =
      ((maximalSpectralIntegral μS).domain : Set H) :=
    congrArg (fun D : Submodule ℂ H => (D : Set H))
      (congrArg LinearPMap.domain heq).symm
  calc
    (T.domain : Set H) = (maximalSpectralIntegral μS).domain := hdomains
    _ = OperatorAlgebra.spectralSquareMomentDomain μS := by
      exact congrArg (fun D : Submodule ℂ H => (D : Set H))
        (maximalSpectralIntegral_domain μS)

end QuantumMechanics.WOTSpectralMeasure

namespace OperatorAlgebra

namespace DomainAwareSelfAdjointSpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

/-! ### The canonical operator equality

The domain-aware certificate contains exactly the extra hypothesis needed by the uniqueness
theorem: its operator domain is the square-moment domain of its PVM.  Exposing this equality as a
method keeps later Cayley and representation proofs from reconstructing the same argument. -/

theorem maximal_eq (D : DomainAwareSelfAdjointSpectralTheorem T μS) :
    QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral μS = T := by
  exact QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution
    T D.isSelfAdjoint D.reconstruction_of
    (fun z => by
      change (z : H) ∈ OperatorAlgebra.spectralSquareMomentDomain μS
      exact D.mem_domain_iff z |>.mp z.property)

end DomainAwareSelfAdjointSpectralTheorem

namespace SelfAdjointSpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

/- The weak reconstruction certificate becomes an actual operator equality as soon as the model
supplies the one missing domain inclusion.  This is the thin, non-domain-aware entry point used
by Cayley and model-specific closures. -/
theorem maximal_eq_of_domain_inclusion
    (D : SelfAdjointSpectralTheorem T μS)
    (hdom : ∀ x : T.domain,
      (x : H) ∈ spectralSquareMomentDomain μS) :
    QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral μS = T := by
  exact QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution
    T D.isSelfAdjoint D.reconstruction hdom

end SelfAdjointSpectralTheorem

namespace EssentialSelfAdjointSpectralData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H} (D : EssentialSelfAdjointSpectralData T)

/-! A core operator's spectral data becomes domain-aware as soon as its concrete model supplies the
square-moment inclusion for the self-adjoint closure.  This is the intended hand-off point for
oscillator, multiplication, and Schrödinger proofs. -/

theorem domainAwareSpectralTheorem
    (hdom : ∀ x : T.closure.domain,
      (x : H) ∈ spectralSquareMomentDomain D.spectralMeasure) :
    DomainAwareSelfAdjointSpectralTheorem T.closure D.spectralMeasure := by
  exact QuantumMechanics.WOTSpectralMeasure.domainAwareSelfAdjointSpectralTheorem_of_isWeakSpectralResolution
      T.closure
      D.closure_isSelfAdjoint D.spectralReconstruction hdom

end EssentialSelfAdjointSpectralData

end OperatorAlgebra

end
