/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.Operators.SpectralTheory.WeakSpectralMeasure.A

/-!
# Weak-operator spectral measures (part 2 of 2)

Continuation of `WeakSpectralMeasure/A.lean`; see `WeakSpectralMeasure.lean` for the full module
overview. This part covers the bounded integral's vector norm-square identity, the strong
unitary one-parameter group construction, and the conversion from the older norm-valued
`SpectralMeasure`.
-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace Function
open ContinuousLinearMap ContinuousLinearMapWOT MeasureTheory Set

namespace QuantumMechanics

namespace WOTSpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μS : WOTSpectralMeasure α H)

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
