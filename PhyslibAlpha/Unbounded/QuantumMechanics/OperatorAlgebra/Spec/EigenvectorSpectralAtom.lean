/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.SpectralTheory.TypeDecomposition
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.SpectralTheory.SpectralIntegral

/-!
# An eigenvector is fixed by its eigenvalue's spectral projection

This file proves the converse direction to
`OperatorAlgebra.atom_eigenvector_of_reconstruction` (`CayleySpectralData.lean`): there, an atom of
the spectral measure was shown to produce an eigenvector.  Here, an *exact* eigenvector of the
self-adjoint operator represented by a `DomainAwareSelfAdjointSpectralTheorem` is shown to be fixed
by the spectral projection onto its eigenvalue — hence to lie in the range of that atomic
projection.

This is entirely general/model-independent theory (Reed-Simon, *Methods of Modern Mathematical
Physics I*, the argument behind Theorem VIII.6's discrete-spectrum corollaries): the key
computation is that the second spectral moment of `T v - c v` around the eigenvalue `c` vanishes,
which forces the vector-state measure of `v` to be concentrated at `{c}`.

## Main results

* `QuantumMechanics.WOTSpectralMeasure.truncation_shift_lintegral_tendsto` : the second moment of
  the truncated spectral variable shifted by a constant `c` converges to the second moment of the
  honest shift `r ↦ (r - c)`.
* `OperatorAlgebra.mem_atom_range_of_isEigenvector` : if `T ⟨v, hv⟩ = c • v` for a domain-aware
  self-adjoint spectral theorem `T`/`μS`, then `μS {c} v = v`.
-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace
open MeasureTheory Set ENNReal

namespace QuantumMechanics.WOTSpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The second moment of the truncated spectral variable, shifted by a real constant `c`,
converges to the second moment of the honest shift `r ↦ (r - c)`.  Same dominated-convergence
technique as `truncation_error_lintegral_tendsto_zero`/`truncation_norm_lintegral_tendsto`, with
dominating function `2 r² + 2 c²`. -/
theorem truncation_shift_lintegral_tendsto
    (μS : WOTSpectralMeasure ℝ H) (x : H) (c : ℝ)
    (hx : Integrable (fun r : ℝ => r ^ 2) (μS.diagonalMeasure x)) :
    Filter.Tendsto
      (fun n : ℕ => ∫⁻ r, ENNReal.ofReal (‖truncationFunction n r - (c : ℂ)‖ ^ 2)
        ∂μS.diagonalMeasure x)
      Filter.atTop (𝓝 (∫⁻ r, ENNReal.ofReal ((r - c) ^ 2) ∂μS.diagonalMeasure x)) := by
  let μ : Measure ℝ := μS.diagonalMeasure x
  let F : ℕ → ℝ → ENNReal := fun n r => ENNReal.ofReal (‖truncationFunction n r - (c : ℂ)‖ ^ 2)
  let F₀ : ℝ → ENNReal := fun r => ENNReal.ofReal ((r - c) ^ 2)
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    exact ENNReal.continuous_ofReal.measurable.comp
      (((truncationFunction_measurable n).sub measurable_const).norm.pow_const 2)
  have hbound : ∀ n, ∀ᵐ r ∂μ, F n r ≤ ENNReal.ofReal (2 * r ^ 2 + 2 * c ^ 2) := by
    intro n
    filter_upwards [] with r
    dsimp only [F]
    apply ENNReal.ofReal_le_ofReal
    by_cases hr : r ∈ Set.Icc (-(n : ℝ)) (n : ℝ)
    · rw [truncationFunction, Set.indicator_of_mem hr]
      have hnorm : ‖(r : ℂ) - (c : ℂ)‖ ^ 2 = (r - c) ^ 2 := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [hnorm]
      nlinarith [sq_nonneg (r - c), sq_nonneg (r + c)]
    · simp only [truncationFunction, Set.indicator_of_notMem hr]
      have hnorm : ‖(0 : ℂ) - (c : ℂ)‖ ^ 2 = c ^ 2 := by
        rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      rw [hnorm]
      nlinarith [sq_nonneg r]
  have hdom : Integrable (fun r : ℝ => 2 * r ^ 2 + 2 * c ^ 2) μ := by
    apply Integrable.add
    · simpa only [smul_eq_mul] using hx.const_mul 2
    · exact integrable_const _
  have hfin : (∫⁻ r, ENNReal.ofReal (2 * r ^ 2 + 2 * c ^ 2) ∂μ) ≠ (⊤ : ENNReal) :=
    hdom.lintegral_lt_top.ne
  have hlim : ∀ᵐ r ∂μ, Filter.Tendsto (fun n => F n r) Filter.atTop (𝓝 (F₀ r)) := by
    filter_upwards [] with r
    have htrunc := truncationFunction_tendsto r
    have hdiff : Filter.Tendsto (fun n : ℕ => truncationFunction n r - (c : ℂ))
        Filter.atTop (𝓝 ((r : ℂ) - (c : ℂ))) :=
      htrunc.sub tendsto_const_nhds
    have hnormsq : Filter.Tendsto (fun n : ℕ => ‖truncationFunction n r - (c : ℂ)‖ ^ 2)
        Filter.atTop (𝓝 (‖(r : ℂ) - (c : ℂ)‖ ^ 2)) :=
      (continuous_norm.pow 2).continuousAt.tendsto.comp hdiff
    have heq : ‖(r : ℂ) - (c : ℂ)‖ ^ 2 = (r - c) ^ 2 := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [heq] at hnormsq
    change Filter.Tendsto (fun n : ℕ => F n r) Filter.atTop (𝓝 (F₀ r))
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnormsq
  have hmain : Filter.Tendsto (fun n : ℕ => ∫⁻ r, F n r ∂μ) Filter.atTop
      (𝓝 (∫⁻ r, F₀ r ∂μ)) := by
    apply MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
      (fun r => ENNReal.ofReal (2 * r ^ 2 + 2 * c ^ 2))
    · filter_upwards [] with n
      exact hFmeas n
    · filter_upwards [] with n
      exact hbound n
    · exact hfin
    · exact hlim
  simpa [F, F₀, μ] using hmain

end QuantumMechanics.WOTSpectralMeasure

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open QuantumMechanics.WOTSpectralMeasure

/-- **An eigenvector is fixed by its eigenvalue's spectral projection.**

If `T ⟨v, hv⟩ = c • v` exactly (for real `c`) and `T`/`μS` form a domain-aware self-adjoint
spectral theorem, then `μS {c} v = v`, i.e. `v` lies in the range of the atomic projection at `c`.

Proof (Reed-Simon style): identify `T` with the canonical `maximalSpectralIntegral μS`; the
bounded truncations `truncationIntegral μS n v` then converge both to `T v = c • v` (by
definition of the maximal integral) and, after subtracting `c • v`, have norm-square equal to the
second moment `∫ |truncationFunction n r - c|² dμ_v` (`boundedIntegral_norm_sq`).  Passing to the
limit (`truncation_shift_lintegral_tendsto`) shows `∫ (r - c)² dμ_v = 0`, so `μ_v` is concentrated
on `{c}`, i.e. `‖μS {c} v‖ = ‖v‖`.  Since `μS {c}` is an orthogonal projection, a vector on which it
acts isometrically must be fixed by it. -/
theorem mem_atom_range_of_isEigenvector
    {T : H →ₗ.[ℂ] H} {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}
    (D : DomainAwareSelfAdjointSpectralTheorem T μS)
    {v : H} (hv : v ∈ T.domain) {c : ℝ} (hcv : T ⟨v, hv⟩ = (c : ℂ) • v) :
    μS {c} v = v := by
  -- Step 1: identify `T` with the canonical maximal spectral integral.
  set M := QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral μS with hMdef
  have heq : M = T := D.maximal_eq
  have hdomeq : M.domain = T.domain := congrArg LinearPMap.domain heq
  have hvM : v ∈ M.domain := by rw [hdomeq]; exact hv
  have hval : M ⟨v, hvM⟩ = T ⟨v, hv⟩ := by
    exact (LinearPMap.ext_iff.mp heq).2 (x := v) (hf := hvM) (hg := hv)
  have hTv : M ⟨v, hvM⟩ = (c : ℂ) • v := hval.trans hcv
  have hvsub : v ∈ QuantumMechanics.WOTSpectralMeasure.spectralSquareMomentSubmodule μS := hvM
  -- Step 2: the truncated bounded integrals converge to `c • v`.
  have htend : Filter.Tendsto
      (fun n : ℕ => QuantumMechanics.WOTSpectralMeasure.truncationIntegral μS n v)
      Filter.atTop (𝓝 ((c : ℂ) • v)) := by
    have h := QuantumMechanics.WOTSpectralMeasure.truncationLimit_tendsto μS
      (⟨v, hvsub⟩ : QuantumMechanics.WOTSpectralMeasure.spectralSquareMomentSubmodule μS)
    have hlim_eq : QuantumMechanics.WOTSpectralMeasure.truncationLimit μS
        (⟨v, hvsub⟩ : QuantumMechanics.WOTSpectralMeasure.spectralSquareMomentSubmodule μS) =
        (c : ℂ) • v := hTv
    rwa [hlim_eq] at h
  have hnorm_tendsto0 : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal
        (‖QuantumMechanics.WOTSpectralMeasure.truncationIntegral μS n v - (c : ℂ) • v‖ ^ 2))
      Filter.atTop (𝓝 0) := by
    have hdiff : Filter.Tendsto
        (fun n : ℕ =>
          QuantumMechanics.WOTSpectralMeasure.truncationIntegral μS n v - (c : ℂ) • v)
        Filter.atTop (𝓝 (0 : H)) := by
      have := htend.sub (tendsto_const_nhds (x := (c : ℂ) • v))
      simpa using this
    have hnorm : Filter.Tendsto
        (fun n : ℕ =>
          ‖QuantumMechanics.WOTSpectralMeasure.truncationIntegral μS n v - (c : ℂ) • v‖ ^ 2)
        Filter.atTop (𝓝 (0 : ℝ)) := by
      have h := (continuous_norm.pow 2).continuousAt.tendsto.comp hdiff
      simpa [Function.comp_def, Pi.pow_apply] using h
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hnorm
    simpa [Function.comp_def, ← ofReal_norm] using h
  -- Step 3: the second-moment identity, for every truncation level `n`.
  have hkey : ∀ n : ℕ, ENNReal.ofReal
      (‖QuantumMechanics.WOTSpectralMeasure.truncationIntegral μS n v - (c : ℂ) • v‖ ^ 2) =
      ∫⁻ r, ENNReal.ofReal
        (‖QuantumMechanics.WOTSpectralMeasure.truncationFunction n r - (c : ℂ)‖ ^ 2)
        ∂μS.diagonalMeasure v := by
    intro n
    have hbf := QuantumMechanics.WOTSpectralMeasure.truncationFunction_bounded n
    have hbg : ∃ C : ℝ, ∀ _ : ℝ, ‖(c : ℂ)‖ ≤ C := ⟨‖(c : ℂ)‖, fun _ => le_rfl⟩
    have hsub := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_sub μS
      (QuantumMechanics.WOTSpectralMeasure.truncationFunction_measurable n)
      (measurable_const : Measurable (fun _ : ℝ => (c : ℂ))) hbf hbg
    have hconst := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_const μS (c : ℂ)
    rw [hconst] at hsub
    have happly := congrArg
      (fun A : H →WOT[ℂ] H => A v) hsub
    simp only [ContinuousLinearMapWOT.sub_apply, ContinuousLinearMapWOT.smul_apply,
      ContinuousLinearMapWOT.one_apply] at happly
    have hnormsq := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_norm_sq μS
      ((QuantumMechanics.WOTSpectralMeasure.truncationFunction_measurable n).sub
        (measurable_const : Measurable (fun _ : ℝ => (c : ℂ))))
      (by
        rcases hbf with ⟨Cn, hCn⟩
        exact ⟨Cn + ‖(c : ℂ)‖, fun r => (norm_sub_le _ _).trans (add_le_add (hCn r) le_rfl)⟩)
      v
    rw [happly] at hnormsq
    simpa [truncationIntegral, Pi.sub_apply, ← ofReal_norm] using hnormsq
  -- Step 4: pass to the limit.
  have hzero : (∫⁻ r, ENNReal.ofReal ((r - c) ^ 2) ∂μS.diagonalMeasure v) = 0 := by
    have hx2 : Integrable (fun r : ℝ => r ^ 2) (μS.diagonalMeasure v) := by
      have := (D.mem_domain_iff v).mp hv
      exact this
    have hshift := QuantumMechanics.WOTSpectralMeasure.truncation_shift_lintegral_tendsto μS v c hx2
    have heqn : (fun n : ℕ => ∫⁻ r, ENNReal.ofReal
        (‖QuantumMechanics.WOTSpectralMeasure.truncationFunction n r - (c : ℂ)‖ ^ 2)
        ∂μS.diagonalMeasure v) =
      (fun n : ℕ => ENNReal.ofReal
        (‖QuantumMechanics.WOTSpectralMeasure.truncationIntegral μS n v - (c : ℂ) • v‖ ^ 2)) := by
      funext n; exact (hkey n).symm
    rw [heqn] at hshift
    exact tendsto_nhds_unique hnorm_tendsto0 hshift |>.symm
  -- Step 5: the diagonal measure of `v` is concentrated on `{c}`.
  have hae : (fun r : ℝ => ENNReal.ofReal ((r - c) ^ 2)) =ᵐ[μS.diagonalMeasure v] 0 :=
    (MeasureTheory.lintegral_eq_zero_iff
      (ENNReal.continuous_ofReal.measurable.comp
        ((measurable_id.sub measurable_const).pow_const 2))).mp hzero
  have hcompl0 : μS.diagonalMeasure v {c}ᶜ = 0 := by
    have : {c}ᶜ ⊆ {r : ℝ | ¬ (ENNReal.ofReal ((r - c) ^ 2) = 0)} := by
      intro r hr
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hr
      simp only [Set.mem_setOf_eq, ENNReal.ofReal_eq_zero, not_le]
      have : r - c ≠ 0 := sub_ne_zero.mpr hr
      positivity
    exact measure_mono_null this (MeasureTheory.ae_iff.mp hae)
  have hunion : (({c} : Set ℝ) ∪ {c}ᶜ) = Set.univ := Set.union_compl_self _
  have hmeasunion : μS.diagonalMeasure v (({c} : Set ℝ) ∪ {c}ᶜ) =
      μS.diagonalMeasure v {c} + μS.diagonalMeasure v {c}ᶜ :=
    measure_union' disjoint_compl_right (measurableSet_singleton c)
  have huniv : μS.diagonalMeasure v Set.univ = μS.diagonalMeasure v {c} := by
    rw [← hunion, hmeasunion, hcompl0, add_zero]
  -- Step 6: convert to a norm equality and conclude via the projection identity.
  have hnormeq : ENNReal.ofReal (‖v‖ ^ 2) = ENNReal.ofReal (‖μS {c} v‖ ^ 2) := by
    rw [← μS.diagonalMeasure_univ v, huniv,
      μS.diagonalMeasure_apply_eq_norm_sq v {c} (measurableSet_singleton c)]
  have hnormeq' : ‖v‖ ^ 2 = ‖μS {c} v‖ ^ 2 :=
    (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) (sq_nonneg _)).mp hnormeq
  have hnormeq'' : ‖v‖ = ‖μS {c} v‖ := by
    have h1 : (0:ℝ) ≤ ‖v‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ ‖μS {c} v‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖v‖ - ‖μS {c} v‖), sq_nonneg (‖v‖ + ‖μS {c} v‖)]
  have hproj : ⟪v, μS {c} v⟫_ℂ = ⟪μS {c} v, μS {c} v⟫_ℂ :=
    μS.inner_eq_inner_projection {c} v
  have hre : (⟪v, μS {c} v⟫_ℂ).re = ‖μS {c} v‖ ^ 2 := by
    rw [hproj]; exact inner_self_eq_norm_sq (𝕜 := ℂ) (μS {c} v)
  have hnormsub : ‖v - μS {c} v‖ ^ 2 = ‖v‖ ^ 2 - 2 * ‖μS {c} v‖ ^ 2 + ‖μS {c} v‖ ^ 2 := by
    calc
      ‖v - μS {c} v‖ ^ 2 = ‖v‖ ^ 2 -
          2 * (⟪v, μS {c} v⟫_ℂ).re + ‖μS {c} v‖ ^ 2 :=
        norm_sub_sq (𝕜 := ℂ) v (μS {c} v)
      _ = ‖v‖ ^ 2 - 2 * ‖μS {c} v‖ ^ 2 + ‖μS {c} v‖ ^ 2 := by rw [hre]
  have hnormsub0 : ‖v - μS {c} v‖ ^ 2 = 0 := by
    rw [hnormsub, ← hnormeq']; ring
  have hfix : v - μS {c} v = 0 := by
    have hnorm0 : ‖v - μS {c} v‖ = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hnormsub0
    exact norm_eq_zero.mp hnorm0
  exact (sub_eq_zero.mp hfix).symm

/-- A nonzero atom produces a nonzero eigenvector of the maximal self-adjoint realization.

This is the converse companion to `mem_atom_range_of_isEigenvector`: a nonzero vector in the
range of `E {a}` has finite second moment (its vector-state measure is supported on the singleton)
and the identity spectral integral acts on it as multiplication by `a`.  Thus, for a
domain-aware spectral theorem, the atomic point spectrum and the operator's eigenvalues agree at
the level needed by later completeness arguments. -/
theorem isEigenvector_of_mem_atom_range
    {T : H →ₗ.[ℂ] H} {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}
    (D : DomainAwareSelfAdjointSpectralTheorem T μS)
    {x : H} {a : ℝ} (hx : μS {a} x ≠ 0) :
    ∃ v : H, ∃ hv : v ∈ T.domain, v ≠ 0 ∧
      T ⟨v, hv⟩ = (a : ℂ) • v := by
  let v : H := μS {a} x
  have hvne : v ≠ 0 := hx
  have hdiag : μS.diagonalMeasure v = (μS.diagonalMeasure x).restrict {a} := by
    dsimp [v]
    exact μS.diagonalMeasure_apply_eq_restrict {a} (measurableSet_singleton a) x
  have hmoment : Integrable (fun r : ℝ => r ^ 2) (μS.diagonalMeasure v) := by
    rw [hdiag]
    exact (integrableOn_singleton (f := fun r : ℝ => r ^ 2) (x := a)).integrable
  have hvdom : v ∈ T.domain := (D.mem_domain_iff v).2 hmoment
  refine ⟨v, hvdom, hvne, ?_⟩
  let M := QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral μS
  have hMdom : v ∈ M.domain := by
    change v ∈ QuantumMechanics.WOTSpectralMeasure.spectralSquareMomentSubmodule μS
    exact hmoment
  have hMT : M = T := D.maximal_eq
  have hscalar (y : H) : μS.scalarMeasure v y =
      (μS.scalarMeasure x y).restrict {a} := by
    dsimp [v]
    apply MeasureTheory.VectorMeasure.ext
    intro S hS
    rw [μS.scalarMeasure_apply,
      MeasureTheory.VectorMeasure.restrict_apply _ (measurableSet_singleton a) hS,
      μS.scalarMeasure_apply]
    change ⟪y, (μS S * μS {a}) x⟫_ℂ = _
    rw [μS.comp_eq_of_inter hS (measurableSet_singleton a)]
  apply ext_inner_left ℂ
  intro y
  letI : IsFiniteMeasure (μS.scalarMeasure x y).variation :=
    QuantumMechanics.WOTSpectralMeasure.scalarMeasure_isFiniteVariation μS x y
  letI : IsFiniteMeasure ((μS.scalarMeasure x y).restrict {a}).variation := by
    rw [MeasureTheory.VectorMeasure.variation_restrict (measurableSet_singleton a)]
    infer_instance
  have hfi : (μS.scalarMeasure v y).Integrable id := by
    rw [hscalar y]
    rw [MeasureTheory.VectorMeasure.Integrable,
      MeasureTheory.VectorMeasure.variation_restrict (measurableSet_singleton a)]
    apply MeasureTheory.Integrable.of_bound measurable_id.aestronglyMeasurable |a|
    filter_upwards [ae_restrict_mem (measurableSet_singleton a)] with r hr
    simp only [Set.mem_singleton_iff] at hr
    simpa [hr, Real.norm_eq_abs]
  have hweak : μS.complexWeakIntegral (fun r : ℝ => (r : ℂ)) v y =
      ⟪y, (a : ℂ) • v⟫_ℂ := by
    unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
    rw [hscalar y]
    have hconst :
        (∫ᵛ r, (r : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
          (μS.scalarMeasure x y).restrict {a}]) =
          ∫ᵛ _ : ℝ, (a : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
            (μS.scalarMeasure x y).restrict {a}] := by
      apply MeasureTheory.VectorMeasure.integral_congr_ae
      rw [MeasureTheory.VectorMeasure.variation_restrict (measurableSet_singleton a)]
      filter_upwards [ae_restrict_mem (measurableSet_singleton a)] with r hr
      simp only [Set.mem_singleton_iff] at hr
      rw [hr]
    rw [hconst, MeasureTheory.VectorMeasure.integral_const,
      MeasureTheory.VectorMeasure.restrict_apply_univ,
      μS.scalarMeasure_apply]
    simp [v, inner_smul_right]
  have hdomid :
      v ∈ (QuantumMechanics.WOTSpectralMeasure.measurableSpectralIntegral μS id
        measurable_id).domain := by
    change v ∈ QuantumMechanics.WOTSpectralMeasure.spectralSquareMomentSubmodule
      (μS.map id measurable_id)
    rw [μS.map_id]
    exact hmoment
  have hrec := measurableSpectralIntegral_inner_eq_complexWeakIntegral
    μS id measurable_id v hdomid y hfi
  have hmapop : QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
      (μS.map id measurable_id) = M := by
    dsimp [M]
    rw [μS.map_id]
  have hrec' :
      ⟪y, M ⟨v, hMdom⟩⟫_ℂ =
        μS.complexWeakIntegral (fun r : ℝ => (r : ℂ)) v y := by
    have hMval : (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
        (μS.map id measurable_id)) ⟨v, hdomid⟩ = M ⟨v, hMdom⟩ := by
      exact (LinearPMap.ext_iff.mp hmapop).2
        (x := v) (hf := hdomid) (hg := hMdom)
    calc
      ⟪y, M ⟨v, hMdom⟩⟫_ℂ =
          ⟪y, (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
            (μS.map id measurable_id)) ⟨v, hdomid⟩⟫_ℂ := by rw [hMval]
      _ = μS.complexWeakIntegral (fun r : ℝ => (r : ℂ)) v y := hrec
  have hleft :
      ⟪y, T ⟨v, hvdom⟩⟫_ℂ =
        μS.complexWeakIntegral (fun r : ℝ => (r : ℂ)) v y := by
    have hval : M ⟨v, hMdom⟩ = T ⟨v, hvdom⟩ := by
      exact (LinearPMap.ext_iff.mp hMT).2 (x := v) (hf := hMdom) (hg := hvdom)
    rw [← hval]
    exact hrec'
  calc
    ⟪y, T ⟨v, hvdom⟩⟫_ℂ =
        μS.complexWeakIntegral (fun r : ℝ => (r : ℂ)) v y := hleft
    _ = ⟪y, (a : ℂ) • v⟫_ℂ := hweak

/-! ### Atomic orthogonality for distinct eigenvalues -/

/-- An eigenvector is annihilated by every distinct atomic spectral projection.

This is the reusable orthogonality step behind diagonal-spectrum arguments.  The preceding
theorem says that an eigenvector with eigenvalue `λ` is fixed by `E {λ}`.  Since the PVM fibres at
`{c}` and `{λ}` are orthogonal when `c ≠ λ`, applying their product to the eigenvector gives
`E {c} v = 0`.  No completeness or special-function input is used here. -/
theorem atom_apply_eq_zero_of_isEigenvector_of_ne
    {T : H →ₗ.[ℂ] H} {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}
    (D : DomainAwareSelfAdjointSpectralTheorem T μS)
    {v : H} (hv : v ∈ T.domain) {a c : ℝ} (hav : T ⟨v, hv⟩ = (a : ℂ) • v)
    (hca : c ≠ a) :
    μS {c} v = 0 := by
  have hfix : μS {a} v = v :=
    mem_atom_range_of_isEigenvector D hv hav
  have hdisj : Disjoint ({c} : Set ℝ) ({a} : Set ℝ) := by
    simp [Set.disjoint_singleton, hca]
  have hcomp : μS {c} * μS {a} = 0 :=
    μS.comp_eq_of_inter (measurableSet_singleton c) (measurableSet_singleton a) |>.trans <| by
      rw [Set.disjoint_iff_inter_eq_empty.mp hdisj]
      simp
  have hcompv := congrArg (fun A : H →WOT[ℂ] H => A v) hcomp
  change μS {c} (μS {a} v) = 0 at hcompv
  rw [hfix] at hcompv
  exact hcompv

end OperatorAlgebra

end
