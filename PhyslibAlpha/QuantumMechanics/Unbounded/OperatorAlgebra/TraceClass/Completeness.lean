/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.Space
public import Mathlib.Analysis.Normed.Group.Completeness

/-!
# Completeness of the trace-class Banach space

This file proves `CompleteSpace (TraceClass H)`.  The proof does not assume an already-built
`B(H)` predual (per the roadmap's requirement); it uses only the trace-norm ≥ operator-norm
domination already proved in `IdealNorm.lean` and the elementary "lower semicontinuity of the
trace norm under operator-norm convergence" fact, itself proved directly from the duality bound
via finite partial sums (`Real.tsum_le_of_sum_le`) — no compactness or spectral theory is used.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology Filter
open OperatorAlgebra Filter

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TraceClass

/-- **Lower semicontinuity of the trace norm under operator-norm convergence.** If a sequence of
trace-class operators with uniformly bounded trace norm converges in operator norm, its limit is
trace class with the same bound.  This is the single analytic fact needed for completeness: it
lets a trace-norm-Cauchy sequence's operator-norm limit be recognized as trace class, with a
quantitative tail bound. -/
theorem isTraceClass_of_tendsto_of_traceNorm_bounded {Tn : ℕ → B(H)} {T : B(H)} {C : ℝ}
    (hTn : ∀ n, IsTraceClass (Tn n)) (hbound : ∀ n, traceNorm (Tn n) (hTn n) ≤ C)
    (htendsto : Tendsto Tn atTop (𝓝 T)) :
    ∃ hT : IsTraceClass T, traceNorm T hT ≤ C := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  set W : B(H) := Polar.polarFactor T with hWdef
  have hWnorm : ‖W‖ ≤ 1 := Polar.polarFactor_opNorm_le T
  have hcont : ∀ i : w, Tendsto (fun n => ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) atTop
      (𝓝 ‖⟪W (b i), T (b i)⟫_ℂ‖) := by
    intro i
    have h1 : Tendsto (fun n => Tn n (b i)) atTop (𝓝 (T (b i))) := by
      have hev : Continuous (fun X : B(H) => X (b i)) :=
        (ContinuousLinearMap.apply ℂ H (b i : H)).continuous
      exact hev.continuousAt.tendsto.comp htendsto
    have h2 : Tendsto (fun n => ⟪W (b i), Tn n (b i)⟫_ℂ) atTop
        (𝓝 ⟪W (b i), T (b i)⟫_ℂ) :=
      (continuous_const.inner continuous_id).continuousAt.tendsto.comp h1
      |>.congr (fun _ => rfl) |>.mono_left le_rfl
    exact (continuous_norm.continuousAt.tendsto.comp h2)
  have hFinset : ∀ u : Finset w, (∑ i ∈ u, ‖⟪W (b i), T (b i)⟫_ℂ‖) ≤ C := by
    intro u
    have hpt : ∀ n, (∑ i ∈ u, ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) ≤ C := by
      intro n
      have hsum : Summable (fun i : w => ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) :=
        summable_norm_inner_contraction_of_isTraceClass (hTn n) hWnorm b
      have hall : (∑' i : w, ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) ≤ C :=
        (tsum_norm_inner_contraction_le_traceNorm (hTn n) hWnorm b).trans (hbound n)
      exact (hsum.sum_le_tsum u (fun i _ => norm_nonneg _)).trans hall
    have hlim : Tendsto (fun n => ∑ i ∈ u, ‖⟪W (b i), Tn n (b i)⟫_ℂ‖) atTop
        (𝓝 (∑ i ∈ u, ‖⟪W (b i), T (b i)⟫_ℂ‖)) :=
      tendsto_finsetSum u (fun i _ => hcont i)
    exact le_of_tendsto hlim (Eventually.of_forall hpt)
  have hsummable : Summable (fun i : w => ‖⟪W (b i), T (b i)⟫_ℂ‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hFinset
  have htsum_le : (∑' i : w, ‖⟪W (b i), T (b i)⟫_ℂ‖) ≤ C :=
    Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hFinset
  have hpoint : ∀ i : w, (⟪b i, CFC.abs T (b i)⟫_ℂ).re = ‖⟪W (b i), T (b i)⟫_ℂ‖ := by
    intro i
    have hval : ⟪b i, CFC.abs T (b i)⟫_ℂ = ⟪W (b i), T (b i)⟫_ℂ := by
      have habs : CFC.abs T = star W * T := (Polar.star_polarFactor_mul_self T).symm
      rw [habs, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.adjoint_inner_right W (b i) (T (b i))]
    have hpos : (CFC.abs T).IsPositive :=
      (operator_nonneg_iff_isPositive (CFC.abs T)).mp (CFC.abs_nonneg T)
    have hx := (ContinuousLinearMap.isPositive_iff_complex (CFC.abs T)).mp hpos (b i)
    have h1 : ⟪CFC.abs T (b i), b i⟫_ℂ = ((⟪CFC.abs T (b i), b i⟫_ℂ).re : ℂ) := hx.1.symm
    have hre : (⟪CFC.abs T (b i), b i⟫_ℂ).re = (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
      rw [← inner_conj_symm (CFC.abs T (b i)) (b i)]; exact Complex.conj_re _
    have heq : ⟪b i, CFC.abs T (b i)⟫_ℂ = ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ) := by
      calc
        ⟪b i, CFC.abs T (b i)⟫_ℂ = (starRingEnd ℂ) ⟪CFC.abs T (b i), b i⟫_ℂ :=
          (inner_conj_symm (b i) (CFC.abs T (b i))).symm
        _ = (starRingEnd ℂ) ((⟪CFC.abs T (b i), b i⟫_ℂ).re : ℂ) := congrArg (starRingEnd ℂ) h1
        _ = ((⟪CFC.abs T (b i), b i⟫_ℂ).re : ℂ) := by simp
        _ = ((⟪b i, CFC.abs T (b i)⟫_ℂ).re : ℂ) := by rw [hre]
    have hnonneg : 0 ≤ (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by rw [← hre]; exact hx.2
    rw [show ‖⟪W (b i), T (b i)⟫_ℂ‖ = ‖⟪b i, CFC.abs T (b i)⟫_ℂ‖ from by rw [hval],
      heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg, Complex.ofReal_re]
  have hT : IsTraceClass T := ⟨w, b, by
    apply hsummable.congr
    exact fun i => (hpoint i).symm⟩
  refine ⟨hT, ?_⟩
  rw [traceNorm_eq_of_hilbertBasis hT b]
  calc
    (∑' i : w, (⟪b i, CFC.abs T (b i)⟫_ℂ).re) = ∑' i : w, ‖⟪W (b i), T (b i)⟫_ℂ‖ :=
      tsum_congr hpoint
    _ ≤ C := htsum_le

/-- **Completeness of the trace-class Banach space.** Given an absolutely convergent series `u`
(`Σ‖uₙ‖₁ < ∞`), its partial sums `Sₙ` are Cauchy in operator norm (since operator norm ≤ trace
norm), hence converge in `B(H)` to some `S`; the lower-semicontinuity lemma above identifies `S`
as trace class (bounded by the full sum `M`), and applied again to the shifted tail sequence gives
the quantitative tail bound `‖⟨S,·⟩ - Sₙ‖₁ ≤ M - Σᵢ₌₀ⁿ⁻¹‖uᵢ‖₁ → 0`, which is exactly trace-norm
convergence of `Sₙ` to `S`. No `B(H)` predual is used. -/
noncomputable instance instCompleteSpace : CompleteSpace (TraceClass H) := by
  apply NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
  intro u hu
  set psum : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, ‖u i‖ with hpartialdef
  set M : ℝ := ∑' n, ‖u n‖ with hMdef
  set Sn : ℕ → TraceClass H := fun n => ∑ i ∈ Finset.range n, u i with hSndef
  set Tn : ℕ → B(H) := fun n => (Sn n).1 with hTndef
  have hpartial_le_M : ∀ n, psum n ≤ M := fun n => hu.sum_le_tsum _ (fun i _ => norm_nonneg _)
  have hpartial_tendsto : Tendsto psum atTop (𝓝 M) := hu.hasSum.tendsto_sum_nat
  set tail : ℕ → ℝ := fun n => M - psum n with htaildef
  have htail_tendsto : Tendsto tail atTop (𝓝 0) := by
    have := hpartial_tendsto.const_sub M
    simpa [htaildef] using this
  have hSn_diff : ∀ n m : ℕ, n ≤ m → Sn m - Sn n = ∑ i ∈ Finset.Ico n m, u i := by
    intro n m hnm
    simp only [hSndef]
    rw [Finset.sum_Ico_eq_sub _ hnm]
  have hpsum_split : ∀ n m : ℕ, n ≤ m →
      (∑ i ∈ Finset.Ico n m, ‖u i‖) = psum m - psum n := by
    intro n m hnm
    simp only [hpartialdef]
    rw [Finset.sum_Ico_eq_sub _ hnm]
  have htrace_tail_bound : ∀ n m : ℕ, n ≤ m → ‖Sn m - Sn n‖ ≤ tail n := by
    intro n m hnm
    rw [hSn_diff n m hnm]
    calc ‖∑ i ∈ Finset.Ico n m, u i‖ ≤ ∑ i ∈ Finset.Ico n m, ‖u i‖ := norm_sum_le _ _
      _ = psum m - psum n := hpsum_split n m hnm
      _ ≤ tail n := by simp only [htaildef]; linarith [hpartial_le_M m]
  have hSn_diff_coe : ∀ n m : ℕ, ((Sn m - Sn n : TraceClass H)).1 = Tn m - Tn n :=
    fun n m => Submodule.coe_sub _ _ _
  have htn_cauchy : CauchySeq Tn := by
    apply cauchySeq_of_le_tendsto_0' tail _ htail_tendsto
    intro n m hnm
    rw [dist_eq_norm]
    have heqop : Tn n - Tn m = -(Tn m - Tn n) := by abel
    rw [heqop, norm_neg, ← hSn_diff_coe n m]
    calc ‖((Sn m - Sn n : TraceClass H)).1‖ ≤ ‖(Sn m - Sn n : TraceClass H)‖ :=
          opNorm_le_traceNorm (isTraceClass_coe (Sn m - Sn n))
      _ ≤ tail n := htrace_tail_bound n m hnm
  obtain ⟨S, hStendsto⟩ := cauchySeq_tendsto_of_complete htn_cauchy
  have hSn_bound : ∀ n, traceNorm (Sn n).1 (isTraceClass_coe (Sn n)) ≤ M := by
    intro n
    show ‖Sn n‖ ≤ M
    calc ‖Sn n‖ ≤ ∑ i ∈ Finset.range n, ‖u i‖ := by
          simp only [hSndef]; exact norm_sum_le _ _
      _ = psum n := rfl
      _ ≤ M := hpartial_le_M n
  obtain ⟨hS, -⟩ := isTraceClass_of_tendsto_of_traceNorm_bounded
    (fun n => isTraceClass_coe (Sn n)) hSn_bound hStendsto
  refine ⟨ofOperator S hS, ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hbound_S : ∀ n, dist (Sn n) (ofOperator S hS : TraceClass H) ≤ tail n := by
    intro n
    rw [dist_eq_norm]
    have hVtrace : ∀ m, IsTraceClass (Tn (n + m) - Tn n) := by
      intro m
      rw [← hSn_diff_coe n (n + m)]
      exact isTraceClass_coe (Sn (n + m) - Sn n)
    have hVbound : ∀ m, traceNorm (Tn (n + m) - Tn n) (hVtrace m) ≤ tail n := by
      intro m
      have h1 : traceNorm (Tn (n + m) - Tn n) (hVtrace m) =
          traceNorm ((Sn (n + m) - Sn n : TraceClass H)).1
            (isTraceClass_coe (Sn (n + m) - Sn n)) := by
        have hEq : Tn (n + m) - Tn n = ((Sn (n + m) - Sn n : TraceClass H)).1 :=
          (hSn_diff_coe n (n + m)).symm
        exact traceNorm_transport hEq (hVtrace m)
      rw [h1]
      show ‖Sn (n + m) - Sn n‖ ≤ tail n
      exact htrace_tail_bound n (n + m) (Nat.le_add_right n m)
    have hVtendsto : Tendsto (fun m => Tn (n + m) - Tn n) atTop (𝓝 (S - Tn n)) := by
      have h1 : Tendsto (fun m => Tn (n + m)) atTop (𝓝 S) := by
        have h2 : Tendsto (fun m => Tn (m + n)) atTop (𝓝 S) :=
          hStendsto.comp (tendsto_add_atTop_nat n)
        simpa only [add_comm] using h2
      exact h1.sub tendsto_const_nhds
    obtain ⟨hSTn, hSTnbound⟩ := isTraceClass_of_tendsto_of_traceNorm_bounded hVtrace hVbound
      hVtendsto
    have heqfinal : ((ofOperator S hS : TraceClass H) - Sn n).1 = S - Tn n := rfl
    have hnorm_eq : ‖(ofOperator S hS : TraceClass H) - Sn n‖ = traceNorm (S - Tn n) hSTn := by
      have h3 : ‖(ofOperator S hS : TraceClass H) - Sn n‖ =
          traceNorm ((ofOperator S hS : TraceClass H) - Sn n).1
            (isTraceClass_coe ((ofOperator S hS : TraceClass H) - Sn n)) := rfl
      rw [h3]
      exact traceNorm_transport heqfinal (isTraceClass_coe ((ofOperator S hS : TraceClass H) - Sn
          n))
    rw [norm_sub_rev]
    rw [hnorm_eq]
    exact hSTnbound
  exact squeeze_zero (fun n => dist_nonneg) hbound_S htail_tendsto

end TraceClass

end OperatorAlgebra
