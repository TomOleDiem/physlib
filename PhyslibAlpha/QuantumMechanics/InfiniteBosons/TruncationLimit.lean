/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.LocalMoments
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Flow.Stone
/-!

# Comparison of a unitary group with an approximate evolution

A Duhamel estimate between the unitary group of a self-adjoint operator and a differentiable path
that solves the evolution equation up to a small error.

## i. Overview

Let `U t = exp(i t T)` be the unitary group of a self-adjoint operator `T`, and let `φ` be a
differentiable path in the domain of `T` with `‖φ'(s) - i T φ(s)‖ ≤ ε` for `0 ≤ s ≤ t`. Then
`‖U t φ(0) - φ(t)‖ ≤ ε t`. The proof differentiates `s ↦ U (t - s) φ(s)`, whose derivative is
`U (t - s) (φ'(s) - i T φ(s))`, and uses that `U` is isometric. This removes the truncation of the
finite-volume Bose-Hubbard dynamics: the truncated evolution solves the true evolution equation up
to the moves that leave the truncation, which are controlled by the truncated moment bound.

## ii. Key results

- `InfiniteBosons.norm_unitaryGroup_apply`: the unitary group is isometric.
- `InfiniteBosons.hasDerivAt_unitaryGroup_comp`: the derivative of `s ↦ U (t - s) φ(s)`.
- `InfiniteBosons.norm_unitaryGroup_sub_le`: the Duhamel estimate.

## iii. Table of contents

- A. Isometry
- B. The Duhamel estimate

## iv. References

* M. Reed, B. Simon, Methods of Modern Mathematical Physics I, Section VIII.4.
-/

@[expose] public section

noncomputable section

namespace InfiniteBosons

open ProbabilisticTheory ProbabilisticTheory.QuantumMechanics
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-!

## A. Isometry

-/

lemma inner_star_wot (A : H →WOT[ℂ] H) (x y : H) : inner ℂ (star A x) y = inner ℂ x (A y) := by
  rw [ContinuousLinearMapWOT.star_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

omit [CompleteSpace H] in
lemma wot_real_smul (A : H →WOT[ℂ] H) (c : ℝ) (v : H) : A (c • v) = c • A v := by
  rw [← Complex.coe_smul, map_smul, Complex.coe_smul]

/-- **A strongly continuous unitary group is isometric.** -/
lemma norm_unitaryGroup_apply (G : WOTSpectralMeasure.StrongUnitaryOneParameterGroup H) (t : ℝ)
    (x : H) : ‖G t x‖ = ‖x‖ := by
  have h1 : star (G t) * G t = 1 := Unitary.star_mul_self_of_mem (G.unitary t)
  have h2 : inner ℂ (G t x) (G t x) = inner ℂ x x := by
    rw [← inner_star_wot, ← ContinuousLinearMapWOT.mul_apply, h1]
    rfl
  have h3 : ‖G t x‖ ^ 2 = ‖x‖ ^ 2 := by
    have := congrArg RCLike.re h2
    rwa [inner_self_eq_norm_sq, inner_self_eq_norm_sq] at this
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3

/-!

## B. The Duhamel estimate

-/

variable {T : H →ₗ.[ℂ] H} {μS : WOTSpectralMeasure ℝ H}

/-- **The derivative of `s ↦ U (t - s) φ(s)`.** For a path `φ` differentiable at `s` with `φ(s)` in
the domain of `T`, the derivative is `U (t - s) (φ'(s) - i T φ(s))`. -/
lemma hasDerivAt_unitaryGroup_comp (D : DomainAwareSelfAdjointSpectralTheorem T μS) (t : ℝ)
    {φ : ℝ → H} {φ' : H} {s : ℝ} (hφ : HasDerivAt φ φ' s) (hdom : φ s ∈ T.domain) :
    HasDerivAt (fun r => D.expUnitaryGroup (t - r) (φ r))
      (D.expUnitaryGroup (t - s) (φ' - Complex.I • T ⟨φ s, hdom⟩)) s := by
  set U := D.expUnitaryGroup
  -- the part with the vector frozen at `φ(s)`
  have h1 : HasDerivAt (fun r => U (t - r) (φ s)) (-(U (t - s) (Complex.I • T ⟨φ s, hdom⟩))) s := by
    have hU := D.expUnitaryGroup_hasDerivAt ⟨φ s, hdom⟩ (t - s)
    have hlin : HasDerivAt (fun r : ℝ => t - r) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub t
    have := hU.scomp s hlin
    simpa [Function.comp_def] using this
  -- the part with the frozen operator applied to the increment of `φ`
  have h2 : HasDerivAt (fun r => U (t - r) (φ r - φ s)) (U (t - s) φ') s := by
    rw [hasDerivAt_iff_isLittleO]
    have hφo := hφ.isLittleO
    have hb : (fun r => U (t - r) (φ r - φ s - (r - s) • φ')) =O[𝓝 s]
        (fun r => φ r - φ s - (r - s) • φ') :=
      Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun r => by
        rw [norm_unitaryGroup_apply, one_mul])
    have hc : Filter.Tendsto (fun r => U (t - r) φ' - U (t - s) φ') (𝓝 s) (𝓝 0) := by
      have hcont := (D.expUnitaryGroup_continuous_apply φ').comp (continuous_sub_left t)
      have := (hcont.tendsto s).sub_const (U (t - s) φ')
      convert this using 2 <;> first | rfl | exact (sub_self (U (t - s) φ')).symm
    have hd : (fun r => (r - s) • (U (t - r) φ' - U (t - s) φ')) =o[𝓝 s] (fun r => r - s) := by
      have := (Asymptotics.isBigO_refl (fun r : ℝ => r - s) (𝓝 s)).smul_isLittleO
        ((Asymptotics.isLittleO_one_iff ℝ).mpr hc)
      simpa using this
    refine ((hb.trans_isLittleO hφo).add hd).congr_left fun r => ?_
    simp only [sub_self, map_zero, sub_zero, map_sub, wot_real_smul, smul_sub]
    abel
  have hsum := h1.add h2
  convert hsum using 1
  · funext r
    simp only [Pi.add_apply]
    rw [← map_add, add_sub_cancel]
  · rw [map_sub]; abel

/-- **Duhamel estimate.** If a path `φ` in the domain of `T` solves `φ' = i T φ` up to an error of
norm at most `ε` on `[0, t]`, then `‖U t φ(0) - φ(t)‖ ≤ ε t`. -/
theorem norm_unitaryGroup_sub_le (D : DomainAwareSelfAdjointSpectralTheorem T μS) {t : ℝ}
    (ht : 0 ≤ t) {φ φ' : ℝ → H} (hφ : ∀ s, HasDerivAt φ (φ' s) s) (hdom : ∀ s, φ s ∈ T.domain)
    {ε : ℝ} (hε : ∀ s ∈ Set.Icc 0 t, ‖φ' s - Complex.I • T ⟨φ s, hdom s⟩‖ ≤ ε) :
    ‖D.expUnitaryGroup t (φ 0) - φ t‖ ≤ ε * t := by
  set g : ℝ → H := fun r => D.expUnitaryGroup (t - r) (φ r)
  have hg : ∀ s, HasDerivAt g (D.expUnitaryGroup (t - s)
      (φ' s - Complex.I • T ⟨φ s, hdom s⟩)) s := fun s =>
    hasDerivAt_unitaryGroup_comp D t (hφ s) (hdom s)
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (C := ε)
    (fun s _ => (hg s).hasDerivWithinAt) (fun s hs => by
      rw [norm_unitaryGroup_apply]; exact hε s ⟨hs.1, hs.2.le⟩) t ⟨ht, le_rfl⟩
  have hg0 : g 0 = D.expUnitaryGroup t (φ 0) := by simp [g]
  have hgt : g t = φ t := by simp [g, D.expUnitaryGroup_zero]
  rw [hg0, hgt, sub_zero, norm_sub_rev] at hbound
  exact hbound


/-- The derivative of `s ↦ U (s - t) φ(s)`: `U (s - t) (φ'(s) + i T φ(s))`. -/
lemma hasDerivAt_unitaryGroup_comp_neg (D : DomainAwareSelfAdjointSpectralTheorem T μS) (t : ℝ)
    {φ : ℝ → H} {φ' : H} {s : ℝ} (hφ : HasDerivAt φ φ' s) (hdom : φ s ∈ T.domain) :
    HasDerivAt (fun r => D.expUnitaryGroup (r - t) (φ r))
      (D.expUnitaryGroup (s - t) (φ' + Complex.I • T ⟨φ s, hdom⟩)) s := by
  set U := D.expUnitaryGroup
  have h1 : HasDerivAt (fun r => U (r - t) (φ s)) (U (s - t) (Complex.I • T ⟨φ s, hdom⟩)) s := by
    have hU := D.expUnitaryGroup_hasDerivAt ⟨φ s, hdom⟩ (s - t)
    have hlin : HasDerivAt (fun r : ℝ => r - t) 1 s := by
      simpa using (hasDerivAt_id s).sub_const t
    have := hU.scomp s hlin
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun r => U (r - t) (φ r - φ s)) (U (s - t) φ') s := by
    rw [hasDerivAt_iff_isLittleO]
    have hb : (fun r => U (r - t) (φ r - φ s - (r - s) • φ')) =O[𝓝 s]
        (fun r => φ r - φ s - (r - s) • φ') :=
      Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun r => by
        rw [norm_unitaryGroup_apply, one_mul])
    have hc : Filter.Tendsto (fun r => U (r - t) φ' - U (s - t) φ') (𝓝 s) (𝓝 0) := by
      have hcont := (D.expUnitaryGroup_continuous_apply φ').comp (continuous_sub_right t)
      have := (hcont.tendsto s).sub_const (U (s - t) φ')
      convert this using 2 <;> first | rfl | exact (sub_self (U (s - t) φ')).symm
    have hd : (fun r => (r - s) • (U (r - t) φ' - U (s - t) φ')) =o[𝓝 s] (fun r => r - s) := by
      have := (Asymptotics.isBigO_refl (fun r : ℝ => r - s) (𝓝 s)).smul_isLittleO
        ((Asymptotics.isLittleO_one_iff ℝ).mpr hc)
      simpa using this
    refine ((hb.trans_isLittleO hφ.isLittleO).add hd).congr_left fun r => ?_
    simp only [sub_self, map_zero, sub_zero, map_sub, wot_real_smul, smul_sub]
    abel
  have hsum := h1.add h2
  convert hsum using 1
  · funext r
    simp only [Pi.add_apply]
    rw [← map_add, add_sub_cancel]
  · rw [map_add]; abel

/-- **Duhamel estimate backwards in time.** If `φ` solves `φ' = -i T φ` up to an error of norm at
most `ε` on `[0, t]`, then `‖U (-t) φ(0) - φ(t)‖ ≤ ε t`. -/
theorem norm_unitaryGroup_neg_sub_le (D : DomainAwareSelfAdjointSpectralTheorem T μS) {t : ℝ}
    (ht : 0 ≤ t) {φ φ' : ℝ → H} (hφ : ∀ s, HasDerivAt φ (φ' s) s) (hdom : ∀ s, φ s ∈ T.domain)
    {ε : ℝ} (hε : ∀ s ∈ Set.Icc 0 t, ‖φ' s + Complex.I • T ⟨φ s, hdom s⟩‖ ≤ ε) :
    ‖D.expUnitaryGroup (-t) (φ 0) - φ t‖ ≤ ε * t := by
  set g : ℝ → H := fun r => D.expUnitaryGroup (r - t) (φ r)
  have hg : ∀ s, HasDerivAt g (D.expUnitaryGroup (s - t)
      (φ' s + Complex.I • T ⟨φ s, hdom s⟩)) s := fun s =>
    hasDerivAt_unitaryGroup_comp_neg D t (hφ s) (hdom s)
  have hbound := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (C := ε)
    (fun s _ => (hg s).hasDerivWithinAt) (fun s hs => by
      rw [norm_unitaryGroup_apply]; exact hε s ⟨hs.1, hs.2.le⟩) t ⟨ht, le_rfl⟩
  have hg0 : g 0 = D.expUnitaryGroup (-t) (φ 0) := by simp [g]
  have hgt : g t = φ t := by simp [g, D.expUnitaryGroup_zero]
  rw [hg0, hgt, sub_zero, norm_sub_rev] at hbound
  exact hbound


/-!

## C. The truncated space inside the Fock space

-/

section Embedding

open Finsupp

variable {L : Type*} [DecidableEq L]

/-- The states supported in `Λ` with every occupation at most `K`. -/
def truncSet (Λ : Finset L) (K : ℕ) : Finset (Occ L) :=
  Finset.univ.image (fun φ : Λ → Fin (K + 1) => fillIn Λ 0 (fun x => (φ x : ℕ)))

lemma mem_truncSet {Λ : Finset L} {K : ℕ} {a : Occ L} :
    a ∈ truncSet Λ K ↔ (∀ z ∉ Λ, a z = 0) ∧ ∀ x ∈ Λ, a x ≤ K := by
  constructor
  · intro h
    obtain ⟨φ, -, rfl⟩ := Finset.mem_image.mp h
    refine ⟨fun z hz => ?_, fun x hx => ?_⟩
    · rw [fillIn_apply_not_mem _ _ _ hz]; rfl
    · rw [fillIn_apply_mem _ _ _ hx]; exact Nat.lt_succ_iff.mp (φ ⟨x, hx⟩).2
  · rintro ⟨hout, hin⟩
    refine Finset.mem_image.mpr ⟨fun x => ⟨a x.1, Nat.lt_succ_of_le (hin x.1 x.2)⟩,
      Finset.mem_univ _, Finsupp.ext fun z => ?_⟩
    by_cases hz : z ∈ Λ
    · rw [fillIn_apply_mem _ _ _ hz]
    · rw [fillIn_apply_not_mem _ _ _ hz, hout z hz]; rfl

/-- The finite vector of a vector of the truncated space. -/
def truncVec (S : Finset (Occ L)) : EuclideanSpace ℂ S →ₗ[ℂ] (Occ L →₀ ℂ) where
  toFun v := ∑ a : S, single a.1 (v a)
  map_add' v w := by simp [Finset.sum_add_distrib, single_add]
  map_smul' c v := by simp [Finset.smul_sum, smul_single]

lemma truncVec_apply (S : Finset (Occ L)) (v : EuclideanSpace ℂ S) (γ : Occ L) :
    truncVec S v γ = if h : γ ∈ S then v ⟨γ, h⟩ else 0 := by
  simp only [truncVec, LinearMap.coe_mk, AddHom.coe_mk, Finsupp.finsetSum_apply,
    Finsupp.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨γ, h⟩ (fun b _ hb => if_neg fun e => hb (Subtype.ext e))
      (by simp)]
    simp
  · exact Finset.sum_eq_zero fun b _ => if_neg fun (e : b.1 = γ) => h (e ▸ b.2)

end Embedding


/-!

## D. The leakage of the truncated evolution

-/

section Leakage

open Finsupp Matrix

variable {L : Type*} [DecidableEq L]

lemma apply_truncVec (S : Finset (Occ L)) (P : Adjointable (Occ L)) (v : EuclideanSpace ℂ S)
    (γ : Occ L) : P.1.1 (truncVec S v) γ = ∑ a : S, matEl P γ a.1 * v a := by
  simp only [truncVec, LinearMap.coe_mk, AddHom.coe_mk, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show (single a.1 (v a) : Occ L →₀ ℂ) = v a • single a.1 1 by simp [Finsupp.smul_single],
    map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  rfl

namespace BoseHubbardData

variable (D : BoseHubbardData L)

lemma toEuclideanCLM_truncHam_apply (V : L → ℕ → ℝ) (Λ : Finset L) (S : Finset (Occ L))
    (v : EuclideanSpace ℂ S) (a : S) :
    toEuclideanCLM (𝕜 := ℂ) (D.truncHam V Λ S) v a = ∑ b : S, matEl (D.finiteHam V Λ) a.1 b.1 * v b := by
  rw [show (toEuclideanCLM (𝕜 := ℂ) (D.truncHam V Λ S) v) a =
    (D.truncHam V Λ S *ᵥ (WithLp.ofLp v)) a from rfl, mulVec, dotProduct]
  rfl

/-- **The leakage is supported outside the truncation.** On states of `S`, the full Hamiltonian
applied to a truncated vector agrees with the truncated Hamiltonian. -/
lemma leak_apply_mem (V : L → ℕ → ℝ) (Λ : Finset L) (S : Finset (Occ L)) (v : EuclideanSpace ℂ S)
    {γ : Occ L} (hγ : γ ∈ S) :
    (D.finiteHam V Λ).1.1 (truncVec S v) γ -
      truncVec S (toEuclideanCLM (𝕜 := ℂ) (D.truncHam V Λ S) v) γ = 0 := by
  rw [apply_truncVec, truncVec_apply, dif_pos hγ, toEuclideanCLM_truncHam_apply, sub_self]

end BoseHubbardData

end Leakage


/-!

## E. The size of the leakage

-/

section LeakageBound

open Finsupp Matrix

variable {L : Type*} [DecidableEq L]

lemma norm_embed_sq_eq_sum {B : Type*} [DecidableEq B] (v : B →₀ ℂ) :
    ‖embed v‖ ^ 2 = ∑ γ ∈ v.support, ‖v γ‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_embed]
  unfold pair
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow]; exact Complex.ofReal_re _

/-- Cauchy-Schwarz for one row: `|Σ_a m_a v_a|² ≤ (Σ_a |m_a|) (Σ_a |m_a| |v_a|²)`. -/
lemma norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (m v : ι → ℂ) :
    ‖∑ a ∈ s, m a * v a‖ ^ 2 ≤ (∑ a ∈ s, ‖m a‖) * ∑ a ∈ s, ‖m a‖ * ‖v a‖ ^ 2 := by
  have h1 : ‖∑ a ∈ s, m a * v a‖ ≤ ∑ a ∈ s, Real.sqrt ‖m a‖ * (Real.sqrt ‖m a‖ * ‖v a‖) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
    rw [norm_mul, ← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun a => Real.sqrt ‖m a‖)
    (fun a => Real.sqrt ‖m a‖ * ‖v a‖)
  have e1 : ∀ a, Real.sqrt ‖m a‖ ^ 2 = ‖m a‖ := fun a => Real.sq_sqrt (norm_nonneg _)
  have e2 : ∀ a, (Real.sqrt ‖m a‖ * ‖v a‖) ^ 2 = ‖m a‖ * ‖v a‖ ^ 2 := fun a => by
    rw [mul_pow, e1]
  simp only [e1, e2] at h2
  calc ‖∑ a ∈ s, m a * v a‖ ^ 2
      ≤ (∑ a ∈ s, Real.sqrt ‖m a‖ * (Real.sqrt ‖m a‖ * ‖v a‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

end LeakageBound

end InfiniteBosons
