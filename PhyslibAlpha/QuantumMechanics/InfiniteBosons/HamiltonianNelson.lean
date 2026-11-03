/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.HamiltonianDynamics
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.AnalyticVector.Nelson
/-!

# Essential self-adjointness of number-conserving Hamiltonians by Nelson's theorem

A symmetric Hamiltonian that preserves a degree and is norm bounded on every degree sector is
essentially self-adjoint.

## i. Overview

Let the formal image of every basis vector be finitely supported. Then the Hamiltonian maps finite
vectors to finite vectors and can be iterated. Let `deg` be a degree on the basis, for instance the
total number of bosons and excited atoms, which the Hamiltonian does not raise. Let the Hamiltonian
be bounded on the vectors of degree at most `m` by a constant `B(m)`. Then `‖Hⁿ ψ‖ ≤ B(m)ⁿ ‖ψ‖` for
every finite `ψ` of degree at most `m`. The series `Σ ‖Hⁿ ψ‖ tⁿ / n!` converges for all `t`, so every
finite vector is an entire analytic vector. The finite vectors are dense. Nelson's theorem of the
Alpha tree gives essential self-adjointness. The hypotheses are statements about a model. They
are not fields of a structure.

## ii. Key results

- `InfiniteBosons.hAlg`: the Hamiltonian on finite vectors with values in finite vectors.
- `InfiniteBosons.hamPMap_ess_of_sector`: essential self-adjointness from sector bounds.
- `InfiniteBosons.norm_le_of_form_bound`: a form bound on an invariant subspace gives a norm bound.
- `InfiniteBosons.hamPMap_ess_of_form`: essential self-adjointness from a quadratic-form bound on
  every degree sector.

## iii. Table of contents

- A. The Hamiltonian on finite vectors
- B. Nelson's theorem

## iv. References

* E. Nelson, Analytic vectors, Ann. Math. 70 (1959) 572.
* M. Reed, B. Simon, Methods of Modern Mathematical Physics II, Theorem X.39.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {β ι : Type*} [DecidableEq β]

/-- If the formal image of every basis vector has finite support then so has the image of every
finite vector. -/
lemma formalH_finite_support (Φ : ι → Adjointable β) (h : RowFinite Φ)
    (hfin : ∀ b, {α | formalH Φ h (single b 1) α ≠ 0}.Finite) (f : β →₀ ℂ) :
    {α | formalH Φ h f α ≠ 0}.Finite := by
  have hf : f = ∑ b ∈ f.support, f b • single b (1 : ℂ) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    exact Finset.sum_congr rfl fun b _ => by simp [Finsupp.smul_single]
  refine Set.Finite.subset (f.support.finite_toSet.biUnion fun b _ => hfin b) fun α hα => ?_
  simp only [Set.mem_setOf_eq] at hα
  simp only [Set.mem_iUnion, Finset.mem_coe, Set.mem_setOf_eq]
  by_contra hn
  push Not at hn
  apply hα
  rw [hf, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_eq_zero fun b hb => by rw [hn b hb]; simp

/-- The Hamiltonian on finite vectors, valued in finite vectors. -/
def hAlg (Φ : ι → Adjointable β) (h : RowFinite Φ)
    (hfin : ∀ b, {α | formalH Φ h (single b 1) α ≠ 0}.Finite) (f : β →₀ ℂ) : β →₀ ℂ :=
  Finsupp.ofSupportFinite (formalH Φ h f) (formalH_finite_support Φ h hfin f)

lemma hAlg_apply (Φ : ι → Adjointable β) (h : RowFinite Φ)
    (hfin : ∀ b, {α | formalH Φ h (single b 1) α ≠ 0}.Finite) (f : β →₀ ℂ) (α : β) :
    hAlg Φ h hfin f α = formalH Φ h f α := rfl


lemma exists_basis_of_ne (Φ : ι → Adjointable β) (h : RowFinite Φ) (g : β →₀ ℂ) {α : β}
    (hα : formalH Φ h g α ≠ 0) : ∃ b ∈ g.support, formalH Φ h (single b 1) α ≠ 0 := by
  have hg : g = ∑ b ∈ g.support, g b • single b (1 : ℂ) := by
    conv_lhs => rw [← Finsupp.sum_single g]
    exact Finset.sum_congr rfl fun b _ => by simp [Finsupp.smul_single]
  by_contra hn
  push Not at hn
  apply hα
  rw [hg, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_eq_zero fun b hb => by rw [hn b hb]; simp

/-- **Essential self-adjointness from sector bounds (Nelson).** A symmetric Hamiltonian that
preserves a degree and is norm bounded on every degree sector has all finite vectors as entire
analytic vectors. -/
theorem hamPMap_ess_of_sector (Φ : ι → Adjointable β) (h : RowFinite Φ)
    (hs : ∀ i, star (Φ i) = Φ i)
    (hfin : ∀ b, {α | formalH Φ h (single b 1) α ≠ 0}.Finite) (deg : β → ℕ)
    (hdeg : ∀ b α, formalH Φ h (single b 1) α ≠ 0 → deg α ≤ deg b)
    (hnorm : ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ f : β →₀ ℂ, (∀ α ∈ f.support, deg α ≤ m) →
      ‖embed (hAlg Φ h hfin f)‖ ≤ B * ‖embed f‖) :
    (hamPMap Φ h).IsEssentiallySelfAdjoint := by
  have hmem : ∀ b, Memℓp (formalH Φ h (single b 1)) 2 := fun b => by
    rw [memℓp_gen_iff (by norm_num)]
    refine summable_of_ne_finset_zero (s := (hfin b).toFinset) fun a ha => ?_
    have h0 : formalH Φ h (single b 1) a = 0 := by
      by_contra hne; exact ha (by simpa using hne)
    simp [h0]
  have htop := hamDomainAlg_eq_top Φ h hmem
  have hsym := hamPMap_isSymmetric Φ h hs
  refine LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors hsym ?_
  have hanalytic : ∀ b, (hamPMap Φ h).IsAnalyticVector (embed (single b (1 : ℂ))) := by
    intro b
    obtain ⟨B, hB0, hB⟩ := hnorm (deg b)
    set w : ℕ → β →₀ ℂ := fun n => (hAlg Φ h hfin)^[n] (single b 1) with hw
    have hwdeg : ∀ n, (∀ α ∈ (w n).support, deg α ≤ deg b) ∧
        ‖embed (w n)‖ ≤ B ^ n * ‖embed (single b (1 : ℂ))‖ := by
      intro n
      induction n with
      | zero =>
        refine ⟨fun α hα => ?_, by simp [hw]⟩
        have : α = b := by simpa [hw] using Finsupp.support_single_subset hα
        simp [this]
      | succ n ih =>
        obtain ⟨hd, hn⟩ := ih
        have hwn : w (n + 1) = hAlg Φ h hfin (w n) := by
          simp only [hw, Function.iterate_succ_apply']
        refine ⟨fun α hα => ?_, ?_⟩
        · rw [hwn] at hα
          have hα' : formalH Φ h (w n) α ≠ 0 := by
            have := Finsupp.mem_support_iff.mp hα
            exact this
          obtain ⟨b0, hb0, hne⟩ := exists_basis_of_ne Φ h (w n) hα'
          exact (hdeg b0 α hne).trans (hd b0 hb0)
        · rw [hwn]
          calc ‖embed (hAlg Φ h hfin (w n))‖ ≤ B * ‖embed (w n)‖ := hB _ hd
            _ ≤ B * (B ^ n * ‖embed (single b (1 : ℂ))‖) := by gcongr
            _ = B ^ (n + 1) * ‖embed (single b (1 : ℂ))‖ := by ring
    have hwmem : ∀ n, embed (w n) ∈ (hamPMap Φ h).domain := fun n => by
      show embed (w n) ∈ (hamDomainAlg Φ h).map embed
      rw [htop]; exact Submodule.mem_map_of_mem trivial
    refine ⟨fun n => ⟨embed (w n), hwmem n⟩, ⟨rfl, ?_⟩, 1, one_pos, ?_⟩
    · intro n
      have hwn : w (n + 1) = hAlg Φ h hfin (w n) := by
        simp only [hw, Function.iterate_succ_apply']
      show embed (w (n + 1)) = (hamPMap Φ h) ⟨embed (w n), hwmem n⟩
      have := hamPMap_apply Φ h ⟨w n, by rw [htop]; trivial⟩
      rw [show (⟨embed (w n), hwmem n⟩ : (hamPMap Φ h).domain) =
        ⟨embed (w n), Submodule.mem_map_of_mem (by rw [htop]; trivial)⟩ from rfl, this, hwn]
      refine Subtype.ext (funext fun α => ?_)
      rw [embed_apply]; rfl
    · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        ((Real.summable_pow_div_factorial B).mul_left ‖embed (single b (1 : ℂ))‖)
      show ‖embed (w n)‖ * (1 : ℝ) ^ n / n.factorial ≤ _
      rw [one_pow, mul_one]
      calc ‖embed (w n)‖ / n.factorial ≤ (B ^ n * ‖embed (single b (1 : ℂ))‖) / n.factorial := by
            gcongr; exact (hwdeg n).2
        _ = _ := by ring
  rw [eq_top_iff]
  have hd := dense_range_embed (B := β)
  intro x _
  have hsub : (LinearMap.range (embed : (β →₀ ℂ) →ₗ[ℂ] HilbertSp β)) ≤
      Submodule.span ℂ {x : HilbertSp β | (hamPMap Φ h).IsAnalyticVector x} := by
    rintro _ ⟨f, rfl⟩
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | single α c =>
      have : (single α c : β →₀ ℂ) = c • single α 1 := by simp [Finsupp.smul_single]
      rw [this, map_smul]
      exact Submodule.smul_mem _ c (Submodule.subset_span (hanalytic α))
  exact closure_mono (show ((LinearMap.range (embed : (β →₀ ℂ) →ₗ[ℂ] HilbertSp β)) :
    Set (HilbertSp β)) ⊆ _ from hsub) (hd x)

theorem norm_le_of_form_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (V : Submodule ℂ E) (T : V →ₗ[ℂ] V)
    (hsym : ∀ φ ψ : V, inner ℂ (φ : E) (T ψ : E) = inner ℂ (T φ : E) (ψ : E))
    (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ φ : V, |(inner ℂ (φ : E) (T φ : E)).re| ≤ c * ‖(φ : E)‖ ^ 2)
    (ψ : V) : ‖(T ψ : E)‖ ≤ c * ‖(ψ : E)‖ := by
  by_cases h0 : (T ψ : E) = 0
  · rw [h0, norm_zero]; positivity
  by_cases hψ : (ψ : E) = 0
  · exfalso
    have : ψ = 0 := Subtype.ext hψ
    apply h0; simp [this]
  have hTψ : 0 < ‖(T ψ : E)‖ := norm_pos_iff.mpr h0
  have hψn : 0 < ‖(ψ : E)‖ := norm_pos_iff.mpr hψ
  set t : ℝ := ‖(ψ : E)‖ / ‖(T ψ : E)‖ with ht
  have htpos : 0 < t := by positivity
  set φ : V := (t : ℂ) • T ψ with hφ
  have key : ∀ (a b : V), 4 * (inner ℂ (a : E) (T b : E)).re =
      (inner ℂ ((a + b : V) : E) (T (a + b) : E)).re - (inner ℂ ((a - b : V) : E) (T (a - b) : E)).re := by
    intro a b
    have e1 : inner ℂ ((a + b : V) : E) (T (a + b) : E) =
        inner ℂ (a : E) (T a : E) + inner ℂ (a : E) (T b : E) + inner ℂ (b : E) (T a : E) +
          inner ℂ (b : E) (T b : E) := by
      simp only [map_add, Submodule.coe_add, inner_add_left, inner_add_right]; ring
    have e2 : inner ℂ ((a - b : V) : E) (T (a - b) : E) =
        inner ℂ (a : E) (T a : E) - inner ℂ (a : E) (T b : E) - inner ℂ (b : E) (T a : E) +
          inner ℂ (b : E) (T b : E) := by
      simp only [map_sub, Submodule.coe_sub, inner_sub_left, inner_sub_right]; ring
    have e3 : inner ℂ (b : E) (T a : E) = starRingEnd ℂ (inner ℂ (a : E) (T b : E)) := by
      rw [hsym b a]; exact (inner_conj_symm (T b : E) (a : E)).symm
    rw [e1, e2, e3]
    simp only [Complex.add_re, Complex.sub_re, Complex.conj_re]
    ring
  have hk := key φ ψ
  have hp : ‖((φ + ψ : V) : E)‖ ^ 2 + ‖((φ - ψ : V) : E)‖ ^ 2 =
      2 * (‖(φ : E)‖ ^ 2 + ‖(ψ : E)‖ ^ 2) := by
    have := parallelogram_law_with_norm ℂ (φ : E) (ψ : E)
    simp only [Submodule.coe_add, Submodule.coe_sub]
    nlinarith [this]
  have hbd : (inner ℂ ((φ + ψ : V) : E) (T (φ + ψ) : E)).re -
      (inner ℂ ((φ - ψ : V) : E) (T (φ - ψ) : E)).re ≤
      c * ‖((φ + ψ : V) : E)‖ ^ 2 + c * ‖((φ - ψ : V) : E)‖ ^ 2 := by
    have h1 := hc (φ + ψ)
    have h2 := hc (φ - ψ)
    have := (abs_le.mp h1).2
    have := (abs_le.mp h2).1
    linarith
  have hre : (inner ℂ (φ : E) (T ψ : E)).re = t * ‖(T ψ : E)‖ ^ 2 := by
    simp only [hφ, Submodule.coe_smul, inner_smul_left, Complex.conj_ofReal]
    rw [inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re]
    left
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hφn : ‖(φ : E)‖ ^ 2 = t ^ 2 * ‖(T ψ : E)‖ ^ 2 := by
    simp only [hφ, Submodule.coe_smul, norm_smul, mul_pow]
    simp [abs_of_pos htpos]
  have hts : t * ‖(T ψ : E)‖ = ‖(ψ : E)‖ := by
    rw [ht]; field_simp
  have h4 : 4 * (t * ‖(T ψ : E)‖ ^ 2) ≤ 2 * c * (t ^ 2 * ‖(T ψ : E)‖ ^ 2 + ‖(ψ : E)‖ ^ 2) := by
    rw [← hre, ← hφn]; nlinarith [hk, hbd, hp]
  have : t * ‖(T ψ : E)‖ ^ 2 = ‖(ψ : E)‖ * ‖(T ψ : E)‖ := by rw [← hts]; ring
  have h5 : t ^ 2 * ‖(T ψ : E)‖ ^ 2 = ‖(ψ : E)‖ ^ 2 := by rw [← hts]; ring
  rw [this, h5] at h4
  nlinarith [h4, hψn]



/-- The finite vectors of degree at most `m`. -/
def degSub (deg : β → ℕ) (m : ℕ) : Submodule ℂ (β →₀ ℂ) where
  carrier := {f | ∀ α ∈ f.support, deg α ≤ m}
  zero_mem' := by intro α hα; simp at hα
  add_mem' := fun {f g} hf hg α hα => by
    rcases Finset.mem_union.mp (Finsupp.support_add hα) with h1 | h1
    · exact hf α h1
    · exact hg α h1
  smul_mem' := fun c f hf α hα => hf α (Finsupp.support_smul hα)

lemma pairF'_eq_conj (u : Formal β) (f : β →₀ ℂ) :
    pairF' u f = starRingEnd ℂ (pairF f u) := by
  unfold pairF pairF'
  rw [map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp [mul_comm]


/-- `hAlg` as a linear map. -/
def hAlgL (Φ : ι → Adjointable β) (h : RowFinite Φ)
    (hfin : ∀ b, {α | formalH Φ h (single b 1) α ≠ 0}.Finite) : (β →₀ ℂ) →ₗ[ℂ] (β →₀ ℂ) where
  toFun := hAlg Φ h hfin
  map_add' f g := Finsupp.ext fun α => by
    simp only [hAlg_apply, map_add, Finsupp.coe_add, Pi.add_apply]
  map_smul' c f := Finsupp.ext fun α => by
    simp only [hAlg_apply, map_smul, Finsupp.coe_smul, Pi.smul_apply, RingHom.id_apply]

/-- **From a quadratic-form bound on each degree sector to a norm bound.** -/
theorem hnorm_of_form (Φ : ι → Adjointable β) (h : RowFinite Φ) (hs : ∀ i, star (Φ i) = Φ i)
    (hfin : ∀ b, {α | formalH Φ h (single b 1) α ≠ 0}.Finite) (deg : β → ℕ)
    (hdeg : ∀ b α, formalH Φ h (single b 1) α ≠ 0 → deg α ≤ deg b)
    (hform : ∀ m : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ φ : β →₀ ℂ, (∀ α ∈ φ.support, deg α ≤ m) →
      |(pairF φ (formalH Φ h φ)).re| ≤ c * ‖embed φ‖ ^ 2) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : β →₀ ℂ, (∀ α ∈ f.support, deg α ≤ m) →
      ‖embed (hAlg Φ h hfin f)‖ ≤ B * ‖embed f‖ := by
  obtain ⟨c, hc0, hc⟩ := hform m
  refine ⟨c, hc0, fun f hf => ?_⟩
  set V : Submodule ℂ (HilbertSp β) := (degSub deg m).map embed with hV
  have hpres : ∀ g ∈ degSub deg m, hAlg Φ h hfin g ∈ degSub deg m := fun g hg α hα => by
    have hα' : formalH Φ h g α ≠ 0 := Finsupp.mem_support_iff.mp hα
    obtain ⟨b0, hb0, hne⟩ := exists_basis_of_ne Φ h g hα'
    exact (hdeg b0 α hne).trans (hg b0 hb0)
  let e : degSub deg m ≃ₗ[ℂ] V :=
    Submodule.equivMapOfInjective embed embed_injective (degSub deg m)
  let T0 : degSub deg m →ₗ[ℂ] degSub deg m :=
    (hAlgL Φ h hfin).restrict (fun g hg => hpres g hg)
  let T : V →ₗ[ℂ] V := e.toLinearMap ∘ₗ T0 ∘ₗ e.symm.toLinearMap
  have hTe : ∀ g : degSub deg m, ((T (e g) : V) : HilbertSp β) = embed (hAlg Φ h hfin g.1) := by
    intro g
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rfl
  have heg : ∀ g : degSub deg m, ((e g : V) : HilbertSp β) = embed g.1 := fun g => rfl
  have hinner : ∀ φ ψ : degSub deg m,
      inner ℂ (embed φ.1) (embed (hAlg Φ h hfin ψ.1)) =
        inner ℂ (embed (hAlg Φ h hfin φ.1)) (embed ψ.1) := by
    intro φ ψ
    rw [inner_embed, inner_embed]
    show pairF φ.1 (formalH Φ h ψ.1) = pair (hAlg Φ h hfin φ.1) ψ.1
    rw [formalH_symmetric Φ h hs φ.1 ψ.1, pairF'_eq_conj]
    rw [pair_conj_symm]
    rfl
  have hsym : ∀ φ ψ : V, inner ℂ (φ : HilbertSp β) (T ψ : HilbertSp β) =
      inner ℂ (T φ : HilbertSp β) (ψ : HilbertSp β) := by
    intro φ ψ
    obtain ⟨φ', rfl⟩ := e.surjective φ
    obtain ⟨ψ', rfl⟩ := e.surjective ψ
    rw [heg, hTe, hTe, heg]
    exact hinner φ' ψ'
  have hbound := norm_le_of_form_bound V T hsym c hc0 (by
    intro φ
    obtain ⟨φ', rfl⟩ := e.surjective φ
    rw [heg, hTe]
    have := hc φ'.1 φ'.2
    rw [inner_embed]
    exact this)
  have := hbound (e ⟨f, hf⟩)
  rw [hTe, heg] at this
  exact this

/-- **Essential self-adjointness from a quadratic-form bound on each degree sector.** -/
theorem hamPMap_ess_of_form (Φ : ι → Adjointable β) (h : RowFinite Φ)
    (hs : ∀ i, star (Φ i) = Φ i)
    (hfin : ∀ b, {α | formalH Φ h (single b 1) α ≠ 0}.Finite) (deg : β → ℕ)
    (hdeg : ∀ b α, formalH Φ h (single b 1) α ≠ 0 → deg α ≤ deg b)
    (hform : ∀ m : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∀ φ : β →₀ ℂ, (∀ α ∈ φ.support, deg α ≤ m) →
      |(pairF φ (formalH Φ h φ)).re| ≤ c * ‖embed φ‖ ^ 2) :
    (hamPMap Φ h).IsEssentiallySelfAdjoint :=
  hamPMap_ess_of_sector Φ h hs hfin deg hdeg (hnorm_of_form Φ h hs hfin deg hdeg hform)

end InfiniteBosons
