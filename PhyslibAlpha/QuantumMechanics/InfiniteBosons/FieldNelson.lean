/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FieldDegree
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.EssentialSelfAdjoint
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FieldTermSelfAdjoint
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.AnalyticVector.Nelson
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.CayleySpectralData.SpecTheorem
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.Flow.Stone
/-!

# The multi-mode field operator is essentially self-adjoint

Finite-particle vectors are analytic vectors of every field operator `φ(f)`. Nelson's theorem gives
essential self-adjointness, and the unbounded spectral theorem gives the Weyl operators.

## i. Overview

For a vector `ψ` with at most `m` bosons in the modes of `S` the field operator satisfies
`‖φ ψ‖ ≤ B √(m+1) ‖ψ‖` and raises the boson number by at most one. Hence
`‖φⁿ ψ‖ ≤ Bⁿ √((m+1)⋯(m+n)) ‖ψ‖`. The product is at most `(m+1)ⁿ n!`. The series
`Σ ‖φⁿ ψ‖ / n!` is bounded by a multiple of `Σ rⁿ/√(n!)` which converges by the ratio test. So
every finite-particle vector is an analytic vector. The finite-particle vectors span a dense
subspace. Nelson's theorem of `PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.AnalyticVector`
gives essential self-adjointness for an arbitrary finite set `S` of modes on an arbitrary lattice.
The spectral theorem for the closure gives the strongly continuous unitary group
`W(t f) = exp(i t φ(f))`. This is the Weyl operator of the phase space vector `f`.

## ii. Key results

- `InfiniteBosons.field_iter_bound`: the growth of the iterates.
- `InfiniteBosons.field_iter_summable`: the series of the iterates converges.
- `InfiniteBosons.field_isAnalyticVector`: finite-particle vectors are analytic.
- `InfiniteBosons.fieldOp_isEssentiallySelfAdjoint`: essential self-adjointness of `φ(f)`.
- `InfiniteBosons.fieldWeyl`: the unitary group `exp(i t φ(f))`.

## iii. Table of contents

- A. Growth of the iterates
- B. Analytic vectors
- C. Essential self-adjointness
- D. The Weyl operators

## iv. References

* E. Nelson, Analytic vectors, Ann. Math. 70 (1959) 572.
* M. Reed, B. Simon, Methods of Modern Mathematical Physics II, Theorem X.39.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- The iterates `φ^n ψ₀` of a vector under the field operator. -/
def fieldIter (S : Finset L) (q p : L →₀ ℝ) (ψ0 : Occ L →₀ ℂ) : ℕ → Occ L →₀ ℂ
  | 0 => ψ0
  | n + 1 => (fieldOp S q p).1.1 (fieldIter S q p ψ0 n)

/-- **Growth of the iterates**: degree `m + n` and the norm bound
`‖φⁿ ψ₀‖ ≤ Bⁿ √((m+1)⋯(m+n)) ‖ψ₀‖`. -/
theorem field_iter_bound {S : Finset L} {m : ℕ} {ψ0 : Occ L →₀ ℂ} (q p : L →₀ ℝ)
    (h : DegLE S m ψ0) (n : ℕ) :
    DegLE S (m + n) (fieldIter S q p ψ0 n) ∧
      ‖embed (fieldIter S q p ψ0 n)‖ ≤ fieldConst S q p ^ n *
        Real.sqrt (∏ k ∈ Finset.range n, ((m : ℝ) + k + 1)) * ‖embed ψ0‖ := by
  induction n with
  | zero => simpa [fieldIter] using h
  | succ n ih =>
    obtain ⟨hdeg, hnorm⟩ := ih
    obtain ⟨hs1, hs2⟩ := field_step (S := S) (m := m + n) q p hdeg
    refine ⟨by simpa [fieldIter, add_assoc] using hs2, ?_⟩
    show ‖embed ((fieldOp S q p).1.1 (fieldIter S q p ψ0 n))‖ ≤ _
    have hB : 0 ≤ fieldConst S q p := by unfold fieldConst; positivity
    calc ‖embed ((fieldOp S q p).1.1 (fieldIter S q p ψ0 n))‖
        ≤ fieldConst S q p * Real.sqrt (((m + n : ℕ) : ℝ) + 1) * ‖embed (fieldIter S q p ψ0 n)‖ := hs1
      _ ≤ fieldConst S q p * Real.sqrt (((m + n : ℕ) : ℝ) + 1) *
          (fieldConst S q p ^ n * Real.sqrt (∏ k ∈ Finset.range n, ((m : ℝ) + k + 1)) *
            ‖embed ψ0‖) := by gcongr
      _ = fieldConst S q p ^ (n + 1) *
          Real.sqrt (∏ k ∈ Finset.range (n + 1), ((m : ℝ) + k + 1)) * ‖embed ψ0‖ := by
        rw [Finset.prod_range_succ, Real.sqrt_mul (Finset.prod_nonneg fun k _ => by positivity)]
        push_cast
        ring


lemma summable_pow_div_sqrt_factorial (r : ℝ) (hr : 0 < r) :
    Summable fun n : ℕ => r ^ n / Real.sqrt (n.factorial) := by
  refine summable_of_ratio_test_tendsto_lt_one (l := 0) (by norm_num) ?_ ?_
  · exact Filter.Eventually.of_forall fun n => by positivity
  · have : ∀ n : ℕ, ‖r ^ (n + 1) / Real.sqrt ((n + 1).factorial)‖ /
        ‖r ^ n / Real.sqrt (n.factorial)‖ = r / Real.sqrt ((n : ℝ) + 1) := by
      intro n
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
        Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity)]
      push_cast
      have h1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have h2 : 0 < Real.sqrt (n.factorial : ℝ) := Real.sqrt_pos.mpr (by positivity)
      field_simp
      ring
    simp only [this]
    have h0 : Filter.Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1)) Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h0


lemma sqrt_pow' {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : Real.sqrt (x ^ n) = Real.sqrt x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

lemma prod_le_pow_mul_factorial (m n : ℕ) :
    ∏ k ∈ Finset.range n, ((m : ℝ) + k + 1) ≤ ((m : ℝ) + 1) ^ n * (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Nat.factorial_succ, pow_succ]
    push_cast
    have h1 : (m : ℝ) + n + 1 ≤ ((m : ℝ) + 1) * ((n : ℝ) + 1) := by
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc (∏ k ∈ Finset.range n, ((m : ℝ) + k + 1)) * ((m : ℝ) + n + 1)
        ≤ (((m : ℝ) + 1) ^ n * (n.factorial : ℝ)) * (((m : ℝ) + 1) * ((n : ℝ) + 1)) := by
          gcongr
      _ = _ := by ring

/-- **Analyticity of the finite-particle vectors**: the series `Σ ‖φⁿψ₀‖ / n!` converges. -/
theorem field_iter_summable {S : Finset L} {m : ℕ} {ψ0 : Occ L →₀ ℂ} (q p : L →₀ ℝ)
    (h : DegLE S m ψ0) :
    Summable fun n : ℕ => ‖embed (fieldIter S q p ψ0 n)‖ * (1 : ℝ) ^ n / n.factorial := by
  set B : ℝ := fieldConst S q p + 1 with hB
  have hB0 : 0 ≤ fieldConst S q p := by unfold fieldConst; positivity
  have hBpos : 0 < B := by rw [hB]; linarith
  have hr : 0 < B * Real.sqrt ((m : ℝ) + 1) := by positivity
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_pow_div_sqrt_factorial _ hr).mul_left ‖embed ψ0‖)
  obtain ⟨-, hn⟩ := field_iter_bound q p h n
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have hsf : 0 < Real.sqrt (n.factorial : ℝ) := Real.sqrt_pos.mpr hfac
  have hP : Real.sqrt (∏ k ∈ Finset.range n, ((m : ℝ) + k + 1)) ≤
      Real.sqrt ((m : ℝ) + 1) ^ n * Real.sqrt (n.factorial : ℝ) := by
    calc _ ≤ Real.sqrt (((m : ℝ) + 1) ^ n * (n.factorial : ℝ)) :=
          Real.sqrt_le_sqrt (prod_le_pow_mul_factorial m n)
      _ = _ := by rw [Real.sqrt_mul (by positivity), sqrt_pow' (by positivity) n]
  have hBn : fieldConst S q p ^ n ≤ B ^ n := pow_le_pow_left₀ hB0 (by linarith) n
  have hsq : (n.factorial : ℝ) = Real.sqrt (n.factorial : ℝ) * Real.sqrt (n.factorial : ℝ) :=
    (Real.mul_self_sqrt hfac.le).symm
  calc ‖embed (fieldIter S q p ψ0 n)‖ * (1 : ℝ) ^ n / n.factorial
      = ‖embed (fieldIter S q p ψ0 n)‖ / n.factorial := by simp
    _ ≤ (fieldConst S q p ^ n * Real.sqrt (∏ k ∈ Finset.range n, ((m : ℝ) + k + 1)) *
          ‖embed ψ0‖) / n.factorial := by gcongr
    _ ≤ (B ^ n * (Real.sqrt ((m : ℝ) + 1) ^ n * Real.sqrt (n.factorial : ℝ)) * ‖embed ψ0‖) /
          n.factorial := by
        gcongr
    _ = ‖embed ψ0‖ * ((B * Real.sqrt ((m : ℝ) + 1)) ^ n / Real.sqrt (n.factorial : ℝ)) := by
        obtain ⟨t, ht⟩ : ∃ t, t = Real.sqrt (n.factorial : ℝ) := ⟨_, rfl⟩
        have htpos : 0 < t := ht ▸ hsf
        rw [← ht]
        rw [hsq, ← ht]
        rw [mul_pow]
        field_simp


/-- The finite-particle vectors are analytic vectors of the field operator. -/
theorem field_isAnalyticVector {S : Finset L} {m : ℕ} {ψ0 : Occ L →₀ ℂ} (q p : L →₀ ℝ)
    (h : DegLE S m ψ0) : (polyOp (fieldOp S q p)).IsAnalyticVector (embed ψ0) := by
  refine ⟨fun n => ⟨embed (fieldIter S q p ψ0 n), LinearMap.mem_range_self embed _⟩, ⟨rfl, ?_⟩,
    1, one_pos, ?_⟩
  · intro n
    show embed (fieldIter S q p ψ0 (n + 1)) = (polyOp (fieldOp S q p)) _
    rw [polyOp_embed]; rfl
  · exact field_iter_summable q p h


/-- **The multi-mode field operator `φ(f)` is essentially self-adjoint** on the algebraic Fock
space of an arbitrary lattice, by Nelson's analytic-vector theorem. -/
theorem fieldOp_isEssentiallySelfAdjoint (S : Finset L) (q p : L →₀ ℝ) :
    (polyOp (fieldOp S q p)).IsEssentiallySelfAdjoint := by
  have hsym : (polyOp (fieldOp S q p)).IsSymmetric := by
    have := polyOp_formalAdjoint (fieldOp S q p)
    rwa [star_fieldOp] at this
  refine LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors hsym ?_
  have hsub : LinearMap.range (embed : (Occ L →₀ ℂ) →ₗ[ℂ] HilbertSp (Occ L)) ≤
      (Submodule.span ℂ {x : HilbertSp (Occ L) | (polyOp (fieldOp S q p)).IsAnalyticVector x}) := by
    rintro _ ⟨f, rfl⟩
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | single α c =>
      have : (single α c : Occ L →₀ ℂ) = c • single α 1 := by simp [Finsupp.smul_single]
      rw [this, map_smul]
      refine Submodule.smul_mem _ c (Submodule.subset_span ?_)
      exact field_isAnalyticVector q p (m := ∑ y ∈ S, α y) (ψ0 := single α 1) (S := S) (by
        intro β hβ
        have := Finsupp.support_single_subset hβ
        rw [Finset.mem_singleton] at this
        rw [this])
  rw [eq_top_iff]
  have hd := dense_range_embed (B := Occ L)
  intro x _
  exact closure_mono (show ((LinearMap.range (embed : (Occ L →₀ ℂ) →ₗ[ℂ] HilbertSp (Occ L))) :
    Set (HilbertSp (Occ L))) ⊆ _ from hsub) (hd x)


open ProbabilisticTheory ProbabilisticTheory.QuantumMechanics

set_option linter.defProp false in
/-- **The spectral theorem for the multi-mode field operator.** -/
def fieldSpectralMulti (S : Finset L) (q p : L →₀ ℝ) :=
  unboundedSpectralTheorem_of_essentiallySelfAdjoint (polyOp (fieldOp S q p))
    (fieldOp_isEssentiallySelfAdjoint S q p)

/-- **The Weyl operators**: the strongly continuous unitary group `t ↦ exp(i t φ(f))` of a phase
space vector `f = (q, p)` supported in the mode set `S`. -/
def fieldWeyl (S : Finset L) (q p : L →₀ ℝ) :=
  (fieldSpectralMulti S q p).expUnitaryGroup

lemma fieldWeyl_zero (S : Finset L) (q p : L →₀ ℝ) : fieldWeyl S q p 0 = 1 :=
  (fieldSpectralMulti S q p).expUnitaryGroup_zero

lemma fieldWeyl_add (S : Finset L) (q p : L →₀ ℝ) (t s : ℝ) :
    fieldWeyl S q p (t + s) = fieldWeyl S q p t * fieldWeyl S q p s :=
  (fieldSpectralMulti S q p).expUnitaryGroup_add t s

lemma fieldWeyl_continuous (S : Finset L) (q p : L →₀ ℝ) (v : HilbertSp (Occ L)) :
    Continuous fun t : ℝ => fieldWeyl S q p t v :=
  (fieldSpectralMulti S q p).expUnitaryGroup_continuous_apply v

lemma fieldWeyl_unitary (S : Finset L) (q p : L →₀ ℝ) (t : ℝ) :
    fieldWeyl S q p t ∈ unitary (HilbertSp (Occ L) →WOT[ℂ] HilbertSp (Occ L)) :=
  (fieldWeyl S q p).mem_unitary t

/-- **The generator**: the orbit of an algebraic vector has derivative `i φ(f) ψ`. -/
theorem fieldWeyl_hasDerivAt (S : Finset L) (q p : L →₀ ℝ) (f : Occ L →₀ ℂ) :
    HasDerivAt (fun t : ℝ => fieldWeyl S q p t (embed f))
      (Complex.I • embed ((fieldOp S q p).1.1 f)) 0 := by
  have hle := (polyOp (fieldOp S q p)).le_closure
  have hmem : embed f ∈ (polyOp (fieldOp S q p)).closure.domain :=
    hle.1 (LinearMap.mem_range_self embed f)
  have h := (fieldSpectralMulti S q p).expUnitaryGroup_hasDerivAt_zero ⟨embed f, hmem⟩
  have hval : (polyOp (fieldOp S q p)).closure ⟨embed f, hmem⟩ =
      embed ((fieldOp S q p).1.1 f) := by
    rw [← polyOp_embed (fieldOp S q p) f]
    exact (hle.2 (x := ⟨embed f, LinearMap.mem_range_self embed f⟩)
      (y := ⟨embed f, hmem⟩) rfl).symm
  rw [hval] at h
  exact h

end InfiniteBosons
