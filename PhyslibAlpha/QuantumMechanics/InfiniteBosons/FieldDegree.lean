/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.GraphNorm
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FieldOperator
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.HilbertSpace
/-!

# Degree bounds for the field operator

Groundwork for the analytic-vector argument for the multi-mode field operator.

## i. Overview

A finite-particle vector of degree at most `m` on a set `S` of modes satisfies
`Σ_{y ∈ S} ⟨ψ, N_y ψ⟩ ≤ m ‖ψ‖²`. This is the first estimate of the standard bound
`‖φ(f)^n ψ‖ ≤ B^n √((m+1)⋯(m+n)) ‖ψ‖`. That bound shows that the finite-particle vectors are
analytic vectors of the field operator `φ(f)`, so Nelson's theorem gives essential self-adjointness
of the multi-mode field operator. The one-step estimate `field_step` is proved here.

## ii. Key results

- `InfiniteBosons.qform_numberOp_eq_sum`: the quadratic form of `N_y` as a sum over the support.
- `InfiniteBosons.DegLE`: degree at most `m` on a set of modes.
- `InfiniteBosons.sum_qform_number_le`: the number estimate.
- `InfiniteBosons.smearAnn`, `InfiniteBosons.smearCre`: smeared annihilation and creation operators.
- `InfiniteBosons.smearAnn_smearCre_comm`: the smeared canonical commutation relation.
- `InfiniteBosons.norm_smearAnn_sq_le`, `InfiniteBosons.norm_smearCre_sq_le`: the norm bounds.
- `InfiniteBosons.field_step`: `‖φ ψ‖ ≤ B √(m+1) ‖ψ‖` and the degree grows by one.
- `InfiniteBosons.hopTerm_graph_bound`, `InfiniteBosons.hop_graph_bound`: the hopping operator is
  bounded relative to the reference operator, `‖hop f‖ ≤ 2 ‖K_X f‖`.
- `InfiniteBosons.pairing_graph_bound`: `‖a_x† a_y† f‖ ≤ ‖K_X f‖` and `‖a_x a_y f‖ ≤ ‖K_X f‖`.

## iii. Table of contents

- A. Number estimate

## iv. References

* M. Reed, B. Simon, Methods of Modern Mathematical Physics II, Theorem X.39 and Section X.7.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

lemma qform_numberOp_eq_sum (y : L) (ψ : Occ L →₀ ℂ) :
    (qform (numberOp y) ψ).re = ∑ α ∈ ψ.support, (α y : ℝ) * ‖ψ α‖ ^ 2 := by
  have h : qform (numberOp y) ψ = ∑ α ∈ ψ.support,
      starRingEnd ℂ (ψ α) * (((α y : ℕ) : ℂ) * ψ α) := by
    show pair ψ ((numberOp y).1.1 ψ) = _
    unfold pair
    refine Finset.sum_congr rfl fun α _ => ?_
    show starRingEnd ℂ (ψ α) * ((numberOp y).1.1 ψ) α = _
    rw [numberOp_apply_coord]
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have : starRingEnd ℂ (ψ α) * (((α y : ℕ) : ℂ) * ψ α) = (((α y : ℝ) * ‖ψ α‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_left_comm, mul_comm (starRingEnd ℂ (ψ α)), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [this, Complex.ofReal_re]

/-- Degree of the vectors: all occupation vectors in the support have total occupation in `S`
bounded by `m`. -/
def DegLE (S : Finset L) (m : ℕ) (ψ : Occ L →₀ ℂ) : Prop :=
  ∀ α ∈ ψ.support, ∑ y ∈ S, α y ≤ m

lemma sum_qform_number_le {S : Finset L} {m : ℕ} {ψ : Occ L →₀ ℂ} (h : DegLE S m ψ) :
    ∑ y ∈ S, (qform (numberOp y) ψ).re ≤ m * (pair ψ ψ).re := by
  simp only [qform_numberOp_eq_sum]
  rw [Finset.sum_comm]
  have hp : (pair ψ ψ).re = ∑ α ∈ ψ.support, ‖ψ α‖ ^ 2 := by
    unfold pair
    rw [Finsupp.sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    show (starRingEnd ℂ (ψ α) * ψ α).re = _
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [hp, Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα => ?_
  rw [← Finset.sum_mul]
  have : (∑ y ∈ S, (α y : ℝ)) ≤ m := by exact_mod_cast h α hα
  exact mul_le_mul_of_nonneg_right this (by positivity)

/-- The smeared annihilation operator `a(c) = Σ_{x ∈ S} c_x a_x`. -/
def smearAnn (S : Finset L) (c : L → ℂ) : adjointable L := ∑ x ∈ S, c x • annOp x

/-- The smeared creation operator `a†(c) = Σ_{x ∈ S} c̄_x a_x†`. -/
def smearCre (S : Finset L) (c : L → ℂ) : adjointable L :=
  ∑ x ∈ S, (starRingEnd ℂ (c x)) • creOp x

lemma star_smearAnn (S : Finset L) (c : L → ℂ) : star (smearAnn S c) = smearCre S c := by
  simp [smearAnn, smearCre, star_sum, star_smul, star_annOp, Complex.star_def]

/-- **The canonical commutation relation of smeared operators**: `[a(c), a†(c)] = Σ |c_x|²`. -/
lemma smearAnn_smearCre_comm (S : Finset L) (c : L → ℂ) :
    smearAnn S c * smearCre S c = smearCre S c * smearAnn S c +
      (((∑ x ∈ S, ‖c x‖ ^ 2 : ℝ)) : ℂ) • (1 : adjointable L) := by
  unfold smearAnn smearCre
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, annOp_creOp_comm, smul_add]
  simp only [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [mul_comm]
  · have : ∀ x ∈ S, ∑ y ∈ S, (starRingEnd ℂ (c y) * c x) • (if x = y then (1 : adjointable L) else 0) =
        ((‖c x‖ ^ 2 : ℝ) : ℂ) • (1 : adjointable L) := by
      intro x hx
      simp only [smul_ite, smul_zero]
      rw [Finset.sum_ite_eq S x (fun y => (starRingEnd ℂ (c y) * c x) • (1 : adjointable L))]
      simp only [hx, if_true]
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Finset.sum_congr rfl this, ← Finset.sum_smul]
    push_cast
    rfl


lemma smearAnn_apply (S : Finset L) (c : L → ℂ) (ψ : Occ L →₀ ℂ) :
    (smearAnn S c).1.1 ψ = ∑ x ∈ S, c x • (annOp x).1.1 ψ := by
  induction S using Finset.induction_on with
  | empty =>
    have : smearAnn (∅ : Finset L) c = 0 := by simp [smearAnn]
    rw [this]; simp
  | insert a T ha ih =>
    have : smearAnn (insert a T) c = c a • annOp a + smearAnn T c := by
      simp [smearAnn, Finset.sum_insert ha]
    rw [this, Finset.sum_insert ha]
    show (c a • annOp a).1.1 ψ + (smearAnn T c).1.1 ψ = _
    rw [ih]; rfl

lemma smearCre_apply (S : Finset L) (c : L → ℂ) (ψ : Occ L →₀ ℂ) :
    (smearCre S c).1.1 ψ = ∑ x ∈ S, starRingEnd ℂ (c x) • (creOp x).1.1 ψ := by
  induction S using Finset.induction_on with
  | empty =>
    have : smearCre (∅ : Finset L) c = 0 := by simp [smearCre]
    rw [this]; simp
  | insert a T ha ih =>
    have : smearCre (insert a T) c = starRingEnd ℂ (c a) • creOp a + smearCre T c := by
      simp [smearCre, Finset.sum_insert ha]
    rw [this, Finset.sum_insert ha]
    show (starRingEnd ℂ (c a) • creOp a).1.1 ψ + (smearCre T c).1.1 ψ = _
    rw [ih]; rfl

/-- The squared Hilbert norm of an algebraic vector. -/
lemma norm_embed_sq (v : Occ L →₀ ℂ) : ‖embed v‖ ^ 2 = (pair v v).re := by
  rw [← inner_embed v v]
  have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed v)
  rw [this]; simp [pow_two, Complex.mul_re]

lemma norm_annOp_sq (x : L) (ψ : Occ L →₀ ℂ) :
    ‖embed ((annOp x).1.1 ψ)‖ ^ 2 = (qform (numberOp x) ψ).re := by
  rw [norm_embed_sq]
  have : numberOp x = star (annOp x) * annOp x := by rw [star_annOp]; rfl
  rw [this, qform_star_mul_self]

/-- **Bound of the smeared annihilation operator.** For a vector of degree at most `m` on `S`:
`‖a(c) ψ‖² ≤ (Σ |c_x|²) m ‖ψ‖²`. -/
theorem norm_smearAnn_sq_le {S : Finset L} {m : ℕ} {ψ : Occ L →₀ ℂ} (c : L → ℂ)
    (h : DegLE S m ψ) :
    ‖embed ((smearAnn S c).1.1 ψ)‖ ^ 2 ≤ (∑ x ∈ S, ‖c x‖ ^ 2) * (m * ‖embed ψ‖ ^ 2) := by
  have hs : embed ((smearAnn S c).1.1 ψ) = ∑ x ∈ S, c x • embed ((annOp x).1.1 ψ) := by
    rw [smearAnn_apply, map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_smul]
  rw [hs]
  calc ‖∑ x ∈ S, c x • embed ((annOp x).1.1 ψ)‖ ^ 2
      ≤ (∑ x ∈ S, ‖c x‖ * ‖embed ((annOp x).1.1 ψ)‖) ^ 2 := by
        gcongr
        refine (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun x _ => by rw [norm_smul]
    _ ≤ (∑ x ∈ S, ‖c x‖ ^ 2) * ∑ x ∈ S, ‖embed ((annOp x).1.1 ψ)‖ ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq S _ _
    _ ≤ (∑ x ∈ S, ‖c x‖ ^ 2) * (m * ‖embed ψ‖ ^ 2) := by
        gcongr
        simp only [norm_annOp_sq]
        rw [norm_embed_sq]
        exact sum_qform_number_le h


/-- A generic support lemma: an operator that sends basis vectors to multiples of basis vectors
`σ α` has image support inside `σ` of the support. -/
lemma support_apply_subset (T : (Occ L →₀ ℂ) →ₗ[ℂ] (Occ L →₀ ℂ)) (σ : Occ L → Occ L)
    (hT : ∀ α, (T (single α 1)).support ⊆ {σ α}) (ψ : Occ L →₀ ℂ) :
    (T ψ).support ⊆ ψ.support.image σ := by
  have hψ : ψ = ∑ α ∈ ψ.support, single α (ψ α) := (Finsupp.sum_single ψ).symm
  conv_lhs => rw [hψ]
  rw [map_sum]
  refine Finsupp.support_finset_sum.trans ?_
  refine Finset.biUnion_subset.mpr fun α hα => ?_
  have : single α (ψ α) = ψ α • single α (1 : ℂ) := by simp [Finsupp.smul_single]
  rw [this, map_smul]
  refine (Finsupp.support_smul).trans ?_
  exact (hT α).trans (by simpa using Finset.mem_image_of_mem σ hα)

lemma degLE_annOp {S : Finset L} {m : ℕ} {ψ : Occ L →₀ ℂ} (x : L) (h : DegLE S m ψ) :
    DegLE S m ((annOp x).1.1 ψ) := by
  intro β hβ
  have := support_apply_subset (ann x) (fun α => α - single x 1) (fun α => by
    rw [ann_single]; exact Finsupp.support_single_subset) ψ hβ
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp this
  refine le_trans (Finset.sum_le_sum fun y _ => ?_) (h α hα)
  simp [Finsupp.tsub_apply]

lemma degLE_creOp {S : Finset L} {m : ℕ} {ψ : Occ L →₀ ℂ} (x : L) (h : DegLE S m ψ) :
    DegLE S (m + 1) ((creOp x).1.1 ψ) := by
  intro β hβ
  have := support_apply_subset (cre x) (fun α => α + single x 1) (fun α => by
    rw [cre_single]; exact Finsupp.support_single_subset) ψ hβ
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp this
  have h1 := h α hα
  have h2 : ∑ y ∈ S, (α + single x 1 : Occ L) y ≤ ∑ y ∈ S, α y + 1 := by
    simp only [Finsupp.add_apply, Finset.sum_add_distrib]
    gcongr
    calc ∑ y ∈ S, (single x 1 : Occ L) y ≤ ∑ y ∈ S, (if y = x then 1 else 0) := by
          refine Finset.sum_le_sum fun y _ => ?_
          by_cases hy : y = x <;> simp [Finsupp.single_apply, hy, eq_comm]
      _ ≤ 1 := by
          rw [Finset.sum_ite_eq']; split_ifs <;> simp
  omega


lemma degLE_sum {S : Finset L} {m : ℕ} {ι : Type*} (T : Finset ι) (v : ι → Occ L →₀ ℂ)
    (h : ∀ i ∈ T, DegLE S m (v i)) : DegLE S m (∑ i ∈ T, v i) := by
  intro β hβ
  obtain ⟨i, hi, hβi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hβ)
  exact h i hi β hβi

lemma degLE_smul {S : Finset L} {m : ℕ} {ψ : Occ L →₀ ℂ} (r : ℂ) (h : DegLE S m ψ) :
    DegLE S m (r • ψ) := fun β hβ => h β (Finsupp.support_smul hβ)

lemma degLE_smearAnn {S : Finset L} {m : ℕ} {ψ : Occ L →₀ ℂ} (c : L → ℂ) (h : DegLE S m ψ) :
    DegLE S m ((smearAnn S c).1.1 ψ) := by
  rw [smearAnn_apply]
  exact degLE_sum _ _ fun x _ => degLE_smul _ (degLE_annOp x h)

lemma degLE_smearCre {S : Finset L} {m : ℕ} {ψ : Occ L →₀ ℂ} (c : L → ℂ) (h : DegLE S m ψ) : DegLE S (m + 1) ((smearCre S c).1.1 ψ) := by
  rw [smearCre_apply]
  exact degLE_sum _ _ fun x _ => degLE_smul _ (degLE_creOp x h)

/-- **Bound of the smeared creation operator**: `‖a†(c) ψ‖² ≤ (Σ |c_x|²) (m + 1) ‖ψ‖²`. -/
theorem norm_smearCre_sq_le {S : Finset L} {m : ℕ} {ψ : Occ L →₀ ℂ} (c : L → ℂ)
    (h : DegLE S m ψ) :
    ‖embed ((smearCre S c).1.1 ψ)‖ ^ 2 ≤ (∑ x ∈ S, ‖c x‖ ^ 2) * ((m + 1) * ‖embed ψ‖ ^ 2) := by
  have hstar : star (smearCre S c) = smearAnn S c := by
    rw [← star_smearAnn, star_star]
  have hq1 : pair ((smearCre S c).1.1 ψ) ((smearCre S c).1.1 ψ) =
      qform (smearAnn S c * smearCre S c) ψ := by
    rw [← hstar, ← qform_star_mul_self, hstar]
  have hq2 : qform (smearCre S c * smearAnn S c) ψ =
      pair ((smearAnn S c).1.1 ψ) ((smearAnn S c).1.1 ψ) := by
    rw [← qform_star_mul_self, star_smearAnn]
  rw [norm_embed_sq, hq1, smearAnn_smearCre_comm, qform_add, qform_smul, hq2, Complex.add_re]
  have hA := norm_smearAnn_sq_le c h
  rw [norm_embed_sq, norm_embed_sq] at hA
  have hnn : (∑ x ∈ S, ‖c x‖ ^ 2 : ℝ) * (pair ψ ψ).re ≥ 0 :=
    mul_nonneg (Finset.sum_nonneg fun x _ => by positivity) (pair_self_nonneg ψ)
  have h3 : ((((∑ x ∈ S, ‖c x‖ ^ 2 : ℝ)) : ℂ) * qform (1 : adjointable L) ψ).re =
      (∑ x ∈ S, ‖c x‖ ^ 2 : ℝ) * (pair ψ ψ).re := by
    rw [qform_one, Complex.re_ofReal_mul]
  rw [h3]
  rw [norm_embed_sq ψ]
  nlinarith [hA]


lemma fieldOp_eq (S : Finset L) (q p : L →₀ ℝ) :
    fieldOp S q p = smearAnn S (fieldCoeff q p) + smearCre S (fieldCoeff q p) := by
  unfold fieldOp smearAnn smearCre fieldTerm
  rw [← Finset.sum_add_distrib]

/-- The constant `B = 2 (Σ |c_x|²)^{1/2}` of the field operator estimate. -/
def fieldConst (S : Finset L) (q p : L →₀ ℝ) : ℝ :=
  2 * Real.sqrt (∑ x ∈ S, ‖fieldCoeff q p x‖ ^ 2)

/-- **One-step estimate**: for a vector of degree at most `m` on `S`,
`‖φ ψ‖ ≤ B √(m+1) ‖ψ‖` and `φ ψ` has degree at most `m + 1`. -/
theorem field_step {S : Finset L} {m : ℕ} {ψ : Occ L →₀ ℂ} (q p : L →₀ ℝ) (h : DegLE S m ψ) :
    ‖embed ((fieldOp S q p).1.1 ψ)‖ ≤ fieldConst S q p * Real.sqrt (m + 1) * ‖embed ψ‖ ∧
      DegLE S (m + 1) ((fieldOp S q p).1.1 ψ) := by
  set C : ℝ := ∑ x ∈ S, ‖fieldCoeff q p x‖ ^ 2 with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun x _ => by positivity
  refine ⟨?_, ?_⟩
  · rw [fieldOp_eq]
    have e : ((smearAnn S (fieldCoeff q p) + smearCre S (fieldCoeff q p) : adjointable L).1.1) ψ =
        (smearAnn S (fieldCoeff q p)).1.1 ψ + (smearCre S (fieldCoeff q p)).1.1 ψ := rfl
    rw [e, map_add]
    have hA := norm_smearAnn_sq_le (ψ := ψ) (fieldCoeff q p) h
    have hB := norm_smearCre_sq_le (ψ := ψ) (fieldCoeff q p) h
    have key : ∀ (v : Occ L →₀ ℂ) (k : ℝ), 0 ≤ k → ‖embed v‖ ^ 2 ≤ C * (k * ‖embed ψ‖ ^ 2) →
        ‖embed v‖ ≤ Real.sqrt C * Real.sqrt k * ‖embed ψ‖ := by
      intro v k hk hv
      have : ‖embed v‖ ^ 2 ≤ (Real.sqrt C * Real.sqrt k * ‖embed ψ‖) ^ 2 := by
        calc ‖embed v‖ ^ 2 ≤ C * (k * ‖embed ψ‖ ^ 2) := hv
          _ = (Real.sqrt C * Real.sqrt k * ‖embed ψ‖) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt hC0, Real.sq_sqrt hk]; ring
      exact le_of_sq_le_sq this (by positivity)
    have h1 := key _ (m : ℝ) (by positivity) hA
    have h2 := key _ ((m : ℝ) + 1) (by positivity) hB
    have hm : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    calc ‖embed ((smearAnn S (fieldCoeff q p)).1.1 ψ) + embed ((smearCre S (fieldCoeff q p)).1.1 ψ)‖
        ≤ ‖embed ((smearAnn S (fieldCoeff q p)).1.1 ψ)‖ + ‖embed ((smearCre S (fieldCoeff q p)).1.1 ψ)‖ :=
          norm_add_le _ _
      _ ≤ Real.sqrt C * Real.sqrt ((m : ℝ) + 1) * ‖embed ψ‖ +
          Real.sqrt C * Real.sqrt ((m : ℝ) + 1) * ‖embed ψ‖ := by
          gcongr
          exact h1.trans (by gcongr)
      _ = fieldConst S q p * Real.sqrt ((m : ℝ) + 1) * ‖embed ψ‖ := by
          unfold fieldConst; rw [← hC]; ring
  · rw [fieldOp_eq]
    have e : ((smearAnn S (fieldCoeff q p) + smearCre S (fieldCoeff q p) : adjointable L).1.1) ψ =
        (smearAnn S (fieldCoeff q p)).1.1 ψ + (smearCre S (fieldCoeff q p)).1.1 ψ := rfl
    rw [e]
    intro β hβ
    rcases Finset.mem_union.mp (Finsupp.support_add hβ) with h' | h'
    · exact (degLE_smearAnn (fieldCoeff q p) h β h').trans (Nat.le_succ m)
    · exact degLE_smearCre (fieldCoeff q p) h β h'

lemma star_hopTerm_mul {x y : L} (hxy : x ≠ y) :
    star (creOp x * annOp y) * (creOp x * annOp y) = (numberOp x + 1) * numberOp y := by
  have h1 : annOp x * creOp x = creOp x * annOp x + 1 := by
    have := annOp_creOp_comm x x
    simpa using this
  have h2 : annOp x * creOp y = creOp y * annOp x := annOp_comm_creOp hxy
  have h5 : creOp x * creOp y = creOp y * creOp x := creOp_comm_creOp x y
  simp only [star_mul, star_annOp, star_creOp, numberOp]
  calc creOp y * annOp x * (creOp x * annOp y)
      = creOp y * (annOp x * creOp x) * annOp y := by simp only [mul_assoc]
    _ = creOp y * (creOp x * annOp x + 1) * annOp y := by rw [h1]
    _ = creOp y * creOp x * annOp x * annOp y + creOp y * annOp y := by
        simp only [mul_add, add_mul, mul_one, mul_assoc]
    _ = creOp x * (creOp y * annOp x) * annOp y + creOp y * annOp y := by
        rw [← h5]; simp only [mul_assoc]
    _ = creOp x * annOp x * (creOp y * annOp y) + creOp y * annOp y := by
        rw [← h2]; simp only [mul_assoc]
    _ = (creOp x * annOp x + 1) * (creOp y * annOp y) := by rw [add_mul, one_mul]


lemma numberOp_add_one_mul_coord (x y : L) (g : Occ L →₀ ℂ) (α : Occ L) :
    (((numberOp x + 1) * numberOp y).1.1 g) α = ((α x : ℂ) + 1) * ((α y : ℂ) * g α) := by
  show ((numberOp x).1.1 ((numberOp y).1.1 g) + (numberOp y).1.1 g) α = _
  rw [Finsupp.add_apply, numberOp_apply_coord, numberOp_apply_coord]
  ring

/-- **Relative bound of the hopping term**: for `x ≠ y` in `X`,
`‖a_x† a_y f‖ ≤ ‖K_X f‖`. -/
theorem hopTerm_graph_bound {X : Finset L} {x y : L} (hxy : x ≠ y) (hx : x ∈ X) (hy : y ∈ X)
    (f : Occ L →₀ ℂ) :
    ‖embed ((creOp x * annOp y).1.1 f)‖ ≤ ‖embed ((refOp X).1.1 f)‖ := by
  have hlhs : ‖embed ((creOp x * annOp y).1.1 f)‖ ^ 2 =
      ∑ α ∈ f.support, ((α x : ℝ) + 1) * (α y : ℝ) * ‖f α‖ ^ 2 := by
    rw [norm_embed_sq]
    have : (pair ((creOp x * annOp y).1.1 f) ((creOp x * annOp y).1.1 f)) =
        qform ((numberOp x + 1) * numberOp y) f := by
      rw [← star_hopTerm_mul hxy, qform_star_mul_self]
    rw [this]
    have h : qform ((numberOp x + 1) * numberOp y) f = ∑ α ∈ f.support,
        starRingEnd ℂ (f α) * (((α x : ℂ) + 1) * ((α y : ℂ) * f α)) := by
      show pair f (((numberOp x + 1) * numberOp y).1.1 f) = _
      unfold pair
      refine Finset.sum_congr rfl fun α _ => ?_
      show starRingEnd ℂ (f α) * (((numberOp x + 1) * numberOp y).1.1 f) α = _
      rw [numberOp_add_one_mul_coord]
    rw [h, Complex.re_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have : starRingEnd ℂ (f α) * (((α x : ℂ) + 1) * ((α y : ℂ) * f α)) =
        ((((α x : ℝ) + 1) * (α y : ℝ) * ‖f α‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_left_comm, mul_left_comm (starRingEnd ℂ (f α)), mul_comm (starRingEnd ℂ (f α)),
        Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    rw [this, Complex.ofReal_re]
  have hrhs : ‖embed ((refOp X).1.1 f)‖ ^ 2 =
      ∑ α ∈ f.support, (1 + ∑ z ∈ X, (α z : ℝ)) ^ 2 * ‖f α‖ ^ 2 := by
    rw [norm_embed_sq, pair_self_eq_sum _ (refOp_apply_coord X) f, Complex.re_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul]
    have hpos : (0 : ℝ) ≤ 1 + ∑ z ∈ X, (α z : ℝ) := by positivity
    have e : ∀ r s : ℝ, (((r : ℂ) ^ 2).re * ((s : ℂ) ^ 2).re -
        ((r : ℂ) ^ 2).im * ((s : ℂ) ^ 2).im) = r ^ 2 * s ^ 2 := by
      intro r s
      simp [pow_two, Complex.mul_re, Complex.mul_im]
    simp [mul_pow]
    have hc : (1 + ∑ x ∈ X, ((α x : ℕ) : ℂ)) = ((1 + ∑ z ∈ X, (α z : ℝ) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [e, hc, Complex.norm_real, Real.norm_of_nonneg hpos]
  refine le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [hlhs, hrhs]
  refine Finset.sum_le_sum fun α _ => ?_
  have hsum : (α x : ℝ) + α y ≤ ∑ z ∈ X, (α z : ℝ) := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun z => (α z : ℝ))
      (show ({x, y} : Finset L) ⊆ X by
        intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption)
      (fun z _ _ => by positivity)
    simpa [Finset.sum_pair hxy] using this
  have hxn : (0 : ℝ) ≤ α x := by positivity
  have hyn : (0 : ℝ) ≤ α y := by positivity
  have hle : ((α x : ℝ) + 1) * α y ≤ (1 + ∑ z ∈ X, (α z : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg ((α x : ℝ)), sq_nonneg ((α y : ℝ))]
  exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- **Relative bound of the hopping operator**: `‖hop x y f‖ ≤ 2 ‖K_X f‖` for `x ≠ y` in `X`. -/
theorem hop_graph_bound {X : Finset L} {x y : L} (hxy : x ≠ y) (hx : x ∈ X) (hy : y ∈ X)
    (f : Occ L →₀ ℂ) :
    ‖embed ((hop x y).1.1 f)‖ ≤ 2 * ‖embed ((refOp X).1.1 f)‖ := by
  have h1 := hopTerm_graph_bound hxy hx hy f
  have h2 := hopTerm_graph_bound hxy.symm hy hx f
  have e : (hop x y).1.1 f = (creOp x * annOp y).1.1 f + (creOp y * annOp x).1.1 f := rfl
  rw [e, map_add]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- If `A* A` is a diagonal operator then `‖A f‖²` is the weighted sum of `|f α|²`. -/
lemma norm_sq_of_starMul (A D : adjointable L) (d : Occ L → ℝ) (hAD : star A * A = D)
    (hD : ∀ g α, (D.1.1 g) α = (d α : ℂ) * g α) (f : Occ L →₀ ℂ) :
    ‖embed (A.1.1 f)‖ ^ 2 = ∑ α ∈ f.support, d α * ‖f α‖ ^ 2 := by
  rw [norm_embed_sq, ← qform_star_mul_self, hAD]
  have h : qform D f = ∑ α ∈ f.support, starRingEnd ℂ (f α) * ((d α : ℂ) * f α) := by
    show pair f (D.1.1 f) = _
    unfold pair
    refine Finset.sum_congr rfl fun α _ => ?_
    show starRingEnd ℂ (f α) * (D.1.1 f) α = _
    rw [hD]
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have : starRingEnd ℂ (f α) * ((d α : ℂ) * f α) = ((d α * ‖f α‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_left_comm, mul_comm (starRingEnd ℂ (f α)), Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [this, Complex.ofReal_re]


lemma star_creCre_mul {x y : L} (hxy : x ≠ y) :
    star (creOp x * creOp y) * (creOp x * creOp y) =
      (numberOp x + 1) * (numberOp y + 1) := by
  have h1 : annOp x * creOp x = creOp x * annOp x + 1 := by simpa using annOp_creOp_comm x x
  have h1y : annOp y * creOp y = creOp y * annOp y + 1 := by simpa using annOp_creOp_comm y y
  have hyx : annOp y * creOp x = creOp x * annOp y := annOp_comm_creOp hxy.symm
  have hxx : annOp y * annOp x = annOp x * annOp y := annOp_comm_annOp y x
  simp only [star_mul, star_annOp, star_creOp, numberOp]
  calc annOp y * annOp x * (creOp x * creOp y)
      = annOp y * (annOp x * creOp x) * creOp y := by simp only [mul_assoc]
    _ = annOp y * (creOp x * annOp x + 1) * creOp y := by rw [h1]
    _ = (annOp y * creOp x) * annOp x * creOp y + annOp y * creOp y := by
        simp only [mul_add, add_mul, mul_one, mul_assoc]
    _ = creOp x * (annOp y * annOp x) * creOp y + annOp y * creOp y := by
        rw [hyx]; simp only [mul_assoc]
    _ = creOp x * annOp x * (annOp y * creOp y) + annOp y * creOp y := by
        rw [hxx]; simp only [mul_assoc]
    _ = (creOp x * annOp x + 1) * (creOp y * annOp y + 1) := by
        rw [h1y]; simp only [mul_add, add_mul, mul_one, one_mul]; abel

lemma star_annAnn_mul {x y : L} (hxy : x ≠ y) :
    star (annOp x * annOp y) * (annOp x * annOp y) = numberOp x * numberOp y := by
  have h2 : annOp x * creOp y = creOp y * annOp x := annOp_comm_creOp hxy
  have h5 : creOp y * creOp x = creOp x * creOp y := creOp_comm_creOp y x
  simp only [star_mul, star_annOp, numberOp]
  calc creOp y * creOp x * (annOp x * annOp y)
      = creOp x * creOp y * (annOp x * annOp y) := by rw [h5]
    _ = creOp x * (creOp y * annOp x) * annOp y := by simp only [mul_assoc]
    _ = creOp x * (annOp x * creOp y) * annOp y := by rw [h2]
    _ = creOp x * annOp x * (creOp y * annOp y) := by simp only [mul_assoc]


lemma norm_sq_diag {T : (Occ L →₀ ℂ) →ₗ[ℂ] (Occ L →₀ ℂ)} (c : Occ L → ℝ)
    (hT : ∀ g α, (T g) α = (c α : ℂ) * g α) (f : Occ L →₀ ℂ) :
    ‖embed (T f)‖ ^ 2 = ∑ α ∈ f.support, c α ^ 2 * ‖f α‖ ^ 2 := by
  rw [norm_embed_sq, pair_self_eq_sum (fun α => (c α : ℂ)) hT f, Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hn : ‖(c α : ℂ) * f α‖ ^ 2 = c α ^ 2 * ‖f α‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have : starRingEnd ℂ ((c α : ℂ) * f α) * ((c α : ℂ) * f α) =
      ((c α ^ 2 * ‖f α‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
  rw [this, Complex.ofReal_re]

/-- **Relative bounds of the pairing terms**: for `x ≠ y` in `X`,
`‖a_x† a_y† f‖ ≤ ‖K_X f‖` and `‖a_x a_y f‖ ≤ ‖K_X f‖`. -/
theorem pairing_graph_bound {X : Finset L} {x y : L} (hxy : x ≠ y) (hx : x ∈ X) (hy : y ∈ X)
    (f : Occ L →₀ ℂ) :
    ‖embed ((creOp x * creOp y).1.1 f)‖ ≤ ‖embed ((refOp X).1.1 f)‖ ∧
      ‖embed ((annOp x * annOp y).1.1 f)‖ ≤ ‖embed ((refOp X).1.1 f)‖ := by
  have hK := norm_sq_diag (T := (refOp X).1.1) (fun α => 1 + ∑ z ∈ X, (α z : ℝ))
    (by intro g α; rw [refOp_apply_coord]) f
  have hsum : ∀ α : Occ L, (α x : ℝ) + α y ≤ ∑ z ∈ X, (α z : ℝ) := fun α => by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun z => (α z : ℝ))
      (show ({x, y} : Finset L) ⊆ X by
        intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption)
      (fun z _ _ => by positivity)
    simpa [Finset.sum_pair hxy] using this
  constructor
  · have hA := norm_sq_of_starMul (creOp x * creOp y) ((numberOp x + 1) * (numberOp y + 1))
      (fun α => ((α x : ℝ) + 1) * ((α y : ℝ) + 1)) (star_creCre_mul hxy) (by
        intro g α
        show ((numberOp x + 1).1.1 ((numberOp y + 1).1.1 g)) α = _
        have e1 : ∀ (z : L) (h : Occ L →₀ ℂ), ((numberOp z + 1).1.1 h) = (numberOp z).1.1 h + h :=
          fun z h => rfl
        simp only [e1, Finsupp.coe_add, Pi.add_apply, numberOp_apply_coord]
        push_cast; ring) f
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [hA, hK]
    refine Finset.sum_le_sum fun α _ => ?_
    have hxn : (0 : ℝ) ≤ α x := by positivity
    have hyn : (0 : ℝ) ≤ α y := by positivity
    have := hsum α
    have hle : ((α x : ℝ) + 1) * ((α y : ℝ) + 1) ≤ (1 + ∑ z ∈ X, (α z : ℝ)) ^ 2 := by
      nlinarith
    exact mul_le_mul_of_nonneg_right hle (by positivity)
  · have hA := norm_sq_of_starMul (annOp x * annOp y) (numberOp x * numberOp y)
      (fun α => (α x : ℝ) * (α y : ℝ)) (star_annAnn_mul hxy) (by
        intro g α
        show ((numberOp x).1.1 ((numberOp y).1.1 g)) α = _
        rw [numberOp_apply_coord, numberOp_apply_coord]
        push_cast; ring) f
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [hA, hK]
    refine Finset.sum_le_sum fun α _ => ?_
    have hxn : (0 : ℝ) ≤ α x := by positivity
    have hyn : (0 : ℝ) ≤ α y := by positivity
    have := hsum α
    have hle : (α x : ℝ) * (α y : ℝ) ≤ (1 + ∑ z ∈ X, (α z : ℝ)) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hle (by positivity)

end InfiniteBosons
