/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.AtomPhotonDomain
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.AtomPhotonBounds
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.HamiltonianNelson
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FieldDegree
/-!

# Sector bounds for the atom-photon lattice

Ingredients for the essential self-adjointness of the coupled atom-photon Hamiltonian by Nelson's
theorem.

## i. Overview

The degree of a basis state is the number of photons plus the number of excited atoms. The
Hamiltonian of the Jaynes-Cummings-Hubbard lattice does not raise it. Its quadratic form on a
vector of degree at most `m` is bounded by a multiple of `m` times the squared norm: each term is
bounded by the photon and atom numbers of the cavities it touches, each cavity belongs to at most
`2 d + 1` terms for a graph of degree at most `d`, and the sum of the charges of all cavities is the
degree. The constants depend only on uniform bounds of the parameters and on `d`.

## ii. Key results

- `InfiniteBosons.sbDeg`: photons plus excited atoms.
- `InfiniteBosons.AtomPhotonData.formalHam_deg`: the Hamiltonian does not raise the degree.
- `InfiniteBosons.sum_charge_forms`: the total charge form is at most `m ‖φ‖²`.
- `InfiniteBosons.bond_sum_le`: counting bound for bonds.

## iii. Table of contents

- A. The degree
- B. Charges
- C. Counting

## iv. References

* B. W. Shore, P. L. Knight, The Jaynes-Cummings model, J. Mod. Opt. 40 (1993) 1195.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- Total number of photons and excited atoms. -/
def sbDeg (b : SBBasis L) : ℕ := b.1.degree + b.2.card

lemma degree_add_single (o : Occ L) (x : L) : (o + single x 1).degree = o.degree + 1 := by
  rw [AddMonoidHom.map_add]; simp [Finsupp.degree_single]

lemma degree_eq_of_sub (o : Occ L) (x : L) (h : o x ≠ 0) : o.degree = (o - single x 1).degree + 1 := by
  have : o = (o - single x 1) + single x 1 := by
    ext l; by_cases hl : l = x
    · subst hl; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hl]
  conv_lhs => rw [this]
  rw [degree_add_single]

lemma creAnnS_deg {x y : L} {b a : SBBasis L}
    (h : (creS x (annS y (single b (1 : ℂ)))) a ≠ 0) : sbDeg a = sbDeg b := by
  rw [annS_single, creS_single] at h
  obtain ⟨rfl, hc⟩ := single_apply_ne'' h
  have hy : b.1 y ≠ 0 := by
    intro h0; apply hc; simp [h0]
  unfold sbDeg
  simp only
  rw [degree_add_single, degree_eq_of_sub b.1 y hy]

lemma creLow_deg {x : L} {b a : SBBasis L}
    (h : (creS x (lowS x (single b (1 : ℂ)))) a ≠ 0) : sbDeg a = sbDeg b := by
  rw [lowS_single] at h
  by_cases hx : x ∈ b.2
  · rw [if_pos hx, creS_single] at h
    obtain ⟨rfl, hc⟩ := single_apply_ne'' h
    unfold sbDeg
    simp only
    rw [degree_add_single, Finset.card_erase_of_mem hx]
    have : 0 < b.2.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  · simp [hx] at h

lemma raiseAnn_deg {x : L} {b a : SBBasis L}
    (h : (raiseS x (annS x (single b (1 : ℂ)))) a ≠ 0) : sbDeg a = sbDeg b := by
  rw [annS_single, raiseS_single] at h
  by_cases hx : x ∉ b.2
  · rw [if_pos (by simpa using hx)] at h
    obtain ⟨rfl, hc⟩ := single_apply_ne'' h
    have hb : b.1 x ≠ 0 := by
      intro h0; apply hc; simp [h0]
    unfold sbDeg
    simp only
    rw [degree_eq_of_sub b.1 x hb, Finset.card_insert_of_notMem hx]
    ring
  · simp [hx] at h

lemma atomNumS_deg {x : L} {b a : SBBasis L}
    (h : (raiseS x (lowS x (single b (1 : ℂ)))) a ≠ 0) : sbDeg a = sbDeg b := by
  rw [lowS_single] at h
  by_cases hx : x ∈ b.2
  · rw [if_pos hx, raiseS_single] at h
    rw [if_pos (by simp)] at h
    obtain ⟨rfl, hc⟩ := single_apply_ne'' h
    unfold sbDeg
    simp only
    rw [Finset.insert_erase hx]
  · simp [hx] at h


namespace AtomPhotonData

variable (D : AtomPhotonData L)

lemma siteTerm_deg {x : L} {b a : SBBasis L}
    (h : (D.siteTerm x).1.1 (single b 1) a ≠ 0) : sbDeg a = sbDeg b := by
  have e : (D.siteTerm x).1.1 (single b 1) a =
      ((D.ω x : ℝ) : ℂ) * (creS x (annS x (single b (1 : ℂ)))) a +
      ((D.ε x : ℝ) : ℂ) * (raiseS x (lowS x (single b (1 : ℂ)))) a +
      (D.g x * (creS x (lowS x (single b (1 : ℂ)))) a +
        starRingEnd ℂ (D.g x) * (raiseS x (annS x (single b (1 : ℂ)))) a) := by
    unfold AtomPhotonData.siteTerm jaynesCummings
    show (((D.ω x : ℝ) : ℂ) • creS x (annS x (single b (1 : ℂ))) +
      ((D.ε x : ℝ) : ℂ) • raiseS x (lowS x (single b (1 : ℂ))) +
      (D.g x • creS x (lowS x (single b (1 : ℂ))) +
        starRingEnd ℂ (D.g x) • raiseS x (annS x (single b (1 : ℂ))))) a = _
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [e] at h
  by_cases h1 : (creS x (annS x (single b (1 : ℂ)))) a = 0
  · by_cases h2 : (raiseS x (lowS x (single b (1 : ℂ)))) a = 0
    · by_cases h3 : (creS x (lowS x (single b (1 : ℂ)))) a = 0
      · by_cases h4 : (raiseS x (annS x (single b (1 : ℂ)))) a = 0
        · exfalso; apply h; simp [h1, h2, h3, h4]
        · exact raiseAnn_deg h4
      · exact creLow_deg h3
    · exact atomNumS_deg h2
  · exact creAnnS_deg h1

lemma bondTerm_deg {x y : L} {b a : SBBasis L}
    (h : (D.bondTerm x y).1.1 (single b 1) a ≠ 0) : sbDeg a = sbDeg b := by
  by_cases hadj : D.graph.Adj x y
  · have e : (D.bondTerm x y).1.1 (single b 1) a =
        ((-D.J x y : ℝ) : ℂ) * ((creS x (annS y (single b (1 : ℂ)))) a +
          (creS y (annS x (single b (1 : ℂ)))) a) := by
      unfold AtomPhotonData.bondTerm
      rw [if_pos hadj]
      show (((-D.J x y : ℝ) : ℂ) • (creS x (annS y (single b (1 : ℂ))) +
        creS y (annS x (single b (1 : ℂ))))) a = _
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [e] at h
    by_cases h1 : (creS x (annS y (single b (1 : ℂ)))) a = 0
    · by_cases h2 : (creS y (annS x (single b (1 : ℂ)))) a = 0
      · exfalso; apply h; simp [h1, h2]
      · exact creAnnS_deg h2
    · exact creAnnS_deg h1
  · exfalso; apply h
    unfold AtomPhotonData.bondTerm
    rw [if_neg hadj]
    rfl

lemma formalHam_deg {b a : SBBasis L} (h : D.formalHam (single b 1) a ≠ 0) : sbDeg a ≤ sbDeg b := by
  have : ∃ i, (D.interaction.Φ i).1.1 (single b 1) a ≠ 0 := by
    by_contra hn
    push Not at hn
    apply h
    show ∑ᶠ i, (D.interaction.Φ i).1.1 (single b 1) a = 0
    exact finsum_eq_zero_of_forall_eq_zero hn
  obtain ⟨i, hi⟩ := this
  rcases i with x | p
  · exact (D.siteTerm_deg hi).le
  · exact (D.bondTerm_deg (x := p.1) (y := p.2) hi).le

end AtomPhotonData

section Gen
variable {β : Type*} [DecidableEq β]

lemma norm_embed_sq' (v : β →₀ ℂ) : ‖embed v‖ ^ 2 = (pair v v).re := by
  rw [← inner_embed v v]
  have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (embed v)
  rw [this]; simp [pow_two, Complex.mul_re]

/-- Real part of the quadratic form of an operator diagonal in the basis. -/
lemma qform_diag_re (T : Adjointable β) (c : β → ℝ)
    (hT : ∀ (g : β →₀ ℂ) α, (T.1.1 g) α = (c α : ℂ) * g α) (φ : β →₀ ℂ) :
    (qform T φ).re = ∑ α ∈ φ.support, c α * ‖φ α‖ ^ 2 := by
  have h : qform T φ = ∑ α ∈ φ.support, starRingEnd ℂ (φ α) * ((c α : ℂ) * φ α) := by
    show pair φ (T.1.1 φ) = _
    unfold pair
    refine Finset.sum_congr rfl fun α _ => ?_
    show starRingEnd ℂ (φ α) * (T.1.1 φ) α = _
    rw [hT]
  rw [h, Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have : starRingEnd ℂ (φ α) * ((c α : ℂ) * φ α) = ((c α * ‖φ α‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_left_comm, mul_comm (starRingEnd ℂ (φ α)), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [this, Complex.ofReal_re]


end Gen

lemma photonNumber_coord (x : L) (g : SBBasis L →₀ ℂ) (α : SBBasis L) :
    ((AtomPhotonData.photonNumber x).1.1 g) α = ((α.1 x : ℕ) : ℂ) * g α := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, mul_add]
  | single β d =>
    have : single β d = d • single β (1 : ℂ) := by simp [Finsupp.smul_single]
    rw [this, map_smul, photonNumber_basis]
    by_cases h : β = α
    · subst h; simp; ring
    · simp [Finsupp.single_apply, h]

lemma atomNumber_coord (x : L) (g : SBBasis L →₀ ℂ) (α : SBBasis L) :
    ((AtomPhotonData.atomNumber x).1.1 g) α = (if x ∈ α.2 then (1 : ℂ) else 0) * g α := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, mul_add]
  | single β d =>
    have : single β d = d • single β (1 : ℂ) := by simp [Finsupp.smul_single]
    rw [this, map_smul, atomNumber_basis]
    by_cases h : β = α
    · subst h
      by_cases hx : x ∈ β.2 <;> simp [hx]
    · have : (single β d : SBBasis L →₀ ℂ) α = 0 := by simp [Finsupp.single_apply, h]
      by_cases hx : x ∈ β.2 <;> simp [hx, this]

lemma qform_photon_re (x : L) (φ : SBBasis L →₀ ℂ) :
    (qform (AtomPhotonData.photonNumber x) φ).re = ∑ α ∈ φ.support, (α.1 x : ℝ) * ‖φ α‖ ^ 2 :=
  qform_diag_re _ (fun α => (α.1 x : ℝ)) (fun g α => by rw [photonNumber_coord]; push_cast; rfl) φ

lemma qform_atom_re (x : L) (φ : SBBasis L →₀ ℂ) :
    (qform (AtomPhotonData.atomNumber x) φ).re =
      ∑ α ∈ φ.support, (if x ∈ α.2 then (1 : ℝ) else 0) * ‖φ α‖ ^ 2 :=
  qform_diag_re _ (fun α => if x ∈ α.2 then (1 : ℝ) else 0)
    (fun g α => by rw [atomNumber_coord]; split_ifs <;> simp) φ


/-- Total number of photons and excited atoms, as a sum over a set of cavities containing the
occupied ones. -/
lemma sum_charges {M : Finset L} {α : SBBasis L} (hM : sbModes α ⊆ M) :
    ∑ x ∈ M, ((α.1 x : ℝ) + (if x ∈ α.2 then (1 : ℝ) else 0)) = (sbDeg α : ℝ) := by
  rw [Finset.sum_add_distrib]
  have h1 : ∑ x ∈ M, (α.1 x : ℝ) = (α.1.degree : ℝ) := by
    have : ∑ x ∈ M, α.1 x = α.1.degree := by
      unfold Finsupp.degree
      exact (Finset.sum_subset (fun x hx => hM (Finset.mem_union_left _ hx))
        (fun x _ hx => by simpa [Finsupp.mem_support_iff] using hx)).symm
    exact_mod_cast this
  have h2 : ∑ x ∈ M, (if x ∈ α.2 then (1 : ℝ) else 0) = (α.2.card : ℝ) := by
    rw [Finset.sum_boole]
    have : M.filter (fun x => x ∈ α.2) = α.2 := by
      ext x; simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hM (Finset.mem_union_right _ h), h⟩⟩
    rw [this]
  rw [h1, h2]; unfold sbDeg; push_cast; ring

/-- **The total charge form is bounded on every degree sector.** -/
lemma sum_charge_forms {M : Finset L} {m : ℕ} {φ : SBBasis L →₀ ℂ}
    (hM : ∀ α ∈ φ.support, sbModes α ⊆ M) (hm : ∀ α ∈ φ.support, sbDeg α ≤ m) :
    ∑ x ∈ M, ((qform (AtomPhotonData.photonNumber x) φ).re +
      (qform (AtomPhotonData.atomNumber x) φ).re) ≤ m * ‖embed φ‖ ^ 2 := by
  simp only [qform_photon_re, qform_atom_re]
  have h : ∀ x : L, (∑ α ∈ φ.support, (α.1 x : ℝ) * ‖φ α‖ ^ 2) +
      (∑ α ∈ φ.support, (if x ∈ α.2 then (1 : ℝ) else 0) * ‖φ α‖ ^ 2) =
      ∑ α ∈ φ.support, (((α.1 x : ℝ) + (if x ∈ α.2 then (1 : ℝ) else 0)) * ‖φ α‖ ^ 2) := fun x => by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun α _ => by ring
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_comm]
  simp only [← Finset.sum_mul]
  have hq : ‖embed φ‖ ^ 2 = ∑ α ∈ φ.support, ‖φ α‖ ^ 2 := by
    rw [norm_embed_sq']
    unfold pair
    rw [Finsupp.sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [hq, Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα => ?_
  rw [sum_charges (hM α hα)]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm α hα) (by positivity)



variable {β ι : Type*} [DecidableEq β]

/-- **The form of the Hamiltonian is a finite sum of the forms of the terms.** -/
theorem pairF_formalH_eq_sum (Φ : ι → Adjointable β) (h : RowFinite Φ) (φ : β →₀ ℂ) :
    ∃ T : Finset ι, (∀ i ∈ T, ∃ α ∈ φ.support, (Φ i).1.1 φ α ≠ 0) ∧
      (∀ i, (∃ α ∈ φ.support, (Φ i).1.1 φ α ≠ 0) → i ∈ T) ∧
      pairF φ (formalH Φ h φ) = ∑ i ∈ T, pair φ ((Φ i).1.1 φ) := by
  classical
  set T : Finset ι := (h.finite_union φ φ.support).toFinset with hT
  refine ⟨T, fun i hi => by simpa [hT] using hi, fun i hi => by simpa [hT] using hi, ?_⟩
  have e1 : ∀ α ∈ φ.support, formalH Φ h φ α = ∑ i ∈ T, (Φ i).1.1 φ α := fun α hα => by
    rw [formalH_apply]
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    simp only [Function.mem_support] at hi
    simp only [hT, Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    exact ⟨α, hα, hi⟩
  unfold pairF pair
  rw [Finset.sum_congr rfl fun α hα => by rw [e1 α hα]]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rfl


/-- **Counting bound for bonds.** Bonds of a graph of degree at most `d` that touch a finite set `M`
contribute at most `2 d` times the sum over `M` of a nonnegative weight vanishing outside `M`. -/
lemma bond_sum_le (M : Finset L) (N : L → Finset L) (d : ℕ) (hcard : ∀ x, (N x).card ≤ d)
    (g : L → ℝ) (hg : ∀ x, 0 ≤ g x) (hg0 : ∀ x, x ∉ M → g x = 0)
    (Tb : Finset (L × L)) (hT : ∀ p ∈ Tb, p.2 ∈ N p.1 ∧ p.1 ∈ N p.2) :
    ∑ p ∈ Tb, (g p.1 + g p.2) ≤ 2 * d * ∑ x ∈ M, g x := by
  rw [Finset.sum_add_distrib]
  set S1 : Finset (L × L) := M.biUnion (fun x => (N x).image (fun y => (x, y))) with hS1
  set S2 : Finset (L × L) := M.biUnion (fun x => (N x).image (fun y => (y, x))) with hS2
  have h1 : ∑ p ∈ Tb, g p.1 ≤ d * ∑ x ∈ M, g x := by
    calc ∑ p ∈ Tb, g p.1 = ∑ p ∈ Tb.filter (fun p => p.1 ∈ M), g p.1 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases h : p.1 ∈ M
          · simp [h]
          · simp [h, hg0 _ h]
      _ ≤ ∑ p ∈ S1, g p.1 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hg _)
          intro p hp
          rw [Finset.mem_filter] at hp
          simp only [hS1, Finset.mem_biUnion, Finset.mem_image]
          exact ⟨p.1, hp.2, p.2, (hT p hp.1).1, rfl⟩
      _ = ∑ x ∈ M, (N x).card * g x := by
          rw [hS1, Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
            simp
          · intro x _ y _ hxy
            rw [Function.onFun, Finset.disjoint_left]
            intro p hp hq
            simp only [Finset.mem_image] at hp hq
            obtain ⟨a, _, rfl⟩ := hp
            obtain ⟨b, _, hb⟩ := hq
            exact hxy (by simpa using (congrArg Prod.fst hb).symm)
      _ ≤ ∑ x ∈ M, d * g x := Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard x) (hg x)
      _ = d * ∑ x ∈ M, g x := by rw [Finset.mul_sum]
  have h2 : ∑ p ∈ Tb, g p.2 ≤ d * ∑ x ∈ M, g x := by
    calc ∑ p ∈ Tb, g p.2 = ∑ p ∈ Tb.filter (fun p => p.2 ∈ M), g p.2 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun p _ => ?_
          by_cases h : p.2 ∈ M
          · simp [h]
          · simp [h, hg0 _ h]
      _ ≤ ∑ p ∈ S2, g p.2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hg _)
          intro p hp
          rw [Finset.mem_filter] at hp
          simp only [hS2, Finset.mem_biUnion, Finset.mem_image]
          exact ⟨p.2, hp.2, p.1, (hT p hp.1).2, rfl⟩
      _ = ∑ x ∈ M, (N x).card * g x := by
          rw [hS2, Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.sum_image (fun a _ b _ h => by simpa using h)]
            simp
          · intro x _ y _ hxy
            rw [Function.onFun, Finset.disjoint_left]
            intro p hp hq
            simp only [Finset.mem_image] at hp hq
            obtain ⟨a, _, rfl⟩ := hp
            obtain ⟨b, _, hb⟩ := hq
            exact hxy (by simpa using (congrArg Prod.snd hb).symm)
      _ ≤ ∑ x ∈ M, d * g x := Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard x) (hg x)
      _ = d * ∑ x ∈ M, g x := by rw [Finset.mul_sum]
  nlinarith [h1, h2]



/-!

## D. The sector form bound

-/

namespace AtomPhotonData

variable (D : AtomPhotonData L)

lemma qform_photon_eq_zero {M : Finset L} {φ : SBBasis L →₀ ℂ}
    (hM : ∀ α ∈ φ.support, sbModes α ⊆ M) {x : L} (hx : x ∉ M) :
    (qform (photonNumber x) φ).re = 0 := by
  rw [qform_photon_re]
  refine Finset.sum_eq_zero fun α hα => ?_
  have : α.1 x = 0 := by
    by_contra h
    exact hx (hM α hα (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h)))
  simp [this]

lemma qform_atom_eq_zero {M : Finset L} {φ : SBBasis L →₀ ℂ}
    (hM : ∀ α ∈ φ.support, sbModes α ⊆ M) {x : L} (hx : x ∉ M) :
    (qform (atomNumber x) φ).re = 0 := by
  rw [qform_atom_re]
  refine Finset.sum_eq_zero fun α hα => ?_
  have : x ∉ α.2 := fun h => hx (hM α hα (Finset.mem_union_right _ h))
  simp [this]

/-- A cavity term is bounded in absolute value by a uniform multiple of the charge of the
cavity. -/
lemma abs_siteTerm_le {Ω E G : ℝ} (hω : ∀ x, |D.ω x| ≤ Ω) (hε : ∀ x, |D.ε x| ≤ E)
    (hg : ∀ x, ‖D.g x‖ ≤ G) (x : L) (φ : SBBasis L →₀ ℂ) :
    |(qform (D.siteTerm x) φ).re| ≤ (Ω + E + G ^ 2 + 1) *
      ((qform (photonNumber x) φ).re + (qform (atomNumber x) φ).re) := by
  have hp := qform_photonNumber_nonneg x φ
  have ha := qform_atomNumber_nonneg x φ
  have hG : Complex.normSq (D.g x) ≤ G ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hg x) 2
  have hΩ : 0 ≤ Ω := (abs_nonneg _).trans (hω x)
  have hE : 0 ≤ E := (abs_nonneg _).trans (hε x)
  have h1 : (|D.ω x| + 1) * (qform (photonNumber x) φ).re ≤
      (Ω + E + G ^ 2 + 1) * (qform (photonNumber x) φ).re :=
    mul_le_mul_of_nonneg_right (by nlinarith [hω x, sq_nonneg G]) hp
  have h2 : (|D.ε x| + Complex.normSq (D.g x)) * (qform (atomNumber x) φ).re ≤
      (Ω + E + G ^ 2 + 1) * (qform (atomNumber x) φ).re :=
    mul_le_mul_of_nonneg_right (by nlinarith [hε x]) ha
  rw [abs_le]
  constructor
  · nlinarith [D.siteTerm_ge x φ]
  · nlinarith [D.siteTerm_le x φ]

open Classical in
/-- A bond term is bounded in absolute value by a uniform multiple of the photon numbers of its
two cavities, and it vanishes unless the cavities are adjacent. -/
lemma abs_bondTerm_le {K : ℝ} (hJ : ∀ x y, |D.J x y| ≤ K) (x y : L) (φ : SBBasis L →₀ ℂ) :
    |(qform (D.bondTerm x y) φ).re| ≤ if D.graph.Adj x y then
      K * ((qform (photonNumber x) φ).re + (qform (photonNumber y) φ).re) else 0 := by
  split_ifs with hadj
  · have hpos := add_nonneg (qform_photonNumber_nonneg x φ) (qform_photonNumber_nonneg y φ)
    have h := mul_le_mul_of_nonneg_right (hJ x y) hpos
    have hl := D.bondTerm_le x y φ
    have hr := D.bondTerm_ge x y φ
    rw [qform_add, Complex.add_re] at hl hr
    rw [abs_le]; constructor <;> linarith
  · have h0 : D.bondTerm x y = 0 := by unfold bondTerm; rw [if_neg hadj]
    have : qform (0 : Adjointable (SBBasis L)) φ = 0 := by
      simpa using qform_smul 0 (0 : Adjointable (SBBasis L)) φ
    rw [h0, this]; simp

open Classical in
/-- Weight dominating the absolute value of the form of a term of the atom-photon
Hamiltonian. -/
def termWeight (C K : ℝ) (φ : SBBasis L →₀ ℂ) : L ⊕ (L × L) → ℝ :=
  Sum.elim (fun x => C * ((qform (photonNumber x) φ).re + (qform (atomNumber x) φ).re))
    (fun p => if D.graph.Adj p.1 p.2 then
      K * ((qform (photonNumber p.1) φ).re + (qform (photonNumber p.2) φ).re) else 0)

lemma termWeight_nonneg {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (φ : SBBasis L →₀ ℂ)
    (i : L ⊕ (L × L)) : 0 ≤ D.termWeight C K φ i := by
  rcases i with x | p
  · exact mul_nonneg hC (add_nonneg (qform_photonNumber_nonneg x φ) (qform_atomNumber_nonneg x φ))
  · simp only [termWeight, Sum.elim_inr]
    split_ifs
    · exact mul_nonneg hK
        (add_nonneg (qform_photonNumber_nonneg _ φ) (qform_photonNumber_nonneg _ φ))
    · exact le_rfl

/-- The finite neighbourhood of a cavity. -/
def nbhd (x : L) : Finset L := (D.locallyFinite x).toFinset

/-- The bonds that touch a finite set of cavities. -/
def bondsAt (M : Finset L) : Finset (L × L) :=
  M.biUnion (fun x => (D.nbhd x).image (fun y => (x, y))) ∪
    M.biUnion (fun x => (D.nbhd x).image (fun y => (y, x)))

/-- The terms that touch a finite set of cavities. -/
def termsAt (M : Finset L) : Finset (L ⊕ (L × L)) :=
  M.disjSum (D.bondsAt M)

/-- The term weight vanishes outside the terms touching the occupied cavities. -/
lemma termWeight_eq_zero {C K : ℝ} {M : Finset L} {φ : SBBasis L →₀ ℂ}
    (hM : ∀ α ∈ φ.support, sbModes α ⊆ M) {i : L ⊕ (L × L)} (hi : i ∉ D.termsAt M) :
    D.termWeight C K φ i = 0 := by
  rcases i with x | p
  · have hx : x ∉ M := by simpa [termsAt] using hi
    simp [termWeight, qform_photon_eq_zero hM hx, qform_atom_eq_zero hM hx]
  · simp only [termWeight, Sum.elim_inr]
    split_ifs with hadj
    · have hp : p ∉ D.bondsAt M := by simpa [termsAt] using hi
      have h1 : p.1 ∉ M := fun h => hp (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨p.1, h, Finset.mem_image.mpr ⟨p.2, by simpa [nbhd] using hadj, rfl⟩⟩))
      have h2 : p.2 ∉ M := fun h => hp (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p.2, h, Finset.mem_image.mpr ⟨p.1, by simpa [nbhd] using hadj.symm, rfl⟩⟩))
      simp [qform_photon_eq_zero hM h1, qform_photon_eq_zero hM h2]
    · rfl

open Classical in
/-- The bond weights touching `M` are bounded by `2 d K` times the photon number in `M`. -/
lemma sum_bond_weight_le {K : ℝ} (hK : 0 ≤ K) {d : ℕ} (hd : ∀ x, (D.nbhd x).card ≤ d)
    {M : Finset L} {φ : SBBasis L →₀ ℂ} (hM : ∀ α ∈ φ.support, sbModes α ⊆ M) :
    ∑ p ∈ D.bondsAt M, D.termWeight 0 K φ (Sum.inr p) ≤
      2 * d * K * ∑ x ∈ M, (qform (photonNumber x) φ).re := by
  set n : L → ℝ := fun x => (qform (photonNumber x) φ).re
  have hsum : ∑ p ∈ D.bondsAt M, D.termWeight 0 K φ (Sum.inr p) =
      K * ∑ p ∈ (D.bondsAt M).filter (fun p => D.graph.Adj p.1 p.2), (n p.1 + n p.2) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [termWeight, Sum.elim_inr, n]
  have hb := bond_sum_le M D.nbhd d hd n (fun x => qform_photonNumber_nonneg x φ)
    (fun x hx => qform_photon_eq_zero hM hx) ((D.bondsAt M).filter (fun p => D.graph.Adj p.1 p.2))
    (fun p hp => by
      have hadj := (Finset.mem_filter.mp hp).2
      exact ⟨by simpa [nbhd] using hadj, by simpa [nbhd] using hadj.symm⟩)
  rw [hsum]
  nlinarith [mul_le_mul_of_nonneg_left hb hK]

/-- The absolute value of the form of a single term is bounded by its weight. -/
lemma abs_term_le_weight {Ω E G K : ℝ} (hω : ∀ x, |D.ω x| ≤ Ω) (hε : ∀ x, |D.ε x| ≤ E)
    (hg : ∀ x, ‖D.g x‖ ≤ G) (hJ : ∀ x y, |D.J x y| ≤ K) (φ : SBBasis L →₀ ℂ)
    (i : L ⊕ (L × L)) :
    |(qform (D.interaction.Φ i) φ).re| ≤ D.termWeight (Ω + E + G ^ 2 + 1) K φ i := by
  rcases i with x | p
  · exact D.abs_siteTerm_le hω hε hg x φ
  · exact D.abs_bondTerm_le hJ p.1 p.2 φ

/-- **The sector form bound.** For uniformly bounded parameters on a graph of degree at most `d`,
the quadratic form of the atom-photon Hamiltonian on a finite vector with at most `m` photons and
excited atoms is bounded by `(|Ω| + |E| + G² + 1 + 2 d |K|) m ‖φ‖²`. -/
theorem abs_form_le {Ω E G K : ℝ} (hω : ∀ x, |D.ω x| ≤ Ω) (hε : ∀ x, |D.ε x| ≤ E)
    (hg : ∀ x, ‖D.g x‖ ≤ G) (hJ : ∀ x y, |D.J x y| ≤ K) {d : ℕ}
    (hd : ∀ x, (D.nbhd x).card ≤ d) {m : ℕ} {φ : SBBasis L →₀ ℂ}
    (hm : ∀ α ∈ φ.support, sbDeg α ≤ m) :
    |(pairF φ (D.formalHam φ)).re| ≤
      (|Ω| + |E| + G ^ 2 + 1 + 2 * d * |K|) * m * ‖embed φ‖ ^ 2 := by
  set C := |Ω| + |E| + G ^ 2 + 1
  set M : Finset L := φ.support.biUnion sbModes
  set w := D.termWeight C |K| φ
  have hM : ∀ α ∈ φ.support, sbModes α ⊆ M := fun α hα => Finset.subset_biUnion_of_mem _ hα
  have hC : 0 ≤ C := by positivity
  have hw0 : ∀ i, 0 ≤ w i := D.termWeight_nonneg hC (abs_nonneg K) φ
  -- the form of the Hamiltonian is a finite sum of forms of terms, each dominated by its weight
  obtain ⟨T, -, -, heq⟩ := pairF_formalH_eq_sum D.interaction.Φ D.rowFinite φ
  have h1 : |(pairF φ (D.formalHam φ)).re| ≤ ∑ i ∈ T, w i := by
    rw [show D.formalHam = formalH D.interaction.Φ D.rowFinite from rfl, heq, Complex.re_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact D.abs_term_le_weight (fun x => (hω x).trans (le_abs_self _))
      (fun x => (hε x).trans (le_abs_self _)) hg (fun x y => (hJ x y).trans (le_abs_self _)) φ i
  -- only the terms touching the occupied cavities have nonzero weight
  have h2 : ∑ i ∈ T, w i ≤ ∑ i ∈ D.termsAt M, w i := by
    rw [← Finset.sum_filter_of_ne (p := fun i => i ∈ D.termsAt M)
      (fun i _ hi => by_contra fun h => hi (D.termWeight_eq_zero hM h))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => (Finset.mem_filter.mp hi).2)
      (fun i _ _ => hw0 i)
  -- split into cavity and bond terms
  have h3 : ∑ i ∈ D.termsAt M, w i ≤ C * ∑ x ∈ M, ((qform (photonNumber x) φ).re +
      (qform (atomNumber x) φ).re) + 2 * d * |K| * ∑ x ∈ M, (qform (photonNumber x) φ).re := by
    rw [termsAt, Finset.sum_disjSum, Finset.mul_sum]
    exact add_le_add le_rfl (D.sum_bond_weight_le (abs_nonneg K) hd hM)
  have hn : ∑ x ∈ M, (qform (photonNumber x) φ).re ≤ ∑ x ∈ M, ((qform (photonNumber x) φ).re +
      (qform (atomNumber x) φ).re) :=
    Finset.sum_le_sum fun x _ => le_add_of_nonneg_right (qform_atomNumber_nonneg x φ)
  have hq := sum_charge_forms hM hm
  have hK : 0 ≤ 2 * d * |K| := by positivity
  calc _ ≤ C * ∑ x ∈ M, ((qform (photonNumber x) φ).re + (qform (atomNumber x) φ).re) +
        2 * d * |K| * ∑ x ∈ M, ((qform (photonNumber x) φ).re + (qform (atomNumber x) φ).re) :=
        by nlinarith [mul_le_mul_of_nonneg_left hn hK]
    _ = (C + 2 * d * |K|) *
        ∑ x ∈ M, ((qform (photonNumber x) φ).re + (qform (atomNumber x) φ).re) := by ring
    _ ≤ (C + 2 * d * |K|) * (m * ‖embed φ‖ ^ 2) := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by ring

/-!

## E. Essential self-adjointness

-/

/-- **The Jaynes-Cummings-Hubbard Hamiltonian is essentially self-adjoint** on an infinite lattice
of bounded degree with uniformly bounded frequencies, couplings and hopping amplitudes. Every finite
vector is an entire analytic vector. -/
theorem hamOp_isEssentiallySelfAdjoint {Ω E G K : ℝ} (hω : ∀ x, |D.ω x| ≤ Ω)
    (hε : ∀ x, |D.ε x| ≤ E) (hg : ∀ x, ‖D.g x‖ ≤ G) (hJ : ∀ x y, |D.J x y| ≤ K) {d : ℕ}
    (hd : ∀ x, (D.nbhd x).card ≤ d) : D.hamOp.IsEssentiallySelfAdjoint :=
  hamPMap_ess_of_form D.interaction.Φ D.rowFinite D.interaction.star_eq D.formalHam_basis_finite
    sbDeg (fun _ _ h => D.formalHam_deg h) fun m =>
      ⟨(|Ω| + |E| + G ^ 2 + 1 + 2 * d * |K|) * m, by positivity,
        fun _ hφ => D.abs_form_le hω hε hg hJ hd hφ⟩

/-- **Dynamics of the coupled atom-photon lattice.** Under the hypotheses of
`hamOp_isEssentiallySelfAdjoint` the Hamiltonian generates a strongly continuous unitary group. -/
theorem dynamics_coupled {Ω E G K : ℝ} (hω : ∀ x, |D.ω x| ≤ Ω) (hε : ∀ x, |D.ε x| ≤ E)
    (hg : ∀ x, ‖D.g x‖ ≤ G) (hJ : ∀ x y, |D.J x y| ≤ K) {d : ℕ}
    (hd : ∀ x, (D.nbhd x).card ≤ d) :
    ∃ U : ProbabilisticTheory.QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup
        (HilbertSp (SBBasis L)),
      (∀ t s, U (t + s) = U t * U s) ∧ U 0 = 1 ∧
      ∀ f : hamDomainAlg D.interaction.Φ D.rowFinite,
        HasDerivAt (fun t : ℝ => U t (embed f.1))
          (Complex.I • (hamVec D.interaction.Φ D.rowFinite f : HilbertSp (SBBasis L))) 0 :=
  D.dynamics_of_essentiallySelfAdjoint (D.hamOp_isEssentiallySelfAdjoint hω hε hg hJ hd)

end AtomPhotonData

end InfiniteBosons
