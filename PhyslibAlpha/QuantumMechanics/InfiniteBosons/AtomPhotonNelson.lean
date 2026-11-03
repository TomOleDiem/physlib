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


end InfiniteBosons
