/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FormalHamiltonian
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.BoseHubbard
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.NumberCalculus
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FieldDegree
/-!

# The Bose-Hubbard Hamiltonian with pairing on an infinite lattice

The Hamiltonian of the Bose-Hubbard model with pairing exists as a linear map from the finite
vectors to the formal vectors and acts on `ℓ²` as a symmetric operator.

## i. Overview

The terms of `H = Σ_x (U_x/2 N_x(N_x-1) - μ_x N_x) + Σ_{x~y} (-J_{xy}(a_x† a_y + a_y† a_x) +
Δ_{xy} a_x† a_y† + Δ̄_{xy} a_y a_x)` are local. A nonzero matrix element `⟨α|Φ|β⟩` of a term
involves only modes occupied in `α` or `β`. Hence for a finite vector and a fixed output state only
the terms supported in a finite set of modes contribute, and the family is row finite. The
Hamiltonian is then a linear map from the finitely supported vectors to the formal vectors. The
same model with `U = 0` and no atoms is the quadratic Hamiltonian of the oscillator lattice. So
this file serves the models E1 and E2. The lattice is arbitrary. Pairing from the vacuum is
allowed: the formal image of the vacuum is the infinite sum of the pair-creation terms, and it
lies in `ℓ²` iff the amplitudes are square summable.

## ii. Key results

- `InfiniteBosons.BoseHubbardData.rowFinite`: row finiteness.
- `InfiniteBosons.BoseHubbardData.formalHam`: the formal Hamiltonian.
- `InfiniteBosons.BoseHubbardData.hamOp`: the operator on `ℓ²(Occ L)`.
- `InfiniteBosons.BoseHubbardData.hamOp_isSymmetric`: it is symmetric.

## iii. Table of contents

- A. Matrix elements of the building blocks
- B. Row finiteness
- C. The Hamiltonian

## iv. References

* O. Bratteli, D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, Section 6.2.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- **Row finiteness from locality of matrix elements.** If every nonzero matrix element of a term
involves only modes occupied in the source or target state, and only finitely many terms live in a
given finite set of modes, then the family is row finite. -/
theorem rowFinite_of_local {β ι : Type*} [DecidableEq β] (Φ : ι → Adjointable β) (supp : ι → Finset L)
    (modes : β → Finset L)
    (hloc : ∀ i (b a : β), (Φ i).1.1 (single b 1) a ≠ 0 → supp i ⊆ modes a ∪ modes b)
    (hfin : ∀ M : Finset L, {i | supp i ⊆ M}.Finite) : RowFinite Φ := by
  intro f α
  set M : Finset L := modes α ∪ f.support.biUnion modes with hM
  refine (hfin M).subset fun i hi => ?_
  have hi' : (Φ i).1.1 f α ≠ 0 := hi
  have hf : f = ∑ b ∈ f.support, single b (f b) := (Finsupp.sum_single f).symm
  rw [hf, map_sum, Finsupp.finset_sum_apply] at hi'
  obtain ⟨b, hb, hbne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi'
  have hb1 : single b (f b) = f b • single b (1 : ℂ) := by simp [Finsupp.smul_single]
  rw [hb1, map_smul, Finsupp.smul_apply, smul_eq_mul] at hbne
  have hne : (Φ i).1.1 (single b 1) α ≠ 0 := fun h0 => hbne (by rw [h0, mul_zero])
  have := hloc i b α hne
  intro x hx
  have hx' := this hx
  simp only [hM, Finset.mem_union, Finset.mem_biUnion] at hx' ⊢
  rcases hx' with h1 | h1
  · exact Or.inl h1
  · exact Or.inr ⟨b, hb, h1⟩


lemma single_apply_ne' {γ α : Occ L} {c : ℂ} (h : (single γ c : Occ L →₀ ℂ) α ≠ 0) :
    α = γ ∧ c ≠ 0 := by
  by_cases hα : γ = α
  · subst hα; simpa using h
  · simp [Finsupp.single_apply, hα] at h

lemma sqrt_ne_zero_of {n : ℕ} (h : Real.sqrt (n : ℝ) * 1 ≠ 0) : n ≠ 0 := by
  rintro rfl; simp at h

/-- Matrix elements of `a_x† a_y`. -/
lemma creAnn_ne {x y : L} {b α : Occ L}
    (h : (cre x (ann y (single b (1 : ℂ)))) α ≠ 0) : y ∈ b.support ∧ x ∈ α.support := by
  rw [ann_single, cre_single] at h
  obtain ⟨rfl, hc⟩ := single_apply_ne' h
  constructor
  · rw [Finsupp.mem_support_iff]
    intro hy
    apply hc
    simp [hy]
  · rw [Finsupp.mem_support_iff]
    intro hx
    simp at hx

lemma creCre_ne {x y : L} {b α : Occ L}
    (h : (cre x (cre y (single b (1 : ℂ)))) α ≠ 0) : x ∈ α.support ∧ y ∈ α.support := by
  rw [cre_single, cre_single] at h
  obtain ⟨rfl, hc⟩ := single_apply_ne' h
  constructor
  · rw [Finsupp.mem_support_iff]; intro hx; simp at hx
  · rw [Finsupp.mem_support_iff]; intro hy
    by_cases hxy : y = x
    · subst hxy; simp at hy
    · simp [hxy] at hy


lemma annAnn_ne {x y : L} {b α : Occ L}
    (h : (ann y (ann x (single b (1 : ℂ)))) α ≠ 0) : x ∈ b.support ∧ y ∈ b.support := by
  rw [ann_single, ann_single] at h
  obtain ⟨rfl, hc⟩ := single_apply_ne' h
  have h1 : (Real.sqrt (b x : ℝ) : ℂ) ≠ 0 := by
    intro h0; apply hc; simp [h0]
  have h2 : ((b - single x 1 : Occ L) y) ≠ 0 := by
    intro h0; apply hc; simp [h0]
  constructor
  · rw [Finsupp.mem_support_iff]; intro hx
    apply h1; simp [hx]
  · rw [Finsupp.mem_support_iff]; intro hy
    apply h2
    simp [Finsupp.tsub_apply, hy]

/-- Locality of the matrix elements of the site term. -/
lemma siteTerm_ne {x : L} (D : BoseHubbardData L) {b α : Occ L}
    (h : (D.siteTerm x).1.1 (single b 1) α ≠ 0) : x ∈ b.support := by
  rw [Finsupp.mem_support_iff]
  intro hx
  apply h
  have hN : (numberOp x).1.1 (single b 1) = ((b x : ℕ) : ℂ) • single b 1 := numberOp_basis x b
  have hNN : (numberOp x * numberOp x).1.1 (single b 1) = (((b x : ℕ) : ℂ) * ((b x : ℕ) : ℂ)) • single b 1 := by
    show (numberOp x).1.1 ((numberOp x).1.1 (single b 1)) = _
    rw [hN, map_smul, hN, smul_smul]
  have e : (D.siteTerm x).1.1 (single b 1) = ((D.U x / 2 : ℝ) : ℂ) •
      ((numberOp x * numberOp x).1.1 (single b 1) - (numberOp x).1.1 (single b 1)) -
      ((D.μ x : ℝ) : ℂ) • (numberOp x).1.1 (single b 1) := rfl
  rw [e, hN, hNN, hx]
  simp


/-- Locality of the matrix elements of the bond term. -/
lemma bondTerm_ne {x y : L} (D : BoseHubbardData L) {b α : Occ L}
    (h : (D.bondTerm x y).1.1 (single b 1) α ≠ 0) :
    x ∈ α.support ∪ b.support ∧ y ∈ α.support ∪ b.support := by
  by_cases hadj : D.graph.Adj x y
  · have e : (D.bondTerm x y).1.1 (single b 1) α =
        (((-D.J x y : ℝ) : ℂ)) * ((cre x (ann y (single b (1 : ℂ)))) α +
          (cre y (ann x (single b (1 : ℂ)))) α) +
        D.Δ x y * (cre x (cre y (single b (1 : ℂ)))) α +
        starRingEnd ℂ (D.Δ x y) * (ann y (ann x (single b (1 : ℂ)))) α := by
      unfold BoseHubbardData.bondTerm
      rw [if_pos hadj]
      show (((-D.J x y : ℝ) : ℂ) • (cre x (ann y (single b (1 : ℂ))) + cre y (ann x (single b (1 : ℂ)))) +
        D.Δ x y • cre x (cre y (single b (1 : ℂ))) +
        starRingEnd ℂ (D.Δ x y) • ann y (ann x (single b (1 : ℂ)))) α = _
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [e] at h
    by_cases h1 : (cre x (ann y (single b (1 : ℂ)))) α = 0
    · by_cases h2 : (cre y (ann x (single b (1 : ℂ)))) α = 0
      · by_cases h3 : (cre x (cre y (single b (1 : ℂ)))) α = 0
        · by_cases h4 : (ann y (ann x (single b (1 : ℂ)))) α = 0
          · exfalso; apply h; simp [h1, h2, h3, h4]
          · have := annAnn_ne h4
            exact ⟨Finset.mem_union_right _ this.1, Finset.mem_union_right _ this.2⟩
        · have := creCre_ne h3
          exact ⟨Finset.mem_union_left _ this.1, Finset.mem_union_left _ this.2⟩
      · have := creAnn_ne h2
        exact ⟨Finset.mem_union_right _ this.1, Finset.mem_union_left _ this.2⟩
    · have := creAnn_ne h1
      exact ⟨Finset.mem_union_left _ this.2, Finset.mem_union_right _ this.1⟩
  · exfalso; apply h
    unfold BoseHubbardData.bondTerm
    rw [if_neg hadj]
    rfl


namespace BoseHubbardData

variable (D : BoseHubbardData L)

/-- **The Bose-Hubbard Hamiltonian with pairing is row finite** on an arbitrary lattice. -/
theorem rowFinite : RowFinite D.interaction.Φ := by
  refine rowFinite_of_local D.interaction.Φ D.interaction.supp (fun b : Occ L => b.support) ?_ ?_
  · rintro (x | p) b a h
    · have := siteTerm_ne D h
      intro z hz
      have : z = x := by simpa [BoseHubbardData.interaction] using hz
      subst this
      exact Finset.mem_union_right _ ‹_›
    · have := bondTerm_ne D (x := p.1) (y := p.2) h
      intro z hz
      have hz' : z = p.1 ∨ z = p.2 := by simpa [BoseHubbardData.interaction] using hz
      rcases hz' with rfl | rfl
      · exact this.1
      · exact this.2
  · intro M
    have : {i : L ⊕ (L × L) | D.interaction.supp i ⊆ M} ⊆
        (Sum.inl '' (M : Set L)) ∪ (Sum.inr '' ((M : Set L) ×ˢ (M : Set L))) := by
      rintro (x | p) hi
      · exact Or.inl ⟨x, by simpa [BoseHubbardData.interaction] using hi (by simp [BoseHubbardData.interaction]), rfl⟩
      · exact Or.inr ⟨p, ⟨by simpa [BoseHubbardData.interaction] using hi (by simp [BoseHubbardData.interaction]),
          by simpa [BoseHubbardData.interaction] using hi (by simp [BoseHubbardData.interaction])⟩, rfl⟩
    exact ((M.finite_toSet.image _).union ((M.finite_toSet.prod M.finite_toSet).image _)).subset this

/-- **The formal Hamiltonian** of the Bose-Hubbard model: a linear map from finite vectors to formal
vectors. -/
def formalHam : (Occ L →₀ ℂ) →ₗ[ℂ] Formal (Occ L) := formalH D.interaction.Φ D.rowFinite

/-- **The Hamiltonian as an operator on `ℓ²(Occ L)`**. -/
def hamOp : HilbertSp (Occ L) →ₗ.[ℂ] HilbertSp (Occ L) := hamPMap D.interaction.Φ D.rowFinite

theorem hamOp_isSymmetric : D.hamOp.IsSymmetric :=
  hamPMap_isSymmetric D.interaction.Φ D.rowFinite D.interaction.star_eq


/-!

## D. Pairing on infinitely many bonds leaves no finite vector in the domain

-/

/-- A linear map evaluated on a finite vector is the sum of its values on the basis vectors. -/
lemma linearMap_apply_eq_sum (T : FockPre L →ₗ[ℂ] FockPre L) (f : FockPre L) (γ : Occ L) :
    T f γ = ∑ b ∈ f.support, f b * T (single b 1) γ := by
  conv_lhs => rw [← Finsupp.sum_single f]
  rw [Finsupp.sum, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show (single b (f b) : FockPre L) = f b • single b 1 by simp [Finsupp.smul_single],
    map_smul, Finsupp.smul_apply, smul_eq_mul]

section PairTarget

variable {x y : L} {b γ : Occ L} (hxy : x ≠ y) (hbx : b x = 0) (hby : b y = 0)
  (hγx : γ x = 1) (hγy : γ y = 1)
include hxy hbx hby hγx hγy

/-- Hopping cannot put a boson on both of two empty modes. -/
lemma cre_ann_single_apply_eq_zero (u v : L) : cre u (ann v (single b (1 : ℂ))) γ = 0 := by
  rw [ann_single, cre_single, Finsupp.single_apply, if_neg]
  intro h
  have h1 := congrArg (· x) h
  have h2 := congrArg (· y) h
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, hbx, hby, hγx, hγy,
    Finsupp.single_apply, zero_tsub, zero_add] at h1 h2
  split_ifs at h1 h2 with h3 h4
  · exact hxy (h3.symm.trans h4)
  all_goals omega

/-- Pair annihilation cannot put a boson on an empty mode. -/
lemma ann_ann_single_apply_eq_zero (u v : L) : ann v (ann u (single b (1 : ℂ))) γ = 0 := by
  rw [ann_single, ann_single, Finsupp.single_apply, if_neg]
  intro h
  have h1 := congrArg (· x) h
  simp only [Finsupp.coe_tsub, Pi.sub_apply, hbx, hγx, zero_tsub] at h1
  omega

/-- Pair creation reaches a state with one boson at each of two empty modes only on that pair. -/
lemma cre_cre_single_apply_eq_zero {u v : L} (huv : ¬ (u = x ∧ v = y) ∧ ¬ (u = y ∧ v = x)) :
    cre u (cre v (single b (1 : ℂ))) γ = 0 := by
  rw [cre_single, cre_single, Finsupp.single_apply, if_neg]
  intro h
  have h1 := congrArg (· x) h
  have h2 := congrArg (· y) h
  simp only [Finsupp.coe_add, Pi.add_apply, hbx, hby, hγx, hγy, Finsupp.single_apply,
    zero_add] at h1 h2
  split_ifs at h1 h2 <;> simp_all <;> omega

/-- A site term cannot put a boson on an empty mode. -/
lemma siteTerm_single_apply_eq_zero (D : BoseHubbardData L) (z : L) :
    (D.siteTerm z).1.1 (single b 1) γ = 0 := by
  have hne : b ≠ γ := fun h => by rw [h, hγx] at hbx; exact one_ne_zero hbx
  have hN : (numberOp z).1.1 (single b 1) = ((b z : ℕ) : ℂ) • single b 1 := numberOp_basis z b
  have hNN : (numberOp z * numberOp z).1.1 (single b 1) =
      (((b z : ℕ) : ℂ) * ((b z : ℕ) : ℂ)) • single b 1 := by
    show (numberOp z).1.1 ((numberOp z).1.1 (single b 1)) = _
    rw [hN, map_smul, hN, smul_smul]
  have e : (D.siteTerm z).1.1 (single b 1) = ((D.U z / 2 : ℝ) : ℂ) •
      ((numberOp z * numberOp z).1.1 (single b 1) - (numberOp z).1.1 (single b 1)) -
      ((D.μ z : ℝ) : ℂ) • (numberOp z).1.1 (single b 1) := rfl
  rw [e, hNN, hN]
  simp [Finsupp.single_apply, hne]

/-- The bond term applied to a basis state, read off at a state with one more boson at each of two
empty modes: only pair creation contributes. -/
lemma bondTerm_single_apply (D : BoseHubbardData L) (u v : L) :
    (D.bondTerm u v).1.1 (single b 1) γ =
      if D.graph.Adj u v then D.Δ u v * cre u (cre v (single b (1 : ℂ))) γ else 0 := by
  unfold BoseHubbardData.bondTerm
  split_ifs with hadj
  · show (((-D.J u v : ℝ) : ℂ) • (cre u (ann v (single b (1 : ℂ))) + cre v (ann u (single b 1))) +
      D.Δ u v • cre u (cre v (single b 1)) + starRingEnd ℂ (D.Δ u v) • ann v (ann u (single b 1))) γ = _
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
      cre_ann_single_apply_eq_zero hxy hbx hby hγx hγy, ann_ann_single_apply_eq_zero hxy hbx hby hγx hγy]
    ring
  · rfl

end PairTarget

/-- Creating the pair `x`, `y` on a state empty at both modes. -/
lemma cre_cre_single_of_empty {x y : L} (hxy : x ≠ y) {b : Occ L} (hbx : b x = 0) (hby : b y = 0) :
    cre x (cre y (single b (1 : ℂ))) = single (b + single x 1 + single y 1) 1 := by
  rw [cre_single, cre_single]
  have : (b + single y 1) x = 0 := by simp [Finsupp.single_apply, hbx, Ne.symm hxy]
  rw [this, hby, add_assoc, add_comm (single y 1), ← add_assoc]
  simp

/-- **The formal image of a finite vector at a created pair.** Let `x ~ y` be a bond whose modes
are empty in every basis state of `f`. Then the formal Hamiltonian at `α + e_x + e_y` is
`(Δ_xy + Δ_yx) f(α)`. -/
lemma formalHam_apply_pair (D : BoseHubbardData L) {x y : L} (hadj : D.graph.Adj x y)
    {f : FockPre L} (hS : ∀ b ∈ f.support, b x = 0 ∧ b y = 0) (α : Occ L) (hα : α x = 0 ∧ α y = 0) :
    D.formalHam f (α + single x 1 + single y 1) = (D.Δ x y + D.Δ y x) * f α := by
  have hxy : x ≠ y := hadj.ne
  set γ := α + single x 1 + single y 1 with hγ
  have hγx : γ x = 1 := by simp [hγ, Finsupp.single_apply, hα.1, hxy.symm]
  have hγy : γ y = 1 := by simp [hγ, Finsupp.single_apply, hα.2, hxy]
  -- the value of each term
  have hterm : ∀ i, (D.interaction.Φ i).1.1 f γ =
      if i = Sum.inr (x, y) then D.Δ x y * f α else if i = Sum.inr (y, x) then D.Δ y x * f α
      else 0 := by
    intro i
    rw [linearMap_apply_eq_sum]
    rcases i with z | ⟨u, v⟩
    · simp only [reduceCtorEq, if_false]
      exact Finset.sum_eq_zero fun b hb =>
        by rw [show D.interaction.Φ (Sum.inl z) = D.siteTerm z from rfl,
          siteTerm_single_apply_eq_zero hxy (hS b hb).1 (hS b hb).2 hγx hγy, mul_zero]
    · have hb' : ∀ b ∈ f.support, (D.interaction.Φ (Sum.inr (u, v))).1.1 (single b 1) γ =
          if D.graph.Adj u v then D.Δ u v * cre u (cre v (single b (1 : ℂ))) γ else 0 :=
        fun b hb => bondTerm_single_apply hxy (hS b hb).1 (hS b hb).2 hγx hγy D u v
      rw [Finset.sum_congr rfl fun b hb => by rw [hb' b hb]]
      by_cases h1 : u = x ∧ v = y
      · obtain ⟨rfl, rfl⟩ := h1
        simp only [if_pos hadj, if_true]
        rw [Finset.sum_eq_single α]
        · rw [cre_cre_single_of_empty hxy hα.1 hα.2]; simp; ring
        · intro b hb hne
          rw [cre_cre_single_of_empty hxy (hS b hb).1 (hS b hb).2, Finsupp.single_apply, if_neg
            (fun h => hne (by simpa [hγ] using h))]
          ring
        · intro hα'; rw [Finsupp.notMem_support_iff.mp hα']; ring
      by_cases h2 : u = y ∧ v = x
      · obtain ⟨rfl, rfl⟩ := h2
        have hne : (Sum.inr (u, v) : L ⊕ (L × L)) ≠ Sum.inr (v, u) := by simp [hxy.symm]
        simp only [if_pos hadj.symm, if_neg hne, if_true]
        rw [Finset.sum_eq_single α]
        · rw [cre_cre_single_of_empty hxy.symm hα.2 hα.1]
          simp [hγ, add_right_comm]
        · intro b hb hne
          rw [cre_cre_single_of_empty hxy.symm (hS b hb).2 (hS b hb).1, Finsupp.single_apply,
            if_neg (fun h => hne (by simpa [hγ, add_right_comm] using h))]
          ring
        · intro hα'; rw [Finsupp.notMem_support_iff.mp hα']; ring
      · have hne1 : (Sum.inr (u, v) : L ⊕ (L × L)) ≠ Sum.inr (x, y) := fun h => h1 (by simpa using h)
        have hne2 : (Sum.inr (u, v) : L ⊕ (L × L)) ≠ Sum.inr (y, x) := fun h => h2 (by simpa using h)
        rw [if_neg hne1, if_neg hne2]
        refine Finset.sum_eq_zero fun b hb => ?_
        split_ifs
        · rw [cre_cre_single_apply_eq_zero hxy (hS b hb).1 (hS b hb).2 hγx hγy ⟨h1, h2⟩]; ring
        · ring
  show ∑ᶠ i, (D.interaction.Φ i).1.1 f γ = _
  rw [finsum_congr hterm]
  have hne : (Sum.inr (x, y) : L ⊕ (L × L)) ≠ Sum.inr (y, x) := by simp [hxy]
  rw [finsum_eq_sum_of_support_subset (s := {Sum.inr (x, y), Sum.inr (y, x)})]
  · rw [Finset.sum_pair hne]; simp [hne.symm]; ring
  · intro i hi
    simp only [Function.mem_support] at hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    by_contra h
    push_neg at h
    exact hi (by rw [if_neg h.1, if_neg h.2])

/-- **Pairing on infinitely many disjoint bonds leaves no finite vector in the domain.** Let
`x_n ~ y_n` be bonds with pairwise distinct modes on which the symmetrized pairing amplitude
`Δ_{x_n y_n} + Δ_{y_n x_n}` is bounded away from zero. Then the formal image of every nonzero finite
vector fails to be square summable: pairs are created on all far away bonds with amplitudes that
do not decay. This covers translation-invariant pairing on an infinite lattice. -/
theorem hamDomainAlg_eq_bot (D : BoseHubbardData L) (x y : ℕ → L)
    (hadj : ∀ n, D.graph.Adj (x n) (y n)) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxy : ∀ n m, x n ≠ y m) {δ : ℝ} (hδ : 0 < δ) (hΔ : ∀ n, δ ≤ ‖D.Δ (x n) (y n) + D.Δ (y n) (x n)‖) :
    hamDomainAlg D.interaction.Φ D.rowFinite = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  by_contra hf0
  obtain ⟨α, hα⟩ := Finsupp.support_nonempty_iff.mpr hf0
  set S : Finset L := f.support.biUnion Finsupp.support
  have hfar : ∀ᶠ n in Filter.atTop, x n ∉ S ∧ y n ∉ S := by
    rw [← Nat.cofinite_eq_atTop]
    exact ((S.finite_toSet.preimage hx.injOn).union (S.finite_toSet.preimage hy.injOn)).subset
      (fun n hn => by simpa [not_and_or] using hn)
  have hzero : ∀ {z : L}, z ∉ S → ∀ b ∈ f.support, b z = 0 := fun hz b hb => by
    by_contra h
    exact hz (Finset.mem_biUnion.mpr ⟨b, hb, Finsupp.mem_support_iff.mpr h⟩)
  set γ : ℕ → Occ L := fun n => α + single (x n) 1 + single (y n) 1
  have hγinj : Function.Injective γ := fun n m h => by
    by_contra hnm
    have := congrArg (· (x n)) h
    simp [γ, Finsupp.single_apply, hx.ne hnm, hxy n n, hxy n m] at this
  -- the formal image is square summable, so it tends to zero along the injective sequence `γ`
  have hlim : Filter.Tendsto (fun n => D.formalHam f (γ n)) Filter.atTop (nhds 0) := by
    have hm : Memℓp (D.formalHam f) 2 := hf
    have hs : Summable fun β => ‖D.formalHam f β‖ ^ (2 : ℝ) := hm.summable (by norm_num)
    have h0 := hs.tendsto_cofinite_zero
    rw [← Nat.cofinite_eq_atTop]
    have h1 : Filter.Tendsto (fun β => D.formalHam f β) Filter.cofinite (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have := h0.rpow_const (p := 1 / 2) (Or.inr (by norm_num))
      simp only [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] at this
      refine this.congr fun β => ?_
      rw [← Real.rpow_mul (norm_nonneg _)]; norm_num
    exact h1.comp hγinj.tendsto_cofinite
  -- but at far away bonds its value is `(Δ + Δ') f(α)`, bounded away from zero
  have hval : ∀ᶠ n in Filter.atTop, δ * ‖f α‖ ≤ ‖D.formalHam f (γ n)‖ := hfar.mono fun n hn => by
    have hα0 : α x n = 0 ∧ α y n = 0 := ⟨hzero hn.1 α hα, hzero hn.2 α hα⟩
    rw [formalHam_apply_pair D (hadj n) (fun b hb => ⟨hzero hn.1 b hb, hzero hn.2 b hb⟩) α hα0,
      norm_mul]
    exact mul_le_mul_of_nonneg_right (hΔ n) (norm_nonneg _)
  have hpos : 0 < δ * ‖f α‖ := mul_pos hδ (norm_pos_iff.mpr (Finsupp.mem_support_iff.mp hα))
  have := (hlim.norm.eventually (gt_mem_nhds (a := 0) (b := δ * ‖f α‖) (by simpa using hpos)))
  obtain ⟨n, hn1, hn2⟩ := (this.and hval).exists
  simp only [norm_zero] at hn1
  linarith

end BoseHubbardData

end InfiniteBosons
