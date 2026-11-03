/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.AtomPhotonHamiltonian
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.HamiltonianDynamics
/-!

# The atom-photon Hamiltonian is densely defined

The formal image of a basis vector of the atom-photon lattice has finite support.

## i. Overview

A basis state has finitely many occupied cavities. The cavity terms act on it only at those cavities.
A hopping term acts only if it touches a photon of the state, and the graph is locally finite. So
finitely many terms act on a basis state, each produces a finitely supported vector, and the formal
image has finite support. It is square summable. The domain of the Hamiltonian contains all finite
vectors and is dense. The dynamics exists as a theorem when the operator is essentially
self-adjoint.

## ii. Key results

- `InfiniteBosons.AtomPhotonData.finite_acting`: finitely many terms act on a state.
- `InfiniteBosons.AtomPhotonData.formalHam_basis_mem`: the image lies in `ℓ²`.
- `InfiniteBosons.AtomPhotonData.hamOp_dense`: density of the domain.
- `InfiniteBosons.AtomPhotonData.dynamics_of_essentiallySelfAdjoint`: the unitary group.
- `InfiniteBosons.AtomPhotonData.isDiagonal_decoupled`, `InfiniteBosons.AtomPhotonData.dynamics_decoupled`:
  the decoupled lattice (no hopping and no coupling) is diagonal and essentially self-adjoint, and
  generates a unitary group.

## iii. Table of contents

- A. Finitely many terms act
- B. Density and dynamics

## iv. References

* B. W. Shore, P. L. Knight, The Jaynes-Cummings model, J. Mod. Opt. 40 (1993) 1195.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

namespace AtomPhotonData

variable (D : AtomPhotonData L)

/-- A bond term acts nontrivially on a state only if it touches a photon of the source. -/
lemma bondTerm_ne_src {x y : L} {b a : SBBasis L}
    (h : (D.bondTerm x y).1.1 (single b 1) a ≠ 0) : x ∈ b.1.support ∨ y ∈ b.1.support := by
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
      · exact Or.inl (creAnnS_ne h2).1
    · exact Or.inr (creAnnS_ne h1).1
  · exfalso; apply h
    unfold AtomPhotonData.bondTerm
    rw [if_neg hadj]
    rfl

lemma adj_of_bondTerm_ne {x y : L} {b a : SBBasis L}
    (h : (D.bondTerm x y).1.1 (single b 1) a ≠ 0) : D.graph.Adj x y := by
  by_contra hadj
  apply h
  unfold AtomPhotonData.bondTerm
  rw [if_neg hadj]
  rfl

/-- The terms acting nontrivially on a basis state form a finite set. -/
lemma finite_acting (b : SBBasis L) :
    {i : L ⊕ (L × L) | ∃ a, (D.interaction.Φ i).1.1 (single b 1) a ≠ 0}.Finite := by
  set B : Finset L := b.1.support with hB
  have hsub : {i : L ⊕ (L × L) | ∃ a, (D.interaction.Φ i).1.1 (single b 1) a ≠ 0} ⊆
      (Sum.inl '' ((sbModes b : Finset L) : Set L)) ∪
        (Sum.inr '' ((⋃ x ∈ B, ({x} : Set L) ×ˢ D.graph.neighborSet x) ∪
          (⋃ y ∈ B, D.graph.neighborSet y ×ˢ ({y} : Set L)))) := by
    rintro (x | p) ⟨a, ha⟩
    · exact Or.inl ⟨x, D.siteTerm_ne ha, rfl⟩
    · have hadj := D.adj_of_bondTerm_ne (x := p.1) (y := p.2) ha
      rcases D.bondTerm_ne_src ha with h1 | h1
      · refine Or.inr ⟨p, Or.inl ?_, rfl⟩
        simp only [Set.mem_iUnion]
        exact ⟨p.1, h1, by simpa using hadj⟩
      · refine Or.inr ⟨p, Or.inr ?_, rfl⟩
        simp only [Set.mem_iUnion]
        exact ⟨p.2, h1, by simpa using hadj.symm⟩
  refine Set.Finite.subset ?_ hsub
  refine (Set.Finite.image _ (Finset.finite_toSet _)).union (Set.Finite.image _ ?_)
  refine Set.Finite.union ?_ ?_
  · exact B.finite_toSet.biUnion fun x _ => (Set.finite_singleton x).prod (D.locallyFinite x)
  · exact B.finite_toSet.biUnion fun y _ => (D.locallyFinite y).prod (Set.finite_singleton y)

/-- **The formal image of a basis vector has finite support.** -/
lemma formalHam_basis_finite (b : SBBasis L) :
    {a : SBBasis L | D.formalHam (single b 1) a ≠ 0}.Finite := by
  have hsub : {a : SBBasis L | D.formalHam (single b 1) a ≠ 0} ⊆
      ⋃ i ∈ D.finite_acting b |>.toFinset, ((D.interaction.Φ i).1.1 (single b 1)).support := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    have : ∃ i, (D.interaction.Φ i).1.1 (single b 1) a ≠ 0 := by
      by_contra hn
      push Not at hn
      apply ha
      show ∑ᶠ i, (D.interaction.Φ i).1.1 (single b 1) a = 0
      exact finsum_eq_zero_of_forall_eq_zero hn
    obtain ⟨i, hi⟩ := this
    simp only [Set.mem_iUnion, Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨i, ⟨a, hi⟩, by simpa [Finsupp.mem_support_iff] using hi⟩
  refine Set.Finite.subset ?_ hsub
  exact (D.finite_acting b).toFinset.finite_toSet.biUnion fun i _ => Finset.finite_toSet _

/-- **The domain of the atom-photon Hamiltonian contains all finite vectors.** -/
theorem formalHam_basis_mem (b : SBBasis L) : Memℓp (D.formalHam (single b 1)) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine summable_of_ne_finset_zero (s := (D.formalHam_basis_finite b).toFinset) fun a ha => ?_
  have h0 : D.formalHam (single b 1) a = 0 := by
    by_contra hne; exact ha (by simpa using hne)
  simp [h0]

theorem hamOp_dense : D.hamOp.HasDenseDomain :=
  hamPMap_dense D.interaction.Φ D.rowFinite D.formalHam_basis_mem

/-- **The atom-photon lattice is usable: its Hamiltonian is a densely defined symmetric operator and
the dynamics exists whenever it is essentially self-adjoint.** -/
theorem dynamics_of_essentiallySelfAdjoint (hess : D.hamOp.IsEssentiallySelfAdjoint) :
    ∃ U : ProbabilisticTheory.QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup
        (HilbertSp (SBBasis L)),
      (∀ t s, U (t + s) = U t * U s) ∧ U 0 = 1 ∧
      ∀ f : hamDomainAlg D.interaction.Φ D.rowFinite,
        HasDerivAt (fun t : ℝ => U t (embed f.1))
          (Complex.I • (hamVec D.interaction.Φ D.rowFinite f : HilbertSp (SBBasis L))) 0 :=
  hamPMap_dynamics D.interaction.Φ D.rowFinite hess

end AtomPhotonData


lemma photonNumber_basis (x : L) (b : SBBasis L) :
    (AtomPhotonData.photonNumber x).1.1 (single b 1) = ((b.1 x : ℕ) : ℂ) • single b 1 := by
  show creS x (annS x (single b (1 : ℂ))) = _
  rw [annS_single, creS_single]
  by_cases h : b.1 x = 0
  · simp [h]
  · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h
    have e1 : b.1 - single x 1 + single x 1 = b.1 := by
      ext l; by_cases hl : l = x
      · subst hl; simp [hn]
      · simp [Finsupp.single_apply, Ne.symm hl]
    have e2 : (b.1 - single x 1 : Occ L) x = n := by simp [hn]
    rw [e1, e2, Finsupp.smul_single]
    congr 1
    rw [hn]
    simp only [mul_one, Nat.cast_succ]
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
    push_cast
    rw [Real.sqrt_mul_self (by positivity)]
    simp [smul_eq_mul]

lemma atomNumber_basis (x : L) (b : SBBasis L) :
    (AtomPhotonData.atomNumber x).1.1 (single b 1) =
      (if x ∈ b.2 then (1 : ℂ) else 0) • single b 1 := by
  show raiseS x (lowS x (single b (1 : ℂ))) = _
  rw [lowS_single]
  by_cases hx : x ∈ b.2
  · simp only [hx, if_true]
    rw [raiseS_single]
    simp [Finset.insert_erase hx]
  · simp [hx]


namespace AtomPhotonData

variable (D : AtomPhotonData L)

/-- The free energy of a cavity in a basis state. -/
def siteEnergy (x : L) (b : SBBasis L) : ℝ := D.ω x * (b.1 x : ℝ) + (if x ∈ b.2 then D.ε x else 0)

lemma siteTerm_basis_decoupled (hg : ∀ x, D.g x = 0) (x : L) (b : SBBasis L) :
    (D.siteTerm x).1.1 (single b 1) = ((D.siteEnergy x b : ℝ) : ℂ) • single b 1 := by
  have hjc : jaynesCummings x (D.g x) = 0 := by
    rw [hg x]; unfold jaynesCummings; simp
  have e : (D.siteTerm x).1.1 (single b 1) = ((D.ω x : ℝ) : ℂ) •
      (photonNumber x).1.1 (single b 1) + ((D.ε x : ℝ) : ℂ) • (atomNumber x).1.1 (single b 1) := by
    unfold AtomPhotonData.siteTerm
    rw [hjc, add_zero]
    rfl
  rw [e, photonNumber_basis, atomNumber_basis, smul_smul, smul_smul, ← add_smul]
  congr 1
  unfold siteEnergy
  by_cases hx : x ∈ b.2 <;> simp [hx]

lemma siteEnergy_zero {x : L} {b : SBBasis L} (hx : x ∉ sbModes b) : D.siteEnergy x b = 0 := by
  have h1 : b.1 x = 0 := by
    by_contra h; exact hx (Finset.mem_union_left _ (Finsupp.mem_support_iff.mpr h))
  have h2 : x ∉ b.2 := fun h => hx (Finset.mem_union_right _ h)
  simp [siteEnergy, h1, h2]

lemma bondTerm_eq_zero (hJ : ∀ x y, D.J x y = 0) (x y : L) : D.bondTerm x y = 0 := by
  unfold AtomPhotonData.bondTerm
  split_ifs
  · simp [hJ]
  · rfl

/-- **The decoupled atom-photon Hamiltonian is diagonal.** -/
theorem isDiagonal_decoupled (hJ : ∀ x y, D.J x y = 0) (hg : ∀ x, D.g x = 0) :
    IsDiagonal D.interaction.Φ D.rowFinite
      (fun b => ∑ x ∈ sbModes b, D.siteEnergy x b) := by
  intro b α
  show ∑ᶠ i, (D.interaction.Φ i).1.1 (single b 1) α = _
  have hterm : ∀ i : L ⊕ (L × L), (D.interaction.Φ i).1.1 (single b 1) α =
      Sum.elim (fun x => ((D.siteEnergy x b : ℝ) : ℂ) * (single b (1 : ℂ) : SBBasis L →₀ ℂ) α)
        (fun _ => 0) i := by
    rintro (x | p)
    · show (D.siteTerm x).1.1 (single b 1) α = _
      rw [D.siteTerm_basis_decoupled hg]
      show (((D.siteEnergy x b : ℝ) : ℂ) • (single b (1 : ℂ) : SBBasis L →₀ ℂ)) α = _
      rw [Finsupp.smul_apply, smul_eq_mul]
      rfl
    · show (D.bondTerm p.1 p.2).1.1 (single b 1) α = _
      rw [D.bondTerm_eq_zero hJ]
      rfl
  rw [finsum_congr hterm]
  rw [finsum_eq_sum_of_support_subset (s := (sbModes b).map Function.Embedding.inl)]
  · rw [Finset.sum_map]
    simp only [Function.Embedding.inl_apply, Sum.elim_inl]
    rw [← Finset.sum_mul]
    by_cases hα : α = b
    · subst hα; simp
    · simp [hα, Finsupp.single_apply, Ne.symm hα]
  · intro i hi
    rcases i with x | p
    · simp only [Function.mem_support, Sum.elim_inl] at hi
      have : x ∈ sbModes b := by
        by_contra hx; exact hi (by simp [D.siteEnergy_zero hx])
      simpa using this
    · simp at hi

/-- **The decoupled atom-photon lattice is usable**: its Hamiltonian is essentially self-adjoint and
generates a unitary group on an arbitrary lattice. -/
theorem dynamics_decoupled (hJ : ∀ x y, D.J x y = 0) (hg : ∀ x, D.g x = 0) :
    ∃ U : ProbabilisticTheory.QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup
        (HilbertSp (SBBasis L)),
      (∀ t s, U (t + s) = U t * U s) ∧ U 0 = 1 ∧
      ∀ f : hamDomainAlg D.interaction.Φ D.rowFinite,
        HasDerivAt (fun t : ℝ => U t (embed f.1))
          (Complex.I • (hamVec D.interaction.Φ D.rowFinite f : HilbertSp (SBBasis L))) 0 :=
  D.dynamics_of_essentiallySelfAdjoint
    (hamPMap_ess_diag _ _ D.interaction.star_eq _ (D.isDiagonal_decoupled hJ hg))

end AtomPhotonData

end InfiniteBosons
