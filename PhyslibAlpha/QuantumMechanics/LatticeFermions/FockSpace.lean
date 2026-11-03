/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.LatticeFermions.WeightedComposition
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!

# The fermionic Fock space and the canonical anticommutation relations

The creation and annihilation operators of fermions in an ordered set of modes, as bounded
operators on the Fock space `ℓ²(Finset M)`.

## i. Overview

A configuration of fermions in a set of modes `M` is the finite set `F ⊆ M` of occupied modes,
and the Fock space is `ℓ²(Finset M)`, with the occupation number basis `e_F`. Fix a linear order
on the modes. The annihilator of the mode `j` removes `j` from a configuration containing it and
multiplies by the Jordan–Wigner sign `(-1)^{#{i ∈ F | i < j}}`, which counts the occupied modes
before `j`:

`c_j e_F = (-1)^{#{i ∈ F | i < j}} e_{F \ {j}}` if `j ∈ F`, and `c_j e_F = 0` otherwise.

On wave functions this is a weighted composition, `(c_j ψ)(F) = ± ψ(F ∪ {j})` for `j ∉ F`, so it
is a bounded operator. Its adjoint, the creator `c_j*`, adds `j` with the same sign. The signs
make the operators of different modes anticommute: the canonical anticommutation relations

`c_i c_j + c_j c_i = 0`, `c_i c_j* + c_j* c_i = δ_ij`

hold. The parity `(-1)^N`, multiplying `e_F` by `(-1)^{|F|}`, is a self-adjoint unitary
anticommuting with every `c_j`. The set of modes may be infinite; the order is only a
bookkeeping device for the signs.

## ii. Key results

- `LatticeFermions.FockSpace` : the Fock space `ℓ²(Finset M)`.
- `LatticeFermions.jwSign` : the Jordan–Wigner sign.
- `LatticeFermions.ann`, `LatticeFermions.cre` : the annihilation and creation operators.
- `LatticeFermions.star_ann` : the creator is the adjoint of the annihilator.
- `LatticeFermions.ann_mul_ann` : annihilators anticommute.
- `LatticeFermions.ann_mul_cre_add` : the anticommutator of an annihilator and a creator.
- `LatticeFermions.parityOp` : the parity operator `(-1)^N`.
- `LatticeFermions.parityOp_mul_ann` : the parity anticommutes with every annihilator.
- `LatticeFermions.numOp` : the number operator of a mode.
- `LatticeFermions.numOp_add_numOp_commutator_cre_mul_cre` : pair creators raise the number of
  particles by two.
- `LatticeFermions.cre_mul_cre_ne_zero` : pair creators of different modes are not zero.

## iii. Table of contents

- A. The Jordan–Wigner sign
- B. Annihilation and creation operators
- C. The anticommutation relations
- D. The parity operator
- E. Number operators
- F. The vacuum

## iv. References

* O. Bratteli, D. W. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 5.2.2.

-/

@[expose] public section

noncomputable section

namespace LatticeFermions

open ComplexConjugate

/-- The fermionic Fock space over the set of modes `M`: square summable functions of the finite
sets of occupied modes. It is a type synonym of `ℓ²(Finset M)`, so that the operators on it have
one canonical ring structure. -/
def FockSpace (M : Type*) : Type _ := lp (fun _ : Finset M => ℂ) 2

namespace FockSpace

variable {M : Type*}

instance : NormedAddCommGroup (FockSpace M) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : Finset M => ℂ) 2))

instance : InnerProductSpace ℂ (FockSpace M) :=
  inferInstanceAs (InnerProductSpace ℂ (lp (fun _ : Finset M => ℂ) 2))

instance : CompleteSpace (FockSpace M) :=
  inferInstanceAs (CompleteSpace (lp (fun _ : Finset M => ℂ) 2))

/-- The amplitude `ψ(F)` of a vector of the Fock space at the configuration `F`. -/
instance : CoeFun (FockSpace M) (fun _ => Finset M → ℂ) :=
  ⟨fun ψ => (Subtype.val ψ : ∀ _ : Finset M, ℂ)⟩

lemma ext {ψ φ : FockSpace M} (h : ∀ F, ψ F = φ F) : ψ = φ :=
  lp.ext (funext h)

@[simp]
lemma add_apply (ψ φ : FockSpace M) (F : Finset M) : (ψ + φ) F = ψ F + φ F := rfl

@[simp]
lemma neg_apply (ψ : FockSpace M) (F : Finset M) : (-ψ) F = -ψ F := rfl

lemma inner_eq_tsum (ψ φ : FockSpace M) :
    inner ℂ ψ φ = ∑' F, conj (ψ F) * φ F := by
  simp only [← RCLike.inner_apply']
  exact lp.inner_eq_tsum (𝕜 := ℂ) (G := fun _ : Finset M => ℂ) ψ φ

end FockSpace

variable {M : Type*}

/-- The algebra of bounded operators on the Fock space, a C⋆-algebra. -/
abbrev FockOp (M : Type*) := FockSpace M →L[ℂ] FockSpace M

/-- Two operators on the Fock space are equal if their values agree on every configuration. -/
lemma fock_ext {T S : FockOp M} (h : ∀ ψ F, T ψ F = S ψ F) : T = S :=
  ContinuousLinearMap.ext fun ψ => FockSpace.ext (h ψ)

variable [LinearOrder M]

/-!

## A. The Jordan–Wigner sign

-/

/-- The Jordan–Wigner sign `(-1)^{#{i ∈ F | i < j}}` of the mode `j` in the configuration `F`. -/
def jwSign (F : Finset M) (j : M) : ℂ := (-1) ^ (F.filter (· < j)).card

lemma jwSign_mul_self (F : Finset M) (j : M) : jwSign F j * jwSign F j = 1 := by
  rw [jwSign, ← pow_add, ← two_mul, pow_mul]; simp

lemma norm_jwSign (F : Finset M) (j : M) : ‖jwSign F j‖ = 1 := by simp [jwSign]

lemma conj_jwSign (F : Finset M) (j : M) : conj (jwSign F j) = jwSign F j := by simp [jwSign]

/-- Adding an unoccupied mode `i` changes the sign of `j` exactly when `i` comes before `j`. -/
lemma jwSign_insert {F : Finset M} {i : M} (hi : i ∉ F) (j : M) :
    jwSign (insert i F) j = (if i < j then -1 else 1) * jwSign F j := by
  unfold jwSign
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => hi (Finset.mem_filter.mp h').1), pow_succ]
    ring
  · ring

lemma jwSign_insert_self (F : Finset M) (j : M) : jwSign (insert j F) j = jwSign F j := by
  unfold jwSign
  rw [Finset.filter_insert, ite_eq_right (lt_irrefl j)]

/-- Removing an occupied mode `i` changes the sign of `j` exactly when `i` comes before `j`. -/
lemma jwSign_erase {F : Finset M} {i : M} (hi : i ∈ F) (j : M) :
    jwSign (F.erase i) j = (if i < j then -1 else 1) * jwSign F j := by
  conv_rhs => rw [← Finset.insert_erase hi, jwSign_insert (Finset.notMem_erase i F)]
  split_ifs <;> ring

/-!

## B. Annihilation and creation operators

-/

/-- The weight of the annihilator: the sign of `j`, or zero if `j` is already occupied. -/
def annWeight (j : M) (F : Finset M) : ℂ := if j ∈ F then 0 else jwSign F j

/-- The weight of the creator: the sign of `j` if `j` is occupied, and zero otherwise. -/
def creWeight (j : M) (G : Finset M) : ℂ := if j ∈ G then jwSign G j else 0

lemma norm_annWeight_le (j : M) (F : Finset M) : ‖annWeight j F‖ ≤ 1 := by
  unfold annWeight; split_ifs <;> simp [norm_jwSign]

lemma norm_creWeight_le (j : M) (G : Finset M) : ‖creWeight j G‖ ≤ 1 := by
  unfold creWeight; split_ifs <;> simp [norm_jwSign]

lemma injOn_annWeight (j : M) : {F | annWeight j F ≠ 0}.InjOn (insert j) := by
  have key : ∀ F : Finset M, annWeight j F ≠ 0 → j ∉ F := fun F h hj => h (by simp [annWeight, hj])
  intro F hF F' hF' h
  rw [← Finset.erase_insert (key F hF), h, Finset.erase_insert (key F' hF')]

lemma injOn_creWeight (j : M) : {G | creWeight j G ≠ 0}.InjOn (fun G => G.erase j) := by
  have key : ∀ G : Finset M, creWeight j G ≠ 0 → j ∈ G := fun G h => by
    by_contra hj; exact h (by simp [creWeight, hj])
  exact fun G hG G' hG' h => Finset.erase_injOn' j (key G hG) (key G' hG') h

/-- The annihilator of the mode `j`. -/
def ann (j : M) : FockOp M :=
  weightedComp (α := Finset M) (norm_annWeight_le j) (injOn_annWeight j)

/-- The creator of the mode `j`. -/
def cre (j : M) : FockOp M :=
  weightedComp (α := Finset M) (norm_creWeight_le j) (injOn_creWeight j)

lemma ann_apply (j : M) (ψ : FockSpace M) (F : Finset M) :
    ann j ψ F = if j ∈ F then 0 else jwSign F j * ψ (insert j F) := by
  change annWeight j F * ψ (insert j F) = _
  unfold annWeight
  split_ifs <;> simp

lemma cre_apply (j : M) (ψ : FockSpace M) (G : Finset M) :
    cre j ψ G = if j ∈ G then jwSign G j * ψ (G.erase j) else 0 := by
  change creWeight j G * ψ (G.erase j) = _
  unfold creWeight
  split_ifs <;> simp

/-- The terms of `⟪c_j* ψ, φ⟫` at `F ∪ {j}` are those of `⟪ψ, c_j φ⟫` at `F`. -/
lemma conj_cre_mul_insert (j : M) (ψ φ : FockSpace M) {F : Finset M} (hF : j ∉ F) :
    conj (cre j ψ (insert j F)) * φ (insert j F) = conj (ψ F) * ann j φ F := by
  rw [cre_apply, ann_apply, ite_eq_left (Finset.mem_insert_self j F), ite_eq_right hF,
    Finset.erase_insert hF, jwSign_insert_self, map_mul, conj_jwSign]
  ring

lemma inner_cre (j : M) (ψ φ : FockSpace M) :
    inner ℂ (cre j ψ) φ = inner ℂ ψ (ann j φ) := by
  simp only [FockSpace.inner_eq_tsum]
  have hsupp : ∀ F : Finset M, conj (ψ F) * ann j φ F ≠ 0 → j ∉ F := fun F h hj =>
    h (by rw [ann_apply, ite_eq_left hj, mul_zero])
  refine tsum_eq_tsum_of_ne_zero_bij (fun F => insert j F.1) ?_ ?_ ?_
  · intro F F' h
    have h' : insert j F.1 = insert j F'.1 := h
    exact Subtype.ext (by
      rw [← Finset.erase_insert (hsupp F F.2), h', Finset.erase_insert (hsupp F' F'.2)])
  · intro G hG
    have hj : j ∈ G := by
      by_contra hj; exact hG (by simp [cre_apply, hj])
    refine ⟨⟨G.erase j, ?_⟩, Finset.insert_erase hj⟩
    simp only [Function.mem_support]
    rw [← conj_cre_mul_insert j ψ φ (Finset.notMem_erase j G), Finset.insert_erase hj]
    exact hG
  · exact fun F => conj_cre_mul_insert j ψ φ (hsupp F F.2)

/-- The creator is the adjoint of the annihilator. -/
lemma star_ann (j : M) : star (ann j) = cre j := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr (inner_cre j)).symm

lemma star_cre (j : M) : star (cre j) = ann j := by rw [← star_ann, star_star]

lemma norm_ann_le (j : M) : ‖ann j‖ ≤ 1 := norm_weightedComp_le _ _

lemma norm_cre_le (j : M) : ‖cre j‖ ≤ 1 := by rw [← star_ann, norm_star]; exact norm_ann_le j

/-!

## C. The anticommutation relations

-/

/-- Annihilators anticommute: `c_i c_j = - c_j c_i`. -/
lemma ann_mul_ann (i j : M) : ann i * ann j = -(ann j * ann i) := by
  refine fock_ext fun ψ F => ?_
  simp only [mul_apply_eq_comp, neg_apply, FockSpace.neg_apply, ann_apply, Finset.mem_insert]
  rcases eq_or_ne i j with rfl | hij
  · simp
  by_cases hi : i ∈ F
  · simp [hi]
  by_cases hj : j ∈ F
  · simp [hj]
  simp only [hi, hj, hij, hij.symm, or_self, ite_false, jwSign_insert hi, jwSign_insert hj,
    Finset.insert_comm i j F]
  rcases lt_or_gt_of_ne hij with h | h <;> simp [h, not_lt.mpr h.le] <;> ring

/-- Creators anticommute: `c_i* c_j* = - c_j* c_i*`. -/
lemma cre_mul_cre (i j : M) : cre i * cre j = -(cre j * cre i) := by
  calc cre i * cre j = star (ann j * ann i) := by rw [star_mul, star_ann, star_ann]
    _ = star (-(ann i * ann j)) := by rw [ann_mul_ann j i]
    _ = -star (ann i * ann j) := star_neg _
    _ = -(cre j * cre i) := by rw [star_mul, star_ann, star_ann]

/-- The anticommutator of an annihilator and a creator of the same mode is the identity. -/
lemma ann_mul_cre_add_self (j : M) : ann j * cre j + cre j * ann j = 1 := by
  refine fock_ext fun ψ F => ?_
  simp only [add_apply, mul_apply_eq_comp, FockSpace.add_apply, one_apply_eq_self, ann_apply,
    cre_apply]
  by_cases hj : j ∈ F
  · rw [ite_eq_left hj, ite_eq_left hj, ite_eq_right (Finset.notMem_erase j F),
      Finset.insert_erase hj, ← jwSign_insert_self (F.erase j), Finset.insert_erase hj,
      ← mul_assoc, jwSign_mul_self]
    simp
  · rw [ite_eq_right hj, ite_eq_right hj, ite_eq_left (Finset.mem_insert_self j F),
      Finset.erase_insert hj, jwSign_insert_self, ← mul_assoc, jwSign_mul_self]
    simp

/-- An annihilator and a creator of different modes anticommute. -/
lemma ann_mul_cre_of_ne {i j : M} (hij : i ≠ j) : ann i * cre j = -(cre j * ann i) := by
  refine fock_ext fun ψ F => ?_
  simp only [mul_apply_eq_comp, neg_apply, FockSpace.neg_apply, ann_apply, cre_apply]
  by_cases hi : i ∈ F
  · simp [hi, Finset.mem_erase, hij]
  by_cases hj : j ∈ F
  · simp only [hi, hj, ite_false, ite_true, Finset.mem_insert, or_true, Finset.mem_erase, hij,
      ne_eq, not_false_eq_true, Finset.erase_insert_of_ne hij, jwSign_insert hi,
      jwSign_erase hj]
    rcases lt_or_gt_of_ne hij with h | h
    · simp [h, not_lt.mpr h.le]; ring
    · simp [h, not_lt.mpr h.le]; ring
  · simp [hi, hj, Finset.mem_insert, hij.symm]

/-- The canonical anticommutation relation `c_i c_j* + c_j* c_i = δ_ij`. -/
lemma ann_mul_cre_add (i j : M) :
    ann i * cre j + cre j * ann i = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h; exact ann_mul_cre_add_self i
  · rw [ann_mul_cre_of_ne h, neg_add_cancel]

/-- A creator and an annihilator of different modes anticommute. -/
lemma cre_mul_ann_of_ne {i j : M} (hij : i ≠ j) : cre i * ann j = -(ann j * cre i) := by
  rw [ann_mul_cre_of_ne hij.symm, neg_neg]

/-!

## D. The parity operator

-/

/-- The weight `(-1)^{|F|}` of the parity operator. -/
def parityWeight (F : Finset M) : ℂ := (-1) ^ F.card

omit [LinearOrder M] in
lemma norm_parityWeight_le (F : Finset M) : ‖parityWeight F‖ ≤ 1 := by simp [parityWeight]

/-- The parity operator `(-1)^N`, multiplying `e_F` by `(-1)^{|F|}`. -/
def parityOp : FockOp M :=
  weightedComp (g := id) norm_parityWeight_le Function.injective_id.injOn

omit [LinearOrder M] in
lemma parityOp_apply (ψ : FockSpace M) (F : Finset M) :
    parityOp ψ F = (-1) ^ F.card * ψ F := rfl

omit [LinearOrder M] in
lemma parityOp_mul_self : (parityOp : FockOp M) * parityOp = 1 :=
  fock_ext fun ψ F => by
    simp only [mul_apply_eq_comp, one_apply_eq_self, parityOp_apply,
      ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp

omit [LinearOrder M] in
lemma star_parityOp : star (parityOp : FockOp M) = parityOp := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun ψ φ => ?_).symm
  simp only [FockSpace.inner_eq_tsum, parityOp_apply]
  exact tsum_congr fun F => by simp; ring

omit [LinearOrder M] in
/-- The parity operator is a unitary. -/
lemma parityOp_mem_unitary : (parityOp : FockOp M) ∈ unitary _ :=
  ⟨by rw [star_parityOp, parityOp_mul_self], by rw [star_parityOp, parityOp_mul_self]⟩

/-- The parity anticommutes with every annihilator: `(-1)^N c_j = - c_j (-1)^N`. -/
lemma parityOp_mul_ann (j : M) : parityOp * ann j = -(ann j * parityOp) := by
  refine fock_ext fun ψ F => ?_
  simp only [mul_apply_eq_comp, neg_apply, FockSpace.neg_apply, ann_apply, parityOp_apply]
  by_cases hj : j ∈ F
  · simp [hj]
  · simp only [hj, ite_false, Finset.card_insert_of_notMem hj, pow_succ]
    ring

/-- The parity anticommutes with every creator. -/
lemma parityOp_mul_cre (j : M) : parityOp * cre j = -(cre j * parityOp) := by
  calc parityOp * cre j = star (ann j * parityOp) := by rw [star_mul, star_parityOp, star_ann]
    _ = star (-(parityOp * ann j)) := by rw [parityOp_mul_ann, neg_neg]
    _ = -star (parityOp * ann j) := star_neg _
    _ = -(cre j * parityOp) := by rw [star_mul, star_ann, star_parityOp]

/-!

## E. Number operators

-/

/-- The number operator `n_j = c_j* c_j` of the mode `j`. -/
def numOp (j : M) : FockOp M := cre j * ann j

lemma isSelfAdjoint_numOp (j : M) : IsSelfAdjoint (numOp j) := by
  rw [IsSelfAdjoint, numOp, star_mul, star_cre, star_ann]

lemma norm_numOp_le (j : M) : ‖numOp j‖ ≤ 1 :=
  (norm_mul_le _ _).trans <| by
    simpa using mul_le_mul (norm_cre_le j) (norm_ann_le j) (norm_nonneg _) zero_le_one

/-- Number operators commute. -/
lemma commute_numOp (i j : M) : Commute (numOp i) (numOp j) := by
  rcases eq_or_ne i j with rfl | hij
  · exact Commute.refl _
  have h1 : numOp i * numOp j = -(cre i * cre j * (ann i * ann j)) := by
    rw [numOp, numOp, show cre i * ann i * (cre j * ann j) = cre i * (ann i * cre j) * ann j by
      noncomm_ring, ann_mul_cre_of_ne hij]
    noncomm_ring
  have h2 : numOp j * numOp i = -(cre j * cre i * (ann j * ann i)) := by
    rw [numOp, numOp, show cre j * ann j * (cre i * ann i) = cre j * (ann j * cre i) * ann i by
      noncomm_ring, ann_mul_cre_of_ne hij.symm]
    noncomm_ring
  rw [Commute, SemiconjBy, h1, h2, cre_mul_cre i j, ann_mul_ann i j]
  noncomm_ring

lemma cre_mul_cre_self (j : M) : cre j * cre j = 0 := by
  have h := cre_mul_cre j j
  have h2 : (2 : ℂ) • (cre j * cre j) = 0 := by
    rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

lemma numOp_mul_cre_self (j : M) : numOp j * cre j = cre j := by
  have h := ann_mul_cre_add_self j
  rw [numOp, mul_assoc, eq_sub_of_add_eq h, mul_sub, mul_one, ← mul_assoc, cre_mul_cre_self,
    zero_mul, sub_zero]

lemma cre_mul_numOp_self (j : M) : cre j * numOp j = 0 := by
  rw [numOp, ← mul_assoc, cre_mul_cre_self, zero_mul]

lemma numOp_mul_cre_of_ne {i j : M} (hij : i ≠ j) : numOp i * cre j = cre j * numOp i := by
  rw [numOp, mul_assoc, ann_mul_cre_of_ne hij, mul_neg, ← mul_assoc, cre_mul_cre i j,
    neg_mul, neg_neg, mul_assoc]

/-- The pair creator `c_i* c_j*` raises the number of particles in the modes `i` and `j` by two:
`[n_i + n_j, c_i* c_j*] = 2 c_i* c_j*`. -/
lemma numOp_add_numOp_commutator_cre_mul_cre {i j : M} (hij : i ≠ j) :
    (numOp i + numOp j) * (cre i * cre j) - cre i * cre j * (numOp i + numOp j) =
      (2 : ℂ) • (cre i * cre j) := by
  have h1 : numOp i * (cre i * cre j) = cre i * cre j := by rw [← mul_assoc, numOp_mul_cre_self]
  have h2 : numOp j * (cre i * cre j) = cre i * cre j := by
    rw [← mul_assoc, numOp_mul_cre_of_ne hij.symm, mul_assoc, numOp_mul_cre_self]
  have h3 : cre i * cre j * numOp i = 0 := by
    rw [mul_assoc, ← numOp_mul_cre_of_ne hij, ← mul_assoc, cre_mul_numOp_self, zero_mul]
  have h4 : cre i * cre j * numOp j = 0 := by rw [mul_assoc, cre_mul_numOp_self, mul_zero]
  rw [add_mul, mul_add, h1, h2, h3, h4, two_smul]
  abel

/-!

## F. The vacuum

-/

/-- The vacuum: the configuration without particles. -/
def vacuum : FockSpace M := lp.single (E := fun _ : Finset M => ℂ) 2 ∅ 1

lemma vacuum_apply (F : Finset M) : vacuum F = if F = ∅ then 1 else 0 := by
  change lp.single (E := fun _ : Finset M => ℂ) 2 ∅ 1 F = _
  rw [lp.single_apply, Pi.single_apply]

lemma jwSign_ne_zero (F : Finset M) (j : M) : jwSign F j ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_jwSign]; exact one_ne_zero)

/-- The pair creator `c_i* c_j*` of two different modes is not zero. -/
lemma cre_mul_cre_ne_zero {i j : M} (hij : i ≠ j) : cre i * cre j ≠ 0 := by
  intro h
  have h0 : cre i (cre j vacuum) {i, j} = 0 := by
    change (cre i * cre j) vacuum {i, j} = 0
    rw [h]; rfl
  rw [cre_apply, ite_eq_left (Finset.mem_insert_self i {j}), cre_apply, Finset.erase_insert
    (by simpa using hij), ite_eq_left (Finset.mem_singleton_self j), Finset.erase_singleton,
    vacuum_apply, ite_eq_left rfl, mul_one] at h0
  exact mul_ne_zero (jwSign_ne_zero _ _) (jwSign_ne_zero _ _) h0

end LatticeFermions
