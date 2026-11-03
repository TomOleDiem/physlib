/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.ReferenceOperator
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.ResolventBridge
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FockNet
/-!

# The hopping operator has a bounded resolvent

Hopping between two modes of an infinite lattice is essentially self-adjoint on the algebraic Fock
space.

## i. Overview

The hopping operator `a_x† a_y + a_y† a_x` is unbounded. It conserves the number of bosons in
`{x, y}` and the occupation of every other mode. The set of such occupation vectors is finite.
Hence each basis vector lies in a finite invariant block, and the criterion
`dense_range_shiftMap_of_finite_invariant` applies. The hypothesis of the bridge from polynomial
to bounded observables is therefore proved for this observable. The lattice is arbitrary and no
sector is fixed.

## ii. Key results

- `InfiniteBosons.hopBlock`: the finite invariant block of an occupation vector.
- `InfiniteBosons.hop_support_subset`: hopping preserves the block.
- `InfiniteBosons.hop_resolvent`: the bounded resolvent of the hopping operator.

## iii. Table of contents

- A. Invariant blocks
- B. The resolvent

## iv. References

* M. Reed, B. Simon, Methods of Modern Mathematical Physics II, Section X.1.
-/

@[expose] public section

open Finsupp

noncomputable section
namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

lemma hop_apply_single (x y : L) (β : Occ L) :
    (hop x y).1.1 (single β 1) = cre x (ann y (single β 1)) + cre y (ann x (single β 1)) := rfl

/-- The occupation with `k` bosons in `x`, `n - k` in `y` and the configuration of `α` elsewhere. -/
def blockVec (x y : L) (α : Occ L) (k : ℕ) : Occ L :=
  (α.update x k).update y (α x + α y - k)

/-- The finite set of occupations reachable from `α` by hopping between `x` and `y`. -/
def hopBlock (x y : L) (α : Occ L) : Finset (Occ L) :=
  (Finset.range (α x + α y + 1)).image (blockVec x y α)

lemma blockVec_x {x y : L} (hxy : x ≠ y) (α : Occ L) (k : ℕ) : blockVec x y α k x = k := by
  simp [blockVec, Finsupp.update_apply, hxy]

lemma blockVec_y {x y : L} (α : Occ L) (k : ℕ) : blockVec x y α k y = α x + α y - k := by
  simp [blockVec, Finsupp.update_apply]

lemma blockVec_other {x y : L} (α : Occ L) (k : ℕ) {l : L} (hx : l ≠ x) (hy : l ≠ y) :
    blockVec x y α k l = α l := by
  simp [blockVec, Finsupp.update_apply, hx, hy]

lemma support_single_subset_of {a : Occ L} {c : ℂ} {F : Finset (Occ L)} (h : c ≠ 0 → a ∈ F) :
    ((single a c).support : Set (Occ L)) ⊆ F := by
  intro γ hγ
  by_cases hc : c = 0
  · simp [hc] at hγ
  · have := Finsupp.support_single_subset (Finset.mem_coe.mp hγ)
    rw [Finset.mem_singleton] at this
    rw [this]; exact h hc

lemma cre_ann_support {x y : L} (hxy : x ≠ y) (α : Occ L) {β : Occ L} (hβ : β ∈ hopBlock x y α) :
    ((cre x (ann y (single β (1 : ℂ)))).support : Set (Occ L)) ⊆ hopBlock x y α := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hβ
  rw [Finset.mem_range] at hk
  rw [ann_single, cre_single]
  refine support_single_subset_of fun hc => ?_
  have hy : blockVec x y α k y ≠ 0 := by
    intro h; apply hc; simp [h]
  rw [blockVec_y] at hy
  refine Finset.mem_image.mpr ⟨k + 1, Finset.mem_range.mpr (by omega), ?_⟩
  ext l
  by_cases hlx : l = x
  · subst hlx
    simp [blockVec_x hxy, hxy]
  · by_cases hly : l = y
    · subst hly
      simp [blockVec_y, hxy, hlx]
      omega
    · simp [blockVec_other _ _ hlx hly, hlx, hly]

lemma blockVec_swap {x y : L} (hxy : x ≠ y) (α : Occ L) {k : ℕ} (hk : k ≤ α y + α x) :
    blockVec y x α k = blockVec x y α (α x + α y - k) := by
  ext l
  by_cases hlx : l = x
  · subst hlx
    simp [blockVec_y, blockVec_x hxy, add_comm]
  · by_cases hly : l = y
    · subst hly
      rw [blockVec_x hxy.symm, blockVec_y]
      omega
    · rw [blockVec_other _ _ hlx hly, blockVec_other _ _ hly hlx]

lemma hopBlock_swap_subset {x y : L} (hxy : x ≠ y) (α : Occ L) :
    hopBlock y x α ⊆ hopBlock x y α := by
  intro β hβ
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hβ
  rw [Finset.mem_range] at hk
  refine Finset.mem_image.mpr ⟨α x + α y - k, Finset.mem_range.mpr (by omega), ?_⟩
  exact (blockVec_swap hxy α (by omega)).symm

lemma mem_hopBlock_self {x y : L} (α : Occ L) : α ∈ hopBlock x y α := by
  refine Finset.mem_image.mpr ⟨α x, Finset.mem_range.mpr (by omega), ?_⟩
  ext l
  by_cases hlx : l = x
  · subst hlx
    by_cases hxy : l = y
    · subst hxy; simp [blockVec, Finsupp.update_apply]
    · simp [blockVec, Finsupp.update_apply, hxy]
  · by_cases hly : l = y
    · subst hly; simp [blockVec, Finsupp.update_apply]
    · simp [blockVec, Finsupp.update_apply, hlx, hly]

/-- **The hopping operator preserves the finite blocks `hopBlock`.** -/
lemma hop_support_subset {x y : L} (hxy : x ≠ y) (α : Occ L) {β : Occ L}
    (hβ : β ∈ hopBlock x y α) :
    (((hop x y).1.1 (single β 1)).support : Set (Occ L)) ⊆ hopBlock x y α := by
  rw [hop_apply_single]
  intro γ hγ
  have hγ' := Finset.mem_coe.mp hγ
  rcases Finset.mem_union.mp (Finsupp.support_add hγ') with h | h
  · exact cre_ann_support hxy α hβ (Finset.mem_coe.mpr h)
  · have hβ' : β ∈ hopBlock y x α := by
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hβ
      rw [Finset.mem_range] at hk
      refine Finset.mem_image.mpr ⟨α x + α y - k, Finset.mem_range.mpr (by omega), ?_⟩
      rw [blockVec_swap hxy α (by omega)]
      congr 1
      omega
    have := cre_ann_support hxy.symm α hβ' (Finset.mem_coe.mpr h)
    exact hopBlock_swap_subset hxy α (Finset.mem_coe.mp this)

lemma star_hop (x y : L) : star (hop x y) = hop x y := by
  simp [hop, star_add, star_mul, star_annOp, star_creOp, add_comm]

/-- **Essential self-adjointness criterion for hopping, and its bounded resolvent.** For two
distinct modes the hopping operator `a_x† a_y + a_y† a_x` conserves the number of bosons in `{x, y}`
and the occupation of all other modes. Every occupation vector lies in a finite invariant block.
Hence the range of `hop + i c` is dense and the resolvent is a bounded operator of norm at most
`1/|c|`. -/
theorem hop_resolvent {x y : L} (hxy : x ≠ y) {c : ℝ} (hc : c ≠ 0) :
    ∃ R : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L), ‖R‖ ≤ 1 / |c| ∧
      ∀ f, R (shiftMap (hop x y).1.1 c f) = embed f := by
  have hsym : ∀ f g, pair ((hop x y).1.1 f) g = pair f ((hop x y).1.1 g) := fun f g => by
    have := star_fst_pair (hop x y) f g
    rwa [star_hop] at this
  exact polyOp_resolvent (hop x y) (star_hop x y) hc
    (dense_range_shiftMap_of_finite_invariant _ hsym
      (fun α => ⟨hopBlock x y α, mem_hopBlock_self α, fun β hβ =>
        hop_support_subset hxy α (Finset.mem_coe.mp hβ |> fun h => h)⟩) hc)

/-- **The on-site Bose-Hubbard term has a bounded resolvent.** The term `U/2 N(N-1) - μ N` is
diagonal in the occupation basis with real eigenvalues. -/
theorem siteTerm_resolvent (D : BoseHubbardData L) (x : L) {c : ℝ} (hc : c ≠ 0) :
    ∃ R : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L), ‖R‖ ≤ 1 / |c| ∧
      ∀ f, R (shiftMap (D.siteTerm x).1.1 c f) = embed f := by
  have hN : ∀ α : Occ L, (numberOp x * numberOp x).1.1 (single α 1) =
      (((α x : ℕ) : ℂ) * ((α x : ℕ) : ℂ)) • single α 1 := fun α => by
    show (numberOp x).1.1 ((numberOp x).1.1 (single α 1)) = _
    rw [numberOp_basis, map_smul, numberOp_basis, smul_smul]
  exact polyOp_resolvent (D.siteTerm x) (D.siteTerm_star x) hc
    (dense_range_shiftMap_of_diag _
      (fun α => D.U x / 2 * ((α x : ℝ) * (α x : ℝ) - α x) - D.μ x * (α x : ℝ))
      (fun α => by
        simp only [BoseHubbardData.siteTerm]
        show ((D.U x / 2 : ℝ) : ℂ) • (((numberOp x * numberOp x).1.1 (single α 1)) -
            (numberOp x).1.1 (single α 1)) - ((D.μ x : ℝ) : ℂ) • (numberOp x).1.1 (single α 1) = _
        rw [hN, numberOp_basis]
        simp only [← sub_smul, smul_smul, ← smul_sub]
        push_cast
        ring_nf) hc)

lemma refOp_basis (X : Finset L) (α : Occ L) :
    (refOp X).1.1 (single α 1) = ((1 + ∑ x ∈ X, (α x : ℝ) : ℝ) : ℂ) • single α 1 := by
  have h : ∀ (s : Finset L), ((∑ x ∈ s, numberOp x : adjointable L).1.1) (single α 1) =
      (∑ x ∈ s, ((α x : ℕ) : ℂ)) • single α 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      show (numberOp a).1.1 (single α 1) + (∑ x ∈ s, numberOp x : adjointable L).1.1 (single α 1) = _
      rw [numberOp_basis, ih, add_smul]
  show ((1 : adjointable L).1.1 (single α 1) + (∑ x ∈ X, numberOp x : adjointable L).1.1
    (single α 1)) = _
  rw [h]
  have h1 : (1 : adjointable L).1.1 (single α 1) = single α 1 := rfl
  rw [h1]
  push_cast
  rw [add_smul, one_smul]

/-- **The reference operator is closable and has a bounded resolvent.** `K_X` is diagonal in the
occupation basis with real eigenvalues `1 + Σ_{x ∈ X} α_x`. -/
theorem refOp_resolvent (X : Finset L) {c : ℝ} (hc : c ≠ 0) :
    ∃ R : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L), ‖R‖ ≤ 1 / |c| ∧
      ∀ f, R (shiftMap (refOp X).1.1 c f) = embed f :=
  polyOp_resolvent (refOp X) (star_refOp X) hc
    (dense_range_shiftMap_of_diag _ (fun α => 1 + ∑ x ∈ X, (α x : ℝ)) (refOp_basis X) hc)

theorem refOp_isClosable (X : Finset L) : (polyOp (refOp X)).IsClosable :=
  polyOp_isClosable _

end InfiniteBosons
