/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.LocalMoments
/-!

# Localized occupation cutoffs

The projection onto the states with at most `n` bosons at every site of a finite region `Y`, with
no condition outside `Y`, and its interaction with hopping and pairing.

## i. Overview

For a finite region `Y` the cutoff `P_{Y,n} = Π_{x∈Y} 1_{N_x ≤ n}` is diagonal in the occupation
basis. It restricts the occupations in `Y` only, so it is not the truncation of the finite-volume
comparison, which imposes the vacuum outside the region. This is the localized cutoff of
Deuchert-Lampart-Lemm, eq. (58). Its tail in a state with uniform local moments is controlled by
`|Y|` and the moment bound, independently of the ambient volume. A hopping or pairing term on a
bond `x ~ y` changes only the occupations at `x` and `y`, so it commutes with `P_{Y,n}` unless the
bond touches `Y`. A term leaving the range of the cutoff raises an occupation in `Y` from `n` to
`n + 1`. For a pairing bond with `x ∈ Y` and `y ∉ Y` the leakage `P_{Y,n}^⊥ a_x† a_y† P_{Y,n}` is
unbounded, since the occupation at `y` is not restricted; its size is a weighted sum involving the
occupation at `y`, controlled by local moments at both sites.

## ii. Key results

- `InfiniteBosons.cutAdj`, `InfiniteBosons.cutOp`: the cutoff on finite vectors and on `ℓ²`.
- `InfiniteBosons.cutOp_mul_self`, `InfiniteBosons.isSelfAdjoint_cutOp`: an orthogonal projection.
- `InfiniteBosons.cutAdj_mul_diagAdj`: the cutoff commutes with occupation-diagonal operators.

## iii. Table of contents

- A. The localized cutoff

## iv. References

* A. Deuchert, J. Lampart, M. Lemm, Dynamics and equilibrium states of infinite systems of lattice
  bosons, arXiv:2505.13170, Section 4.1, eqs. (58)-(68).
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-!

## A. The localized cutoff

-/

/-- The indicator of the states with at most `n` bosons at every site of `Y`. -/
def cutWeight (Y : Finset L) (n : ℕ) (α : Occ L) : ℝ := if ∀ x ∈ Y, α x ≤ n then 1 else 0

omit [DecidableEq L] in
lemma cutWeight_mul_self (Y : Finset L) (n : ℕ) (α : Occ L) :
    cutWeight Y n α * cutWeight Y n α = cutWeight Y n α := by
  unfold cutWeight; split_ifs <;> norm_num

omit [DecidableEq L] in
lemma cutWeight_mem (Y : Finset L) (n : ℕ) (α : Occ L) :
    cutWeight Y n α = 0 ∨ cutWeight Y n α = 1 := by
  unfold cutWeight; split_ifs <;> simp

omit [DecidableEq L] in
/-- The cutoff depends only on the occupations in `Y`. -/
lemma cutWeight_congr (Y : Finset L) (n : ℕ) {α β : Occ L} (h : ∀ x ∈ Y, α x = β x) :
    cutWeight Y n α = cutWeight Y n β := by
  unfold cutWeight
  congr 1
  exact propext ⟨fun hα x hx => h x hx ▸ hα x hx, fun hβ x hx => (h x hx).symm ▸ hβ x hx⟩

/-- **The localized cutoff on finite vectors.** -/
def cutAdj (Y : Finset L) (n : ℕ) : adjointable L := diagAdj (cutWeight Y n)

lemma cutAdj_single (Y : Finset L) (n : ℕ) (α : Occ L) :
    (cutAdj Y n).1.1 (single α 1) = single α ((cutWeight Y n α : ℝ) : ℂ) :=
  diagAdj_single _ α

lemma star_cutAdj (Y : Finset L) (n : ℕ) : star (cutAdj Y n) = cutAdj Y n := star_diagAdj _

section Diagonal

variable {B : Type*} [DecidableEq B]

/-- Diagonal operators multiply entrywise. -/
lemma diagAdj_mul (c d : B → ℝ) : diagAdj c * diagAdj d = diagAdj (c * d) := by
  refine adjointable_ext (Finsupp.lhom_ext fun α z => ?_)
  show diagLin c (diagLin d (single α z)) = diagLin (c * d) (single α z)
  rw [diagLin_single, diagLin_single, diagLin_single]
  congr 1
  push_cast [Pi.mul_apply]; ring

/-- Diagonal operators commute. -/
lemma diagAdj_commute (c d : B → ℝ) : diagAdj c * diagAdj d = diagAdj d * diagAdj c := by
  rw [diagAdj_mul, diagAdj_mul, mul_comm c]

end Diagonal

/-- **The cutoff commutes with every occupation-diagonal operator**, in particular with an
arbitrary on-site potential `D(N)`. -/
lemma cutAdj_mul_diagAdj (Y : Finset L) (n : ℕ) (c : Occ L → ℝ) :
    cutAdj Y n * diagAdj c = diagAdj c * cutAdj Y n := diagAdj_commute _ _

/-- **The cutoff is idempotent.** -/
lemma cutAdj_mul_self (Y : Finset L) (n : ℕ) : cutAdj Y n * cutAdj Y n = cutAdj Y n := by
  unfold cutAdj
  rw [diagAdj_mul]
  congr 1
  funext α
  exact cutWeight_mul_self Y n α

omit [DecidableEq L] in
lemma norm_cutWeight_le (Y : Finset L) (n : ℕ) (α : Occ L) :
    ‖((cutWeight Y n α : ℝ) : ℂ)‖ ≤ 1 := by
  rcases cutWeight_mem Y n α with h | h <;> simp [h]

omit [DecidableEq L] in
/-- **The localized cutoff as a bounded operator on `ℓ²`.** -/
def cutOp (Y : Finset L) (n : ℕ) : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L) :=
  diagOp (norm_cutWeight_le Y n)

omit [DecidableEq L] in
lemma cutOp_apply (Y : Finset L) (n : ℕ) (ψ : HilbertSp (Occ L)) (α : Occ L) :
    (cutOp Y n ψ : HilbertSp (Occ L)) α = ((cutWeight Y n α : ℝ) : ℂ) * ψ α := rfl

/-- The bounded cutoff extends the cutoff on finite vectors. -/
lemma cutOp_embed (Y : Finset L) (n : ℕ) (f : Occ L →₀ ℂ) :
    cutOp Y n (embed f) = embed ((cutAdj Y n).1.1 f) := by
  refine Subtype.ext (funext fun α => ?_)
  rw [cutOp_apply, embed_apply, embed_apply]
  show _ = diagLin (cutWeight Y n) f α
  simp only [diagLin, Finsupp.lsum_apply, Finsupp.sum, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single α (fun b _ hb => by rw [if_neg hb, mul_zero])
    (fun h => by rw [Finsupp.notMem_support_iff.mp h]; simp)]
  simp

omit [DecidableEq L] in
/-- **The cutoff is an orthogonal projection: idempotent ...** -/
lemma cutOp_mul_self (Y : Finset L) (n : ℕ) : cutOp Y n * cutOp Y n = cutOp Y n := by
  refine ContinuousLinearMap.ext fun ψ => Subtype.ext (funext fun α => ?_)
  show ((cutWeight Y n α : ℝ) : ℂ) * (((cutWeight Y n α : ℝ) : ℂ) * ψ α) =
    ((cutWeight Y n α : ℝ) : ℂ) * ψ α
  rw [← mul_assoc, ← Complex.ofReal_mul, cutWeight_mul_self]

omit [DecidableEq L] in
/-- **... and self-adjoint.** -/
lemma isSelfAdjoint_cutOp (Y : Finset L) (n : ℕ) : IsSelfAdjoint (cutOp Y n) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, cutOp,
    diagOp_adjoint _ (fun α => by rw [Complex.conj_ofReal]; exact norm_cutWeight_le Y n α)]
  congr 1
  funext α
  exact Complex.conj_ofReal _


/-!

## B. The tail of the cutoff

-/

omit [DecidableEq L] in
/-- **Pointwise Markov bound.** `1 - P_{Y,n} ≤ Σ_{x∈Y} ((N_x + 1) / (n + 1))^k` on basis states. -/
lemma one_sub_cutWeight_le (Y : Finset L) (n k : ℕ) (α : Occ L) :
    1 - cutWeight Y n α ≤ ∑ x ∈ Y, (((α x : ℝ) + 1) / ((n : ℝ) + 1)) ^ k := by
  unfold cutWeight
  split_ifs with h
  · simp only [sub_self]; positivity
  · push Not at h
    obtain ⟨x, hx, hlt⟩ := h
    have h1 : (1 : ℝ) ≤ ((α x : ℝ) + 1) / ((n : ℝ) + 1) := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact_mod_cast (show n + 1 ≤ α x + 1 by omega)
    have h2 : (1 : ℝ) ≤ (((α x : ℝ) + 1) / ((n : ℝ) + 1)) ^ k := one_le_pow₀ h1
    have h3 := Finset.single_le_sum (f := fun x => (((α x : ℝ) + 1) / ((n : ℝ) + 1)) ^ k)
      (fun _ _ => by positivity) hx
    simp only [sub_zero]
    linarith

omit [DecidableEq L] in
/-- **The tail of the localized cutoff is controlled by local moments in `Y` only.** Let `q ≥ 0` be
a weight on basis states, for instance the diagonal `q(α) = ⟨α|ρ|α⟩` of a density matrix, whose
local moments `Σ_α q(α) (α_x + 1)^k` are at most `M` at every site of `Y`. Then the weight of the
complement of `P_{Y,n}` is at most `|Y| M / (n + 1)^k`. Nothing depends on the occupations outside
`Y` or on the ambient volume. -/
lemma tsum_tail_le (Y : Finset L) (n k : ℕ) (q : Occ L → ℝ) (hq : ∀ α, 0 ≤ q α) {M : ℝ}
    (hsum : ∀ x ∈ Y, Summable fun α => q α * ((α x : ℝ) + 1) ^ k)
    (hM : ∀ x ∈ Y, ∑' α, q α * ((α x : ℝ) + 1) ^ k ≤ M) :
    Summable (fun α => q α * (1 - cutWeight Y n α)) ∧
      ∑' α, q α * (1 - cutWeight Y n α) ≤ Y.card * M / ((n : ℝ) + 1) ^ k := by
  have hn : (0 : ℝ) < ((n : ℝ) + 1) ^ k := by positivity
  set g : Occ L → ℝ := fun α => ∑ x ∈ Y, q α * ((α x : ℝ) + 1) ^ k / ((n : ℝ) + 1) ^ k
  have hle : ∀ α, q α * (1 - cutWeight Y n α) ≤ g α := fun α => by
    have := mul_le_mul_of_nonneg_left (one_sub_cutWeight_le Y n k α) (hq α)
    refine this.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [div_pow]; ring
  have hnn : ∀ α, 0 ≤ q α * (1 - cutWeight Y n α) := fun α =>
    mul_nonneg (hq α) (by rcases cutWeight_mem Y n α with h | h <;> simp [h])
  have hg : Summable g := summable_sum fun x hx => (hsum x hx).div_const _
  refine ⟨hg.of_nonneg_of_le hnn hle, ?_⟩
  calc ∑' α, q α * (1 - cutWeight Y n α) ≤ ∑' α, g α :=
        (hg.of_nonneg_of_le hnn hle).tsum_le_tsum hle hg
    _ = ∑ x ∈ Y, (∑' α, q α * ((α x : ℝ) + 1) ^ k) / ((n : ℝ) + 1) ^ k := by
        rw [Summable.tsum_finsetSum fun x hx => (hsum x hx).div_const _]
        exact Finset.sum_congr rfl fun x _ => tsum_div_const
    _ ≤ ∑ x ∈ Y, M / ((n : ℝ) + 1) ^ k :=
        Finset.sum_le_sum fun x hx => div_le_div_of_nonneg_right (hM x hx) hn.le
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_div_assoc]

omit [DecidableEq L] in
/-- **The tail in a vector state.** `‖(1 - P_{Y,n}) ψ‖² ≤ |Y| M / (n + 1)^k` if the local moments
`Σ_α (α_x + 1)^k |ψ_α|²` at the sites of `Y` are at most `M`. -/
lemma norm_sub_cutOp_sq_le (Y : Finset L) (n k : ℕ) (ψ : HilbertSp (Occ L)) {M : ℝ}
    (hsum : ∀ x ∈ Y, Summable fun α => ‖(ψ : HilbertSp (Occ L)) α‖ ^ 2 * ((α x : ℝ) + 1) ^ k)
    (hM : ∀ x ∈ Y, ∑' α, ‖(ψ : HilbertSp (Occ L)) α‖ ^ 2 * ((α x : ℝ) + 1) ^ k ≤ M) :
    ‖ψ - cutOp Y n ψ‖ ^ 2 ≤ Y.card * M / ((n : ℝ) + 1) ^ k := by
  have hcoord : ∀ α, ‖((ψ - cutOp Y n ψ : HilbertSp (Occ L)) α)‖ ^ 2 =
      ‖(ψ : HilbertSp (Occ L)) α‖ ^ 2 * (1 - cutWeight Y n α) := fun α => by
    rw [lp.coeFn_sub, Pi.sub_apply, cutOp_apply]
    rcases cutWeight_mem Y n α with h | h <;> simp [h]
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (ψ - cutOp Y n ψ)
  have e2 : (2 : ENNReal).toReal = 2 := by norm_num
  simp only [e2, Real.rpow_two] at h
  rw [h, tsum_congr hcoord]
  exact (tsum_tail_le Y n k _ (fun _ => by positivity) hsum hM).2

end InfiniteBosons
