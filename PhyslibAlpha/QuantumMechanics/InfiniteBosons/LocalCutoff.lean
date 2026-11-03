/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.TruncationLimit
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


/-!

## C. Local leakage of hopping and pairing

-/

section Leakage

variable {B : Type*} [DecidableEq B]

lemma diagLin_apply (c : B → ℝ) (g : B →₀ ℂ) (γ : B) :
    diagLin c g γ = ((c γ : ℝ) : ℂ) * g γ := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, Finsupp.add_apply, Finsupp.add_apply, hf, hg, mul_add]
  | single a z =>
    rw [diagLin_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · ring

lemma matEl_diagAdj_mul (c : B → ℝ) (P : Adjointable B) (α β : B) :
    matEl (diagAdj c * P) α β = (c α : ℂ) * matEl P α β := by
  unfold matEl
  show diagLin c (P.1.1 (single β 1)) α = _
  rw [diagLin_apply]

lemma matEl_mul_diagAdj (c : B → ℝ) (P : Adjointable B) (α β : B) :
    matEl (P * diagAdj c) α β = matEl P α β * (c β : ℂ) := by
  unfold matEl
  show P.1.1 (diagLin c (single β 1)) α = _
  rw [diagLin_single, mul_one, show (single β ((c β : ℝ) : ℂ) : B →₀ ℂ) =
    ((c β : ℝ) : ℂ) • single β 1 by simp [Finsupp.smul_single], map_smul, Finsupp.smul_apply,
    smul_eq_mul, mul_comm]

/-- Two formally adjointable operators with the same matrix elements are equal. -/
lemma adjointable_ext_matEl {P Q : Adjointable B} (h : ∀ α β, matEl P α β = matEl Q α β) :
    P = Q := by
  refine adjointable_ext (Finsupp.lhom_ext fun β z => ?_)
  rw [show (single β z : B →₀ ℂ) = z • single β 1 by simp [Finsupp.smul_single], map_smul,
    map_smul]
  exact congrArg _ (Finsupp.ext fun α => h α β)

end Leakage

/-- The complement `1 - P_{Y,n}` of the cutoff on finite vectors. -/
def cutComplAdj (Y : Finset L) (n : ℕ) : adjointable L :=
  diagAdj (fun α => 1 - cutWeight Y n α)

/-- **The leakage** `P_{Y,n}^⊥ T P_{Y,n}` of an operator out of the range of the cutoff. -/
def leakOp (Y : Finset L) (n : ℕ) (T : adjointable L) : adjointable L :=
  cutComplAdj Y n * T * cutAdj Y n

lemma matEl_leakOp (Y : Finset L) (n : ℕ) (T : adjointable L) (α β : Occ L) :
    matEl (leakOp Y n T) α β =
      ((1 - cutWeight Y n α : ℝ) : ℂ) * matEl T α β * ((cutWeight Y n β : ℝ) : ℂ) := by
  rw [leakOp, cutComplAdj, cutAdj, matEl_mul_diagAdj, matEl_diagAdj_mul]

/-- An operator whose matrix elements never change the occupations in `Y` does not leak. -/
lemma leakOp_eq_zero (Y : Finset L) (n : ℕ) (T : adjointable L)
    (hT : ∀ α β, matEl T α β ≠ 0 → ∀ z ∈ Y, α z = β z) : leakOp Y n T = 0 := by
  refine adjointable_ext_matEl fun α β => ?_
  rw [matEl_leakOp, show matEl (0 : adjointable L) α β = 0 from rfl]
  by_cases h : matEl T α β = 0
  · rw [h]; ring
  · rw [cutWeight_congr Y n (hT α β h)]
    rcases cutWeight_mem Y n β with hb | hb <;> simp [hb]

lemma leakOp_add (Y : Finset L) (n : ℕ) (S T : adjointable L) :
    leakOp Y n (S + T) = leakOp Y n S + leakOp Y n T := by
  unfold leakOp; rw [mul_add, add_mul]

lemma leakOp_sum {ι : Type*} (Y : Finset L) (n : ℕ) (s : Finset ι) (T : ι → adjointable L) :
    leakOp Y n (∑ i ∈ s, T i) = ∑ i ∈ s, leakOp Y n (T i) := by
  unfold leakOp; rw [Finset.mul_sum, Finset.sum_mul]

namespace BoseHubbardData

variable (D : BoseHubbardData L)

/-- A nonzero matrix element of a bond term is one of its four moves. -/
lemma isMove_of_matEl_bondTerm_ne {x y : L} {α β : Occ L} (h : matEl (D.bondTerm x y) α β ≠ 0) :
    ∃ amp : ℝ, IsMove x y α β amp := by
  rw [matEl_bondTerm] at h
  split_ifs at h with hadj
  · have hxy : x ≠ y := hadj.ne
    by_cases h1 : cre x (ann y (single β (1 : ℂ))) α = 0
    · by_cases h2 : cre y (ann x (single β (1 : ℂ))) α = 0
      · by_cases h3 : cre x (cre y (single β (1 : ℂ))) α = 0
        · have h4 : ann y (ann x (single β (1 : ℂ))) α ≠ 0 := by
            intro h4; apply h; simp [h1, h2, h3, h4]
          exact ⟨_, (isMove_ann_ann hxy h4).2⟩
        · exact ⟨_, (isMove_cre_cre hxy h3).2⟩
      · exact ⟨_, (isMove_cre_ann hxy.symm h2).2.symm⟩
    · exact ⟨_, (isMove_cre_ann hxy h1).2⟩
  · exact absurd rfl h

/-- A bond term changes the occupations at its two endpoints only. -/
lemma matEl_bondTerm_out {x y : L} {α β : Occ L} (h : matEl (D.bondTerm x y) α β ≠ 0) :
    ∀ z, z ≠ x → z ≠ y → α z = β z := fun z hzx hzy => by
  obtain ⟨_, hm⟩ := D.isMove_of_matEl_bondTerm_ne h
  exact (hm.out z hzx hzy).symm

/-- A bond term changes every occupation by at most one. -/
lemma matEl_bondTerm_step {x y : L} {α β : Occ L} (h : matEl (D.bondTerm x y) α β ≠ 0) (z : L) :
    α z ≤ β z + 1 ∧ β z ≤ α z + 1 := by
  obtain ⟨_, hm⟩ := D.isMove_of_matEl_bondTerm_ne h
  by_cases hzx : z = x
  · subst hzx; exact ⟨hm.step_x.2, hm.step_x.1⟩
  by_cases hzy : z = y
  · subst hzy; exact ⟨hm.step_y.2, hm.step_y.1⟩
  rw [hm.out z hzx hzy]; omega

/-- **Bonds away from `Y` do not leak.** -/
lemma leakOp_bondTerm_eq_zero (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∉ Y) (hy : y ∉ Y) :
    leakOp Y n (D.bondTerm x y) = 0 :=
  leakOp_eq_zero Y n _ fun _ _ h z hz =>
    D.matEl_bondTerm_out h z (fun e => hx (e ▸ hz)) fun e => hy (e ▸ hz)

/-- **The leakage of the finite-volume Hamiltonian comes from the bonds touching `Y`**, split into
the bonds inside `Y` and the bonds crossing its boundary. The on-site potential does not leak. -/
lemma leakOp_finiteHam (V : L → ℕ → ℝ) (Λ Y : Finset L) (n : ℕ) :
    leakOp Y n (D.finiteHam V Λ) =
      ∑ q ∈ (Λ ×ˢ Λ).filter (fun q => q.1 ∈ Y ∧ q.2 ∈ Y), leakOp Y n (D.bondTerm q.1 q.2) +
        ∑ q ∈ (Λ ×ˢ Λ).filter (fun q => (q.1 ∈ Y ∧ q.2 ∉ Y) ∨ (q.1 ∉ Y ∧ q.2 ∈ Y)),
          leakOp Y n (D.bondTerm q.1 q.2) := by
  rw [finiteHam, leakOp_add, leakOp_eq_zero Y n _ fun α β h z _ => by
      rw [matEl_diagAdj] at h; split_ifs at h with hb
      · rw [hb]
      · exact absurd rfl h, zero_add, leakOp_sum,
    ← Finset.sum_filter_add_sum_filter_not (Λ ×ˢ Λ) (fun q => q.1 ∈ Y ∧ q.2 ∈ Y)]
  congr 1
  refine (Finset.sum_subset (fun q hq => ?_) fun q hq hq' => ?_).symm
  · obtain ⟨hΛ, hc⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hΛ, by tauto⟩
  · obtain ⟨hΛ, hni⟩ := Finset.mem_filter.mp hq
    have hnc : ¬((q.1 ∈ Y ∧ q.2 ∉ Y) ∨ (q.1 ∉ Y ∧ q.2 ∈ Y)) :=
      fun h => hq' (Finset.mem_filter.mpr ⟨hΛ, h⟩)
    exact D.leakOp_bondTerm_eq_zero Y n (by tauto) (by tauto)

/-- **Leaking moves raise an occupation in `Y` from `n` to `n + 1`.** -/
lemma exists_raise_of_leakOp_ne (Y : Finset L) (n : ℕ) {x y : L} {α β : Occ L}
    (h : matEl (leakOp Y n (D.bondTerm x y)) α β ≠ 0) :
    (∀ z ∈ Y, β z ≤ n) ∧ ∃ z ∈ Y, (z = x ∨ z = y) ∧ α z = n + 1 ∧ β z = n := by
  rw [matEl_leakOp] at h
  have hb : cutWeight Y n β = 1 := by
    rcases cutWeight_mem Y n β with hb | hb
    · exact absurd (by rw [hb]; simp) h
    · exact hb
  have ha : cutWeight Y n α = 0 := by
    rcases cutWeight_mem Y n α with ha | ha
    · exact ha
    · exact absurd (by rw [ha]; simp) h
  have hT : matEl (D.bondTerm x y) α β ≠ 0 := fun h0 => h (by rw [h0]; ring)
  have hβY : ∀ z ∈ Y, β z ≤ n := by
    unfold cutWeight at hb; split_ifs at hb with hc; exacts [hc, absurd hb (by norm_num)]
  obtain ⟨z, hz, hαz⟩ : ∃ z ∈ Y, n < α z := by
    unfold cutWeight at ha; split_ifs at ha with hc
    · exact absurd ha (by norm_num)
    · push Not at hc; exact hc
  have hstep := D.matEl_bondTerm_step hT z
  refine ⟨hβY, z, hz, ?_, by have := hβY z hz; omega, by have := hβY z hz; omega⟩
  by_contra hzxy
  push Not at hzxy
  have := D.matEl_bondTerm_out hT z hzxy.1 hzxy.2
  have := hβY z hz
  omega

end BoseHubbardData


/-!

## D. The pairing term across the boundary of `Y`

-/

section Orthogonal

variable {B : Type*} [DecidableEq B]

/-- Finite vectors with coefficients on distinct basis states: the square norm is the sum of the
squares of the coefficients. -/
lemma norm_embed_sum_single_sq (s : Finset B) (τ : B → B) (hτ : Function.Injective τ)
    (w : B → ℂ) :
    ‖embed (∑ β ∈ s, single (τ β) (w β))‖ ^ 2 = ∑ β ∈ s, ‖w β‖ ^ 2 := by
  classical
  set v := ∑ β ∈ s, single (τ β) (w β)
  have hv : ∀ β ∈ s, v (τ β) = w β := fun β hβ => by
    simp only [v, Finsupp.finsetSum_apply, Finsupp.single_apply, hτ.eq_iff]
    rw [Finset.sum_eq_single β (fun b _ hb => if_neg hb) (fun h => absurd hβ h), if_pos rfl]
  have hsupp : v.support ⊆ s.image τ := fun γ hγ => by
    by_contra h
    apply Finsupp.mem_support_iff.mp hγ
    simp only [v, Finsupp.finsetSum_apply, Finsupp.single_apply]
    exact Finset.sum_eq_zero fun β hβ => if_neg fun e => h (Finset.mem_image.mpr ⟨β, hβ, e⟩)
  rw [norm_embed_sq_eq_sum, Finset.sum_subset hsupp fun γ _ hγ => by
      rw [Finsupp.notMem_support_iff.mp hγ, norm_zero]; ring,
    Finset.sum_image fun a _ b _ h => hτ h]
  exact Finset.sum_congr rfl fun β hβ => by rw [hv β hβ]

end Orthogonal

/-- The weight of the states that the boundary pairing term pushes out of the cutoff: `β` is in the
cutoff and has exactly `n` bosons at `x`. -/
def edgeWeight (Y : Finset L) (n : ℕ) (x : L) (β : Occ L) : ℝ :=
  if (∀ z ∈ Y, β z ≤ n) ∧ β x = n then 1 else 0

omit [DecidableEq L] in
lemma edgeWeight_mem (Y : Finset L) (n : ℕ) (x : L) (β : Occ L) :
    edgeWeight Y n x β = 0 ∨ edgeWeight Y n x β = 1 := by
  unfold edgeWeight; split_ifs <;> simp

/-- The cutoff weight of `β + e_y + e_x` when `x ∈ Y` and `y ∉ Y`. -/
lemma cutWeight_mul_one_sub_add_pair (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∈ Y) (hy : y ∉ Y)
    (β : Occ L) :
    (1 - cutWeight Y n (β + single y 1 + single x 1)) * cutWeight Y n β = edgeWeight Y n x β := by
  have hcoord : ∀ z ∈ Y, (β + single y 1 + single x 1 : Occ L) z = β z + if x = z then 1 else 0 :=
    fun z hz => by simp [Finsupp.single_apply, show y ≠ z from fun e => hy (e ▸ hz)]
  unfold cutWeight edgeWeight
  by_cases hβY : ∀ z ∈ Y, β z ≤ n
  · rw [if_pos hβY, mul_one]
    by_cases hbx : β x = n
    · rw [if_neg, if_pos ⟨hβY, hbx⟩]
      · norm_num
      · intro h; have := h x hx; rw [hcoord x hx, if_pos rfl] at this; omega
    · rw [if_pos, if_neg (fun h => hbx h.2)]
      · norm_num
      · intro z hz
        rw [hcoord z hz]
        have := hβY z hz
        split_ifs with hzx
        · subst hzx; omega
        · omega
  · rw [if_neg hβY, if_neg (show ¬((∀ z ∈ Y, β z ≤ n) ∧ β x = n) from fun h => hβY h.1),
      mul_zero]

/-- **The boundary pairing leakage on basis states.** For `x ∈ Y` and `y ∉ Y`,
`P_{Y,n}^⊥ a_x† a_y† P_{Y,n} e_β = 1_{β ∈ P_{Y,n}, β_x = n} √(β_x+1) √(β_y+1) e_{β + e_x + e_y}`.
On the support of the indicator `β_x = n`, while `β_y` is arbitrary: the occupation at `y ∉ Y` is
not restricted and the operator is unbounded. -/
lemma leakOp_pair_single (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∈ Y) (hy : y ∉ Y)
    (β : Occ L) :
    (leakOp Y n (creOp x * creOp y)).1.1 (single β 1) = single (β + single y 1 + single x 1)
      (((edgeWeight Y n x β : ℝ) : ℂ) * (((Real.sqrt ((β x : ℝ) + 1) : ℝ) : ℂ) *
        ((Real.sqrt ((β y : ℝ) + 1) : ℝ) : ℂ))) := by
  have hxy : x ≠ y := fun e => hy (e ▸ hx)
  have hbx : (β + single y 1 : Occ L) x = β x := by simp [hxy.symm]
  show diagLin _ (cre x (cre y (diagLin (cutWeight Y n) (single β 1)))) = _
  rw [diagLin_single, mul_one, show (single β ((cutWeight Y n β : ℝ) : ℂ) : Occ L →₀ ℂ) =
      ((cutWeight Y n β : ℝ) : ℂ) • single β 1 by simp [Finsupp.smul_single], map_smul,
    map_smul, cre_single, cre_single, map_smul, diagLin_single, Finsupp.smul_single, smul_eq_mul,
    hbx, ← cutWeight_mul_one_sub_add_pair Y n hx hy β]
  congr 1
  push_cast
  ring


/-- The boundary pairing leakage of a finite vector as a sum over distinct target states. -/
lemma leakOp_pair_apply (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∈ Y) (hy : y ∉ Y)
    (f : Occ L →₀ ℂ) :
    (leakOp Y n (creOp x * creOp y)).1.1 f = ∑ β ∈ f.support, single (β + single y 1 + single x 1)
      (f β * (((edgeWeight Y n x β : ℝ) : ℂ) * (((Real.sqrt ((β x : ℝ) + 1) : ℝ) : ℂ) *
        ((Real.sqrt ((β y : ℝ) + 1) : ℝ) : ℂ)))) := by
  conv_lhs => rw [← Finsupp.sum_single f]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [show (single β (f β) : Occ L →₀ ℂ) = f β • single β 1 by simp [Finsupp.smul_single],
    map_smul, leakOp_pair_single Y n hx hy, Finsupp.smul_single, smul_eq_mul]

/-- **The size of the boundary pairing leakage.** For `x ∈ Y`, `y ∉ Y` and a finite vector `f`,
`‖P_{Y,n}^⊥ a_x† a_y† P_{Y,n} f‖² = Σ_β 1_{β ∈ P_{Y,n}, β_x = n} (β_x + 1)(β_y + 1) |f_β|²`. The
weight `β_y + 1` is not bounded. -/
lemma norm_leakOp_pair_sq (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∈ Y) (hy : y ∉ Y)
    (f : Occ L →₀ ℂ) :
    ‖embed ((leakOp Y n (creOp x * creOp y)).1.1 f)‖ ^ 2 = ∑ β ∈ f.support,
      edgeWeight Y n x β * (((β x : ℝ) + 1) * ((β y : ℝ) + 1)) * ‖f β‖ ^ 2 := by
  rw [leakOp_pair_apply Y n hx hy, norm_embed_sum_single_sq _ _
    (fun a b h => add_right_cancel (add_right_cancel h))]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, mul_pow, sq_abs, Real.sq_sqrt
    (by positivity), Real.sq_sqrt (by positivity)]
  rcases edgeWeight_mem Y n x β with h | h <;> rw [h] <;> ring

omit [DecidableEq L] in
/-- On the support of the edge weight, `β_x = n`, so a local moment at `x` controls it. -/
lemma edgeWeight_mul_le (Y : Finset L) (n k : ℕ) (x : L) (β : Occ L) :
    edgeWeight Y n x β * ((β x : ℝ) + 1) ≤
      ((n : ℝ) + 1) * (((β x : ℝ) + 1) / ((n : ℝ) + 1)) ^ k := by
  unfold edgeWeight
  split_ifs with h
  · rw [one_mul, h.2, div_self (by positivity), one_pow, mul_one]
  · rw [zero_mul]; positivity

/-- **Weighted estimate for the boundary pairing leakage.** For `x ∈ Y`, `y ∉ Y` and a finite
vector `f` with local moments `Σ_β (β_x + 1)^{2k} |f_β|² ≤ M_x` at `x` and
`Σ_β (β_y + 1)² |f_β|² ≤ M_y` at `y`,
`‖P_{Y,n}^⊥ a_x† a_y† P_{Y,n} f‖² ≤ (n + 1)^{1-k} (M_x + M_y) / 2`.
The operator is unbounded, but on states with moments of order `2k ≥ 4` at `x` and of order `2` at
`y` its contribution decays in the cutoff level `n`. -/
lemma norm_leakOp_pair_sq_le (Y : Finset L) (n k : ℕ) {x y : L} (hx : x ∈ Y) (hy : y ∉ Y)
    (f : Occ L →₀ ℂ) {Mx My : ℝ}
    (hMx : ∑ β ∈ f.support, ((β x : ℝ) + 1) ^ (2 * k) * ‖f β‖ ^ 2 ≤ Mx)
    (hMy : ∑ β ∈ f.support, ((β y : ℝ) + 1) ^ 2 * ‖f β‖ ^ 2 ≤ My) :
    ‖embed ((leakOp Y n (creOp x * creOp y)).1.1 f)‖ ^ 2 ≤
      ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ k * ((Mx + My) / 2) := by
  have hn : (0 : ℝ) < ((n : ℝ) + 1) ^ k := by positivity
  rw [norm_leakOp_pair_sq Y n hx hy]
  have hpt : ∀ β ∈ f.support, edgeWeight Y n x β * (((β x : ℝ) + 1) * ((β y : ℝ) + 1)) *
      ‖f β‖ ^ 2 ≤ ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ k *
        ((((β x : ℝ) + 1) ^ (2 * k) * ‖f β‖ ^ 2 + ((β y : ℝ) + 1) ^ 2 * ‖f β‖ ^ 2) / 2) := by
    intro β _
    have h1 := edgeWeight_mul_le Y n k x β
    have hamgm : ((β x : ℝ) + 1) ^ k * ((β y : ℝ) + 1) ≤
        (((β x : ℝ) + 1) ^ (2 * k) + ((β y : ℝ) + 1) ^ 2) / 2 := by
      rw [pow_mul']
      nlinarith [sq_nonneg (((β x : ℝ) + 1) ^ k - ((β y : ℝ) + 1))]
    have hy0 : (0 : ℝ) ≤ ((β y : ℝ) + 1) * ‖f β‖ ^ 2 := by positivity
    calc edgeWeight Y n x β * (((β x : ℝ) + 1) * ((β y : ℝ) + 1)) * ‖f β‖ ^ 2
        = (edgeWeight Y n x β * ((β x : ℝ) + 1)) * (((β y : ℝ) + 1) * ‖f β‖ ^ 2) := by ring
      _ ≤ (((n : ℝ) + 1) * (((β x : ℝ) + 1) / ((n : ℝ) + 1)) ^ k) *
          (((β y : ℝ) + 1) * ‖f β‖ ^ 2) := mul_le_mul_of_nonneg_right h1 hy0
      _ = ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ k * ((((β x : ℝ) + 1) ^ k * ((β y : ℝ) + 1)) *
          ‖f β‖ ^ 2) := by rw [div_pow]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖f β‖]) (by positivity)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  linarith

end InfiniteBosons
