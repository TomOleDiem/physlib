/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.TruncationLimit
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.Pairing
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
occupation at `y`, controlled by local moments at both sites. The hopping `a_x† a_y` into `Y` has
the same structure, with amplitude `√(β_x + 1) √β_y`; hopping out of `Y` and pair annihilation do
not leak. The tail estimate holds for positive trace-class density matrices, whose moments enter
through the diagonal `⟨α|ρ|α⟩`. The compressed Hamiltonian `P H_Λ P` is dominated entrywise by
`H_Λ`, hence essentially self-adjoint for every on-site potential. For the Duhamel comparison the
reverse leakage `P H_Λ P^⊥` matters too: across the boundary it is pair annihilation and hopping out
of `Y` from states with `n + 1` bosons at the inner site, with the same weighted estimate.

## ii. Key results

- `InfiniteBosons.cutAdj`, `InfiniteBosons.cutOp`: the cutoff on finite vectors and on `ℓ²`.
- `InfiniteBosons.cutOp_mul_self`, `InfiniteBosons.isSelfAdjoint_cutOp`: an orthogonal projection.
- `InfiniteBosons.cutAdj_mul_diagAdj`: the cutoff commutes with occupation-diagonal operators.
- `InfiniteBosons.tsum_tail_le`, `InfiniteBosons.norm_sub_cutOp_sq_le`: the tail of the cutoff is
  at most `|Y| M / (n + 1)^k`, independently of the ambient volume.
- `InfiniteBosons.BoseHubbardData.leakOp_finiteHam`: only bonds touching `Y` leak, split into bonds
  inside `Y` and bonds crossing its boundary.
- `InfiniteBosons.BoseHubbardData.exists_raise_of_leakOp_ne`: leaking moves raise an occupation in
  `Y` from `n` to `n + 1`.
- `InfiniteBosons.leakOp_pair_single`, `InfiniteBosons.norm_leakOp_pair_sq_le`: the unbounded
  boundary pairing leakage, exactly and with a weighted estimate.
- `InfiniteBosons.leakOp_hop_single`, `InfiniteBosons.norm_leakOp_hop_sq_le`: the hopping leakage
  into `Y`, exactly and with the same weighted estimate.
- `InfiniteBosons.BoseHubbardData.leakOp_bondTerm_boundary`,
  `InfiniteBosons.BoseHubbardData.leakOp_bondTerm_inside`: the leakage of a bond term as a sum of
  the hopping and pairing leakages.
- `InfiniteBosons.BoseHubbardData.cutHam_isEssentiallySelfAdjoint`: the compressed Hamiltonian
  `P_{Y,n} H_Λ P_{Y,n}` is essentially self-adjoint.
- `InfiniteBosons.norm_revLeakOp_pair_sq_le`, `InfiniteBosons.norm_revLeakOp_hop_sq_le`: weighted
  estimates for the reverse leakage `P_{Y,n} H_Λ P_{Y,n}^⊥` across the boundary.
- `InfiniteBosons.trace_tail_le`: the tail `Tr ρ (1 - P_{Y,n}) ≤ |Y| M / (n + 1)^k` for a density
  matrix.

## iii. Table of contents

- A. The localized cutoff
- B. The tail of the cutoff
- C. Local leakage of hopping and pairing
- D. The pairing term across the boundary of `Y`
- E. The hopping term into `Y`
- F. The leakage of a bond term
- G. The tail in a density matrix
- H. The compressed Hamiltonian
- I. The reverse leakage across the boundary of `Y`

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
lemma norm_embed_sum_single_sq (s : Finset B) (τ : B → B) (hτ : Set.InjOn τ s)
    (w : B → ℂ) :
    ‖embed (∑ β ∈ s, single (τ β) (w β))‖ ^ 2 = ∑ β ∈ s, ‖w β‖ ^ 2 := by
  classical
  set v := ∑ β ∈ s, single (τ β) (w β)
  have hv : ∀ β ∈ s, v (τ β) = w β := fun β hβ => by
    simp only [v, Finsupp.finsetSum_apply, Finsupp.single_apply]
    rw [Finset.sum_eq_single β (fun b hb hne => if_neg fun e => hne (hτ hb hβ e))
      (fun h => absurd hβ h), if_pos rfl]
  have hsupp : v.support ⊆ s.image τ := fun γ hγ => by
    by_contra h
    apply Finsupp.mem_support_iff.mp hγ
    simp only [v, Finsupp.finsetSum_apply, Finsupp.single_apply]
    exact Finset.sum_eq_zero fun β hβ => if_neg fun e => h (Finset.mem_image.mpr ⟨β, hβ, e⟩)
  rw [norm_embed_sq_eq_sum, Finset.sum_subset hsupp fun γ _ hγ => by
      rw [Finsupp.notMem_support_iff.mp hγ, norm_zero]; ring,
    Finset.sum_image fun a ha b hb h => hτ ha hb h]
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
    (fun a _ b _ h => add_right_cancel (add_right_cancel h))]
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

omit [DecidableEq L] in
/-- The weighted sum that controls the leakage across the boundary. If `w(β) a(β)` is at most
`(n + 1) ((β_x + 1) / (n + 1))^k`, then by the arithmetic-geometric mean inequality
`Σ_β w(β) a(β) (β_y + 1) |f_β|² ≤ (n + 1)^{1-k} (M_x + M_y) / 2`. -/
lemma sum_weight_mul_le (n k : ℕ) (x y : L) (s : Finset (Occ L)) (f : Occ L → ℂ)
    (w a : Occ L → ℝ) (hw : ∀ β, w β * a β ≤ ((n : ℝ) + 1) * (((β x : ℝ) + 1) / ((n : ℝ) + 1)) ^ k)
    {Mx My : ℝ} (hMx : ∑ β ∈ s, ((β x : ℝ) + 1) ^ (2 * k) * ‖f β‖ ^ 2 ≤ Mx)
    (hMy : ∑ β ∈ s, ((β y : ℝ) + 1) ^ 2 * ‖f β‖ ^ 2 ≤ My) :
    ∑ β ∈ s, w β * (a β * ((β y : ℝ) + 1)) * ‖f β‖ ^ 2 ≤
      ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ k * ((Mx + My) / 2) := by
  have hpt : ∀ β ∈ s, w β * (a β * ((β y : ℝ) + 1)) * ‖f β‖ ^ 2 ≤
      ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ k *
        ((((β x : ℝ) + 1) ^ (2 * k) * ‖f β‖ ^ 2 + ((β y : ℝ) + 1) ^ 2 * ‖f β‖ ^ 2) / 2) := by
    intro β _
    have hamgm : ((β x : ℝ) + 1) ^ k * ((β y : ℝ) + 1) ≤
        (((β x : ℝ) + 1) ^ (2 * k) + ((β y : ℝ) + 1) ^ 2) / 2 := by
      rw [pow_mul']
      nlinarith [sq_nonneg (((β x : ℝ) + 1) ^ k - ((β y : ℝ) + 1))]
    have hy0 : (0 : ℝ) ≤ ((β y : ℝ) + 1) * ‖f β‖ ^ 2 := by positivity
    calc w β * (a β * ((β y : ℝ) + 1)) * ‖f β‖ ^ 2
        = (w β * a β) * (((β y : ℝ) + 1) * ‖f β‖ ^ 2) := by ring
      _ ≤ (((n : ℝ) + 1) * (((β x : ℝ) + 1) / ((n : ℝ) + 1)) ^ k) *
          (((β y : ℝ) + 1) * ‖f β‖ ^ 2) := mul_le_mul_of_nonneg_right (hw β) hy0
      _ = ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ k * ((((β x : ℝ) + 1) ^ k * ((β y : ℝ) + 1)) *
          ‖f β‖ ^ 2) := by rw [div_pow]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg ‖f β‖]) (by positivity)
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  linarith

omit [DecidableEq L] in
/-- The weighted sum for the edge weight: on its support `β_x = n`. -/
lemma sum_edgeWeight_le (Y : Finset L) (n k : ℕ) (x y : L) (s : Finset (Occ L)) (f : Occ L → ℂ)
    {Mx My : ℝ} (hMx : ∑ β ∈ s, ((β x : ℝ) + 1) ^ (2 * k) * ‖f β‖ ^ 2 ≤ Mx)
    (hMy : ∑ β ∈ s, ((β y : ℝ) + 1) ^ 2 * ‖f β‖ ^ 2 ≤ My) :
    ∑ β ∈ s, edgeWeight Y n x β * (((β x : ℝ) + 1) * ((β y : ℝ) + 1)) * ‖f β‖ ^ 2 ≤
      ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ k * ((Mx + My) / 2) :=
  sum_weight_mul_le n k x y s f _ _ (edgeWeight_mul_le Y n k x) hMx hMy

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
  rw [norm_leakOp_pair_sq Y n hx hy]
  exact sum_edgeWeight_le Y n k x y f.support f hMx hMy


/-!

## E. The hopping term into `Y`

-/

/-- The cutoff weight of `β - e_y + e_x` when `x ∈ Y`, `x ≠ y` and `β_y ≥ 1`. The site `y` may lie
inside or outside `Y`. -/
lemma cutWeight_mul_one_sub_hop (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∈ Y) (hxy : x ≠ y)
    {β : Occ L} (hβ : 1 ≤ β y) :
    (1 - cutWeight Y n (β - single y 1 + single x 1)) * cutWeight Y n β = edgeWeight Y n x β := by
  have hcoord : ∀ z, (β - single y 1 + single x 1 : Occ L) z =
      β z - (if y = z then 1 else 0) + if x = z then 1 else 0 := fun z => by
    simp [Finsupp.single_apply]
  unfold cutWeight edgeWeight
  by_cases hβY : ∀ z ∈ Y, β z ≤ n
  · rw [if_pos hβY, mul_one]
    by_cases hbx : β x = n
    · rw [if_neg, if_pos ⟨hβY, hbx⟩]
      · norm_num
      · intro h; have := h x hx; rw [hcoord x, if_pos rfl, if_neg hxy.symm] at this; omega
    · rw [if_pos, if_neg (fun h => hbx h.2)]
      · norm_num
      · intro z hz
        rw [hcoord z]
        have := hβY z hz
        split_ifs with h1 h2 h2
        · exact absurd (h1.trans h2.symm) hxy.symm
        · omega
        · subst h2; omega
        · omega
  · rw [if_neg hβY, if_neg (show ¬((∀ z ∈ Y, β z ≤ n) ∧ β x = n) from fun h => hβY h.1),
      mul_zero]

/-- **The hopping leakage on basis states.** For `x ∈ Y` and `x ≠ y`,
`P_{Y,n}^⊥ a_x† a_y P_{Y,n} e_β = 1_{β ∈ P_{Y,n}, β_x = n} √(β_x+1) √(β_y) e_{β - e_y + e_x}`.
For `y ∉ Y` the occupation `β_y` is not restricted and the operator is unbounded; for `y ∈ Y` it is
at most `n` on the range of the cutoff. -/
lemma leakOp_hop_single (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∈ Y) (hxy : x ≠ y)
    (β : Occ L) :
    (leakOp Y n (creOp x * annOp y)).1.1 (single β 1) = single (β - single y 1 + single x 1)
      (((edgeWeight Y n x β : ℝ) : ℂ) * (((Real.sqrt ((β x : ℝ) + 1) : ℝ) : ℂ) *
        ((Real.sqrt (β y : ℝ) : ℝ) : ℂ))) := by
  have hbx : (β - single y 1 : Occ L) x = β x := by simp [Finsupp.single_apply, hxy.symm]
  show diagLin _ (cre x (ann y (diagLin (cutWeight Y n) (single β 1)))) = _
  rw [diagLin_single, mul_one, show (single β ((cutWeight Y n β : ℝ) : ℂ) : Occ L →₀ ℂ) =
      ((cutWeight Y n β : ℝ) : ℂ) • single β 1 by simp [Finsupp.smul_single], map_smul,
    map_smul, ann_single, cre_single, map_smul, diagLin_single, Finsupp.smul_single, smul_eq_mul,
    hbx]
  rcases Nat.eq_zero_or_pos (β y) with h0 | hpos
  · simp [h0]
  · rw [← cutWeight_mul_one_sub_hop Y n hx hxy hpos]
    congr 1
    push_cast
    ring

/-- The hopping leakage of a finite vector as a sum over basis states. -/
lemma leakOp_hop_apply (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∈ Y) (hxy : x ≠ y)
    (f : Occ L →₀ ℂ) :
    (leakOp Y n (creOp x * annOp y)).1.1 f = ∑ β ∈ f.support, single (β - single y 1 + single x 1)
      (f β * (((edgeWeight Y n x β : ℝ) : ℂ) * (((Real.sqrt ((β x : ℝ) + 1) : ℝ) : ℂ) *
        ((Real.sqrt (β y : ℝ) : ℝ) : ℂ)))) := by
  conv_lhs => rw [← Finsupp.sum_single f]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [show (single β (f β) : Occ L →₀ ℂ) = f β • single β 1 by simp [Finsupp.smul_single],
    map_smul, leakOp_hop_single Y n hx hxy, Finsupp.smul_single, smul_eq_mul]

/-- The hopping move `β ↦ β - e_y + e_x` is injective on the states with `β_y ≥ 1`. -/
lemma injOn_hop (s : Finset (Occ L)) (x y : L) :
    Set.InjOn (fun β : Occ L => β - single y 1 + single x 1) ↑(s.filter fun β => β y ≠ 0) :=
  fun a ha b hb h => by
    have ha' : single y 1 ≤ a := (single_le_iff' y a).mpr
      (Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp ha).2)
    have hb' : single y 1 ≤ b := (single_le_iff' y b).mpr
      (Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hb).2)
    exact (tsub_left_inj ha' hb').mp (add_right_cancel h)

/-- **The size of the hopping leakage.** For `x ∈ Y`, `x ≠ y` and a finite vector `f`,
`‖P_{Y,n}^⊥ a_x† a_y P_{Y,n} f‖² = Σ_β 1_{β ∈ P_{Y,n}, β_x = n} (β_x + 1) β_y |f_β|²`. -/
lemma norm_leakOp_hop_sq (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∈ Y) (hxy : x ≠ y)
    (f : Occ L →₀ ℂ) :
    ‖embed ((leakOp Y n (creOp x * annOp y)).1.1 f)‖ ^ 2 = ∑ β ∈ f.support,
      edgeWeight Y n x β * (((β x : ℝ) + 1) * (β y : ℝ)) * ‖f β‖ ^ 2 := by
  rw [leakOp_hop_apply Y n hx hxy, ← Finset.sum_filter_of_ne (p := fun β => β y ≠ 0)
      (fun β _ hne h0 => hne (by simp [h0])),
    norm_embed_sum_single_sq _ _ (injOn_hop _ x y), ← Finset.sum_filter_of_ne
      (s := f.support) (p := fun β => β y ≠ 0) (fun β _ hne h0 => hne (by simp [h0]))]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, mul_pow, sq_abs, Real.sq_sqrt
    (by positivity), Real.sq_sqrt (by positivity)]
  rcases edgeWeight_mem Y n x β with h | h <;> rw [h] <;> ring

omit [DecidableEq L] in
lemma edgeWeight_nonneg (Y : Finset L) (n : ℕ) (x : L) (β : Occ L) : 0 ≤ edgeWeight Y n x β := by
  rcases edgeWeight_mem Y n x β with h | h <;> rw [h] <;> norm_num

/-- **Weighted estimate for the hopping leakage.** For `x ∈ Y`, `x ≠ y` and a finite vector `f`
with local moments of order `2k` at `x` and of order `2` at `y`, as for pairing,
`‖P_{Y,n}^⊥ a_x† a_y P_{Y,n} f‖² ≤ (n + 1)^{1-k} (M_x + M_y) / 2`. -/
lemma norm_leakOp_hop_sq_le (Y : Finset L) (n k : ℕ) {x y : L} (hx : x ∈ Y) (hxy : x ≠ y)
    (f : Occ L →₀ ℂ) {Mx My : ℝ}
    (hMx : ∑ β ∈ f.support, ((β x : ℝ) + 1) ^ (2 * k) * ‖f β‖ ^ 2 ≤ Mx)
    (hMy : ∑ β ∈ f.support, ((β y : ℝ) + 1) ^ 2 * ‖f β‖ ^ 2 ≤ My) :
    ‖embed ((leakOp Y n (creOp x * annOp y)).1.1 f)‖ ^ 2 ≤
      ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ k * ((Mx + My) / 2) := by
  rw [norm_leakOp_hop_sq Y n hx hxy]
  refine (Finset.sum_le_sum fun β _ => ?_).trans (sum_edgeWeight_le Y n k x y f.support f hMx hMy)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (by linarith) (by positivity)) (edgeWeight_nonneg Y n x β)) (by positivity)


/-!

## F. The leakage of a bond term

-/

/-- An operator whose matrix elements never raise an occupation in `Y` does not leak. -/
lemma leakOp_eq_zero_of_le (Y : Finset L) (n : ℕ) (T : adjointable L)
    (hT : ∀ α β, matEl T α β ≠ 0 → ∀ z ∈ Y, α z ≤ β z) : leakOp Y n T = 0 := by
  refine adjointable_ext_matEl fun α β => ?_
  rw [matEl_leakOp, show matEl (0 : adjointable L) α β = 0 from rfl]
  by_cases h : matEl T α β = 0
  · rw [h]; ring
  · rcases cutWeight_mem Y n β with hb | hb
    · simp [hb]
    · have ha : cutWeight Y n α = 1 := by
        unfold cutWeight at hb ⊢
        split_ifs at hb with hc
        · exact if_pos fun z hz => (hT α β h z hz).trans (hc z hz)
        · exact absurd hb (by norm_num)
      simp [ha]

lemma leakOp_smul (Y : Finset L) (n : ℕ) (c : ℂ) (T : adjointable L) :
    leakOp Y n (c • T) = c • leakOp Y n T := by
  unfold leakOp; rw [mul_smul_comm, smul_mul_assoc]

/-- **Pair annihilation does not leak.** -/
lemma leakOp_annOp_mul_annOp (Y : Finset L) (n : ℕ) (a b : L) :
    leakOp Y n (annOp a * annOp b) = 0 :=
  leakOp_eq_zero_of_le Y n _ fun α β h z _ => by
    change ann a (ann b (single β 1)) α ≠ 0 at h
    rw [ann_single, ann_single, Finsupp.single_apply] at h
    split_ifs at h with he
    · rw [← he]; simp only [Finsupp.tsub_apply]; omega
    · exact absurd rfl h

/-- **Hopping out of `Y` does not leak:** `a_a† a_b` with `a ∉ Y` lowers the occupations in `Y`. -/
lemma leakOp_creOp_mul_annOp_of_not_mem (Y : Finset L) (n : ℕ) {a : L} (b : L) (ha : a ∉ Y) :
    leakOp Y n (creOp a * annOp b) = 0 :=
  leakOp_eq_zero_of_le Y n _ fun α β h z hz => by
    change cre a (ann b (single β 1)) α ≠ 0 at h
    rw [ann_single, cre_single, Finsupp.single_apply] at h
    split_ifs at h with he
    · rw [← he]
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply,
        if_neg (show a ≠ z from fun e => ha (e ▸ hz))]
      omega
    · exact absurd rfl h

namespace BoseHubbardData

variable (D : BoseHubbardData L)

open Classical in
/-- **The leakage of a bond crossing the boundary of `Y`.** For `x ∈ Y` and `y ∉ Y`, only the
hopping `a_x† a_y` into `Y` and the pair creation `a_x† a_y†` leak; both are unbounded. -/
lemma leakOp_bondTerm_boundary (Y : Finset L) (n : ℕ) {x y : L} (hy : y ∉ Y) :
    leakOp Y n (D.bondTerm x y) = if D.graph.Adj x y then
      ((-D.J x y : ℝ) : ℂ) • leakOp Y n (creOp x * annOp y) +
        D.Δ x y • leakOp Y n (creOp x * creOp y) else 0 := by
  unfold bondTerm
  split_ifs
  · rw [leakOp_add, leakOp_add, leakOp_smul, leakOp_smul, leakOp_smul, leakOp_add,
      leakOp_creOp_mul_annOp_of_not_mem Y n x hy, leakOp_annOp_mul_annOp, add_zero, smul_zero,
      add_zero]
  · unfold leakOp; rw [mul_zero, zero_mul]

open Classical in
/-- **The same bond, in the other orientation.** For `x ∈ Y` and `y ∉ Y`. -/
lemma leakOp_bondTerm_boundary' (Y : Finset L) (n : ℕ) {x y : L} (hy : y ∉ Y) :
    leakOp Y n (D.bondTerm y x) = if D.graph.Adj y x then
      ((-D.J y x : ℝ) : ℂ) • leakOp Y n (creOp x * annOp y) +
        D.Δ y x • leakOp Y n (creOp x * creOp y) else 0 := by
  unfold bondTerm
  split_ifs
  · rw [leakOp_add, leakOp_add, leakOp_smul, leakOp_smul, leakOp_smul, leakOp_add,
      leakOp_creOp_mul_annOp_of_not_mem Y n x hy, leakOp_annOp_mul_annOp, zero_add, smul_zero,
      add_zero, creOp_comm_creOp]
  · unfold leakOp; rw [mul_zero, zero_mul]

open Classical in
/-- **The leakage of a bond inside `Y`.** Both hoppings and the pair creation can leak, and pair
annihilation cannot. -/
lemma leakOp_bondTerm_inside (Y : Finset L) (n : ℕ) (x y : L) :
    leakOp Y n (D.bondTerm x y) = if D.graph.Adj x y then
      ((-D.J x y : ℝ) : ℂ) • (leakOp Y n (creOp x * annOp y) + leakOp Y n (creOp y * annOp x)) +
        D.Δ x y • leakOp Y n (creOp x * creOp y) else 0 := by
  unfold bondTerm
  split_ifs
  · rw [leakOp_add, leakOp_add, leakOp_smul, leakOp_smul, leakOp_smul, leakOp_add,
      leakOp_annOp_mul_annOp, smul_zero, add_zero]
  · unfold leakOp; rw [mul_zero, zero_mul]

end BoseHubbardData

/-- The cutoff weight of `β + e_y + e_x` when `x, y ∈ Y` and `x ≠ y`: the pair creation leaks
from the states of the cutoff with `n` bosons at `x` or at `y`. -/
lemma cutWeight_mul_one_sub_add_pair_inside (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∈ Y)
    (hy : y ∈ Y) (hxy : x ≠ y) (β : Occ L) :
    (1 - cutWeight Y n (β + single y 1 + single x 1)) * cutWeight Y n β =
      if (∀ z ∈ Y, β z ≤ n) ∧ (β x = n ∨ β y = n) then 1 else 0 := by
  have hcoord : ∀ z, (β + single y 1 + single x 1 : Occ L) z =
      β z + (if y = z then 1 else 0) + if x = z then 1 else 0 := fun z => by
    simp [Finsupp.single_apply]
  unfold cutWeight
  by_cases hβY : ∀ z ∈ Y, β z ≤ n
  · rw [if_pos hβY, mul_one]
    by_cases hb : β x = n ∨ β y = n
    · rw [if_neg, if_pos ⟨hβY, hb⟩]
      · norm_num
      · intro h
        rcases hb with hb | hb
        · have := h x hx; rw [hcoord x, if_pos rfl] at this; omega
        · have := h y hy; rw [hcoord y, if_pos rfl] at this; omega
    · rw [if_pos, if_neg (fun h => hb h.2)]
      · norm_num
      · intro z hz
        rw [hcoord z]
        have := hβY z hz
        push Not at hb
        split_ifs with h1 h2 h2
        · exact absurd (h2.trans h1.symm) hxy
        · subst h1; omega
        · subst h2; omega
        · omega
  · rw [if_neg hβY, if_neg (show ¬((∀ z ∈ Y, β z ≤ n) ∧ (β x = n ∨ β y = n)) from
      fun h => hβY h.1), mul_zero]

/-- **The pair creation inside `Y` on basis states.** For `x, y ∈ Y`, `x ≠ y`, the leakage
`P_{Y,n}^⊥ a_x† a_y† P_{Y,n} e_β` is `√(β_x+1) √(β_y+1) e_{β + e_x + e_y}` if `β` is in the cutoff
with `β_x = n` or `β_y = n`, and zero otherwise. Its amplitude is at most `n + 1`: inside `Y` the
leakage is bounded. -/
lemma leakOp_pair_single_inside (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∈ Y) (hy : y ∈ Y)
    (hxy : x ≠ y) (β : Occ L) :
    (leakOp Y n (creOp x * creOp y)).1.1 (single β 1) = single (β + single y 1 + single x 1)
      (((if (∀ z ∈ Y, β z ≤ n) ∧ (β x = n ∨ β y = n) then 1 else 0 : ℝ) : ℂ) *
        (((Real.sqrt ((β x : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((β y : ℝ) + 1) : ℝ) : ℂ))) := by
  have hbx : (β + single y 1 : Occ L) x = β x := by simp [hxy.symm]
  show diagLin _ (cre x (cre y (diagLin (cutWeight Y n) (single β 1)))) = _
  rw [diagLin_single, mul_one, show (single β ((cutWeight Y n β : ℝ) : ℂ) : Occ L →₀ ℂ) =
      ((cutWeight Y n β : ℝ) : ℂ) • single β 1 by simp [Finsupp.smul_single], map_smul,
    map_smul, cre_single, cre_single, map_smul, diagLin_single, Finsupp.smul_single, smul_eq_mul,
    hbx, ← cutWeight_mul_one_sub_add_pair_inside Y n hx hy hxy β]
  congr 1
  push_cast
  ring


/-!

## G. The tail in a density matrix

-/

section DensityMatrix

open ProbabilisticTheory
open scoped InnerProductSpace

omit [DecidableEq L] in
/-- The occupation basis `e_α` of `ℓ²(Occ L)`. -/
def occBasis : HilbertBasis (Occ L) ℂ (HilbertSp (Occ L)) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

lemma occBasis_apply (α : Occ L) : occBasis α = lp.single 2 α (1 : ℂ) := by
  rw [← HilbertBasis.repr_symm_single]; rfl

omit [DecidableEq L] in
lemma occBasis_injective : Function.Injective (occBasis (L := L)) :=
  occBasis.orthonormal.linearIndependent.injective

omit [DecidableEq L] in
/-- The occupation basis indexed by its range, the form used by the trace-class library. -/
def occBasisSet : HilbertBasis (Set.range (occBasis (L := L))) ℂ (HilbertSp (Occ L)) :=
  HilbertBasis.mk (v := Subtype.val) ((orthonormal_subtype_range occBasis_injective).mpr
    occBasis.orthonormal) (by rw [Subtype.range_coe]; exact occBasis.dense_span.ge)

omit [DecidableEq L] in
lemma tsum_occBasisSet (F : HilbertSp (Occ L) → ℂ) :
    ∑' i, F (occBasisSet i) = ∑' α, F (occBasis α) := by
  rw [occBasisSet, HilbertBasis.coe_mk]
  exact (Equiv.tsum_eq (Equiv.ofInjective _ occBasis_injective) fun i => F i.1).symm

lemma sub_cutOp_occBasis (Y : Finset L) (n : ℕ) (α : Occ L) :
    (1 - cutOp Y n) (occBasis α) = ((1 - cutWeight Y n α : ℝ) : ℂ) • occBasis α := by
  refine Subtype.ext (funext fun β => ?_)
  show (occBasis α : HilbertSp (Occ L)) β - (cutOp Y n (occBasis α) : HilbertSp (Occ L)) β = _
  rw [cutOp_apply, occBasis_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply]
  by_cases h : β = α
  · subst h; simp
  · simp [Pi.single_apply, h]

omit [DecidableEq L] in
/-- The diagonal `⟨α|ρ|α⟩` of a positive operator is real. -/
lemma inner_occBasis_eq_re {ρ : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L)} (hρ : 0 ≤ ρ)
    (α : Occ L) :
    ⟪occBasis α, ρ (occBasis α)⟫_ℂ = (((⟪occBasis α, ρ (occBasis α)⟫_ℂ).re : ℝ) : ℂ) := by
  have h := ((ContinuousLinearMap.isPositive_iff_complex ρ).mp
    (ρ.nonneg_iff_isPositive.mp hρ) (occBasis α)).1
  rw [← inner_conj_symm, ← h, Complex.conj_ofReal, Complex.ofReal_inj, ← h, Complex.ofReal_re]

omit [DecidableEq L] in
lemma isTraceClass_mul_right {ρ : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L)}
    (h : IsTraceClass ρ) (B : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L)) :
    IsTraceClass (ρ * B) := by
  simpa using isTraceClass_mul_mul (A := 1) (B := B) h

omit [DecidableEq L] in
lemma sub_cutOp_mul_self (Y : Finset L) (n : ℕ) :
    (1 - cutOp Y n) * (1 - cutOp Y n) = 1 - cutOp Y n := by
  rw [sub_mul, mul_sub, mul_sub, cutOp_mul_self, one_mul, mul_one, one_mul, sub_self, sub_zero]

omit [DecidableEq L] in
/-- The trace of `ρ Q` for a positive trace-class `ρ` and a self-adjoint idempotent `Q` that is
diagonal in the occupation basis with eigenvalues `c α ∈ {0, 1}`. -/
lemma trace_mul_diag_proj {ρ : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L)} (hρ : 0 ≤ ρ)
    (htr : IsTraceClass ρ) {Q : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L)} (hQ : IsSelfAdjoint Q)
    (hQQ : Q * Q = Q) {c : Occ L → ℝ} (hc : ∀ α, Q (occBasis α) = (c α : ℂ) • occBasis α)
    (hcc : ∀ α, c α * c α = c α) :
    trace (ρ * Q) (isTraceClass_mul_right htr Q) =
      ((∑' α, (⟪occBasis α, ρ (occBasis α)⟫_ℂ).re * c α : ℝ) : ℂ) := by
  have key : ∀ {X Z : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L)} (hXZ : X = Z) hX hZ,
      trace X hX = trace Z hZ := by intro X Z h hX hZ; subst h; rfl
  have hT := isTraceClass_mul_right htr Q
  have hX : IsTraceClass (Q * ρ * Q) := isTraceClass_mul_mul htr
  have hX0 : 0 ≤ Q * ρ * Q := by
    have h := star_left_conjugate_nonneg hρ Q
    rwa [hQ.star_eq] at h
  have hQT : IsTraceClass (Q * (ρ * Q)) := mul_assoc Q ρ Q ▸ hX
  have hcyc := trace_mul_cycle (A := Q) hT
  calc trace (ρ * Q) (isTraceClass_mul_right htr Q)
        = trace (ρ * Q * Q) (isTraceClass_mul_right hT Q) := key (by rw [mul_assoc, hQQ]) _ _
    _ = trace (Q * (ρ * Q)) hQT := trace_congr.trans (hcyc.symm.trans trace_congr)
    _ = trace (Q * ρ * Q) hX := key (mul_assoc Q ρ Q).symm _ _
    _ = _ := by
      rw [trace_eq_of_hilbertBasis_of_nonneg hX0 hX occBasisSet,
        tsum_occBasisSet (fun v => ⟪v, (Q * ρ * Q) v⟫_ℂ), Complex.ofReal_tsum]
      refine tsum_congr fun α => ?_
      have hsa : ⟪occBasis α, Q (ρ (Q (occBasis α)))⟫_ℂ =
          ⟪Q (occBasis α), ρ (Q (occBasis α))⟫_ℂ := by
        rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
          hQ.star_eq]
      show ⟪occBasis α, Q (ρ (Q (occBasis α)))⟫_ℂ = _
      rw [hsa, hc, map_smul, inner_smul_left, inner_smul_right, inner_occBasis_eq_re hρ α,
        Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul, hcc, ← Complex.ofReal_mul,
        mul_comm, Complex.ofReal_re]

/-- **The trace of a density matrix against the complement of the cutoff** is the diagonal sum
`Tr ρ (1 - P_{Y,n}) = Σ_α ⟨α|ρ|α⟩ (1 - P_{Y,n}(α))`. -/
lemma trace_mul_sub_cutOp {ρ : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L)} (hρ : 0 ≤ ρ)
    (htr : IsTraceClass ρ) (Y : Finset L) (n : ℕ) :
    trace (ρ * (1 - cutOp Y n)) (isTraceClass_mul_right htr _) =
      ((∑' α, (⟪occBasis α, ρ (occBasis α)⟫_ℂ).re * (1 - cutWeight Y n α) : ℝ) : ℂ) := by
  have hQ : IsSelfAdjoint (1 - cutOp Y n) := by
    have h := isSelfAdjoint_cutOp Y n
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint] at h ⊢
    rw [map_sub, h, ← ContinuousLinearMap.star_eq_adjoint, star_one]
  exact trace_mul_diag_proj hρ htr hQ (sub_cutOp_mul_self Y n) (sub_cutOp_occBasis Y n)
    fun α => by rcases cutWeight_mem Y n α with h | h <;> simp [h]

/-- **The tail of the localized cutoff in a density matrix**, independently of the ambient volume.
For a positive trace-class `ρ` whose local moments `Tr ρ (N_x + 1)^k = Σ_α ⟨α|ρ|α⟩ (α_x + 1)^k` are
at most `M` at the sites of `Y`, `Re Tr ρ (1 - P_{Y,n}) ≤ |Y| M / (n + 1)^k`. The moments of the
unbounded diagonal `(N_x + 1)^k` are defined by their diagonal sum, which is the standard value
in `[0, ∞]` for a positive `ρ`. -/
lemma trace_tail_le {ρ : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L)} (hρ : 0 ≤ ρ)
    (htr : IsTraceClass ρ) (Y : Finset L) (n k : ℕ) {M : ℝ}
    (hsum : ∀ x ∈ Y, Summable fun α => (⟪occBasis α, ρ (occBasis α)⟫_ℂ).re * ((α x : ℝ) + 1) ^ k)
    (hM : ∀ x ∈ Y, ∑' α, (⟪occBasis α, ρ (occBasis α)⟫_ℂ).re * ((α x : ℝ) + 1) ^ k ≤ M) :
    (trace (ρ * (1 - cutOp Y n)) (isTraceClass_mul_right htr _)).re ≤
      Y.card * M / ((n : ℝ) + 1) ^ k := by
  rw [trace_mul_sub_cutOp hρ htr, Complex.ofReal_re]
  refine (tsum_tail_le Y n k _ (fun α => ?_) hsum hM).2
  have h := ((ContinuousLinearMap.isPositive_iff_complex ρ).mp
    (ρ.nonneg_iff_isPositive.mp hρ) (occBasis α)).2
  rw [← inner_conj_symm, RCLike.conj_re] at h
  exact h

end DensityMatrix


/-!

## H. The compressed Hamiltonian

-/

namespace BoseHubbardData

variable (D : BoseHubbardData L)

/-- **The compressed Hamiltonian** `P_{Y,n} H_Λ P_{Y,n}`. It commutes with `P_{Y,n}` and vanishes
on the range of `1 - P_{Y,n}`, so it is `H_P ⊕ 0` with `H_P` the restriction of `P H_Λ P` to the
range of the cutoff, and `e^{-it P H P} P = e^{-it H_P} P`. -/
def cutHam (V : L → ℕ → ℝ) (Λ Y : Finset L) (n : ℕ) : adjointable L :=
  cutAdj Y n * D.finiteHam V Λ * cutAdj Y n

lemma star_cutHam (V : L → ℕ → ℝ) (Λ Y : Finset L) (n : ℕ) :
    star (D.cutHam V Λ Y n) = D.cutHam V Λ Y n := by
  rw [cutHam, star_mul, star_mul, star_cutAdj, D.star_finiteHam, mul_assoc]

lemma matEl_cutHam (V : L → ℕ → ℝ) (Λ Y : Finset L) (n : ℕ) (α β : Occ L) :
    matEl (D.cutHam V Λ Y n) α β =
      ((cutWeight Y n α : ℝ) : ℂ) * matEl (D.finiteHam V Λ) α β * ((cutWeight Y n β : ℝ) : ℂ) := by
  rw [cutHam, cutAdj, matEl_mul_diagAdj, matEl_diagAdj_mul]

/-- The compressed Hamiltonian is dominated entrywise by `H_Λ`. -/
lemma norm_matEl_cutHam_le (V : L → ℕ → ℝ) (Λ Y : Finset L) (n : ℕ) (α β : Occ L) :
    ‖matEl (D.cutHam V Λ Y n) α β‖ ≤ ‖matEl (D.finiteHam V Λ) α β‖ := by
  rw [matEl_cutHam]
  rcases cutWeight_mem Y n α with ha | ha <;> rcases cutWeight_mem Y n β with hb | hb <;>
    simp [ha, hb]

/-- **The compressed Hamiltonian is essentially self-adjoint** on the finite vectors, for every
real on-site potential, every finite region `Y` and every cutoff level `n`. -/
lemma cutHam_isEssentiallySelfAdjoint (V : L → ℕ → ℝ) (Λ Y : Finset L) (n : ℕ) :
    (polyOp (D.cutHam V Λ Y n)).IsEssentiallySelfAdjoint :=
  D.isEssentiallySelfAdjoint_of_dominated V Λ (D.star_cutHam V Λ Y n)
    (D.norm_matEl_cutHam_le V Λ Y n)

/-- The compressed Hamiltonian commutes with the cutoff. -/
lemma cutAdj_mul_cutHam (V : L → ℕ → ℝ) (Λ Y : Finset L) (n : ℕ) :
    cutAdj Y n * D.cutHam V Λ Y n = D.cutHam V Λ Y n ∧
      D.cutHam V Λ Y n * cutAdj Y n = D.cutHam V Λ Y n := by
  refine ⟨?_, ?_⟩ <;> rw [cutHam]
  · rw [← mul_assoc, ← mul_assoc, cutAdj_mul_self]
  · rw [mul_assoc, cutAdj_mul_self]

end BoseHubbardData


/-!

## I. The reverse leakage across the boundary of `Y`

-/

/-- **The reverse leakage** `P_{Y,n} T P_{Y,n}^⊥` of an operator into the range of the cutoff. -/
def revLeakOp (Y : Finset L) (n : ℕ) (T : adjointable L) : adjointable L :=
  cutAdj Y n * T * cutComplAdj Y n

/-- The weight of the states that a lowering move at `x` brings back into the cutoff: `n + 1`
bosons at `x` and at most `n` at the other sites of `Y`. -/
def revWeight (Y : Finset L) (n : ℕ) (x : L) (β : Occ L) : ℝ :=
  if (∀ z ∈ Y, z ≠ x → β z ≤ n) ∧ β x = n + 1 then 1 else 0

lemma revWeight_mem (Y : Finset L) (n : ℕ) (x : L) (β : Occ L) :
    revWeight Y n x β = 0 ∨ revWeight Y n x β = 1 := by
  unfold revWeight; split_ifs <;> simp

/-- A state `γ` with `γ_z = β_z - [z = x]` on `Y`, `x ∈ Y`, `β_x ≥ 1`: the cutoff weight of `γ`
times that of the complement of `β` is the reverse weight. -/
lemma cutWeight_mul_one_sub_lower (Y : Finset L) (n : ℕ) {x : L} (hx : x ∈ Y) {β γ : Occ L}
    (hβ : 1 ≤ β x) (hγ : ∀ z ∈ Y, γ z = β z - if x = z then 1 else 0) :
    cutWeight Y n γ * (1 - cutWeight Y n β) = revWeight Y n x β := by
  unfold cutWeight revWeight
  by_cases hr : (∀ z ∈ Y, z ≠ x → β z ≤ n) ∧ β x = n + 1
  · rw [if_pos hr, if_pos, if_neg]
    · norm_num
    · intro h; have := h x hx; omega
    · intro z hz
      rw [hγ z hz]
      by_cases hzx : z = x
      · subst hzx; rw [if_pos rfl]; omega
      · rw [if_neg (Ne.symm hzx)]; exact hr.1 z hz hzx
  · rw [if_neg hr]
    by_cases hc : ∀ z ∈ Y, γ z ≤ n
    · rw [if_pos hc]
      have hb : ∀ z ∈ Y, β z ≤ n := by
        intro z hz
        have h1 := hc z hz
        rw [hγ z hz] at h1
        by_cases hzx : z = x
        · subst hzx
          rw [if_pos rfl] at h1
          by_contra hlt
          exact hr ⟨fun w hw hwx => by
            have := hc w hw; rw [hγ w hw, if_neg (Ne.symm hwx)] at this; exact this, by omega⟩
        · rw [if_neg (Ne.symm hzx)] at h1; exact h1
      rw [if_pos hb]; norm_num
    · rw [if_neg hc, zero_mul]

/-- **Pair annihilation back into the cutoff on basis states.** For `x ∈ Y`, `y ∉ Y`,
`P_{Y,n} a_y a_x P_{Y,n}^⊥ e_β = 1_{β_x = n+1, β - e_x ∈ P_{Y,n}} √β_x √β_y e_{β - e_x - e_y}`. -/
lemma revLeakOp_pair_single (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∈ Y) (hy : y ∉ Y)
    (β : Occ L) :
    (revLeakOp Y n (annOp y * annOp x)).1.1 (single β 1) = single (β - single x 1 - single y 1)
      (((revWeight Y n x β : ℝ) : ℂ) * (((Real.sqrt (β x : ℝ) : ℝ) : ℂ) *
        ((Real.sqrt (β y : ℝ) : ℝ) : ℂ))) := by
  have hxy : x ≠ y := fun e => hy (e ▸ hx)
  have hby : (β - single x 1 : Occ L) y = β y := by simp [Finsupp.single_apply, hxy]
  show diagLin _ (ann y (ann x (diagLin (fun α => 1 - cutWeight Y n α) (single β 1)))) = _
  rw [diagLin_single, mul_one, show (single β ((1 - cutWeight Y n β : ℝ) : ℂ) : Occ L →₀ ℂ) =
      ((1 - cutWeight Y n β : ℝ) : ℂ) • single β 1 by simp [Finsupp.smul_single], map_smul,
    map_smul, ann_single, ann_single, map_smul, diagLin_single, Finsupp.smul_single, smul_eq_mul,
    hby]
  rcases Nat.eq_zero_or_pos (β x) with h0 | hpos
  · simp [h0]
  rcases Nat.eq_zero_or_pos (β y) with h0 | _
  · simp [h0]
  rw [← cutWeight_mul_one_sub_lower Y n hx hpos (γ := β - single x 1 - single y 1) fun z hz => by
    simp [Finsupp.single_apply, show y ≠ z from fun e => hy (e ▸ hz)]]
  congr 1
  push_cast
  ring

/-- **Hopping out of `Y` back into the cutoff on basis states.** For `x ∈ Y`, `y ∉ Y`,
`P_{Y,n} a_y† a_x P_{Y,n}^⊥ e_β = 1_{β_x = n+1, β - e_x ∈ P_{Y,n}} √β_x √(β_y+1) e_{β-e_x+e_y}`. -/
lemma revLeakOp_hop_single (Y : Finset L) (n : ℕ) {x y : L} (hx : x ∈ Y) (hy : y ∉ Y)
    (β : Occ L) :
    (revLeakOp Y n (creOp y * annOp x)).1.1 (single β 1) = single (β - single x 1 + single y 1)
      (((revWeight Y n x β : ℝ) : ℂ) * (((Real.sqrt (β x : ℝ) : ℝ) : ℂ) *
        ((Real.sqrt ((β y : ℝ) + 1) : ℝ) : ℂ))) := by
  have hxy : x ≠ y := fun e => hy (e ▸ hx)
  have hby : (β - single x 1 : Occ L) y = β y := by simp [Finsupp.single_apply, hxy]
  show diagLin _ (cre y (ann x (diagLin (fun α => 1 - cutWeight Y n α) (single β 1)))) = _
  rw [diagLin_single, mul_one, show (single β ((1 - cutWeight Y n β : ℝ) : ℂ) : Occ L →₀ ℂ) =
      ((1 - cutWeight Y n β : ℝ) : ℂ) • single β 1 by simp [Finsupp.smul_single], map_smul,
    map_smul, ann_single, cre_single, map_smul, diagLin_single, Finsupp.smul_single, smul_eq_mul,
    hby]
  rcases Nat.eq_zero_or_pos (β x) with h0 | hpos
  · simp [h0]
  rw [← cutWeight_mul_one_sub_lower Y n hx hpos (γ := β - single x 1 + single y 1) fun z hz => by
    simp [Finsupp.single_apply, show y ≠ z from fun e => hy (e ▸ hz)]]
  congr 1
  push_cast
  ring

section Apply

variable {B : Type*} [DecidableEq B]

/-- An operator acting on basis states by `e_β ↦ w(β) e_{τ(β)}`, applied to a finite vector. -/
lemma apply_eq_sum_single (T : Adjointable B) (τ : B → B) (w : B → ℂ)
    (hT : ∀ β, T.1.1 (single β 1) = single (τ β) (w β)) (f : B →₀ ℂ) :
    T.1.1 f = ∑ β ∈ f.support, single (τ β) (f β * w β) := by
  conv_lhs => rw [← Finsupp.sum_single f]
  rw [Finsupp.sum, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [show (single β (f β) : B →₀ ℂ) = f β • single β 1 by simp [Finsupp.smul_single],
    map_smul, hT, Finsupp.smul_single, smul_eq_mul]

/-- **The square norm of such an operator applied to a finite vector**, if `τ` is injective on the
states with `w(β) ≠ 0`. -/
lemma norm_apply_sq_eq (T : Adjointable B) (τ : B → B) (w : B → ℂ)
    (hT : ∀ β, T.1.1 (single β 1) = single (τ β) (w β))
    (hτ : ∀ a b, w a ≠ 0 → w b ≠ 0 → τ a = τ b → a = b) (f : B →₀ ℂ) :
    ‖embed (T.1.1 f)‖ ^ 2 = ∑ β ∈ f.support, ‖w β‖ ^ 2 * ‖f β‖ ^ 2 := by
  classical
  rw [apply_eq_sum_single T τ w hT, ← Finset.sum_filter_of_ne (p := fun β => w β ≠ 0)
      (fun β _ hne h0 => hne (by simp [h0])),
    norm_embed_sum_single_sq _ _ (fun a ha b hb => hτ a b (Finset.mem_filter.mp ha).2
      (Finset.mem_filter.mp hb).2), ← Finset.sum_filter_of_ne (s := f.support)
      (p := fun β => w β ≠ 0) (fun β _ hne h0 => hne (by simp [h0]))]
  exact Finset.sum_congr rfl fun β _ => by rw [norm_mul, mul_pow, mul_comm]

end Apply

/-- On the support of the reverse weight `β_x = n + 1`. -/
lemma revWeight_mul_le (Y : Finset L) (n k : ℕ) (x : L) (β : Occ L) :
    revWeight Y n x β * (β x : ℝ) ≤ ((n : ℝ) + 1) * (((β x : ℝ) + 1) / ((n : ℝ) + 1)) ^ k := by
  unfold revWeight
  split_ifs with h
  · rw [one_mul, h.2]
    push_cast
    have : (1 : ℝ) ≤ (((n : ℝ) + 1 + 1) / ((n : ℝ) + 1)) ^ k :=
      one_le_pow₀ (by rw [le_div_iff₀ (by positivity)]; linarith)
    nlinarith
  · rw [zero_mul]; positivity

lemma revWeight_nonneg (Y : Finset L) (n : ℕ) (x : L) (β : Occ L) : 0 ≤ revWeight Y n x β := by
  rcases revWeight_mem Y n x β with h | h <;> rw [h] <;> norm_num

/-- **Weighted estimate for pair annihilation back into the cutoff.** For `x ∈ Y`, `y ∉ Y` and
every finite vector `g` with local moments of order `2k` at `x` and `2` at `y`,
`‖P_{Y,n} a_y a_x P_{Y,n}^⊥ g‖² ≤ (n + 1)^{1-k} (M_x + M_y) / 2`. -/
lemma norm_revLeakOp_pair_sq_le (Y : Finset L) (n k : ℕ) {x y : L} (hx : x ∈ Y) (hy : y ∉ Y)
    (g : Occ L →₀ ℂ) {Mx My : ℝ}
    (hMx : ∑ β ∈ g.support, ((β x : ℝ) + 1) ^ (2 * k) * ‖g β‖ ^ 2 ≤ Mx)
    (hMy : ∑ β ∈ g.support, ((β y : ℝ) + 1) ^ 2 * ‖g β‖ ^ 2 ≤ My) :
    ‖embed ((revLeakOp Y n (annOp y * annOp x)).1.1 g)‖ ^ 2 ≤
      ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ k * ((Mx + My) / 2) := by
  rw [norm_apply_sq_eq _ _ _ (revLeakOp_pair_single Y n hx hy) (fun a b ha hb h => ?_)]
  · refine (Finset.sum_le_sum fun β _ => ?_).trans (sum_weight_mul_le n k x y g.support g
      (revWeight Y n x) (fun β => (β x : ℝ)) (revWeight_mul_le Y n k x) hMx hMy)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity), sq_abs]
    rcases revWeight_mem Y n x β with h | h <;> rw [h]
    · simp
    · nlinarith [sq_nonneg ‖g β‖, (Nat.cast_nonneg (β x) : (0 : ℝ) ≤ β x)]
  · have h1 : single x 1 ≤ a := (single_le_iff' x a).mpr (Nat.one_le_iff_ne_zero.mpr fun h0 =>
      ha (by simp [h0]))
    have h2 : single x 1 ≤ b := (single_le_iff' x b).mpr (Nat.one_le_iff_ne_zero.mpr fun h0 =>
      hb (by simp [h0]))
    have hxy : x ≠ y := fun e => hy (e ▸ hx)
    have hay : a y ≠ 0 := fun h0 => ha (by simp [h0])
    have hby : b y ≠ 0 := fun h0 => hb (by simp [h0])
    have h3 : single y 1 ≤ a - single x 1 := (single_le_iff' y _).mpr (by
      simp only [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hxy]; omega)
    have h4 : single y 1 ≤ b - single x 1 := (single_le_iff' y _).mpr (by
      simp only [Finsupp.tsub_apply, Finsupp.single_apply, if_neg hxy]; omega)
    exact (tsub_left_inj h1 h2).mp ((tsub_left_inj h3 h4).mp h)

/-- **Weighted estimate for hopping out of `Y` back into the cutoff.** For `x ∈ Y`, `y ∉ Y` and
every finite vector `g` with local moments of order `2k` at `x` and `2` at `y`,
`‖P_{Y,n} a_y† a_x P_{Y,n}^⊥ g‖² ≤ (n + 1)^{1-k} (M_x + M_y) / 2`. -/
lemma norm_revLeakOp_hop_sq_le (Y : Finset L) (n k : ℕ) {x y : L} (hx : x ∈ Y) (hy : y ∉ Y)
    (g : Occ L →₀ ℂ) {Mx My : ℝ}
    (hMx : ∑ β ∈ g.support, ((β x : ℝ) + 1) ^ (2 * k) * ‖g β‖ ^ 2 ≤ Mx)
    (hMy : ∑ β ∈ g.support, ((β y : ℝ) + 1) ^ 2 * ‖g β‖ ^ 2 ≤ My) :
    ‖embed ((revLeakOp Y n (creOp y * annOp x)).1.1 g)‖ ^ 2 ≤
      ((n : ℝ) + 1) / ((n : ℝ) + 1) ^ k * ((Mx + My) / 2) := by
  rw [norm_apply_sq_eq _ _ _ (revLeakOp_hop_single Y n hx hy) (fun a b ha hb h => ?_)]
  · refine (Finset.sum_le_sum fun β _ => ?_).trans (sum_weight_mul_le n k x y g.support g
      (revWeight Y n x) (fun β => (β x : ℝ)) (revWeight_mul_le Y n k x) hMx hMy)
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity), sq_abs]
    rcases revWeight_mem Y n x β with h | h <;> rw [h] <;> ring_nf <;> simp
  · have h1 : single x 1 ≤ a := (single_le_iff' x a).mpr (Nat.one_le_iff_ne_zero.mpr fun h0 =>
      ha (by simp [h0]))
    have h2 : single x 1 ≤ b := (single_le_iff' x b).mpr (Nat.one_le_iff_ne_zero.mpr fun h0 =>
      hb (by simp [h0]))
    exact (tsub_left_inj h1 h2).mp (add_right_cancel h)

end InfiniteBosons
