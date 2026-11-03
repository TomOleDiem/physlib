/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.LatticeFermions.LiebRobinson

/-!

# The thermodynamic limit of the dynamics

For a locally finite interaction bounded by `J`, the finite-volume dynamics `α_t^Λ(A)` of a local
observable `A` converge in norm as `Λ` grows, uniformly for `t` in compact intervals.

## i. Overview

*Duhamel.* For `Λ ⊆ Λ'` the derivative of `s ↦ α_s^{Λ'}(α_{t-s}^Λ(A))` is
`α_s^{Λ'}(i[H_{Λ'} - H_Λ, α_{t-s}^Λ(A)])`, so

`‖α_t^{Λ'}(A) - α_t^Λ(A)‖ ≤ t · sup_{0 ≤ r ≤ t} ‖[H_{Λ'} - H_Λ, α_r^Λ(A)]‖`.

The difference `H_{Λ'} - H_Λ` consists of the on-site terms of `Λ' \ Λ`, which commute with
`α_r^Λ(A) ∈ 𝔄_Λ` (they are even and supported outside `Λ`), and of the terms `Φ(Z)` with
`Z ⊆ Λ'`, `Z ⊄ Λ`. These are even, so the Lieb–Robinson bound applies to each with `B = Φ(Z)`:

`‖α_t^{Λ'}(A) - α_t^Λ(A)‖ ≤ 2 t ‖A‖ Σ_{Z ⊆ Λ', Z ⊄ Λ} ‖Φ(Z)‖ Σ_k e_k(t) w_k(X, Z)`.

*Smallness.* Let `R_k(X)` be the sites reached from `X` by chains of `k` nonzero interaction
terms, a finite set by local finiteness. If `w_k(X, Z) ≠ 0` and `Φ(Z) ≠ 0` then `Z ⊆ R_{k+1}(X)`.
So if `R_K(X) ⊆ Λ`, only the terms with `k ≥ K` survive, and since
`Σ_Z ‖Φ(Z)‖ w_k(X, Z) = W_{k+1}(X) ≤ max(1, |X|) J^{k+1}`, the difference is bounded by the tail
`Σ_{k ≥ K} e_k(T) max(1, |X|) J^{k+1}` of a convergent series, uniformly in `Λ' ⊇ Λ` and
`0 ≤ t ≤ T`. Negative times are the positive times of the interaction `-Φ`.

## ii. Key results

- `LatticeFermions.norm_evolution_sub_evolution_le` : the Duhamel estimate.
- `LatticeFermions.Interaction.norm_evolution_sub_le_tail` : the Cauchy estimate.
- `LatticeFermions.Interaction.uniformCauchySeqOn_evolution` : the finite-volume dynamics of a
  local observable are uniformly Cauchy on compact time intervals as `Λ` grows.

## iii. Table of contents

- A. The Duhamel estimate
- B. Adding regions to the Hamiltonian
- C. Monotonicity of the Lieb–Robinson bound
- D. Reachable sets
- E. The Cauchy estimate
- F. Negative times
- G. Uniform convergence for local observables

## iv. References

* B. Nachtergaele, R. Sims, A. Young, Quasi-locality bounds for quantum lattice systems. Part I,
  arXiv:1810.02428, Section 3.
* O. Bratteli, D. W. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Theorem 6.2.11.

-/

@[expose] public section

noncomputable section

namespace LatticeFermions

open Finset Complex Filter Topology

/-!

## A. The Duhamel estimate

-/

section duhamel

variable {𝔄 : Type*} [CStarAlgebra 𝔄]

lemma hasDerivAt_duhamel (H H' : selfAdjoint 𝔄) (b : 𝔄) (s : ℝ) :
    HasDerivAt (fun r => evolution H' r (evolution H (-r) b))
      (evolution H' s (I • (((H' : 𝔄) - H) * evolution H (-s) b -
        evolution H (-s) b * ((H' : 𝔄) - H)))) s := by
  convert hasDerivAt_evolution_comp H' (hasDerivAt_evolution_neg H b s) using 2
  simp only [sub_mul, mul_sub, smul_sub]
  abel

/-- The Duhamel estimate: if `‖[H' - H, α_r(a)]‖ ≤ C` for `0 ≤ r ≤ t`, where `α` is the
dynamics of `H`, then `‖α'_t(a) - α_t(a)‖ ≤ C t` for the dynamics `α'` of `H'`. -/
lemma norm_evolution_sub_evolution_le (H H' : selfAdjoint 𝔄) (a : 𝔄) {t C : ℝ} (ht : 0 ≤ t)
    (hC : ∀ r, 0 ≤ r → r ≤ t → ‖((H' : 𝔄) - H) * evolution H r a -
      evolution H r a * ((H' : 𝔄) - H)‖ ≤ C) :
    ‖evolution H' t a - evolution H t a‖ ≤ C * t := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun r => evolution H' r (evolution H (-r) (evolution H t a))) (C := C)
    (fun s _ => (hasDerivAt_duhamel H H' (evolution H t a) s).hasDerivWithinAt)
    (fun s hs => ?_) t ⟨ht, le_rfl⟩
  · simpa [evolution_neg_evolution, evolution_zero] using h
  · rw [norm_evolution, norm_smul, Complex.norm_I, one_mul, ← evolution_add]
    exact hC _ (by linarith [hs.2]) (by linarith [hs.1])

end duhamel

namespace Interaction

variable {V : Type*} [DecidableEq V] {𝔄 : Type*} [CStarAlgebra 𝔄] {N : GradedLocalNet V 𝔄}
  {Φ : Interaction N}

/-!

## B. Adding regions to the Hamiltonian

-/

/-- The new interaction terms of `Λ'` compared with `Λ`. -/
def newTerms (Λ Λ' : Finset V) : Finset (Finset V) := Λ'.powerset \ Λ.powerset

omit [DecidableEq V] in
lemma evolution_hamiltonian_mem (Φ : Interaction N) (Λ : Finset V) (t : ℝ) {a : 𝔄}
    (ha : a ∈ N.loc Λ) : evolution (Φ.hamiltonian Λ) t a ∈ N.loc Λ :=
  evolution_mem _ t (N.isClosed_loc Λ) (Φ.hamiltonian_mem Λ) ha

lemma hamiltonian_sub_hamiltonian (Φ : Interaction N) {Λ Λ' : Finset V} (h : Λ ⊆ Λ') :
    (Φ.hamiltonian Λ' : 𝔄) - Φ.hamiltonian Λ =
      ∑ x ∈ Λ' \ Λ, Φ.onSite x + ∑ Z ∈ newTerms Λ Λ', Φ.term Z := by
  rw [hamiltonian_coe, hamiltonian_coe, onSiteSum, onSiteSum, ← sum_sdiff h (f := Φ.onSite),
    ← sum_sdiff (powerset_mono.mpr h) (f := Φ.term), newTerms]
  abel

/-- The commutator of `H_{Λ'} - H_Λ` with an element of `𝔄_Λ` only involves the new interaction
terms. -/
lemma norm_commutator_hamiltonian_sub_le (Φ : Interaction N) {Λ Λ' : Finset V} (h : Λ ⊆ Λ')
    {a : 𝔄} (ha : a ∈ N.loc Λ) :
    ‖((Φ.hamiltonian Λ' : 𝔄) - Φ.hamiltonian Λ) * a - a * ((Φ.hamiltonian Λ' : 𝔄) -
      Φ.hamiltonian Λ)‖ ≤ ∑ Z ∈ newTerms Λ Λ', ‖a * Φ.term Z - Φ.term Z * a‖ := by
  have hD : Commute a (∑ x ∈ Λ' \ Λ, Φ.onSite x) :=
    commute_sum_of_disjoint ha _ _ (fun x => {x})
      (fun x hx => disjoint_singleton_right.mpr (mem_sdiff.mp hx).2)
      (fun x _ => Φ.onSite_mem x) (fun x _ => Φ.isEven_onSite x)
  rw [Φ.hamiltonian_sub_hamiltonian h, add_mul, mul_add, hD.eq, add_sub_add_left_eq_sub,
    sum_mul, mul_sum, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun Z _ => ?_)
  rw [← norm_neg, neg_sub]

/-!

## C. Monotonicity of the Lieb–Robinson bound

-/

lemma chainWeight_mono {Λ Λ' : Finset V} (h : Λ ⊆ Λ') (k : ℕ) (X Y : Finset V) :
    Φ.chainWeight Λ k X Y ≤ Φ.chainWeight Λ' k X Y := by
  induction k generalizing X with
  | zero => exact le_rfl
  | succ k ih =>
    exact (sum_le_sum fun Z _ => mul_le_mul_of_nonneg_left (ih Z) (norm_nonneg _)).trans
      (sum_le_sum_of_subset_of_nonneg (touching_mono h X) fun Z _ _ =>
        mul_nonneg (norm_nonneg _) (chainWeight_nonneg Λ' k Z Y))

/-- The Lieb–Robinson series grows with the time and the region. -/
lemma tsum_lrCoeff_mul_chainWeight_mono {J : ℝ} (hJ : Φ.IsBoundedBy J) {Λ Λ' : Finset V}
    (h : Λ ⊆ Λ') (X Y : Finset V) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∑' k, lrCoeff k s * Φ.chainWeight Λ k X Y ≤ ∑' k, lrCoeff k t * Φ.chainWeight Λ' k X Y :=
  (summable_lrCoeff_mul_chainWeight hJ.max_zero (le_max_right J 0) Λ X Y hs).tsum_le_tsum
    (fun k => mul_le_mul (lrCoeff_mono k hs hst) (chainWeight_mono h k X Y)
      (chainWeight_nonneg Λ k X Y) (lrCoeff_nonneg k (hs.trans hst)))
    (summable_lrCoeff_mul_chainWeight hJ.max_zero (le_max_right J 0) Λ' X Y (hs.trans hst))

/-- Summing the chain weights against the last interaction term gives the weight of all chains
one step longer. -/
lemma sum_norm_mul_chainWeight (Λ : Finset V) (k : ℕ) (X : Finset V) :
    ∑ Z ∈ Λ.powerset, ‖Φ.term Z‖ * Φ.chainWeight Λ k X Z = Φ.chainWeightAll Λ (k + 1) X := by
  induction k generalizing X with
  | zero =>
    simp only [chainWeight, chainWeightAll, mul_ite, mul_zero, mul_one, sum_ite,
      sum_const_zero, zero_add, touching]
    exact sum_congr (filter_congr fun Z _ => by rw [disjoint_comm]) fun _ _ => rfl
  | succ k ih =>
    rw [chainWeightAll]
    simp only [chainWeight, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun W _ => ?_
    rw [← ih W, mul_sum]
    exact sum_congr rfl fun Z _ => by ring

/-!

## D. Reachable sets

-/

/-- The sites reached from `X` by one nonzero interaction term: `X` together with every region
`Z` meeting `X` with `Φ(Z) ≠ 0`. It is finite by local finiteness. -/
def reachStep (hfin : Φ.LocallyFinite) (X : Finset V) : Finset V :=
  X ∪ X.biUnion fun x => (hfin x).toFinset.biUnion id

/-- The sites reached from `X` by chains of `k` nonzero interaction terms. -/
def reach (hfin : Φ.LocallyFinite) (k : ℕ) (X : Finset V) : Finset V := (reachStep hfin)^[k] X

variable (hfin : Φ.LocallyFinite)

lemma subset_reachStep (X : Finset V) : X ⊆ reachStep hfin X := subset_union_left

lemma subset_reachStep_of {X Z : Finset V} (hZ : Φ.term Z ≠ 0) (h : ¬Disjoint Z X) :
    Z ⊆ reachStep hfin X := by
  obtain ⟨x, hxZ, hxX⟩ := not_disjoint_iff.mp h
  refine subset_union_right.trans' ((subset_biUnion_of_mem _ hxX).trans' ?_)
  exact subset_biUnion_of_mem id ((hfin x).mem_toFinset.mpr ⟨hxZ, hZ⟩)

lemma reachStep_mono : Monotone (reachStep hfin) := fun _ _ h =>
  union_subset_union h (biUnion_subset_biUnion_of_subset_left _ h)

lemma reach_zero (X : Finset V) : reach hfin 0 X = X := rfl

lemma reach_succ (k : ℕ) (X : Finset V) : reach hfin (k + 1) X = reach hfin k (reachStep hfin X) :=
  Function.iterate_succ_apply _ _ _

lemma reach_succ' (k : ℕ) (X : Finset V) :
    reach hfin (k + 1) X = reachStep hfin (reach hfin k X) :=
  Function.iterate_succ_apply' _ _ _

lemma reach_mono (k : ℕ) : Monotone (reach hfin k) := (reachStep_mono hfin).iterate k

lemma reach_subset_reach {k l : ℕ} (hkl : k ≤ l) (X : Finset V) :
    reach hfin k X ⊆ reach hfin l X := by
  induction l, hkl using Nat.le_induction with
  | base => exact subset_rfl
  | succ l _ ih => exact ih.trans (by rw [reach_succ']; exact subset_reachStep hfin _)

lemma subset_reach (k : ℕ) (X : Finset V) : X ⊆ reach hfin k X :=
  reach_subset_reach hfin (Nat.zero_le k) X

/-- A region carrying a nonzero chain weight from `X` meets the sites reached in `k` steps. -/
lemma not_disjoint_reach_of_chainWeight_ne_zero (Λ : Finset V) (k : ℕ) {X Z : Finset V}
    (hw : Φ.chainWeight Λ k X Z ≠ 0) : ¬Disjoint Z (reach hfin k X) := by
  induction k generalizing X with
  | zero =>
    simp only [chainWeight, ne_eq, ite_eq_left_iff, Classical.not_imp] at hw
    rw [reach_zero, disjoint_comm]; exact hw.1
  | succ k ih =>
    obtain ⟨W, hW, hW0⟩ := exists_ne_zero_of_sum_ne_zero hw
    have hW1 : Φ.term W ≠ 0 := fun h0 => hW0 (by rw [h0, norm_zero, zero_mul])
    have hW2 : Φ.chainWeight Λ k W Z ≠ 0 := fun h0 => hW0 (by rw [h0, mul_zero])
    rw [reach_succ]
    exact fun hd => ih hW2 (hd.mono_right (reach_mono hfin k
      (subset_reachStep_of hfin hW1 (mem_touching.mp hW).2)))

lemma subset_reach_of_chainWeight_ne_zero (Λ : Finset V) (k : ℕ) {X Z : Finset V}
    (hZ : Φ.term Z ≠ 0) (hw : Φ.chainWeight Λ k X Z ≠ 0) : Z ⊆ reach hfin (k + 1) X := by
  rw [reach_succ']
  exact subset_reachStep_of hfin hZ (not_disjoint_reach_of_chainWeight_ne_zero hfin Λ k hw)

/-- If `Λ` contains the sites reached in `k + 1` steps, no new term of a larger region carries
a chain weight of length `k`. -/
lemma sum_newTerms_eq_zero {k : ℕ} {X Λ : Finset V} (hΛ : reach hfin (k + 1) X ⊆ Λ)
    (Λ' : Finset V) : ∑ Z ∈ newTerms Λ Λ', ‖Φ.term Z‖ * Φ.chainWeight Λ' k X Z = 0 := by
  refine sum_eq_zero fun Z hZ => ?_
  by_contra hne
  have hZ0 : Φ.term Z ≠ 0 := fun h0 => hne (by rw [h0, norm_zero, zero_mul])
  have hw : Φ.chainWeight Λ' k X Z ≠ 0 := fun h0 => hne (by rw [h0, mul_zero])
  exact (mem_sdiff.mp hZ).2 (mem_powerset.mpr
    ((subset_reach_of_chainWeight_ne_zero hfin Λ' k hZ0 hw).trans hΛ))

/-!

## E. The Cauchy estimate

-/

/-- The majorant `e_k(T) max(1, |X|) J^{k+1}` of the terms of the Cauchy estimate. -/
def lrMajorant (J T : ℝ) (X : Finset V) (k : ℕ) : ℝ := lrCoeff k T * (max 1 (#X : ℝ) * J ^ (k + 1))

omit [DecidableEq V] in
lemma lrMajorant_nonneg {J T : ℝ} (hJ0 : 0 ≤ J) (hT : 0 ≤ T) (X : Finset V) (k : ℕ) :
    0 ≤ lrMajorant J T X k :=
  mul_nonneg (lrCoeff_nonneg k hT) (mul_nonneg (by positivity) (pow_nonneg hJ0 _))

omit [DecidableEq V] in
lemma summable_lrMajorant (J : ℝ) {T : ℝ} (X : Finset V) : Summable (lrMajorant J T X) := by
  refine ((Real.summable_pow_div_factorial (2 * T * J)).mul_left (max 1 (#X : ℝ) * J)).congr
    fun k => ?_
  simp only [lrMajorant, lrCoeff, mul_pow, pow_succ]
  ring

/-- The tail `Σ_{k ≥ K} e_k(T) max(1, |X|) J^{k+1}` of the Cauchy estimate. -/
def lrTail (J T : ℝ) (X : Finset V) (K : ℕ) : ℝ := ∑' k, lrMajorant J T X (k + K)

omit [DecidableEq V] in
lemma tendsto_lrTail (J T : ℝ) (X : Finset V) :
    Tendsto (lrTail J T X) atTop (𝓝 0) :=
  tendsto_sum_nat_add (lrMajorant J T X)

omit [DecidableEq V] in
lemma mul_sum_eq_sum_mul_lrCoeff (c : ℝ) (s : Finset (Finset V)) (f : Finset V → ℝ)
    (w : Finset V → ℝ) : c * ∑ Z ∈ s, w Z * f Z = ∑ Z ∈ s, w Z * (c * f Z) := by
  rw [mul_sum]; exact sum_congr rfl fun Z _ => by ring

/-- The new terms of `Λ'`, weighted with the Lieb–Robinson series of `X`, are bounded by the
tail of the series once `Λ` contains the sites reached from `X` in `K` steps. -/
lemma sum_newTerms_le_lrTail {J : ℝ} (hJ : Φ.IsBoundedBy J) (hJ0 : 0 ≤ J) {K : ℕ}
    {X Λ : Finset V} (hΛ : reach hfin K X ⊆ Λ) (Λ' : Finset V) {T : ℝ} (hT : 0 ≤ T) :
    ∑ Z ∈ newTerms Λ Λ', ‖Φ.term Z‖ * ∑' k, lrCoeff k T * Φ.chainWeight Λ' k X Z ≤
      lrTail J T X K := by
  have hsum : ∀ Z, Summable fun k => ‖Φ.term Z‖ * (lrCoeff k T * Φ.chainWeight Λ' k X Z) :=
    fun Z => (summable_lrCoeff_mul_chainWeight hJ hJ0 Λ' X Z hT).mul_left _
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun Z _ => hsum Z, lrTail,
    ← zero_add (∑' k, lrMajorant J T X (k + K))]
  let g : ℕ → ℝ := fun k => if k < K then 0 else lrMajorant J T X k
  have hg : Summable g := (summable_lrMajorant J X).of_nonneg_of_le
    (fun k => by unfold g; split_ifs; exacts [le_rfl, lrMajorant_nonneg hJ0 hT X k])
    fun k => by unfold g; split_ifs; exacts [lrMajorant_nonneg hJ0 hT X k, le_rfl]
  have hg' : ∑' k, g k = 0 + ∑' k, lrMajorant J T X (k + K) := by
    rw [← hg.sum_add_tsum_nat_add K, sum_eq_zero fun k hk => ite_eq_left (mem_range.mp hk)]
    exact congrArg _ (tsum_congr fun k => ite_eq_right (by omega))
  rw [← hg']
  refine (summable_sum fun Z _ => hsum Z).tsum_le_tsum (fun k => ?_) hg
  unfold g
  split_ifs with hk
  · rw [← mul_sum_eq_sum_mul_lrCoeff, sum_newTerms_eq_zero hfin
      ((reach_subset_reach hfin hk X).trans hΛ) Λ', mul_zero]
  · rw [← mul_sum_eq_sum_mul_lrCoeff, lrMajorant]
    refine mul_le_mul_of_nonneg_left ?_ (lrCoeff_nonneg k hT)
    calc ∑ Z ∈ newTerms Λ Λ', ‖Φ.term Z‖ * Φ.chainWeight Λ' k X Z
        ≤ ∑ Z ∈ Λ'.powerset, ‖Φ.term Z‖ * Φ.chainWeight Λ' k X Z :=
          sum_le_sum_of_subset_of_nonneg sdiff_subset fun Z _ _ =>
            mul_nonneg (norm_nonneg _) (chainWeight_nonneg Λ' k X Z)
      _ = Φ.chainWeightAll Λ' (k + 1) X := sum_norm_mul_chainWeight Λ' k X
      _ ≤ max 1 (#X : ℝ) * J ^ (k + 1) := chainWeightAll_le hJ hJ0 Λ' (k + 1) X

/-- The Cauchy estimate for `0 ≤ t ≤ T`: if `Λ` contains the sites reached from `X` in `K`
steps and `Λ ⊆ Λ'`, then `‖α_t^{Λ'}(A) - α_t^Λ(A)‖ ≤ 2 ‖A‖ T · Σ_{k ≥ K} e_k(T) max(1, |X|)
J^{k+1}` for `A ∈ 𝔄_X`. -/
lemma norm_evolution_sub_le_tail {J : ℝ} (hJ : Φ.IsBoundedBy J) (hJ0 : 0 ≤ J) {K : ℕ}
    {X Λ Λ' : Finset V} (hΛ : reach hfin K X ⊆ Λ) (h : Λ ⊆ Λ') {A : 𝔄} (hA : A ∈ N.loc X)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    ‖evolution (Φ.hamiltonian Λ') t A - evolution (Φ.hamiltonian Λ) t A‖ ≤
      2 * ‖A‖ * lrTail J T X K * T := by
  have hX : X ⊆ Λ := (subset_reach hfin K X).trans hΛ
  have hT : 0 ≤ T := ht.trans htT
  have hC : 0 ≤ 2 * ‖A‖ * lrTail J T X K :=
    mul_nonneg (by positivity) (tsum_nonneg fun k => lrMajorant_nonneg hJ0 hT X _)
  refine (norm_evolution_sub_evolution_le _ _ A ht fun r hr hrt => ?_).trans
    (mul_le_mul_of_nonneg_left htT hC)
  calc _ ≤ ∑ Z ∈ newTerms Λ Λ', ‖evolution (Φ.hamiltonian Λ) r A * Φ.term Z -
          Φ.term Z * evolution (Φ.hamiltonian Λ) r A‖ :=
        Φ.norm_commutator_hamiltonian_sub_le h
          (Φ.evolution_hamiltonian_mem Λ r (N.loc_mono hX hA))
    _ ≤ ∑ Z ∈ newTerms Λ Λ', 2 * ‖A‖ * ‖Φ.term Z‖ *
          ∑' k, lrCoeff k T * Φ.chainWeight Λ' k X Z := sum_le_sum fun Z _ =>
        (Φ.lieb_robinson hJ Λ Z (Φ.term_mem Z) (Φ.isEven_term Z) hX hA hr).trans
          (mul_le_mul_of_nonneg_left (tsum_lrCoeff_mul_chainWeight_mono hJ h X Z hr
            (hrt.trans htT)) (by positivity))
    _ = 2 * ‖A‖ * ∑ Z ∈ newTerms Λ Λ', ‖Φ.term Z‖ *
          ∑' k, lrCoeff k T * Φ.chainWeight Λ' k X Z := by
        rw [mul_sum]; exact sum_congr rfl fun Z _ => by ring
    _ ≤ 2 * ‖A‖ * lrTail J T X K :=
        mul_le_mul_of_nonneg_left (sum_newTerms_le_lrTail hfin hJ hJ0 hΛ Λ' hT) (by positivity)

/-!

## F. Negative times

-/

lemma reachStep_neg (X : Finset V) : reachStep hfin.neg X = reachStep hfin X := by
  ext v; simp [reachStep, neg_term]

lemma reach_neg (k : ℕ) (X : Finset V) : reach hfin.neg k X = reach hfin k X := by
  unfold reach
  rw [show reachStep hfin.neg = reachStep hfin from funext (reachStep_neg hfin)]

/-- The Cauchy estimate for `|t| ≤ T`. -/
lemma norm_evolution_sub_le_tail_abs {J : ℝ} (hJ : Φ.IsBoundedBy J) (hJ0 : 0 ≤ J) {K : ℕ}
    {X Λ Λ' : Finset V} (hΛ : reach hfin K X ⊆ Λ) (h : Λ ⊆ Λ') {A : 𝔄} (hA : A ∈ N.loc X)
    {t T : ℝ} (htT : |t| ≤ T) :
    ‖evolution (Φ.hamiltonian Λ') t A - evolution (Φ.hamiltonian Λ) t A‖ ≤
      2 * ‖A‖ * lrTail J T X K * T := by
  rcases le_total 0 t with ht | ht
  · exact norm_evolution_sub_le_tail hfin hJ hJ0 hΛ h hA ht ((le_abs_self t).trans htT)
  · have h' := norm_evolution_sub_le_tail hfin.neg hJ.neg hJ0 ((reach_neg hfin K X).symm ▸ hΛ)
      h hA (neg_nonneg.mpr ht) ((neg_le_abs t).trans htT)
    simpa only [evolution_hamiltonian_neg, neg_neg] using h'

/-!

## G. Uniform convergence for local observables

-/

include hfin in
/-- The finite-volume dynamics of a local observable are uniformly Cauchy on `[-T, T]` as `Λ`
grows. -/
lemma uniformCauchySeqOn_evolution {J : ℝ} (hJ : Φ.IsBoundedBy J) {X : Finset V} {A : 𝔄}
    (hA : A ∈ N.loc X) (T : ℝ) :
    UniformCauchySeqOn (fun Λ t => evolution (Φ.hamiltonian Λ) t A) atTop (Set.Icc (-T) T) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  have h := (tendsto_lrTail (max J 0) T X).const_mul (4 * ‖A‖ * T)
  rw [mul_zero] at h
  obtain ⟨K, hK⟩ := (h.eventually (gt_mem_nhds hε)).exists
  refine ⟨reach hfin K X, fun m hm n hn t ht => ?_⟩
  have habs : |t| ≤ T := abs_le.mpr ht
  have h1 := norm_evolution_sub_le_tail_abs hfin hJ.max_zero (le_max_right J 0)
    hm subset_union_left hA habs (Λ' := m ∪ n)
  have h2 := norm_evolution_sub_le_tail_abs hfin hJ.max_zero (le_max_right J 0)
    hn subset_union_right hA habs (Λ' := m ∪ n)
  rw [dist_eq_norm]
  calc _ ≤ ‖evolution (Φ.hamiltonian (m ∪ n)) t A - evolution (Φ.hamiltonian m) t A‖ +
        ‖evolution (Φ.hamiltonian (m ∪ n)) t A - evolution (Φ.hamiltonian n) t A‖ := by
        rw [norm_sub_rev _ (evolution (Φ.hamiltonian m) t A)]
        exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add h1 h2
    _ < ε := by linarith

end Interaction

end LatticeFermions
