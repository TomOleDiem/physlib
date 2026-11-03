/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.LatticeFermions.Interaction
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.Order.Floor

/-!

# The Lieb–Robinson bound for graded local nets

For an even element `B` of `𝔄_Y` and any `A ∈ 𝔄_X`, the commutator `[α_t(A), B]` of the
finite-volume dynamics is bounded by a series in `t` whose coefficients are weighted chains of
interaction terms leading from `X` to `Y`. The bound does not depend on the region `Λ` beyond the
chains it contains, and not at all on the on-site terms.

## i. Overview

Let `H = H_Λ`, `α_t` its dynamics, `A ∈ 𝔄_X` with `X ⊆ Λ` and `B ∈ 𝔄_Y` even. Write
`K = K_X` for the sum of the interaction terms meeting `X` and `β_t` for the dynamics of `H - K`.
The derivative of `s ↦ β_s(α_{-s}(B))` is `-β_s(i[K, α_{-s}(B)])`, whose norm is
`‖[α_s(K), B]‖`. Since `β_t` maps `𝔄_X` into itself (the on-site terms are absorbed here), the
element `A' = β_t(A)` lies in `𝔄_X`, and

`‖[α_t(A), B]‖ = ‖[A', β_t(α_{-t}(B))]‖ ≤ ‖[A', B]‖ + 2 ‖A‖ ∫_0^t ‖[α_s(K), B]‖ ds`.

The first term vanishes if `X ∩ Y = ∅` by even-odd locality, and is at most `2 ‖A‖ ‖B‖`
otherwise. Iterating this inequality for the terms `Φ(Z)` of `K` gives, with `e_k(t) = (2t)^k/k!`,

`‖[α_t(A), B]‖ ≤ 2 ‖A‖ ‖B‖ Σ_k e_k(t) w_k(X, Y)`,

where the *chain weight* `w_k(X, Y)` sums `‖Φ(Z_1)‖ ⋯ ‖Φ(Z_k)‖` over chains of subregions of `Λ`
with `Z_1` meeting `X`, `Z_{i+1}` meeting `Z_i`, and `Z_k` meeting `Y`. The iteration is an
induction over the number of steps with a remainder `e_n(t) W_n(X)`, where `W_n(X)` drops the
condition on `Z_n`; the fencing inequality of the mean value theorem replaces the integrals. The
bound `Σ_{Z ∋ x} |Z| ‖Φ(Z)‖ ≤ J` gives `W_n(X) ≤ max(1, |X|) J^n`, so the remainder tends to zero.

The proof only uses ordinary commutators with the even element `B`: this is why even-odd
locality suffices, and why the abstract statement covers spin systems (trivial parity) and
fermions at once.

## ii. Key results

- `LatticeFermions.norm_commutator_twisted_le` : the analytic step, for any `H`, `K`, `A`, `B`.
- `LatticeFermions.Interaction.chainWeight` : the chain weights `w_k(X, Y)`.
- `LatticeFermions.Interaction.chainWeightAll_le` : `W_n(X) ≤ max(1, |X|) J^n`.
- `LatticeFermions.Interaction.norm_commutator_le_lrPartial` : the bound after `n` steps.
- `LatticeFermions.Interaction.lieb_robinson` : the Lieb–Robinson bound.

## iii. Table of contents

- A. Commutator norms
- B. The analytic step
- C. Chain weights
- D. The bound after finitely many steps
- E. The Lieb–Robinson bound

## iv. References

* B. Nachtergaele, R. Sims, A. Young, Lieb-Robinson bounds, the spectral flow, and stability of
  the spectral gap for lattice fermion systems, arXiv:1705.08553, Section 3.
* B. Nachtergaele, R. Sims, A. Young, Quasi-locality bounds for quantum lattice systems. Part I,
  arXiv:1810.02428, Section 3.

-/

@[expose] public section

noncomputable section

namespace LatticeFermions

open Finset Complex Nat Filter Topology

/-!

## A. Commutator norms

-/

section commutator

variable {𝔄 : Type*} [CStarAlgebra 𝔄]

lemma norm_mul_sub_mul_le (a b : 𝔄) : ‖a * b - b * a‖ ≤ 2 * ‖a‖ * ‖b‖ :=
  calc ‖a * b - b * a‖ ≤ ‖a * b‖ + ‖b * a‖ := norm_sub_le _ _
    _ ≤ ‖a‖ * ‖b‖ + ‖b‖ * ‖a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖a‖ * ‖b‖ := by ring

lemma evolution_mul_sub_mul (H : selfAdjoint 𝔄) (t : ℝ) (a b : 𝔄) :
    evolution H t (a * b - b * a) = evolution H t a * evolution H t b -
      evolution H t b * evolution H t a := by
  rw [map_sub, map_mul, map_mul]

/-- The commutator norm is invariant under the dynamics. -/
lemma norm_commutator_evolution (H : selfAdjoint 𝔄) (t : ℝ) (a b : 𝔄) :
    ‖evolution H t a * evolution H t b - evolution H t b * evolution H t a‖ =
      ‖a * b - b * a‖ := by
  rw [← evolution_mul_sub_mul, norm_evolution]

end commutator

/-!

## B. The analytic step

-/

section step

variable {𝔄 : Type*} [CStarAlgebra 𝔄]

/-- The element `β_s(α_{-s}(B))`, where `α` is the dynamics of `H` and `β` that of `H - K`. -/
def twisted (H K : selfAdjoint 𝔄) (B : 𝔄) (s : ℝ) : 𝔄 :=
  evolution (H - K) s (evolution H (-s) B)

lemma twisted_zero (H K : selfAdjoint 𝔄) (B : 𝔄) : twisted H K B 0 = B := by
  simp [twisted, evolution_zero]

lemma hasDerivAt_evolution_neg (H : selfAdjoint 𝔄) (B : 𝔄) (s : ℝ) :
    HasDerivAt (fun r => evolution H (-r) B)
      (-(I • ((H : 𝔄) * evolution H (-s) B - evolution H (-s) B * H))) s := by
  have h := hasDerivAt_evolution (-H) B s
  simp only [evolution_neg_hamiltonian] at h
  convert h using 1
  have hH : evolution H (-s) (H : 𝔄) = H := evolution_self H (-s)
  rw [map_smul, map_sub, map_mul, map_mul, AddSubgroup.coe_neg, map_neg, hH]
  simp only [neg_mul, mul_neg, sub_neg_eq_add, smul_add, smul_neg, smul_sub, neg_sub]
  abel

/-- The derivative of `s ↦ β_s(α_{-s}(B))` is `-β_s(i[K, α_{-s}(B)])`. -/
lemma hasDerivAt_twisted (H K : selfAdjoint 𝔄) (B : 𝔄) (s : ℝ) :
    HasDerivAt (twisted H K B) (evolution (H - K) s
      (-(I • ((K : 𝔄) * evolution H (-s) B - evolution H (-s) B * K)))) s := by
  have h := hasDerivAt_evolution_comp (H - K) (hasDerivAt_evolution_neg H B s)
  change HasDerivAt (fun r => evolution (H - K) r (evolution H (-r) B)) _ s
  convert h using 2
  rw [AddSubgroup.coe_sub]
  simp only [sub_mul, mul_sub, smul_sub, neg_sub]
  abel

lemma norm_deriv_twisted (H K : selfAdjoint 𝔄) (B : 𝔄) (s : ℝ) :
    ‖evolution (H - K) s (-(I • ((K : 𝔄) * evolution H (-s) B - evolution H (-s) B * K)))‖ =
      ‖evolution H s K * B - B * evolution H s K‖ := by
  rw [norm_evolution, norm_neg, norm_smul, Complex.norm_I, one_mul,
    ← norm_evolution H s, evolution_mul_sub_mul, evolution_evolution_neg]

/-- The analytic step of the Lieb–Robinson bound: if `b` bounds `‖[A, B]‖` at time zero and its
derivative bounds `2 ‖A‖ ‖[α_s(K), B]‖`, then `b(t)` bounds `‖[A, β_t(α_{-t}(B))]‖`. -/
lemma norm_commutator_twisted_le (H K : selfAdjoint 𝔄) (A B : 𝔄) {b b' : ℝ → ℝ}
    (hb : ∀ s, HasDerivAt b (b' s) s) (h0 : ‖A * B - B * A‖ ≤ b 0)
    (hd : ∀ s, 0 ≤ s → 2 * ‖A‖ * ‖evolution H s K * B - B * evolution H s K‖ ≤ b' s)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖A * twisted H K B t - twisted H K B t * A‖ ≤ b t := by
  have hf : ∀ s, HasDerivAt (fun r => A * twisted H K B r - twisted H K B r * A)
      (A * _ - _ * A) s := fun s =>
    ((hasDerivAt_twisted H K B s).const_mul A).sub ((hasDerivAt_twisted H K B s).mul_const A)
  refine image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun s _ => (hf s).continuousAt.continuousWithinAt) (fun s _ => (hf s).hasDerivWithinAt)
    (by simpa [twisted_zero] using h0) hb (fun s hs => ?_) ⟨ht, le_rfl⟩
  refine (norm_mul_sub_mul_le _ _).trans ?_
  rw [norm_deriv_twisted]
  exact hd s hs.1

end step

/-!

## C. Chain weights

-/

namespace Interaction

variable {V : Type*} [DecidableEq V] {𝔄 : Type*} [CStarAlgebra 𝔄] {N : GradedLocalNet V 𝔄}
  (Φ : Interaction N)

/-- The chain weight `w_k(X, Y)` in `Λ`: the sum of `‖Φ(Z_1)‖ ⋯ ‖Φ(Z_k)‖` over chains of
subregions of `Λ` with `Z_1` meeting `X`, `Z_{i+1}` meeting `Z_i` and `Z_k` meeting `Y`; for
`k = 0` it is one if `X` meets `Y` and zero otherwise. -/
def chainWeight (Λ : Finset V) : ℕ → Finset V → Finset V → ℝ
  | 0, X, Y => if Disjoint X Y then 0 else 1
  | k + 1, X, Y => ∑ Z ∈ touching Λ X, ‖Φ.term Z‖ * chainWeight Λ k Z Y

/-- The weight `W_k(X)` of all chains of length `k` starting at `X` in `Λ`. -/
def chainWeightAll (Λ : Finset V) : ℕ → Finset V → ℝ
  | 0, _ => 1
  | k + 1, X => ∑ Z ∈ touching Λ X, ‖Φ.term Z‖ * chainWeightAll Λ k Z

variable {Φ}

lemma chainWeight_nonneg (Λ : Finset V) (k : ℕ) (X Y : Finset V) :
    0 ≤ Φ.chainWeight Λ k X Y := by
  induction k generalizing X with
  | zero => simp only [chainWeight]; split_ifs <;> norm_num
  | succ k ih => exact sum_nonneg fun Z _ => mul_nonneg (norm_nonneg _) (ih Z)

lemma chainWeightAll_nonneg (Λ : Finset V) (k : ℕ) (X : Finset V) :
    0 ≤ Φ.chainWeightAll Λ k X := by
  induction k generalizing X with
  | zero => simp [chainWeightAll]
  | succ k ih => exact sum_nonneg fun Z _ => mul_nonneg (norm_nonneg _) (ih Z)

lemma chainWeight_le_chainWeightAll (Λ : Finset V) (k : ℕ) (X Y : Finset V) :
    Φ.chainWeight Λ k X Y ≤ Φ.chainWeightAll Λ k X := by
  induction k generalizing X with
  | zero => simp only [chainWeight, chainWeightAll]; split_ifs <;> norm_num
  | succ k ih => exact sum_le_sum fun Z _ => mul_le_mul_of_nonneg_left (ih Z) (norm_nonneg _)

lemma chainWeight_zero_of_disjoint (Λ : Finset V) {X Y : Finset V} (h : Disjoint X Y) :
    Φ.chainWeight Λ 0 X Y = 0 := by
  simp [chainWeight, h]

/-- The sum of `|Z| ‖Φ(Z)‖` over the subregions of `Λ` meeting `X` is at most `|X| J`. -/
lemma sum_touching_card_mul_le {J : ℝ} (hJ : Φ.IsBoundedBy J) (Λ X : Finset V) :
    ∑ Z ∈ touching Λ X, (#Z : ℝ) * ‖Φ.term Z‖ ≤ #X * J := by
  calc ∑ Z ∈ touching Λ X, (#Z : ℝ) * ‖Φ.term Z‖
      ≤ ∑ Z ∈ touching Λ X, ∑ x ∈ X, if x ∈ Z then (#Z : ℝ) * ‖Φ.term Z‖ else 0 := by
        refine sum_le_sum fun Z hZ => ?_
        obtain ⟨x, hxZ, hxX⟩ := not_disjoint_iff.mp (mem_touching.mp hZ).2
        rw [← sum_filter]
        exact single_le_sum (f := fun _ => (#Z : ℝ) * ‖Φ.term Z‖)
          (fun _ _ => by positivity) (mem_filter.mpr ⟨hxX, hxZ⟩)
    _ = ∑ x ∈ X, ∑ Z ∈ (touching Λ X).filter (x ∈ ·), (#Z : ℝ) * ‖Φ.term Z‖ := by
        rw [sum_comm]; exact sum_congr rfl fun x _ => (sum_filter _ _).symm
    _ ≤ ∑ x ∈ X, J := sum_le_sum fun x _ =>
        (sum_le_sum_of_subset_of_nonneg
          (fun Z hZ => mem_filter.mpr ⟨mem_powerset.mpr (mem_touching.mp (mem_filter.mp hZ).1).1,
            (mem_filter.mp hZ).2⟩) fun _ _ _ => by positivity).trans (hJ x Λ)
    _ = #X * J := by rw [sum_const, nsmul_eq_mul]

/-- The weight of all chains of length `n` is at most `max(1, |X|) J^n`. -/
lemma chainWeightAll_le {J : ℝ} (hJ : Φ.IsBoundedBy J) (hJ0 : 0 ≤ J) (Λ : Finset V) (n : ℕ)
    (X : Finset V) : Φ.chainWeightAll Λ n X ≤ max 1 (#X : ℝ) * J ^ n := by
  induction n generalizing X with
  | zero => simp [chainWeightAll]
  | succ n ih =>
    calc Φ.chainWeightAll Λ (n + 1) X
        ≤ ∑ Z ∈ touching Λ X, ‖Φ.term Z‖ * ((#Z : ℝ) * J ^ n) := by
          refine sum_le_sum fun Z hZ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have hne : Z.Nonempty := (not_disjoint_iff_nonempty_inter.mp
            (mem_touching.mp hZ).2).mono inter_subset_left
          have h1 : (1 : ℝ) ≤ #Z := by exact_mod_cast hne.card_pos
          simpa [max_eq_right h1] using ih Z
      _ = (∑ Z ∈ touching Λ X, (#Z : ℝ) * ‖Φ.term Z‖) * J ^ n := by
          rw [sum_mul]; exact sum_congr rfl fun Z _ => by ring
      _ ≤ (#X * J) * J ^ n := mul_le_mul_of_nonneg_right (sum_touching_card_mul_le hJ Λ X)
          (pow_nonneg hJ0 n)
      _ ≤ max 1 (#X : ℝ) * J ^ (n + 1) := by
          rw [pow_succ, mul_assoc, mul_comm J]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-!

## D. The bound after finitely many steps

-/

/-- The coefficient `e_k(t) = (2t)^k / k!` of the Lieb–Robinson series. -/
def lrCoeff (k : ℕ) (t : ℝ) : ℝ := (2 * t) ^ k / k !

lemma lrCoeff_zero_left (t : ℝ) : lrCoeff 0 t = 1 := by simp [lrCoeff]

lemma lrCoeff_succ_zero (k : ℕ) : lrCoeff (k + 1) 0 = 0 := by simp [lrCoeff]

lemma lrCoeff_nonneg (k : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ lrCoeff k t := by
  unfold lrCoeff; positivity

lemma lrCoeff_mono (k : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : lrCoeff k s ≤ lrCoeff k t := by
  unfold lrCoeff
  gcongr

lemma hasDerivAt_lrCoeff_succ (k : ℕ) (t : ℝ) :
    HasDerivAt (lrCoeff (k + 1)) (2 * lrCoeff k t) t := by
  have h := (((hasDerivAt_id t).const_mul 2).pow (k + 1)).div_const ((k + 1)! : ℝ)
  convert h using 1
  · funext s; simp [lrCoeff]
  · simp only [lrCoeff, id, mul_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ,
      Nat.add_sub_cancel]
    field_simp

/-- The Lieb–Robinson bound after `n` steps: `Σ_{k < n} e_k(t) w_k(X, Y) + e_n(t) W_n(X)`. -/
def lrPartial (Φ : Interaction N) (Λ Y : Finset V) (n : ℕ) (X : Finset V) (t : ℝ) : ℝ :=
  ∑ k ∈ range n, lrCoeff k t * Φ.chainWeight Λ k X Y + lrCoeff n t * Φ.chainWeightAll Λ n X

lemma lrPartial_zero (Λ Y X : Finset V) (t : ℝ) : Φ.lrPartial Λ Y 0 X t = 1 := by
  simp [lrPartial, lrCoeff_zero_left, chainWeightAll]

lemma lrPartial_succ_zero (Λ Y : Finset V) (n : ℕ) (X : Finset V) :
    Φ.lrPartial Λ Y (n + 1) X 0 = Φ.chainWeight Λ 0 X Y := by
  simp [lrPartial, sum_range_succ', lrCoeff_succ_zero, lrCoeff_zero_left]

lemma lrPartial_succ_eq (Λ Y : Finset V) (n : ℕ) (X : Finset V) (t : ℝ) :
    Φ.lrPartial Λ Y (n + 1) X t = Φ.chainWeight Λ 0 X Y +
      (∑ k ∈ range n, lrCoeff (k + 1) t * Φ.chainWeight Λ (k + 1) X Y +
        lrCoeff (n + 1) t * Φ.chainWeightAll Λ (n + 1) X) := by
  rw [lrPartial, sum_range_succ', lrCoeff_zero_left, one_mul]
  ring

/-- The derivative of the bound after `n + 1` steps is `2 Σ_{Z ∩ X ≠ ∅} ‖Φ(Z)‖` times the bound
after `n` steps at `Z`. -/
lemma hasDerivAt_lrPartial (Λ Y : Finset V) (n : ℕ) (X : Finset V) (t : ℝ) :
    HasDerivAt (Φ.lrPartial Λ Y (n + 1) X)
      (2 * ∑ Z ∈ touching Λ X, ‖Φ.term Z‖ * Φ.lrPartial Λ Y n Z t) t := by
  have h := (hasDerivAt_const t (Φ.chainWeight Λ 0 X Y)).add
    ((HasDerivAt.fun_sum (u := range n) fun k _ =>
      (hasDerivAt_lrCoeff_succ k t).mul_const (Φ.chainWeight Λ (k + 1) X Y)).add
      ((hasDerivAt_lrCoeff_succ n t).mul_const (Φ.chainWeightAll Λ (n + 1) X)))
  convert h using 1
  · exact funext (lrPartial_succ_eq Λ Y n X)
  · simp only [lrPartial, chainWeight, chainWeightAll, mul_add, mul_sum, sum_add_distrib,
      zero_add]
    rw [sum_comm]
    congr 1
    · exact sum_congr rfl fun k _ => sum_congr rfl fun Z _ => by ring
    · exact sum_congr rfl fun Z _ => by ring

/-- The commutator with `B` of the dynamics of `K_X` is bounded by the sum over the terms. -/
lemma norm_commutator_interactionAt_le (H : selfAdjoint 𝔄) (Λ X : Finset V) (s : ℝ) (B : 𝔄) :
    ‖evolution H s (Φ.interactionAt Λ X) * B - B * evolution H s (Φ.interactionAt Λ X)‖ ≤
      ∑ Z ∈ touching Λ X, ‖evolution H s (Φ.term Z) * B - B * evolution H s (Φ.term Z)‖ := by
  rw [interactionAt_coe, map_sum, sum_mul, mul_sum, ← sum_sub_distrib]
  exact norm_sum_le _ _

/-- One step of the Lieb–Robinson bound: `‖[α_t(A), B]‖ = ‖[A', β_t(α_{-t}(B))]‖` with
`A' = β_t(A)`, where `β` is the dynamics of `H_Λ - K_X`. -/
lemma norm_commutator_eq_twisted (Λ X : Finset V) (t : ℝ) (A B : 𝔄) :
    ‖evolution (Φ.hamiltonian Λ) t A * B - B * evolution (Φ.hamiltonian Λ) t A‖ =
      ‖evolution (Φ.hamiltonian Λ - Φ.interactionAt Λ X) t A *
          twisted (Φ.hamiltonian Λ) (Φ.interactionAt Λ X) B t -
        twisted (Φ.hamiltonian Λ) (Φ.interactionAt Λ X) B t *
          evolution (Φ.hamiltonian Λ - Φ.interactionAt Λ X) t A‖ := by
  rw [twisted, ← evolution_mul_sub_mul, norm_evolution]
  conv_rhs => rw [← norm_commutator_evolution (Φ.hamiltonian Λ) t]
  rw [evolution_evolution_neg]

/-- The Lieb–Robinson bound after `n` steps, for `A ∈ 𝔄_X` with `X ⊆ Λ` and `B ∈ 𝔄_Y` even:
`‖[α_t(A), B]‖ ≤ 2 ‖A‖ ‖B‖ (Σ_{k < n} e_k(t) w_k(X, Y) + e_n(t) W_n(X))` for `t ≥ 0`. -/
lemma norm_commutator_le_lrPartial (Λ Y : Finset V) {B : 𝔄} (hB : B ∈ N.loc Y)
    (hBe : N.IsEven B) (n : ℕ) :
    ∀ {X : Finset V}, X ⊆ Λ → ∀ {A : 𝔄}, A ∈ N.loc X → ∀ {t : ℝ}, 0 ≤ t →
      ‖evolution (Φ.hamiltonian Λ) t A * B - B * evolution (Φ.hamiltonian Λ) t A‖ ≤
        2 * ‖A‖ * ‖B‖ * Φ.lrPartial Λ Y n X t := by
  induction n with
  | zero =>
    intro X _ A _ t _
    rw [lrPartial_zero, mul_one, ← norm_evolution (Φ.hamiltonian Λ) t A]
    exact norm_mul_sub_mul_le _ _
  | succ n ih =>
    intro X hX A hA t ht
    have hA' := Φ.evolution_sub_interactionAt_mem hX t hA
    rw [Φ.norm_commutator_eq_twisted Λ X]
    refine norm_commutator_twisted_le _ _ _ B
      (fun s => ((Φ.hasDerivAt_lrPartial Λ Y n X s).const_mul (2 * ‖A‖ * ‖B‖))) ?_ ?_ ht
    · rw [lrPartial_succ_zero]
      by_cases hXY : Disjoint X Y
      · rw [(N.commute_of_disjoint hXY hA' hB hBe).eq, sub_self, norm_zero,
          chainWeight_zero_of_disjoint Λ hXY, mul_zero]
      · simp only [chainWeight, hXY, ite_false, mul_one]
        rw [← norm_evolution (Φ.hamiltonian Λ - Φ.interactionAt Λ X) t A]
        exact norm_mul_sub_mul_le _ _
    · intro s hs
      rw [norm_evolution]
      calc 2 * ‖A‖ * ‖evolution (Φ.hamiltonian Λ) s (Φ.interactionAt Λ X) * B -
            B * evolution (Φ.hamiltonian Λ) s (Φ.interactionAt Λ X)‖
          ≤ 2 * ‖A‖ * ∑ Z ∈ touching Λ X, 2 * ‖Φ.term Z‖ * ‖B‖ * Φ.lrPartial Λ Y n Z s := by
            refine mul_le_mul_of_nonneg_left ((Φ.norm_commutator_interactionAt_le _ Λ X s B).trans
              (sum_le_sum fun Z hZ => ?_)) (by positivity)
            exact ih ((mem_touching.mp hZ).1) (Φ.term_mem Z) hs
        _ = 2 * ‖A‖ * ‖B‖ * (2 * ∑ Z ∈ touching Λ X, ‖Φ.term Z‖ * Φ.lrPartial Λ Y n Z s) := by
            rw [mul_sum, mul_sum, mul_sum]
            exact sum_congr rfl fun Z _ => by ring

/-!

## E. The Lieb–Robinson bound

-/

lemma IsBoundedBy.max_zero {J : ℝ} (hJ : Φ.IsBoundedBy J) : Φ.IsBoundedBy (max J 0) :=
  fun x Λ => (hJ x Λ).trans (le_max_left _ _)

lemma lrCoeff_mul_chainWeightAll_le {J : ℝ} (hJ : Φ.IsBoundedBy J) (hJ0 : 0 ≤ J)
    (Λ X : Finset V) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    lrCoeff k t * Φ.chainWeightAll Λ k X ≤ max 1 (#X : ℝ) * ((2 * t * J) ^ k / k !) := by
  calc lrCoeff k t * Φ.chainWeightAll Λ k X ≤ lrCoeff k t * (max 1 (#X : ℝ) * J ^ k) :=
        mul_le_mul_of_nonneg_left (chainWeightAll_le hJ hJ0 Λ k X) (lrCoeff_nonneg k ht)
    _ = max 1 (#X : ℝ) * ((2 * t * J) ^ k / k !) := by rw [lrCoeff, mul_pow]; ring

lemma summable_lrCoeff_mul_chainWeight {J : ℝ} (hJ : Φ.IsBoundedBy J) (hJ0 : 0 ≤ J)
    (Λ X Y : Finset V) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun k => lrCoeff k t * Φ.chainWeight Λ k X Y :=
  ((Real.summable_pow_div_factorial (2 * t * J)).mul_left (max 1 (#X : ℝ))).of_nonneg_of_le
    (fun k => mul_nonneg (lrCoeff_nonneg k ht) (chainWeight_nonneg Λ k X Y))
    fun k => (mul_le_mul_of_nonneg_left (chainWeight_le_chainWeightAll Λ k X Y)
      (lrCoeff_nonneg k ht)).trans (lrCoeff_mul_chainWeightAll_le hJ hJ0 Λ X k ht)

/-- The remainder `e_n(t) W_n(X)` of the bound after `n` steps tends to zero. -/
lemma tendsto_lrCoeff_mul_chainWeightAll {J : ℝ} (hJ : Φ.IsBoundedBy J) (hJ0 : 0 ≤ J)
    (Λ X : Finset V) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => lrCoeff n t * Φ.chainWeightAll Λ n X) atTop (𝓝 0) := by
  have h := (FloorSemiring.tendsto_pow_div_factorial_atTop (2 * t * J)).const_mul
    (max 1 (#X : ℝ))
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => ?_)
    (fun n => lrCoeff_mul_chainWeightAll_le hJ hJ0 Λ X n ht)
  exact mul_nonneg (lrCoeff_nonneg n ht) (chainWeightAll_nonneg Λ n X)

lemma tendsto_lrPartial {J : ℝ} (hJ : Φ.IsBoundedBy J) (hJ0 : 0 ≤ J) (Λ Y X : Finset V)
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => Φ.lrPartial Λ Y n X t) atTop
      (𝓝 (∑' k, lrCoeff k t * Φ.chainWeight Λ k X Y)) := by
  simpa [lrPartial] using
    ((summable_lrCoeff_mul_chainWeight hJ hJ0 Λ X Y ht).hasSum.tendsto_sum_nat).add
      (tendsto_lrCoeff_mul_chainWeightAll hJ hJ0 Λ X ht)

/-- The Lieb–Robinson bound. Let `A ∈ 𝔄_X` with `X ⊆ Λ` and let `B ∈ 𝔄_Y` be even. For `t ≥ 0`,

`‖[α_t(A), B]‖ ≤ 2 ‖A‖ ‖B‖ Σ_k (2t)^k / k! · w_k(X, Y)`,

where `w_k(X, Y)` is the weight of the chains of `k` interaction terms in `Λ` from `X` to `Y`.
The on-site terms do not enter. -/
theorem lieb_robinson {J : ℝ} (hJ : Φ.IsBoundedBy J) (Λ Y : Finset V) {B : 𝔄}
    (hB : B ∈ N.loc Y) (hBe : N.IsEven B) {X : Finset V} (hX : X ⊆ Λ) {A : 𝔄}
    (hA : A ∈ N.loc X) {t : ℝ} (ht : 0 ≤ t) :
    ‖evolution (Φ.hamiltonian Λ) t A * B - B * evolution (Φ.hamiltonian Λ) t A‖ ≤
      2 * ‖A‖ * ‖B‖ * ∑' k, lrCoeff k t * Φ.chainWeight Λ k X Y :=
  ge_of_tendsto' (((tendsto_lrPartial hJ.max_zero (le_max_right J 0) Λ Y X ht)).const_mul _)
    fun n => Φ.norm_commutator_le_lrPartial Λ Y hB hBe n hX hA ht

end Interaction

end LatticeFermions
