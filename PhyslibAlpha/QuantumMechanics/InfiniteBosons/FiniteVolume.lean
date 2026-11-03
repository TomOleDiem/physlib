/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.ModelHamiltonians
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.JacobiCarleman
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.EssentialSelfAdjoint
/-!

# The finite-volume Bose-Hubbard Hamiltonian with pairing

The Hamiltonian of a finite region with an arbitrary on-site potential, hopping and pairing.

## i. Overview

For a finite region `Λ`, the Hamiltonian is `H_Λ = Σ_{x∈Λ} V_x(N_x) + Σ_{x,y∈Λ} b_{xy}` with an
arbitrary real function `V_x` of the occupation number and the bond terms `b_{xy}` of the
Bose-Hubbard model with pairing. It is an element of the algebra of formally adjointable operators
on the finite vectors. No sign or growth condition is imposed on `V`. Its essential
self-adjointness reduces to the absence of square-summable solutions of `H g = i c g`, read row by
row in the occupation basis.

## ii. Key results

- `InfiniteBosons.diagAdj`: the diagonal operator with real eigenvalues.
- `InfiniteBosons.BoseHubbardData.finiteHam`: the finite-volume Hamiltonian.
- `InfiniteBosons.row_eq_of_orth`: orthogonality to the range of `H + i c` as a row equation.

## iii. Table of contents

- A. Diagonal operators
- B. The finite-volume Hamiltonian
- C. Orthogonality and the row equation

## iv. References

* M. Reed, B. Simon, Methods of Modern Mathematical Physics II, Section X.1.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

/-!

## A. Diagonal operators

-/

section Diagonal

variable {B : Type*} [DecidableEq B]

/-- The diagonal operator with eigenvalues `c` on the finite vectors. -/
def diagLin (c : B → ℝ) : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ) :=
  Finsupp.lsum ℂ fun α => ((c α : ℝ) : ℂ) • Finsupp.lsingle α

lemma diagLin_single (c : B → ℝ) (α : B) (z : ℂ) :
    diagLin c (single α z) = single α (((c α : ℝ) : ℂ) * z) := by
  simp [diagLin, Finsupp.lsum_single, Finsupp.smul_single]

lemma pair_diagLin (c : B → ℝ) (f g : B →₀ ℂ) : pair (diagLin c f) g = pair f (diagLin c g) := by
  refine pair_eq_of_basis (fun α β => ?_) f g
  rw [diagLin_single, diagLin_single, pair_single_single, pair_single_single]
  split_ifs with h
  · subst h; simp [Complex.conj_ofReal]
  · rfl

/-- The diagonal operator with real eigenvalues `c` as a formally adjointable operator. -/
def diagAdj (c : B → ℝ) : Adjointable B :=
  ⟨(diagLin c, MulOpposite.op (ofEnd (diagLin c))), by
    rw [mem_adjointable]
    intro f g
    simp only [MulOpposite.unop_op, toEnd_ofEnd]
    exact pair_diagLin c f g⟩

lemma star_diagAdj (c : B → ℝ) : star (diagAdj c) = diagAdj c := by
  refine adjointable_ext ?_
  show toEnd (MulOpposite.unop (MulOpposite.op (ofEnd (diagLin c)))) = diagLin c
  simp [toEnd_ofEnd]

lemma diagAdj_single (c : B → ℝ) (α : B) :
    (diagAdj c).1.1 (single α 1) = single α ((c α : ℝ) : ℂ) := by
  show diagLin c (single α 1) = _
  rw [diagLin_single, mul_one]

end Diagonal

/-!

## B. The finite-volume Hamiltonian

-/

variable {L : Type*} [DecidableEq L]

namespace BoseHubbardData

variable (D : BoseHubbardData L)

/-- **The finite-volume Hamiltonian** `Σ_{x∈Λ} V_x(N_x) + Σ_{x,y∈Λ} b_{xy}` with an arbitrary real
on-site potential `V` and the hopping and pairing bond terms of `D`. -/
def finiteHam (V : L → ℕ → ℝ) (Λ : Finset L) : adjointable L :=
  diagAdj (fun α : Occ L => ∑ x ∈ Λ, V x (α x)) + ∑ p ∈ Λ ×ˢ Λ, D.bondTerm p.1 p.2

lemma star_finiteHam (V : L → ℕ → ℝ) (Λ : Finset L) :
    star (D.finiteHam V Λ) = D.finiteHam V Λ := by
  unfold finiteHam
  rw [star_add, star_diagAdj, star_sum]
  simp only [bondTerm_star]

end BoseHubbardData

/-!

## C. Orthogonality and the row equation

-/

section Row

variable {B : Type*} [DecidableEq B]

lemma inner_embed_right (g : HilbertSp B) (v : B →₀ ℂ) :
    inner ℂ g (embed v) = ∑ β ∈ v.support, starRingEnd ℂ (g β) * v β := by
  conv_lhs => rw [← Finsupp.sum_single v]
  rw [Finsupp.sum, map_sum, inner_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [embed_single, lp.inner_single_right]
  simp [RCLike.inner_apply, mul_comm]

/-- The matrix element `⟨a|p|b⟩` in the basis. -/
def matEl (p : Adjointable B) (a b : B) : ℂ := (p.1.1 (single b 1)) a

lemma matEl_conj (p : Adjointable B) (hp : star p = p) (a b : B) :
    matEl p b a = starRingEnd ℂ (matEl p a b) := by
  have h := mem_adjointable.mp p.2 (single a 1) (single b 1)
  have hs : toEnd (MulOpposite.unop p.1.2) = p.1.1 := by
    have := congrArg (fun q : Adjointable B => q.1.1) hp
    exact this
  rw [hs, pair_single_left, pair_conj_symm, pair_single_left] at h
  unfold matEl
  rw [← h, Complex.conj_conj]

/-- **Orthogonality to the range of `p + i c` as a row equation.** If `g` is orthogonal to
`(p + i c) e_α` for every basis vector, then `Σ_β ⟨α|p|β⟩ g_β = i c g_α` along every row. -/
lemma row_eq_of_orth (p : Adjointable B) (hp : star p = p) (c : ℝ) (g : HilbertSp B)
    (h : ∀ α, inner ℂ g (shiftMap p.1.1 c (single α 1)) = 0) (α : B) :
    ∑ β ∈ (p.1.1 (single α 1)).support, matEl p α β * g β = Complex.I * c * g α := by
  have hα := h α
  have e : shiftMap p.1.1 c (single α 1) =
      embed (p.1.1 (single α 1)) + ((Complex.I * c : ℂ)) • embed (single α 1) := by
    simp only [shiftMap, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_add, map_smul]
  rw [e, inner_add_right, inner_smul_right, inner_embed_right, inner_embed_right,
    Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same, mul_one] at hα
  have hc := congrArg (starRingEnd ℂ) hα
  simp only [map_add, map_sum, map_mul, Complex.conj_conj, map_zero, Complex.conj_I,
    Complex.conj_ofReal] at hc
  have hm : ∀ β, starRingEnd ℂ ((p.1.1 (single α 1)) β) = matEl p α β := fun β => by
    rw [matEl_conj p hp β α]; rfl
  simp only [hm, mul_comm (g _)] at hc
  linear_combination hc

end Row


/-!

## D. Occupation of the region and elementary matrix elements

-/

section Occupation

variable {L : Type*} [DecidableEq L]

/-- The number of bosons in the region `Λ`. -/
def occIn (Λ : Finset L) (a : Occ L) : ℕ := ∑ x ∈ Λ, a x

lemma occIn_add (Λ : Finset L) (a b : Occ L) : occIn Λ (a + b) = occIn Λ a + occIn Λ b := by
  simp [occIn, Finset.sum_add_distrib]

lemma occIn_single (Λ : Finset L) {u : L} (hu : u ∈ Λ) : occIn Λ (single u 1) = 1 := by
  rw [occIn, Finset.sum_eq_single u (fun x _ hx => by simp [Finsupp.single_apply, Ne.symm hx])
    (fun h => absurd hu h)]
  simp

/-- Hopping inside the region preserves its occupation and the occupation outside. -/
lemma cre_ann_apply_ne {Λ : Finset L} {u v : L} (hu : u ∈ Λ) (hv : v ∈ Λ) {a b : Occ L}
    (h : cre u (ann v (single b (1 : ℂ))) a ≠ 0) :
    occIn Λ a = occIn Λ b ∧ ∀ z ∉ Λ, a z = b z := by
  rw [ann_single, cre_single] at h
  obtain ⟨rfl, hc⟩ := single_apply_ne' h
  have hbv : 1 ≤ b v := by
    by_contra h0; apply hc; simp [show b v = 0 by omega]
  have e : b - single v 1 + single u 1 + single v 1 = b + single u 1 := by
    rw [add_right_comm, tsub_add_cancel_of_le ((single_le_iff' v b).mpr hbv)]
  constructor
  · have := congrArg (occIn Λ) e
    rw [occIn_add, occIn_add, occIn_add, occIn_single Λ hu, occIn_single Λ hv] at this
    rw [occIn_add, occIn_single Λ hu]
    omega
  · intro z hz
    have := congrArg (· z) e
    have hu' : u ≠ z := fun h => hz (h ▸ hu)
    have hv' : v ≠ z := fun h => hz (h ▸ hv)
    simpa [Finsupp.single_apply, hu', hv'] using this

/-- Pair creation inside the region adds two bosons and leaves the outside unchanged. -/
lemma cre_cre_apply_ne {Λ : Finset L} {u v : L} (hu : u ∈ Λ) (hv : v ∈ Λ) {a b : Occ L}
    (h : cre u (cre v (single b (1 : ℂ))) a ≠ 0) :
    occIn Λ a = occIn Λ b + 2 ∧ ∀ z ∉ Λ, a z = b z := by
  rw [cre_single, cre_single] at h
  obtain ⟨rfl, -⟩ := single_apply_ne' h
  refine ⟨?_, fun z hz => ?_⟩
  · simp only [occIn_add, occIn_single Λ hu, occIn_single Λ hv]
  · simp [show u ≠ z from fun h => hz (h ▸ hu), show v ≠ z from fun h => hz (h ▸ hv)]

/-- Pair annihilation inside the region removes two bosons and leaves the outside unchanged. -/
lemma ann_ann_apply_ne {Λ : Finset L} {u v : L} (hu : u ∈ Λ) (hv : v ∈ Λ) {a b : Occ L}
    (h : ann v (ann u (single b (1 : ℂ))) a ≠ 0) :
    occIn Λ a + 2 = occIn Λ b ∧ ∀ z ∉ Λ, a z = b z := by
  rw [ann_single, ann_single] at h
  obtain ⟨rfl, hc⟩ := single_apply_ne' h
  have hbu : 1 ≤ b u := by
    by_contra h0; apply hc; simp [show b u = 0 by omega]
  have hbv : 1 ≤ (b - single u 1 : Occ L) v := by
    by_contra h0; apply hc; simp [show (b - single u 1 : Occ L) v = 0 by omega]
  have e : b - single u 1 - single v 1 + single v 1 + single u 1 = b := by
    rw [tsub_add_cancel_of_le ((single_le_iff' v _).mpr hbv),
      tsub_add_cancel_of_le ((single_le_iff' u b).mpr hbu)]
  constructor
  · have := congrArg (occIn Λ) e
    rw [occIn_add, occIn_add, occIn_single Λ hu, occIn_single Λ hv] at this
    omega
  · intro z hz
    have := congrArg (· z) e
    have hu' : u ≠ z := fun h => hz (h ▸ hu)
    have hv' : v ≠ z := fun h => hz (h ▸ hv)
    simpa [Finsupp.single_apply, hu', hv'] using this

end Occupation


/-!

## E. The band structure of the finite-volume Hamiltonian

-/

section Band

variable {B : Type*} [DecidableEq B]

lemma matEl_add (p q : Adjointable B) (a b : B) : matEl (p + q) a b = matEl p a b + matEl q a b :=
  rfl

lemma matEl_sum {ι : Type*} (s : Finset ι) (p : ι → Adjointable B) (a b : B) :
    matEl (∑ i ∈ s, p i) a b = ∑ i ∈ s, matEl (p i) a b := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, matEl_add, ih]

lemma matEl_diagAdj (c : B → ℝ) (a b : B) :
    matEl (diagAdj c) a b = if b = a then ((c b : ℝ) : ℂ) else 0 := by
  unfold matEl
  rw [diagAdj_single, Finsupp.single_apply]

end Band

variable {L : Type*} [DecidableEq L]

namespace BoseHubbardData

variable (D : BoseHubbardData L)

open Classical in
lemma matEl_bondTerm (x y : L) (a b : Occ L) :
    matEl (D.bondTerm x y) a b = if D.graph.Adj x y then
      ((-D.J x y : ℝ) : ℂ) * (cre x (ann y (single b (1 : ℂ))) a + cre y (ann x (single b 1)) a) +
        D.Δ x y * cre x (cre y (single b 1)) a +
        starRingEnd ℂ (D.Δ x y) * ann y (ann x (single b 1)) a else 0 := by
  unfold matEl bondTerm
  split_ifs
  · show (((-D.J x y : ℝ) : ℂ) • (cre x (ann y (single b (1 : ℂ))) + cre y (ann x (single b 1))) +
      D.Δ x y • cre x (cre y (single b 1)) + starRingEnd ℂ (D.Δ x y) • ann y (ann x (single b 1))) a
      = _
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  · rfl

/-- **Band structure.** A nonzero matrix element of the finite-volume Hamiltonian connects states
that agree outside the region and whose occupations of the region differ by `0` or `2`. -/
lemma finiteHam_matEl_ne (V : L → ℕ → ℝ) (Λ : Finset L) {a b : Occ L}
    (h : matEl (D.finiteHam V Λ) a b ≠ 0) :
    (occIn Λ a = occIn Λ b ∨ occIn Λ a = occIn Λ b + 2 ∨ occIn Λ a + 2 = occIn Λ b) ∧
      ∀ z ∉ Λ, a z = b z := by
  unfold finiteHam at h
  rw [matEl_add, matEl_sum, matEl_diagAdj] at h
  by_cases hd : b = a
  · subst hd; exact ⟨Or.inl rfl, fun _ _ => rfl⟩
  rw [if_neg hd, zero_add] at h
  obtain ⟨⟨x, y⟩, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
  rw [matEl_bondTerm] at hne
  split_ifs at hne with hadj
  · by_cases h1 : cre x (ann y (single b (1 : ℂ))) a = 0
    · by_cases h2 : cre y (ann x (single b (1 : ℂ))) a = 0
      · by_cases h3 : cre x (cre y (single b (1 : ℂ))) a = 0
        · have h4 : ann y (ann x (single b (1 : ℂ))) a ≠ 0 := by
            intro h4; apply hne; simp [h1, h2, h3, h4]
          obtain ⟨e, ho⟩ := ann_ann_apply_ne hx hy h4
          exact ⟨Or.inr (Or.inr e), ho⟩
        · obtain ⟨e, ho⟩ := cre_cre_apply_ne hx hy h3
          exact ⟨Or.inr (Or.inl e), ho⟩
      · obtain ⟨e, ho⟩ := cre_ann_apply_ne hy hx h2
        exact ⟨Or.inl e, ho⟩
    · obtain ⟨e, ho⟩ := cre_ann_apply_ne hx hy h1
      exact ⟨Or.inl e, ho⟩
  · exact absurd rfl hne

end BoseHubbardData


/-!

## F. The blocks between neighbouring grades

-/

section Blocks

variable {L : Type*} [DecidableEq L]

lemma ann_ann_single_apply (u v : L) (b a : Occ L) :
    ann v (ann u (single b (1 : ℂ))) a = if b - single u 1 - single v 1 = a then
      ((Real.sqrt ((b - single u 1 : Occ L) v) : ℝ) : ℂ) * (((Real.sqrt (b u) : ℝ) : ℂ) * 1)
      else 0 := by
  rw [ann_single, ann_single, Finsupp.single_apply]

lemma le_occIn {Λ : Finset L} {z : L} (hz : z ∈ Λ) (b : Occ L) : b z ≤ occIn Λ b :=
  Finset.single_le_sum (f := fun x => b x) (fun _ _ => Nat.zero_le _) hz

lemma sqrt_mul_sqrt_le {m k M : ℝ} (hm : 0 ≤ m) (hk : 0 ≤ k) (hmM : m ≤ M) (hkM : k ≤ M) :
    Real.sqrt m * Real.sqrt k ≤ M := by
  nlinarith [sq_nonneg (Real.sqrt m - Real.sqrt k), Real.sq_sqrt hm, Real.sq_sqrt hk]

/-- The amplitude of pair annihilation inside the region is at most the occupation of the region. -/
lemma norm_ann_ann_le {Λ : Finset L} {u v : L} (hu : u ∈ Λ) (hv : v ∈ Λ) (b a : Occ L) :
    ‖ann v (ann u (single b (1 : ℂ))) a‖ ≤ occIn Λ b := by
  rw [ann_ann_single_apply]
  split_ifs
  · rw [mul_one, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have h1 : ((b - single u 1 : Occ L) v : ℝ) ≤ occIn Λ b := by
      have : (b - single u 1 : Occ L) v ≤ b v := by simp
      exact_mod_cast this.trans (le_occIn hv b)
    have h2 : (b u : ℝ) ≤ occIn Λ b := by exact_mod_cast le_occIn hu b
    exact sqrt_mul_sqrt_le (by positivity) (by positivity) h1 h2
  · simp

/-- Pair annihilation is injective: the source state is the target with the pair added. -/
lemma eq_add_of_ann_ann_ne {u v : L} {a b : Occ L} (h : ann v (ann u (single b (1 : ℂ))) a ≠ 0) :
    b = a + single v 1 + single u 1 := by
  rw [ann_ann_single_apply] at h
  split_ifs at h with he
  · have hc : ((Real.sqrt ((b - single u 1 : Occ L) v) : ℝ) : ℂ) ≠ 0 ∧
        ((Real.sqrt (b u) : ℝ) : ℂ) ≠ 0 := by
      constructor
      · intro h0; apply h; rw [h0, zero_mul]
      · intro h0; apply h; rw [h0, zero_mul, mul_zero]
    have hbu : 1 ≤ b u := by
      by_contra h0; apply hc.2; simp [show b u = 0 by omega]
    have hbv : 1 ≤ (b - single u 1 : Occ L) v := by
      by_contra h0; apply hc.1; simp [show (b - single u 1 : Occ L) v = 0 by omega]
    rw [← he, tsub_add_cancel_of_le ((single_le_iff' v _).mpr hbv),
      tsub_add_cancel_of_le ((single_le_iff' u b).mpr hbu)]
  · exact absurd rfl h

end Blocks

namespace BoseHubbardData

variable (D : BoseHubbardData L)

/-- Between states whose occupations of the region differ by two, only pair annihilation acts. -/
lemma matEl_bondTerm_of_occ {Λ : Finset L} {x y : L} (hx : x ∈ Λ) (hy : y ∈ Λ) {a b : Occ L}
    (hab : occIn Λ b = occIn Λ a + 2) :
    ‖matEl (D.bondTerm x y) a b‖ ≤ ‖D.Δ x y‖ * ‖ann y (ann x (single b (1 : ℂ))) a‖ := by
  rw [matEl_bondTerm]
  split_ifs
  · have h1 : cre x (ann y (single b (1 : ℂ))) a = 0 := by
      by_contra h; have := (cre_ann_apply_ne hx hy h).1; omega
    have h2 : cre y (ann x (single b (1 : ℂ))) a = 0 := by
      by_contra h; have := (cre_ann_apply_ne hy hx h).1; omega
    have h3 : cre x (cre y (single b (1 : ℂ))) a = 0 := by
      by_contra h; have := (cre_cre_apply_ne hx hy h).1; omega
    simp only [h1, h2, h3, add_zero, mul_zero, zero_add]
    rw [norm_mul, RCLike.norm_conj]
  · calc ‖(0 : ℂ)‖ = 0 := norm_zero
      _ ≤ _ := by positivity

/-- **Block bound.** Between grades `n` and `n + 1` the matrix elements of the finite-volume
Hamiltonian are bounded by the pair-annihilation amplitudes. -/
lemma norm_matEl_finiteHam_le (V : L → ℕ → ℝ) (Λ : Finset L) {a b : Occ L}
    (hab : occIn Λ a / 2 + 1 = occIn Λ b / 2) :
    ‖matEl (D.finiteHam V Λ) a b‖ ≤
      ∑ p ∈ Λ ×ˢ Λ, ‖D.Δ p.1 p.2‖ * ‖ann p.2 (ann p.1 (single b (1 : ℂ))) a‖ := by
  by_cases h0 : matEl (D.finiteHam V Λ) a b = 0
  · rw [h0, norm_zero]; positivity
  have hocc : occIn Λ b = occIn Λ a + 2 := by
    rcases (D.finiteHam_matEl_ne V Λ h0).1 with h | h | h <;> omega
  have hne : b ≠ a := fun h => by rw [h] at hocc; omega
  unfold finiteHam
  rw [matEl_add, matEl_sum, matEl_diagAdj, if_neg hne, zero_add]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
  exact D.matEl_bondTerm_of_occ hx hy hocc

end BoseHubbardData

end InfiniteBosons
