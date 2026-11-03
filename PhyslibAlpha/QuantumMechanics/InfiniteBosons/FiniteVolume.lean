/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.ModelHamiltonians
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.JacobiCarleman
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.EssentialSelfAdjoint
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.QuadratureSelfAdjoint
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

omit [DecidableEq B] in
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
    Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
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

omit [DecidableEq L] in
lemma occIn_add (Λ : Finset L) (a b : Occ L) : occIn Λ (a + b) = occIn Λ a + occIn Λ b := by
  simp [occIn, Finset.sum_add_distrib]

omit [DecidableEq L] in
lemma occIn_single (Λ : Finset L) {u : L} (hu : u ∈ Λ) : occIn Λ (single u 1) = 1 := by
  rw [occIn, Finset.sum_eq_single u (fun x _ hx => by simp [Ne.symm hx])
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
    have hu' : u ≠ z := fun h => hz (h ▸ hu)
    have hv' : v ≠ z := fun h => hz (h ▸ hv)
    simp [hu', hv']

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
    have hu' : u ≠ z := fun h => hz (h ▸ hu)
    have hv' : v ≠ z := fun h => hz (h ▸ hv)
    simp [hu', hv']

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

omit [DecidableEq L] in
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


/-!

## G. Essential self-adjointness

-/

section Fibres

variable {L : Type*} [DecidableEq L]

/-- The state equal to `ρ` outside `Λ` and to `φ` on `Λ`. -/
def fillIn (Λ : Finset L) (ρ : Occ L) (φ : Λ → ℕ) : Occ L :=
  Finsupp.filter (· ∉ Λ) ρ + ∑ x : Λ, single x.1 (φ x)

lemma fillIn_apply_mem (Λ : Finset L) (ρ : Occ L) (φ : Λ → ℕ) {z : L} (hz : z ∈ Λ) :
    fillIn Λ ρ φ z = φ ⟨z, hz⟩ := by
  rw [fillIn, Finsupp.add_apply, Finsupp.filter_apply, if_neg (not_not.mpr hz), zero_add,
    Finsupp.finsetSum_apply, Finset.sum_eq_single ⟨z, hz⟩]
  · simp
  · intro x _ hx
    rw [Finsupp.single_apply, if_neg (fun h => hx (Subtype.ext h))]
  · simp

lemma fillIn_apply_not_mem (Λ : Finset L) (ρ : Occ L) (φ : Λ → ℕ) {z : L} (hz : z ∉ Λ) :
    fillIn Λ ρ φ z = ρ z := by
  rw [fillIn, Finsupp.add_apply, Finsupp.filter_apply, if_pos hz, Finsupp.finsetSum_apply,
    Finset.sum_eq_zero fun x _ => ?_, add_zero]
  rw [Finsupp.single_apply, if_neg (fun h : (x : L) = z => hz (h ▸ x.2))]

/-- The states agreeing with `ρ` outside `Λ` with `⌊N_Λ / 2⌋ = n` form a finite set. -/
lemma finite_fibreGrade (Λ : Finset L) (ρ : Occ L) (n : ℕ) :
    {a : Occ L | (∀ z ∉ Λ, a z = ρ z) ∧ occIn Λ a / 2 = n}.Finite := by
  refine (Set.finite_range (fun φ : Λ → Fin (2 * n + 2) => fillIn Λ ρ (fun x => (φ x : ℕ)))).subset
    fun a ⟨hout, hn⟩ => ?_
  have hle : ∀ x : Λ, a x.1 < 2 * n + 2 := fun x => by
    have := le_occIn x.2 a; omega
  refine ⟨fun x => ⟨a x.1, hle x⟩, Finsupp.ext fun z => ?_⟩
  by_cases hz : z ∈ Λ
  · rw [fillIn_apply_mem _ _ _ hz]
  · rw [fillIn_apply_not_mem _ _ _ hz, hout z hz]

/-- The states of grade `n` in the fibre of `ρ`. -/
def fibreGrade (Λ : Finset L) (ρ : Occ L) (n : ℕ) : Finset (Occ L) :=
  (finite_fibreGrade Λ ρ n).toFinset

lemma mem_fibreGrade {Λ : Finset L} {ρ a : Occ L} {n : ℕ} :
    a ∈ fibreGrade Λ ρ n ↔ (∀ z ∉ Λ, a z = ρ z) ∧ occIn Λ a / 2 = n := by
  simp [fibreGrade]

/-- A sum with at most one nonzero nonnegative term is bounded by that term. -/
lemma sum_le_of_eq_zero {β : Type*} (s : Finset β) (f : β → ℝ) (hf : ∀ x, 0 ≤ f x) (x0 : β)
    (h : ∀ x ∈ s, x ≠ x0 → f x = 0) : ∑ x ∈ s, f x ≤ f x0 := by
  classical
  by_cases hx0 : x0 ∈ s
  · rw [Finset.sum_eq_single_of_mem x0 hx0 h]
  · rw [Finset.sum_eq_zero fun x hx => h x hx fun e => hx0 (e ▸ hx)]; exact hf x0

/-- The harmonic-type series `Σ 1 / (C (2 n + 3))` diverges. -/
lemma not_summable_inv_linear {C : ℝ} (hC : 0 < C) :
    ¬ Summable fun n : ℕ => 1 / (C * (2 * n + 3)) := by
  intro hs
  apply Real.not_summable_one_div_natCast
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hs.mul_left (3 * C))
  push_cast
  rw [div_le_iff₀ (by positivity)]
  field_simp
  nlinarith

end Fibres

namespace BoseHubbardData

variable (D : BoseHubbardData L)

/-- The bound on the blocks between grades `n` and `n + 1`. -/
def blockBound (Λ : Finset L) (n : ℕ) : ℝ :=
  (∑ p ∈ Λ ×ˢ Λ, ‖D.Δ p.1 p.2‖ + 1) * (2 * n + 3)

omit [DecidableEq L] in
lemma blockBound_pos (Λ : Finset L) (n : ℕ) : 0 < D.blockBound Λ n := by
  unfold blockBound; positivity

omit [DecidableEq L] in
lemma sum_Δ_le (Λ : Finset L) (n : ℕ) (f : L × L → ℝ)
    (hf : ∀ p ∈ Λ ×ˢ Λ, f p ≤ 2 * n + 3) :
    ∑ p ∈ Λ ×ˢ Λ, ‖D.Δ p.1 p.2‖ * f p ≤ D.blockBound Λ n := by
  unfold blockBound
  calc ∑ p ∈ Λ ×ˢ Λ, ‖D.Δ p.1 p.2‖ * f p ≤ ∑ p ∈ Λ ×ˢ Λ, ‖D.Δ p.1 p.2‖ * (2 * n + 3) :=
        Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hf p hp) (norm_nonneg _)
    _ ≤ _ := by rw [← Finset.sum_mul]; nlinarith [Finset.sum_nonneg fun p (_ : p ∈ Λ ×ˢ Λ) =>
        norm_nonneg (D.Δ p.1 p.2)]

/-- Row sums of the block from grade `n` to grade `n + 1`. -/
lemma rowSum_le (V : L → ℕ → ℝ) (Λ : Finset L) (ρ : Occ L) (n : ℕ) {a : Occ L}
    (ha : a ∈ fibreGrade Λ ρ n) :
    ∑ b ∈ fibreGrade Λ ρ (n + 1), ‖matEl (D.finiteHam V Λ) a b‖ ≤ D.blockBound Λ n := by
  have hga := (mem_fibreGrade.mp ha).2
  calc _ ≤ ∑ b ∈ fibreGrade Λ ρ (n + 1),
        ∑ p ∈ Λ ×ˢ Λ, ‖D.Δ p.1 p.2‖ * ‖ann p.2 (ann p.1 (single b (1 : ℂ))) a‖ :=
        Finset.sum_le_sum fun b hb => D.norm_matEl_finiteHam_le V Λ (by
          rw [(mem_fibreGrade.mp hb).2, hga])
    _ = ∑ p ∈ Λ ×ˢ Λ, ‖D.Δ p.1 p.2‖ *
        ∑ b ∈ fibreGrade Λ ρ (n + 1), ‖ann p.2 (ann p.1 (single b (1 : ℂ))) a‖ := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ _ := D.sum_Δ_le Λ n _ fun p hp => by
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
        refine (sum_le_of_eq_zero _ _ (fun _ => norm_nonneg _) (a + single p.2 1 + single p.1 1)
          fun b _ hb => ?_).trans ?_
        · by_contra h
          exact hb (eq_add_of_ann_ann_ne (norm_ne_zero_iff.mp h))
        · refine (norm_ann_ann_le hx hy _ _).trans ?_
          rw [occIn_add, occIn_add, occIn_single Λ hy, occIn_single Λ hx]
          push_cast
          have : (occIn Λ a : ℝ) ≤ 2 * n + 1 := by exact_mod_cast (show occIn Λ a ≤ 2 * n + 1 by omega)
          linarith

/-- Column sums of the block from grade `n` to grade `n + 1`. -/
lemma colSum_le (V : L → ℕ → ℝ) (Λ : Finset L) (ρ : Occ L) (n : ℕ) {b : Occ L}
    (hb : b ∈ fibreGrade Λ ρ (n + 1)) :
    ∑ a ∈ fibreGrade Λ ρ n, ‖matEl (D.finiteHam V Λ) a b‖ ≤ D.blockBound Λ n := by
  have hgb := (mem_fibreGrade.mp hb).2
  calc _ ≤ ∑ a ∈ fibreGrade Λ ρ n,
        ∑ p ∈ Λ ×ˢ Λ, ‖D.Δ p.1 p.2‖ * ‖ann p.2 (ann p.1 (single b (1 : ℂ))) a‖ :=
        Finset.sum_le_sum fun a ha => D.norm_matEl_finiteHam_le V Λ (by
          rw [(mem_fibreGrade.mp ha).2, hgb])
    _ = ∑ p ∈ Λ ×ˢ Λ, ‖D.Δ p.1 p.2‖ *
        ∑ a ∈ fibreGrade Λ ρ n, ‖ann p.2 (ann p.1 (single b (1 : ℂ))) a‖ := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ _ := D.sum_Δ_le Λ n _ fun p hp => by
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
        refine (sum_le_of_eq_zero _ _ (fun _ => norm_nonneg _) (b - single p.1 1 - single p.2 1)
          fun a _ ha => ?_).trans ?_
        · rw [ann_ann_single_apply, if_neg (fun h => ha h.symm), norm_zero]
        · refine (norm_ann_ann_le hx hy _ _).trans ?_
          have : occIn Λ b ≤ 2 * n + 3 := by omega
          exact_mod_cast this

end BoseHubbardData


namespace BoseHubbardData

variable (D : BoseHubbardData L)

/-- A row of the finite-volume Hamiltonian lies in the fibre of its state and in grades at most one
above it. -/
lemma mem_gradeLe_of_matEl_ne (V : L → ℕ → ℝ) (Λ : Finset L) {a b : Occ L}
    (h : matEl (D.finiteHam V Λ) a b ≠ 0) :
    b ∈ gradeLe (fibreGrade Λ a) (occIn Λ a / 2 + 1) := by
  obtain ⟨hocc, hout⟩ := D.finiteHam_matEl_ne V Λ h
  refine subset_gradeLe (S := fibreGrade Λ a) (n := occIn Λ b / 2) (by omega)
    (mem_fibreGrade.mpr ⟨fun z hz => (hout z hz).symm, rfl⟩)

/-- **Orthogonality to the range of `H_Λ + i c` forces the vector to vanish.** -/
lemma eq_zero_of_orth (V : L → ℕ → ℝ) (Λ : Finset L) {c : ℝ} (hc : c ≠ 0)
    (g : HilbertSp (Occ L))
    (hg : ∀ α, inner ℂ g (shiftMap (D.finiteHam V Λ).1.1 c (single α 1)) = 0) (a0 : Occ L) :
    g a0 = 0 := by
  classical
  set H := D.finiteHam V Λ
  have hH : star H = H := D.star_finiteHam V Λ
  set fib : Occ L → Prop := fun a => ∀ z ∉ Λ, a z = a0 z
  set g' : Occ L → ℂ := fun a => if fib a then g a else 0
  have hrowEq := row_eq_of_orth H hH c g hg
  have key := blockJacobi_no_l2_solution (gr := fun a => occIn Λ a / 2) (S := fibreGrade Λ a0)
    (fun a n ha => (mem_fibreGrade.mp ha).2) (matEl H) (fun a b => matEl_conj H hH a b)
    (fun a b h => by have := (D.finiteHam_matEl_ne V Λ h).1; omega) (D.blockBound Λ)
    (D.blockBound_pos Λ) (fun n a ha => D.rowSum_le V Λ a0 n ha)
    (fun n b hb => D.colSum_le V Λ a0 n hb)
    (by simpa [blockBound, mul_comm] using (not_summable_inv_linear
      (C := ∑ p ∈ Λ ×ˢ Λ, ‖D.Δ p.1 p.2‖ + 1) (by positivity))) hc g' ?_ ?_ ?_ a0
  · simpa [g', fib] using key
  · -- square summability
    have hm : Summable fun a => ‖g a‖ ^ (2 : ℝ) := (lp.memℓp g).summable (by norm_num)
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun a => ?_) hm
    rw [Real.rpow_two]
    by_cases ha : fib a <;> simp [g', ha]
  · -- the support of `g'` lies in the fibre
    intro a ha
    by_cases hf : fib a
    · exact mem_fibreGrade.mpr ⟨hf, rfl⟩
    · exact absurd (by simp [g', hf]) ha
  · -- the row equation on the fibre
    intro a ha
    have hfa : fib a := (mem_fibreGrade.mp ha).1
    have hfib : fibreGrade Λ a = fibreGrade Λ a0 := by
      ext b; simp only [mem_fibreGrade]
      exact ⟨fun ⟨h1, h2⟩ => ⟨fun z hz => (h1 z hz).trans (hfa z hz), h2⟩,
        fun ⟨h1, h2⟩ => ⟨fun z hz => (h1 z hz).trans (hfa z hz).symm, h2⟩⟩
    have hsub : (H.1.1 (single a 1)).support ⊆ gradeLe (fibreGrade Λ a0) (occIn Λ a / 2 + 1) := by
      intro b hb
      have hne : matEl H a b ≠ 0 := by
        intro h0
        apply Finsupp.mem_support_iff.mp hb
        show matEl H b a = 0
        rw [matEl_conj H hH, h0, map_zero]
      rw [← hfib]; exact D.mem_gradeLe_of_matEl_ne V Λ hne
    rw [show g' a = g a by simp [g', hfa], ← hrowEq a]
    refine (Finset.sum_congr rfl fun b hb => ?_).trans (Finset.sum_subset hsub fun b _ hb => ?_).symm
    · obtain ⟨n, -, hbn⟩ := exists_mem_of_mem_gradeLe hb
      have hfb : fib b := (mem_fibreGrade.mp hbn).1
      show matEl H a b * (if fib b then g b else 0) = _
      rw [if_pos hfb]
    · have : matEl H b a = 0 := Finsupp.notMem_support_iff.mp hb
      rw [matEl_conj H hH] at this
      rw [(map_eq_zero _).mp this, zero_mul]

/-- The range of `H_Λ + i c` is dense. -/
lemma finiteHam_dense_range (V : L → ℕ → ℝ) (Λ : Finset L) {c : ℝ} (hc : c ≠ 0) :
    Dense (LinearMap.range (shiftMap (D.finiteHam V Λ).1.1 c) : Set (HilbertSp (Occ L))) := by
  refine dense_of_orth _ fun g hg => lp.ext (funext fun a0 => ?_)
  rw [D.eq_zero_of_orth V Λ hc g (fun α => hg _ ⟨single α 1, rfl⟩) a0]
  rfl

/-- **The finite-volume Bose-Hubbard Hamiltonian with pairing is essentially self-adjoint** on the
finite vectors, for an arbitrary real on-site potential `V`. No sign or growth condition on `V` is
needed: pairing couples the grades `⌊N_Λ / 2⌋` like a block Jacobi matrix with off-diagonal blocks
of size `O(n)`, and Carleman's criterion applies. -/
theorem finiteHam_isEssentiallySelfAdjoint (V : L → ℕ → ℝ) (Λ : Finset L) :
    (polyOp (D.finiteHam V Λ)).IsEssentiallySelfAdjoint :=
  polyOp_isEssentiallySelfAdjoint _ (D.star_finiteHam V Λ) (D.finiteHam_dense_range V Λ one_ne_zero)
    (D.finiteHam_dense_range V Λ (by norm_num))

end BoseHubbardData

end InfiniteBosons
