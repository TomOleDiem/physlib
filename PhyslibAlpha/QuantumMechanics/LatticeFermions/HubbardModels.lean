/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.LatticeFermions.CARDynamics

/-!

# Hubbard-type models with pairing

Spin-1/2 electrons on a graph of bounded degree with hopping, density-density interaction and
pairing along the edges, and arbitrary on-site Hubbard interactions and chemical potentials. They
have an infinite-volume dynamics.

## i. Overview

The modes are pairs `(x, s)` of a site and a spin `s ∈ {↓, ↑} = Bool`, ordered
lexicographically. Along an edge `{x, y}` of the graph the interaction term is

`Φ({x, y}) = Σ_s (t_{xy} c*_{xs} c_{ys} + h.c.) + W_{xy} n_x n_y + (Δ_{xy} c*_{x↑} c*_{y↓} + h.c.)`

with `n_x = n_{x↓} + n_{x↑}`, and the on-site terms are `D_x = U_x n_{x↑} n_{x↓} - μ_x n_x`. All
terms are even and self-adjoint; the pairing terms do not conserve the particle number. The
interaction has range one, and if the degree is at most `d` and `‖t_{xy}‖ ≤ T`, `|W_{xy}| ≤ W`,
`‖Δ_{xy}‖ ≤ P`, it is bounded by `J = 2 d (4 T + 4 W + 2 P)`. The on-site couplings `U_x` and
`μ_x` are arbitrary. The main theorem `car_dynamics` therefore applies.

Special cases: the Hubbard model (`t` constant, `W = Δ = 0`), the extended Hubbard model
(`Δ = 0`), translation-invariant pairing (constant `Δ`), and quartic interaction together with
pairing.

## ii. Key results

- `LatticeFermions.Hubbard.Couplings` : the coupling constants.
- `LatticeFermions.Hubbard.bond` : the interaction term of an edge.
- `LatticeFermions.Hubbard.interaction` : the interaction of the CAR net.
- `LatticeFermions.Hubbard.isBoundedBy` : the bound `J`.
- `LatticeFermions.Hubbard.dynamics_exists` : the infinite-volume dynamics.

## iii. Table of contents

- A. Hopping and pairing terms
- B. Electron modes
- C. Bond and on-site terms
- D. The interaction on a graph
- E. Bounds and the dynamics
- F. Examples

## iv. References

* B. Nachtergaele, R. Sims, A. Young, Lieb-Robinson bounds, the spectral flow, and stability of
  the spectral gap for lattice fermion systems, arXiv:1705.08553, Section 4.

-/

@[expose] public section

noncomputable section

namespace LatticeFermions

open Finset Complex ComplexConjugate

/-!

## A. Hopping and pairing terms

-/

section terms

variable {M : Type*} [LinearOrder M]

/-- The hopping term `z c*_a c_b + z̄ c*_b c_a`. -/
def hopTerm (z : ℂ) (a b : M) : FockOp M := z • (cre a * ann b) + conj z • (cre b * ann a)

/-- The pairing term `z c*_a c*_b + z̄ c_b c_a`. It does not conserve the particle number. -/
def pairTerm (z : ℂ) (a b : M) : FockOp M := z • (cre a * cre b) + conj z • (ann b * ann a)

lemma isSelfAdjoint_hopTerm (z : ℂ) (a b : M) : IsSelfAdjoint (hopTerm z a b) := by
  rw [IsSelfAdjoint, hopTerm, star_add, star_smul, star_smul, star_mul, star_mul, star_ann,
    star_ann, star_cre, star_cre]
  simp only [Complex.star_def, Complex.conj_conj]
  rw [add_comm]

lemma isSelfAdjoint_pairTerm (z : ℂ) (a b : M) : IsSelfAdjoint (pairTerm z a b) := by
  rw [IsSelfAdjoint, pairTerm, star_add, star_smul, star_smul, star_mul, star_mul, star_ann,
    star_ann, star_cre, star_cre]
  simp only [Complex.star_def, Complex.conj_conj]
  rw [add_comm]

lemma parityAut_hopTerm (z : ℂ) (a b : M) : parityAut M (hopTerm z a b) = hopTerm z a b := by
  rw [hopTerm, map_add, map_smul, map_smul, parityAut_mul_of_neg (parityAut_cre a)
    (parityAut_ann b), parityAut_mul_of_neg (parityAut_cre b) (parityAut_ann a)]

lemma parityAut_pairTerm (z : ℂ) (a b : M) : parityAut M (pairTerm z a b) = pairTerm z a b := by
  rw [pairTerm, map_add, map_smul, map_smul, parityAut_mul_of_neg (parityAut_cre a)
    (parityAut_cre b), parityAut_mul_of_neg (parityAut_ann b) (parityAut_ann a)]

omit [LinearOrder M] in
lemma norm_mul_le_one {a b : FockOp M} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 :=
  (norm_mul_le _ _).trans (by simpa using mul_le_mul ha hb (norm_nonneg _) zero_le_one)

omit [LinearOrder M] in
lemma norm_smul_add_smul_le {z : ℂ} {a b : FockOp M} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖z • a + conj z • b‖ ≤ 2 * ‖z‖ := by
  calc ‖z • a + conj z • b‖ ≤ ‖z‖ * ‖a‖ + ‖z‖ * ‖b‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Complex.norm_conj]
    _ ≤ ‖z‖ * 1 + ‖z‖ * 1 := by gcongr
    _ = 2 * ‖z‖ := by ring

lemma norm_hopTerm_le (z : ℂ) (a b : M) : ‖hopTerm z a b‖ ≤ 2 * ‖z‖ :=
  norm_smul_add_smul_le (norm_mul_le_one (norm_cre_le a) (norm_ann_le b))
    (norm_mul_le_one (norm_cre_le b) (norm_ann_le a))

lemma norm_pairTerm_le (z : ℂ) (a b : M) : ‖pairTerm z a b‖ ≤ 2 * ‖z‖ :=
  norm_smul_add_smul_le (norm_mul_le_one (norm_cre_le a) (norm_cre_le b))
    (norm_mul_le_one (norm_ann_le b) (norm_ann_le a))

end terms

namespace Hubbard

/-!

## B. Electron modes

-/

variable {V : Type*} [LinearOrder V]

/-- The modes of spin-1/2 electrons on the sites `V`: a site and a spin, ordered
lexicographically. -/
abbrev Mode (V : Type*) := Lex (V × Bool)

/-- The mode of spin `s` at the site `x`. -/
def mode (x : V) (s : Bool) : Mode V := toLex (x, s)

/-- The site of a mode. -/
def site (m : Mode V) : V := (ofLex m).1

omit [LinearOrder V] in
@[simp]
lemma site_mode (x : V) (s : Bool) : site (mode x s) = x := rfl

/-- The density `n_x = n_{x↓} + n_{x↑}` at a site. -/
def density (x : V) : FockOp (Mode V) := numOp (mode x false) + numOp (mode x true)

lemma isSelfAdjoint_density (x : V) : IsSelfAdjoint (density x) :=
  (isSelfAdjoint_numOp _).add (isSelfAdjoint_numOp _)

lemma commute_density (x y : V) : Commute (density x) (density y) :=
  ((commute_numOp _ _).add_right (commute_numOp _ _)).add_left
    ((commute_numOp _ _).add_right (commute_numOp _ _))

lemma norm_density_le (x : V) : ‖density x‖ ≤ 2 :=
  (norm_add_le _ _).trans (by linarith [norm_numOp_le (mode x false), norm_numOp_le (mode x true)])

lemma parityAut_density (x : V) : parityAut (Mode V) (density x) = density x := by
  rw [density, map_add, parityAut_numOp, parityAut_numOp]

variable {X : Finset V}

lemma ann_mem {x : V} (hx : x ∈ X) (s : Bool) : ann (mode x s) ∈ carLocal site X :=
  ann_mem_carLocal (by simpa using hx)

lemma cre_mem {x : V} (hx : x ∈ X) (s : Bool) : cre (mode x s) ∈ carLocal site X :=
  cre_mem_carLocal (by simpa using hx)

lemma numOp_mem {x : V} (hx : x ∈ X) (s : Bool) : numOp (mode x s) ∈ carLocal site X :=
  (carLocal site X).mul_mem (cre_mem hx s) (ann_mem hx s)

lemma density_mem {x : V} (hx : x ∈ X) : density x ∈ carLocal site X :=
  (carLocal site X).add_mem (numOp_mem hx false) (numOp_mem hx true)

lemma hopTerm_mem {x y : V} (hx : x ∈ X) (hy : y ∈ X) (z : ℂ) (s : Bool) :
    hopTerm z (mode x s) (mode y s) ∈ carLocal site X :=
  (carLocal site X).add_mem
    ((carLocal site X).smul_mem ((carLocal site X).mul_mem (cre_mem hx s) (ann_mem hy s)) _)
    ((carLocal site X).smul_mem ((carLocal site X).mul_mem (cre_mem hy s) (ann_mem hx s)) _)

lemma pairTerm_mem {x y : V} (hx : x ∈ X) (hy : y ∈ X) (z : ℂ) :
    pairTerm z (mode x true) (mode y false) ∈ carLocal site X :=
  (carLocal site X).add_mem
    ((carLocal site X).smul_mem ((carLocal site X).mul_mem (cre_mem hx _) (cre_mem hy _)) _)
    ((carLocal site X).smul_mem ((carLocal site X).mul_mem (ann_mem hy _) (ann_mem hx _)) _)

/-!

## C. Bond and on-site terms

-/

/-- The coupling constants: hopping `t_{xy}`, density-density interaction `W_{xy}`, pairing
`Δ_{xy}`, on-site Hubbard interaction `U_x` and chemical potential `μ_x`. -/
structure Couplings (V : Type*) where
  /-- The hopping amplitude `t_{xy}`. -/
  hop : V → V → ℂ
  /-- The density-density interaction `W_{xy}`. -/
  dens : V → V → ℝ
  /-- The pairing amplitude `Δ_{xy}`. -/
  pair : V → V → ℂ
  /-- The on-site Hubbard interaction `U_x`. -/
  hubbardU : V → ℝ
  /-- The chemical potential `μ_x`. -/
  chemPot : V → ℝ

variable (K : Couplings V)

/-- The interaction term of the edge `{x, y}`:
`Σ_s (t_{xy} c*_{xs} c_{ys} + h.c.) + W_{xy} n_x n_y + (Δ_{xy} c*_{x↑} c*_{y↓} + h.c.)`. -/
def Couplings.bond (x y : V) : FockOp (Mode V) :=
  hopTerm (K.hop x y) (mode x false) (mode y false) +
    hopTerm (K.hop x y) (mode x true) (mode y true) +
    (K.dens x y : ℂ) • (density x * density y) +
    pairTerm (K.pair x y) (mode x true) (mode y false)

/-- The on-site term `D_x = U_x n_{x↑} n_{x↓} - μ_x n_x`. -/
def Couplings.onSiteTerm (x : V) : FockOp (Mode V) :=
  (K.hubbardU x : ℂ) • (numOp (mode x true) * numOp (mode x false)) -
    (K.chemPot x : ℂ) • density x

omit [LinearOrder V] in
lemma isSelfAdjoint_real_smul_mul {r : ℝ} {a b : FockOp (Mode V)} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (hab : Commute a b) : IsSelfAdjoint ((r : ℂ) • (a * b)) := by
  rw [IsSelfAdjoint, star_smul, star_mul, ha.star_eq, hb.star_eq, hab.eq, Complex.star_def,
    Complex.conj_ofReal]

lemma isSelfAdjoint_bond (x y : V) : IsSelfAdjoint (K.bond x y) :=
  (((isSelfAdjoint_hopTerm _ _ _).add (isSelfAdjoint_hopTerm _ _ _)).add
    (isSelfAdjoint_real_smul_mul (isSelfAdjoint_density x) (isSelfAdjoint_density y)
      (commute_density x y))).add (isSelfAdjoint_pairTerm _ _ _)

lemma parityAut_bond (x y : V) : parityAut (Mode V) (K.bond x y) = K.bond x y := by
  rw [Couplings.bond, map_add, map_add, map_add, parityAut_hopTerm, parityAut_hopTerm,
    parityAut_pairTerm, map_smul, map_mul, parityAut_density, parityAut_density]

lemma bond_mem {x y : V} (hx : x ∈ X) (hy : y ∈ X) : K.bond x y ∈ carLocal site X :=
  (carLocal site X).add_mem ((carLocal site X).add_mem ((carLocal site X).add_mem
    (hopTerm_mem hx hy _ _) (hopTerm_mem hx hy _ _))
    ((carLocal site X).smul_mem ((carLocal site X).mul_mem (density_mem hx) (density_mem hy)) _))
    (pairTerm_mem hx hy _)

lemma norm_bond_le (x y : V) :
    ‖K.bond x y‖ ≤ 4 * ‖K.hop x y‖ + 4 * |K.dens x y| + 2 * ‖K.pair x y‖ := by
  have hd : ‖(K.dens x y : ℂ) • (density x * density y)‖ ≤ 4 * |K.dens x y| := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    calc |K.dens x y| * ‖density x * density y‖ ≤ |K.dens x y| * (2 * 2) :=
          mul_le_mul_of_nonneg_left ((norm_mul_le _ _).trans (mul_le_mul (norm_density_le x)
            (norm_density_le y) (norm_nonneg _) zero_le_two)) (abs_nonneg _)
      _ = 4 * |K.dens x y| := by ring
  calc ‖K.bond x y‖ ≤ 2 * ‖K.hop x y‖ + 2 * ‖K.hop x y‖ + 4 * |K.dens x y| +
        2 * ‖K.pair x y‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (norm_hopTerm_le _ _ _) (norm_hopTerm_le _ _ _)))
          hd)) (norm_pairTerm_le _ _ _))
    _ = _ := by ring

lemma isSelfAdjoint_onSiteTerm (x : V) : IsSelfAdjoint (K.onSiteTerm x) :=
  (isSelfAdjoint_real_smul_mul (isSelfAdjoint_numOp _) (isSelfAdjoint_numOp _)
    (commute_numOp _ _)).sub
    (IsSelfAdjoint.smul (Complex.conj_ofReal _) (isSelfAdjoint_density x))

lemma parityAut_onSiteTerm (x : V) :
    parityAut (Mode V) (K.onSiteTerm x) = K.onSiteTerm x := by
  rw [Couplings.onSiteTerm, map_sub, map_smul, map_smul, map_mul, parityAut_numOp, parityAut_numOp,
    parityAut_density]

lemma onSiteTerm_mem (x : V) : K.onSiteTerm x ∈ carLocal site {x} :=
  (carLocal site {x}).sub_mem ((carLocal site {x}).smul_mem ((carLocal site {x}).mul_mem
    (numOp_mem (mem_singleton_self x) _) (numOp_mem (mem_singleton_self x) _)) _)
    ((carLocal site {x}).smul_mem (density_mem (mem_singleton_self x)) _)

/-!

## D. The interaction on a graph

-/

variable (G : SimpleGraph V)

omit [LinearOrder V] in
lemma nonempty_of_card_eq_two {X : Finset V} (h : #X = 2) : X.Nonempty :=
  card_pos.mp (by rw [h]; norm_num)

open Classical in
/-- The interaction term of a region: the bond term of an edge `{x, y}`, and zero for every other
region. -/
def term (X : Finset V) : FockOp (Mode V) :=
  if h : #X = 2 ∧ ∀ u ∈ X, ∀ v ∈ X, u ≠ v → G.Adj u v then
    K.bond (X.min' (nonempty_of_card_eq_two h.1)) (X.max' (nonempty_of_card_eq_two h.1))
  else 0

lemma term_mem (X : Finset V) : term K G X ∈ carLocal site X := by
  unfold term
  split_ifs with h
  · exact bond_mem K (min'_mem _ _) (max'_mem _ _)
  · exact zero_mem _

lemma isSelfAdjoint_term (X : Finset V) : IsSelfAdjoint (term K G X) := by
  unfold term
  split_ifs
  · exact isSelfAdjoint_bond K _ _
  · exact IsSelfAdjoint.zero _

lemma parityAut_term (X : Finset V) : parityAut (Mode V) (term K G X) = term K G X := by
  unfold term
  split_ifs
  · exact parityAut_bond K _ _
  · exact map_zero _

lemma norm_term_le {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ x y, ‖K.bond x y‖ ≤ B) (X : Finset V) :
    ‖term K G X‖ ≤ B := by
  unfold term
  split_ifs
  · exact hB _ _
  · simpa using hB0

lemma of_term_ne_zero {X : Finset V} (h : term K G X ≠ 0) :
    #X = 2 ∧ ∀ u ∈ X, ∀ v ∈ X, u ≠ v → G.Adj u v := by
  by_contra hc
  exact h (by unfold term; simp [hc])

/-- The interaction of the Hubbard-type model on the graph `G` with couplings `K`. -/
def interaction : Interaction (carNet (site (V := V))) where
  term := term K G
  term_mem := term_mem K G
  isSelfAdjoint_term := isSelfAdjoint_term K G
  isEven_term := parityAut_term K G
  onSite := K.onSiteTerm
  onSite_mem := onSiteTerm_mem K
  isSelfAdjoint_onSite := isSelfAdjoint_onSiteTerm K
  isEven_onSite := parityAut_onSiteTerm K

/-- The interaction has range one. -/
lemma hasFiniteRange : (interaction K G).HasFiniteRange G 1 := fun X hX u hu v hv => by
  rcases eq_or_ne u v with rfl | huv
  · simp
  · exact (SimpleGraph.edist_eq_one_iff_adj.mpr ((of_term_ne_zero K G hX).2 u hu v hv huv)).le

/-!

## E. Bounds and the dynamics

-/

/-- A region containing `v` with a nonzero term is an edge `{v, w}`. -/
lemma mem_image_of_term_ne_zero [G.LocallyFinite] {v : V} {Z : Finset V} (hv : v ∈ Z)
    (h : term K G Z ≠ 0) : Z ∈ (G.neighborFinset v).image fun w => {v, w} := by
  obtain ⟨h2, hadj⟩ := of_term_ne_zero K G h
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp h2
  rw [mem_image]
  rcases mem_insert.mp hv with rfl | hvb
  · exact ⟨b, (G.mem_neighborFinset _ _).mpr (hadj _ (by simp) _ (by simp) hab), rfl⟩
  · rw [mem_singleton] at hvb
    subst hvb
    exact ⟨a, (G.mem_neighborFinset _ _).mpr (hadj _ (by simp) _ (by simp) hab.symm), pair_comm _ _⟩

/-- If the degree is at most `d` and every bond term has norm at most `B`, the interaction is
bounded by `J = 2 d B`. -/
lemma isBoundedBy [G.LocallyFinite] {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x y, ‖K.bond x y‖ ≤ B) : (interaction K G).IsBoundedBy (2 * d * B) := by
  intro v Λ
  classical
  let S := Λ.powerset.filter (v ∈ ·)
  have hle : ∀ Z ∈ S.filter fun Z => term K G Z ≠ 0, (#Z : ℝ) * ‖term K G Z‖ ≤ 2 * B :=
    fun Z hZ => by
      rw [(of_term_ne_zero K G (mem_filter.mp hZ).2).1]
      push_cast
      exact mul_le_mul_of_nonneg_left (norm_term_le K G hB0 hB Z) zero_le_two
  have hsub : S.filter (fun Z => term K G Z ≠ 0) ⊆ (G.neighborFinset v).image fun w => {v, w} :=
    fun Z hZ => mem_image_of_term_ne_zero K G (mem_filter.mp (mem_filter.mp hZ).1).2
      (mem_filter.mp hZ).2
  calc ∑ Z ∈ S, (#Z : ℝ) * ‖(interaction K G).term Z‖
      = ∑ Z ∈ S.filter fun Z => term K G Z ≠ 0, (#Z : ℝ) * ‖term K G Z‖ := by
        refine (sum_filter_of_ne (p := fun Z => term K G Z ≠ 0) fun Z _ hf h0 => hf ?_).symm
        change (#Z : ℝ) * ‖term K G Z‖ = 0
        rw [h0, norm_zero, mul_zero]
    _ ≤ ∑ Z ∈ S.filter fun Z => term K G Z ≠ 0, 2 * B := sum_le_sum hle
    _ = #(S.filter fun Z => term K G Z ≠ 0) * (2 * B) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ d * (2 * B) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast ((card_le_card hsub).trans card_image_le).trans (hdeg v)
    _ = 2 * d * B := by ring

/-- Bounds on the couplings along the edges: `‖t_{xy}‖ ≤ T`, `|W_{xy}| ≤ W`, `‖Δ_{xy}‖ ≤ P`. The
on-site couplings are not bounded. -/
def Couplings.IsBounded (T W P : ℝ) : Prop :=
  (∀ x y, ‖K.hop x y‖ ≤ T) ∧ (∀ x y, |K.dens x y| ≤ W) ∧ ∀ x y, ‖K.pair x y‖ ≤ P

variable {K} in
lemma Couplings.IsBounded.norm_bond_le {T W P : ℝ} (hK : K.IsBounded T W P) (x y : V) :
    ‖K.bond x y‖ ≤ max (4 * T + 4 * W + 2 * P) 0 :=
  (Hubbard.norm_bond_le K x y).trans (le_max_of_le_left
    (by linarith [hK.1 x y, hK.2.1 x y, hK.2.2 x y]))

/-- The infinite-volume dynamics of the Hubbard-type model on a graph of degree at most `d` with
bounded couplings along the edges and arbitrary on-site couplings `U_x`, `μ_x`: the conclusions
of `car_dynamics` hold for every local observable. -/
theorem dynamics_exists [G.LocallyFinite] {d : ℕ} (hdeg : ∀ v, G.degree v ≤ d) {T W P : ℝ}
    (hK : K.IsBounded T W P) {X : Finset V} {A : FockOp (Mode V)} (hA : A ∈ carLocal site X) :
    (∀ T : ℝ, TendstoUniformlyOn (fun Λ t => evolution ((interaction K G).hamiltonian Λ) t A)
      (fun t => (interaction K G).dynamics t A) Filter.atTop (Set.Icc (-T) T)) ∧
    (∀ Λs : ℕ → Finset V, Monotone Λs → (∀ x, ∃ n, x ∈ Λs n) → ∀ T : ℝ,
      TendstoUniformlyOn (fun n t => evolution ((interaction K G).hamiltonian (Λs n)) t A)
        (fun t => (interaction K G).dynamics t A) Filter.atTop (Set.Icc (-T) T)) ∧
    (∀ t, parityAut (Mode V) ((interaction K G).dynamics t A) =
      (interaction K G).dynamics t (parityAut (Mode V) A)) ∧
    HasDerivAt (fun t => (interaction K G).dynamics t A)
      (I • (∑ Z ∈ Interaction.touching (Interaction.reachStep
          (Interaction.locallyFinite_of_hasFiniteRange (hasFiniteRange K G)) X) X,
          ((interaction K G).term Z * A - A * (interaction K G).term Z) +
        ∑ x ∈ X, ((interaction K G).onSite x * A - A * (interaction K G).onSite x))) 0 :=
  car_dynamics (interaction K G) G (hasFiniteRange K G)
    (isBoundedBy K G hdeg (le_max_right _ 0) hK.norm_bond_le) hA

/-!

## F. Examples

All examples have constant couplings along the edges, so they are translation invariant on a
vertex-transitive graph such as `ℤ^d`, and arbitrary on-site couplings.

-/

/-- The Hubbard model: hopping `t`, on-site interaction `U_x` and chemical potential `μ_x`. -/
def hubbard (t : ℂ) (U μ : V → ℝ) : Couplings V := ⟨fun _ _ => t, fun _ _ => 0, fun _ _ => 0, U, μ⟩

/-- The extended Hubbard model: hopping `t`, nearest-neighbour density interaction `W`, on-site
interaction `U_x` and chemical potential `μ_x`. -/
def extendedHubbard (t : ℂ) (W : ℝ) (U μ : V → ℝ) : Couplings V :=
  ⟨fun _ _ => t, fun _ _ => W, fun _ _ => 0, U, μ⟩

/-- Free fermions with translation-invariant pairing `Δ c*_{x↑} c*_{y↓} + h.c.` along the edges:
a model without particle-number conservation. -/
def pairing (t Δ : ℂ) (μ : V → ℝ) : Couplings V :=
  ⟨fun _ _ => t, fun _ _ => 0, fun _ _ => Δ, fun _ => 0, μ⟩

/-- Quartic interactions together with pairing: the extended Hubbard model with translation
invariant pairing `Δ`. -/
def hubbardPairing (t : ℂ) (W : ℝ) (Δ : ℂ) (U μ : V → ℝ) : Couplings V :=
  ⟨fun _ _ => t, fun _ _ => W, fun _ _ => Δ, U, μ⟩

omit [LinearOrder V] in
lemma isBounded_hubbard (t : ℂ) (U μ : V → ℝ) : (hubbard t U μ).IsBounded ‖t‖ 0 0 :=
  ⟨fun _ _ => le_rfl, fun _ _ => by simp [hubbard], fun _ _ => by simp [hubbard]⟩

omit [LinearOrder V] in
lemma isBounded_extendedHubbard (t : ℂ) (W : ℝ) (U μ : V → ℝ) :
    (extendedHubbard t W U μ).IsBounded ‖t‖ |W| 0 :=
  ⟨fun _ _ => le_rfl, fun _ _ => le_rfl, fun _ _ => by simp [extendedHubbard]⟩

omit [LinearOrder V] in
lemma isBounded_pairing (t Δ : ℂ) (μ : V → ℝ) : (pairing t Δ μ).IsBounded ‖t‖ 0 ‖Δ‖ :=
  ⟨fun _ _ => le_rfl, fun _ _ => by simp [pairing], fun _ _ => le_rfl⟩

omit [LinearOrder V] in
lemma isBounded_hubbardPairing (t : ℂ) (W : ℝ) (Δ : ℂ) (U μ : V → ℝ) :
    (hubbardPairing t W Δ U μ).IsBounded ‖t‖ |W| ‖Δ‖ :=
  ⟨fun _ _ => le_rfl, fun _ _ => le_rfl, fun _ _ => le_rfl⟩

end Hubbard

end LatticeFermions
