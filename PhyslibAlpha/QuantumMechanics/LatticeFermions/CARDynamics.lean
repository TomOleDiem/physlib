/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.LatticeFermions.CARNet
public import PhyslibAlpha.QuantumMechanics.LatticeFermions.InfiniteDynamics
public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!

# The infinite-volume dynamics of interacting lattice fermions

Fermions on the vertices of a locally finite graph, with interactions of finite range bounded
by `J` and arbitrary on-site terms, have a strongly continuous infinite-volume dynamics on the
quasi-local CAR algebra.

## i. Overview

Let `G` be a locally finite graph on the sites `V` (for instance a graph of bounded degree), and
let every fermionic mode `m` sit at a site `site m`. An interaction of the CAR net has *range*
`R` if every nonzero term `Φ(X)` has all its sites at graph distance at most `R` from each other.
Balls of a locally finite graph are finite, so only finitely many regions containing a given site
carry a nonzero term: the interaction is locally finite. Together with the bound
`Σ_{X ∋ x} |X| ‖Φ(X)‖ ≤ J`, the results for graded local nets apply to the CAR net.

The main theorem `car_dynamics` collects the conclusions for a local CAR observable `A ∈ 𝔄_X`:
`α_t(A) = lim_{Λ ↑ V} e^{itH_Λ} A e^{-itH_Λ}` exists in norm uniformly for `t ∈ [-T, T]`, along
every exhaustion of the lattice; the dynamics is a strongly continuous group of `⋆`-automorphisms
of the quasi-local CAR algebra (`Interaction.dynamicsGroup`) commuting with the parity; and

`d/dt α_t(A)|_{t=0} = i Σ_{Z ∩ X ≠ ∅} [Φ(Z), A] + i Σ_{x ∈ X} [D_x, A]`.

No bound on the on-site terms `D_x` and no particle-number conservation is assumed.

## ii. Key results

- `SimpleGraph.finite_setOf_edist_le` : balls of a locally finite graph are finite.
- `LatticeFermions.Interaction.HasFiniteRange` : the range of an interaction on a graph.
- `LatticeFermions.Interaction.locallyFinite_of_hasFiniteRange` : finite range implies local
  finiteness.
- `LatticeFermions.car_dynamics` : the infinite-volume dynamics of lattice fermions.
- `LatticeFermions.Interaction.lieb_robinson_exp` : the Lieb–Robinson bound
  `‖[α_t(A), B]‖ ≤ C ‖A‖ ‖B‖ e^{v t - μ d(X, Y)}` on a graph.

## iii. Table of contents

- A. Balls in locally finite graphs
- B. Interactions of finite range
- C. The dynamics of lattice fermions
- D. The Lieb–Robinson bound on graphs

## iv. References

* O. Bratteli, D. W. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Theorem 6.2.11.
* B. Nachtergaele, R. Sims, A. Young, Lieb-Robinson bounds, the spectral flow, and stability of
  the spectral gap for lattice fermion systems, arXiv:1705.08553, Section 3.

-/

@[expose] public section

noncomputable section

/-!

## A. Balls in locally finite graphs

-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]

/-- The endpoints of the walks of length at most `n` from `x` form a finite set. -/
lemma finite_setOf_walk_length_le (n : ℕ) (x : V) :
    {y | ∃ p : G.Walk x y, p.length ≤ n}.Finite := by
  induction n generalizing x with
  | zero =>
    refine (Set.finite_singleton x).subset fun y ⟨p, hp⟩ => ?_
    exact (Walk.eq_of_length_eq_zero (Nat.le_zero.mp hp)).symm
  | succ n ih =>
    refine ((Set.finite_singleton x).union ((G.neighborSet x).toFinite.biUnion
      fun z _ => ih z)).subset fun y ⟨p, hp⟩ => ?_
    cases p with
    | nil => exact Or.inl rfl
    | cons h q =>
      refine Or.inr (Set.mem_biUnion h ⟨q, ?_⟩)
      simp only [Walk.length_cons] at hp
      omega

/-- Balls of a locally finite graph are finite. -/
lemma finite_setOf_edist_le (n : ℕ) (x : V) : {y | G.edist x y ≤ n}.Finite :=
  (G.finite_setOf_walk_length_le n x).subset fun y hy => by
    obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by simp) hy)
    exact ⟨p, by exact_mod_cast hp.trans_le hy⟩

end SimpleGraph

namespace LatticeFermions

open Finset Complex Filter Topology

/-!

## B. Interactions of finite range

-/

namespace Interaction

variable {V : Type*} [DecidableEq V] {𝔄 : Type*} [CStarAlgebra 𝔄] {N : GradedLocalNet V 𝔄}

/-- An interaction has range `R` on the graph `G` if the sites of every region carrying a nonzero
interaction term are at graph distance at most `R` from each other. -/
def HasFiniteRange (Φ : Interaction N) (G : SimpleGraph V) (R : ℕ) : Prop :=
  ∀ X, Φ.term X ≠ 0 → ∀ x ∈ X, ∀ y ∈ X, G.edist x y ≤ R

omit [DecidableEq V] in
/-- An interaction of finite range on a locally finite graph is locally finite. -/
lemma locallyFinite_of_hasFiniteRange {Φ : Interaction N} {G : SimpleGraph V} [G.LocallyFinite]
    {R : ℕ} (hR : Φ.HasFiniteRange G R) : Φ.LocallyFinite := fun x => by
  have hB := (G.finite_setOf_edist_le R x).finite_subsets
  refine (hB.preimage (Finset.coe_injective.injOn)).subset fun Z ⟨hxZ, hZ⟩ => ?_
  exact fun y hy => hR Z hZ x hxZ y hy

end Interaction

/-!

## C. The dynamics of lattice fermions

-/

variable {M : Type*} [LinearOrder M] {V : Type*} [DecidableEq V] {site : M → V}

/-- The infinite-volume dynamics of interacting lattice fermions. Let the interaction `Φ` of the
CAR net have finite range on a locally finite graph and satisfy `Σ_{X ∋ x} |X| ‖Φ(X)‖ ≤ J`; the
on-site terms are arbitrary. For a local CAR observable `A ∈ 𝔄_X`:

1. `α_t^Λ(A) = e^{itH_Λ} A e^{-itH_Λ}` converges in norm to `α_t(A)`, uniformly for
   `t ∈ [-T, T]`;
2. the same holds along every exhaustion `Λ_n ↑ V`, with the same limit;
3. the dynamics commutes with the parity `(-1)^N`;
4. `t ↦ α_t(A)` is differentiable at zero with derivative
   `i Σ_{Z ∩ X ≠ ∅} [Φ(Z), A] + i Σ_{x ∈ X} [D_x, A]`;

and `α_t` is a strongly continuous one-parameter group of `⋆`-automorphisms of the quasi-local
CAR algebra (`Interaction.dynamicsGroup`, `Interaction.continuous_dynamicsAut`). -/
theorem car_dynamics (Φ : Interaction (carNet site)) (G : SimpleGraph V) [G.LocallyFinite]
    {R : ℕ} (hR : Φ.HasFiniteRange G R) {J : ℝ} (hJ : Φ.IsBoundedBy J) {X : Finset V}
    {A : FockOp M} (hA : A ∈ carLocal site X) :
    (∀ T : ℝ, TendstoUniformlyOn (fun Λ t => evolution (Φ.hamiltonian Λ) t A)
      (fun t => Φ.dynamics t A) atTop (Set.Icc (-T) T)) ∧
    (∀ Λs : ℕ → Finset V, Monotone Λs → (∀ x, ∃ n, x ∈ Λs n) → ∀ T : ℝ,
      TendstoUniformlyOn (fun n t => evolution (Φ.hamiltonian (Λs n)) t A)
        (fun t => Φ.dynamics t A) atTop (Set.Icc (-T) T)) ∧
    (∀ t, parityAut M (Φ.dynamics t A) = Φ.dynamics t (parityAut M A)) ∧
    HasDerivAt (fun t => Φ.dynamics t A)
      (I • (∑ Z ∈ Interaction.touching
          (Interaction.reachStep (Interaction.locallyFinite_of_hasFiniteRange hR) X) X,
          (Φ.term Z * A - A * Φ.term Z) + ∑ x ∈ X, (Φ.onSite x * A - A * Φ.onSite x))) 0 := by
  have hfin := Interaction.locallyFinite_of_hasFiniteRange hR
  have hq := (carNet site).loc_le_quasiLocal X hA
  refine ⟨fun T => Interaction.tendstoUniformlyOn_dynamics hJ hfin hq T,
    fun Λs hmono hcov T => Interaction.tendstoUniformlyOn_dynamics_of_tendsto hJ hfin
      (Interaction.tendsto_atTop_of_exhaustion hmono hcov) hq T,
    fun t => Interaction.parity_dynamics hJ hfin hq t, ?_⟩
  rw [← Interaction.generator_eq hfin hA]
  exact Interaction.hasDerivAt_dynamics hJ hfin hA

/-!

## D. The Lieb–Robinson bound on graphs

For an interaction of range `R` a chain of `k` nonzero terms from `X` to `Y` spans a graph distance
at most `k R`. If all points of `X` and `Y` are at distance at least `n`, only chains of length
`k ≥ n / R` contribute, and `e^{-μ n} ≤ e^{μ (k R - n)}` turns the Lieb–Robinson series into an
exponential: with `v = 2 J e^{μ R}`,

`‖[α_t(A), B]‖ ≤ 2 max(1, |X|) ‖A‖ ‖B‖ e^{v |t| - μ n}` for every `μ ≥ 0`.

The constants do not depend on the region `Λ` nor on the on-site terms.

-/

namespace Interaction

open Nat

variable {V : Type*} [DecidableEq V] {𝔄 : Type*} [CStarAlgebra 𝔄] {N : GradedLocalNet V 𝔄}
  {Φ : Interaction N} {G : SimpleGraph V} {R : ℕ}

/-- A chain of `k` nonzero interaction terms of range `R` from `X` to `Y` spans graph distance at
most `k R`. -/
lemma exists_edist_le_of_chainWeight_ne_zero (hR : Φ.HasFiniteRange G R) (Λ : Finset V)
    (k : ℕ) {X Y : Finset V} (hw : Φ.chainWeight Λ k X Y ≠ 0) :
    ∃ x ∈ X, ∃ y ∈ Y, G.edist x y ≤ k * R := by
  induction k generalizing X with
  | zero =>
    simp only [chainWeight, ne_eq, ite_eq_left_iff, Classical.not_imp] at hw
    obtain ⟨x, hxX, hxY⟩ := not_disjoint_iff.mp hw.1
    exact ⟨x, hxX, x, hxY, by simp⟩
  | succ k ih =>
    obtain ⟨Z, hZ, hZ0⟩ := exists_ne_zero_of_sum_ne_zero hw
    have hZ1 : Φ.term Z ≠ 0 := fun h0 => hZ0 (by rw [h0, norm_zero, zero_mul])
    obtain ⟨z, hz, y, hy, hzy⟩ := ih fun h0 => hZ0 (by rw [h0, mul_zero])
    obtain ⟨x, hxZ, hxX⟩ := not_disjoint_iff.mp (mem_touching.mp hZ).2
    refine ⟨x, hxX, y, hy, (G.edist_triangle (v := z)).trans ?_⟩
    calc G.edist x z + G.edist z y ≤ R + k * R := add_le_add (hR Z hZ1 x hxZ z hz) hzy
      _ = (k + 1 : ℕ) * R := by push_cast; ring

/-- The Lieb–Robinson coefficients of a chain weight are bounded by the exponentially weighted
majorant `max(1, |X|) (2 t J e^{μ R})^k / k! · e^{-μ n}`. -/
lemma lrCoeff_mul_chainWeight_le_exp (hR : Φ.HasFiniteRange G R) {J : ℝ}
    (hJ : Φ.IsBoundedBy J) (hJ0 : 0 ≤ J) (Λ : Finset V) {X Y : Finset V} {n : ℕ}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, (n : ℕ∞) ≤ G.edist x y) {μ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 ≤ t)
    (k : ℕ) :
    lrCoeff k t * Φ.chainWeight Λ k X Y ≤
      max 1 (#X : ℝ) * ((2 * t * J * Real.exp (μ * R)) ^ k / k !) * Real.exp (-(μ * n)) := by
  by_cases hw : Φ.chainWeight Λ k X Y = 0
  · rw [hw, mul_zero]; positivity
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_edist_le_of_chainWeight_ne_zero hR Λ k hw
  have hn : (n : ℝ) ≤ k * R := by exact_mod_cast (ENat.natCast_le_natCast.mp ((hXY x hx y hy).trans hxy))
  have hexp : 1 ≤ Real.exp (μ * R) ^ k * Real.exp (-(μ * n)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.one_le_exp (by nlinarith)
  calc lrCoeff k t * Φ.chainWeight Λ k X Y
      ≤ max 1 (#X : ℝ) * ((2 * t * J) ^ k / k !) :=
        (mul_le_mul_of_nonneg_left (chainWeight_le_chainWeightAll Λ k X Y)
          (lrCoeff_nonneg k ht)).trans (lrCoeff_mul_chainWeightAll_le hJ hJ0 Λ X k ht)
    _ ≤ max 1 (#X : ℝ) * ((2 * t * J) ^ k / k !) *
          (Real.exp (μ * R) ^ k * Real.exp (-(μ * n))) :=
        le_mul_of_one_le_right (by positivity) hexp
    _ = _ := by rw [mul_pow]; ring

lemma hasSum_exp_mul (x c : ℝ) : HasSum (fun k : ℕ => c * (x ^ k / k !)) (c * Real.exp x) := by
  have h : Real.exp x = ∑' k : ℕ, x ^ k / k ! := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [h]
  exact ((Real.summable_pow_div_factorial x).hasSum).mul_left c

/-- The Lieb–Robinson bound on a graph. For an interaction of range `R` bounded by `J`,
`A ∈ 𝔄_X` with `X ⊆ Λ`, `B ∈ 𝔄_Y` even, and all points of `X` and `Y` at graph distance at
least `n`, for every `μ ≥ 0` and `t ≥ 0`:

`‖[α_t(A), B]‖ ≤ 2 max(1, |X|) ‖A‖ ‖B‖ e^{v t - μ n}`, `v = 2 J e^{μ R}`.

The constants are independent of `Λ` and of the on-site terms. -/
lemma lieb_robinson_exp (hR : Φ.HasFiniteRange G R) {J : ℝ} (hJ : Φ.IsBoundedBy J)
    (hJ0 : 0 ≤ J) (Λ Y : Finset V) {B : 𝔄} (hB : B ∈ N.loc Y) (hBe : N.IsEven B)
    {X : Finset V} (hX : X ⊆ Λ) {A : 𝔄} (hA : A ∈ N.loc X) {n : ℕ}
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, (n : ℕ∞) ≤ G.edist x y) {μ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 ≤ t) :
    ‖evolution (Φ.hamiltonian Λ) t A * B - B * evolution (Φ.hamiltonian Λ) t A‖ ≤
      2 * max 1 (#X : ℝ) * ‖A‖ * ‖B‖ *
        Real.exp (2 * J * Real.exp (μ * R) * t - μ * n) := by
  have hsum := (hasSum_exp_mul (2 * t * J * Real.exp (μ * R)) (max 1 (#X : ℝ))).mul_right
    (Real.exp (-(μ * n)))
  have hle := (summable_lrCoeff_mul_chainWeight hJ hJ0 Λ X Y ht).tsum_le_tsum
    (lrCoeff_mul_chainWeight_le_exp hR hJ hJ0 Λ hXY hμ ht) hsum.summable
  rw [hsum.tsum_eq] at hle
  refine (Φ.lieb_robinson hJ Λ Y hB hBe hX hA ht).trans ?_
  calc 2 * ‖A‖ * ‖B‖ * ∑' k, lrCoeff k t * Φ.chainWeight Λ k X Y
      ≤ 2 * ‖A‖ * ‖B‖ * (max 1 (#X : ℝ) * Real.exp (2 * t * J * Real.exp (μ * R)) *
          Real.exp (-(μ * n))) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by
        rw [mul_assoc (max 1 (#X : ℝ)), ← Real.exp_add, sub_eq_add_neg]
        ring_nf

end Interaction

end LatticeFermions
