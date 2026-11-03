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

## iii. Table of contents

- A. Balls in locally finite graphs
- B. Interactions of finite range
- C. The dynamics of lattice fermions

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

end LatticeFermions
