/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.Locality
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.LocalAlgebra
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
/-!

# The infinite Bose-Hubbard model with pairing

The local interaction of bosons on an arbitrary locally finite graph, with hopping, on-site
repulsion, chemical potential and number-nonconserving pairing.

## i. Overview

The Hamiltonian formally reads

`H = Σ_x (U_x/2 N_x(N_x-1) - μ_x N_x) + Σ_{x~y} (-J_xy (a_x† a_y + a_y† a_x) + Δ_xy a_x† a_y† + h.c.)`.

Each term is a polynomial in the modes of one site or one bond. The graph is arbitrary and
locally finite. Nothing is assumed about the size of the lattice and no particle-number sector is
used. The model is a local interaction in the sense of `LocalGenerators`, with the sites and the
ordered pairs of sites as index set. Hence its Heisenberg derivation is defined on all
polynomials, obeys the Leibniz rule and commutes with the star. Whether it integrates to a
dynamics is a separate question.

## ii. Key results

- `InfiniteBosons.BoseHubbardData`: the parameters of the model.
- `InfiniteBosons.BoseHubbardData.interaction`: the model as a local interaction.
- `InfiniteBosons.BoseHubbardData.heisenberg_mul`: the Leibniz rule.
- `InfiniteBosons.BoseHubbardData.heisenberg_star`: the star rule.

## iii. Table of contents

- A. The model
- B. Its local terms

## iv. References

* M. P. A. Fisher et al., Boson localization and the superfluid-insulator transition, Phys. Rev. B
  40, 546 (1989).
* A. Deuchert, J. Lampart and M. Lemm, Dynamics and equilibrium states of infinite systems of
  lattice bosons, arXiv:2505.13170.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- Parameters of a Bose-Hubbard model with pairing on a locally finite graph: real hopping
amplitudes `J`, on-site repulsion `U`, chemical potential `μ` and complex pairing amplitudes `Δ`. -/
structure BoseHubbardData (L : Type*) where
  /-- The lattice. -/
  graph : SimpleGraph L
  /-- Every site has finitely many neighbours. -/
  locallyFinite : ∀ x, (graph.neighborSet x).Finite
  /-- Hopping amplitudes. -/
  J : L → L → ℝ
  /-- On-site repulsion. -/
  U : L → ℝ
  /-- Chemical potential. -/
  μ : L → ℝ
  /-- Pairing amplitudes. -/
  Δ : L → L → ℂ

namespace BoseHubbardData

variable (D : BoseHubbardData L)

open Classical in
/-- The site term `U/2 N(N-1) - μ N`. -/
def siteTerm (x : L) : adjointable L :=
  ((D.U x / 2 : ℝ) : ℂ) • (numberOp x * numberOp x - numberOp x) - ((D.μ x : ℝ) : ℂ) • numberOp x

open Classical in
/-- The bond term `-J (a_x† a_y + a_y† a_x) + Δ a_x† a_y† + Δ̄ a_y a_x` on adjacent sites. -/
def bondTerm (x y : L) : adjointable L :=
  if D.graph.Adj x y then
    ((-D.J x y : ℝ) : ℂ) • (creOp x * annOp y + creOp y * annOp x) +
      D.Δ x y • (creOp x * creOp y) + (starRingEnd ℂ (D.Δ x y)) • (annOp y * annOp x)
  else 0


lemma star_numberOp (x : L) : star (numberOp x) = numberOp x := by
  simp [numberOp, star_mul, star_annOp, star_creOp]

lemma siteTerm_mem_on (x : L) : D.siteTerm x ∈ (bosonGenerators L).on (({x} : Finset L) : Set L) := by
  have hx : x ∈ (({x} : Finset L) : Set L) := by simp
  have hN : numberOp x ∈ (bosonGenerators L).on (({x} : Finset L) : Set L) :=
    mul_mem (creOp_mem_gen hx) (annOp_mem_gen hx)
  unfold siteTerm
  exact sub_mem (Subalgebra.smul_mem _ (sub_mem (mul_mem hN hN) hN) _)
    (Subalgebra.smul_mem _ hN _)

lemma siteTerm_star (x : L) : star (D.siteTerm x) = D.siteTerm x := by
  unfold siteTerm
  simp [star_sub, star_smul, star_mul, star_numberOp, Complex.star_def, Complex.conj_ofReal]


lemma bondTerm_mem_on (x y : L) :
    D.bondTerm x y ∈ (bosonGenerators L).on (({x, y} : Finset L) : Set L) := by
  unfold bondTerm
  split_ifs
  · have hx : x ∈ (({x, y} : Finset L) : Set L) := by simp
    have hy : y ∈ (({x, y} : Finset L) : Set L) := by simp
    exact add_mem (add_mem (Subalgebra.smul_mem _ (add_mem (mul_mem (creOp_mem_gen hx)
      (annOp_mem_gen hy)) (mul_mem (creOp_mem_gen hy) (annOp_mem_gen hx))) _)
      (Subalgebra.smul_mem _ (mul_mem (creOp_mem_gen hx) (creOp_mem_gen hy)) _))
      (Subalgebra.smul_mem _ (mul_mem (annOp_mem_gen hy) (annOp_mem_gen hx)) _)
  · exact zero_mem _

lemma bondTerm_star (x y : L) : star (D.bondTerm x y) = D.bondTerm x y := by
  unfold bondTerm
  split_ifs
  · simp only [star_add, star_smul, star_mul, star_annOp, star_creOp, Complex.star_def,
      Complex.conj_ofReal, Complex.conj_conj]
    module
  · simp


lemma adj_of_bondTerm_ne_zero {x y : L} (h : D.bondTerm x y ≠ 0) : D.graph.Adj x y := by
  by_contra hn
  apply h
  simp [bondTerm, hn]

/-- **The Bose-Hubbard model with pairing is a local interaction.** The terms are indexed by the
sites and the ordered pairs of sites. -/
def interaction : LocalGenerators.LocalInteraction (bosonGenerators L) (L ⊕ (L × L)) where
  Φ := Sum.elim D.siteTerm (fun p => D.bondTerm p.1 p.2)
  supp := Sum.elim (fun x => {x}) (fun p => {p.1, p.2})
  mem_on := by
    rintro (x | p)
    · exact D.siteTerm_mem_on x
    · exact D.bondTerm_mem_on p.1 p.2
  star_eq := by
    rintro (x | p)
    · exact D.siteTerm_star x
    · exact D.bondTerm_star p.1 p.2
  finite_near := by
    intro z
    have hfin : (({Sum.inl z} : Set (L ⊕ (L × L))) ∪
        (Sum.inr '' (({z} : Set L) ×ˢ D.graph.neighborSet z)) ∪
        (Sum.inr '' (D.graph.neighborSet z ×ˢ ({z} : Set L)))).Finite :=
      ((Set.finite_singleton _).union
        ((Set.finite_singleton z).prod (D.locallyFinite z) |>.image _)).union
        ((D.locallyFinite z).prod (Set.finite_singleton z) |>.image _)
    refine hfin.subset ?_
    rintro (x | ⟨x, y⟩) ⟨hz, hne⟩
    · left; left
      simp only [Sum.elim_inl, Finset.mem_singleton] at hz
      simp [hz]
    · have hadj : D.graph.Adj x y := D.adj_of_bondTerm_ne_zero hne
      simp only [Sum.elim_inr, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h | h
      · subst h
        left; right
        exact ⟨(z, y), ⟨rfl, hadj⟩, rfl⟩
      · subst h
        right
        exact ⟨(x, z), ⟨hadj.symm, rfl⟩, rfl⟩

/-- **The Heisenberg derivation of the infinite Bose-Hubbard model with pairing** obeys the
Leibniz rule. -/
theorem heisenberg_mul {p q : adjointable L} (hp : p ∈ (bosonGenerators L).on Set.univ)
    (hq : q ∈ (bosonGenerators L).on Set.univ) :
    D.interaction.delta (p * q) = D.interaction.delta p * q + p * D.interaction.delta q :=
  D.interaction.delta_mul hp hq

/-- The Heisenberg derivation of the model commutes with the star. -/
theorem heisenberg_star {p : adjointable L} (hp : p ∈ (bosonGenerators L).on Set.univ) :
    D.interaction.delta (star p) = star (D.interaction.delta p) :=
  D.interaction.delta_star hp

end BoseHubbardData

end InfiniteBosons
