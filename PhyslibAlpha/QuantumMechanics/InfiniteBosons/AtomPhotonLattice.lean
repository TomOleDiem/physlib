/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.SpinBosonLocal
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
/-!

# The infinite Jaynes-Cummings-Hubbard lattice

Photons hopping between coupled cavities on an arbitrary locally finite graph, each cavity coupled
to a two-level atom.

## i. Overview

The Hamiltonian formally reads

`H = Σ_x (ω_x a_x† a_x + ε_x σ_x⁺ σ_x⁻ + g_x a_x† σ_x⁻ + ḡ_x σ_x⁺ a_x) - Σ_{x~y} J_xy (a_x† a_y + a_y† a_x)`.

It does not conserve the photon number. It conserves the total number of photons and excited atoms
when all couplings are of the above form. No sector decomposition is used. The model is a local
interaction in the sense of `LocalGenerators`. The terms are indexed by the cavities and the
ordered pairs of cavities. Hence the Heisenberg derivation is defined on all polynomials in the
photon and atom operators of the whole lattice, and it obeys the Leibniz rule and commutes with
the star.

## ii. Key results

- `InfiniteBosons.AtomPhotonData`: the parameters.
- `InfiniteBosons.AtomPhotonData.interaction`: the model as a local interaction.
- `InfiniteBosons.AtomPhotonData.heisenberg_mul`, `heisenberg_star`: Leibniz and star rule.

## iii. Table of contents

- A. The model
- B. The local interaction

## iv. References

* E. T. Jaynes and F. W. Cummings, Proc. IEEE 51, 89 (1963).
* M. J. Hartmann, F. G. S. L. Brandão and M. B. Plenio, Strongly interacting polaritons in coupled
  arrays of cavities, Nature Physics 2, 849 (2006).
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- Parameters of the Jaynes-Cummings-Hubbard lattice: photon hopping `J` between adjacent
cavities, photon frequency `ω`, atom frequency `ε` and atom-photon coupling `g`. -/
structure AtomPhotonData (L : Type*) where
  /-- The lattice of cavities. -/
  graph : SimpleGraph L
  /-- Every cavity has finitely many neighbours. -/
  locallyFinite : ∀ x, (graph.neighborSet x).Finite
  /-- Photon hopping amplitudes. -/
  J : L → L → ℝ
  /-- Photon frequencies. -/
  ω : L → ℝ
  /-- Atom frequencies. -/
  ε : L → ℝ
  /-- Atom-photon couplings. -/
  g : L → ℂ

namespace AtomPhotonData

variable (D : AtomPhotonData L)

/-- The photon number operator at `x`. -/
def photonNumber (x : L) : Adjointable (SBBasis L) := creOpS x * annOpS x

/-- The atom excitation operator `σ⁺σ⁻` at `x`. -/
def atomNumber (x : L) : Adjointable (SBBasis L) := raiseOpS x * lowOpS x

/-- The site term `ω a†a + ε σ⁺σ⁻ + g a†σ⁻ + ḡ σ⁺a`. -/
def siteTerm (x : L) : Adjointable (SBBasis L) :=
  ((D.ω x : ℝ) : ℂ) • photonNumber x + ((D.ε x : ℝ) : ℂ) • atomNumber x +
    jaynesCummings x (D.g x)

open Classical in
/-- The bond term `-J (a_x† a_y + a_y† a_x)` of adjacent cavities. -/
def bondTerm (x y : L) : Adjointable (SBBasis L) :=
  if D.graph.Adj x y then ((-D.J x y : ℝ) : ℂ) • (creOpS x * annOpS y + creOpS y * annOpS x)
  else 0

lemma star_photonNumber (x : L) : star (photonNumber x) = photonNumber x := by
  simp [photonNumber, star_mul, star_annOpS, star_creOpS]

lemma star_atomNumber (x : L) : star (atomNumber x) = atomNumber x := by
  simp [atomNumber, star_mul, star_lowOpS, star_raiseOpS]

lemma siteTerm_star (x : L) : star (D.siteTerm x) = D.siteTerm x := by
  unfold siteTerm
  rw [star_add, star_add, star_smul, star_smul, star_photonNumber, star_atomNumber,
    star_jaynesCummings]
  simp [Complex.star_def, Complex.conj_ofReal]

lemma bondTerm_star (x y : L) : star (D.bondTerm x y) = D.bondTerm x y := by
  unfold bondTerm
  split_ifs
  · simp [star_add, star_smul, star_mul, star_annOpS, star_creOpS, Complex.star_def,
      Complex.conj_ofReal, add_comm]
  · simp


section Membership

variable {X : Set L}

lemma annOpS_mem {x : L} (hx : x ∈ X) : annOpS x ∈ (sbGenerators L).on X :=
  (sbGenerators L).gen_mem_on hx (by simp [sbGenerators])

lemma creOpS_mem {x : L} (hx : x ∈ X) : creOpS x ∈ (sbGenerators L).on X :=
  (sbGenerators L).gen_mem_on hx (by simp [sbGenerators])

lemma lowOpS_mem {x : L} (hx : x ∈ X) : lowOpS x ∈ (sbGenerators L).on X :=
  (sbGenerators L).gen_mem_on hx (by simp [sbGenerators])

lemma raiseOpS_mem {x : L} (hx : x ∈ X) : raiseOpS x ∈ (sbGenerators L).on X :=
  (sbGenerators L).gen_mem_on hx (by simp [sbGenerators])

end Membership

lemma siteTerm_mem (x : L) : D.siteTerm x ∈ (sbGenerators L).on (({x} : Finset L) : Set L) := by
  have hx : x ∈ (({x} : Finset L) : Set L) := by simp
  unfold siteTerm jaynesCummings photonNumber atomNumber
  exact add_mem (add_mem (Subalgebra.smul_mem _ (mul_mem (creOpS_mem hx) (annOpS_mem hx)) _)
    (Subalgebra.smul_mem _ (mul_mem (raiseOpS_mem hx) (lowOpS_mem hx)) _))
    (add_mem (Subalgebra.smul_mem _ (mul_mem (creOpS_mem hx) (lowOpS_mem hx)) _)
      (Subalgebra.smul_mem _ (mul_mem (raiseOpS_mem hx) (annOpS_mem hx)) _))

lemma bondTerm_mem (x y : L) :
    D.bondTerm x y ∈ (sbGenerators L).on (({x, y} : Finset L) : Set L) := by
  unfold bondTerm
  split_ifs
  · have hx : x ∈ (({x, y} : Finset L) : Set L) := by simp
    have hy : y ∈ (({x, y} : Finset L) : Set L) := by simp
    exact Subalgebra.smul_mem _ (add_mem (mul_mem (creOpS_mem hx) (annOpS_mem hy))
      (mul_mem (creOpS_mem hy) (annOpS_mem hx))) _
  · exact zero_mem _

lemma adj_of_bondTerm_ne_zero {x y : L} (h : D.bondTerm x y ≠ 0) : D.graph.Adj x y := by
  by_contra hn
  apply h
  simp [bondTerm, hn]

/-- **The Jaynes-Cummings-Hubbard lattice is a local interaction.** -/
def interaction : LocalGenerators.LocalInteraction (sbGenerators L) (L ⊕ (L × L)) where
  Φ := Sum.elim D.siteTerm (fun p => D.bondTerm p.1 p.2)
  supp := Sum.elim (fun x => {x}) (fun p => {p.1, p.2})
  mem_on := by
    rintro (x | p)
    · exact D.siteTerm_mem x
    · exact D.bondTerm_mem p.1 p.2
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

/-- **Leibniz rule for the Heisenberg derivation of the atom-photon lattice.** -/
theorem heisenberg_mul {p q : Adjointable (SBBasis L)} (hp : p ∈ (sbGenerators L).on Set.univ)
    (hq : q ∈ (sbGenerators L).on Set.univ) :
    D.interaction.delta (p * q) = D.interaction.delta p * q + p * D.interaction.delta q :=
  D.interaction.delta_mul hp hq

/-- The Heisenberg derivation of the atom-photon lattice commutes with the star. -/
theorem heisenberg_star {p : Adjointable (SBBasis L)} (hp : p ∈ (sbGenerators L).on Set.univ) :
    D.interaction.delta (star p) = star (D.interaction.delta p) :=
  D.interaction.delta_star hp

end AtomPhotonData

end InfiniteBosons
