/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.BondSymmetries
public import Physlib.CondensedMatter.Crystal.Species

/-!
# The honeycomb lattice

Two sites per cell, each bonded to three sites of the other kind, with a half-turn that exchanges
the two sites.

## i. Overview

The honeycomb lattice has two sites `a` and `b` in each cell of `ℤ²`. Each `a` is bonded to three
`b` sites: one in its own cell and one in each of two neighboring cells. A half-turn about the
midpoint of a bond exchanges `a` and `b`, sending each cell `n` to `-n`. It maps every site to a
site and every bond to a bond, so it is in the space group. It exchanges the two labels, so it is a
symmetry of the crystal when both have the same species, and not when the species differ.

## ii. Key results

- `Crystal.honeycomb` : the crystal with two sites per cell of `ℤ²`.
- `Crystal.honeycombGraph` : its bonds.
- `Crystal.halfTurn` : the half-turn exchanging the two sites.
- `Crystal.halfTurn_mem_spaceGroup` : the half-turn preserves the bonds.
- `Crystal.halfTurn_mem_speciesSpaceGroup` : with equal species it is a crystal symmetry.
- `Crystal.halfTurn_not_mem_speciesGroup` : with distinct species it is not.

## iii. Table of contents

- A. The honeycomb lattice
- B. The half-turn

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

/-! ## A. The honeycomb lattice -/

/-- Two sites per cell of `ℤ²`. -/
abbrev honeycomb := Crystal.ofUnitCell (Fin 2 → ℤ) (Fin 2)

/-- The displacements from `a` to its three neighbors `b`. -/
def honeycombSteps : Finset (Fin 2 → ℤ) := {0, Pi.single 0 1, Pi.single 1 1}

/-- The bonds of the honeycomb lattice: from `a` to `b` in the same cell and in two neighboring
cells. -/
def honeycombBonds : Finset (Bond honeycomb) :=
  honeycombSteps.image fun d => ⟨0, 1, d⟩

/-- Each `a` is bonded to three `b` sites. -/
def honeycombGraph : PeriodicGraph honeycomb := PeriodicGraph.ofBonds honeycombBonds

/-! ## B. The half-turn -/

/-- The half-turn about the midpoint of a bond: it exchanges `a` and `b` and sends the cell `n`
to `-n`. -/
def halfTurn : Symmetry honeycomb :=
  Symmetry.linear honeycomb (AddEquiv.neg _) (Equiv.swap 0 1)

/-- The half-turn is its own inverse. -/
lemma halfTurn_inv : halfTurn⁻¹ = halfTurn := by
  rw [inv_eq_iff_mul_eq_one]
  ext x : 1
  refine Site.ext ?_ (Equiv.swap_apply_self _ _ _)
  simp [halfTurn]
  rfl

/-- The half-turn maps every bond to a bond. -/
lemma halfTurn_adj (d : Fin 2 → ℤ) (hd : d ∈ honeycombSteps) :
    honeycombGraph.toSimpleGraph.Adj (halfTurn ⟨0, 0⟩) (halfTurn ⟨d, 1⟩) := by
  refine (PeriodicGraph.adj_ofBonds honeycombBonds _ _).2 ⟨?_, ⟨0, 1, d⟩,
    Finset.mem_image.2 ⟨d, hd, rfl⟩, Or.inr ⟨rfl, rfl, by simp [halfTurn]⟩⟩
  intro h
  exact absurd (congrArg Site.label h)
    (show ¬ (Equiv.swap (0 : Fin 2) 1 0 = Equiv.swap (0 : Fin 2) 1 1) by decide)

/-- **The half-turn is in the space group of the honeycomb lattice.** -/
lemma halfTurn_mem_spaceGroup : halfTurn ∈ honeycombGraph.spaceGroup := by
  refine PeriodicGraph.mem_spaceGroup_ofBonds _ _ ?_ ?_
  · intro b hb
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hb
    exact halfTurn_adj d hd
  · rw [halfTurn_inv]
    intro b hb
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hb
    exact halfTurn_adj d hd

/-- With equal species, the half-turn is a symmetry of the crystal. -/
lemma halfTurn_mem_speciesSpaceGroup :
    halfTurn ∈ honeycombGraph.speciesSpaceGroup (Function.const _ ()) := by
  refine ⟨halfTurn_mem_spaceGroup, ?_⟩
  intro _
  rfl

/-- With the two sites of different species, the half-turn is not a symmetry of the crystal. -/
lemma halfTurn_not_mem_speciesGroup :
    halfTurn ∉ speciesGroup (C := honeycomb) id := by
  intro h
  exact absurd (h 0) (by decide)

end Physlib.CondensedMatter.Crystal
