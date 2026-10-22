/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.PeriodicGraph

/-!
# Symmetries of the graph of a list of bonds

To check that a symmetry is in the space group of the graph of a finite list of bonds, it is enough
to look at the bonds of the list.

## i. Overview

The graph of a finite list of bonds is the translates of those bonds. A symmetry commutes with
translation up to the lattice automorphism, so it maps the graph into itself as soon as it maps
the bonds of the list to bonds of the graph. The symmetry is in the space group when this holds for
it and for its inverse.

## ii. Key results

- `Crystal.PeriodicGraph.adj_ofBonds_apply` : a symmetry that maps the listed bonds to bonds maps
  every bond to a bond.
- `Crystal.PeriodicGraph.mem_spaceGroup_ofBonds` : the symmetries of the graph of a list of bonds
  are checked on the list.

## iii. Table of contents

- A. Checking a symmetry on a list of bonds

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

namespace PeriodicGraph

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G] {C : Crystal G}
  [DecidableEq G] [DecidableEq C.UnitCell]

/-! ## A. Checking a symmetry on a list of bonds -/

/-- A symmetry that maps each listed bond to a bond of the graph maps every bond of the graph to
a bond. -/
lemma adj_ofBonds_apply (B : Finset (Bond C)) (φ : Symmetry C)
    (h : ∀ b ∈ B, (ofBonds B).toSimpleGraph.Adj (φ ⟨0, b.source⟩) (φ ⟨b.displacement, b.target⟩))
    {x y : C.Site} (hxy : (ofBonds B).toSimpleGraph.Adj x y) :
    (ofBonds B).toSimpleGraph.Adj (φ x) (φ y) := by
  have key : ∀ b ∈ B, ∀ {x y : C.Site}, b.Links x y →
      (ofBonds B).toSimpleGraph.Adj (φ x) (φ y) := by
    intro b hb x y hl
    have hx : x = x.cell +ᵥ (⟨0, b.source⟩ : C.Site) := Site.ext (by simp) hl.1
    have hy : y = x.cell +ᵥ (⟨b.displacement, b.target⟩ : C.Site) := Site.ext hl.2.2 hl.2.1
    rw [hx, hy, φ.map_vadd, φ.map_vadd, (ofBonds B).adj_vadd]
    exact h b hb
  obtain ⟨-, b, hb, hl | hl⟩ := (adj_ofBonds B x y).1 hxy
  exacts [key b hb hl, (key b hb hl).symm]

/-- A symmetry is in the space group of the graph of a list of bonds when it and its inverse map the
listed bonds to bonds. -/
lemma mem_spaceGroup_ofBonds (B : Finset (Bond C)) (φ : Symmetry C)
    (h : ∀ b ∈ B, (ofBonds B).toSimpleGraph.Adj (φ ⟨0, b.source⟩) (φ ⟨b.displacement, b.target⟩))
    (h' : ∀ b ∈ B,
      (ofBonds B).toSimpleGraph.Adj (φ⁻¹ ⟨0, b.source⟩) (φ⁻¹ ⟨b.displacement, b.target⟩)) :
    φ ∈ (ofBonds B).spaceGroup := by
  intro x y
  constructor
  · intro hxy
    convert adj_ofBonds_apply B φ⁻¹ h' hxy using 2 <;> exact (Symmetry.inv_apply_apply φ _).symm
  · exact adj_ofBonds_apply B φ h

end PeriodicGraph

end Physlib.CondensedMatter.Crystal
