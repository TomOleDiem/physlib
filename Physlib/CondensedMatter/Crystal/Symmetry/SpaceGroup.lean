/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.PeriodicGraph
public import Physlib.CondensedMatter.Crystal.Symmetry.PointOperations

/-!
# Space group of a periodic graph

The crystal symmetries preserving the bonds of a periodic graph.

## i. Overview

A periodic graph need not have all the symmetries of its underlying crystal. Its space group
consists of the crystal symmetries that preserve adjacency,

`Adj (φ x) (φ y) ↔ Adj x y`.

Since the graph is determined by finitely many bonds in a reference cell, a crystal symmetry
preserves the graph precisely when `Symmetry.mapBond` maps these bonds to bonds. Thus, the space
group can be characterized by a finite condition.

The point group consists of the point operations of the space group.

## ii. Key results

- `PeriodicGraph.spaceGroup`: The crystal symmetries preserving adjacency.
- `PeriodicGraph.pointGroup`: The point operations of the space group.
- `PeriodicGraph.mem_spaceGroup_iff_preservesBonds`: A crystal symmetry belongs to the space
  group exactly when it preserves the finite bond set.

## iii. Table of contents

- A. Space group and translations
- B. Point group
- C. Finite bond criterion

## iv. References

* F. Göhmann, *Introduction to Solid State Physics*, lecture L3, Section 3.1.
  [ref: goehmann_solid_state_2021]

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G] {C : Crystal G}

namespace PeriodicGraph

variable {g : PeriodicGraph C} {φ ψ : Symmetry C}

/-! ## A. Space group and translations -/

/-- The subgroup of crystal symmetries preserving adjacency. -/
noncomputable def spaceGroup (g : PeriodicGraph C) : Subgroup (Symmetry C) :=
  g.graphAutomorphisms.comap (Symmetry.toPerm C)

/-- A crystal symmetry belongs to the space group exactly when it preserves adjacency. -/
lemma mem_spaceGroup_iff :
    φ ∈ g.spaceGroup ↔ ∀ x y, g.toSimpleGraph.Adj (φ x) (φ y) ↔ g.toSimpleGraph.Adj x y := by
  rfl

/-- Every lattice translation belongs to the space group. -/
lemma translation_mem_spaceGroup (a : G) : Symmetry.translation C a ∈ g.spaceGroup := by
  intro x y
  exact g.adj_vadd a x y

/-- The translation subgroup is contained in the space group. -/
lemma translations_le_spaceGroup : Symmetry.translations C ≤ g.spaceGroup := by
  rintro _ ⟨a, rfl⟩
  exact translation_mem_spaceGroup _

/-! ## B. Point group -/

/-- The image of the space group under the point-operation homomorphism. -/
noncomputable def pointGroup (g : PeriodicGraph C) : Subgroup (Symmetry C) :=
  g.spaceGroup.map (Symmetry.pointOp C)

/-- A symmetry is in the point group exactly when it is a point operation of a space-group
element. -/
lemma mem_pointGroup_iff :
    ψ ∈ g.pointGroup ↔ ∃ φ ∈ g.spaceGroup, Symmetry.pointOp C φ = ψ :=
  Subgroup.mem_map

/-! ## C. Finite bond criterion -/

variable [DecidableEq G] [DecidableEq C.UnitCell] [Fintype C.UnitCell]

/-- A crystal symmetry maps every bond of the reference cell to another such bond. -/
def PreservesBonds (g : PeriodicGraph C) (φ : Symmetry C) : Prop :=
  ∀ b ∈ g.bonds, φ.mapBond b ∈ g.bonds

/-- Preserving the reference-cell bonds implies preserving adjacency in the forward direction. -/
lemma PreservesBonds.map_adj (h : g.PreservesBonds φ) {x y : C.Site}
    (hxy : g.toSimpleGraph.Adj x y) : g.toSimpleGraph.Adj (φ x) (φ y) := by
  have hl : (⟨x.label, y.label, y.cell - x.cell⟩ : Bond C).Links x y :=
    ⟨rfl, rfl, (add_sub_cancel _ _).symm⟩
  exact g.adj_of_links (h _ (g.adj_iff_mem_bonds hl |>.1 hxy)) (φ.mapBond_links hl)

/-- Every space-group symmetry preserves the reference-cell bonds. -/
lemma PreservesBonds.of_mem_spaceGroup (hφ : φ ∈ g.spaceGroup) : g.PreservesBonds φ := by
  intro b hb
  have hl : b.Links ⟨0, b.source⟩ ⟨b.displacement, b.target⟩ := ⟨rfl, rfl, (zero_add _).symm⟩
  have hadj := (g.mem_bonds b).1 hb
  have hmap := (hφ _ _).2 hadj
  exact (g.adj_iff_mem_bonds (φ.mapBond_links hl)).1 hmap

/-- Preservation of the finite bond set is inherited by the inverse symmetry. -/
lemma PreservesBonds.inv (h : g.PreservesBonds φ) : g.PreservesBonds φ⁻¹ := by
  intro b hb
  have hbij := (g.bonds.finite_toSet.injOn_iff_bijOn_of_mapsTo h).1
    (Function.LeftInverse.injective φ.mapBond_inv_mapBond).injOn
  obtain ⟨b', hb', rfl⟩ := hbij.surjOn hb
  rwa [φ.mapBond_inv_mapBond]

/-- A crystal symmetry preserves adjacency exactly when it preserves the reference-cell bonds. -/
lemma mem_spaceGroup_iff_preservesBonds : φ ∈ g.spaceGroup ↔ g.PreservesBonds φ := by
  constructor
  · exact PreservesBonds.of_mem_spaceGroup
  · intro h
    rw [mem_spaceGroup_iff]
    intro x y
    constructor
    · intro hxy
      simpa using h.inv.map_adj hxy
    · exact h.map_adj

end PeriodicGraph

end Physlib.CondensedMatter.Crystal
