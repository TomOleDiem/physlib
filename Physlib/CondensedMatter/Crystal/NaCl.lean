/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.BondSymmetries
public import Physlib.CondensedMatter.Crystal.Species
public import Mathlib.Tactic.FinCases

/-!
# A NaCl-type pattern

Na and Cl on alternating sites of a square array: the shift by one site is a symmetry of the bare
pattern, but not of the crystal.

## i. Overview

Place two kinds of atoms on alternating sites of a square array. A cell is a pair of neighboring
sites in a row, so the translation group is `ℤ²` and each cell has two labels, `0` for Na and `1`
for Cl. Every site is bonded to its four neighbors. Shifting the array by one site spacing along a
row exchanges the two kinds of site and maps every bond to a bond, so it is a symmetry of the
sites and bonds. It sends Na sites to Cl sites, so it is not a symmetry once the species are
assigned.

## ii. Key results

- `Crystal.nacl` : the crystal with two sites per cell of `ℤ²`.
- `Crystal.naclGraph` : the bonds of the square array.
- `Crystal.naclShift` : the shift by one site spacing along a row.
- `Crystal.naclShift_mem_spaceGroup` : the shift preserves the bonds.
- `Crystal.naclShift_not_mem_speciesGroup` : the shift does not keep the species.

## iii. Table of contents

- A. The square array with two kinds of site
- B. The shift by one site

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

/-! ## A. The square array with two kinds of site -/

/-- Two sites per cell of `ℤ²`: label `0` is Na and label `1` is Cl. -/
abbrev nacl := Crystal.ofUnitCell (Fin 2 → ℤ) (Fin 2)

/-- The bonds of the square array: along a row inside the cell and to the next cell, and up a
column from each kind of site. -/
def naclBonds : Finset (Bond nacl) :=
  {⟨0, 1, 0⟩, ⟨1, 0, Pi.single 0 1⟩, ⟨0, 0, Pi.single 1 1⟩, ⟨1, 1, Pi.single 1 1⟩}

/-- Every site is bonded to its four neighbors. -/
def naclGraph : PeriodicGraph nacl := PeriodicGraph.ofBonds naclBonds

/-! ## B. The shift by one site -/

/-- The shift of the sites of each label: Na by one cell along a row, Cl not at all. -/
def naclCells (i : Fin 2) : Fin 2 → ℤ := if i = 0 then Pi.single 0 1 else 0

/-- The shift by one site spacing along a row: Na goes to the Cl in the same cell, and Cl goes to
the Na in the next cell. -/
noncomputable def naclShift : Symmetry nacl :=
  Symmetry.ofData nacl 0 (Equiv.swap 0 1) (naclCells ∘ Equiv.swap 0 1)

/-- The shift moves the site `⟨n, i⟩` to the other kind of site, one cell along if that is a Na. -/
lemma naclShift_apply (n : Fin 2 → ℤ) (i : Fin 2) :
    naclShift ⟨n, i⟩ = ⟨n + naclCells (Equiv.swap 0 1 i), Equiv.swap 0 1 i⟩ := rfl

/-- The inverse of the shift. -/
lemma naclShift_inv_apply (n : Fin 2 → ℤ) (i : Fin 2) :
    naclShift⁻¹ ⟨n, i⟩ = ⟨n - naclCells i, Equiv.swap 0 1 i⟩ := by
  have h : naclShift ⟨n - naclCells i, Equiv.swap 0 1 i⟩ = ⟨n, i⟩ := by
    rw [naclShift_apply, Equiv.swap_apply_self]
    exact Site.ext (sub_add_cancel _ _) rfl
  rw [← Symmetry.inv_apply_apply naclShift ⟨n - naclCells i, Equiv.swap 0 1 i⟩, h]

/-- Two sites joined by one of the bonds are adjacent. -/
lemma naclAdj {x y : nacl.Site} {b : Bond nacl} (hb : b ∈ naclBonds) (hne : x ≠ y)
    (hl : b.Links x y ∨ b.Links y x) : naclGraph.toSimpleGraph.Adj x y :=
  (PeriodicGraph.adj_ofBonds naclBonds x y).2 ⟨hne, b, hb, hl⟩

/-- The shift maps every bond to a bond. -/
lemma naclShift_adj : ∀ b ∈ naclBonds,
    naclGraph.toSimpleGraph.Adj (naclShift ⟨0, b.source⟩)
      (naclShift ⟨b.displacement, b.target⟩) := by
  intro b hb
  simp only [naclBonds, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  · refine naclAdj (b := ⟨1, 0, Pi.single 0 1⟩) (by simp [naclBonds]) ?_ (Or.inl ⟨rfl, rfl, ?_⟩)
    · intro h
      exact absurd (congrArg Site.label h) (by decide)
    · ext j; fin_cases j <;> simp [naclShift_apply, naclCells]
  · refine naclAdj (b := ⟨0, 1, 0⟩) (by simp [naclBonds]) ?_ (Or.inl ⟨rfl, rfl, ?_⟩)
    · intro h
      exact absurd (congrArg Site.label h) (by decide)
    · ext j; fin_cases j <;> simp [naclShift_apply, naclCells]
  · refine naclAdj (b := ⟨1, 1, Pi.single 1 1⟩) (by simp [naclBonds]) ?_ (Or.inl ⟨rfl, rfl, ?_⟩)
    · intro h
      have := congrFun (congrArg Site.cell h) 1
      simp [naclShift_apply, naclCells] at this
    · ext j; fin_cases j <;> simp [naclShift_apply, naclCells]
  · refine naclAdj (b := ⟨0, 0, Pi.single 1 1⟩) (by simp [naclBonds]) ?_ (Or.inl ⟨rfl, rfl, ?_⟩)
    · intro h
      have := congrFun (congrArg Site.cell h) 1
      simp [naclShift_apply, naclCells] at this
    · ext j; fin_cases j <;> simp [naclShift_apply, naclCells]

/-- The inverse of the shift maps every bond to a bond. -/
lemma naclShift_inv_adj : ∀ b ∈ naclBonds,
    naclGraph.toSimpleGraph.Adj (naclShift⁻¹ ⟨0, b.source⟩)
      (naclShift⁻¹ ⟨b.displacement, b.target⟩) := by
  intro b hb
  simp only [naclBonds, Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl | rfl | rfl
  all_goals simp only [naclShift_inv_apply]
  · refine naclAdj (b := ⟨1, 0, Pi.single 0 1⟩) (by simp [naclBonds]) ?_ (Or.inl ⟨rfl, rfl, ?_⟩)
    · intro h
      exact absurd (congrArg Site.label h) (by decide)
    · ext j; fin_cases j <;> simp [naclCells]
  · refine naclAdj (b := ⟨0, 1, 0⟩) (by simp [naclBonds]) ?_ (Or.inl ⟨rfl, rfl, ?_⟩)
    · intro h
      exact absurd (congrArg Site.label h) (by decide)
    · ext j; fin_cases j <;> simp [naclCells]
  · refine naclAdj (b := ⟨1, 1, Pi.single 1 1⟩) (by simp [naclBonds]) ?_ (Or.inl ⟨rfl, rfl, ?_⟩)
    · intro h
      have := congrFun (congrArg Site.cell h) 1
      simp [naclCells] at this
    · ext j; fin_cases j <;> simp [naclCells]
  · refine naclAdj (b := ⟨0, 0, Pi.single 1 1⟩) (by simp [naclBonds]) ?_ (Or.inl ⟨rfl, rfl, ?_⟩)
    · intro h
      have := congrFun (congrArg Site.cell h) 1
      simp [naclCells] at this
    · ext j; fin_cases j <;> simp [naclCells]

/-- **The shift by one site is in the space group of the square array.** -/
lemma naclShift_mem_spaceGroup : naclShift ∈ naclGraph.spaceGroup :=
  PeriodicGraph.mem_spaceGroup_ofBonds _ _ naclShift_adj naclShift_inv_adj

/-- With Na and Cl as different species, the shift is not a symmetry of the crystal. -/
lemma naclShift_not_mem_speciesGroup : naclShift ∉ speciesGroup (C := nacl) id := by
  intro h
  exact absurd (h 0) (by decide)

end Physlib.CondensedMatter.Crystal
