/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.PeriodicGraph

/-!
# Species of a crystal

A species assigned to every label of the unit cell restricts the symmetries to those that keep it.

## i. Overview

The sites of a crystal are located by the labels of the reference cell. A map `q : F → Q` assigns
a species to each label. A symmetry permutes the labels, and it respects the species when it
sends every label to a label of the same species. When `q` is constant, any permutation of the
labels is allowed. When `q` is injective, every label is fixed.

## ii. Key results

- `Crystal.speciesGroup` : the symmetries that keep the species of every label.
- `Crystal.speciesGroup_const` : with a single species every symmetry is allowed.
- `Crystal.mem_speciesGroup_iff_of_injective` : with distinct species, the labels are fixed.
- `Crystal.PeriodicGraph.speciesSpaceGroup` : the space group symmetries that keep the species.

## iii. Table of contents

- A. Symmetries that keep the species
- B. With the bonds of a periodic graph

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G] {C : Crystal G} {Q : Type*}

/-! ## A. Symmetries that keep the species -/

/-- The permutations of the labels that keep the species. -/
def labelStabilizer (q : C.UnitCell → Q) : Subgroup (Equiv.Perm C.UnitCell) where
  carrier := {σ | ∀ i, q (σ i) = q i}
  one_mem' _ := rfl
  mul_mem' {σ τ} hσ hτ i := (hσ (τ i)).trans (hτ i)
  inv_mem' {σ} hσ i := by rw [← hσ (σ⁻¹ i)]; simp

/-- The symmetries of a crystal that keep the species of every label. -/
noncomputable def speciesGroup (q : C.UnitCell → Q) : Subgroup (Symmetry C) :=
  (labelStabilizer q).comap (Symmetry.labelHom C)

/-- A symmetry keeps the species when the image of every label has the same species. -/
lemma mem_speciesGroup_iff (q : C.UnitCell → Q) (φ : Symmetry C) :
    φ ∈ speciesGroup q ↔ ∀ i, q (φ ⟨0, i⟩).label = q i := Iff.rfl

/-- With a single species, every symmetry keeps the species. -/
lemma speciesGroup_const (c : Q) : speciesGroup (C := C) (Function.const _ c) = ⊤ := by
  apply top_unique
  intro _ _ _
  rfl

/-- With distinct species, a symmetry keeps the species exactly when it fixes every label. -/
lemma mem_speciesGroup_iff_of_injective {q : C.UnitCell → Q} (hq : Function.Injective q)
    (φ : Symmetry C) : φ ∈ speciesGroup q ↔ ∀ i, (φ ⟨0, i⟩).label = i := by
  constructor
  · intro h i
    exact hq ((mem_speciesGroup_iff q φ).1 h i)
  · intro h
    rw [mem_speciesGroup_iff]
    intro i
    rw [h i]

/-! ## B. With the bonds of a periodic graph -/

namespace PeriodicGraph

/-- The symmetries that preserve the bonds and keep the species. -/
noncomputable def speciesSpaceGroup (g : PeriodicGraph C) (q : C.UnitCell → Q) :
    Subgroup (Symmetry C) :=
  g.spaceGroup ⊓ speciesGroup q

/-- A symmetry is in the species space group when it preserves adjacency and the species. -/
lemma mem_speciesSpaceGroup_iff (g : PeriodicGraph C) (q : C.UnitCell → Q) (φ : Symmetry C) :
    φ ∈ g.speciesSpaceGroup q ↔ φ ∈ g.spaceGroup ∧ φ ∈ speciesGroup q := Iff.rfl

end PeriodicGraph

end Physlib.CondensedMatter.Crystal
