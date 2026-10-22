/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A chain with two sites per cell

The sites of a chain placed on the real line, alternately at integers and half-integers.

## i. Overview

The translation group `ℤ` acts on the real line by shifting, which is an isometric action. The chain
has two sites per cell: the site `a` of the cell `n` sits at `n` and the site `b` at `n + 1/2`. This
is the embedding of the periodic chain used to explain how distances enter.

## ii. Key results

- `Crystal.chain` : the crystal with two sites per cell of `ℤ`.
- `Crystal.chainEmbedding` : the sites at the integers and half-integers of the real line.
- `Crystal.chainEmbedding_dist` : the two sites of a cell are `1/2` apart.

## iii. Table of contents

- A. The real line as a space for the chain
- B. The chain

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

/-! ## A. The real line as a space for the chain -/

/-- Integers shift the real line. -/
local instance : AddAction ℤ ℝ := AddAction.compHom ℝ (Int.castAddHom ℝ)

local instance : IsIsometricVAdd ℤ ℝ where
  isometry_vadd n := by
    apply Isometry.of_dist_eq
    intro x y
    change dist ((n : ℝ) + x) ((n : ℝ) + y) = dist x y
    simp [Real.dist_eq]

/-! ## B. The chain -/

/-- Two sites per cell of `ℤ`. -/
abbrev chain := Crystal.ofUnitCell ℤ (Fin 2)

/-- The site `a` of the cell `n` at `n`, and the site `b` at `n + 1/2`. -/
noncomputable def chainEmbedding : Embedding chain ℝ where
  position x := (x.cell : ℝ) + if x.label = 0 then 0 else 1 / 2
  position_vadd a x := by
    simp only [Site.cell_vadd, Site.label_vadd]
    change ((a + x.cell : ℤ) : ℝ) + _ = (a : ℝ) + ((x.cell : ℝ) + _)
    push_cast
    ring

/-- The two sites of a cell are `1/2` apart. -/
lemma chainEmbedding_dist (n : ℤ) :
    chainEmbedding.dist ⟨n, 0⟩ ⟨n, 1⟩ = 1 / 2 := by
  simp [Embedding.dist, chainEmbedding, Real.dist_eq]

end Physlib.CondensedMatter.Crystal
