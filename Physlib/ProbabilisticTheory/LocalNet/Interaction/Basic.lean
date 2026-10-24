/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.LocalNet.Basic

/-!

# Interactions on a local net

A family of local pieces, each an observable of the region it lives in.

## i. Overview

The energy, the magnetization and the particle number of a large system are sums of local pieces. An
interaction labels the pieces and gives the region and the observable of each one. A piece seen in a
larger region is included into it. A piece seen in a region it does not live in is zero.

## ii. Key results

- `Interaction` : a region and a piece for every label.
- `Interaction.piece` : a piece seen in a region.
- `Interaction.incl_piece` : a piece seen in a region, then included into a larger one.

## iii. Table of contents

- A. Interactions
- B. Pieces in a region

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

variable {R : Type*} [Preorder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]
  {N : LocalNet R A} {ι : Type*}

/-! ## A. Interactions -/

/-- An interaction on the local net `N`: for every label a region and an observable of that
region. -/
structure Interaction (N : LocalNet R A) (ι : Type*) where
  /-- The region in which a piece lives. -/
  supp : ι → R
  /-- The piece, an observable of its region. -/
  term : ∀ i, A (supp i)

namespace Interaction

variable (Φ : Interaction N ι)

/-! ## B. Pieces in a region -/

/-- The labels whose piece lives in `Λ`. -/
def labelsIn (Λ : R) : Set ι := {i | Φ.supp i ≤ Λ}

open Classical in
/-- The piece `i` seen in the region `Λ`. It is zero if the piece does not live in `Λ`. -/
noncomputable def piece (Λ : R) (i : ι) : A Λ :=
  if h : Φ.supp i ≤ Λ then N.incl h (Φ.term i) else 0

/-- A piece seen in `Λ` and included into a larger region `Λ'` is the piece seen in `Λ'`, if it
lives in `Λ`, and zero otherwise. -/
lemma incl_piece {Λ Λ' : R} (h : Λ ≤ Λ') (i : ι) :
    N.incl h (Φ.piece Λ i) = (Φ.labelsIn Λ).indicator (Φ.piece Λ') i := by
  by_cases h1 : Φ.supp i ≤ Λ
  · simp [piece, labelsIn, h1, h1.trans h, N.incl_trans_apply h1 h (h1.trans h)]
  · simp [piece, labelsIn, h1]

lemma piece_add (s : ι → R) (t t' : ∀ i, A (s i)) (Λ : R) (i : ι) :
    (⟨s, t + t'⟩ : Interaction N ι).piece Λ i =
      (⟨s, t⟩ : Interaction N ι).piece Λ i + (⟨s, t'⟩ : Interaction N ι).piece Λ i := by
  by_cases h : s i ≤ Λ <;> simp [piece, h]

lemma piece_smul (s : ι → R) (c : ℝ) (t : ∀ i, A (s i)) (Λ : R) (i : ι) :
    (⟨s, c • t⟩ : Interaction N ι).piece Λ i = c • (⟨s, t⟩ : Interaction N ι).piece Λ i := by
  by_cases h : s i ≤ Λ <;> simp [piece, h]

end Interaction

end ProbabilisticTheory
