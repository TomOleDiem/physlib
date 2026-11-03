/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.Representation
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.LocalAlgebra
/-!

# The bosonic modes as local generators

Creation and annihilation operators of different modes commute, so the polynomial CCR algebra is a
local algebra.

## i. Overview

The creation and annihilation operators of a mode, taken together, form a star-closed family of
local generators. Operators of different modes commute. This makes the polynomial CCR algebra a
local algebra in the sense of `LocalGenerators`. Finite support of polynomials, locality and the
Heisenberg derivation of local interactions are then the general theorems of `LocalAlgebra`.

## ii. Key results

- `InfiniteBosons.bosonGenerators`: the local generators of the bosonic modes.
- `InfiniteBosons.annOp_comm_creOp`: the commutation of different modes.

## iii. Table of contents

- A. Commutation of different modes
- B. The local generators

## iv. References

* O. Bratteli and D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, Section 5.2.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

lemma annOp_comm_annOp (x y : L) : annOp x * annOp y = annOp y * annOp x :=
  adjointable_ext (ann_comm x y)

lemma creOp_comm_creOp (x y : L) : creOp x * creOp y = creOp y * creOp x :=
  adjointable_ext (cre_comm x y)

lemma annOp_comm_creOp {x y : L} (hxy : x ≠ y) : annOp x * creOp y = creOp y * annOp x := by
  have := annOp_creOp_comm x y
  simpa [hxy] using this

lemma creOp_comm_annOp {x y : L} (hxy : x ≠ y) : creOp x * annOp y = annOp y * creOp x :=
  (annOp_comm_creOp (Ne.symm hxy)).symm

/-- **The bosonic modes are local generators**: creation and annihilation operators of a mode, with
commutation across different modes. -/
def bosonGenerators (L : Type*) [DecidableEq L] : LocalGenerators L (adjointable L) where
  gen x := {annOp x, creOp x}
  star_mem x a ha := by
    rcases ha with rfl | rfl
    · simp [star_annOp]
    · simp [star_creOp]
  commute x y hxy a ha b hb := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact annOp_comm_annOp x y
    · exact annOp_comm_creOp hxy
    · exact creOp_comm_annOp hxy
    · exact creOp_comm_creOp x y

lemma annOp_mem_gen {X : Set L} {x : L} (hx : x ∈ X) : annOp x ∈ (bosonGenerators L).on X :=
  (bosonGenerators L).gen_mem_on hx (by simp [bosonGenerators])

lemma creOp_mem_gen {X : Set L} {x : L} (hx : x ∈ X) : creOp x ∈ (bosonGenerators L).on X :=
  (bosonGenerators L).gen_mem_on hx (by simp [bosonGenerators])

end InfiniteBosons
