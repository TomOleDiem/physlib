/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Module.Defs

/-!

# Order units

## i. Overview

Order-unit spaces capture the basic structure needed for a probabilistic theory: observables,
positivity, effects, states, and probabilities. They do this without assuming that the theory is
classical or quantum, or that observables have any particular algebraic structure.

In quantum mechanics, the standard example is the real vector space of self-adjoint matrices,
ordered by positive semidefiniteness, with the identity matrix as 1. Keeping only the vector
space, its order, and this distinguished unit gives the abstract order-unit setting.

## ii. Key results

- `IsOrderUnit.exists_two_sided_bound` : every observable sits between `-(n • 1)` and `n • 1`, for
  some `n`.
- `IsOrderUnit.exists_eq_sub_nonneg` : every observable is a difference of two positive
  observables.

## iii. Table of contents

- A. Order-unit elements
- B. Consequences of being an order unit

## iv. References

-/

@[expose] public section

/-!

## A. Order-unit elements

-/

/-- A positive element `A` is an order unit if every element is bounded above by a natural
multiple of `A`. -/
def IsOrderUnitElement {E : Type*} [AddCommMonoid E] [PartialOrder E] (A : E) : Prop :=
  0 ≤ A ∧ ∀ B : E, ∃ n : ℕ, B ≤ n • A

/-- The distinguished element `1 : E` is an order unit. No multiplication is assumed. -/
class IsOrderUnit (E : Type*) [AddCommMonoid E] [PartialOrder E] [One E] : Prop where
  /-- `1` itself satisfies the order-unit condition. -/
  isOrderUnitElement_one : IsOrderUnitElement (1 : E)

namespace IsOrderUnit

variable {E : Type*} [AddCommMonoid E] [PartialOrder E] [One E] [IsOrderUnit E]

/-- The distinguished unit is positive. -/
lemma one_nonneg : 0 ≤ (1 : E) :=
  IsOrderUnit.isOrderUnitElement_one.1

/-- Every element is bounded by some finite multiple of the identity. -/
lemma exists_nsmul_one_le (A : E) : ∃ n : ℕ, A ≤ n • (1 : E) :=
  IsOrderUnit.isOrderUnitElement_one.2 A

/-!

## B. Consequences of being an order unit

-/

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [One E]
  [IsOrderUnit E]

/-- Every element is bounded on both sides by a natural multiple of the order unit. -/
lemma exists_two_sided_bound (A : E) : ∃ n : ℕ, -(n • (1 : E)) ≤ A ∧ A ≤ n • (1 : E) := by
  obtain ⟨n, hn⟩ := IsOrderUnit.exists_nsmul_one_le A
  obtain ⟨m, hm⟩ := IsOrderUnit.exists_nsmul_one_le (-A)
  refine ⟨max n m, ?_, hn.trans (nsmul_le_nsmul_left IsOrderUnit.one_nonneg (le_max_left n m))⟩
  have hm' : -A ≤ max n m • (1 : E) :=
    hm.trans (nsmul_le_nsmul_left IsOrderUnit.one_nonneg (le_max_right n m))
  simpa using neg_le_neg hm'

/-- Every element is a difference of two positive elements. -/
lemma exists_eq_sub_nonneg (A : E) :
    ∃ Ap An : E, 0 ≤ Ap ∧ 0 ≤ An ∧ A = Ap - An := by
  obtain ⟨n, hn⟩ := IsOrderUnit.exists_nsmul_one_le (-A)
  refine ⟨A + n • (1 : E), n • (1 : E), ?_, nsmul_nonneg IsOrderUnit.one_nonneg n, ?_⟩
  · simpa using add_le_add_right hn A
  · exact (add_sub_cancel_right A (n • (1 : E))).symm

end IsOrderUnit
