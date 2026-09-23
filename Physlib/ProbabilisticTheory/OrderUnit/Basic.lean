/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Data.Real.Basic

/-!

# Ordered vector spaces and order units

## i. Overview

Order-unit spaces capture the basic structure needed for a probabilistic theory: observables,
positivity, effects, states and probabilities. They do this without assuming that the theory is
classical or quantum, or that observables have any particular algebraic structure.

In quantum mechanics, the standard example is the real vector space of self-adjoint matrices,
ordered by positive semidefiniteness, with the identity matrix as 1. Keeping only the vector
space, its order, and this distinguished unit gives the abstract order-unit setting.

## ii. Key results

- `OrderUnitSpace.exists_two_sided_bound` : every observable sits between `-(n • 1)` and `n • 1`,
  for some `n`.
- `OrderUnitSpace.exists_eq_sub_nonneg` : every observable is a difference of two positive
  observables.

## iii. Table of contents

- A. Order-unit elements
- B. Consequences of being an order unit

## iv. References

-/

@[expose] public section

/-!

## A. Ordered vector spaces and order-unit elements

-/

/-- An ordered real vector space. -/
class OrderedVectorSpace (E : Type*) extends AddCommGroup E, PartialOrder E, Module ℝ E,
    IsOrderedAddMonoid E, PosSMulMono ℝ E

/-- An ordered real vector space with a distinguished element `1`, without assuming it is an
order unit. -/
class OrderedVectorSpaceWithUnit (E : Type*) extends OrderedVectorSpace E, One E

/-- A positive element `A` is an order unit if every element is bounded above by a natural
multiple of `A`. -/
class IsOrderUnitElement {E : Type*} [AddCommMonoid E] [PartialOrder E] (A : E) : Prop where
  /-- An order-unit element is nonnegative. -/
  nonneg : 0 ≤ A
  /-- Every element is bounded above by a natural multiple of the order unit. -/
  exists_nsmul_le : ∀ B : E, ∃ n : ℕ, B ≤ n • A

/-- An ordered real vector space whose distinguished element `1` is an order unit. No
multiplication is assumed. -/
class OrderUnitSpace (E : Type*) extends OrderedVectorSpaceWithUnit E where
  /-- `1` itself satisfies the order-unit condition. -/
  isOrderUnitElement_one : IsOrderUnitElement (1 : E)

namespace OrderUnitSpace

variable {E : Type*} [OrderUnitSpace E]

/-- The distinguished unit is positive. -/
lemma one_nonneg : 0 ≤ (1 : E) :=
  OrderUnitSpace.isOrderUnitElement_one.nonneg

/-- Every element is bounded by some finite multiple of the identity. -/
lemma exists_nsmul_one_le (A : E) : ∃ n : ℕ, A ≤ n • (1 : E) :=
  OrderUnitSpace.isOrderUnitElement_one.exists_nsmul_le A

/-!

## B. Consequences of being an order unit

-/

/-- Every element is bounded on both sides by a natural multiple of the order unit. -/
lemma exists_two_sided_bound (A : E) : ∃ n : ℕ, -(n • (1 : E)) ≤ A ∧ A ≤ n • (1 : E) := by
  obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le A
  obtain ⟨m, hm⟩ := OrderUnitSpace.exists_nsmul_one_le (-A)
  refine ⟨max n m, ?_,
    hn.trans (nsmul_le_nsmul_left OrderUnitSpace.one_nonneg (le_max_left n m))⟩
  have hm' : -A ≤ max n m • (1 : E) :=
    hm.trans (nsmul_le_nsmul_left OrderUnitSpace.one_nonneg (le_max_right n m))
  simpa using neg_le_neg hm'

/-- Every element is a difference of two positive elements. -/
lemma exists_eq_sub_nonneg (A : E) :
    ∃ Ap An : E, 0 ≤ Ap ∧ 0 ≤ An ∧ A = Ap - An := by
  obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le (-A)
  refine ⟨A + n • (1 : E), n • (1 : E), ?_, nsmul_nonneg OrderUnitSpace.one_nonneg n, ?_⟩
  · simpa using add_le_add_right hn A
  · exact (add_sub_cancel_right A (n • (1 : E))).symm

end OrderUnitSpace
