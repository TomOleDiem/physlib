/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.LocalNet.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Archimedean
public import Mathlib.Algebra.Order.Group.Cone

/-!
# Order-unit structure on quasilocal observables

Positivity and the order unit on the space of quasilocal observables.

## i. Overview

Each `A X` already has an order and an order unit. But `N.Quasilocal` was constructed as a direct
limit of vector spaces, which gives it no order. The set `Pos N` supplies the missing positive
cone: a quasilocal observable belongs to it when some local representative is positive.

For a nonempty directed net, this cone defines an order on the quasilocal space. A quasilocal
observable cannot be both positive and negative unless it is zero: equality with zero in the
direct limit already holds in some larger subsystem. The additional assumption
`N.IsOrderEmbedding` ensures that the quasilocal order agrees with the existing order of each
subsystem.

Every inclusion channel preserves `1`, so the order units of all subsystems give the same quasilocal
observable. Together with the order, this makes `N.Quasilocal` an order-unit space, and each
subsystem maps to it by a channel. If the subsystem spaces are Archimedean, the quasilocal space is
Archimedean as well.

## ii. Key results

- `LocalNet.Quasilocal.toQuasilocal_nonneg_iff`: with order-embedding inclusions, a local
  observable is positive in the quasilocal space exactly when it is positive in its subsystem.
- `LocalNet.Quasilocal.instOrderUnitSpace`: the quasilocal observables form an order-unit space.
- `LocalNet.Quasilocal.toQuasilocalChannel`: each subsystem maps into the quasilocal space by a
  channel.
- `LocalNet.Quasilocal.instArchimedeanOrderUnitSpace`: the Archimedean property passes to the
  quasilocal space.

## iii. Table of contents

- A. Positivity
- B. The common order unit
- C. The order
- D. The quasilocal order-unit space and local channels
- E. The Archimedean property

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

open ArchimedeanOrderUnitSpace UnitalPositiveLinearMap

variable {R : Type*} [Preorder R] {A : R → Type*}

namespace LocalNet.Quasilocal

section Pos

variable [∀ X, OrderUnitSpace (A X)] {N : LocalNet R A}

/-!

## A. Positivity

The vector-space direct limit does not supply a positive cone. The set below collects the quasilocal
observables represented by positive local observables. For a directed family, positive
representatives from different subsystems can be included in a common larger one and added there.

-/

variable (N) in
/-- The candidate positive cone on the direct limit, formed from positive local representatives. -/
def Pos : Set N.Quasilocal :=
  {x | ∃ (i : R) (a : A i), 0 ≤ a ∧ toQuasilocal N i a = x}

/-- A nonnegative local observable represents an element of the quasilocal positive cone. -/
lemma toQuasilocal_mem_pos {i : R} {a : A i} (ha : 0 ≤ a) : toQuasilocal N i a ∈ Pos N :=
  ⟨i, a, ha, rfl⟩

/-- The quasilocal positive cone is closed under nonnegative scalar multiplication. -/
lemma smul_mem_pos {c : ℝ} (hc : 0 ≤ c) {x : N.Quasilocal} (hx : x ∈ Pos N) : c • x ∈ Pos N := by
  obtain ⟨i, a, ha, rfl⟩ := hx
  exact ⟨i, c • a, smul_nonneg hc ha, map_smul _ _ _⟩

variable [IsDirectedOrder R]

/-- The quasilocal positive cone is closed under addition for a directed net. -/
lemma add_mem_pos {x y : N.Quasilocal} (hx : x ∈ Pos N) (hy : y ∈ Pos N) :
    x + y ∈ Pos N := by
  obtain ⟨i, a, ha, rfl⟩ := hx
  obtain ⟨j, b, hb, rfl⟩ := hy
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  refine ⟨k, N.incl hik a + N.incl hjk b, add_nonneg (map_nonneg _ ha) (map_nonneg _ hb), ?_⟩
  rw [map_add, toQuasilocal_incl, toQuasilocal_incl]

/-!

## B. The common order unit

The inclusion channels preserve `1`. Consequently, the order unit of every subsystem represents
the same quasilocal observable.

-/

variable [Nonempty R]

/-- The quasilocal order unit: the image of the order unit of a subsystem. By
`toQuasilocal_one`, it does not matter which one. -/
@[no_expose] noncomputable instance : One N.Quasilocal := ⟨toQuasilocal N (Classical.arbitrary R) 1⟩

/-- The order unit of each subsystem represents the quasilocal order unit. -/
lemma toQuasilocal_one (i : R) : toQuasilocal N i 1 = (1 : N.Quasilocal) := by
  rw [show (1 : N.Quasilocal) = toQuasilocal N (Classical.arbitrary R) 1 from rfl,
    toQuasilocal_eq_iff]
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i (Classical.arbitrary R)
  exact ⟨k, hik, hjk, (map_one _).trans (map_one _).symm⟩

end Pos

section Order

variable [∀ X, OrderUnitSpace (A X)] {N : LocalNet R A} [IsDirectedOrder R]

/-!

## C. The order

The quasilocal positive cone is pointed because an equality in the direct limit holds in some later
subsystem. Order-embedding inclusions additionally make the resulting order agree with each
subsystem's original order.

-/

/-- An observable in both the quasilocal positive cone and its negative is zero. -/
lemma eq_zero_of_mem_pos_of_neg_mem_pos {x : N.Quasilocal} (hx : x ∈ Pos N) (hx' : -x ∈ Pos N) :
    x = 0 := by
  classical
  obtain ⟨i, a, ha, rfl⟩ := hx
  obtain ⟨j, b, hb, hb'⟩ := hx'
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  have hsum : toQuasilocal N k (N.incl hik a + N.incl hjk b) = 0 := by
    rw [map_add, toQuasilocal_incl, toQuasilocal_incl, hb', add_neg_cancel]
  obtain ⟨l, hkl, hl⟩ := Module.DirectLimit.of.zero_exact (f := N.inclLin) hsum
  have h0 : N.incl hkl (N.incl hik a) = 0 := by
    rw [map_add] at hl
    exact ((add_eq_zero_iff_of_nonneg
      (map_nonneg (N.incl hkl) (map_nonneg (N.incl hik) ha))
      (map_nonneg (N.incl hkl) (map_nonneg (N.incl hjk) hb))).1 hl).1
  rw [← toQuasilocal_incl hik, ← toQuasilocal_incl hkl, h0, map_zero]

variable [Nonempty R]

/-- The quasilocal positive cone as an additive group cone. -/
@[no_expose] noncomputable def posCone : AddGroupCone N.Quasilocal where
  carrier := Pos N
  zero_mem' := ⟨Classical.arbitrary R, 0, le_rfl, map_zero _⟩
  add_mem' := add_mem_pos
  eq_zero_of_mem_of_neg_mem' := eq_zero_of_mem_pos_of_neg_mem_pos

/-- A quasilocal observable is below another when their difference is positive in some subsystem. -/
@[no_expose] noncomputable instance : PartialOrder N.Quasilocal :=
  PartialOrder.mkOfAddGroupCone posCone

/-- `x ≤ y` exactly when `y - x` is nonnegative. -/
lemma le_def {x y : N.Quasilocal} : x ≤ y ↔ y - x ∈ Pos N := Iff.rfl

/-- Quasilocal nonnegativity is membership in the positive cone. -/
lemma nonneg_iff {x : N.Quasilocal} : 0 ≤ x ↔ x ∈ Pos N := by
  rw [le_def, sub_zero]

variable [N.IsOrderEmbedding] in
/-- A local observable is nonnegative in the quasilocal space exactly when it is nonnegative
locally. -/
lemma toQuasilocal_nonneg_iff (i : R) (a : A i) : 0 ≤ toQuasilocal N i a ↔ 0 ≤ a := by
  refine ⟨fun ha => ?_, fun ha => nonneg_iff.2 (toQuasilocal_mem_pos ha)⟩
  obtain ⟨j, b, hb, heq⟩ := nonneg_iff.1 ha
  obtain ⟨k, hik, hjk, h⟩ := (toQuasilocal_eq_iff a b).1 heq.symm
  exact IsOrderEmbedding.nonneg_of_incl_nonneg hik (h ▸ map_nonneg (N.incl hjk) hb)

/-- Adding a quasilocal observable preserves the order. -/
instance : IsOrderedAddMonoid N.Quasilocal := IsOrderedAddMonoid.mkOfCone posCone

/-- Scaling by a nonnegative real preserves the order of quasilocal observables. -/
instance : PosSMulMono ℝ N.Quasilocal where
  smul_le_smul_of_nonneg_left c hc x y h := by
    rw [le_def] at h ⊢
    simpa [smul_sub] using smul_mem_pos hc h

/-- The quasilocal observables form an ordered real vector space. -/
noncomputable instance : OrderedVectorSpace N.Quasilocal where

variable [N.IsOrderEmbedding] in
/-- Two local observables have the same order relation in their subsystem and in the quasilocal
space. -/
lemma toQuasilocal_le_iff (i : R) (a b : A i) :
    toQuasilocal N i a ≤ toQuasilocal N i b ↔ a ≤ b := by
  rw [← sub_nonneg, ← map_sub, toQuasilocal_nonneg_iff, sub_nonneg]

/-!

## D. The quasilocal order-unit space and local channels

The common image of `1` is an order unit for the quasilocal space. The canonical map from each
subsystem preserves positivity and this order unit, so it is a channel.

-/

/-- The quasilocal observables form an order-unit space. -/
noncomputable instance : OrderUnitSpace N.Quasilocal where
  one_nonneg := by
    rw [← toQuasilocal_one (Classical.arbitrary R)]
    exact nonneg_iff.2 (toQuasilocal_mem_pos OrderUnitSpace.one_nonneg)
  exists_nsmul_one_le x := by
    obtain ⟨i, a, rfl⟩ := exists_toQuasilocal_eq x
    obtain ⟨n, hn⟩ := OrderUnitSpace.exists_nsmul_one_le a
    refine ⟨n, ?_⟩
    rw [← toQuasilocal_one i, ← map_nsmul, le_def, ← map_sub]
    exact toQuasilocal_mem_pos (sub_nonneg.mpr hn)

variable (N) in
/-- The canonical channel from a subsystem to the quasilocal observable space. -/
noncomputable def toQuasilocalChannel (i : R) : A i →ₚ₁[ℝ] N.Quasilocal :=
  ofLinearMap (toQuasilocal N i) (fun _ ha => nonneg_iff.2 (toQuasilocal_mem_pos ha))
    (toQuasilocal_one i)

@[simp] lemma toQuasilocalChannel_apply (i : R) (a : A i) :
    toQuasilocalChannel N i a = toQuasilocal N i a := rfl

end Order

/-!

## E. The Archimedean property

The Archimedean condition can be checked in a subsystem representing the quasilocal observable.

-/

section Archimedean

variable [∀ X, ArchimedeanOrderUnitSpace (A X)] {N : LocalNet R A} [IsDirectedOrder R]
  [Nonempty R] [N.IsOrderEmbedding]

/-- The quasilocal order-unit space is Archimedean when every subsystem is Archimedean. -/
noncomputable instance : ArchimedeanOrderUnitSpace N.Quasilocal where
  le_zero_of_forall_pos_smul_one_le x hx := by
    obtain ⟨i, a, rfl⟩ := exists_toQuasilocal_eq x
    rw [← map_zero (toQuasilocal N i), toQuasilocal_le_iff]
    refine le_zero_of_forall_pos_smul_one_le a fun ε hε => ?_
    have h := hx ε hε
    rwa [← toQuasilocal_one i, ← map_smul, toQuasilocal_le_iff] at h

end Archimedean

end LocalNet.Quasilocal

end ProbabilisticTheory
