/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.Channel.Basic
public import Physlib.ProbabilisticTheory.OrderUnit.Basic
public import Mathlib.Algebra.Colimit.Module

/-!
# Local nets of observables

Observables of subsystems and their inclusion into larger subsystems.

## i. Overview

Let `R` index subsystems, with `X ≤ Y` meaning that `X` is contained in `Y`. The observables of
`X` form an order-unit space `A X`. A local net assigns to `X ≤ Y` a channel,
which regards an observable of `X` as one of `Y`.

For a tensor product system with `H_Y ≃ H_X ⊗ H_rest`, take `A X` to be the Hermitian operators
on `H_X`. Then the inclusion is the familiar map `M ↦ M ⊗ 1`: the observable acts as `M` on `X` and
as the identity on the remaining factors.

The local observables can also be viewed in one space, `N.Quasilocal`.

## ii. Key results

- `LocalNet`: subsystem observables with channels into larger subsystems.
- `LocalNet.IsOrderEmbedding`: the inclusion maps reflect order.
- `LocalNet.map_le_map_iff`: inclusion preserves and reflects inequalities.
- `LocalNet.incl_injective`: order-embedding inclusion maps are injective.
- `LocalNet.Quasilocal`: the algebraic direct limit of the local observable spaces.
- `LocalNet.Quasilocal.toQuasilocal`: regard an observable of one subsystem as a quasilocal
  observable.
- `LocalNet.Quasilocal.toQuasilocal_eq_iff`: equality of quasilocal observables can be checked in a
  common larger subsystem.
- `LocalNet.Quasilocal.toQuasilocal_injective`: order-embedding inclusions keep local observables
  distinct.

## iii. Table of contents

- A. Subsystems and inclusions
- B. Order-embedding inclusions
- C. The quasilocal observable space
- D. Embedding the local observables

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

variable {R : Type*} [Preorder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]

/-! ## A. Subsystems and inclusions -/

/-- The observables of each subsystem, with channels into larger subsystems. -/
@[ext]
structure LocalNet (R : Type*) [Preorder R] (A : R → Type*)
    [∀ X, OrderUnitSpace (A X)] where
  /-- Regard an observable of `X` as an observable of `Y` when `X ≤ Y`. -/
  incl : ∀ {X Y : R}, X ≤ Y → A X →ₚ₁[ℝ] A Y
  /-- An observable is unchanged by inclusion into the same subsystem. -/
  incl_refl : ∀ (X : R) (a : A X), incl (le_refl X) a = a
  /-- Including through an intermediate subsystem agrees with direct inclusion. -/
  incl_trans : ∀ {X Y Z : R} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (h3 : X ≤ Z) (a : A X),
    incl h3 a = incl h₂ (incl h₁ a)

attribute [simp] LocalNet.incl_refl

namespace LocalNet

variable (N : LocalNet R A) {X Y Z : R}

/-! ## B. Order-embedding inclusions -/

/-- The inclusion maps are order embeddings if each reflects positivity. -/
class IsOrderEmbedding (N : LocalNet R A) : Prop where
  /-- An observable that is positive in a larger subsystem is already positive in the smaller. -/
  nonneg_of_incl_nonneg : ∀ {X Y : R} (h : X ≤ Y) {a : A X}, 0 ≤ N.incl h a → 0 ≤ a

section OrderEmbedding

variable [N.IsOrderEmbedding]

/-- Inclusion in an order-embedding net preserves and reflects inequalities. -/
lemma map_le_map_iff (h : X ≤ Y) {a b : A X} :
    N.incl h a ≤ N.incl h b ↔ a ≤ b := by
  rw [← sub_nonneg, ← map_sub, ← sub_nonneg (a := b) (b := a)]
  exact ⟨IsOrderEmbedding.nonneg_of_incl_nonneg h, map_nonneg _⟩

/-- The inclusion maps of an order-embedding net are injective. -/
lemma incl_injective (h : X ≤ Y) : Function.Injective (N.incl h) :=
  (OrderEmbedding.ofMapLEIff (N.incl h) fun _ _ => N.map_le_map_iff h).injective

end OrderEmbedding

variable [DecidableEq R]

/-!

## C. The quasilocal observable space

For a directed family of subsystems, observables from different subsystems can be included in a
common larger one and combined there. The direct limit identifies all such local descriptions
consistently and supplies the resulting real vector space.

-/

/-- The inclusions as linear maps: the transition maps of the direct limit defining
`N.Quasilocal`. -/
abbrev inclLin (N : LocalNet R A) ⦃X Y : R⦄ (h : X ≤ Y) : A X →ₗ[ℝ] A Y :=
  (N.incl h).toLinearMap

/-- The inclusions form a directed system: including a subsystem into itself does nothing, and
successive inclusions compose. -/
instance directedSystem (N : LocalNet R A) : DirectedSystem A fun _ _ h => N.inclLin h where
  map_self _ x := N.incl_refl _ x
  map_map _ _ _ hij hjk x := (N.incl_trans hij hjk x).symm

/-- The algebraic direct limit of the local observable spaces. -/
def Quasilocal (N : LocalNet R A) : Type* :=
  Module.DirectLimit A N.inclLin

namespace Quasilocal

variable {N : LocalNet R A}

/-- Quasilocal observables add, as elements of a direct limit of vector spaces. -/
noncomputable instance : AddCommGroup N.Quasilocal :=
  inferInstanceAs (AddCommGroup (Module.DirectLimit A N.inclLin))

/-- Quasilocal observables can be scaled by real numbers. -/
noncomputable instance : Module ℝ N.Quasilocal :=
  inferInstanceAs (Module ℝ (Module.DirectLimit A N.inclLin))

/-!

## D. Embedding the local observables

The map `toQuasilocal N i` takes an observable of subsystem `i` to the quasilocal observable it
represents.
-/

variable (N) in
/-- Regard an observable of subsystem `i` as a quasilocal observable. -/
noncomputable def toQuasilocal (i : R) : A i →ₗ[ℝ] N.Quasilocal :=
  Module.DirectLimit.of ℝ R A N.inclLin i

/-- Including an observable in a larger subsystem does not change its quasilocal representation. -/
lemma toQuasilocal_incl {i j : R} (h : i ≤ j) (a : A i) :
    toQuasilocal N j (N.incl h a) = toQuasilocal N i a :=
  Module.DirectLimit.of_f (hij := h) (x := a)

section Directed

variable [IsDirectedOrder R]

/-- Two local observables represent the same quasilocal observable exactly when they agree in a
common larger subsystem. -/
lemma toQuasilocal_eq_iff {i j : R} (a : A i) (b : A j) :
    toQuasilocal N i a = toQuasilocal N j b ↔
      ∃ (k : R) (hik : i ≤ k) (hjk : j ≤ k), N.incl hik a = N.incl hjk b := by
  refine ⟨fun h => ?_, fun ⟨k, hik, hjk, h⟩ => by
    rw [← toQuasilocal_incl hik, ← toQuasilocal_incl hjk, h]⟩
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  obtain ⟨l, hkl, hl⟩ := Module.DirectLimit.exists_eq_of_of_eq
    (G := A) (f := N.inclLin)
    (show toQuasilocal N k (N.incl hik a) = toQuasilocal N k (N.incl hjk b) by
      rw [toQuasilocal_incl, toQuasilocal_incl, h])
  exact ⟨l, hik.trans hkl, hjk.trans hkl,
    (N.incl_trans hik hkl a).trans (hl.trans (N.incl_trans hjk hkl b).symm)⟩

variable [N.IsOrderEmbedding] in
/-- Order-embedding inclusions keep distinct local observables distinct in the quasilocal space. -/
lemma toQuasilocal_injective (i : R) : Function.Injective (toQuasilocal N i) :=
  fun _ _ h => let ⟨_, hik, _, h⟩ := (toQuasilocal_eq_iff _ _).1 h; N.incl_injective hik h

variable [Nonempty R]

/-- Every quasilocal observable has a representative in some subsystem. -/
lemma exists_local (x : N.Quasilocal) : ∃ (i : R) (a : A i), toQuasilocal N i a = x :=
  Module.DirectLimit.exists_of x

/-- Any two quasilocal observables have representatives in a common subsystem. -/
lemma exists_local₂ (x y : N.Quasilocal) :
    ∃ (i : R) (a b : A i), toQuasilocal N i a = x ∧ toQuasilocal N i b = y :=
  Module.DirectLimit.exists_of₂ x y

end Directed

end Quasilocal

end LocalNet

end ProbabilisticTheory
