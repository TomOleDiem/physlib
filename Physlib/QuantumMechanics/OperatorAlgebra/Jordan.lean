/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Basic
public import Mathlib.Algebra.Jordan.Basic

/-!

# Jordan structure on observables

The observables of a complex C⋆-algebra carry the Jordan product

    a ∘ b = 1/2 (ab + ba),

equivalently the real part of their algebra product.

The product is commutative and satisfies the Jordan identity

    (a ∘ b) ∘ (a ∘ a) = a ∘ (b ∘ (a ∘ a)).

`JordanObservable A` is a thin wrapper around `Observable A` carrying this
product as its multiplication. It is therefore a commutative Jordan algebra
in Mathlib's sense.

-/

@[expose] public section

namespace OperatorAlgebra

variable {A : Type*} [CStarAlgebra A]

namespace Observable

/-- The Jordan product of observables is the real part of their algebra product. -/
noncomputable def jordan (a b : Observable A) : Observable A :=
  realPart ((a : A) * (b : A))

@[simp]
lemma coe_jordan (a b : Observable A) :
    (jordan a b : A) = (2⁻¹ : ℝ) • ((a : A) * b + (b : A) * a) := by
  change (↑(realPart ((a : A) * (b : A))) : A) =
    (2⁻¹ : ℝ) • ((a : A) * b + (b : A) * a)
  rw [realPart_apply_coe, star_mul, a.property.star_eq, b.property.star_eq]

lemma jordan_comm (a b : Observable A) : jordan a b = jordan b a := by
  apply Subtype.ext
  simp [coe_jordan, add_comm]

lemma jordan_self (a : Observable A) : (jordan a a : A) = (a : A) * a := by
  rw [coe_jordan]
  module

lemma add_jordan (a b c : Observable A) : jordan (a + b) c = jordan a c + jordan b c := by
  change realPart (((a + b : Observable A) : A) * (c : A)) =
    realPart ((a : A) * (c : A)) + realPart ((b : A) * (c : A))
  rw [AddSubgroup.coe_add, add_mul, map_add]

lemma jordan_add (a b c : Observable A) : jordan a (b + c) = jordan a b + jordan a c := by
  change realPart ((a : A) * ((b + c : Observable A) : A)) =
    realPart ((a : A) * (b : A)) + realPart ((a : A) * (c : A))
  rw [AddSubgroup.coe_add, mul_add, map_add]

lemma jordan_smul (t : ℝ) (a b : Observable A) : jordan a (t • b) = t • jordan a b := by
  change realPart ((a : A) * ((t • b : Observable A) : A)) =
    t • realPart ((a : A) * (b : A))
  rw [selfAdjoint.val_smul, mul_smul_comm]
  exact map_smul (realPart : A →ₗ[ℝ] Observable A) t ((a : A) * (b : A))

lemma jordan_identity (a b : Observable A) :
    jordan (jordan a b) (jordan a a) = jordan a (jordan b (jordan a a)) := by
  apply Subtype.ext
  simp only [coe_jordan, smul_add]
  norm_num [← smul_add]
  noncomm_ring

end Observable

/-! ## Jordan observables

`Observable A` itself cannot receive the Jordan product as a global `Mul`
instance, since Mathlib can already provide multiplication on self-adjoint
elements under stronger assumptions on `A`.

`JordanObservable A` is therefore the same underlying real vector space,
equipped with the Jordan product as multiplication.
-/

/-- Observables equipped with their Jordan multiplication. -/
noncomputable abbrev JordanObservable (A : Type*) [CStarAlgebra A] := Observable A

namespace JordanObservable

variable {A : Type*} [CStarAlgebra A]

noncomputable instance instNonUnitalNonAssocCommRing :
    NonUnitalNonAssocCommRing (JordanObservable A) where
  mul a b := Observable.jordan a b
  mul_comm a b := Observable.jordan_comm a b
  left_distrib a b c := Observable.jordan_add a b c
  right_distrib a b c := Observable.add_jordan a b c
  zero_mul a := by
    change Observable.jordan 0 a = 0
    simp [Observable.jordan]
  mul_zero a := by
    change Observable.jordan a 0 = 0
    simp [Observable.jordan]

noncomputable instance instIsCommJordan : IsCommJordan (JordanObservable A) where
  lmul_comm_rmul_rmul a b := by
    change Observable.jordan (Observable.jordan a b) (Observable.jordan a a) =
      Observable.jordan a (Observable.jordan b (Observable.jordan a a))
    exact Observable.jordan_identity a b

end JordanObservable

end OperatorAlgebra
