/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OperatorAlgebra.Basic

/-!

# Effects in C⋆-algebras

An effect in a unital C⋆-algebra `A` is a self-adjoint element in the order
interval `[0, 1]`.

Effects represent individual measurement outcomes. The definition applies
equally to commutative and noncommutative C⋆-algebras.

This file provides the basic structural API:

* zero and unit effects;
* positivity and the upper bound by the identity;
* complements;
* order reversal under complements.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder

variable {A : Type*}
  [CStarAlgebra A]
  [PartialOrder A]
  [StarOrderedRing A]

namespace Effect


/-- The zero observable is an effect. -/
noncomputable instance : Zero (Effect A) where
  zero := ⟨0, by
    constructor
    · exact le_rfl
    · change (0 : A) ≤ 1
      exact zero_le_one⟩


/-- The identity observable is an effect. -/
noncomputable instance : One (Effect A) where
  one := ⟨1, by
    constructor
    · change (0 : A) ≤ 1
      exact zero_le_one
    · exact le_rfl⟩


@[simp]
lemma coe_zero :
    ((0 : Effect A) : Observable A) = 0 :=
  rfl


@[simp]
lemma coe_one :
    ((1 : Effect A) : Observable A) = 1 :=
  rfl


/-- Every effect is positive. -/
lemma nonneg (E : Effect A) :
    0 ≤ (E : Observable A) :=
  E.property.1


/-- Every effect is bounded above by the identity. -/
lemma le_one (E : Effect A) :
    (E : Observable A) ≤ 1 :=
  E.property.2


/-- Two effects are equal if their underlying observables are equal. -/
@[ext]
lemma ext {E F : Effect A}
    (h : (E : Observable A) = (F : Observable A)) :
    E = F :=
  Subtype.ext h


/-!
## Complement
-/

/--
The complement `1 - E` of an effect.

For a two-outcome measurement, this represents the outcome complementary to
`E`.
-/
noncomputable def complement (E : Effect A) : Effect A :=
  ⟨1 - (E : Observable A), by
    constructor
    · exact sub_nonneg.mpr E.property.2
    · exact sub_le_self 1 E.property.1⟩


@[simp]
lemma coe_complement (E : Effect A) :
    (complement E : Observable A) =
      1 - (E : Observable A) :=
  rfl


@[simp]
lemma complement_zero :
    complement (0 : Effect A) = 1 := by
  apply ext
  simp [complement]


@[simp]
lemma complement_one :
    complement (1 : Effect A) = 0 := by
  apply ext
  simp [complement]


@[simp]
lemma complement_complement (E : Effect A) :
    complement (complement E) = E := by
  apply ext
  simp [complement]


/-- An effect and its complement sum to the identity. -/
lemma add_complement (E : Effect A) :
    (E : Observable A) + complement E = 1 := by
  simp [complement]


/-- Complement reverses the order on effects. -/
lemma complement_le_complement {E F : Effect A}
    (h : (E : Observable A) ≤ F) :
    (complement F : Observable A) ≤ complement E := by
  simpa [complement] using sub_le_sub_left h 1


/-- Complement reverses the order exactly. -/
lemma complement_le_complement_iff {E F : Effect A} :
    (complement E : Observable A) ≤ complement F ↔
      (F : Observable A) ≤ E := by
  constructor
  · intro h
    have h' := complement_le_complement h
    simpa using h'
  · exact complement_le_complement


end Effect

end OperatorAlgebra
