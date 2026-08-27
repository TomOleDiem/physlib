/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
-/
module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Complex.Basic

/-! # Algebraic invariant cores

The common-core container is independent of affiliation and functional calculus. -/

@[expose] public section

namespace OperatorAlgebra

variable {β : Type*} {ι : Type*}

/-- A common algebraic core for a family of operators. -/
structure InvariantCore (T : ι → β) where
  D : Type*
  instAddCommGroup : AddCommGroup D
  instModule : Module ℂ D
  restrict : ι → Module.End ℂ D

attribute [instance] InvariantCore.instAddCommGroup InvariantCore.instModule

namespace InvariantCore

variable {T : ι → β} (core : InvariantCore T) (i j : ι)

/-- The commutator of two restrictions in ordinary endomorphism algebra. -/
noncomputable def restrictCommutator : Module.End ℂ core.D :=
  core.restrict i * core.restrict j - core.restrict j * core.restrict i

/-- A vanishing restriction commutator is the ordinary endomorphism commutation relation.
This is the small algebraic bridge used by common-core arguments; it makes no claim about the
strong commutation of the represented unbounded operators. -/
lemma commute_of_restrictCommutator_eq_zero
    (h : core.restrictCommutator i j = 0) :
    Commute (core.restrict i) (core.restrict j) := by
  rw [commute_iff_eq]
  exact sub_eq_zero.mp h

end InvariantCore

end OperatorAlgebra
