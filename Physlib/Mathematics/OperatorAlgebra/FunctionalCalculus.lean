/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OperatorAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Restrict

/-!

# Functional calculus of observables

Mathlib provides the continuous functional calculus for self-adjoint elements
of a C⋆-algebra.

This file only packages the real continuous functional calculus so that
applying a real-valued function to an `Observable` again returns an
`Observable`.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder

variable {A : Type*}
  [CStarAlgebra A]
  [PartialOrder A]
  [StarOrderedRing A]

/--
Apply a real-valued function to an observable using Mathlib's continuous
functional calculus.
-/
noncomputable def observableCFC
    (f : ℝ → ℝ)
    (a : Observable A) :
    Observable A :=
  ⟨_root_.cfc f (a : A), cfc_predicate f (a : A)⟩

omit [PartialOrder A] [StarOrderedRing A]
/--
The underlying algebra element of `observableCFC f a` is Mathlib's
continuous functional calculus `cfc f a`.
-/
@[simp]
lemma coe_observableCFC
    (f : ℝ → ℝ)
    (a : Observable A) :
    (observableCFC f a : A) =
      _root_.cfc f (a : A) :=
  rfl

end OperatorAlgebra
