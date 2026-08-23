/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Bounded operators on Hilbert space

This file connects the abstract operator-algebraic quantum-mechanics API with the concrete
C⋆-algebra of bounded operators on a complex Hilbert space. The C⋆-algebra, Loewner order, and
ordered-star-ring instances for bounded operators are supplied by Mathlib.
-/

@[expose] public section

namespace OperatorAlgebra

/-- A complex Hilbert space: a complete complex inner-product space. -/
class HilbertSpace (H : Type*) extends NormedAddCommGroup H, InnerProductSpace ℂ H, CompleteSpace H

/-- Mathlib's separate Hilbert-space assumptions provide Physlib's bundled physics interface. -/
noncomputable instance (priority := low) instHilbertSpace (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : HilbertSpace H := {}

/-- Bounded operators on a complex Hilbert space, written in the usual physics notation. -/
notation "B(" H ")" => H →L[ℂ] H

variable {H : Type*} [HilbertSpace H]

/-- Bounded operators form an `OperatorAlgebra` using Mathlib's native Hilbert-space instances. -/
noncomputable instance instOperatorAlgebraBoundedOperators : OperatorAlgebra B(H) := {}

section Representation

/-- A Hilbert-space representation of `A` as a unital ⋆-homomorphism into `B(H)`. -/
abbrev Representation (A H : Type*) [OperatorAlgebra A] [HilbertSpace H] := A →⋆ₐ[ℂ] B(H)

end Representation

end OperatorAlgebra
