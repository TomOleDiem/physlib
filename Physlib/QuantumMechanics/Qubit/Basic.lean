/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OperatorAlgebra.Basic
public import Physlib.Meta.Linters.Sorry
public import Physlib.Meta.TODO.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Fin.VecNotation

/-!

# Abstract qubit observable algebras

This file develops the qubit from its abstract observable-algebra structure, rather than
starting from `2 × 2` matrices. The generators are only assumed to be self-adjoint elements
of a unital C⋆-algebra `A` satisfying the Pauli relations, together with a basis condition
making `A` genuinely four-dimensional. The matrix representation is a later, concrete
instance of this structure (see `Qubit/Matrix.lean`, not yet written).

## Main definitions

* `QubitAlgebra A` : the class asserting that `A` carries a Pauli triple.

## Design

The three generators are indexed by `Fin 3` rather than given three separate names `X, Y, Z`.
This lets every relation among them be stated once, for all indices, using the cyclic order on
`Fin 3` (`i, i + 1, i + 2`), instead of writing out `X, Y, Z`'s six relations and their three
mirror images by hand. `gen 0, gen 1, gen 2` play the roles of `X, Y, Z`.

## Roadmap

This is the first file of a step-by-step development; see `Qubit/todo.md` for what is
deliberately deferred.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra
open Module OperatorAlgebra

namespace Qubit

/-!
## The qubit observable algebra
-/

/--
`A` is a qubit observable algebra: a unital C⋆-algebra carrying three self-adjoint generators,
indexed by `Fin 3`, satisfying the Pauli relations in cyclic form, with `1` together with the
generators forming a complex basis of `A`.

The basis condition (rather than a mere spanning condition) is what makes Pauli decompositions
of elements of `A` unique; this is used throughout the rest of the development.
-/
class QubitAlgebra (A : Type*)
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  /-- The three Pauli generators, indexed by `Fin 3`. `gen 0, gen 1, gen 2` are `X, Y, Z`. -/
  gen : Fin 3 → Observable A
  /-- Each generator squares to `1`. -/
  gen_sq : ∀ i, (gen i : A) * gen i = 1
  /-- The cyclic Pauli relation: `gen i * gen (i + 1) = i • gen (i + 2)`, indices mod 3.
  This single field is `XY = iZ`, `YZ = iX`, `ZX = iY` at `i = 0, 1, 2` respectively. -/
  gen_mul_cyc : ∀ i, (gen i : A) * gen (i + 1) = Complex.I • (gen (i + 2) : A)
  /-- `1, gen 0, gen 1, gen 2` form a complex basis of `A`. -/
  pauliBasis : Basis (Fin 4) ℂ A
  /-- The basis `pauliBasis` is exactly `1` followed by the generators. -/
  pauliBasis_eq : ⇑pauliBasis = Fin.cons (1 : A) (fun i => (gen i : A))

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [QubitAlgebra A]

/-!
## Reversed products

Self-adjointness of the generators turns the cyclic relation `gen i * gen (i + 1) = i • gen
(i + 2)` into its own reversed form, by taking `star` of both sides. This is the single
uniform replacement for what would otherwise be three separate lemmas `YX = -iZ`, `ZY = -iX`,
`XZ = -iY`.
-/

/-- `gen (i + 1) * gen i = -i • gen (i + 2)`, indices mod 3. -/
@[sorryful]
theorem gen_mul_cyc_symm (i : Fin 3) :
    (QubitAlgebra.gen (A := A) (i + 1) : A) * (QubitAlgebra.gen (A := A) i : A) =
      -Complex.I • (QubitAlgebra.gen (A := A) (i + 2) : A) :=
  sorry

TODO "Prove `Qubit.gen_mul_cyc_symm` by taking `star` of `QubitAlgebra.gen_mul_cyc i` and using
  that every generator is self-adjoint."

end Qubit
