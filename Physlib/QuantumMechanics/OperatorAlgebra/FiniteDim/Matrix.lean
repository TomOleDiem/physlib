/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.HilbertSpace
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!

# The finite-dimensional matrix and Hilbert-space cases

Mathlib already knows that `Matrix n n ℂ` (any finite `n`) and `H →L[ℂ] H` (bounded operators on
any complex Hilbert space `H`) are C⋆-algebras; what neither comes with is the canonical
compatible order `OperatorAlgebra` needs (see `OperatorAlgebra.Basic`). The bounded-operator
instance lives in `OperatorAlgebra.HilbertSpace`, while this file adds the corresponding matrix
instance from `CStarAlgebra.spectralOrder`/`spectralOrderedRing` for every finite `n` — rather
than only for one particular example, such as the qubit's `Matrix (Fin 2) (Fin 2) ℂ`
(`Qubit.Matrix`, which specializes this file at `n = Fin 2`).

`matrixEquivCLM` packages Mathlib's star-algebra equivalence `Matrix.toEuclideanCLM` between the
two: `n`-dimensional matrices and bounded operators on `EuclideanSpace ℂ n` present the same
operator algebra.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace OperatorAlgebra

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable instance : PartialOrder (Matrix n n ℂ) := CStarAlgebra.spectralOrder _
instance : StarOrderedRing (Matrix n n ℂ) := CStarAlgebra.spectralOrderedRing _

/-- Every finite-dimensional matrix algebra is an operator algebra, via the spectral order. -/
noncomputable instance instMatrix : OperatorAlgebra (Matrix n n ℂ) where

/-- `n`-dimensional matrices and bounded operators on `EuclideanSpace ℂ n` present the same
operator algebra: Mathlib's star-algebra equivalence between them, viewed over `ℝ` so that it is
usable at the `OperatorAlgebra`/`QubitAlgebra` level (`Qubit.Matrix`). -/
noncomputable def matrixEquivCLM (n : Type*) [Fintype n] [DecidableEq n] :
    Matrix n n ℂ ≃⋆ₐ[ℝ] (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  Matrix.toEuclideanCLM.restrictScalars ℝ

end OperatorAlgebra
