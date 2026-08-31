/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Dynamics.FiniteDimensional
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Dynamics.ChristensenEvans
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Finite-dimensional GKSL and Christensen--Evans compatibility

The matrix-level finite-dimensional theorem is the unconditional converse available in this
repository.  This file is the small bridge to the abstract `ChristensenEvansData` interface: a
finite matrix noise family is packaged as a completely positive map on the matrix C⋆-algebra,
and its abstract generator is identified with the matrix GKSL generator.
-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder CStarAlgebra Matrix.Norms.L2Operator NNReal

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
variable {ι : Type*} [Fintype ι]

noncomputable local instance matrixPartialOrder : PartialOrder (Matrix d d ℂ) :=
  CStarAlgebra.spectralOrder _
noncomputable local instance matrixStarOrderedRing : StarOrderedRing (Matrix d d ℂ) :=
  CStarAlgebra.spectralOrderedRing _
noncomputable local instance matrixOperatorAlgebra : OperatorAlgebra (Matrix d d ℂ) := {}

noncomputable def matrixMapToContinuousLinearMap (L : MatrixMap d d ℂ) :
    Matrix d d ℂ →L[ℂ] Matrix d d ℂ :=
  { toLinearMap := L
    cont := L.continuous_of_finiteDimensional }

noncomputable def matrixJumpCPMap (V : ι → Matrix d d ℂ) :
    Matrix d d ℂ →CP Matrix d d ℂ :=
  completelyPositiveMapFinsetSum Finset.univ
    (fun i => completelyPositiveMapConjugation (V i))

@[simp]
lemma matrixJumpCPMap_apply (V : ι → Matrix d d ℂ) (X : Matrix d d ℂ) :
    matrixJumpCPMap V X = ∑ i, (V i).conjTranspose * X * V i := by
  simp [matrixJumpCPMap, completelyPositiveMap_finsetSum_apply,
    completelyPositiveMap_conjugation_apply, Matrix.star_eq_conjTranspose,
    Matrix.mul_assoc]

noncomputable def matrixChristensenEvansData
    (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) : ChristensenEvansData (Matrix d d ℂ) where
  hamiltonian := ⟨H, selfAdjoint.mem_iff.mpr (by
    rw [Matrix.star_eq_conjTranspose]
    exact hH)⟩
  jump := matrixJumpCPMap V

lemma matrixChristensenEvansData_generator_apply
    (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) (X : Matrix d d ℂ) :
    (matrixChristensenEvansData H hH V).generator X =
      matrixLindbladGenerator H hH V X := by
  rw [ChristensenEvansData.generator_apply, matrixLindbladGenerator_apply]
  simp [matrixChristensenEvansData, matrixJumpCPMap_apply,
    ChristensenEvansData.jumpMap, matrixMulLeft, matrixMulRight,
    Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_smul,
    Finset.sum_mul, Matrix.mul_sum, Matrix.mul_assoc]
  simp only [← Finset.smul_sum]
  module

lemma finiteDimensional_generator_isChristensenEvans
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) :
    IsChristensenEvansGenerator
      (matrixMapToContinuousLinearMap (finiteDimensionalGenerator Φ).map) := by
  obtain ⟨H, hH, V, hL⟩ := exists_lindblad_generator_of_continuous Φ
  refine ⟨matrixChristensenEvansData H hH V, ?_⟩
  apply ContinuousLinearMap.ext
  intro X
  rw [matrixChristensenEvansData_generator_apply]
  change (matrixLindbladGenerator H hH V) X =
    (finiteDimensionalGenerator Φ).map X
  rw [← hL]

end OperatorAlgebra
