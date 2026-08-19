/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!

# Finite-dimensional operator algebras as matrix algebras

For a finite target type `d`, the operator algebra `𝒜[d]` is star-algebra equivalent to the
algebra of `d × d` matrices, via the standard basis. This file records that equivalence and
the induced equivalence between abstract observables and self-adjoint matrices.

This is the *only* file in which a finite-dimensional operator algebra should be unfolded down
to a matrix: everywhere else, `d × d` matrices are reached (if at all) only through
`operatorAlgebraEquivMatrix` or `observableMatrixEquiv`, never by hand.

## Main definitions

* `operatorAlgebraEquivMatrix`: the star-algebra equivalence `𝒜[d] ≃⋆ₐ[ℂ] Matrix d d ℂ`.
* `observableMatrixEquiv`: the induced real-linear equivalence of self-adjoint elements,
  `𝒪[d] ≃ₗ[ℝ] selfAdjoint (Matrix d d ℂ)`.

-/

@[expose] public section

open scoped Matrix.Norms.L2Operator

namespace QuantumMechanics

variable {d : Type*} [Fintype d] [DecidableEq d]

/--
The star-algebra equivalence between the operator algebra of a finite-dimensional quantum
system and `d × d` matrices, induced by the standard basis: conjugate by the isometry
`𝓗[d] ≃ EuclideanSpace ℂ d`, then read off matrix entries via `Matrix.toEuclideanCLM`.
-/
noncomputable def operatorAlgebraEquivMatrix :
    𝒜[d] ≃⋆ₐ[ℂ] Matrix d d ℂ :=
  (FiniteHilbertSpace.isometryEquivEuclidean (d := d)).conjStarAlgEquiv.trans
    (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)).symm

/--
Observables of a finite-dimensional quantum system are linearly equivalent to self-adjoint
`d × d` matrices.

This is `operatorAlgebraEquivMatrix.selfAdjointCongr`, restated by hand: `𝒜[d]`'s `Module ℝ`
instance is resolved via `ContinuousLinearMap.module` rather than the generic
`Module.complexToReal` that a bare `[Algebra ℂ A]` hypothesis picks up, so the two don't unify
syntactically even though they agree propositionally.
-/
noncomputable def observableMatrixEquiv :
    𝒪[d] ≃ₗ[ℝ] selfAdjoint (Matrix d d ℂ) where
  toFun A := ⟨operatorAlgebraEquivMatrix (A : 𝒜[d]), A.property.map operatorAlgebraEquivMatrix⟩
  invFun M := ⟨operatorAlgebraEquivMatrix.symm M, M.property.map operatorAlgebraEquivMatrix.symm⟩
  left_inv A := by
    apply Subtype.ext
    show operatorAlgebraEquivMatrix.symm (operatorAlgebraEquivMatrix (A : 𝒜[d])) = (A : 𝒜[d])
    exact operatorAlgebraEquivMatrix.symm_apply_apply (A : 𝒜[d])
  right_inv M := by
    apply Subtype.ext
    show operatorAlgebraEquivMatrix (operatorAlgebraEquivMatrix.symm (M : Matrix d d ℂ)) =
      (M : Matrix d d ℂ)
    exact operatorAlgebraEquivMatrix.apply_symm_apply (M : Matrix d d ℂ)
  map_add' A B := by
    apply Subtype.ext
    show operatorAlgebraEquivMatrix ((A : 𝒜[d]) + (B : 𝒜[d])) =
      operatorAlgebraEquivMatrix (A : 𝒜[d]) + operatorAlgebraEquivMatrix (B : 𝒜[d])
    exact map_add operatorAlgebraEquivMatrix (A : 𝒜[d]) (B : 𝒜[d])
  map_smul' r A := by
    apply Subtype.ext
    show operatorAlgebraEquivMatrix (r • (A : 𝒜[d])) = r • operatorAlgebraEquivMatrix (A : 𝒜[d])
    rw [show r • (A : 𝒜[d]) = (r : ℂ) • (A : 𝒜[d]) from (Complex.coe_smul r (A : 𝒜[d])).symm,
      map_smul, Complex.coe_smul]

/-!
### Continuity, and compatibility with the exponential map

`Matrix.toEuclideanCLM`'s operator norm is *definitionally* the pushforward of the Euclidean
operator norm, so it (and its inverse) is an isometry. Continuity of `operatorAlgebraEquivMatrix`
then follows from continuity of its two constituent pieces, and both maps commute with
`NormedSpace.exp`: this is what lets closed-form matrix computations (e.g. the Pauli cosine-sine
rotation formula) be transported to statements about time evolution at the operator level.
-/

lemma _root_.Matrix.toEuclideanCLM_isometry :
    Isometry (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)) :=
  AddMonoidHomClass.isometry_of_norm _ (fun A => Matrix.cstar_norm_def A)

lemma _root_.Matrix.toEuclideanCLM_continuous :
    Continuous (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)) :=
  Matrix.toEuclideanCLM_isometry.continuous

lemma _root_.Matrix.toEuclideanCLM_symm_continuous :
    Continuous (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)).symm :=
  (Isometry.of_dist_eq fun x y => by
    have h := Matrix.toEuclideanCLM_isometry.dist_eq
      ((Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)).symm x)
      ((Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)).symm y)
    simp at h
    rw [h]).continuous

/-- `Matrix.toEuclideanCLM` commutes with the exponential map. -/
lemma _root_.Matrix.toEuclideanCLM_exp (x : Matrix d d ℂ) :
    Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) (NormedSpace.exp x) =
      NormedSpace.exp (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) x) := by
  let _ : NormedAlgebra ℚ (Matrix d d ℂ) := .restrictScalars ℚ ℂ _
  let _ : NormedAlgebra ℚ (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) := .restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ))
    Matrix.toEuclideanCLM_continuous x

-- The `synthInstance.maxHeartbeats` bump is needed because of the size of the ambient instance
-- cache, not because this instance search is actually hard; it is otherwise the same proof.
set_option synthInstance.maxHeartbeats 400000 in
/-- `operatorAlgebraEquivMatrix` is continuous: both of its two constituent pieces
(conjugation by a Hilbert-space isometry, and the identification of matrices with Euclidean
operators) are isometries. -/
theorem operatorAlgebraEquivMatrix_continuous :
    Continuous (operatorAlgebraEquivMatrix (d := d)) := by
  have h1 : Continuous (FiniteHilbertSpace.isometryEquivEuclidean (d := d)).conjStarAlgEquiv := by
    have h : ⇑(FiniteHilbertSpace.isometryEquivEuclidean (d := d)).conjStarAlgEquiv =
        ⇑((FiniteHilbertSpace.isometryEquivEuclidean (d := d)).toContinuousLinearEquiv.conjContinuousAlgEquiv) := by
      funext x
      rw [LinearIsometryEquiv.conjStarAlgEquiv_apply, ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
      rfl
    rw [h]
    exact map_continuous _
  exact Matrix.toEuclideanCLM_symm_continuous.comp h1

/-- `operatorAlgebraEquivMatrix` commutes with the exponential map: taking the matrix of an
operator and exponentiating agree in either order. -/
lemma operatorAlgebraEquivMatrix_exp (x : 𝒜[d]) :
    operatorAlgebraEquivMatrix (NormedSpace.exp x) =
      NormedSpace.exp (operatorAlgebraEquivMatrix x) := by
  let _ : NormedAlgebra ℚ (𝒜[d]) := .restrictScalars ℚ ℂ _
  exact NormedSpace.map_exp operatorAlgebraEquivMatrix operatorAlgebraEquivMatrix_continuous x

/-- The matrix of an operator of a finite-dimensional quantum system, in the standard basis. -/
noncomputable def operatorToMatrix (A : 𝒜[d]) :
    Matrix d d ℂ :=
  operatorAlgebraEquivMatrix A

/-- An observable of a finite-dimensional quantum system, as a self-adjoint `d × d` matrix. -/
noncomputable def Observable.toMatrix (A : 𝒪[d]) :
    selfAdjoint (Matrix d d ℂ) :=
  observableMatrixEquiv A

@[simp]
lemma coe_observable_toMatrix (A : 𝒪[d]) :
    (Observable.toMatrix A : Matrix d d ℂ) = operatorToMatrix (A : 𝒜[d]) :=
  rfl

/-- The operator trace agrees with the matrix trace of the corresponding matrix, in the standard
basis: `operatorAlgebraEquivMatrix` conjugates by an isometry, and the standard basis realizes
`Matrix.toEuclideanCLM` as `LinearMap.toLin`, so trace is preserved at each step. -/
theorem operatorTrace_eq_matrix_trace (A : 𝒜[d]) :
    operatorTrace A = Matrix.trace (operatorToMatrix A) := by
  have step1 : LinearMap.trace ℂ 𝓗[d] (A : 𝓗[d] →ₗ[ℂ] 𝓗[d]) =
      LinearMap.trace ℂ (EuclideanSpace ℂ d)
        ((FiniteHilbertSpace.isometryEquivEuclidean (d := d)).conjStarAlgEquiv A :
          EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d) := by
    rw [show ((FiniteHilbertSpace.isometryEquivEuclidean (d := d)).conjStarAlgEquiv A :
        EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) =
        (FiniteHilbertSpace.isometryEquivEuclidean (d := d)).toLinearEquiv.conj
          (A : 𝓗[d] →ₗ[ℂ] 𝓗[d]) from ?_]
    · rw [LinearMap.trace_conj']
    · ext v
      simp [LinearIsometryEquiv.conjStarAlgEquiv_apply]
  have step2 : ∀ M : Matrix d d ℂ,
      LinearMap.trace ℂ (EuclideanSpace ℂ d)
        (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) M :
          EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d) = Matrix.trace M := by
    intro M
    rw [show (Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ) M :
        EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d) = Matrix.toEuclideanLin M from
      Matrix.coe_toEuclideanCLM_eq_toEuclideanLin M]
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]
  have step3 := step2 ((Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)).symm
    ((FiniteHilbertSpace.isometryEquivEuclidean (d := d)).conjStarAlgEquiv A))
  rw [(Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)).apply_symm_apply] at step3
  rw [operatorTrace, operatorToMatrix, operatorAlgebraEquivMatrix]
  show LinearMap.trace ℂ 𝓗[d] (A : 𝓗[d] →ₗ[ℂ] 𝓗[d]) = _
  rw [step1, step3]
  rfl

end QuantumMechanics
