/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.FiniteDim.Matrix
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!

# Trace pairing and positive-operator spectral theory in finite dimensions

On a finite-dimensional complex Hilbert space `H`, this file develops the finite-dimensional
operator theory used to represent states by density operators:

* `operatorTracePairing`, the bilinear pairing `(ρ, A) ↦ Tr(ρA)` on `B(H)`, and the fact that
  it is symmetric and nondegenerate (`operatorTracePairing_nondegenerate`).
* `operatorTracePairing_nonneg`, `0 ≤ ρ → 0 ≤ A → 0 ≤ Tr(ρA)`, built on `operator_nonneg_iff_
  isPositive` from `OperatorAlgebra.HilbertSpace` (that fact needs no finite-dimensionality, so
  it lives there, not here).
* `operator_eq_sum_eigen_rankOne`, the spectral (eigenbasis) decomposition of a positive
  operator as a sum of rank-one projectors. This genuinely needs `FiniteDimensional ℂ H`
  (the eigenbasis) and the trace (to normalize eigenvalues), so it belongs here.

None of this is specific to states or density operators; it belongs to finite-dimensional
operator theory on its own.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-!
## The trace pairing
-/

/-- The trace pairing `(ρ, A) ↦ Tr(ρA)` on bounded operators on a finite-dimensional Hilbert
space. -/
noncomputable def operatorTracePairing :
    (B(H)) →ₗ[ℂ] (B(H)) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun ρ A => LinearMap.trace ℂ H (ρ * A).toLinearMap)
    (fun ρ₁ ρ₂ A => by simp [add_mul])
    (fun c ρ A => by simp)
    (fun ρ A₁ A₂ => by simp [mul_add])
    (fun c ρ A => by simp)

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
lemma operatorTracePairing_apply (ρ A : B(H)) :
    operatorTracePairing ρ A = LinearMap.trace ℂ H (ρ * A).toLinearMap :=
  rfl

omit [CompleteSpace H] in
lemma operatorTracePairing_rankOne (ρ : B(H)) (x y : H) :
    operatorTracePairing ρ (InnerProductSpace.rankOne ℂ x y) = ⟪y, ρ x⟫_ℂ := by
  rw [operatorTracePairing_apply, ContinuousLinearMap.mul_def,
    InnerProductSpace.comp_rankOne, InnerProductSpace.trace_rankOne]

/-- The trace pairing of a rank-one operator against an arbitrary operator, evaluated on the
left. This is the algebraic fact underlying the usual Hilbert-space expectation-value formula
`⟪ψ, A ψ⟫`. -/
lemma operatorTracePairing_rankOne_left (x y : H) (A : B(H)) :
    operatorTracePairing (InnerProductSpace.rankOne ℂ x y) A = ⟪y, A x⟫_ℂ := by
  rw [operatorTracePairing_apply, ContinuousLinearMap.mul_def,
    InnerProductSpace.rankOne_comp, InnerProductSpace.trace_rankOne,
    ContinuousLinearMap.adjoint_inner_left]

omit [FiniteDimensional ℂ H] [CompleteSpace H] in
lemma operatorTracePairing_isSymm : (operatorTracePairing (H := H)).IsSymm :=
  ⟨fun ρ A => by
    change LinearMap.trace ℂ H (ρ.toLinearMap * A.toLinearMap) =
      LinearMap.trace ℂ H (A.toLinearMap * ρ.toLinearMap)
    exact LinearMap.trace_mul_comm ℂ ρ.toLinearMap A.toLinearMap⟩

omit [CompleteSpace H] in
lemma operatorTracePairing_separatingLeft :
    (operatorTracePairing (H := H)).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_linear_nontrivial]
  intro ρ hρ
  apply ContinuousLinearMap.ext
  intro x
  have h := congrFun (congrArg DFunLike.coe hρ)
    (InnerProductSpace.rankOne ℂ x (ρ x))
  simp only [operatorTracePairing_rankOne, LinearMap.zero_apply] at h
  simpa using (inner_self_eq_zero.mp h)

omit [CompleteSpace H] in
lemma operatorTracePairing_nondegenerate :
    (operatorTracePairing (H := H)).Nondegenerate :=
  (operatorTracePairing_isSymm.isRefl).nondegenerate_iff_separatingLeft.mpr
    operatorTracePairing_separatingLeft

/-- The trace pairing of two positive operators is nonnegative. -/
lemma operatorTracePairing_nonneg {ρ A : B(H)} (hρ : 0 ≤ ρ) (hA : 0 ≤ A) :
    0 ≤ operatorTracePairing ρ A := by
  have hρ' := (operator_nonneg_iff_isPositive ρ).mp hρ
  obtain ⟨m, u, rfl⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp
    ((operator_nonneg_iff_isPositive A).mp hA)
  rw [map_sum]
  exact Finset.sum_nonneg fun i _ => by
    rw [operatorTracePairing_rankOne]
    exact hρ'.inner_nonneg_right (u i)

/-!
## Positive-operator spectral decomposition
-/

omit [CompleteSpace H] in
/-- A positive operator on a finite-dimensional complex Hilbert space decomposes as a sum of
rank-one projectors onto an eigenbasis, with nonnegative eigenvalue coefficients. -/
lemma operator_eq_sum_eigen_rankOne {T : B(H)} (hT : T.IsPositive) :
    T = ∑ i : Fin (Module.finrank ℂ H),
      (hT.isSymmetric.eigenvalues rfl i : ℂ) • InnerProductSpace.rankOne ℂ
        (hT.isSymmetric.eigenvectorBasis rfl i) (hT.isSymmetric.eigenvectorBasis rfl i) := by
  apply ContinuousLinearMap.ext
  intro x
  conv_lhs =>
    rw [← (hT.isSymmetric.eigenvectorBasis rfl).sum_repr x]
  rw [map_sum, _root_.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  have heig :
      T.toLinearMap (hT.isSymmetric.eigenvectorBasis rfl i) =
        (hT.isSymmetric.eigenvalues rfl i : ℂ) •
          hT.isSymmetric.eigenvectorBasis rfl i := by
    exact hT.isSymmetric.apply_eigenvectorBasis rfl i
  change ((hT.isSymmetric.eigenvectorBasis rfl).repr x i) •
    T.toLinearMap (hT.isSymmetric.eigenvectorBasis rfl i) = _
  rw [heig]
  simp only [OrthonormalBasis.repr_apply_apply, smul_apply,
    InnerProductSpace.rankOne_apply, smul_smul]
  rw [mul_comm]

end OperatorAlgebra
