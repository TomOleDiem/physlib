/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.FiniteDim.Trace

/-!

# Density operators in finite dimensions

A density operator on a finite-dimensional complex Hilbert space `H` is a positive operator with
trace one. This file collects the basic definitions (`DensityOperator`, `DensityOperator.rankOne`,
`DensityOperator.IsRankOneProjector`) and the spectral decomposition of a density operator, built
from the positive-operator spectral theorem in `FiniteDim.Trace`.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- The set of positive trace-one operators on a finite-dimensional complex Hilbert space. -/
@[nolint unusedArguments]
def densityOperatorSet (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] :=
  {ρ : B(H) | 0 ≤ ρ ∧ LinearMap.trace ℂ H ρ.toLinearMap = 1}

/-- A density operator on a finite-dimensional complex Hilbert space is a positive operator
with trace one.

Kept as an `abbrev` for `densityOperatorSet` rather than a fresh structure: the set itself is
useful directly for `Convex`, `IsClosed`, `IsCompact`, etc. -/
abbrev DensityOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H] :=
  densityOperatorSet H

namespace DensityOperator

/-- A density operator is a rank-one projector if it is the orthogonal projector onto the span
of a unit vector. -/
def IsRankOneProjector (ρ : DensityOperator H) : Prop :=
  ∃ ψ : H, ‖ψ‖ = 1 ∧ ρ.1 = InnerProductSpace.rankOne ℂ ψ ψ

/-- The rank-one density operator associated with a unit vector. -/
noncomputable def rankOne (ψ : H) (hψ : ‖ψ‖ = 1) : DensityOperator H where
  val := InnerProductSpace.rankOne ℂ ψ ψ
  property := ⟨(operator_nonneg_iff_isPositive _).mpr
    (InnerProductSpace.isPositive_rankOne_self ψ), by
      rw [InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K, hψ]
      norm_num⟩

@[simp]
lemma rankOne_val (ψ : H) (hψ : ‖ψ‖ = 1) :
    (rankOne ψ hψ : B(H)) = InnerProductSpace.rankOne ℂ ψ ψ :=
  rfl

lemma isRankOneProjector_rankOne (ψ : H) (hψ : ‖ψ‖ = 1) :
    DensityOperator.IsRankOneProjector (rankOne ψ hψ) :=
  ⟨ψ, hψ, rfl⟩

/-!
## Spectral decomposition
-/

/-- The spectral decomposition of a density operator: its eigenvalues form a probability
distribution and its eigenvectors give unit rank-one projectors. -/
lemma spectralDecomposition (ρ : DensityOperator H) :
    ∃ (p : Fin (Module.finrank ℂ H) → ℝ) (ψ : Fin (Module.finrank ℂ H) → H),
      (∀ i, 0 ≤ p i) ∧ (∀ i, ‖ψ i‖ = 1) ∧ (∑ i, p i) = 1 ∧
        ρ.1 = ∑ i, (p i : ℂ) • InnerProductSpace.rankOne ℂ (ψ i) (ψ i) := by
  let hρ : ρ.1.IsPositive := (operator_nonneg_iff_isPositive ρ.1).mp ρ.2.1
  let p : Fin (Module.finrank ℂ H) → ℝ := hρ.isSymmetric.eigenvalues rfl
  let ψ : Fin (Module.finrank ℂ H) → H := hρ.isSymmetric.eigenvectorBasis rfl
  refine ⟨p, ψ, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hρ.toLinearMap.nonneg_eigenvalues rfl i
  · intro i
    exact OrthonormalBasis.norm_eq_one _ i
  · calc
      ∑ i, p i = Complex.re (LinearMap.trace ℂ H ρ.1.toLinearMap) := by
        exact (hρ.toLinearMap.isSymmetric.re_trace_eq_sum_eigenvalues rfl).symm
      _ = 1 := by rw [ρ.2.2]; norm_num
  · exact operator_eq_sum_eigen_rankOne hρ

/-- Every density operator has operator norm at most one. -/
lemma norm_le_one (ρ : DensityOperator H) : ‖(ρ.1 : B(H))‖ ≤ 1 := by
  obtain ⟨p, ψ, hp, hψ, hsum, hop⟩ := DensityOperator.spectralDecomposition ρ
  rw [hop]
  calc
    ‖∑ i, (p i : ℂ) • InnerProductSpace.rankOne ℂ (ψ i) (ψ i)‖ ≤
        ∑ i, ‖(p i : ℂ) • InnerProductSpace.rankOne ℂ (ψ i) (ψ i)‖ :=
      norm_sum_le _ _
    _ = ∑ i, p i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, InnerProductSpace.norm_rankOne, hψ i, mul_one]
      simpa using abs_of_nonneg (hp i)
    _ = 1 := hsum

end DensityOperator

end OperatorAlgebra
