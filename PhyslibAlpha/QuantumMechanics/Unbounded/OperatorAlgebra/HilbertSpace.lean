/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Bounded operators on Hilbert space

This file connects the abstract operator-algebraic quantum-mechanics API with the concrete
C⋆-algebra of bounded operators on a complex Hilbert space. The C⋆-algebra, Loewner order, and
ordered-star-ring instances for bounded operators are supplied by Mathlib.

This is the general level, for any complex Hilbert space `H`: nothing here needs
`FiniteDimensional ℂ H`. Finite-dimensional specializations (trace pairing, density operators,
spectral decompositions) live under `FiniteDim/`; they should build on `operator_nonneg_iff_
isPositive` rather than reprove it.
-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder InnerProductSpace

/-- Bounded operators on a complex Hilbert space, written in the usual physics notation. -/
notation "B(" H ")" => H →L[ℂ] H

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded operators form an `OperatorAlgebra` using Mathlib's native Hilbert-space instances. -/
noncomputable instance instOperatorAlgebraBoundedOperators : OperatorAlgebra B(H) := {}

/-- Physlib's spectral order on bounded operators agrees with Hilbert-space positivity. -/
lemma operator_nonneg_iff_isPositive (T : B(H)) :
    0 ≤ T ↔ T.IsPositive := by
  constructor
  · intro hT
    obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
    simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using
      ContinuousLinearMap.isPositive_adjoint_comp_self S
  · intro hT
    rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts]
    exact ⟨hT.isSelfAdjoint, QuasispectrumRestricts.nnreal_iff.mpr
      (QuasispectrumRestricts.nnreal_iff.mp (sub_zero T ▸ hT.spectrumRestricts))⟩

/-- A positive operator vanishing in the quadratic form `⟪T x, x⟫` at `x` already vanishes at
`x`. -/
lemma operator_apply_eq_zero_of_inner_eq_zero {T : B(H)} (hT : 0 ≤ T) (x : H)
    (hx : ⟪T x, x⟫_ℂ = 0) : T x = 0 := by
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT
  have hSx : S x = 0 := by
    rw [hS, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] at hx
    change ⟪ContinuousLinearMap.adjoint S (S x), x⟫_ℂ = 0 at hx
    rw [ContinuousLinearMap.adjoint_inner_left] at hx
    exact inner_self_eq_zero.mp hx
  rw [hS]
  change ContinuousLinearMap.adjoint S (S x) = 0
  rw [hSx, map_zero]

section Representation

/-- A Hilbert-space representation of `A` as a unital ⋆-homomorphism into `B(H)`. -/
abbrev Representation (A H : Type*) [OperatorAlgebra A] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] := A →⋆ₐ[ℂ] B(H)

end Representation

end OperatorAlgebra
