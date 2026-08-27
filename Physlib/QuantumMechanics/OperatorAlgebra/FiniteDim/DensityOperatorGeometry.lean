/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.FiniteDim.DensityOperator

/-!

# Density operators form a compact convex set

Geometric facts about the set of density operators on a finite-dimensional complex Hilbert space,
independent of the state–density-operator correspondence: it is convex, closed, bounded, hence
compact, and (when `H` is nonzero) nonempty.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- The trace as a continuous linear functional on the finite-dimensional operator space. -/
noncomputable def continuousOperatorTrace : (B(H)) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℂ H).comp (ContinuousLinearMap.coeLM ℂ))

omit [CompleteSpace H] in
@[simp]
lemma continuousOperatorTrace_apply (ρ : B(H)) :
    continuousOperatorTrace ρ = LinearMap.trace ℂ H ρ.toLinearMap :=
  rfl

/-- Density operators form a convex subset of the real vector space of bounded operators. -/
theorem densityOperatorSet_convex : Convex ℝ (densityOperatorSet H) := by
  intro ρ hρ σ hσ a b ha hb hab
  constructor
  · exact add_nonneg (smul_nonneg ha hρ.1) (smul_nonneg hb hσ.1)
  · change LinearMap.trace ℂ H
      ((((a : ℂ) • ρ) + ((b : ℂ) • σ)).toLinearMap) = 1
    rw [ContinuousLinearMap.toLinearMap_add, map_add,
      ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_smul,
      map_smul, map_smul, hρ.2, hσ.2]
    simp only [smul_eq_mul, mul_one]
    exact_mod_cast hab

/-- The set of density operators is closed in operator norm. -/
theorem densityOperatorSet_isClosed : IsClosed (densityOperatorSet H) := by
  have htrace : IsClosed {ρ : B(H) | continuousOperatorTrace ρ = 1} :=
    isClosed_eq continuousOperatorTrace.continuous continuous_const
  rw [show densityOperatorSet H = Set.Ici 0 ∩
      {ρ : B(H) | continuousOperatorTrace ρ = 1} by rfl]
  exact isClosed_Ici.inter htrace

/-- The set of density operators is bounded in operator norm. -/
theorem densityOperatorSet_isBounded : Bornology.IsBounded (densityOperatorSet H) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, ?_⟩
  intro ρ hρ
  exact DensityOperator.norm_le_one ⟨ρ, hρ⟩

/-- Density operators form a compact subset of the finite-dimensional operator space. -/
theorem densityOperatorSet_isCompact : IsCompact (densityOperatorSet H) := by
  let _ : ProperSpace (B(H)) := FiniteDimensional.proper ℂ (B(H))
  exact Metric.isCompact_of_isClosed_isBounded densityOperatorSet_isClosed
    densityOperatorSet_isBounded

/-- On a nonzero Hilbert space, the set of density operators is nonempty. -/
theorem densityOperatorSet_nonempty [Nontrivial H] : (densityOperatorSet H).Nonempty := by
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  let ψ := ‖x‖⁻¹ • x
  have hψ : ‖ψ‖ = 1 := by
    simp [ψ, norm_smul, inv_mul_cancel₀ (norm_pos_iff.mpr hx).ne']
  exact ⟨(DensityOperator.rankOne ψ hψ).1,
    (DensityOperator.rankOne ψ hψ).2⟩

/-- The bundled type of density operators is compact in its subtype topology. -/
noncomputable instance densityOperatorCompactSpace : CompactSpace (DensityOperator H) :=
  isCompact_iff_compactSpace.mp densityOperatorSet_isCompact

end OperatorAlgebra
