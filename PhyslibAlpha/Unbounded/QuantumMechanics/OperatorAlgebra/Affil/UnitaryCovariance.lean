/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Affil.Concrete
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Spec.CayleySpectralData
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.SpectralTheory.SpectralIntegral

/-!
# Unitary covariance of unbounded spectral data

This file packages the covariance statements which are repeatedly needed when an unbounded
operator is moved between unitarily equivalent Hilbert-space realizations.  The important point
is that covariance transports the *domain-aware* theorem, not merely the weak integral identity:
the square-moment domain and the closure are transported at the same time.
-/

@[expose] public section

open scoped InnerProductSpace
open MeasureTheory

namespace QuantumMechanics
namespace WOTSpectralMeasure

open OperatorAlgebra

variable {α : Type*} [MeasurableSpace α] [Nonempty α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded spectral integration commutes with transport through a Hilbert-space unitary. -/
theorem unitaryConj_boundedIntegral
    (μS : WOTSpectralMeasure α H)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') (f : α → ℂ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ a, ‖f a‖ ≤ C)
    (hfinite : ∀ x y : H, IsFiniteMeasure (μS.scalarMeasure x y).variation) :
    boundedIntegral (unitaryConjSpectralMeasure u μS) f hf hfb =
      unitaryConj u (boundedIntegral μS f hf hfb) := by
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  have hfinite' : IsFiniteMeasure
      ((unitaryConjSpectralMeasure u μS).scalarMeasure x y).variation := by
    rw [unitaryConjSpectralMeasure_scalarMeasure]
    exact hfinite (u.symm x) (u.symm y)
  rw [boundedIntegral_inner (unitaryConjSpectralMeasure u μS) hf hfb x y hfinite']
  change _ = ⟪y, u ((boundedIntegral μS f hf hfb) (u.symm x))⟫_ℂ
  calc
    _ = ∫ᵛ a, f a ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μS.scalarMeasure (u.symm x) (u.symm y)] := by
      rw [unitaryConjSpectralMeasure_scalarMeasure]
    _ = ⟪u.symm y, (boundedIntegral μS f hf hfb) (u.symm x)⟫_ℂ := by
      exact (boundedIntegral_inner μS hf hfb (u.symm x) (u.symm y)
        (hfinite (u.symm x) (u.symm y))).symm
    _ = ⟪y, u ((boundedIntegral μS f hf hfb) (u.symm x))⟫_ℂ :=
      u.symm.inner_map_eq_flip _ _

/-- In particular, the strongly continuous unitary group obtained from a spectral measure is
covariant under unitary transport. -/
theorem unitaryConj_expIntegral
    (μS : WOTSpectralMeasure ℝ H)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') (t : ℝ) :
    expIntegral (unitaryConjSpectralMeasure u μS) t =
      unitaryConj u (expIntegral μS t) := by
  exact unitaryConj_boundedIntegral μS u (expFunction t)
    (expFunction_measurable t) (expFunction_bounded t)
    (fun x y => scalarMeasure_isFiniteVariation μS x y)

/-! ### Cayley-side transport and bounded commutation -/

/-- For the bounded spectral measures used by the Cayley construction, unitary transport commutes
with pushing the measure forward along the Cayley coordinate. -/
theorem cayleyMap_unitaryConjSpectralMeasure
    (μS : WOTSpectralMeasure ℝ H)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') :
    cayleyMap (unitaryConjSpectralMeasure u μS) =
      unitaryConjSpectralMeasure u (cayleyMap μS) := by
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  change ((unitaryConjSpectralMeasure u μS).toVectorMeasure.map cayley) S =
    (cayleyMap μS).toVectorMeasure.mapRange (unitaryConjAddHom u)
      (continuous_unitaryConjAddHom u) S
  rw [MeasureTheory.VectorMeasure.map_apply _ measurable_cayley hS]
  rw [MeasureTheory.VectorMeasure.mapRange_apply]
  change (unitaryConjSpectralMeasure u μS) (cayley ⁻¹' S) =
    unitaryConj u ((cayleyMap μS) S)
  rw [unitaryConjSpectralMeasure_apply]
  change unitaryConj u (μS (cayley ⁻¹' S)) =
    unitaryConj u ((μS.toVectorMeasure.map cayley) S)
  rw [MeasureTheory.VectorMeasure.map_apply _ measurable_cayley hS]

/- A bounded operator commutes with every Cayley spectral projection exactly when its unitary
conjugation leaves each projection fixed.  Stating this equivalence at the WOT level keeps the
unbounded commutant API independent of a particular representation of the ambient algebra. -/
theorem unitaryConj_eq_self_iff_commute
    (u : H ≃ₗᵢ[ℂ] H) (A : H →WOT[ℂ] H) :
    unitaryConj u A = A ↔
      Commute (u.toLinearIsometry.toContinuousLinearMap)
        (ContinuousLinearMapWOT.toCLM A) := by
  constructor
  · intro h
    rw [commute_iff_eq]
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun F : H →L[ℂ] H => F (u x))
      (congrArg ContinuousLinearMapWOT.toCLM h)
    simpa [unitaryConj, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply] using hx
  · intro h
    apply ContinuousLinearMapWOT.toCLM_injective
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun F : H →L[ℂ] H => F (u.symm x)) h.eq
    simpa [unitaryConj, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
      u.apply_symm_apply] using hx

/-! ### Recovering real spectral invariance from the Cayley side -/

/-- Cayley pushforward is injective even after unitary transport.  This is the uniqueness step
which lets commutation be checked on the bounded transform. -/
theorem unitaryConjSpectralMeasure_eq_of_cayleyMap_eq
    (μS : WOTSpectralMeasure ℝ H)
    (u : H ≃ₗᵢ[ℂ] H)
    (h : unitaryConjSpectralMeasure u (cayleyMap μS) = cayleyMap μS) :
    unitaryConjSpectralMeasure u μS = μS := by
  apply cayleyMap_injective
  rw [cayleyMap_unitaryConjSpectralMeasure]
  exact h

/-- A bounded commutation certificate directly implies invariance of a real spectral measure.
This is the generic Cayley uniqueness lemma; no self-adjoint operator is needed yet. -/
theorem spectralMeasure_invariant_of_cayley_projection_commute
    (μS : WOTSpectralMeasure ℝ H)
    (u : H ≃ₗᵢ[ℂ] H)
    (hcomm : ∀ S : Set ℂ, MeasurableSet S →
      Commute (u.toLinearIsometry.toContinuousLinearMap)
        (ContinuousLinearMapWOT.toCLM (cayleyMap μS S))) :
    unitaryConjSpectralMeasure u μS = μS := by
  apply unitaryConjSpectralMeasure_eq_of_cayleyMap_eq μS u
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  rw [unitaryConjSpectralMeasure_apply]
  exact (unitaryConj_eq_self_iff_commute u _).2 (hcomm S hS)

end QuantumMechanics.WOTSpectralMeasure

namespace OperatorAlgebra
namespace DomainAwareSelfAdjointSpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

/-- The maximal spectral integral of a unitarily transported PVM is the unitarily transported
operator.  This is the packaged operator equality behind unitary covariance. -/
theorem unitaryConj_maximal_eq
    (D : DomainAwareSelfAdjointSpectralTheorem T μS)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') :
    QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
        (QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u μS) =
      LinearPMap.unitaryConj u T := by
  exact (D.unitaryConj u).maximal_eq

end DomainAwareSelfAdjointSpectralTheorem

namespace SelfAdjointSpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H}

/-- A symmetry commuting with every projection of the canonical bounded Cayley spectral measure
also commutes with the original self-adjoint operator.  The proof passes through Cayley
pushforward injectivity and the maximal-integral uniqueness theorem. -/
theorem unitaryConj_eq_of_cayley_projection_commute
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T)
    (u : H ≃ₗᵢ[ℂ] H)
    (hcomm : ∀ S : Set ℂ, MeasurableSet S →
      Commute (u.toLinearIsometry.toContinuousLinearMap)
        (ContinuousLinearMapWOT.toCLM
          (cayleyBoundedSpectralMeasure T hT S))) :
    LinearPMap.unitaryConj u T = T := by
  let μR := cayleyRealSpectralMeasure T hT
  have hmap : QuantumMechanics.WOTSpectralMeasure.cayleyMap μR =
      cayleyBoundedSpectralMeasure T hT := by
    exact cayleyMap_cayleyRealSpectralMeasure T hT
  have hμ : QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u μR = μR := by
    apply QuantumMechanics.WOTSpectralMeasure.spectralMeasure_invariant_of_cayley_projection_commute
      μR u
    intro S hS
    have hS' := congrArg (fun E : QuantumMechanics.WOTSpectralMeasure ℂ H => E S) hmap
    rw [hS']
    exact hcomm S hS
  let D := cayleyDomainAwareSelfAdjointSpectralTheorem T hT
  have htransport := (D.unitaryConj u).maximal_eq
  rw [hμ] at htransport
  exact htransport.symm.trans D.maximal_eq

/-- The canonical Stone group of a self-adjoint operator is fixed by the same Cayley-side
commutation certificate. -/
theorem expIntegral_eq_of_cayley_projection_commute
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T)
    (u : H ≃ₗᵢ[ℂ] H)
    (hcomm : ∀ S : Set ℂ, MeasurableSet S →
      Commute (u.toLinearIsometry.toContinuousLinearMap)
        (ContinuousLinearMapWOT.toCLM
          (cayleyBoundedSpectralMeasure T hT S)))
    (t : ℝ) :
    QuantumMechanics.WOTSpectralMeasure.unitaryConj u
        (QuantumMechanics.WOTSpectralMeasure.expIntegral
          (cayleyRealSpectralMeasure T hT) t) =
      QuantumMechanics.WOTSpectralMeasure.expIntegral
        (cayleyRealSpectralMeasure T hT) t := by
  let μR := cayleyRealSpectralMeasure T hT
  have hμ :=
    QuantumMechanics.WOTSpectralMeasure.spectralMeasure_invariant_of_cayley_projection_commute
      μR u (by
      intro S hS
      have hmap := cayleyMap_cayleyRealSpectralMeasure T hT
      have hS' := congrArg (fun E : QuantumMechanics.WOTSpectralMeasure ℂ H => E S) hmap
      rw [hS']
      exact hcomm S hS)
  have hgroup := QuantumMechanics.WOTSpectralMeasure.unitaryConj_expIntegral μR u t
  rw [hμ] at hgroup
  exact hgroup.symm

end SelfAdjointSpectralTheorem

namespace EssentialSelfAdjointSpectralData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H}

/-- The strongly continuous unitary group attached to the closure represented by the spectral
data package. -/
noncomputable abbrev expUnitaryGroup
    (D : EssentialSelfAdjointSpectralData T) :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup H :=
  D.spectralTheorem.expUnitaryGroup

/-- Transport essential self-adjointness and its domain-aware spectral realization through a
unitary.  In particular, this proves that the self-adjoint closure commutes with unitary
conjugation as part of the resulting package. -/
noncomputable def unitaryConj
    (D : EssentialSelfAdjointSpectralData T)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') :
    EssentialSelfAdjointSpectralData (LinearPMap.unitaryConj u T) where
  essentiallySelfAdjoint := by
    change IsSelfAdjoint (LinearPMap.unitaryConj u T).closure
    rw [LinearPMap.IsClosable.unitaryConj_closure u T D.essentiallySelfAdjoint.isClosable]
    exact LinearPMap.unitaryConj_isSelfAdjoint u D.closure_isSelfAdjoint
  spectralMeasure := QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u
      D.spectralMeasure
  spectralTheorem := by
    rw [LinearPMap.IsClosable.unitaryConj_closure u T D.essentiallySelfAdjoint.isClosable]
    exact D.spectralTheorem.unitaryConj u

/-- The unitary group is transported by the same unitary as the spectral measure and the closure. -/
theorem expUnitaryGroup_unitaryConj
    (D : EssentialSelfAdjointSpectralData T)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') (t : ℝ) :
    (D.unitaryConj u).expUnitaryGroup t =
      QuantumMechanics.WOTSpectralMeasure.unitaryConj u (D.expUnitaryGroup t) := by
  change QuantumMechanics.WOTSpectralMeasure.expIntegral
      (QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u D.spectralMeasure) t = _
  exact QuantumMechanics.WOTSpectralMeasure.unitaryConj_expIntegral D.spectralMeasure u t

/-- The closure of an essentially self-adjoint core is transported by unitary conjugation. -/
theorem closure_unitaryConj
    (D : EssentialSelfAdjointSpectralData T)
    {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') :
    (LinearPMap.unitaryConj u T).closure = LinearPMap.unitaryConj u T.closure := by
  exact LinearPMap.IsClosable.unitaryConj_closure u T D.essentiallySelfAdjoint.isClosable

/-- If the spectral measure is invariant under a unitary on the same Hilbert space, then so is
the self-adjoint closure.  This is the operator-level form used by commutation arguments. -/
theorem closure_eq_of_spectralMeasure_invariant
    (D : EssentialSelfAdjointSpectralData T)
    (u : H ≃ₗᵢ[ℂ] H)
    (hμ : QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u D.spectralMeasure =
      D.spectralMeasure) :
    LinearPMap.unitaryConj u T.closure = T.closure := by
  have htransport := (D.spectralTheorem.unitaryConj u).maximal_eq
  rw [hμ] at htransport
  exact htransport.symm.trans D.spectralTheorem.maximal_eq

/-- Equality of all spectral projections is enough to establish invariance of the transported
spectral measure. -/
theorem spectralMeasure_invariant_of_projection_commute
    (D : EssentialSelfAdjointSpectralData T)
    (u : H ≃ₗᵢ[ℂ] H)
    (hproj : ∀ S : Set ℝ, MeasurableSet S →
      QuantumMechanics.WOTSpectralMeasure.unitaryConj u (D.spectralMeasure S) =
        D.spectralMeasure S) :
    QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u D.spectralMeasure =
      D.spectralMeasure := by
  rw [QuantumMechanics.WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  rw [QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure_apply]
  exact hproj S hS

/-- The common commutant-facing form: a unitary fixing every spectral projection fixes the
self-adjoint closure of the core. -/
theorem closure_eq_of_projection_commute
    (D : EssentialSelfAdjointSpectralData T)
    (u : H ≃ₗᵢ[ℂ] H)
    (hproj : ∀ S : Set ℝ, MeasurableSet S →
      QuantumMechanics.WOTSpectralMeasure.unitaryConj u (D.spectralMeasure S) =
        D.spectralMeasure S) :
    LinearPMap.unitaryConj u T.closure = T.closure := by
  exact D.closure_eq_of_spectralMeasure_invariant u
    (D.spectralMeasure_invariant_of_projection_commute u hproj)

/-- Commutation with all bounded Cayley spectral projections transports back to invariance of the
real spectral measure.  This is the spectral-data half of the commutant criterion, separated from
the closure and dynamics consequences below. -/
theorem spectralMeasure_invariant_of_cayley_projection_commute
    (D : EssentialSelfAdjointSpectralData T)
    (u : H ≃ₗᵢ[ℂ] H)
    (hcomm : ∀ S : Set ℂ, MeasurableSet S →
      Commute (u.toLinearIsometry.toContinuousLinearMap)
        (ContinuousLinearMapWOT.toCLM
          (QuantumMechanics.WOTSpectralMeasure.cayleyMap D.spectralMeasure S))) :
    QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u D.spectralMeasure =
      D.spectralMeasure := by
  apply QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure_eq_of_cayleyMap_eq
    D.spectralMeasure u
  rw [QuantumMechanics.WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  rw [QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure_apply]
  exact (QuantumMechanics.WOTSpectralMeasure.unitaryConj_eq_self_iff_commute u _).2
    (hcomm S hS)

/-- A Cayley-side commutation certificate fixes the self-adjoint closure.  This is the reusable
commutant-facing form: the bounded Cayley spectral projections are ordinary bounded operators,
while the conclusion is an equality of the unbounded closed operators. -/
theorem closure_eq_of_cayley_projection_commute
    (D : EssentialSelfAdjointSpectralData T)
    (u : H ≃ₗᵢ[ℂ] H)
    (hcomm : ∀ S : Set ℂ, MeasurableSet S →
      Commute (u.toLinearIsometry.toContinuousLinearMap)
        (ContinuousLinearMapWOT.toCLM
          (QuantumMechanics.WOTSpectralMeasure.cayleyMap D.spectralMeasure S))) :
    LinearPMap.unitaryConj u T.closure = T.closure := by
  apply D.closure_eq_of_spectralMeasure_invariant u
  exact D.spectralMeasure_invariant_of_cayley_projection_commute u hcomm

/-- The same Cayley-side commutation certificate fixes the entire bounded unitary group generated
by the self-adjoint closure. -/
theorem expUnitaryGroup_eq_of_cayley_projection_commute
    (D : EssentialSelfAdjointSpectralData T)
    (u : H ≃ₗᵢ[ℂ] H)
    (hcomm : ∀ S : Set ℂ, MeasurableSet S →
      Commute (u.toLinearIsometry.toContinuousLinearMap)
        (ContinuousLinearMapWOT.toCLM
          (QuantumMechanics.WOTSpectralMeasure.cayleyMap D.spectralMeasure S)))
    (t : ℝ) :
    QuantumMechanics.WOTSpectralMeasure.unitaryConj u (D.expUnitaryGroup t) =
      D.expUnitaryGroup t := by
  have hμ := D.spectralMeasure_invariant_of_cayley_projection_commute u hcomm
  have hgroup := D.expUnitaryGroup_unitaryConj u t
  change QuantumMechanics.WOTSpectralMeasure.expIntegral
      (QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u D.spectralMeasure) t = _
    at hgroup
  rw [hμ] at hgroup
  exact hgroup.symm

end EssentialSelfAdjointSpectralData

end OperatorAlgebra
