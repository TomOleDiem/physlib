/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded

/-!
# Public API smoke tests for the general unbounded theory

These declarations intentionally use only the public `Unbounded` entry point.  They are small
compile-time tests for the intended application workflow: a self-adjoint `LinearPMap` exposes its
exact spectral domain and both Stone sign conventions, while the concrete affiliation package
bundles the same operator without repeating a dependent self-adjointness proof.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The public spectral theorem exposes the exact square-moment domain directly. -/
theorem public_domain_eq_squareMoment (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    T.domain = spectralSquareMomentDomain (cayleyRealSpectralMeasure T hT) :=
  (unboundedSpectralTheorem T hT).domain_eq_squareMoment

/-- The positive Stone convention is available from the same public theorem object. -/
theorem public_expUnitaryGroup_zero (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    (unboundedSpectralTheorem T hT).expUnitaryGroup 0 = 1 :=
  (unboundedSpectralTheorem T hT).expUnitaryGroup_zero

/-- The public positive-sign group exposes its composition law. -/
theorem public_expUnitaryGroup_add (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (t s : ℝ) :
    (unboundedSpectralTheorem T hT).expUnitaryGroup (t + s) =
      (unboundedSpectralTheorem T hT).expUnitaryGroup t *
        (unboundedSpectralTheorem T hT).expUnitaryGroup s :=
  (unboundedSpectralTheorem T hT).expUnitaryGroup_add t s

/-- Every vector orbit of the positive-sign group is continuous. -/
theorem public_expUnitaryGroup_continuous_apply (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    Continuous (fun t : ℝ => (unboundedSpectralTheorem T hT).expUnitaryGroup t x) :=
  (unboundedSpectralTheorem T hT).expUnitaryGroup_continuous_apply x

/-- The conventional quantum-mechanical negative-sign group is also public. -/
theorem public_negativeExpUnitaryGroup_zero (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    (unboundedSpectralTheorem T hT).negativeExpUnitaryGroup 0 = 1 :=
  (unboundedSpectralTheorem T hT).negativeExpUnitaryGroup_zero

/-- The conventional negative-sign group has the same public group-law interface. -/
theorem public_negativeExpUnitaryGroup_add (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (t s : ℝ) :
    (unboundedSpectralTheorem T hT).negativeExpUnitaryGroup (t + s) =
      (unboundedSpectralTheorem T hT).negativeExpUnitaryGroup t *
        (unboundedSpectralTheorem T hT).negativeExpUnitaryGroup s :=
  (unboundedSpectralTheorem T hT).negativeExpUnitaryGroup_add t s

/-- The negative-sign quantum orbit is continuous on every vector as well. -/
theorem public_negativeExpUnitaryGroup_continuous_apply
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    Continuous (fun t : ℝ => (unboundedSpectralTheorem T hT).negativeExpUnitaryGroup t x) :=
  (unboundedSpectralTheorem T hT).negativeExpUnitaryGroup_continuous_apply x

/- The abstract bounded transform is part of the public entry point as well. -/
theorem public_boundedTransform_isSelfAdjoint
    {A : Type*} [OperatorAlgebra A] (T : AffiliatedObservable A) :
    IsSelfAdjoint T.boundedTransform :=
  T.boundedTransform_isSelfAdjoint

theorem public_boundedTransform_norm_le_one
    {A : Type*} [OperatorAlgebra A] (T : AffiliatedObservable A) :
    ‖T.boundedTransform‖ ≤ 1 :=
  T.norm_boundedTransform_le_one

theorem public_negativeExpUnitaryGroup_generator_domain
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    (∃ y : H, HasDerivAt
      (fun t : ℝ => (unboundedSpectralTheorem T hT).negativeExpUnitaryGroup t x) y 0) ↔
      x ∈ T.domain :=
  ((unboundedSpectralTheorem T hT).mem_domain_iff_negativeExpUnitaryGroup_hasDerivAt x 0).symm

theorem public_negativeExpUnitaryGroup_hasDerivAt_iff
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x y : H) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (unboundedSpectralTheorem T hT).negativeExpUnitaryGroup t x) y s ↔
      ∃ hx : x ∈ T.domain,
        y = (unboundedSpectralTheorem T hT).negativeExpUnitaryGroup s
          (-Complex.I • T ⟨x, hx⟩) :=
  (unboundedSpectralTheorem T hT).negativeExpUnitaryGroup_hasDerivAt_iff x y s

/-- Differentiability at time zero detects exactly the self-adjoint operator domain. -/
theorem public_expUnitaryGroup_generator_domain (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    (∃ y : H, HasDerivAt
      (fun t : ℝ => (unboundedSpectralTheorem T hT).expUnitaryGroup t x) y 0) ↔
      x ∈ T.domain :=
  ((unboundedSpectralTheorem T hT).mem_domain_iff_expUnitaryGroup_hasDerivAt x 0).symm

/-- At arbitrary time, the derivative of an orbit is the evolved generator vector. -/
theorem public_expUnitaryGroup_hasDerivAt_iff
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x y : H) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (unboundedSpectralTheorem T hT).expUnitaryGroup t x) y s ↔
      ∃ hx : x ∈ T.domain,
        y = (unboundedSpectralTheorem T hT).expUnitaryGroup s (Complex.I • T ⟨x, hx⟩) :=
  (unboundedSpectralTheorem T hT).expUnitaryGroup_hasDerivAt_iff x y s

/-- Every concrete self-adjoint operator can be bundled as affiliated to `B(H)`. -/
noncomputable def public_full_affiliation (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    VonNeumannAlgebra.AffiliatedSelfAdjointOperator
      (VonNeumannAlgebra.full (H := H)) :=
  VonNeumannAlgebra.fullAffiliatedSelfAdjointOperator T hT

@[simp]
theorem public_full_affiliation_operator (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    (public_full_affiliation T hT).operator = T := rfl

/-- The affiliation bundle can be transported into a larger concrete von Neumann algebra. -/
@[simp]
theorem public_affiliation_mono_operator {M N : VonNeumannAlgebra H}
    (hMN : M ≤ N) (T : VonNeumannAlgebra.AffiliatedSelfAdjointOperator M) :
    (T.mono hMN).operator = T.operator :=
  T.mono_operator hMN

/-- The bundled API exposes commutation of every real spectral projection with the commutant. -/
theorem public_affiliation_real_projection_commutes
    {M : VonNeumannAlgebra H}
    (T : VonNeumannAlgebra.AffiliatedSelfAdjointOperator M)
    (S : Set ℝ) (hS : MeasurableSet S) {y : H →L[ℂ] H} (hy : y ∈ M.commutant) :
    Commute y (ContinuousLinearMapWOT.toCLM
      (cayleyRealSpectralMeasure T.operator T.isSelfAdjoint S)) :=
  T.realSpectralProjection_commutes_commutant S hS hy

/-! The model-facing handoff from an essentially self-adjoint core to the concrete affiliation
bundle is available through the same public import. -/
noncomputable def public_affiliated_core
    {M : VonNeumannAlgebra H} (C : EssentialSelfAdjointCore (H := H))
    (hAff : VonNeumannAlgebra.IsAffiliated M C.closure C.closure_isSelfAdjoint) :
    VonNeumannAlgebra.AffiliatedSelfAdjointOperator M :=
  VonNeumannAlgebra.AffiliatedSelfAdjointOperator.ofEssentialSelfAdjointCore C hAff

@[simp]
theorem public_affiliated_core_operator
    {M : VonNeumannAlgebra H} (C : EssentialSelfAdjointCore (H := H))
    (hAff : VonNeumannAlgebra.IsAffiliated M C.closure C.closure_isSelfAdjoint) :
    (public_affiliated_core C hAff).operator = C.closure := rfl

theorem public_affiliated_core_domain
    {M : VonNeumannAlgebra H} (C : EssentialSelfAdjointCore (H := H))
    (hAff : VonNeumannAlgebra.IsAffiliated M C.closure C.closure_isSelfAdjoint) :
    (public_affiliated_core C hAff).operator.domain =
      spectralSquareMomentDomain
        (cayleyRealSpectralMeasure C.closure C.closure_isSelfAdjoint) := by
  exact (public_affiliated_core C hAff).domain_eq_squareMoment

noncomputable def public_affiliated_core_of_real_commutant
    {M : VonNeumannAlgebra H} (C : EssentialSelfAdjointCore (H := H))
    (hcomm : ∀ S : Set ℝ, MeasurableSet S → ∀ y ∈ M.commutant,
      Commute y (ContinuousLinearMapWOT.toCLM
        (cayleyRealSpectralMeasure C.closure C.closure_isSelfAdjoint S))) :
    VonNeumannAlgebra.AffiliatedSelfAdjointOperator M :=
  VonNeumannAlgebra.AffiliatedSelfAdjointOperator.ofEssentialSelfAdjointCore_of_realSpectralProjection_commutes_commutant
    C hcomm

@[simp]
theorem public_affiliated_core_of_real_commutant_operator
    {M : VonNeumannAlgebra H} (C : EssentialSelfAdjointCore (H := H))
    (hcomm : ∀ S : Set ℝ, MeasurableSet S → ∀ y ∈ M.commutant,
      Commute y (ContinuousLinearMapWOT.toCLM
        (cayleyRealSpectralMeasure C.closure C.closure_isSelfAdjoint S))) :
    (public_affiliated_core_of_real_commutant C hcomm).operator = C.closure := rfl

noncomputable def public_affiliated_core_of_real_membership
    {M : VonNeumannAlgebra H} (C : EssentialSelfAdjointCore (H := H))
    (hmem : ∀ S : Set ℝ, MeasurableSet S →
      ContinuousLinearMapWOT.toCLM
        (cayleyRealSpectralMeasure C.closure C.closure_isSelfAdjoint S) ∈ M) :
    VonNeumannAlgebra.AffiliatedSelfAdjointOperator M :=
  VonNeumannAlgebra.AffiliatedSelfAdjointOperator.ofEssentialSelfAdjointCore_of_realSpectralProjection_mem
    C hmem

@[simp]
theorem public_affiliated_core_of_real_membership_operator
    {M : VonNeumannAlgebra H} (C : EssentialSelfAdjointCore (H := H))
    (hmem : ∀ S : Set ℝ, MeasurableSet S →
      ContinuousLinearMapWOT.toCLM
        (cayleyRealSpectralMeasure C.closure C.closure_isSelfAdjoint S) ∈ M) :
    (public_affiliated_core_of_real_membership C hmem).operator = C.closure := rfl

end OperatorAlgebra

end

/- These checks are intentionally kept at the public-import boundary.  In particular, they make a
   hidden `sorryAx` in the central theorem chain visible during an audit even when the source scan
   itself is clean. -/
#print axioms OperatorAlgebra.unboundedSpectralTheorem
#print axioms LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors
#print axioms OperatorAlgebra.NormalAffiliationBridge.representedSelfAdjointOperator_eq_of_spectralTheorem
