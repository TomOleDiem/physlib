/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Core.ClosureAPI
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Representation.NormalRepresentation
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Representation.NormalRepresentationBoundedOperators
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Affiliation.NormalAffiliatedCanonical

/-!
# The affiliation/spectral-theorem hand-off

This module contains the small theorem package that connects the two sides of the theory:

* an affiliated observable supplies a represented weak spectral measure;
* the unbounded spectral theorem supplies the maximal square-moment realization of that measure;
* a model-specific self-adjoint closure can therefore be identified with that realization.

The point is not to hide analytic hypotheses.  A model still has to provide a
`DomainAwareSelfAdjointSpectralTheorem` (or an `EssentialSelfAdjointCore`, whose Cayley spectral
theorem is canonical).  Once it does, these lemmas turn the representation-level spectral data
into the actual operator equality normally used in applications.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {A H : Type*} [WStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace NormalAffiliationBridge

variable (bridge : NormalAffiliationBridge (A := A) (H := H))

/-! ### Equality with an arbitrary domain-aware realization -/

/-- The represented maximal realization is the operator in any domain-aware spectral theorem for
the represented spectral measure.  This is the packaged unbounded operator equality at the
affiliation boundary. -/
theorem representedSelfAdjointOperator_eq_of_spectralTheorem
    (T : NormalAffiliatedObservable A)
    {S : H →ₗ.[ℂ] H}
    (D : DomainAwareSelfAdjointSpectralTheorem S (bridge.representedSpectralMeasure T)) :
    bridge.representedSelfAdjointOperator T = S := by
  change QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
      (bridge.representedSpectralMeasure T) = S
  exact D.maximal_eq

/-! ### Equality with a self-adjoint closure -/

/-- If an affiliated observable has the Cayley spectral measure of an essentially self-adjoint
core as its represented measure, its represented maximal operator is exactly the canonical
self-adjoint closure of that core. -/
theorem representedSelfAdjointOperator_eq_closure
    (T : NormalAffiliatedObservable A)
    (C : EssentialSelfAdjointCore (H := H))
    (hmeasure : bridge.representedSpectralMeasure T = C.spectralMeasure) :
    bridge.representedSelfAdjointOperator T = C.closure := by
  change QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
      (bridge.representedSpectralMeasure T) = C.closure
  rw [hmeasure]
  exact C.spectralTheorem.maximal_eq

theorem representedSelfAdjointOperator_domain_eq_closure_domain
    (T : NormalAffiliatedObservable A)
    (C : EssentialSelfAdjointCore (H := H))
    (hmeasure : bridge.representedSpectralMeasure T = C.spectralMeasure) :
    (bridge.representedSelfAdjointOperator T).domain = C.closure.domain := by
  rw [bridge.representedSelfAdjointOperator_eq_closure T C hmeasure]

/-! ### Core and uniqueness consequences -/

/-- The model core is contained in the represented affiliated operator. -/
theorem core_le_representedSelfAdjointOperator
    (T : NormalAffiliatedObservable A)
    (C : EssentialSelfAdjointCore (H := H))
    (hmeasure : bridge.representedSpectralMeasure T = C.spectralMeasure) :
    C.operator ≤ bridge.representedSelfAdjointOperator T := by
  rw [bridge.representedSelfAdjointOperator_eq_closure T C hmeasure]
  exact C.le_closure

/-- Any self-adjoint realization extending the core agrees with the represented affiliated
operator.  This is the form used when a model identifies its closure indirectly. -/
theorem selfAdjoint_eq_representedSelfAdjointOperator_of_core_le
    (T : NormalAffiliatedObservable A)
    (C : EssentialSelfAdjointCore (H := H))
    (hmeasure : bridge.representedSpectralMeasure T = C.spectralMeasure)
    {S : H →ₗ.[ℂ] H} (hCS : C.operator ≤ S) (hS : IsSelfAdjoint S) :
    S = bridge.representedSelfAdjointOperator T := by
  rw [bridge.representedSelfAdjointOperator_eq_closure T C hmeasure]
  exact C.unique_selfAdjoint_extension hCS hS

/-! ### Canonical represented bounded dynamics -/

/-- The canonical abstract exponential of a normal affiliated observable is represented by the
corresponding concrete spectral exponential.  The normal bridge supplies the representation of
the canonical bounded Borel calculus automatically. -/
theorem representation_canonicalExpUnitary
    (T : NormalAffiliatedObservable A) (t : ℝ) :
    bridge.representation ((T.canonicalExpUnitary t : unitary A) : A) =
      (QuantumMechanics.WOTSpectralMeasure.expIntegral
        (bridge.representedSpectralMeasure T) t).toCLM := by
  change bridge.representation
      ((NormalBorelFunctionalCalculus.ofNormalPVM T.spectralMeasure).boundedFC
        (AffiliatedObservable.expFunction t)
        (AffiliatedObservable.expFunction_measurable t)
        (AffiliatedObservable.expFunction_bounded t)) = _
  exact BoundedOperatorsNormalRepresentation.represented_boundedFC_eq_boundedIntegral
    bridge T.spectralMeasure _ _

/-- The canonical algebra-level `exp (-i t T)` is represented by the corresponding negative-time
concrete spectral exponential. -/
theorem representation_canonicalNegativeExpUnitary
    (T : NormalAffiliatedObservable A) (t : ℝ) :
    bridge.representation ((T.canonicalNegativeExpUnitary t : unitary A) : A) =
      (QuantumMechanics.WOTSpectralMeasure.expIntegral
        (bridge.representedSpectralMeasure T) (-t)).toCLM := by
  change bridge.representation
      ((NormalBorelFunctionalCalculus.ofNormalPVM T.spectralMeasure).boundedFC
        (AffiliatedObservable.expFunction (-t))
        (AffiliatedObservable.expFunction_measurable (-t))
        (AffiliatedObservable.expFunction_bounded (-t))) = _
  exact BoundedOperatorsNormalRepresentation.represented_boundedFC_eq_boundedIntegral
    bridge T.spectralMeasure _ _

/-- The canonical abstract resolvent is represented by the concrete bounded resolvent spectral
integral. -/
theorem representation_canonicalResolvent
    (T : NormalAffiliatedObservable A) (z : ℂ) (hz : z.im ≠ 0) :
    bridge.representation (T.canonicalResolvent z hz) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.representedSpectralMeasure T)
        (AffiliatedObservable.resolventFunction z)
        (AffiliatedObservable.resolventFunction_measurable z)
        (AffiliatedObservable.resolventFunction_bounded z hz)).toCLM := by
  change bridge.representation
      ((NormalBorelFunctionalCalculus.ofNormalPVM T.spectralMeasure).boundedFC
        (AffiliatedObservable.resolventFunction z)
        (AffiliatedObservable.resolventFunction_measurable z)
        (AffiliatedObservable.resolventFunction_bounded z hz)) = _
  exact BoundedOperatorsNormalRepresentation.represented_boundedFC_eq_boundedIntegral
    bridge T.spectralMeasure _ _

end NormalAffiliationBridge

/-! ### Direct canonical bounded-calculus compatibility -/

namespace NormalOperatorAffiliationBridge

variable (bridge : NormalOperatorAffiliationBridge (A := A) (H := H))

/-- The canonical bounded Borel calculus of a real normal affiliated observable is represented by
the corresponding real WOT spectral integral.  This direct façade avoids making callers unfold
`canonicalBorelCalculus` or use the more general witness package. -/
theorem representation_canonicalBoundedFC
    (T : NormalAffiliatedObservable A) (f : ℝ → ℂ)
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    bridge.representation (T.canonicalBoundedFC f hf hfb) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toNormalAffiliationBridge.representedSpectralMeasure T) f hf hfb).toCLM := by
  change bridge.toNormalAffiliationBridge.representation
      ((NormalBorelFunctionalCalculus.ofNormalPVM T.spectralMeasure).boundedFC f hf hfb) = _
  exact BoundedOperatorsNormalRepresentation.represented_boundedFC_eq_boundedIntegral
    bridge.toNormalAffiliationBridge T.spectralMeasure hf hfb

/-- The canonical bounded Borel calculus of a complex normal affiliated operator is represented by
its complex WOT spectral integral. -/
theorem representation_canonicalBoundedFCComplex
    (T : NormalAffiliatedOperator A) (f : ℂ → ℂ)
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    bridge.representation (T.canonicalBoundedFC f hf hfb) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.representedSpectralMeasure T) f hf hfb).toCLM := by
  change bridge.representation
      ((NormalBorelFunctionalCalculus.ofNormalPVM T.spectralMeasure).boundedFC f hf hfb) = _
  exact BoundedOperatorsNormalRepresentation.represented_boundedFCComplex_eq_boundedIntegral
    bridge T.spectralMeasure hf hfb

end NormalOperatorAffiliationBridge

/-! ### One-step façade for normal representations -/

namespace NormalRepresentation

variable (π : NormalRepresentation (A := A) (H := H))

/- The representation itself now constructs the normal affiliation bridge.  These theorems are
  deliberately thin façades over `NormalAffiliationBridge`: they keep model files from having to
  name that intermediate structure when identifying a concrete closure. -/

/-- A normal representation identifies the represented maximal affiliated realization with the
canonical closure of an essentially self-adjoint core once their WOT spectral measures agree. -/
theorem representedSelfAdjointOperator_eq_closure
    (T : NormalAffiliatedObservable A)
    (C : EssentialSelfAdjointCore (H := H))
    (hmeasure :
      π.toNormalAffiliationBridge.representedSpectralMeasure T = C.spectralMeasure) :
    π.toNormalAffiliationBridge.representedSelfAdjointOperator T = C.closure := by
  exact π.toNormalAffiliationBridge.representedSelfAdjointOperator_eq_closure T C hmeasure

/-- The domain of the represented affiliated realization is the closure domain of the core. -/
theorem representedSelfAdjointOperator_domain_eq_closure_domain
    (T : NormalAffiliatedObservable A)
    (C : EssentialSelfAdjointCore (H := H))
    (hmeasure :
      π.toNormalAffiliationBridge.representedSpectralMeasure T = C.spectralMeasure) :
    (π.toNormalAffiliationBridge.representedSelfAdjointOperator T).domain = C.closure.domain := by
  rw [π.representedSelfAdjointOperator_eq_closure T C hmeasure]

/-- The original core operator is contained in the represented affiliated realization. -/
theorem core_le_representedSelfAdjointOperator
    (T : NormalAffiliatedObservable A)
    (C : EssentialSelfAdjointCore (H := H))
    (hmeasure :
      π.toNormalAffiliationBridge.representedSpectralMeasure T = C.spectralMeasure) :
    C.operator ≤ π.toNormalAffiliationBridge.representedSelfAdjointOperator T := by
  rw [π.representedSelfAdjointOperator_eq_closure T C hmeasure]
  exact C.le_closure

/-- The represented Stone orbit has the expected generator on the closure domain. -/
theorem representedExpUnitaryGroup_hasDerivAt_zero
    (T : NormalAffiliatedObservable A)
    (C : EssentialSelfAdjointCore (H := H))
    (hmeasure :
      π.toNormalAffiliationBridge.representedSpectralMeasure T = C.spectralMeasure)
    (x : C.closure.domain) :
    HasDerivAt
      (fun t : ℝ => π.toNormalAffiliationBridge.expUnitaryGroup T t (x : H))
      (Complex.I • C.closure x) 0 := by
  change HasDerivAt
    (fun t : ℝ => QuantumMechanics.WOTSpectralMeasure.expIntegral
      (π.toNormalAffiliationBridge.representedSpectralMeasure T) t (x : H))
    (Complex.I • C.closure x) 0
  rw [hmeasure]
  exact C.spectralTheorem.expUnitaryGroup_hasDerivAt_zero x

/-- The represented conventional quantum-evolution orbit has generator `-i • closure` on the
closure domain. -/
theorem representedNegativeExpUnitaryGroup_hasDerivAt_zero
    (T : NormalAffiliatedObservable A)
    (C : EssentialSelfAdjointCore (H := H))
    (hmeasure :
      π.toNormalAffiliationBridge.representedSpectralMeasure T = C.spectralMeasure)
    (x : C.closure.domain) :
    HasDerivAt
      (fun t : ℝ => π.toNormalAffiliationBridge.negativeExpUnitaryGroup T t (x : H))
      (-Complex.I • C.closure x) 0 := by
  change HasDerivAt
    (fun t : ℝ => QuantumMechanics.WOTSpectralMeasure.expIntegral
      (π.toNormalAffiliationBridge.representedSpectralMeasure T) (-t) (x : H))
    (-Complex.I • C.closure x) 0
  rw [hmeasure]
  exact C.spectralTheorem.negativeExpUnitaryGroup_hasDerivAt_zero x

end NormalRepresentation

end OperatorAlgebra

end
