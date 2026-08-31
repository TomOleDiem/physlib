/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Spectral.BoundedSelfAdjointSpectralData
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Representation.NormalPVMTraceClass

/-!
# The concrete bounded normal Borel calculus

The bounded self-adjoint spectral theorem and the trace-class normality theorem together give a
certificate-free `NormalObservableBorelCalculus` for the concrete algebra `B(H)`.  This is the
bounded entry point for applications: a bounded self-adjoint operator can be included in the
normal affiliated layer without supplying a separately chosen Borel-calculus witness.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra InnerProductSpace
open OperatorAlgebra
open MeasureTheory Set

namespace OperatorAlgebra

open BoundedOperatorsNormalRepresentation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The normal-functional real spectral measure of a bounded self-adjoint operator on `H`. -/
noncomputable def boundedObservableNormalPVM
    (a : Observable (B(H))) : NormalPVM ℝ (B(H)) :=
  wotSpectralMeasure_toNormalPVM_of_traceClass
    (boundedSelfAdjointSpectralMeasure (a : H →L[ℂ] H) a.property)

@[simp]
theorem boundedObservableNormalPVM_apply
    (a : Observable (B(H))) (S : Set ℝ) :
    boundedObservableNormalPVM a S =
      (boundedSelfAdjointSpectralMeasure (a : H →L[ℂ] H) a.property S).toCLM := rfl

/-- The canonical bounded Borel calculus attached to the bounded operator's normal PVM. -/
noncomputable def boundedObservableNormalCalculus
    (a : Observable (B(H))) :
    NormalBorelFunctionalCalculus (boundedObservableNormalPVM a) :=
  NormalBorelFunctionalCalculus.ofNormalPVM (boundedObservableNormalPVM a)

/-- `B(H)` has the canonical certificate-free normal Borel calculus for bounded observables. -/
noncomputable instance instNormalObservableBorelCalculusBoundedOperators :
    NormalObservableBorelCalculus (B(H)) where
  spectralMeasure := boundedObservableNormalPVM
  calculus := boundedObservableNormalCalculus
  spectralSupport := by
    intro a
    rcases exists_boundedSelfAdjointSpectralSupport
      (a : H →L[ℂ] H) a.property with ⟨C, hC⟩
    refine ⟨C, hC.1, ?_⟩
    intro S hS hdisj
    change (boundedSelfAdjointSpectralMeasure (a : H →L[ℂ] H) a.property S).toCLM = 0
    exact congrArg ContinuousLinearMapWOT.toCLM (hC.2 S hS hdisj)

example : NormalObservableBorelCalculus (B(H)) := inferInstance

/-! ### Recovery of the bounded operator -/

/-- The concrete identity representation used for bounded normal affiliation. -/
noncomputable def boundedObservableAffiliationBridge :
    NormalAffiliationBridge (A := B(H)) (H := H) :=
  (BoundedOperatorsNormalRepresentation.normalRepresentationAffiliationBridge (H :=
      H)).toNormalAffiliationBridge

/-- The normal spectral measure assigned to a bounded self-adjoint `B(H)` observable is represented
by the bounded self-adjoint spectral measure constructed from that operator. -/
theorem boundedObservable_representedSpectralMeasure
    (a : Observable (B(H))) :
    (boundedObservableAffiliationBridge (H := H)).representedSpectralMeasure
        (Observable.toNormalAffiliatedObservable a) =
      boundedSelfAdjointSpectralMeasure (a : H →L[ℂ] H) a.property := by
  rw [QuantumMechanics.WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  apply ContinuousLinearMapWOT.toCLM_injective
  rw [NormalAffiliationBridge.representedSpectralMeasure_apply]
  rw [ContinuousLinearMapWOT.ofCLM_toCLM]
  change (BoundedOperatorsNormalRepresentation.normalRepresentation (H := H)).representation
      (boundedObservableNormalPVM a S) =
    (boundedSelfAdjointSpectralMeasure (a : H →L[ℂ] H) a.property S).toCLM
  simp [boundedObservableNormalPVM,
    BoundedOperatorsNormalRepresentation.normalRepresentation_apply]

/-- The represented maximal unbounded realization of a bounded observable is its original bounded
operator, viewed as a full-domain `LinearPMap`.  This is the concrete recovery law for the
bounded-to-affiliated inclusion. -/
theorem boundedObservable_representedSelfAdjointOperator_eq
    (a : Observable (B(H))) :
    (boundedObservableAffiliationBridge (H := H)).representedSelfAdjointOperator
        (Observable.toNormalAffiliatedObservable a) =
      continuousLinearMapToPMap (a : H →L[ℂ] H) := by
  exact DomainAwareSelfAdjointSpectralTheorem.representedNormalSelfAdjointOperator_eq
    (boundedSelfAdjointDomainAwareSpectralTheorem (a : H →L[ℂ] H) a.property)
    (boundedObservableAffiliationBridge (H := H))
    (Observable.toNormalAffiliatedObservable a)
    (boundedObservable_representedSpectralMeasure a)

/-! ### Compatibility of the bounded Borel calculus -/

/-- The certificate-free normal Borel calculus on `B(H)` agrees with the concrete bounded WOT
spectral integral for every bounded measurable complex-valued function. -/
theorem boundedObservable_normalBoundedFC_eq_boundedIntegral
    (a : Observable (B(H))) {f : ℝ → ℂ} (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    Observable.normalBoundedFC a f hf hfb =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (boundedSelfAdjointSpectralMeasure (a : H →L[ℂ] H) a.property) f hf hfb).toCLM := by
  exact BoundedOperatorsNormalRepresentation.represented_boundedFC_eq_boundedIntegral
    (boundedObservableAffiliationBridge (H := H))
    (boundedObservableNormalPVM a) hf hfb

end OperatorAlgebra

end
