/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.BoundedSelfAdjointSpectralData
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalPVMTraceClass

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

end OperatorAlgebra

end
