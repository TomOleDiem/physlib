/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

-- Core/domain layer
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Core.AnalyticVector
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Core.ClosureAPI
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Core.Core
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Core.EssentialSelfAdjoint
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Core.InvariantCore
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Core.RealAnalytic

-- Cayley transform and bounded spectral layer
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.BoundedSelfAdjointData
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.UnitaryInfrastructure
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.Cayley
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.CayleyCertificate
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.CayleyInverse
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.CayleySpectralData
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.EigenvectorSpectralAtom
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.SpectralDecomposition

-- Affiliation and measurable calculus layer
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.Affiliated
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.SpectralTheorem
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.BoundedTransform
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.Concrete
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.ConcreteAffiliation
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.NormalAffiliated
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.NormalCanonical
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.NormalAffiliatedCayley
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.UnitaryCovariance
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Calculus.FunctionalCalculus
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Calculus.NormalBorelBounded
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Calculus.WeakStarCalculus

-- Representations and states
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Repr.NormalPVMTraceClass
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Repr.NormalRepresentation
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Repr.NormalBoundedOperators
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Repr.NormalFiniteDimensional
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Repr.Representation
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.States.DensityOperator
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.States.DensityQuadraticForm
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.States.DensityTraceBridge
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.States.DensityTraceState
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.States.Distribution
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.States.NormalState
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Measurement.NormalPVM
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Measurement.PVM
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Measurement.POVM

-- Dynamics
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Flow.NegativeStoneAPI
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Flow.Stone
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Flow.StoneAPI
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.PositiveIdeal
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.GeneralIdeal
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.PositiveTrace
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.HSAlgebra
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.TraceAlgebra
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.WStarAlgebra.FiniteDimensional
public import PhyslibAlpha.QuantumMechanics.Unbounded.Operators.SpectralTheory.SpectralIntegral
public import PhyslibAlpha.QuantumMechanics.Unbounded.Operators.SpectralTheory.Stone
public import PhyslibAlpha.QuantumMechanics.Unbounded.Operators.Multiplication.Spectral

/-!
# Public entry point for the general unbounded-operator theory

This module is the single import for the reusable unbounded spectral API.  It deliberately
contains no model-specific examples: a Hamiltonian only needs to supply a self-adjoint closure and
the corresponding spectral-resolution certificate, after which the affiliated, functional
calculus, Cayley, domain, and Stone APIs are available here.

The imports are grouped by role rather than by implementation file:

* `Concrete`, `Cayley`, and `CayleySpectralData` provide self-adjoint closure and the Cayley-side
  bounded spectral theorem;
* `UnboundedSpectralIntegral` provides the maximal square-moment integral and its domain-aware
  self-adjoint reconstruction;
* `Affiliated`, `FunctionalCalculus`, and `Representation` provide the abstract spectral-data and
  representation bridges;
* `NormalPVM` provides the normal-state σ-additivity contract needed for an honest
  infinite-dimensional von Neumann realization, separately from the stronger norm-valued `PVM`;
* `NormalAffiliated` provides the corresponding representation-free real and complex measurable
  spectral-data façades;
* `NormalBorelFunctionalCalculusBoundedOperators` supplies the certificate-free bounded-observable
  normal calculus for the concrete algebra `B(H)`;
* `NormalRepresentation` supplies the explicit normality bridge into weak-operator spectral data
  and the canonical represented maximal operator;
* `StoneAPI` exposes the exact generator-domain/differentiability interface for the resulting
  unitary group;
* `SpectralDecomposition`, `Distribution`, `EigenvectorSpectralAtom`, and `Stone` provide the
  downstream analysis API.
* `Operators.MultiplicationSpectral` exports the reusable maximal multiplication-operator and
  Fourier-momentum instances, including their exact domains, Cayley-side spectral measures,
  essential self-adjointness, and domain-aware spectral theorems.

No theorem in this entry point is an assumption: every imported declaration is checked by Lean in
its defining module.
-/

@[expose] public section
