/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

-- Core/domain layer
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Core.AnalyticVector
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Core.ClosureAPI
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Core.Core
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Core.EssentialSelfAdjoint
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Core.InvariantCore
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Core.RealAnalytic

-- Cayley transform and bounded spectral layer
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Spec.BoundedSelfAdjointData
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Spec.UnitaryInfrastructure
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Spec.Cayley
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Spec.CayleyCertificate
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Spec.CayleyInverse
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Spec.CayleySpectralData
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Spec.EigenvectorSpectralAtom
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Spec.SpectralDecomposition

-- Affiliation and measurable calculus layer
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Affil.Affiliated
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Affil.SpectralTheorem
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Affil.BoundedTransform
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Affil.Concrete
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Affil.ConcreteAffiliation
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Affil.NormalAffiliated
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Affil.NormalCanonical
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Affil.NormalAffiliatedCayley
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Affil.UnitaryCovariance
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Calculus.FunctionalCalculus
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Calculus.NormalBorelBounded
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Calculus.WeakStarCalculus

-- Representations and states
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Repr.NormalPVMTraceClass
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Repr.NormalRepresentation
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Repr.NormalBoundedOperators
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Repr.NormalFiniteDimensional
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Repr.Representation
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.DensityOperator
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.DensityQuadraticForm
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.DensityTraceBridge
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.DensityTraceState
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.Distribution
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.NormalState
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.NormalPVM
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.PVM
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.POVM

-- Dynamics
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Flow.NegativeStoneAPI
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Flow.Stone
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Flow.StoneAPI
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.PositiveIdeal
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.GeneralIdeal
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.PositiveTrace
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.HSAlgebra
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.TraceAlgebra
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.WStarAlgebra.FiniteDimensional
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.SpectralTheory.SpectralIntegral
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.SpectralTheory.Stone
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.Multiplication.Spectral

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
