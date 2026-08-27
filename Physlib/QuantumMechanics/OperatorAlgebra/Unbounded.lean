/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.Affiliated
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.AffiliationSpectralTheorem
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.BoundedUnitaryInfrastructure
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.BoundedSelfAdjointSpectralData
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.Cayley
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.CayleyCertificate
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.CayleyInverse
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.CayleySpectralData
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.Concrete
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.Core
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.ClosureAPI
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.DensityOperator
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.DensityOperatorQuadraticForm
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.DensityOperatorTraceBridge
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.DensityOperatorTraceState
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.Distribution
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.EigenvectorSpectralAtom
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.EssentialSelfAdjointCriteria
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.FunctionalCalculus
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.InvariantCore
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalState
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalStateRepresentation
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalPVM
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalAffiliated
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalAffiliatedCanonical
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalRepresentation
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalRepresentationBoundedOperators
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalPVMTraceClass
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalBorelFunctionalCalculusBoundedOperators
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalStateRepresentation
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalRepresentationFiniteDimensional
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NegativeStoneAPI
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.POVM
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.RealAnalytic
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.Representation
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.SpectralDecomposition
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.Stone
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.StoneAPI
public import Physlib.QuantumMechanics.OperatorAlgebra.TraceClass.PositiveIdeal
public import Physlib.QuantumMechanics.OperatorAlgebra.TraceClass.GeneralIdeal
public import Physlib.QuantumMechanics.OperatorAlgebra.TraceClass.PositiveTrace
public import Physlib.QuantumMechanics.OperatorAlgebra.TraceClass.HilbertSchmidtAlgebra
public import Physlib.QuantumMechanics.OperatorAlgebra.TraceClass.TraceAlgebra
public import Physlib.QuantumMechanics.OperatorAlgebra.WStarAlgebra.FiniteDimensional
public import Physlib.QuantumMechanics.Operators.SpectralTheory.UnboundedSpectralIntegral
public import Physlib.QuantumMechanics.Operators.SpectralTheory.Stone
public import Physlib.QuantumMechanics.Operators.MultiplicationSpectral

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
