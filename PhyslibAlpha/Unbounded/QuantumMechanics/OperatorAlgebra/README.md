# Quantum-mechanical operator algebra

This directory contains the reusable operator-algebra layer.  It is separate
from model-specific work in `QuantumMechanics/Qubit` and from the harmonic
oscillator examples.  The public entry point for the unbounded theory is
`PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded`.

## What is proved here

The current API has the following verified pieces.

* `OperatorAlgebra.Basic` defines the abstract bounded observable algebra,
  projections, and bounded observables.
* `OperatorAlgebra.WStarAlgebra` and its submodules provide the weak-star
  algebra interface and the concrete infinite-dimensional infrastructure.
* `OperatorAlgebra.TraceClass` and its submodules provide trace-class ideals,
  products, positivity, rank-one operators, the trace pairing, and the
  Hilbert--Schmidt estimates used by normality arguments.
* `Unbounded.Core` defines partial linear maps with explicit domains, invariant
  cores, analytic vectors, and essential-self-adjointness certificates.
* `Unbounded.Spectral` proves the Cayley transform and inverse constructions,
  their round trips, bounded spectral data, and the unbounded reconstruction
  interface.
* `Unbounded.Affiliation` defines representation-free affiliated observables
  and the concrete bridge from spectral data on a Hilbert space to an abstract
  operator algebra.
* `Unbounded.Calculus` provides the bounded measurable functional-calculus
  layer, including the real and complex canonical laws that are currently
  available.
* `States` provides states, normal states, density operators, and state
  distributions. `Measurement` provides the general PVM/POVM interfaces and
  their finite-outcome specialization.
* `Unbounded.Dynamics` provides the unitary group, continuity, and generator
  domain/differentiability statements obtained from the same spectral data.
* `Dynamics` contains the bounded reversible and irreversible layer: automorphism
  groups, norm-continuous quantum dynamical semigroups, and the general
  Christensen--Evans/Lindblad theorem on `B(H)`.  Its CP/Stinespring files are
  development sources here and are not imported by the upstream-facing `qubit`
  checkout.

These are theorem and structure names, not a list of intended future work.
The source is the authority for the precise hypotheses and conclusions.

## How the unbounded pipeline fits together

For a densely defined symmetric operator `T`, the intended application order
is:

1. Package `T` as a `LinearPMap` and provide its explicit domain.
2. Prove density and essential self-adjointness.  The reusable analytic-vector
   theorem is
   `LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors`.
3. Obtain the self-adjoint closure using the closure API in
   `Unbounded.Core.ClosureAPI`.
4. Apply
   `OperatorAlgebra.unboundedSpectralTheorem` or
   `OperatorAlgebra.unboundedSpectralTheorem_of_essentiallySelfAdjoint`.
   The result uses the Cayley transform to supply the real WOT spectral
   measure and the maximal square-moment integral.
5. Use `DomainAwareSelfAdjointSpectralTheorem` and its fields/theorems to
   identify the closure domain with the square-moment domain and to recover
   the operator from its spectral integral.
6. Define the unitary evolution with `expUnitaryGroup`; use the theorems in
   `Unbounded.Dynamics` for the group law, continuity, and generator domain.
7. If an abstract algebra element is needed, use the affiliation bridge in
   `Unbounded.Affiliation`.  The packaged equality is
   `representedSelfAdjointOperator_eq_of_spectralTheorem`.

The key point is that the spectral measure, domain, reconstruction, and
unitary group all come from one spectral-data package.  No oscillator-specific
completeness theorem is used by this general pipeline.

## Definitions to integrate first in a new application

The first definitions worth importing are:

* `LinearPMap` and `LinearPMap.IsSymmetric` for the operator and its domain;
* `EssentialSelfAdjointCore` when the application naturally starts from a
  core and a closure certificate;
* `SelfAdjointClosureData` when the closure is already available;
* `SelfAdjointSpectralData` or
  `EssentialSelfAdjointSpectralData` for the spectral package;
* `DomainAwareSelfAdjointSpectralTheorem` for the exact domain statement;
* `ConcreteAffiliatedObservable` for a Hilbert-space spectral measure;
* `AffiliationBridge` and `RepresentedAffiliatedObservable` only when the
  result must be exported into an abstract operator algebra;
* `NormalAffiliatedObservable` and the normal representation modules when
  measurable Borel functions or weak-star normality are part of the use case.

For a first integration, import only
`OperatorAlgebra.Unbounded` and construct the smallest package above.  The
individual folders exist for implementation and dependency control; consumers
should normally not depend on their internal import order.

## Scope boundary

This directory documents the general theory that is present in the source.
Hermite-function completeness, the oscillator's explicit eigenbasis, and
qubit-specific constructions are applications and are intentionally not
presented as prerequisites or as general theorems here.  The comparison with
the selected master ref is recorded in `master-delta.md`.
