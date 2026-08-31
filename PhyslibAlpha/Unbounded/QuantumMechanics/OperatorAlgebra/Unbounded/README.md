# Unbounded operator theory

The folder layout follows the mathematical dependency graph.

| Folder | Current role |
| --- | --- |
| `Core` | domains, cores, closure, analytic vectors, essential self-adjointness |
| `Spectral` | Cayley transform, bounded spectral data, unbounded reconstruction |
| `Affiliation` | affiliated observables and concrete/abstract bridges |
| `Calculus` | measurable functional calculus and bounded transforms |
| `Representation` | normal representations and spectral-measure transport |
| `States` | normal states, density operators, distributions, POVMs |
| `Dynamics` | unitary groups and Stone/generator statements |
| `Examples` | optional ladder, Schwartz, and oscillator applications |
| `Tests` | compile-time API smoke tests |

## The central theorem chain

The reusable chain begins with a `LinearPMap` `T`.

* Analytic vectors and symmetry imply essential self-adjointness through
  `LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors`.
* `EssentialSelfAdjointCore` and `SelfAdjointClosureData` package the closure
  and its domain facts.
* `OperatorAlgebra.unboundedSpectralTheorem` constructs the spectral data from
  the Cayley-side bounded spectral theorem.
* `DomainAwareSelfAdjointSpectralTheorem` identifies the operator domain with
  the square-moment domain of the measure and reconstructs the operator as the
  maximal spectral integral.
* `expUnitaryGroup` gives the bounded unitary group associated to that same
  measure.  `expUnitaryGroup_zero`, `expUnitaryGroup_add`, and
  `expUnitaryGroup_continuous_apply` give its basic group and continuity laws;
  the `Dynamics` files add the generator statements.
* `AffiliationBridge` converts the Hilbert-space spectral measure to the
  projections of an abstract operator algebra.  The representation-level
  operator equality is supplied by
  `representedSelfAdjointOperator_eq_of_spectralTheorem`.

## Recommended integration order

An application should first define its operator and domain, then establish
symmetry, density, and essential self-adjointness.  Next it should consume the
domain-aware spectral theorem and only then add affiliation or measurable
functional calculus.  The state and representation modules are downstream of
the spectral-measure package.  `Examples` is not imported by the public
umbrella, so the general API cannot accidentally depend on the oscillator.
