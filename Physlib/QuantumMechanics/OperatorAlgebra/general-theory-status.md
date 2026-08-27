# Unbounded spectral theory: live status

Status audit: 2026-08-27.

This is the result of a source sweep and build audit. “Finished” below means
that the declaration is implemented and checked by Lean; it does not mean
that every possible textbook formulation has been formalized.

## Verified finished

- `Operators/SpectralTheory/UnboundedSpectralIntegral.lean` constructs the
  maximal real spectral integral from an arbitrary real WOT spectral measure.
  Its domain is the explicit square-moment domain, and the operator is proved
  self-adjoint. The reverse-domain theorem identifies any self-adjoint
  realization with this maximal integral.
- `Cayley.lean`, `CayleyInverse.lean`, and `CayleySpectralData.lean` prove
  the Cayley construction, inverse construction, round trips, real spectral
  measure, and domain-aware reconstruction.
- `ClosureAPI.lean` packages an essentially self-adjoint `LinearPMap` into
  its canonical graph closure, self-adjointness, uniqueness, spectral measure,
  exact domain equality, resolvents, and Stone unitary group.
- `Operators/SpectralTheory/Stone.lean` and `Unbounded/StoneAPI.lean` prove
  strong continuity, the group laws, and the exact generator/domain
  differentiability statements, including the `-iT` convention.
- Bounded measurable functional calculus, measurable real/complex pushforwards,
  indicators, resolvents, and exponentials are implemented for the normal-PVM
  façade. `NormalRepresentation.lean` now also proves
  `NormalAffiliationBridge.representedResolvent_apply`, identifying the
  represented bounded resolvent with `LinearPMap.resolvent` of the represented
  maximal operator.
- The trace-class, completed predual, density-operator state, and concrete
  `B(H)` normal-PVM conversion are implemented. The concrete bounded-observable
  normal Borel calculus is available through
  `NormalBorelFunctionalCalculusBoundedOperators.lean`.
- `HarmonicOscillator/DifferentialCore.lean` proves the actual one-dimensional
  Schwartz differential Hamiltonian is essentially self-adjoint. It proves
  the Hermite eigenfunction calculation and uses the proved Hermite-basis
  density theorem; it then exposes the canonical closure, its spectral measure,
  maximal-integral equality, domain equality, and unitary evolution.

## What is not yet the full textbook theory

1. The abstract `AffiliatedObservable` façade is the older norm-valued PVM
   layer. A bare C*-algebra does not automatically contain all Borel spectral
   projections, so its `BorelFunctionalCalculus` and `AffiliationBridge` inputs
   remain explicit. The newer `NormalAffiliatedObservable`/`NormalPVM` layer
   handles the normal-functional version, but a general von Neumann-algebra
   representation still has to supply (or prove) normality of its matrix
   coefficients. The `B(H)` instance is the concrete completed-trace-class
   exception to that boundary.
2. The full equivalence between representation-free affiliation and the
   bounded-transform/commutant definition of affiliation is not present.
   The represented maximal operator and all its spectral/dynamical consequences
   are present once the normal representation bridge is supplied.
3. `StronglyCommutes.of_commonCore_comm_certificate` deliberately consumes a
   supplied strong-commutation conclusion. It is an interface for a future
   Nelson analytic-vector theorem, not a proof of Nelson’s theorem.
4. The older `HarmonicOscillator/EssentialSelfAdjointness.lean` still exposes
   a conditional deficiency-certificate route. That is not needed for the
   actual differential result in `DifferentialCore.lean`, but it remains a
   supported compatibility API. The separate `LadderOperators.lean` and a few
   oscillator `Basic.lean` items contain TODO documentation for future algebraic
   and higher-dimensional work; these are not proof holes.
5. The differential oscillator closure is canonical and fully usable, but the
   project does not yet define a separately named, independently characterized
   “intended maximal differential Hamiltonian” and prove equality to it. The
   current closure itself is the self-adjoint realization used by the spectral
   API.
6. Some spectral decomposition terminology is intentionally topological rather
   than the strongest finite-multiplicity textbook notion. The finite-rank and
   trace formulas that are available are proved, but this does not by itself
   formalize every general essential-spectrum theorem.

## Evidence

The following commands succeed in the live tree:

```text
lake env lake build Physlib.QuantumMechanics.OperatorAlgebra.Unbounded
lake env lake build Physlib
```

The scoped declaration scan over
`QuantumMechanics/OperatorAlgebra`, `Operators/SpectralTheory`, and
`HarmonicOscillator` finds no source-level `sorry`, `admit`, `sorryAx`, or
`axiom` declarations. `#print axioms` on the principal spectral, closure,
oscillator, resolvent, and trace-class constructors reports only Lean's normal
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`).

This does not make the entire Physlib repository sorry-free. The repository
still has unrelated source holes in the pendulum/rigid-body, relativity, QFT,
and archived qubit backup areas. They are outside this unbounded-operator
scope and were not altered by this audit.
