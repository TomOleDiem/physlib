# Unbounded spectral theorem roadmap

The current foundational job is the following chain for a densely-defined operator
`T : H →ₗ.[ℂ] H` (in particular, the oscillator Hamiltonian on `L²(ℝ)`):

```text
essential self-adjointness → self-adjoint closure → unbounded spectral theorem
```

## Current implementation boundary

The concrete implementation currently handles maximal real multiplication operators
and their unitary conjugates. In particular, Fourier conjugation gives the maximal
momentum realization as multiplication by `2πℏ pᵢ`; identifying it with the original
Schwartz-core differential operator is a separate core/closure theorem.

This is not yet an automatic theorem for an arbitrary unbounded symmetric operator.
Such an operator can use the representation-level interface below only after a
source-specific spectral construction (or a unitary equivalence to multiplication)
has been supplied.

## 1. Essential self-adjointness

For a symmetric core operator `T`, prove

```text
T.IsEssentiallySelfAdjoint
```

using a genuine analytic criterion. The existing operator layer already contains the
definition and the von Neumann defect-number criterion. Maximal multiplication
operators already have this result; the oscillator's differential core still needs its
concrete dense-domain, symmetry, and vanishing-deficiency proofs.

## 2. Self-adjoint closure

Once essential self-adjointness is available, use the canonical graph closure
`T.closure` and prove:

* `T.closure` is self-adjoint;
* `T ≤ T.closure`;
* `T.closure` is the unique self-adjoint extension of `T`;
* the closure has the same resolvent domain as `T`.

These facts are now exposed through the concrete closure-data API in
`OperatorAlgebra.Unbounded.Concrete`.

## 3. Unbounded spectral theorem

The Cayley layer now proves the reusable analytic part: a self-adjoint partial linear map has a
full-domain bounded Cayley extension, that extension is an actual unitary linear isometry
equivalence, and its scalar Cayley pullback is an exact inverse whenever the bounded measure is
supported on the unit circle away from `1`.  The bounded-unitary spectral measure is now genuinely
constructed in `Unbounded/BoundedUnitaryInfrastructure.lean` as `cfcSpectralMeasure`; the Cayley
adapter packages it as `cayleyBoundedSpectralMeasure`.

For a self-adjoint closed operator `A`, construct a weak-operator projection-valued
measure

```text
E : WOTSpectralMeasure ℝ H
```

and connect it to `A` by the actual unbounded functional-calculus reconstruction

```text
A = ∫ λ dE(λ)
```

The bounded-unitary PVM construction and the Cayley-domain argument are now proved.  The remaining
foundational work is the abstract uniqueness/coherence packaging and the faithful von Neumann
algebra/predual bridge.  Cayley transport itself is now packaged
as `cayleyMeasureEquiv`, an equivalence between real WOT spectral measures and bounded-side
measures supported on the unit circle away from `1`; `BoundedUnitarySpectralData` and
`SelfAdjointSpectralTheorem` remain explicit data structures because they describe the interfaces
consumed by downstream code; no arbitrary PVM is silently treated as a spectral resolution.  For the multiplication model, the
the generic bounded-normal certificate is now `BoundedNormalSpectralData`, constructed by
`cfcBoundedNormalSpectralData`; `cfcBoundedUnitarySpectralData` adds the precise `1 ∉ spectrum(U)`
hypothesis required before applying the Cayley inverse.

For the multiplication model, the
vector-measure composition identity

```text
∫ᵛ f d(μ.withDensityᵥ g) = ∫ f g dμ,
```

including its integrability statement, is now proved in
`Operators/MultiplicationSpectral.lean`.

The maximal unbounded realization now also exposes the two resolvent identities which make the
Cayley connection computational rather than merely existential.  For every vector `x`, the
inverse values of `M + i` and `M - i` are the bounded WOT integrals of
`(r + i)⁻¹` and `(r - i)⁻¹`, respectively.  Thus the resolvent part of the unbounded theorem is
available directly from the spectral measure, before any model-specific differential-operator
argument is supplied.

The bounded-unitary theorem is now implemented in
`Unbounded/BoundedUnitaryInfrastructure.lean`.  It proves, for an arbitrary normal bounded
operator, the following steps:

* real continuous test functions on the complex spectrum are embedded explicitly into the complex
  continuous functional calculus;
* the vector-state functional is positive by an actual square-root factorization and the
  positivity of `S† ∘L S`;
* Riesz--Markov produces its regular finite scalar measure;
* the measure integral is identified with the vector-state matrix coefficient.

The same file now also proves self-adjointness of the real CFC operator, constructs the canonical
four-term polarized complex scalar measure, and proves its scalar reconstruction formula for every
real compactly supported continuous test function.  The vector-measure layer now also proves the
finite signed-measure complexification identity: the real embedding component has exactly the
expected complex signed-measure integral, `SignedMeasure.toComplexMeasure` decomposes into
the real embedding plus the `I`-times-real embedding, and the latter component is proved to be
multiplication by `I` on the ordinary complex integral.  Finite signed differences are handled
linearly, so the four-term polarized scalar measure now has the weak reconstruction identity
against every compactly supported real test function.  The diagonal Riesz measures also satisfy
the parallelogram, sign, and `I`-phase identities, proved by regular-measure uniqueness rather
than assumed algebraically.

What remains after this layer is now sharply isolated: uniqueness/coherence of the resulting
spectral measure and the faithful von Neumann algebra/predual bridge.  The bounded part of the
representation bridge is now proved in `Unbounded/Representation.lean`: an explicit projection
bridge transports both bounded measurable functional calculus and the abstract exponential unitary
to the concrete WOT integral. Independently, the WOT integral itself
is now complete in `WeakSpectralMeasure.lean`: bounded measurable multipliers have a canonical
operator realization with the vector norm-square identity, and their exponentials form a strongly
continuous one-parameter unitary group (`expUnitaryGroup`).

The reusable unbounded layer is now complete in
`Operators/SpectralTheory/UnboundedSpectralIntegral.lean`: it constructs the square-moment
submodule, proves cutoff convergence, density of bounded spectral cutoffs, and the canonical
maximal symmetric closable `LinearPMap` with the exact second-moment norm identity. The canonical
operator is proved self-adjoint by the explicit resolvent construction; bounded real multipliers
are also proved equal to their bounded WOT integrals via
`boundedIntegral_ofReal_eq_measurableSpectralIntegral`.

Every `DomainAwareSelfAdjointSpectralTheorem` now has a `maximal_eq` theorem identifying its
operator with this canonical maximal realization. This is the packaged operator equality needed
by consumers; it is not an equality of only matrix coefficients.

The scalar analytic kernel for Stone's theorem is now in
`Operators/SpectralTheory/Stone.lean`: the exponential multiplier has its exact real-parameter
derivative, a uniform near-zero slope estimate, and a vector-measure dominated-convergence
theorem for the derivative remainder. The same file now proves the corresponding weak Stone
derivative for every scalar-measure matrix coefficient, as well as the strong Hilbert-space
derivative on the maximal square-moment domain. `OperatorAlgebra.Unbounded.Stone` packages this
as the domain-aware Stone theorem and proves the converse: the strong derivative exists exactly
on the operator domain.

## Deliberate scope

Hermite-function completeness is not required for the general spectral theorem. It is
only needed later to turn `E` into the discrete occupation-number sum. The representation layer
now has both directions that are available without extra hypotheses: abstract PVMs push forward
to concrete WOT PVMs, and an explicit projection bridge recovers its concrete measure and
transports bounded functional calculus and exponentials. The remaining abstract bridge is
specifically the faithful normal/WOT-to-norm von Neumann layer; that is what is needed to obtain a
canonical `AffiliatedObservable (B(H))` theory rather than a representation-parametrized one.

## Oscillator import closure

The oscillator example now imports the algebraic `InvariantCore` container directly rather
than pulling in the unfinished abstract affiliation/functional-calculus layer. A transitive
source audit from `Example/Spectrum` covers the local `Physlib` modules and the imported
`PhyslibAlpha` modules; none contains `sorry` or `sorryful`. The representation-bridge TODOs in
`Unbounded/Affiliated.lean`, `DensityOperator.lean`, `Distribution.lean`, and Nelson's commutation
layer are therefore not hidden dependencies of the oscillator target. `FunctionalCalculus.lean`
is sorry-free; its remaining TODOs concern compatibility with concrete domains and the canonical
unbounded realization, not the bounded algebraic laws. The WOT result and the Stone
generator/domain theorem are now representation-level results; the oscillator's closure or
explicit spectral decomposition remain separate.

The representation boundary now also has an explicit `FaithfulAffiliationBridge` extension. It
proves that represented PVM values, and hence represented affiliated observables, are unique when
the representation is faithful. What is still absent is the construction of such a bridge for a
general von Neumann algebra—most notably the trace-class predual realization of `B(H)`—rather than
the uniqueness theorem once that bridge is supplied.

The coherence surface is now tightened as well: bounded normal/unitary certificates have
extensionality lemmas, bounded-integral equality gives uniqueness of their PVMs, and the Cayley
side exposes both certificate extensionality and uniqueness of real measures recovered from equal
Cayley data. The self-adjoint certificate also has a thin operator-equality theorem once the
square-moment domain inclusion is supplied. These are consolidation theorems; they add no axioms
and do not weaken the explicit representation boundary.
