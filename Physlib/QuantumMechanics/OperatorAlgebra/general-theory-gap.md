# General unbounded-operator theory: what is still missing

Status checked: 2026-08-27.

This is the architectural checklist for a reusable theory of unbounded
self-adjoint observables. The harmonic oscillator should be an application of
this theory, not the place where its foundational theorems are hidden.

## The target

The intended endpoint has three compatible layers:

~~~text
closed densely-defined operators on H
        │  closure, Cayley transform, spectral theorem
        ▼
PVMs E : Borel ℝ → projections on H
        │  measurable functional calculus
        ▼
affiliated self-adjoint operators of a W⋆-algebra
        │
        ├── spectral projections and probability measures
        └── resolvents, exp(-itT), and unbounded functions of T
~~~

A PVM is not itself an unbounded operator. It becomes one only after a domain
is defined and the identity function is integrated with the correct
square-integrability condition. The theory must therefore keep domains,
closures, PVMs, functional calculus, affiliation, and dynamics distinct but
compatible.

### Important semantic boundary

The Hilbert-space object used by the concrete spectral theorem is a
`WOTSpectralMeasure`: its countable additivity is weak-operator additivity. The
abstract `PVM` currently used by `AffiliatedObservable` is stronger: it extends
Mathlib's norm-valued `VectorMeasure`. These notions coincide in finite
dimension, but not for a general infinite-dimensional `B(H)`. For example, the
spectral projections of an infinite orthogonal decomposition have tails of
operator norm one even though their strong/WOT sum converges.

Consequently `AffiliationBridge.toPVM` is an explicit capability, not a theorem
that follows merely from a faithful normal representation. The new
`Unbounded/NormalPVM.lean` module supplies the normal-state σ-additivity
contract, and `NormalAffiliated.lean` supplies the corresponding spectral-data
façade. The concrete `B(H)` realization now has the completed trace-class
predual, the normal-state/density correspondence, and the identity
representation's full trace-class matrix-coefficient bridge.
`NormalPVMTraceClass.lean` proves the extension from positive functionals to
self-adjoint and then arbitrary complex trace-class functionals, and
`normalPVM_toPredualPVM` packages the result as a usable `PredualPVM`
constructor. The old norm-additive and new normal-functional APIs remain
distinct by design, but the concrete `B(H)` conversion is now explicit.
The reverse direction is explicit as well: `WOTNormalityCertificate`
promotes a concrete `WOTSpectralMeasure` to a `NormalPVM`, while a
`PredualPVM` produces that certificate automatically. Both conversions have
proved round-trip laws, and the corresponding real and complex affiliated
façades are available. For the concrete algebra `B(H)`, the theorem
`wotSpectralMeasure_toWOTNormalityCertificate_of_traceClass` now proves the
certificate from the Hilbert--Schmidt square-root decomposition of every density
operator, so `wotSpectralMeasure_toNormalPVM_of_traceClass` and its affiliated
wrappers are certificate-free. The certificate remains explicit for an abstract
`WStarAlgebra`, where no representation/predual theorem is assumed.

## What is currently present

The whole subtree compiles, but compilation does not mean that the theory is
complete. The current code provides the following real infrastructure.

### Bounded algebra

Basic.lean, Observables/, Measurement/, FiniteDim/, VectorState.lean, and
Dynamics/ provide the bounded observable, state, finite-dimensional,
Jordan/Lie, and bounded Hamiltonian layers. These are mostly independent of the
unresolved unbounded-domain questions.

### Concrete partial operators

Unbounded/Concrete.lean, InvariantCore.lean, and RealAnalytic.lean use
LinearPMap for densely defined operators and provide analytic-core and
deficiency-index infrastructure. The one-dimensional oscillator module now
proves the Schwartz-domain, symmetry, and density facts and turns an explicit
deficiency certificate into essential self-adjointness. The certificate is
still the genuine model-specific ODE input; it is not fabricated by the
general operator layer.

`ClosureAPI.lean` now packages the graph closure, self-adjointness, uniqueness,
Cayley spectral measure, exact square-moment domain, and Stone unitary group once
essential self-adjointness is supplied. The model-specific theorem still has to
prove the actual essential self-adjointness hypothesis (the oscillator currently
does this through its explicit defect certificate).

### Cayley spectral data

Cayley.lean, BoundedUnitaryInfrastructure.lean, and CayleySpectralData.lean
construct the bounded Cayley transform, obtain its unitary spectral measure,
transport it to the real line, and prove a weak spectral-resolution/reconstruction
statement for self-adjoint LinearPMaps.

This is a substantial concrete foundation. The domain-aware endpoint is now public in
`UnboundedSpectralIntegral.lean`: the canonical maximal square-moment integral is self-adjoint,
and any self-adjoint `LinearPMap` with the corresponding weak reconstruction and domain inclusion
is proved equal to it, including domains. `AffiliationSpectralTheorem.lean` packages the
remaining handoff to the abstract affiliated façade.

### Bounded PVM integration: first layer

`Operators/SpectralTheory/WeakSpectralMeasure.lean` now contains the positive
diagonal measure construction for a weak PVM. For every vector `x`,

~~~text
μₓ(S) = ofReal (Re ⟪x, E(S)x⟫),
μₓ(S) = ofReal ‖E(S)x‖²,
μₓ(univ) = ofReal ‖x‖².
~~~

The same file defines the finite/simple multiplier integral as a finite weak
operator sum and proves its matrix-element formula and constant-function
normalization. This is the right starting point for bounded integration: it
uses weak σ-additivity and does not assume that an infinite-dimensional PVM
has finite operator-norm variation.

The abstract extension from simple multipliers to all bounded measurable
multipliers is now implemented in `Unbounded/FunctionalCalculus.lean` as a
norm completion in `A`. It has proved addition, multiplication, scalar
multiplication, negation, subtraction, star, constants, unitary functions,
and the indicator identity. The Hilbert-space/WOT extension is now also
implemented in `Operators/SpectralTheory/WeakSpectralMeasure.lean`: it has a
canonical completion independent of approximating simple functions, the exact
vector norm-square identity, and the corresponding algebraic laws.

The Hilbert-space representation part of that argument is now isolated in
`Operators/SpectralTheory/BoundedSesquilinear.lean`: a bounded sesquilinear
form has a canonical bounded operator realization, with proved matrix-element
uniqueness and a self-adjointness criterion. The WOT completion is now present
in `WeakSpectralMeasure.lean`, and
`Unbounded/BoundedUnitaryInfrastructure.lean` now constructs the bounded-normal
spectral PVM itself, including weak σ-additivity and projection values.
The reusable bounded self-adjoint adapter is now separate in
`Unbounded/BoundedSelfAdjointSpectralData.lean`: it pushes that complex-spectrum
measure through `Complex.re`, proves weak reconstruction, proves bounded real
support, and packages the full-domain case as a domain-aware spectral theorem.
Its finite-variation input is the general theorem
`polarizedCfcScalarMeasure_isFiniteMeasure`, so the Cayley-specific adapter no
longer contains a duplicated polarization estimate.

The new `Operators/SpectralTheory/UnboundedSpectralIntegral.lean` file now
implements the first genuinely unbounded construction for an arbitrary real
WOT spectral measure: the square-moment set is a proved complex submodule,
bounded cutoffs converge there, and their limit defines a canonical maximal
`LinearPMap`. Its domain is dense, the operator is symmetric and closable,
and its vector norm-square is exactly the second spectral moment. The canonical
operator is now proved self-adjoint by the Cayley-resolvent argument: the
bounded multipliers `(λ + i)⁻¹` and `(λ - i)⁻¹` give explicit preimages for
both shifted operators, so both ranges are all of `H`. The closure therefore
equals the maximal operator, and essential self-adjointness follows as a
corollary. The forward Cayley bridge proves that every vector in the self-adjoint
operator domain has finite second moment for the transported real spectral measure.
The reusable truncation layer also proves the real/complex scalar-integral
compatibility needed to compare weak reconstruction with norm limits.
For every measurable real `f`, `measurableSpectralIntegral` is the corresponding pushforward
realization, with its exact square-moment domain; bounded `f` is now exposed by the theorem
`measurableSpectralIntegral_domain_eq_top_of_bounded`.
The identity multiplier is now explicitly normalized by
`measurableSpectralIntegral_id`, so the measurable calculus returns the
original maximal spectral integral at `id` rather than merely an equivalent
pushforward presentation.
The square-moment API now also accepts an arbitrary finite coordinate bound,
not only the normalized bound used by the first resolvent construction. This
exposes the full non-real resolvent interface: for every `z` with `z.im ≠ 0`,
`resolventMultiplier z` is measurable and bounded, its coordinate multiplier
`λ ↦ λ / (λ - z)` is bounded, and the canonical maximal integral satisfies

~~~text
range (M - z • 1) = ⊤,
(M - z • 1)⁻¹ x = ∫ (λ - z)⁻¹ dE(λ) x.
~~~

Thus the concrete theorem no longer treats only the two Cayley shifts
`z = ± I` as resolvents; arbitrary non-real resolvents are now part of the
reusable API. This still does not construct the abstract von Neumann
algebra/predual bridge.
The same result is now exposed directly as
`maximalSpectralIntegral_mem_resolventSet` and
`maximalSpectralIntegral_resolvent_apply`, so the standard `LinearPMap.resolvent`
and `resolventSet` interfaces can be used without unpacking the construction.
`maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution` now
supplies the reusable reverse-domain/operator-equality step, and
`domainAwareSelfAdjointSpectralTheorem_of_isWeakSpectralResolution` packages the
result. `CayleySpectralData.lean` instantiates both the equality and the exact
domain theorem for the Cayley PVM.

The finite stage has also been strengthened:
`WOTSpectralMeasure.simpleIntegral_norm_sq` proves, for every complex-valued
measurable simple multiplier, the vector-state identity

~~~text
ofReal ‖(∑ z ∈ f.range, z • E(f ⁻¹' {z})) x‖²
  = ∑ z ∈ f.range, ofReal ‖z‖² · μₓ(f ⁻¹' {z}).
~~~

Its proof uses only orthogonality of disjoint spectral fibres and the positive
diagonal measure. The companion
`simpleIntegral_norm_le` theorem already gives the uniform estimate
`‖f(E)x‖ ≤ C‖x‖` whenever all values of the simple multiplier have norm at most
`C`. The abstract PVM completion and WOT operator-valued completion now consume
this estimate. The WOT-side construction, coherence, and uniqueness packaging
are complete.

### Representation-free affiliated data

Affiliated.lean defines AffiliatedObservable A by a real PVM whose values are
projections in A. This is useful spectral data, but it is not yet connected in
both directions to closed operators on a Hilbert space. The `NormalAffiliated`
and representation modules now provide that connection for a represented normal
PVM. The bounded observable inclusion still requires an explicit
`BorelFunctionalCalculus A` capability;
there is deliberately no default instance for a bare C⋆-algebra.

### W⋆ and normal-state scaffolding

WStarAlgebra.lean carries a chosen Banach predual, transports the weak-star
topology, and defines weak-star continuous NormalStates. The concrete `B(H)`
instance is now present, using the completed trace-class space and the
isometric duality

~~~text
B(H) ≃ StrongDual (TraceClass H),   A ↦ (ρ ↦ Tr(Aρ)).
~~~

The finite-dimensional boundary is now complete: `WStarAlgebra (B(H))` is instantiated through
the canonical bidual equivalence, every bounded operator is proved trace class, the witness trace
is identified with the ordinary linear-map trace in every Hilbert basis, and the standard finite
dimensional density-operator state certificate is constructed from the finite trace pairing. The
general trace-class Banach completion, two-sided ideal, `B(H)`/trace-class predual duality,
normal-state/density-operator correspondence, and concrete `NormalPVM` → `PredualPVM` conversion
are also proved. There is no longer a concrete trace-class completion gap at this boundary.

The general POVM/statistics layer is also pending; see todo.md.

The finite-multiplicity trace calculation is now proved at both useful boundaries:
`HasFiniteMultiplicity.finiteDimensional_range` shows unconditionally that a trace-class star
projection has finite-dimensional range, and
`HasFiniteMultiplicity.trace_eq_finrank_range_of_finiteDimensional` identifies the trace with that
dimension in finite dimension. The corresponding infinite-dimensional formula for star projections
is also proved unconditionally by `HasFiniteMultiplicity.trace_eq_finrank_range`; it uses the
self-adjoint Parseval/Fubini argument and does not assume the unresolved general trace theorem.
What remains is the genuinely general non-self-adjoint trace-basis-independence theorem, exposed as
the explicit `TraceBasisIndependence H` capability and requiring the polar-decomposition/trace-ideal
development. No such theorem is silently assumed by the current API.

### Representation compatibility now exposed

`Unbounded/NormalRepresentation.lean` now provides the reusable interface
`NormalAffiliationBridge`. It records the normal representation theorem at its
actual boundary: a normal affiliated PVM is sent to a weak-operator PVM, its
measurable pushforwards commute with that representation, and the represented
observable is the canonical maximal square-moment operator. The file proves
the represented operator's self-adjointness, exact domain, measurable-real
functional-calculus identity, the strongly continuous unitary group
`expUnitaryGroup`, and the domain-aware operator equality. The normal affiliated
façade also now exposes probability distributions, measurable pushforwards,
moments, expectations, and variances.

The underlying constructor is now generic in the measurable spectral space:
`NormalPVM.IsWOTCountablyAdditive` and
`NormalPVM.toWOTSpectralMeasure` work for arbitrary `X`, not only `ℝ`.
The normal Borel calculus is now generic in the same way: its spectral space
is an arbitrary measurable `X`, and `NormalAffiliatedOperator.boundedFC`
therefore exposes the bounded complex calculus for complex normal spectra,
not only the real self-adjoint specialization.
The theorem `NormalPVM.isWOTCountablyAdditive_of_diagonal` derives the full
matrix-coefficient certificate from diagonal quadratic coefficients by
polarization, and both bridge constructors have diagonal-certificate
variants.
`NormalOperatorAffiliationBridge.ofRepresentation` consumes the corresponding
real and complex certificates together, so the complex normal-affiliated API
has the same concrete construction boundary as the self-adjoint API.

The `PredualPVM` refinement now records countable additivity against every
chosen-predual vector, rather than only against positive normal states. A
norm-valued `PVM` upgrades to it automatically, and measurable pushforwards
preserve the refinement. `PredualMatrixCoefficientCertificate` proves full
WOT countable additivity directly from predual representations of matrix
coefficients; this is the exact coefficient-level input needed by a concrete
von Neumann representation.

`NormalOperatorAffiliationBridge` in the same module extends this compatibility
to complex normal affiliated operators: it represents their complex PVMs and
proves compatibility with arbitrary measurable complex pushforwards.

The abstract-to-concrete calculus seam is now proved from a
`NormalAffiliationBridge`: common uniform simple-function approximation gives
the representation theorem for the canonical bounded Borel calculus, with
derived compatibility for indicators, exponentials, resolvents, and
`NormalAffiliatedObservable` packaging. `NormalBorelRepresentationWitness.ofBridge`
and `NormalOperatorBorelRepresentationWitness.ofBridge` construct the real and
complex witnesses automatically; the corresponding `...Certificate.ofBridge`
definitions are compatibility packages, not hidden axioms. The representation-level construction
is now complete under the mathematically correct hypothesis that all bounded matrix coefficients
are weak-star continuous: `NormalRepresentation` proves the predual coefficient and vector-state
certificates and constructs the real/complex affiliation bridges. The concrete `B(H)` identity
representation supplies this hypothesis by rank-one trace-class coefficients.
`WStarAlgebra.predualPairing` and its norm estimate expose the canonical predual-to-algebra pairing.

This closes the formal API gap without pretending that normality of an arbitrary representation is
automatic. What remains external is only proving the weak-star continuity hypothesis (and the
relevant predual identification) for a separately chosen general von Neumann-algebra
representation; once supplied, the representation and domain results above apply immediately.

## Missing work, in dependency order

The order is important. Later layers must consume one domain notion and one
spectral-integral notion rather than introducing parallel formal substitutes.

### 1. A coherent concrete closed-operator API

Expose a single project-level vocabulary, either wrapping Mathlib's LinearPMap
or thinly naming its existing notions:

- dense domain and explicit domain inclusion/equality;
- graph closure and closedness;
- adjoint partial operator and adjoint domain;
- symmetric and self-adjoint operators;
- restriction and extension;
- closure of a closable operator;
- equality by agreement on a common domain;
- a Core T C predicate saying that C is graph-dense in T.

The usable essential-self-adjointness theorem should have this content:

~~~text
T essentially self-adjoint
  → T.closure is self-adjoint
  → T is a core for T.closure.
~~~

The defect-index/Nelson route belongs here. A certificate should imply the
actual closure theorem, not merely a proposition that every example has to
interpret independently.

For the oscillator, this layer must identify the closure of the
Schwartz-space differential operator with the intended L2(R) Hamiltonian.
Having the expected formula on Schwartz functions is not such an identification.

### 2. Finish the Cayley correspondence

The Cayley transform must be packaged as an equivalence, not only as a
one-way construction.

Prove and expose:

- a self-adjoint densely defined operator has a unitary Cayley transform;
- its Cayley transform has no eigenvalue at 1;
- a unitary with the corresponding missing-point/range condition reconstructs
  a self-adjoint operator;
- the two constructions are inverse up to equality of partial operators;
- domains are transported explicitly through x - U x, with the chosen sign;
- the PVM transports between the unit circle and the real line;
- the real PVM is normalized, weakly countably additive, and unique.

CayleySpectralData.lean already proves substantial pieces, including the inverse
moment argument. The public domain-aware result is now available as
`cayleyDomainAwareSelfAdjointSpectralTheorem`. The measure-level converse and
uniqueness are now packaged by `cayleyMeasureEquiv`: Cayley transport is an
actual equivalence with the unit-circle-away-from-`1` support condition. The
operator-level converse is now packaged in `Unbounded/CayleyInverse.lean`: the inverse Cayley
partial operator is defined on `range (1 - u)`, its symmetry and self-adjointness are proved, and
the no-fixed-vector condition is shown to imply dense domain. Both operator round trips are now
proved: the Cayley transform of the inverse operator is the original unitary, and the inverse
Cayley transform of `cayleyUnitary T hT` is the original self-adjoint `LinearPMap` `T`, including
the domain equality. The final bridge from this Cayley correspondence to the abstract affiliated
spectral-measure layer remains.

### 3. State the concrete unbounded spectral theorem with domains

For a PVM E, define scalar measures

~~~text
μₓᵧ(S) = ⟪y, E(S) x⟫
μₓ    = μₓₓ
D(E)  = {x | ∫ λ² ∂μₓ < ∞}.
~~~

Then construct T_E and prove:

- D(E) is a dense linear subspace;
- T_E is closed and self-adjoint;
- for x in D(E), T_E x is characterized by scalar integration against
  every test vector y;
- norm-squared satisfies ||T_E x||² = ∫ λ² ∂μₓ;
- the original T and T_E have the same domain and agree there;
- E is unique for T;
- spectral projections have the correct domain-sensitive commutation laws.

The formula T = ∫ λ dE(λ) must therefore mean equality of closed operators
with an explicit domain. A weak matrix-element identity alone is not enough
for the public spectral theorem.

Current implementation status: `Concrete.lean` now exposes
`spectralSquareMomentDomain` and a `DomainAwareSelfAdjointSpectralTheorem`
package. `UnboundedSpectralIntegral.lean` also provides the generic
self-adjoint weak-reconstruction equality theorem and its domain-aware
constructor. `MultiplicationSpectral.lean` proves the exact maximal-domain
characterization for real multiplication operators, including both inclusions
between the maximal `L²` domain and the pushed-forward square-moment domain.
The same package transports through Fourier/unitary conjugation, so the
momentum-coordinate realization is covered by the reusable theorem.

### 4. Complete the Hilbert-space bounded Borel calculus

For bounded measurable f : ℝ → ℂ, define f(T) by the PVM integral and prove:

- id(T) agrees with T when T is bounded;
- zero and one have their expected values;
- addition and multiplication are respected;
- conjugation corresponds to the adjoint;
- f(T) commutes with every spectral projection;
- indicator functions give exactly E(S);
- equality almost everywhere for the spectral measure gives equality;
- composition and pushforward are compatible with the PVM.

The representation-free `boundedFC` is already present in
Unbounded/FunctionalCalculus.lean, including `boundedFC_indicator`, and the
PVM transport laws are present in NormalState.lean and WeakSpectralMeasure.lean.
The normal-functional layer now also exposes the complex measurable calculus:
`NormalAffiliatedObservable.measurableFC` produces a
`NormalAffiliatedOperator`, its spectral-measure formula is proved, and the
calculus is functorial under composition. `NormalBorelFunctionalCalculus.ofPVM`
packages the existing norm-additive construction as a normal-calculus
certificate, giving an explicit one-way compatibility bridge between the two
layers.
The WOT-valued Hilbert-space construction and its vector norm-square identity
are now present. The identification with the abstract `boundedFC` object is
proved in `Unbounded/Representation.lean`: `Representation.simpleIntegral_eq_boundedIntegral`
handles finite sums, `Representation.boundedFC_eq_boundedIntegral` handles the norm completion
for every bounded measurable multiplier, and `Representation.expUnitary_eq_expIntegral` gives
the exponential/unitary specialization. `Representation.boundedFC_indicator_eq_representedSpectralProjection`
also identifies indicator functions with represented spectral projections. The remaining work is
only the abstract algebra-valued packaging when no normal-PVM/Borel-calculus
structure has been chosen. The concrete Hilbert-space bounded spectral PVM is
constructed by `BoundedUnitaryInfrastructure.lean` and the `B(H)` normal bridge.

### 5. Define unbounded measurable functions and domains

For measurable f, the correct domain is

~~~text
D(f(T)) = {x | ∫ ‖f(λ)‖² ∂μₓ < ∞}.
~~~

The resulting operator must be independent of representatives, closed, and
self-adjoint when f is real-valued.

Prove the domain-aware laws:

- id(T) = T as closed operators;
- bounded f agrees with the bounded calculus;
- composition f(g(T)) has the correct maximal domain;
- sums and products state their common/maximal-domain hypotheses;
- truncations converge in a specified graph or strong-resolvent sense;
- resolvents are bounded for z outside the real line;
- real Borel functions produce affiliated self-adjoint observables.

This is where measurableFC, boundedFC, resolvent, and truncate belong. The
representation-free spectral-data operations are now present, and `truncate`
is proved self-adjoint. The domain statements are essential: without them,
“functional calculus” only names bounded operators.

The normal-PVM façade has the corresponding real and complex measurable
pushforward operations, with identity and composition laws. The canonical
`NormalBorelFunctionalCalculus.ofNormalPVM` constructs the bounded calculus
for every normal-functional PVM; `ofPVM` remains the compatibility constructor
for the older norm-valued layer.
The algebra-level `NormalObservableBorelCalculus` now packages that certificate
per bounded observable, and `Observable.normalBoundedFC` exposes its measurable
calculus. Its bounded-observable finite-moment corollary is also proved in
`NormalAffiliated.lean`; the support hypothesis is consumed explicitly, so no
integrability of an unbounded function is silently assumed.
The same file now exposes `Observable.normalExpUnitary` and
`Observable.normalResolvent`, together with their group and resolvent identities,
as the direct bounded-observable entry points.

### 6. Make affiliation a genuine bridge

For a representation π : A → B(H), establish equivalence between:

1. a closed self-adjoint T whose spectral projections lie in π(A);
2. a real PVM in A whose represented PVM is the spectral measure of T;
3. the bounded-transform or commutant characterization of affiliation.

`Observable.toAffiliatedObservable` no longer hides this requirement behind a
`sorry`: its PVM is obtained from the explicit `BorelFunctionalCalculus A`
capability. The remaining work is to construct that capability from a faithful
normal representation and prove its compatibility with continuous functional
calculus.

The bridge needs:

- uniqueness from spectral projections;
- functoriality under StarAlgEquiv and representations;
- the canonical bounded inclusion Observable.toAffiliatedObservable;
- recovery of bounded observables from the affiliated identity calculus;
- representation compatibility of projections, resolvents, truncations, and
  bounded functions.

The first uniqueness component is now implemented: `Concrete.lean` exposes a
`FaithfulAffiliationBridge` extension, and proves that a faithful representation reflects equality
of bridged PVM values and determines an affiliated observable from its represented spectral
projections. The bridge construction is complete under the explicit normal-representation
hypothesis; the remaining theorem for a genuinely arbitrary von Neumann algebra is proving that
its chosen representation has weak-star-continuous matrix coefficients, not the uniqueness step.
The representation side is now factored cleanly: `NormalPVM.IsWOTCountablyAdditive` states the
matrix-coefficient σ-additivity condition, `NormalPVM.toWOTSpectralMeasure` constructs the WOT
spectral measure from it, and `NormalAffiliationBridge.ofRepresentation` packages the resulting
map and its measurable-pushforward law. `NormalRepresentation.continuousCoeff_exists_predual`
proves the coefficient certificate from weak-star continuity, and
`NormalRepresentation.toNormalAffiliationBridge` supplies the bridge itself. The WOT construction
is no longer an unimplemented bridge field. The remaining theorem for an arbitrary chosen von
Neumann algebra is only the external proof of the normality hypothesis.
`NormalPVM.NormalVectorStateCertificate` packages the concrete normality input at the vector-state
level: every unit-vector state is a weak-star-continuous `NormalState` and agrees with the
represented quadratic form. Its proved `diagonal_hasSum` theorem derives diagonal additivity for
every normal PVM, so `NormalAffiliationBridge.ofNormalVectorStateCertificate` and
`NormalOperatorAffiliationBridge.ofNormalVectorStateCertificate` are direct entry points once the
concrete predual theorem supplies those vector states. The norm-additive special case is available
through `NormalPVM.isWOTCountablyAdditive_ofPVM`.
The stronger `PredualPVM` refinement now records additivity against every chosen-predual
functional, with automatic construction from norm-valued `PVM`s and preservation under measurable
pushforward. `PredualMatrixCoefficientCertificate.isWOTCountablyAdditive` turns a predual
realization of all matrix coefficients directly into the WOT certificate, and
`NormalPVM.toWOTSpectralMeasure_of_predual` consumes that pair as a proved adapter. For the
concrete identity representation, `NormalPVMTraceClass.lean` now proves the refinement for every
trace-class functional and exposes `normalPVM_toPredualPVM`; the trace-norm completion argument is
no longer pending.
`NormalAffiliationBridge.ofPredualRepresentation` and its faithful variant now package this
adapter for an entire measurable-PVM family, provided the predual lifts satisfy their explicit
pushforward law. The concrete identity representation now supplies those lifts for real and complex
normal PVMs through `traceClassAffiliationBridge` and
`traceClassOperatorAffiliationBridge`. The remaining theorem is only the analogous construction
for an arbitrary chosen von Neumann algebra representation.
`NormalObservableBorelCalculus` supplies the corresponding algebra-level bounded Borel entry point
for normal PVMs: it chooses the spectral measure and a law-governed bounded measurable calculus
for each bounded observable. `NormalObservableBorelCalculus.ofBorelFunctionalCalculus` embeds the
stronger norm-additive calculus into this normal layer, while
`Observable.toNormalAffiliatedObservable`, `normalBorelCalculus`, and `normalBoundedFC` expose the
usable bounded-observable API without silently asserting that an arbitrary C⋆-algebra contains
Borel projections.
The concrete file `NormalBorelFunctionalCalculusBoundedOperators.lean` now supplies this entry
point automatically for `B(H)`: bounded self-adjoint spectral data is converted to a normal PVM
by the trace-class theorem, and `boundedObservableNormalCalculus` supplies the canonical bounded
measurable calculus. Thus concrete `B(H)` applications no longer need to provide an algebra-level
normal-calculus capability for bounded observables.

The bounded-observable inclusion must be supplied by the bounded Borel
calculus, not by choosing an arbitrary normalized PVM. This requirement is now
represented explicitly by `BorelFunctionalCalculus A` in Affiliated.lean.

Unbounded algebraic operations also need explicit hypotheses. Sums and products
of unbounded operators are not automatically self-adjoint; strong commutation or
a suitable invariant common core is required. Core.lean should eventually
express those domain conditions and prove the Nelson/strong-commutation bridge.

**Status (checked 2026-08-26).** `AffiliatedOperator`/`AffiliatedObservable` (Affiliated.lean) are
now defined for real, representation-free, directly by their spectral measure (`PVM ℂ A`/`PVM ℝ A`
respectively — see item 8 below for `PVM`); `toAffiliatedOperator` (real → complex spectral
measure via `PVM.map`), `spectralProjection`, and the spectrum/discrete-spectrum/essential-spectrum
vocabulary and symmetry-preservation theorems (`SpectralDecomposition.lean`, entirely sorry-free)
are genuinely built and proved. `Core.lean`'s `StronglyCommutes` (spectral-projection commutation)
and its consequences (`spectralProjection_comm`, `map_comm`, `preserves_spectralSubspace`) are
proved; `preserves_eigenspace` is now also proved for real, but with a corrected hypothesis — it
turned out to be **unprovable as originally stated**: its hypothesis `StronglyCommutes` is a fact
about `T`'s spectral measures inside `A`, while `InvariantCore` carries *no* field connecting
`core.restrict` back to `T` at all, so the old hypothesis was logically inert. The fix (see the
lemma's docstring in `Core.lean`) states the coherence that is actually available and usable at
the algebra level directly: `Commute (core.restrict 0) (core.restrict 1)` as the hypothesis, from
which the standard "commuting endomorphisms preserve each other's eigenspaces" fact is proved in
full. `of_commonCore_comm` exposes Nelson's commutation conclusion as an explicit analytic
certificate: the algebraic/core hypotheses alone do not prove the strong-commutation theorem in
the current library, so there is no hidden axiom or `sorry`. The remaining Borel
functional-calculus work is now explicit in `BorelFunctionalCalculus A`, which is required by
`Observable.toAffiliatedObservable` — it needs a Borel/measurable functional
calculus producing indicator-function projections `1_S(a) ∈ A` for a bounded self-adjoint element
`a`, and since `A` here is only assumed a plain `OperatorAlgebra` (C⋆-algebra), not a von Neumann
algebra, this is not just "hard Lean plumbing": for a *non*-weakly-closed C⋆-algebra, `1_S(a)`
generally does not even lie back in `A` (e.g. take `A = C(X)` for compact `X`, where indicator
functions of most Borel sets are not continuous) — so the fully general statement genuinely needs
`A` upgraded to a `WStarAlgebra` (weakly closed) first, which is a separate, still-open
prerequisite (see item 7).

### 7. Complete W⋆-algebras and normal states

The chosen-predual WStarAlgebra design is a reasonable foundation, but the
quantum-mechanical consequences still need to be proved:

- trace-class operators form a complete normed space;
- trace and trace norm are basis-independent;
- trace class is a two-sided ideal;
- B(H) has the intended predual identification;
- density operators define normalized positive states;
- every normal state has the intended density-operator representation;
- normality is connected to countable additivity of scalar spectral measures.

The trace-class and density-operator conclusions are not necessary for one abstract PVM, but they
are necessary before the framework can honestly claim a usable theory of normal quantum states on
B(H). The current files prove the trace ideal, completed trace-class space, product-trace state,
and normal-state/density-operator correspondence. The certificate-taking constructors remain
only as explicit compatibility interfaces; no hidden sorries remain in them.

**Status (checked 2026-08-27).** `WStarAlgebra.lean` is complete and sorry-free: `WStarAlgebra A`
(chosen predual + isometric identification `A ≃ₗᵢ[ℂ] StrongDual ℂ (Predual A)`), the induced
weak-⋆ topology `weakStarTopology`, `norm_le_weakStarTopology`, and `NormalState A` (a state
continuous for that topology, with `NormalState.continuous` as a proved corollary) are all real,
Sakai-honest definitions/theorems — this closes the "no predual/weak-⋆ topology" gap `todo.md`
identified. `TraceClass.lean`'s positive/Hilbert–Schmidt basis-independence result is closed
without needing any unbounded (or even bounded) spectral theorem:
`summable_inner_abs_of_hilbertBasis` is proved directly from Mathlib's `HilbertBasis` Parseval
API. General basis-independence, the trace-class ideal theorem, and the density-state
positivity/linearity package are now proved by the polar, Hilbert--Schmidt, and trace-product
development. The positive part is also exposed through `trace_eq_of_hilbertBasis_of_nonneg`, and
the self-adjoint extension through `trace_eq_of_hilbertBasis_of_isSelfAdjoint`. In the concrete
spectral pipeline,
The reusable API now also exposes `isTraceClass_iff`, which removes the existential witness from
downstream statements, `traceNorm_congr` for proof-independent trace norms, and
`traceNorm_nonneg`. These are proved consequences of the existing basis-independence argument;
the polar-decomposition/ideal theorem is now also complete in the trace-class
support modules.
`EssentialSelfAdjointSpectralData.spectralTheorem` now retains the full domain-aware theorem,
including the exact square-moment domain, rather than only its weak reconstruction projection.
`DensityOperator.lean` defines `DensityOperator H`, `toStateFun`, and the Born-rule specialization
`bornRule`. `DensityOperatorTraceState.lean` now supplies the canonical product-trace state and
the unique normal-state/density-operator correspondence; the older certificate-taking
constructors remain only as compatibility interfaces. A finite-dimensional `WStarAlgebra (B(H))` instance is now available in
`WStarAlgebra/FiniteDimensional.lean` (using the strong dual of `B(H)` as its predual), and
`Unbounded/NormalRepresentationFiniteDimensional.lean` supplies the identity representation's
normal vector-state certificate and faithful real/complex affiliation bridges. The
infinite-dimensional instance (predual = the completed trace-class space) and its normal-state
representation are now built in `WStarAlgebra/InfiniteDimensional.lean` and
`Unbounded/NormalStateRepresentation.lean`.

The finite-dimensional projection case is no longer a placeholder: the trace is proved equal to
`Module.finrank ℂ (LinearMap.range p.toLinearMap)` by reducing to Mathlib's ordinary linear-map
trace theorem. The infinite-dimensional trace-class/range and product-trace arguments are now
also proved, using the completed ideal and Hilbert--Schmidt factorization.

### 8. General POVMs and measurement statistics

A PVM for a self-adjoint observable is a special case of a POVM. The general
measurement layer needs a measurable outcome space and an explicit
sigma-additivity convention: norm, weak-operator, or normal-functional.

The reusable bridge is:

~~~text
POVM E + normal state ω
        → probability measure (S ↦ ω(E(S)))
        → integrals, moments, distributions.
~~~

Implement the plan in todo.md:

- choose and document the topology or normal-functional formulation;
- keep values in an additive positive operator space, not Effect A;
- prove scalar probability-measure laws and normalization;
- provide finite-discrete compatibility;
- connect PVM functional calculus to moments;
- prove finite-moment statements only after the affiliated construction exists.

**Status (checked 2026-08-25): done.** `todo.md`'s "honest" route (option 1, the abstract
`WStarAlgebra`/normal-state characterization) was chosen and is fully implemented, sorry-free:
`Projection A` (star projections), `PVM X A` (a normalized `Projection`-valued `VectorMeasure`,
`NormalState.lean`) with composition (`comp_eq_of_inter`, `commute`), pushforward (`PVM.map`), and
the measurement-statistics bridge `PVM.distribution`/`distribution_apply` (`μ_{ω,E}(S) = ω(E(S))`,
built as an honest `MeasureTheory.Measure` via `Measure.ofMeasurable`, using `ω`'s continuity for
countable additivity, exactly the "normal-functional σ-additivity" convention `todo.md` asked for
in place of a norm/WOT topology on the algebra itself). The genuinely *general* (non-projective)
POVM — `todo.md`'s actual headline ask, values in `Effect A` rather than `IsStarProjection` — is
now also built, in the new file `Unbounded/POVM.lean`: `POVM X A` (a normalized, pointwise-
nonnegative `VectorMeasure`), `POVM.mem_effect` (every measurable value is a genuine effect,
`0 ≤ M S ≤ 1`, proved from positivity plus `M S + M Sᶜ = M univ = 1`), `PVM.toPOVM` (every PVM is
a POVM) with `PVM.distribution_toPOVM` (the two `distribution` constructions agree along it), and
`POVM.distribution`/`distribution_apply`, all sorry-free. `Basic.lean`'s finite POVM was renamed
`FinitePOVM` (nothing else referenced the old name) and given the promised finite-discrete
correspondence `FinitePOVM.toPOVM` (a finite sum of Dirac vector measures on the discrete
measurable space on `X`), also sorry-free. What remains open in this section: connecting `PVM`
functional calculus to moments beyond the real spectral measure case (`Distribution.lean`'s
`HasFiniteMoment`/`moment`/`expectation`/`variance` already exist and are sorry-free for
`AffiliatedObservable`).  The bounded-observable compatibility corollary
`Observable.toAffiliatedObservable_hasFiniteMoment` is now also proved, using the explicit
bounded-support certificate carried by `BorelFunctionalCalculus`.

### 9. Construct the unitary group from the calculus

After bounded Borel calculus, define

~~~text
U(T,t) = (fun λ => exp (-Complex.I * t * λ))(T).
~~~

Then prove:

- U(T,t) is unitary;
- U(T,0) = 1 and U(T,s+t) = U(T,s) * U(T,t);
- U(T,-t) = star (U(T,t));
- t ↦ U(T,t)x is strongly continuous;
- the generator is -Complex.I • T with the correct domain;
- the result agrees with the Stone correspondence;
- strongly commuting bounded observables evolve by conjugation with the
  expected derivative where defined.

This is the proper home of AffiliatedObservable.expUnitary. It should be a
corollary of bounded measurable functional calculus, not a formal exponential
of an unbounded algebra element.

**Status (updated 2026-08-26).** The finite PVM integral, its refinement/additivity laws, the
uniform bounded-range simple approximation, and the norm-completion construction of `boundedFC`
are implemented in `FunctionalCalculus.lean`. Independence/uniqueness, addition, multiplication,
star, constants, unitary functions, the indicator identity, the resolvent identity, and the
one-parameter multiplication laws for `expUnitary` are proved. `truncate` is self-adjoint as well.
The WOT layer additionally proves the vector norm-square identity, star and multiplication
compatibility, and strong continuity of the exponential; `expUnitaryGroup` packages it as a
strongly continuous one-parameter group of unitary bounded operators. It now also has
`measurableSpectralIntegral`: for every measurable real function it constructs the maximal
operator from the pushforward PVM, proves its exact square-integrability domain, weak
reconstruction, self-adjointness/closure, composition, and norm-square identity. The exponential
evolution now also preserves the square-moment domain via
`expIntegral_mem_spectralSquareMomentDomain`. The abstract `boundedFC`/WOT compatibility is now
proved by `Representation.boundedFC_eq_boundedIntegral`, its indicator specialization, and its
exponential specialization.
The operator-level Stone result is also complete: `Unbounded/Stone.lean` proves the strong
derivative on the operator domain and the converse characterization of that domain by existence of
the derivative at zero. What remains is the genuinely concrete von Neumann boundary: constructing
the normal/Borel PVM and its affiliated algebra element from a faithful normal representation.
The concrete `B(H)` normal/Borel boundary is now implemented by the trace-class
bridge; only the analogous construction for an arbitrary chosen von Neumann
algebra remains external to this package.

## Oscillator as an application

Once the general layers exist, the oscillator-specific work should be:

1. define position and momentum on a common dense Schwartz core;
2. prove their algebraic identities on that core;
3. prove essential self-adjointness of the Hamiltonian;
4. identify its self-adjoint closure with the intended L2(R) Hamiltonian;
5. obtain its PVM from the general spectral theorem;
6. prove Hermite completeness only for the explicit discrete decomposition;
7. calculate the energy spectral projections and their sum;
8. define exp(-itH) through the general calculus.

Hermite completeness is special-function input. It should not be needed for the
reusable operator theory.

## Acceptance criteria

Do not call the general theory complete merely because the files compile.
The following should hold:

- no sorry, admit, or placeholder axiom in the general theory modules;
- the spectral theorem states equality of closed operators with an explicit
  domain;
- the PVM is unique and indicator calculus is proved;
- bounded and unbounded measurable calculus share one construction;
- the identity function returns the original self-adjoint operator;
- exp(-itT) is a proved strongly continuous unitary group;
- concrete affiliation is equivalent to the abstract PVM object under a
  representation;
- B(H) has the intended predual/normal-state instance, or the limitation is
  explicit;
- the oscillator imports the theory without adding foundational axioms.

Practical priority:

**domains and closure → Cayley equivalence → domain-aware spectral theorem →
bounded Borel calculus → unbounded calculus → affiliation and normal states →
unitary dynamics → model applications**.
