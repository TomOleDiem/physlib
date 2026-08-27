# General unbounded spectral theory: remaining work packages

Status: 2026-08-27.  This document is the authoritative handoff plan for
parallel agents.  It describes the remaining work needed for a reusable, sorry-free unbounded
spectral theory.  `HardyInequality.lean` is intentionally outside this plan
because it is an independent analytic application, not a prerequisite for the
general operator API.

## Current baseline

The following pieces already compile and should be treated as existing APIs:

- `LinearPMap` domains, dense cores, closure/essential-self-adjointness
  certificates, and the Cayley-transform infrastructure;
- the domain-aware Hilbert-space spectral theorem for a self-adjoint
  `LinearPMap`, with the exact square-moment domain;
- weak-operator spectral measures, bounded/simple spectral integration, the
  measurable pushforward construction, resolvents, and Stone's strongly
  continuous unitary group;
- the public `Unbounded/StoneAPI.lean` generator façade, including the exact
  zero-time differentiability/domain equivalence and the forced derivative
  formula;
- representation-free `AffiliatedObservable`/`NormalAffiliatedObservable`
  spectral-data façades;
- `PredualPVM`, predual matrix-coefficient certificates, and the adapter
  `NormalPVM.toWOTSpectralMeasure_of_predual`;
- the concrete infinite-dimensional `WStarAlgebra (B(H))` instance, whose predual is
  the completed trace-class space and whose pairing is proved onto;
- the arbitrary-dimension identity-representation normal bridge, including rank-one
  matrix-coefficient certificates and compatibility of bounded Borel calculus with
  the WOT spectral integral.
- `NormalPVMTraceClass.lean` proves the predual σ-additivity formula for every
  completed trace-class functional and packages the concrete `B(H)` conversion
  as `normalPVM_toPredualPVM`, with real and complex affiliation bridges.
- `Operators/MultiplicationSpectral.lean` publicly supplies the maximal real
  multiplication spectral theorem and Fourier-side momentum realization.
  `Operators/MomentumSpectral.lean` additionally proves the reusable Schwartz
  core identity `𝓕 (-iℏ ∂ᵢ f) = 2πℏ pᵢ 𝓕 f` and the graph inclusion
  `momentumOperator i ≤ fourierMomentumOperator i`, hence the one-sided closure
  bound `closure (momentumOperator i) ≤ fourierMomentumOperator i`.
- `Operators/MultiplicationCore.lean` now proves the reusable graph-core theorem
  `schwartzMulOperator_closure_eq_mulOperator`: a continuous temperate multiplier's
  maximal multiplication operator is exactly the closure of its Schwartz restriction,
  together with the real-multiplier essential-self-adjointness corollary.  It also
  proves the graph-measure domain representation used by the density argument.
- `Operators/Unbounded.lean` now proves `IsClosable.unitaryConj_closure`, so graph-core
  results can be transported through Fourier/unitary representations without a new
  closure argument each time.
- `Operators/PositionSpectral.lean` applies the same theorem to the Schwartz position
  restriction.  `Operators/MomentumSpectral.lean` applies it after the exact Fourier
  identification, yielding the momentum closure and spectral data.
- `Unbounded/ClosureAPI.lean`, which packages the essential-self-adjoint core
  handoff: canonical closure, self-adjointness, extension uniqueness, Cayley
  spectral data, exact square-moment domain, and the Stone generator interface.
- `Unbounded/CayleyCertificate.lean`, which packages the already-constructed
  Cayley spectral data into a canonical `CayleySpectralCertificate` directly
  from self-adjointness.
- `Unbounded/NegativeStoneAPI.lean`, which exposes the conventional quantum
  dynamics group `e⁻ⁱᵗᵀ` by time reversal of the proved `e⁺ⁱᵗᵀ` group, including
  strong continuity and the exact `-iT` generator-domain theorem.
- `NormalAffiliated.lean`, `NormalAffiliatedCanonical.lean`, and
  `NormalRepresentation.lean` now expose the same negative-time convention at
  the abstract normal-affiliated, observable, and represented-Hilbert-space
  levels, with proved group laws and canonical representation compatibility.
- `Unbounded/EssentialSelfAdjointCriteria.lean`, which proves the reusable
  deficiency-space criterion that a symmetric partial operator with a total
  family of domain eigenvectors having real eigenvalues is essentially
  self-adjoint. This is a criterion; it does not yet prove that the
  oscillator's Schwartz eigenfunctions satisfy its hypotheses.
- `Unbounded/DensityOperatorQuadraticForm.lean`, which constructs a genuine
  normalized positive linear state from a density operator using the bounded
  square-root quadratic form. It also exports `bornRuleQuadraticForm` with
  proved positivity and normalization for every PVM value.
- `Unbounded/DensityOperatorTraceState.lean`, which proves the arbitrary-
  dimensional product-trace state using the Hilbert--Schmidt square-root
  cycle, identifies it with the trace-class predual pairing, and proves the
  unique normal-state ↔ density-operator correspondence. The direct API is
  `NormalState.densityOperator`; certificate-taking constructors remain only
  for compatibility.
- `TraceClass/PositiveIdeal.lean`, which proves the reusable positive ideal
  estimate: if `P` is positive and trace class, then `A⋆ P A` is trace class
  for every bounded `A`. The proof is an explicit Parseval/Tonelli double-sum
  argument and does not assume polar decomposition. It also proves scalar
  closure for arbitrary trace-class operators and additive closure for positive
  trace-class operators.
- `Unbounded/DensityOperatorTraceBridge.lean`, which proves that for a density
  operator `ρ` and a positive bounded observable `A`, the sandwich
  `√ρ A √ρ` is trace class and its trace is exactly the quadratic-form state.
  This is the positive-observable trace formula used by the full product-trace
  state in `DensityOperatorTraceState.lean`.
- `TraceClass/Polar.lean`, `TraceClass/HilbertSchmidt.lean`,
  `TraceClass/TraceProduct.lean`, and `TraceClass/GeneralIdeal.lean`, which
  provide the bounded polar factor, basis-independent Hilbert--Schmidt
  square sums, absolute summability of Hilbert--Schmidt products, and the
  unconditional basis-independent diagonal trace theorem.
- `TraceClass/PositiveTrace.lean`, which proves that a positive trace-class
  operator has complex trace equal to the real trace norm and therefore has
  nonnegative trace.  This is a finished positive-state lemma, not the
  unresolved general ideal theorem.
- `TraceClass/HilbertSchmidtAlgebra.lean`, which proves linear closure of the
  Hilbert--Schmidt predicate, its two-sided bounded-module closure, and that
  both `S⋆S` and `S S⋆` are trace class whenever `S` is Hilbert--Schmidt.
- The same module now proves the quantitative identities identifying the
  trace norms of `S⋆S` and `S S⋆` with their Hilbert--Schmidt square sums in
  every Hilbert basis.  The quantitative ideal estimates are now in
  `TraceClass/IdealNorm.lean`.
- `TraceClass/Space.lean` and `TraceClass/Completeness.lean` now assemble the witness predicate into a public
  `TraceClass H` subtype with `AddCommGroup`, `Module ℂ`,
  `NormedAddCommGroup`, and `NormedSpace ℂ` instances, and it builds
  standalone, and `Completeness.lean` proves the promised `CompleteSpace
  (TraceClass H)` instance by lower semicontinuity under operator-norm limits.
  `TraceClass.Pairing` imports this completed subtype for downstream use.
- `TraceClass/RankOne.lean` now proves, by Parseval, that every positive
  rank-one operator `rankOne ℂ x x` is trace class and has both trace and
  trace norm equal to `‖x‖²`.  This is the rank-one test object reserved for
  Card 2's predual norm and density arguments.
- `TraceClass/HilbertSchmidtEstimate.lean` exports the quantitative
  Hilbert--Schmidt right-module square-sum bound, and
  `TraceClass/PositiveIdealEstimate.lean` turns it into the two positive
  conjugation estimates `‖A⋆PA‖₁, ‖APA⋆‖₁ ≤ ‖A‖²‖P‖₁`.  The arbitrary
  non-self-adjoint ideal theorem is supplied by `GeneralProduct.lean`.
- `TraceClass/PositiveDomination.lean` exports the order-theoretic fact that
  a positive operator dominated by a positive trace-class operator is trace
  class.  It also applies this to the positive and negative parts of a
  trace-class self-adjoint operator.  This is a reusable ingredient for the
  self-adjoint decomposition step.
- `TraceClass/GeneralProduct.lean` now proves the master product theorem:
  Hilbert--Schmidt times Hilbert--Schmidt is trace class, using the polar
  partial-isometry identity and the Hilbert--Schmidt Cauchy--Schwarz bound.
  The same module proves arbitrary additive closure of `IsTraceClass` and
  two-sided bounded multiplication via the polar/square-root factorization,
  as well as adjoint closure.
- `TraceClass/TraceAlgebra.lean` now exports trace additivity, bounded-factor
  cyclicity, and the adjoint/conjugation law for the unconditional trace.
- `TraceClass/IdealNorm.lean` now exports the quantitative contraction-duality
  estimate, trace-norm subadditivity, operator-norm domination, and the
  explicit two-sided estimate
  `‖A*T*B‖₁ ≤ ‖A‖ * ‖T‖₁ * ‖B‖`.
- `TraceClass/TraceAlgebra.lean` exports scalar homogeneity, additivity,
  bounded-factor cyclicity, and the adjoint/conjugation law for the
  unconditional trace.

The following targets were rebuilt in the live tree on 2026-08-27 and finished
successfully (warnings only): `TraceClass.IdealNorm`,
`TraceClass.TraceAlgebra`, `Unbounded.WeakStarFunctionalCalculus`,
`Unbounded.ClosureAPI`, `Unbounded.StoneAPI`,
`Unbounded.DensityOperatorTraceState`, and the public `Unbounded` entry point.
This is a compilation status, not a claim that the architecture is complete.

`Unbounded/WeakStarFunctionalCalculus.lean` is imported by `Unbounded.lean` and
provides the canonical bounded calculus for every `NormalPVM`, constructed by
uniform simple-function approximation.  The stronger, separately packaged
predual scalar-integral object is not needed by this API and remains an
optional future refinement; it must not be confused with a missing theorem in
the current norm-completion calculus.

The trace/predual work (P1/P2), bounded normal calculus (P3), Cayley/domain
theorem (P4), and Stone derivative theorem (P6's analytic core) are complete.
The current remaining work is the explicit representation/affiliation
boundary (P5), model-specific applications such as the oscillator (P7), and
the final capability/import audit (P8).  The new
`Unbounded/AffiliationSpectralTheorem.lean` module now completes the reusable
operator hand-off inside P5: it identifies a represented maximal integral
with any domain-aware realization or with the canonical closure of an
essentially self-adjoint core, and exposes the canonical represented
exponential and resolvent.  Its `NormalRepresentation` façade additionally
constructs the bridge automatically and exposes the closure equality, domain
equality, core inclusion, both Stone sign conventions, and their generator
derivatives in one model-facing API.

`Unbounded/NormalPVMTraceClass.lean` now also exposes the reverse concrete
boundary.  A WOT spectral measure can be promoted to a `NormalPVM` through
`WOTNormalityCertificate`; the certificate records exactly the missing
σ-additivity against all normal states, and the round-trip back to the WOT
measure is proved.  A `PredualPVM` supplies that certificate automatically,
and the corresponding round-trip to its `NormalPVM` is also proved.  This is
deliberately an explicit hypothesis at the abstract algebra boundary.  In the
concrete `B(H)` case, `wotSpectralMeasure_toWOTNormalityCertificate_of_traceClass`
proves the certificate from the density-operator/Hilbert--Schmidt decomposition,
and `wotSpectralMeasure_toNormalPVM_of_traceClass` plus the affiliated wrappers
hide the certificate from applications.  The new
`NormalBorelFunctionalCalculusBoundedOperators.lean` file similarly supplies a
certificate-free `NormalObservableBorelCalculus (B(H))` for bounded
self-adjoint operators, using the bounded self-adjoint spectral theorem and
the concrete normal-PVM promotion.

## What is still a capability rather than a theorem

These are the exact declaration-level boundaries an agent must eliminate or
explicitly retain as external hypotheses:

- the compatibility-only `TraceClassRightIdeal` and
  `DensityOperatorStateCertificate` interfaces in `Unbounded/DensityOperator.lean`.
  The right-ideal instance and the arbitrary-dimensional canonical product-trace
  certificate are now proved; callers should use
  `DensityOperator.canonicalNormalState` or `NormalState.densityOperator`;
- `BorelFunctionalCalculus` in `Unbounded/Affiliated.lean`, because an arbitrary
  C⋆-algebra has no automatic Borel projection calculus.  The concrete `B(H)`
  normal-functional version is now supplied by
  `NormalBorelFunctionalCalculusBoundedOperators.lean`;
- `AffiliationBridge`/`FaithfulAffiliationBridge` in `Unbounded/Concrete.lean`,
  because WOT/normal-functional σ-additivity does not imply norm σ-additivity;
- the `NormalAffiliationBridge` representation input in
  `Unbounded/NormalRepresentation.lean`, while its bounded-calculus
  compatibility theorem is now proved canonically for every supplied bridge;

The target is not to delete every structure with “certificate” in its name.
The target is to replace each certificate whose content follows from the
chosen general construction by a theorem, while retaining explicit input
only for genuinely external facts (for example, a concrete differential
operator's essential self-adjointness).  A green Lean build alone does not
cross any of these boundaries.

## Concrete task cards for parallel development

These cards are the authoritative split for the next agents.  Each card is
independently mergeable: it has a narrow file boundary, a dependency list, a
public output contract, and a test that can be run without waiting for the
other cards.  An agent must not edit a file owned by another card merely to
make its own target compile; instead, add a small adapter in the agent's own
support file and report the required contract change.

### Card 1 — Trace ideal and polar decomposition

**Files owned:** `TraceClass.lean`, and new files below `TraceClass/`.
The public output of this card is the `TraceClass H` subtype and its
normed-space instances; downstream work should consume it rather than
reimplement it.

**Purpose:** replace the witness-basis/capability boundary by the actual
trace-class ideal.  The mathematical route is:

1. Keep the already-proved positive/self-adjoint basis-independence theorems.
2. Use the concrete polar factor in `TraceClass/Polar.lean`, which currently
   proves `polarFactor T * CFC.abs T = T` and `‖polarFactor T‖ ≤ 1`.
3. **Done:** prove the Hilbert--Schmidt double-sum lemma: if `R` is Hilbert--Schmidt,
   then `A * R` and `R * A` are Hilbert--Schmidt for bounded `A`, and the
   square-sum is basis independent.
4. **Done:** factor a trace-class operator as `(U * sqrt |T|) * sqrt |T|`; apply the
   Hilbert--Schmidt Cauchy--Schwarz estimate to prove absolute convergence of
   every diagonal series `∑ ⟪eᵢ, T eᵢ⟫`.
5. **Done:** swap the two Hilbert-basis sums by Tonelli/Fubini and prove that this
   diagonal sum is basis independent.  Derive linearity and cyclicity from
   the same absolutely convergent series, not from an unproved trace axiom.
6. **Partly done in `TraceClass/Space.lean`:** define the subtype
   `TraceClass H`, give it zero/addition/scalar action and the trace norm.
7. Prove `CompleteSpace (TraceClass H)` without assuming the `B(H)` predual.
   The natural route is to turn a trace-norm Cauchy sequence into an
   operator-norm Cauchy sequence using `opNorm_le_traceNorm`, take its
   operator-norm limit in `B(H)`, and prove that the limit is trace class by
   a summable telescoping-series argument.  Do not stop at an operator-norm
   limit: that would not prove completeness in the trace norm.
8. Import the finished space through `TraceAlgebra` and `Unbounded`, then
   package the trace pairing and bounded left/right actions at subtype level.

**Exported contract:** a complete normed complex space of trace-class
operators; basis-independent `trace`; bounded trace pairing; ideal estimates;
trace cyclicity.  No `TraceBasisIndependence` class may occur in the general
theorem statements.

**Do not do:** do not create the `WStarAlgebra (B(H))` instance, normal-state
representation, or weak-* integration here.

**Standalone test:** build `TraceClass.Polar` and `TraceClass`, then test the
pairing on rank-one operators and on the finite-dimensional instance.  The
test must include a non-self-adjoint operator.

### Card 2 — Concrete infinite-dimensional predual

**Files owned:** `WStarAlgebra/InfiniteDimensional.lean`,
`Unbounded/DensityOperator.lean`, and new support files in that directory.

**Depends on:** Card 1's trace-class subtype and pairing.

**Purpose:** identify the Banach predual of `B(H)` and eliminate the current
state/ideal capability records.

1. Define `A ↦ (T ↦ Tr (A*T))` as a continuous linear map from `B(H)` into
   the strong dual of trace class.  Prove its norm is exactly `‖A‖`, using
   rank-one trace-class operators for the lower bound.
2. Prove surjectivity: for every bounded functional on trace class, recover
   a bounded operator from its values on rank-one operators; prove the operator
   bound and equality of the functional with the trace pairing on finite-rank
   operators, then extend by trace-norm density.
3. Package the result as an isometric linear equivalence and use it as the
   chosen predual for `B(H)`.
4. Prove the density-operator theorem: `ρ ≥ 0` and `Tr ρ = 1` gives a state,
   and every normal state is represented by a unique such `ρ`.
5. Prove the trace-class right ideal and the matrix-coefficient/rank-one
   predual certificates from this concrete construction.

**Exported contract:** one canonical `WStarAlgebra (B(H))` instance under the
intended hypotheses, an isometric predual pairing, and the normal-state ↔
density-operator theorem.  Existing finite-dimensional bridges must use the
same public certificate names.

**Do not do:** do not define a second PVM calculus or add a theorem-specific
axiom/certificate to make a state compile.  The positive quadratic-form
package may remain as a useful application theorem, but it is not the final
predual proof.

**Standalone test:** instantiate the pairing on a finite-rank matrix unit,
prove the identity representation's matrix-coefficient certificate, and run
`#synth WStarAlgebra (B(H))` for the intended infinite-dimensional hypotheses.

### Card 3 — Weak-* bounded Borel calculus

**Files owned:** `Unbounded/WeakStarFunctionalCalculus.lean` and, if needed,
small interface changes in `Unbounded/NormalPVM.lean` and
`Unbounded/NormalAffiliated.lean`.

**Depends on:** the abstract predual/PVM interfaces; Card 2 for the concrete
`B(H)` smoke test, but not for the abstract construction.

**Purpose:** turn predual scalar integration into an actual bounded operator.

1. The current simple-function layer is green.  Keep its finite-additive
   proofs and do not reintroduce the old field-notation or ambiguous-`univ`
   elaboration errors.
2. Import the finished module through `Unbounded.lean` only after checking
   that the public import graph has no cycle.
3. Define the scalar functional obtained by integrating every predual
   functional against a bounded measurable function.
4. Prove boundedness uniformly in the predual functional and invoke the
   dual/predual representation theorem to obtain one operator.
5. Prove uniqueness and independence of approximating simple functions.
6. Prove constants, addition, scalar multiplication, multiplication, star,
   congruence a.e., indicators, pushforward, truncations, and resolvents.
7. Prove that indicators recover the original normal PVM and that the new
   calculus agrees with the existing norm-valued calculus whenever the latter
   is available.

The present file's `ofPredualPVM` is only an adapter to `ofNormalPVM`.  If the
project's claim is specifically a von Neumann/predual theorem, replace that
adapter with a construction through the P1/P2 pairing and prove its
representation and uniqueness theorem.  If the weaker `NormalPVM` calculus is
deliberately the chosen abstraction, record that decision in the module
docstring and make the public contract say so; do not call the adapter a proof
of a stronger predual representation result.

**Exported contract:** a constructor such as
`NormalBorelFunctionalCalculus.ofPredualPVM`, with exact measurability and
boundedness hypotheses, plus uniqueness and representation-compatibility
theorems.

**Do not do:** do not infer norm-valued sigma-additivity from weak-* or WOT
additivity.  Keep all limits in the topology actually supplied by the
predual theorem.

**Standalone test:** build the file independently; test the indicator of a
measurable set, a constant function, a bounded exponential, and a
pushforward.

### Card 4 — Closed operators and Cayley reconstruction

**Files owned:** `Unbounded/Cayley.lean`, `Unbounded/CayleySpectralData.lean`,
`Unbounded/Concrete.lean`, and
`Operators/SpectralTheory/UnboundedSpectralIntegral.lean`.

**Depends on:** no trace/predual work for its concrete Hilbert-space route.

**Purpose:** expose the actual unbounded spectral theorem with domains.

1. Stabilize the public closed/densely-defined operator boundary (the current
   supported representation is `LinearPMap`).
2. Prove both Cayley directions, inverse formulas, range/domain statements,
   and the self-adjointness criterion.
3. Construct and prove uniqueness of the WOT spectral PVM.
4. Define the maximal measurable operator with domain
   `x ↦ ∫ ‖f(λ)‖² dμₓ(λ) < ∞` and prove the identity function gives the
   original self-adjoint operator with equality of domains.
5. Prove the maximal integral is closed/self-adjoint where appropriate,
   and prove resolvent identities.

**Already available:** `Unbounded/ClosureAPI.lean` packages the essential
self-adjoint core, canonical closure, exact square-moment domain, Cayley
spectral data, and Stone generator interface.  New code should consume this
package rather than unfold its proof.

**Exported contract:** closure, self-adjointness, PVM uniqueness,
maximal-domain equality, identity reconstruction, resolvents, and measurable
functional calculus.

**Standalone test:** generic self-adjoint `LinearPMap`, including the domain
equality and identity-integral theorem, with no oscillator imports.

### Card 5 — Affiliation and representation bridge

**Files owned:** `Unbounded/Affiliated.lean`,
`Unbounded/NormalRepresentation.lean`, `Unbounded/NormalAffiliated.lean`,
`Unbounded/Representation.lean`.

**Depends on:** Cards 3 and 4, and Card 2 for the concrete `B(H)` case.

**Purpose:** make “affiliated” mean an actual represented closed
self-adjoint operator, not merely a spectral-data record.

1. Prove equivalence between a closed self-adjoint operator with spectral
   projections in the represented von Neumann algebra, a normal-functional
   PVM, and the bounded-transform commutant condition.
2. Prove uniqueness and functoriality under faithful normal representations
   and star-algebra equivalences.
3. Prove compatibility for indicators, bounded Borel functions,
   truncations, resolvents, and maximal unbounded integrals.
4. Replace `NormalBorelRepresentationCertificate` wherever its conclusion
   now follows from Card 3. Retain a certificate only if it is genuinely an
   external representation theorem, and document that boundary.

**Exported contract:** one conversion path between normal affiliated data and
closed operators, with no duplicate predual or silent WOT-to-norm upgrade.

**Standalone test:** represent a bounded self-adjoint operator and a
resolvent; verify that the spectral projections and represented operators are
definitionally connected by the public theorems.

### Card 6 — Dynamics and exponentials

**Files owned:** `Unbounded/Stone.lean`, `Operators/SpectralTheory/Stone.lean`,
and dynamics-only portions of `NormalRepresentation.lean`.

**Depends on:** Cards 3–5.

**Purpose:** make the unitary group of an unbounded self-adjoint operator a
first-class measurable-calculus result.

1. Define `exp (-Complex.I * t * T)` through bounded Borel calculus, never as
   an algebraic exponential of an unbounded element.
2. Prove unitarity, identity, group law, inverse/star law, and strong
   continuity.
3. Prove the generator statement with the exact sign:
   differentiability at zero is equivalent to membership in `Dom T`, and
   the derivative is `-Complex.I • T x` for `exp (-itT)`.
4. Prove compatibility with normal-affiliated representations and the
   concrete WOT spectral integral.

**Already available:** `Unbounded/StoneAPI.lean` exposes the exact public
zero-time derivative/domain equivalence for `e⁺ⁱᵗᵀ`, and
`Unbounded/NegativeStoneAPI.lean` exposes the corresponding `e⁻ⁱᵗᵀ` façade
with derivative `-iT`; this card should preserve and reuse those APIs.

**Standalone test:** generic self-adjoint `LinearPMap`, checking `U 0`,
`U (s+t)`, `U (-t) = U t⋆`, strong continuity, and the derivative/domain
equivalence.

### Card 7 — Oscillator application

**Files owned:** only `Unbounded/Example/Schwartz.lean`,
`Unbounded/Example/Spectrum.lean`,
`Unbounded/Example/HarmonicOscillatorSpectrum.lean`, and oscillator-specific
support.

**Depends on:** Cards 4–6; Card 1/2 only for any explicitly requested state or
affiliation application.

**Purpose:** instantiate the finished theory, without hiding foundation work
in special-function lemmas.

1. Prove the position and momentum operators on the common Schwartz core,
   their domains, symmetry, and canonical commutation relations where used.
2. Prove essential self-adjointness of the actual oscillator differential
   operator on Schwartz space and identify its closure with the intended
   `L²(ℝ)` Hamiltonian.
3. Obtain its actual spectral PVM and prove the identity maximal integral
   reconstruction.
4. Prove Hermite-function completeness here, as application-specific input,
   and derive the discrete projections and energy sum.
5. Derive the oscillator unitary group from Card 6 and connect it to the
   Hermite expansion.

**Do not do:** do not add foundational axioms, capability classes, or
certificate fields to make the oscillator compile.

**Standalone test:** build the oscillator target with no `sorry`, and test
the closure, PVM, identity integral, spectral projections, and unitary group.

### Card 8 — Integration and no-sorry audit

**Files owned:** public import aggregators, documentation, and small adapter
files only after Cards 1–7 have landed.

1. Build every card target separately, then build
`Physlib.QuantumMechanics.OperatorAlgebra.Unbounded`, then the full project.
2. Search declarations (not prose) for `sorry`, `admit`, and `axiom` in all
in-scope operator-algebra files.
3. Search for capability classes and TODOs.  Every remaining hit must either
be eliminated or be marked as an explicitly external theorem outside the
claimed general theory.
4. Check that no oscillator import is needed by foundational theory and that
there is only one intended infinite-dimensional `WStarAlgebra (B(H))`
instance.
5. Run smoke tests for multiplication operators, finite-dimensional PVMs,
generic self-adjoint `LinearPMap`s, an affiliated operator, and the oscillator.

**Completion criterion:** the public API has a concrete domain, concrete
closed self-adjoint operator, concrete WOT spectral PVM, maximal integral,
bounded Borel calculus, affiliated representation bridge, and unitary group;
none is asserted only by a capability placeholder.

## Live handoff status

The following work is already in the tree and should not be duplicated:

- P4's reusable closure package is available in `Unbounded/ClosureAPI.lean`.
  It packages essential self-adjointness, self-adjoint closure, the Cayley
  spectral data, maximal square-moment reconstruction, and the Stone generator
  interface.
- The positive trace-class subproblem is available in
  `TraceClass/PositiveIdeal.lean`, and the density-state positive trace
  formula is available in `Unbounded/DensityOperatorTraceBridge.lean`.
- The public `Unbounded` entry point builds with these additions.

`Unbounded/WeakStarFunctionalCalculus.lean` is standalone-green and is now
imported by the public entry point.  Its canonical `ofNormalPVM` construction
is the selected bounded calculus, and `ofPredualPVM` is a compatibility adapter
for predual-certified PVMs.  The concrete `B(H)` bridge and its representation
compatibility are available in `NormalRepresentationBoundedOperators.lean`.

The genuinely unfinished contracts are the full textbook equivalence between
representation-free affiliation and the bounded-transform/commutant
definition (P5), and the oscillator application (P7).  P1–P4 are complete at
their stated interfaces; P6's unitary group and generator-domain theorems are
proved, with only integration into any future stronger affiliation object
remaining.  A successful build still does not claim the full textbook
commutant characterization unless that external representation theorem is
added.

## Parallelization rule

Agents should work in support modules with acyclic imports. There is currently
no parallel ownership lock. If an interface must change, revise the named
public theorem/type and keep downstream code dependent on that interface, not
on private implementation details.

The critical path is:

~~~text
P1 trace class ──► P2 B(H) predual ──► P3 weak-* Borel calculus
                                      │
P4 Cayley/domain packaging ──────────┼──► P5 affiliation + unbounded calculus
                                      │
                                      └──► P6 dynamics integration
                                                     │
                                                     └──► P7 oscillator application
~~~

P1, P4, and most of the abstract part of P3 can proceed in parallel.  P2
depends on P1.  P5 and P6 depend on the contracts from P2/P3/P4.  P7 is an
application and must not become a place where foundational theorems are hidden.

## Copy/paste handoff assignments

These are the smallest independently mergeable work units.  An agent should
claim one unit, edit only its owned files, and leave the named public contract
at the end.  A unit is complete only when its target module builds with
`-Dwarn.sorry=false -Dweak.says.verify=true` and its acceptance tests pass.

### Assignment A — trace-class Banach space (complete)

`TraceClass/Space.lean`, `TraceClass/Completeness.lean`, and `TraceClass/Pairing.lean`
now provide the complete trace-class subtype, basis-independent trace,
cyclicity, ideal estimates, and bounded pairing. Do not duplicate this work.

### Assignment B — concrete `B(H)` predual (complete)

Own only `WStarAlgebra/InfiniteDimensional.lean`,
`Unbounded/DensityOperator.lean`, and support files in those directories.
The isometric equivalence and the one intended concrete `WStarAlgebra (B(H))`
instance and the density-operator ↔ normal-state representation theorem are
already implemented. The legacy
`TraceClassRightIdeal` and `DensityOperatorStateCertificate` interfaces remain
for source compatibility; do not edit A's files or
the PVM/affiliation files.

### Assignment C — weak-* / normal Borel calculus (complete)

Own `Unbounded/WeakStarFunctionalCalculus.lean` and, only if necessary,
`NormalPVM.lean` and `NormalAffiliated.lean`. The file currently builds and
supplies the norm-completion `NormalPVM` calculus, including indicators,
pushforwards, truncations, and resolvents. `NormalPVMTraceClass.lean` proves
predual σ-additivity for every trace-class functional in the concrete `B(H)`
instance and `normalPVM_toPredualPVM` packages the conversion. The abstract
normal-Borel calculus remains distinct from norm σ-additivity; do not infer the
latter from WOT additivity.

### Assignment D — closed operators, Cayley, and maximal integrals

Own `Unbounded/Cayley.lean`, `CayleySpectralData.lean`, `Concrete.lean`, and
`Operators/SpectralTheory/UnboundedSpectralIntegral.lean`.  Stabilize the
`LinearPMap` domain boundary; audit both Cayley directions, PVM uniqueness,
the square-moment domain equality, identity reconstruction, closedness, and
resolvents.  Consume `ClosureAPI.lean` where possible.  Do not edit trace or
normal-calculus files.  This assignment is independent of A–C.

### Assignment E — affiliation and representation

Own `Unbounded/Affiliated.lean`, `NormalRepresentation.lean`,
`NormalAffiliated.lean`, and `Representation.lean`.  Consume C and D to
replace `BorelFunctionalCalculus`, `AffiliationBridge`, and
`NormalBorelRepresentationCertificate` wherever their conclusions are
theorems.  Prove the represented closed self-adjoint operator, bounded
transform/commutant equivalence, uniqueness, functoriality, and compatibility
for projections, bounded functions, truncations, resolvents, and maximal
integrals.  Do not construct another predual or edit trace files.

### Assignment F — Stone dynamics

Own `Unbounded/Stone.lean`, `Operators/SpectralTheory/Stone.lean`, and only
dynamics portions of `NormalRepresentation.lean`.  Consume D's measurable
calculus and `StoneAPI.lean`; prove the public `e^{-itT}` laws, unitarity,
strong continuity, representation compatibility, and the exact generator
domain/sign statement.  Do not unfold or duplicate the Cayley proof.

### Assignment G — oscillator application

Own only `Unbounded/Example/Schwartz.lean`, `Example/Spectrum.lean`,
`Example/HarmonicOscillatorSpectrum.lean`, and oscillator-specific support.
Prove position and momentum on Schwartz space, essential self-adjointness of
the actual oscillator, closure identification, its PVM and identity integral,
Hermite completeness, discrete projections/energy sum, and the unitary group.
Consume A–F; never add a foundational axiom, capability class, or theorem
placeholder to make the example compile.

### Assignment H — final integration and audit

Own import aggregators, smoke-test files, and documentation only after A–G
land.  Build every target separately and the full project; perform a
declaration-level no-`sorry`/`admit`/`axiom` audit; classify every remaining
capability/TODO; and test multiplication operators, finite-dimensional PVMs,
generic self-adjoint `LinearPMap`s, affiliation, exponentials, and the
oscillator.  This assignment is the only one allowed to change imports solely
for integration.

### Current ownership boundary

No parallel ownership boundary is active. The local implementation has already
landed the trace-class completion, concrete predual, and identity normal bridge;
remaining work may be developed in whichever support module keeps the import
graph acyclic. The quadratic-form density-state package remains the safe
application route when a full normal-state representation theorem is not yet
needed.

## P1 — Construct the trace-class Banach space

**Owner:** one agent; owns `OperatorAlgebra/TraceClass.lean` and any new
`OperatorAlgebra/TraceClass/` support files.

**Goal:** replace the current capability records by an actual trace-class
space `𝒮₁(H)` for a complete complex Hilbert space `H`.

### Required results

1. **Already assembled:** `TraceClass/Space.lean` defines the subtype/type of
   trace-class operators with zero, addition, and scalar multiplication.
2. **Done:** `traceNorm` has its norm laws and
   `‖A T B‖₁ ≤ ‖A‖ ‖T‖₁ ‖B‖`; witness-level bounded actions and cyclicity are
   exported by `TraceAlgebra` and `IdealNorm`.
3. **Done:** `TraceClass/Completeness.lean` proves completeness of `𝒮₁(H)`
   without assuming an already-built `B(H)` predual.
4. **Done:** polar/Hilbert--Schmidt product arguments prove basis independence
   of the trace and trace norm for arbitrary trace-class operators.
5. **Done:** `TraceClass/Pairing.lean` proves and packages the bounded trace
   pairing:

   `A ↦ (T ↦ Tr (A T))`, with `‖φ_A‖ = ‖A‖`.

The positive conjugation sub-result is already exported as
`isTraceClass_star_mul_mul_of_nonneg` from `TraceClass/PositiveIdeal.lean`.

### Contract exported to P2

Export an actual complete `NormedSpace ℂ (TraceClass H)` and a theorem giving
the bounded trace pairing, with a stable name such as
`tracePairingContinuousLinearMap`.  Export the ideal estimate and trace
cyclicity statements needed to prove surjectivity in P2.  Do not define a
`WStarAlgebra (B(H))` instance in P1.

### Acceptance tests

- no `TraceBasisIndependence`, `TraceClassRightIdeal`, or similar capability is
  needed for the general theorem;
- arbitrary trace-class operators, not just positive ones, have
  basis-independent trace;
- a complete-space instance exists and the module builds without axioms or
  `sorry`.

## P2 — Build the infinite-dimensional `B(H)` predual and normal states

**Owner:** one agent; owns `OperatorAlgebra/WStarAlgebra/InfiniteDimensional.lean`
and `Unbounded/DensityOperator.lean` (coordinate with P1 rather than editing
P1's files).

**Depends on:** P1's concrete trace-class contract.

**Goal:** instantiate the chosen-predual architecture for bounded operators.

### Required results

1. **Done:** `TracePairingSurjectivity.lean` proves the trace pairing map

   `B(H) →L[ℂ] StrongDual ℂ (TraceClass H)`

   is an isometric linear equivalence.  Surjectivity is the key theorem: every
   bounded functional on trace class is `T ↦ Tr (A T)` for a unique bounded `A`.
2. **Done:** `WStarAlgebra/InfiniteDimensional.lean` registers
   `WStarAlgebra (B(H))` using trace class as its predual.  Avoid
   competing instances with the existing finite-dimensional prototype; use a
   dimension-gated or unified construction.
3. **Done:** the general trace-class product theorem supplies the right ideal,
   and `DensityOperatorTraceState.lean` proves the canonical product-trace
   state in arbitrary dimension. `DensityOperator.toNormalState` also proves
   weak-* continuity by the trace pairing and cyclicity:

   `ρ ≥ 0`, `Tr ρ = 1` ⇒ `A ↦ Tr (ρ A)` is a normal state.

4. **Done:** `Unbounded/NormalStateRepresentation.lean` proves that every
   weak-* continuous state on `B(H)` is represented by a positive trace-class
   operator of trace one, and proves uniqueness through the surjective trace
   pairing.  The proof uses Mathlib's weak representation theorem plus the
   public rank-one trace identities in `WStarAlgebra/RankOnePairing.lean`.
5. **Done:** rank-one matrix coefficients are represented by trace-class
   operators, yielding the existing
   `PredualMatrixCoefficientCertificate` for the identity representation.

### Contract exported to P3/P5

Export the `B(H)` predual pairing, the quadratic-form state, and the proved
normal-state/density-operator correspondence,
and the matrix-coefficient certificate.  P3 must not depend on a particular
   basis of `H`; P5 may use the pairing only through the exported interface.

### Acceptance tests

- `#synth WStarAlgebra (B(H))` works for the intended infinite-dimensional
  hypotheses;
- the finite-dimensional identity bridge and the infinite-dimensional bridge
  use the same public certificate API;
- no existential capability class is needed for the quadratic-form path; the
  product-trace compatibility path still exposes its explicit positivity
  certificate.

## P3 — Prove the weak-* bounded Borel functional calculus

**Owner:** one agent; owns `Unbounded/NormalPVM.lean`,
`Unbounded/NormalAffiliated.lean`, and a new
`Unbounded/WeakStarFunctionalCalculus.lean`.

**Depends on:** abstract `WStarAlgebra`/`PredualPVM` already present; P2 only
for the concrete `B(H)` instance and its tests.

**Goal:** turn the current `NormalBorelFunctionalCalculus` certificate into a
proved construction whenever the PVM has normal-functional additivity.

### Required results

1. **Done:** the concrete normal-representation bridge is done in
   `NormalRepresentationBoundedOperators.lean`; its generic `ofPredualPVM`
   constructor remains the explicit weak-* adapter boundary.
2. **Done:** `WeakStarFunctionalCalculus.lean` constructs the bounded calculus
   by norm completion of finite orthogonal spectral sums; it works for every
   `NormalPVM`, hence also for every `PredualPVM`.
3. **Done:** the full bounded Borel laws: congruence, constants, addition,
   multiplication, star, scalar multiplication, indicators, and unitary
   functions.
4. **Done:** measurable pushforward/functoriality and compatibility with the
   existing norm-valued `PVM` calculus.
5. **Done:** `NormalAffiliatedCanonical.lean` makes
   `NormalAffiliatedObservable` and `NormalAffiliatedOperator` the usable
   normal-functional entry points, with canonical bounded calculus,
   projections, resolvents, and (for real observables) unitary groups.
6. **Done:** representation compatibility for the canonical real and complex
   calculi is proved by common uniform simple-function approximation.  The
   constructors `NormalBorelRepresentationWitness.ofBridge` and
   `NormalOperatorBorelRepresentationWitness.ofBridge` derive the witnesses
   from a bridge, so no separate calculus certificate is needed.  The
   remaining representation boundary is only construction of a faithful normal
   bridge for an arbitrary chosen von Neumann algebra; `B(H)` is covered by
   the completed trace-class bridge.
7. **Done:** `NormalRepresentation` packages weak-star continuity of all
   bounded matrix coefficients.  Mathlib's weak representation theorem then
   constructs the predual coefficient certificate, the vector-state
   certificate, and the real/complex affiliation bridges.  The identity
   representation of `B(H)` is instantiated in
   `NormalRepresentationBoundedOperators.lean` by rank-one trace-class
   coefficients, including a faithful generic bridge.  Conversely,
   `NormalRepresentation.ofPredualMatrixCoefficientCertificate` turns any
   supplied predual coefficient certificate into a normal representation.

### Contract exported to P5/P6

Export a constructor (not a class field) of the shape
`NormalBorelFunctionalCalculus.ofPredualPVM`, plus uniqueness and
representation-compatibility theorems.  The theorem must state exactly which
measurability and boundedness hypotheses are required.

### Acceptance tests

- no `NormalBorelRepresentationCertificate` is needed merely to obtain the
   calculus from a predual-certified PVM;
- indicators recover the PVM exactly;
- all bounded laws are proved by the one construction, not by unrelated
   certificates;
- the old norm-valued calculus remains a specialization.

## P4 — Finish the closed-operator/Cayley package

**Owner:** one agent; owns `Unbounded/Cayley.lean`,
`Unbounded/CayleySpectralData.lean`, `Unbounded/Concrete.lean`, and
`Operators/SpectralTheory/UnboundedSpectralIntegral.lean`.

**Can proceed in parallel with P1–P3.**

**Implemented boundary:** `Unbounded/ClosureAPI.lean` now provides a stable
`EssentialSelfAdjointCore` package for the already-proved Cayley/domain route.
The items below remain the audit criteria for the underlying implementation;
new model files should consume the package instead of unfolding Cayley
coordinates.

**Goal:** make the concrete Hilbert-space theorem a self-contained public API,
not a collection of low-level certificates.  Much of this card already
builds; the remaining work is to verify the public theorem statements and
remove any accidental dependence on certificate-only routes.

### Required results

1. Introduce or stabilize a public closed densely-defined operator structure
   (or a documented `LinearPMap` equivalent) with explicit domain.
2. Prove the Cayley equivalence in both directions, including the exact
   inverse formulas and domain statements.
3. Prove the domain-aware unbounded spectral theorem:

   a self-adjoint operator equals the maximal square-moment integral of its
   unique WOT PVM, including equality of domains.

4. Prove uniqueness of the PVM from the operator/resolvent data and prove that
   the identity measurable function reconstructs the original operator.
5. Remove any remaining “certificate-only” public theorem where its content
   can be derived from the Cayley construction. Keep genuinely external input
   (for example, essential self-adjointness of a concrete differential
   operator) explicit.

### Contract exported to P5/P6

Export named theorems for closure, PVM uniqueness, maximal-domain equality,
resolvent identity, and measurable functional calculus. P5 should consume
these theorems without unfolding Cayley coordinates.

The eigenvector criterion is exported separately to model applications as
`LinearPMap.isEssentiallySelfAdjoint_of_dense_eigenvectors`. A model agent
must still supply domain membership, the eigenvalue equation, and totality;
those are not assumptions hidden in P4.

### Acceptance tests

- the theorem has an explicit domain equality;
- the closure of an essentially self-adjoint operator is the returned
   self-adjoint operator;
- no `sorry`/axiom/certificate is used to assert the spectral theorem itself.

## P5 — Complete affiliation and representation compatibility

**Owner:** one agent; owns `Unbounded/Affiliated.lean`,
`Unbounded/NormalRepresentation.lean`, `Unbounded/NormalAffiliated.lean`,
and `Unbounded/Representation.lean` after coordinating P3's interface.

**Depends on:** P3 and P4; P2 supplies the concrete `B(H)` instance.

**Goal:** connect representation-free affiliated spectral data to actual
closed operators and make the bridge usable.  The reusable operator equality
and canonical represented dynamics are now in
`Unbounded/AffiliationSpectralTheorem.lean`; remaining work is the stronger
textbook affiliation equivalence, if that is required by the project.

### Required results

1. For a faithful normal representation, prove equivalence between:

   - a closed self-adjoint operator whose spectral projections lie in the
     represented von Neumann algebra;
   - a normal-functional PVM in the algebra;
   - the corresponding bounded-transform/commutant affiliation condition.

2. Prove uniqueness and functoriality under faithful representations and
   `StarAlgEquiv`s.
3. Prove representation compatibility for indicators, bounded Borel
   functions, truncations, resolvents, and the maximal unbounded integral.
4. Decide and document whether the primary abstract object is
   `NormalAffiliatedObservable` or the older norm-valued
   `AffiliatedObservable`; provide a proved conversion only where the required
   additivity really exists.
5. **Done for the calculus portion:** `NormalBorelRepresentationCertificate.ofBridge`
   and `NormalOperatorBorelRepresentationCertificate.ofBridge` derive the
   canonical certificates from any normal bridge.  Retain the structures only
   as compatibility packages; the genuinely external boundary is construction
   of the normal bridge itself.

### Acceptance tests

- an affiliated observable represented on `H` yields exactly one closed
   self-adjoint operator;
- its represented spectral projections and resolvents agree by theorem;
- no theorem silently converts WOT/normal-functional additivity into norm
   additivity.

## P6 — Finish unbounded measurable calculus and Stone dynamics

**Owner:** one agent; owns `Unbounded/Stone.lean`,
`Operators/SpectralTheory/Stone.lean`, and the dynamics portions of
`NormalRepresentation.lean` after P3/P5 contracts stabilize.

**Depends on:** P3, P4, and P5.

The existing Stone proof establishes the strong derivative and its converse;
`Unbounded/StoneAPI.lean` now exposes that zero-time generator/domain theorem
as a direct public API.  The remaining P6 work is to integrate it with the
chosen bounded Borel calculus and affiliated representation, and to audit the
sign/domain statements in the public imports—not to duplicate the existing
derivative proof.

**Goal:** make `e^{-itT}` and arbitrary measurable functions of an affiliated
self-adjoint operator first-class API results.

### Required results

1. Define the maximal operator for every measurable real function with the
   exact square-integrability domain.
2. Prove composition, adjoint/self-adjointness where applicable, bounded
   restrictions, and the identity-function theorem.
3. Define `exp (-Complex.I * t * T)` through bounded Borel calculus and prove
   unitarity, identity, group law, inverse/star law, and strong continuity.
4. Prove the Stone generator theorem with the correct sign and domain:
   derivative at zero exists exactly on `Dom(T)` and equals the appropriate
   scalar multiple of `T`.
5. Prove compatibility between abstract affiliated exponentials and concrete
   WOT spectral integrals.

### Acceptance tests

- no formal exponential of an unbounded algebra element is used;
- `U 0 = 1`, `U (s+t) = U s * U t`, and strong continuity are public theorems;
- the generator/domain statement is explicit.

## P7 — Oscillator application and final dependency cleanup

**Owner:** separate application agent; owns only
`Unbounded/Example/Schwartz.lean`, `Example/Spectrum.lean`,
`Example/HarmonicOscillatorSpectrum.lean`, and oscillator-specific support.

**Depends on:** P4–P6.  This package must not edit foundational theory files to
make the oscillator compile.

### Required results

1. Prove the position and momentum differential operators on the common
   Schwartz core, including their algebraic relations.
2. Prove essential self-adjointness of the actual oscillator differential
   operator on Schwartz space and identify its closure with the intended
   `L²(ℝ)` Hamiltonian.
3. Obtain its actual unbounded spectral measure from P4/P5 and reconstruct
   the closure by the identity integral.
4. Prove Hermite-function completeness only here, as special-function input,
   and derive the explicit discrete spectral projections and energy sum.
5. Derive the oscillator unitary group from P6 and prove its relation to the
   Hermite expansion.

## Final audit (must be run after all packages)

1. Build the public entry points and then run the full `lake env lake build`.
2. Search all in-scope general-theory `.lean` files for actual declarations of
   `sorry`, `admit`, or `axiom`; ignore prose/comments but investigate every
   real hit.
3. Search for capability classes and TODOs.  Each remaining one must either be
   eliminated by P1–P7 or be explicitly documented as an external theorem
   outside the general theory's claimed scope.
4. Check public imports and ensure no oscillator file is required to establish
   a foundational theorem.
5. Run small API examples for: a multiplication operator, a finite-dimensional
   projection/PVM, a generic self-adjoint `LinearPMap`, and the oscillator.
6. Do not claim completion merely from compilation: verify domain equality,
   PVM uniqueness, bounded/unbounded calculus compatibility, affiliation, and
   the Stone generator theorem individually.

The repository contains unrelated sorries in other subject areas.  The final
claim should be scoped to the general unbounded/operator-algebra modules unless
those unrelated files are separately repaired.
