# Unbounded spectral theory: consolidation plan

## Decision

Keep `WOTSpectralMeasure` and the domain-aware spectral-integral construction as the canonical
unbounded layer.  They already express strictly more of the information needed by applications
than a resolvent-only or bounded-Borel presentation: in particular, they retain the exact maximal
square-moment domain of an unbounded observable.

The linked `adambornemann-glitch/Spectra` development is valuable as a source of proof
organization and as an independent validation of the Cayley route.  It must not be imported or
copied as a second public operator/PVM hierarchy.  Its `ProjValMeasure` and this project's
`WOTSpectralMeasure` overlap substantially but make different representation choices.  The
existing local type already carries weak-operator countable additivity and supports the bounded
and unbounded integrals used below.

The right common abstraction is nevertheless real and should be introduced before either the
abstract JBW Borel calculus or further concrete unbounded façades.  It is **not** a Hilbert-space
operator-valued measure.

```text
MeasurableProjectionResolution α J
  E : measurable sets of α → projections of J
  E(∅) = 0, E(univ) = 1, E(S ∩ T) = E(S) * E(T)
  E(⋃ₙ Sₙ) = supₙ E(Sₙ)                 (disjoint measurable family)
```

Here the last equality is order convergence in a monotone-complete ordered Jordan algebra.  This
interface is now implemented as `MeasurableProjectionResolution` in
`JordanOrderUnit/ProjectionResolution.lean`: it is an extension of the existing
`EffectValuedMeasure`, adding Jordan idempotence and the intersection-product law without
duplicating countable additivity.  Its JBW companion supplies normal-state scalar probability
laws and the separating-family extensionality theorem.  The interface is deliberately independent
of Hilbert spaces, complex scalars, Cayley maps, or an unbounded operator domain.

`WOTSpectralMeasure α H` is then a **concrete realization target**, not the generic definition:
its values are weak-operator projections on a Hilbert space and its vector-measure countable
additivity proves the generic projection-resolution laws.  Spectra's `ProjValMeasure` has the
same role, but is not imported because it is another Hilbert-special carrier.

## What exists here

```text
WOTSpectralMeasure α H
  ├─ boundedIntegral: bounded measurable calculus
  ├─ maximalSpectralIntegral: unbounded measurable calculus
  ├─ spectralSquareMomentDomain: exact operator domain
  └─ Cayley map/inverse map

bounded normal CFC spectral data
  └─ cayleyRealSpectralMeasure
       └─ DomainAwareSelfAdjointSpectralTheorem T μ
            ├─ T.domain = spectralSquareMomentDomain μ
            ├─ maximal spectral integral realizes T
            └─ expUnitaryGroup and the domain-aware Stone API
```

The public self-adjoint endpoint is `unboundedSpectralTheorem`; the reusable uniqueness endpoint
is the maximal-spectral-integral characterization in `SpectralIntegral/SpecTheorem.lean`.

## What Spectra contributes conceptually

Spectra's Cayley development isolates a useful three-stage proof spine:

```text
self-adjoint LinearPMap
  → bounded unitary Cayley transform
  → bounded continuous/Borel calculus
  → pushforward along the inverse Cayley map
  → spectral theorem and Stone group
```

This project already implements the same mathematical route, but with a stronger final package:
the inverse-Cayley measure is tied to the square-moment domain and then to a maximal unbounded
integral.  That extra domain equality must remain the non-negotiable boundary.  A weak integral
identity alone cannot identify an unbounded operator.

The directly reusable *ideas*, not a duplicate API, are:

1. Treat the Cayley transform as the bounded-normal gateway and keep all Borel work downstream
   of it.
2. State uniqueness through scalarization: diagonal/resolvent data determine the PVM by complex
   polarization and Cauchy-transform injectivity.
3. Keep bounded calculus, unbounded measurable calculus, and the Stone-generator theorem as
   separate vertical slices.
4. Expose a compact public resolvent API only after proving it agrees with the spectral
   multiplier; do not make applications reconstruct domain witnesses.

## Consolidation slices

### U1 — make the existing public spectral theorem easy to consume

Add a focused façade module with only these exports:

- the canonical measure supplied by `unboundedSpectralTheorem`;
- the exact domain equivalence;
- the coordinate reconstruction theorem;
- the non-real resolvent multiplier formula;
- the bounded measurable calculus and its continuous restriction.

This is packaging only: no new spectral representation is defined.

### U2 — measurable functional calculus as a domain-aware construction

For a measurable `f : ℝ → ℂ`, make the domain

```text
{x | ∫ ‖f(λ)‖² dμ_x(λ) < ∞}
```

the public domain of `f(T)`, prove agreement with `maximalSpectralIntegral`, and provide the
bounded specialization through `boundedIntegral`.  The coordinate function recovers `T`.

### U3 — resolvent façade

Specialize U2 to `(λ - z)⁻¹` for `Im z ≠ 0`.  Prove the inverse/range formula once and package a
canonical bounded operator.  This is where the concise Cayley/resolvent presentation used by
Spectra is useful, but the proof must go through the local maximal-integral domain theorem.

### U4 — Stone equivalence

Use the established `expUnitaryGroup` and its differentiability/domain API to state the exact
operator-level Stone theorem: the group generated by the spectral measure has generator `iT` on
precisely `T.domain`.  Keep construction from a given self-adjoint operator distinct from the
converse construction of a generator from an arbitrary strongly continuous unitary group.

### U5 — JBW connection

Only after the abstract JB Stage C exact-cone and positive-root results are complete, define
`MeasurableProjectionResolution` and the **bounded** JBW Borel calculus by simple functions and
monotone completion.  Its universal laws are addition, multiplication on each one-observable
commutative sector, positivity, and normal-state scalarization.  The Hilbert-space
`WOTSpectralMeasure` development is then the concrete special-JBW realization, not an import of
operator/Cstar facts into abstract Jordan theory.

Unbounded measurable functions are a separate, represented/affiliated-operator layer: their
domains are square-integrability domains of scalarized spectral measures.  That construction is
meaningful for a Hilbert representation, but not for a bare JBW algebra; it must therefore sit
above the bounded JBW calculus rather than distort the JBW core.

## Boundaries to preserve

- No second `ProjValMeasure` type in PhyslibAlpha.
- No Cstar import into the abstract `JordanOrderUnit/JB` or `JBW` layers.
- No claim that a weak reconstruction formula determines an unbounded operator without the
  square-moment-domain equality.
- No reverse normality-transport theorem until its directed-set domain is matched exactly.
- No unbounded calculus API with arbitrary functions unless its domain/integrability condition is
  explicit.
- The Cayley transform is a complex Hilbert/operator realization technique, not an abstract-JBW
  primitive.  Abstract JBW spectral theory proceeds from order suprema and projections; Cayley
  is used only to construct or compare its concrete special realization.
