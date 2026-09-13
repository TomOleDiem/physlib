# Single-generator JB analysis

The authoritative architecture and global milestones are in
[`../JB_ROADMAP.md`](../JB_ROADMAP.md). This note records only the local state of the
single-generator analytic construction.

## Implemented

```text
Jordan powers
    -> power-associativity
    -> algebraic generatedByOne a
    -> CommRing / Algebra ℝ structure
    -> closedGeneratedByOne a
    -> NormedRing / NormedAlgebra ℝ / CompleteSpace
    -> jordanSpectrum a
    -> compactness of jordanSpectrum a
    -> uniform square norm and exact powers-of-two norm growth
```

The closure and all analytic structure are abstract in a coherent `NormedJordanAlgebra`; ambient
completeness is requested only for the complete-space instance. The spectrum is canonically the
ordinary real-algebra spectrum of the bundled generator inside its closed generated algebra.

## Remaining

1. Establish the JB-specific spectral facts not true for an arbitrary real Banach algebra,
   beginning with nonemptiness and the correct spectral-radius/norm relation. The square norm and
   powers-of-two norm identities are now available in `Uniform.lean`.
2. Implement one of the two sound routes isolated in `CFC_AUDIT.md`: a real uniform-algebra
   representation theorem, or a named complexification proved to be a commutative Cstar algebra.
3. Construct a bundled unital isometric homomorphism
   `C(jordanSpectrum a, ℝ) -> ClosedGeneratedByOne a`.
4. Prove that it sends the coordinate function to the generator and is onto.
5. Derive continuous functions of `a`, then `abs`, positive/negative parts, and positive square
   roots.

There is deliberately no placeholder CFC declaration. In particular, no arbitrary set may be
passed in as “the spectrum,” and no theorem in this layer may be supplied by a new axiom.
