# Operator-algebra development area

This directory contains experimental API that is not part of the upstream-facing
`OperatorAlgebra` namespace yet.  A module here must be independently useful and
must not be imported by `Physlib.lean` or by the small master-facing modules.

The promotion rule is deliberately strict: a development module moves into the
public tree only after its definitions, dependencies, and intended use are clear,
and after a small downstream example uses it without importing unrelated theory.

## First slices

`States` is for state-independent state vocabulary and elementary expectations.
It must not depend on W⋆-algebras, trace class, density-operator analysis, or
unbounded operators.

`Measurement` is for finite-outcome measurements first.  The initial public
candidate is the existing finite `POVM` idea: effects indexed by a finite type
whose sum is the identity.  Its Born probabilities use an ordinary `State`.

General measurable PVMs and POVMs are deliberately later.  Their countable
additivity needs a specified topology (norm, strong, or ultraweak), so the name
must not hide that choice.  State-dependent distributions belong in a separate
statistics module rather than in the measurement primitive.

W⋆/normal-state, trace-class, affiliation, and unbounded spectral developments
remain separate research layers until these small slices are stable.

## Promotion checklist

* imports only the layer immediately below it;
* contains no `sorry`, placeholder axiom, or hidden capability assumption;
* has a short public interface and at least one downstream example;
* does not enlarge the default `Physlib` import surface;
* has a clear path to a master-facing filename and namespace.

The development area is a staging boundary, not a second permanent public API.
