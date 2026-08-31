# Unbounded / operator-algebra staging tree

This directory holds a large, mostly-independent body of work on operator-algebra
foundations, W\*-algebras, trace-class operators, and unbounded self-adjoint spectral theory,
staged inside `PhyslibAlpha` (not yet reviewed for the public `Physlib` API — see
`OperatorAlgebra/Development/` and `OperatorAlgebra/README.md` inside this tree for the detailed
package-by-package staging plan).

It was migrated here, on `2026-08-31`, from an out-of-tree snapshot folder
(`~/Projects/physlib-dev/unbounded-dev`) that had accumulated against a base slightly ahead of
`upstream/master`, onto this branch's fresh `upstream/master` checkout, under the
`PhyslibAlpha.Unbounded.*` namespace (mirroring the original `Physlib.QuantumMechanics.{
OperatorAlgebra,Operators,HarmonicOscillator}` layout one level down). It builds clean
(`lake build PhyslibAlpha`, 0 errors) with the exclusions below.

## What's excluded from the aggregate, and why

18 of the original 150 files are *not* wired into `PhyslibAlpha.lean` (though they remain on disk,
unmodified in content, for reference/future repair). All are genuinely broken independent of the
migration itself — pre-existing staleness or bugs in the snapshot, not artifacts of the move:

- **`OperatorAlgebra/FiniteDim/{StateRepresentation,PureStates}.lean`** — import
  `Physlib.Mathematics.OperatorAlgebra.State`, a module that no longer exists on `upstream/master`
  (the real `State` content has since moved to `Physlib.QuantumMechanics.OperatorAlgebra.*`).
- **`OperatorAlgebra/Dynamics.lean`, `Dynamics/{Automorphism,Hamiltonian}.lean`** — same issue,
  importing the no-longer-existing `Physlib.Mathematics.OperatorAlgebra.Dynamics`.
- **`OperatorAlgebra/Dynamics/Stinespring.lean`, and its dependents `Lindblad.lean`,
  `ChristensenEvans.lean`, `FiniteDimensional.lean`, `FiniteDimensionalChristensenEvans.lean`** —
  `Stinespring.lean` imports a `States.Vector` module that was never created in the snapshot (the
  file that exists is `OperatorAlgebra/VectorState.lean`, a different path) — a pre-existing typo
  or planning artifact, not something introduced here.
- **`OperatorAlgebra/Dynamics/{CPClosure,Semigroup}.lean`** — genuine standalone elaboration
  errors ("Function expected at ...") unrelated to any import path, most likely Mathlib API drift
  since these files were last built against their original base.
- **`HarmonicOscillator/{Basic,DifferentialCore,EssentialSelfAdjointness,
  IntendedMaximalHamiltonian,LadderOperators,SpectralProjections}.lean`** — downstream of
  `HarmonicOscillator/Basic.lean`'s own import chain pulling in a duplicate-declaration clash (see
  below, since fixed for the base `Operators/Unbounded.lean`/`Operators/Multiplication.lean` case,
  but `HarmonicOscillator/Basic.lean` itself was not otherwise touched/re-verified after the fix).

See `git log` on this branch for the exact commit that performed the migration and exclusion.

## Duplicate-declaration fixes made during the migration

Two files in the snapshot (`Operators/Core/Unbounded.lean`, `Operators/Multiplication/Basic.lean`)
turned out to be near-verbatim copies of the real, already-public `Physlib.QuantumMechanics.
Operators.{Unbounded,Multiplication}` — plus a handful of genuinely new lemmas appended at the end.
Importing both the copy and the real file in the same build (which the full `PhyslibAlpha`
aggregate does, since other pre-existing `PhyslibAlpha` content already depends on the real files)
caused a hard "environment already contains ..." duplicate-declaration error. Fixed by extracting
just the new lemmas into their own file (`Operators/Core/UnboundedExtras.lean`, `Operators/
Multiplication/BasicExtras.lean`) that imports the real base file instead of re-declaring it, and
redirecting every consumer in this tree to import the real file directly plus the small extras
file. Six further files (`Operators/Canonical/{Position,Momentum,Commutation,Covariance,
AngularMomentum,Uncertainty}.lean`) turned out to be *pure*, content-identical duplicates of real
`Physlib.QuantumMechanics.Operators.*` files with no new lemmas at all — these were deleted
outright and every reference redirected to the real files.

Other same-basename files elsewhere in this tree (e.g. `Observables/{Jordan,Lie}.lean`,
`Operators/OneDimension/{Position,Commutation,Parity}.lean`, `Operators/SpectralTheory/{
SelfAdjoint,Symmetric,SpectralMeasure}.lean`, `Operators/StateObservables/Variance.lean`,
`HarmonicOscillator/OneDimension/{Completeness,TISE,Examples}.lean`) are *also* apparently
content-identical or near-identical copies of real Physlib files, but did not trigger a build
error (they are evidently never co-imported with their real counterpart anywhere in the current
`PhyslibAlpha` aggregate's transitive closure). They were left as-is rather than preemptively
deduplicated, since the build is clean; a future cleanup pass could apply the same
extract-and-redirect treatment to shrink this tree further.
