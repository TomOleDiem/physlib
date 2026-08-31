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
(`lake build PhyslibAlpha`, 0 errors, 0 `sorry`) with the exclusions below.

## The headline result

**Read `HarmonicOscillator/Summary.lean` first.** It is the whole story — plain `theorem`s, mostly
one-line citations of results proved elsewhere, no operator-algebra jargon in the statements: the
energy-level formula, the textbook Hermite-times-Gaussian eigenfunction formula, essential
self-adjointness, each eigenfunction genuinely being an eigenvector, pure point spectrum, the full
iff-statement tying it together, and — the one place with a short new proof — a genuine
time-evolution operator (unitary, one-parameter group, built by Stone's theorem from the
self-adjoint closure) together with the Schrödinger equation on the oscillator's own eigenstates.
The file's own doc comment is explicit about what that last part does *not* yet claim: the closed
form `U(t) ψₙ = exp(-iEₙt) • ψₙ` for all `t`, and the Heisenberg-picture adjoint action of `U(t)`
on an operator, both need a further eigenvector/functional-calculus lemma that isn't in this tree
yet.

That last one is `DifferentialSpectrum.lean`'s `harmonicOscillator_isEigenvalue_iff`: for the
*actual* physical Hamiltonian of the one-dimensional quantum harmonic oscillator (a genuine
unbounded differential operator on `L²(ℝ)`, essentially self-adjoint, built from first principles
in `DifferentialCore.lean`), a real number `E` is an energy level if and only if `E = ℏω(n + ½)`
for some natural number `n` — stated purely in eigenvector/eigenvalue language, with no bespoke
spectral-measure vocabulary in the statement itself. Completeness of that list (no continuous or
scattering spectrum) is `H_pp_eq_top`, used internally in the proof.

### Why there seem to be several "harmonic oscillators"

This tree is not the only place the quantum harmonic oscillator gets formalized, and that's worth
being upfront about rather than leaving as a surprise:

- `Physlib.QuantumMechanics.OneDimension.HarmonicOscillator` (`Basic.lean`/`TISE.lean`/
  `OneDimension/Examples.lean`) is a **1d, pointwise-formula model**: `eigenValue`, `eigenfunction`
  as plain `ℝ → ℂ` functions, `schrodingerOperator` as a bare differential expression — no Hilbert
  space, no self-adjointness, nothing about *why* those formulas are the right ones. This is
  `OldOscillator` in the files below.
- `Physlib.QuantumMechanics.HarmonicOscillator` (`Basic.lean`/`Eigenstates.lean`/
  `LadderOperators.lean`/`Vacuum.lean`) is the **`d`-dimensional Hilbert-space model**: genuine
  `𝓢(Space d, ℂ)` Schwartz-space eigenfunctions, ladder operators, a real vacuum state — but
  (before this tree) it left essential self-adjointness and the honest energy-level statement as
  `informal_lemma`/`informal_definition` placeholders.
- **This tree's `HarmonicOscillator/{DifferentialCore,EssentialSelfAdjointness,
  IntendedMaximalHamiltonian,SpectralProjections,DifferentialSpectrum}.lean`** is what actually
  connects the two: it builds the real unbounded differential operator at `d = 1` (via
  `Physlib.QuantumMechanics.HarmonicOscillator`'s own machinery), proves it's essentially
  self-adjoint, and shows its eigenvectors are exactly `OldOscillator`'s transported Hermite
  functions — discharging those placeholders and finally justifying the 1d model's formulas as
  genuinely correct, not just asserted.

`HarmonicOscillator/Summary.lean` is the file to read if you don't want to track any of that by
hand — it states the end result in isolation and cites straight through to whichever of the three
layers actually proved each piece.

## What's excluded from the aggregate, and why

122 of the 127 files here are wired into `PhyslibAlpha.lean` and build clean. 5 remain excluded
(kept on disk, unmodified), all rooted in the same single cause:

- **`OperatorAlgebra/Dynamics.lean`, `Dynamics/{Automorphism,Hamiltonian}.lean`,
  `FiniteDim/{StateRepresentation,PureStates}.lean`** — import `Physlib.Mathematics.
  OperatorAlgebra.{Dynamics,State}`, modules that no longer exist on `upstream/master` (that
  content has since moved to `Physlib.QuantumMechanics.OperatorAlgebra.*`). A `Physlib.Mathematics.
  OperatorAlgebra.Dynamics` does exist on the separate, still-unmerged `hamiltonian-dynamics`
  worktree/branch, and a `Physlib.Mathematics.OperatorAlgebra.State` exists in an old snapshot
  (`unbounded-dev/qubit-snapshot`) — reconciling either into this tree is a further, separate
  migration, not attempted here.

Everything else that was excluded in the first migration pass has since been fixed:

- **`OperatorAlgebra/Dynamics/{CPClosure,Semigroup}.lean`** and their dependents (`Lindblad.lean`,
  `ChristensenEvans.lean`, `FiniteDimensional.lean`, `FiniteDimensionalChristensenEvans.lean`,
  `Stinespring.lean`) — now build clean. Root causes and fixes:
  - `CPClosure.lean` used `completelyPositiveMap_comp` (composition of two completely positive
    maps) without ever defining it — a genuine missing definition, not a naming/import issue.
    Added it for real: entrywise composition on `CStarMatrix` amplifications, positivity transported
    through `CStarMatrix.map_apply`-based extensionality (`CStarMatrix.map_map`'s stated pattern
    uses the underlying `Matrix.map`, not `CStarMatrix.map`, so a direct `rw` doesn't fire — proved
    the composition identity by `ext`/`simp` instead).
  - `Semigroup.lean` applied `Channel A A`-valued fields directly as functions (`map t a`); `Channel
    A₁ A₂ := {φ : A₁ →CP A₂ // φ 1 = 1}` is a bare `Subtype`, and Lean does not automatically chase
    a `Subtype.val` coercion *and then* a `FunLike` coercion together. Fixed at the root: added
    `instCoeFunChannel` (`OperatorAlgebra/Basic.lean`) so `φ a` elaborates directly for `φ :
    Channel A₁ A₂` — this alone resolved 71 of `Semigroup.lean`'s 75 errors; the rest were one
    `.toContinuousLinearMap` field-projection through the same subtype (routed through
    `completelyPositiveMap_toContinuousLinearMap` instead) and one now-redundant trailing `rfl`.
  - `Stinespring.lean`'s bad import (`States.Vector`, never created — the real file is
    `OperatorAlgebra/VectorState.lean`) was a one-line redirect. Its two `⟨0, by simp⟩`/`⟨‖L‖,
    ...⟩` parse failures ("unexpected token ','; expected '⟩'") are the same anonymous-constructor
    parse quirk hit earlier this project in the real import chain — fixed with `Subtype.mk`/
    `Exists.intro` instead of `⟨…⟩`. `Lindblad.lean` had one more instance of the same pattern.
- **`HarmonicOscillator/{Basic,DifferentialCore,EssentialSelfAdjointness,
  IntendedMaximalHamiltonian,LadderOperators,SpectralProjections}.lean`** — now build clean.
  `HarmonicOscillator/Basic.lean` turned out to be a *completed* version of the pre-existing,
  already-public `PhyslibAlpha.QuantumMechanics.HarmonicOscillator.Basic` (upstream/master's copy
  still had `informal_lemma hamiltonian_essentially_self_adjoint`/`informal_definition
  toQuantumSystem` placeholders; ours has real proofs, pointing at
  `EssentialSelfAdjointness.lean`). Deleted our duplicate, redirected consumers to the real file,
  and replaced the real file's two `informal_lemma`/`informal_definition` stubs with a doc comment
  pointing at `EssentialSelfAdjointness.lean` (they're superseded, not merely duplicated).
  `LadderOperators.lean` looked like the same situation (same file name, same pre-existing
  `PhyslibAlpha.QuantumMechanics.HarmonicOscillator.LadderOperators`) but turned out to declare an
  entirely disjoint set of names (confirmed via a name-diff) — a genuinely separate, later,
  independent elaboration of `d`-dimensional ladder operators, not a duplicate at all; it needed no
  fix beyond pointing its own `Basic.lean` import at the real file.
- 20 further pure-or-near-pure duplicate files (`Observables/{Jordan,Lie}.lean` excepted — see
  below — plus `Operators/OneDimension/{Position,Commutation,Parity}.lean`, `Operators/
  SpectralTheory/{SelfAdjoint,Symmetric,SpectralMeasure,Basic}.lean`, `Operators/
  {OneDimension.Momentum,OneDimension.Unbounded,StateObservables.ExpectedValue,
  StateObservables.IsEigenvector}.lean`, `HarmonicOscillator/OneDimension/{Basic,Completeness,
  Eigenfunction,Examples,TISE}.lean`) were deleted outright, with every reference redirected to the
  real `Physlib.QuantumMechanics.*` files.

## Duplicate-declaration fixes made during the migration

Several files in the snapshot turned out to be near-verbatim copies of already-public
`Physlib.QuantumMechanics.*` files, plus a handful of genuinely new lemmas appended at the end.
Importing both the copy and the real file in the same build (which the full `PhyslibAlpha`
aggregate does, since other pre-existing `PhyslibAlpha` content already depends on the real files)
caused a hard "environment already contains ..." duplicate-declaration error each time. Fixed with
one of two patterns depending on how much was genuinely new:

- **Superset forks** (`Operators/Core/Unbounded.lean`, `Operators/Multiplication/Basic.lean`): the
  new lemmas were extracted into their own small file (`Operators/Core/UnboundedExtras.lean`,
  `Operators/Multiplication/BasicExtras.lean`) that imports the real base file instead of
  re-declaring it; every consumer redirected to import the real file directly plus the extras file.
- **Pure duplicates** with nothing new (`Operators/Canonical/{Position,Momentum,Commutation,
  Covariance,AngularMomentum,Uncertainty}.lean` and the 20 files listed just above): deleted
  outright, every reference redirected straight to the real file.

`Observables/{Jordan,Lie}.lean` are the one pair kept as genuine duplicates rather than
redirected: `OperatorAlgebra/Basic.lean` here is itself a *deliberately* modified fork of the real
one (`State`/`POVM` moved out to `States/`/`Measurement/`, per this tree's own staging-plan docs),
so anything importing the real `Observables.{Jordan,Lie}` would transitively pull in the real
(unmodified) `Basic.lean` alongside ours — a second, different collision. Kept our copies pointing
at our `Basic.lean`, consistent with the rest of this tree.
