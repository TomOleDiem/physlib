# TODO: general POVMs

## TL;DR for the implementation agent

Replace the finite-only POVM in `Basic.lean` with a genuinely general POVM built
on Mathlib's measure theory. Reuse the existing infrastructure; do not
reimplement σ-additivity.

The mathematical target is a normalized positive operator-valued measure

\[
  M : \Sigma_X \to A_{\rm sa},
  \qquad M(S) \geq 0, \qquad M(X) = 1.
\]

Values must live in an additive operator/observable space. Do **not** make a
measure valued in `Effect A`: effects are not closed under addition. Preserve

```lean
Effect A := Set.Icc (0 : Observable A) 1
```

as the notion of one yes/no event, and prove that every measurable `S` has an
effect `M S` as a consequence of positivity and normalization.

## Investigation required before coding

- Read and reuse `Mathlib.MeasureTheory.VectorMeasure.Basic`. In particular,
  investigate `VectorMeasure`, its measurable-set conventions, σ-additivity,
  `restrict`, `map`, and `mapRange`.
- Check the available measurable-space APIs and the exact continuity
  hypotheses required by `VectorMeasure.mapRange`.
- Investigate Mathlib's weak operator topology for concrete Hilbert-space
  operators: `ContinuousLinearMapWOT` / `H →WOT[ℂ] H`. Verify the convergence
  characterization by matrix elements
  `⟪y, A_i x⟫ → ⟪y, A x⟫`.
- Explicitly resolve whether `ContinuousLinearMapWOT` has enough order,
  positivity, self-adjointness, star, and additive infrastructure for a
  pleasant POVM wrapper. Do not assume that the existence of WOT alone makes
  `VectorMeasure` plus positivity work out of the box.
- Inspect the existing `Operators/SpectralTheory/SpectralMeasure.lean` for
  reusable patterns, while keeping spectral measures separate from general
  POVMs.

## Topology and scope warning

`VectorMeasure X (Observable A)` uses the norm topology and therefore expresses
norm σ-additivity. This is stronger than the standard infinite-dimensional
POVM notion. Do not silently describe that construction as the fully general
physical definition.

For concrete `B(H)`, investigate a WOT-based formulation, since WOT is the
appropriate topology for standard POVM σ-additivity. If Mathlib cannot support
the desired order/positivity API directly, document the limitation and keep
the abstraction honest rather than hiding a stronger norm-topology assumption.

## Measurement-statistics bridge

The central API theorem should construct, from a state `ω` and POVM `M`, the
ordinary scalar probability measure

```text
μ_{ω,M}(S) = ω(M(S))
```

This bridge should be the foundation for probabilities, integration,
expectations, moments, pushforwards, and related measurement statistics, all
using ordinary Mathlib `MeasureTheory`. Observables/Jordan covariance remain a
separate operator-level statistics API.

At minimum, establish the scalar measure laws, nonnegativity, and
normalization (`μ_{ω,M} univ = 1`), with the necessary measurability and
coercion details made explicit in the Lean API.

## Finite case compatibility

The existing definition

```text
x ↦ E_x,     ∑ x, E_x = 1
```

must not remain the fundamental POVM. Either remove it or retain it under an
explicit name such as `FinitePOVM` as a convenient discrete representation.
Provide conversion/equivalence with the general POVM on a finite discrete
measurable space, including the correspondence between singleton effects and
finite sums.

## Suggested implementation order

1. Finish the Mathlib/API investigation above and record the chosen topology
   and value type in module documentation.
2. Define the general POVM wrapper around the appropriate Mathlib measure
   object, with positivity and normalization fields.
3. Prove that measurable values are effects.
4. Implement the state-to-probability-measure construction and its basic
   probability lemmas.
5. Add the finite-discrete conversion/equivalence and migrate or rename the
   current finite definition.
6. Add tests/examples for arbitrary measurable spaces and for a finite
   discrete outcome space.

Conceptual target:

```text
POVM  --ω-->  Probability Measure  --∫ f dμ-->  Measurement Statistics
```

## Alternative: abstract W\*-algebra POVM via the dual/normal-state characterization

A second route to the same "measurement-statistics bridge" goal above, proposed
independently of the `VectorMeasure`/WOT plan: define the POVM directly on an
abstract `WStarAlgebra M`, with σ-additivity stated pointwise through every
*normal* positive functional/state, rather than through a topology on `M`
itself:

```text
E : Σ_X → Effect M,      E(∅) = 0,      E(X) = 1,
ω(E(⋃ₙ Aₙ)) = ∑ₙ ω(E(Aₙ))     for every normal state ω, disjoint (Aₙ).
```

and then, as the central theorem, `μ_{ω,E}(A) := ω(E(A))` should be an ordinary
probability measure for every normal `ω`:

```lean
structure POVM
    (X : Type*) [MeasurableSpace X]
    (M : Type*) [OperatorAlgebra M] [WStarAlgebra M] where
  effect : Set X → Effect M
  empty : effect ∅ = 0
  univ : effect Set.univ = 1
  m_iUnion :
    ∀ (s : ℕ → Set X), (∀ n, MeasurableSet (s n)) → Pairwise (Disjoint on s) →
      ∀ ω : NormalState M,
        ω.prob (effect (⋃ n, s n)) = ∑' n, ω.prob (effect (s n))

def POVM.toMeasure (E : POVM X M) (ω : NormalState M) : Measure X

@[simp] lemma toMeasure_apply : (E.toMeasure ω) A = ω (effect A)
@[simp] lemma toMeasure_univ : (E.toMeasure ω) Set.univ = 1
```

Scope note: as with the WOT plan above, do **not** restrict this to `B(H)`,
and do not add finite POVMs or extra architecture here — `POVM` (the
finite/`Fintype X` one in `Basic.lean`) and its eventual general replacement
already own that.

### Mathlib investigation done (2026-08-24) — record before coding

- `WStarAlgebra M` already exists: `Mathlib.Analysis.VonNeumannAlgebra.Basic`.
  It is a `Prop`-valued mixin on `CStarAlgebra M` asserting only the *mere
  existence* of a Banach predual (`∃ X, Nonempty (StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)`)
  — no predual is chosen, so it carries **no operations**: no weak-\*/ultraweak
  topology, no distinguished normal-functional set, nothing to build `Effect`,
  `∑'`, or a topology instance out of directly. Using `[WStarAlgebra M]` as a
  hypothesis is fine, but it buys nothing beyond documentation that `M` is
  meant to be a von Neumann algebra.
- There is **no** `NormalState`, `NormalFunctional`, `IsNormal` (for
  functionals/states), or any "normal" qualifier anywhere in Mathlib. The
  `NormalState` in the schematic definition above does not exist and would
  have to be built from scratch.
- There is **no** abstract ultraweak/weak-\* topology tied to a `WStarAlgebra`
  predual. The only weak-operator-topology infrastructure
  (`Mathlib.Analysis.LocallyConvex.WeakOperatorTopology`,
  `Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology`,
  `ContinuousLinearMapWOT` / `E →SWOT[σ] F`) is for *concrete* continuous
  (semi)linear maps between normed spaces — it is not phrased in terms of a
  predual of an abstract algebra, and (per the existing WOT investigation
  above) carries no positivity/order API of its own.
- Mathlib does have `PositiveLinearMap` / the `A →ₚ[ℂ] B` notation
  (`Mathlib.Analysis.CStarAlgebra.PositiveLinearMap`), which is exactly what
  `OperatorAlgebra.State` in `Basic.lean` already wraps
  (`toPositiveLinearMap : A →ₚ[ℂ] ℂ`, `map_one`). There is no "normal" refinement
  of it.
- No countable-sum-of-positive-elements / `tsum` API specific to
  `StarOrderedRing` turned up (searched for `tsum`+positivity combinations in
  `Analysis/CStarAlgebra`); `∑' n, ω.prob (effect (s n))` in the schematic
  definition is an ordinary `tsum` in `ℝ`/`ℂ` (via `ω`, which lands in `ℂ`),
  not a sum taken inside `M`, so this part is unproblematic once `ω` exists.

### Upstream mathlib4 activity (checked 2026-08-24 via `gh search`/GitHub, against
the mathlib rev `db584cd` pinned in this project's `.lake/packages/mathlib`,
dated 2026-08-10) — nobody is building `NormalState`/W\*-predual-topology
directly, but the one load-bearing prerequisite piece landed recently:

- **Already merged and present in our pinned mathlib**:
  [`leanprover-community/mathlib4#40489`](https://github.com/leanprover-community/mathlib4/pull/40489),
  "introduce typeclass `LinearMap.IsWeak` for weak topologies induced by
  bilinear forms" (`Mathlib.Topology.Algebra.Module.IsWeak`). This is
  *exactly* the general infrastructure needed to eventually put a genuine
  weak-\* topology on `M` from a chosen predual pairing
  `B : M →ₗ[ℂ] X →ₗ[ℂ] ℂ`: once `M`'s topology is declared `B.IsWeak`, its
  API (`continuous_eval`, `tendsto_iff_forall_eval_tendsto`, ...) gives
  weak-\* continuity/convergence for free, without physlib having to
  reinvent it. The motivating issue that led to this PR,
  [`#38484`](https://github.com/leanprover-community/mathlib4/issues/38484)
  ("Weak spaces as a class", filed by Jireh Loreaux, still open), explicitly
  names "a W⋆-algebra ... equipped with the weak-⋆ topology" as a target
  application — so this is a recognized direction, just not yet built for
  `WStarAlgebra` specifically.
- **Not done anywhere upstream**: nothing wires `WStarAlgebra`/
  `VonNeumannAlgebra` to `LinearMap.IsWeak` (`grep -rl IsWeak
  Mathlib/Analysis` is empty), and there is still no `Predual`/predual-choice
  structure, no `NormalState`/normal-functional notion, and no open PR or
  issue for "predual", "normal state", "normal functional", "ultraweak", or
  "POVM" against `mathlib4` addressing any of this. I.e. option 1 below (the
  honest route) is not something we can wait for — it isn't in flight
  upstream, though `IsWeak` removes its single hardest missing ingredient.

### Consequence for the plan

Since Mathlib has no normal-state or predual-topology API to reuse, defining
`NormalState M` faithfully means building real infrastructure first (pick a
predual witness, or otherwise define normality as weak-\* continuity), which
is a substantial prerequisite project of its own, not a one-file addition.
Two ways forward, to decide before implementing:

1. **Do the honest thing** (recommended future direction, not ready to start
   now): define `Predual M` (a chosen, not merely asserted, predual pairing
   `B : M →ₗ[ℂ] X →ₗ[ℂ] ℂ`), declare `B.IsWeak` (now available via
   `Mathlib.Topology.Algebra.Module.IsWeak`, see above) to get the weak-\*
   topology on `M` essentially for free, and define `NormalState` as the
   states that are continuous for it (equivalently, via
   `LinearMap.IsWeak.tendsto_iff_forall_eval_tendsto`, states whose value on
   `M` agrees with evaluation against some `x : X`). Then define `POVM`
   exactly as schematized above. This is real progress over the situation a
   few months ago — the topology infrastructure no longer needs to be
   invented — but picking/justifying the predual and building `NormalState`
   on top is still its own scoped task, not a one-file addition; revisit this
   file once that groundwork exists.
2. **Cheaper stand-in, flagged as such**: state `m_iUnion` for *every*
   `State M` (the existing structure in `Basic.lean`, no `WStarAlgebra`
   needed) rather than a not-yet-existing `NormalState M`. This is a strictly
   *weaker* statement than the physical one (it says nothing about
   continuity/normality, only about countable additivity of the induced
   scalar measure for each state), so it must be documented in the module
   doc as a deliberate simplification, not silently presented as the general
   physical POVM definition — mirroring the honesty requirement already
   imposed on the WOT/norm-topology plan above.

Do not start coding either the `Predual`/`NormalState` infrastructure or the
`POVM`/`POVM.toMeasure` construction until one of these two is chosen
explicitly.

## Resolution (2026-08-25): option 1 was built; implementation status

Option 1 above ("do the honest thing") was chosen and carried out in full:

- `Predual`/weak-⋆ topology/`NormalState`: `WStarAlgebra.lean` (`WStarAlgebra A`, chosen predual +
  isometric identification, `weakStarTopology`, `NormalState A` as a weak-⋆-continuous state).
  Sorry-free.
- `PVM` (the sharp/projective case, i.e. this file's schematic `POVM` specialized to
  `IsStarProjection`-valued): `Unbounded/NormalState.lean` — `Projection A`, `PVM X A` (a
  normalized `Projection`-valued `VectorMeasure`), `PVM.distribution`/`distribution_apply`
  (`μ_{ω,E}(S) = ω(E(S))`, built via `Measure.ofMeasurable` from `ω`'s continuity). Sorry-free.
- The genuinely general POVM (values in `Effect A`, not restricted to projections — this file's
  actual headline ask): `Unbounded/POVM.lean` — `POVM X A` (normalized, pointwise-nonnegative
  `VectorMeasure`), `POVM.mem_effect`, `PVM.toPOVM` (with `PVM.distribution_toPOVM` confirming
  agreement of the two `distribution` constructions), `POVM.distribution`/`distribution_apply`.
  Sorry-free.
- Finite-discrete compatibility (this file's suggested-order item 5): `Basic.lean`'s finite POVM
  was renamed `FinitePOVM` (nothing else in the codebase referenced the old `POVM` name), and
  `Unbounded/POVM.lean` proves `FinitePOVM.toPOVM` — viewing `X` as a discrete measurable space
  (`[DiscreteMeasurableSpace X]`), a `FinitePOVM` becomes a `POVM` as a finite sum of Dirac vector
  measures. Sorry-free.
- Not done: the concrete `WStarAlgebra (B(H))` instance itself (predual = trace-class operators as
  a genuine Banach space) — `WStarAlgebra.lean`'s module docstring and `general-theory-gap.md`
  section 7 track this; it is what would let `DensityOperator.toState` (`Unbounded/
  DensityOperator.lean`) literally *be* a `NormalState (B(H))` rather than only a `State (B(H))`
  under separate sorries.
- Not done (separately from the general-POVM question above): connecting `PVM`/`POVM` to
  *unbounded* functional calculus/moments beyond what `Distribution.lean` already gives for
  `AffiliatedObservable` — see `general-theory-gap.md` sections 6/9 (`boundedFC`,
  `Observable.toAffiliatedObservable`).

