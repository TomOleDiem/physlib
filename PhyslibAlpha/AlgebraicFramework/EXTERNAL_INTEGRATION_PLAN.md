# External library integration plan: Spectra and unbounded-alpha-public

This document maps what exists in two external/sibling code bases against `AlgebraicFramework`'s
own layered hierarchy (see `JordanOrderUnit/JB_ROADMAP.md` §1), states what is already covered
here — much more of it than first assumed, see §2 — and assigns each genuinely reusable remaining
piece to the layer it belongs at, always preferring the strongest/most general hypotheses actually
needed rather than the source's own scoping. Superseded content is stated explicitly as superseded,
not silently dropped, so this stays an accurate record rather than a wish list.

Every claim below is from direct file reads (this session, both trees, both via `gh api` for
Spectra and `Read`/`grep` for `unbounded-alpha-public`), not from names or descriptions alone.

**Looking for the per-library file list?** §7 at the end of this document is a flat, one-table-per-
library reference (file → verdict → port target) for all three sources read this session
(`unbounded-alpha-public`, Spectra, `Cobord/JordanAlgebra`). Sections 2–4 below are the same
findings organized by topic/gap instead of by source, with the full reasoning; §7 is the quick
index into them.

## 1. The layer question, answered once

Per `JB_ROADMAP.md` §1's hierarchy:

```text
bilinear algebra → Jordan algebra → Jordan order-unit → normed/JB → JBW
                                                                        \
                                                          Cstar/Hilbert-space realization
```

A Hilbert-space projection-valued-measure/spectral-theorem/automorphism-group construction is
**always** a realization-layer object, never an abstract-layer primitive. The abstract layers only
ever get the generic order/Jordan-theoretic version (`MeasurableProjectionResolution`,
`OneParameterAutomorphismGroup E`, etc.) — Hilbert-space-specific facts are corollaries applied to
`selfAdjoint (H →L[ℂ] H)` or `H →L[ℂ] H`, never smuggled upward. Nothing below changes this; every
recommendation respects it.

## 2. Correction to the previous version of this document: far more is already superseded

Direct comparison this session shows `AlgebraicFramework` has **already independently rebuilt**,
at the correct and usually *more general* abstract level, almost everything `unbounded-alpha-public`
has at the `Observables/`/`Dynamics/` layer, and almost everything Spectra/`unbounded-alpha-public`
have for the unbounded self-adjoint spectral theorem itself. Concretely, file-by-file:

| `unbounded-alpha-public` file | Content | Superseded by (this repo) | Verdict |
|---|---|---|---|
| `Observables/Jordan.lean` | `JordanObservable A`, symmetrized product `a⊙b`, on `[OperatorAlgebra A]` (old class) | `StarAlgebra/Jordan.lean` — same construction, on bare `[Ring A][StarRing A]`, no `OperatorAlgebra` wrapper needed | **Superseded, strictly more general here.** Do not port. |
| `Observables/Lie.lean` | Lie bracket `⁅a,b⁆ = -(i/2)(ab-ba)` on `[OperatorAlgebra A]` | `StarAlgebra/Lie.lean` — same, on `[Ring A][StarRing A][Module ℂ A][StarModule ℂ A]` (verified minimal by a prior session, not just assumed) | **Superseded.** Do not port. |
| `Dynamics/{Automorphism,AutomorphismGroup}.lean` | `AutomorphismGroup A` (one-parameter `*`-automorphism group) and `Aut⋆(B(H))≅PU(H)` (Wigner-type theorem), both on `[OperatorAlgebra A]`/concrete `B(H)` | `OrderUnit/Symmetry.lean`'s `OneParameterAutomorphismGroup E` (fully abstract, `[AddCommGroup E][PartialOrder E]`, no Cstar assumption — genuinely more general) for the abstract half; `HilbertSpace/Dynamics/Automorphism.lean`'s `ProjectiveUnitary H`/the `Aut⋆(H→L[ℂ]H) ≅ PU(H)` theorem (confirmed present, line 25/73/81) for the concrete half | **Superseded on both halves.** Do not port. |
| `Core/AnalyticVector/{Basic,Local,Nelson}.lean` | Nelson's analytic-vector essential-self-adjointness criterion | `HilbertSpace/Unbounded/AnalyticVector/{Basic,Local,Nelson}.lean` (same file names, present, wired in) | **Already exists here independently.** Do not port; if genuinely absent details differ, diff the two directly before assuming either needs work. |
| `Affil/SpectralTheorem.lean`, `Spec/Cayley*.lean`, `Spec/CayleySpectralData*.lean` | Unbounded self-adjoint spectral theorem via Cayley transform | `HilbertSpace/Unbounded/{Cayley,CayleySpectralData,SpectralIntegral}/*.lean`, public endpoint `unboundedSpectralTheorem` (1 `sorry` in the whole ~150-file tree, unrelated) | **Already exists here, independently built, with a stronger final package** (tied to the exact square-moment domain, not just a resolvent identity). Do not port. |
| `Flow/{Stone,StoneAPI,StoneInvariance}.lean` | Stone's theorem | `HilbertSpace/Unbounded/Flow/{Stone,StoneAPI,StoneInvariance}.lean`, `Existence/{StoneGenerator,...}.lean` (same names, present) | **Already exists here.** Do not port. |

**Conclusion of §2**: `unbounded-alpha-public`'s `OperatorAlgebra/` subtree was, at some point, the
seed this repo's `HilbertSpace/Unbounded/` and `StarAlgebra/`/`OrderUnit/` trees grew from (or a
parallel rebuild covering the same ground) — either way, it is now almost entirely redundant with
what exists here, and usually strictly weaker (Cstar/`B(H)`-specific where this repo has the
abstract order-unit version too). Only two pieces of real, non-redundant value remain, both below.

## 3. Genuine remaining gaps — what to reuse, and at which exact layer

### 3.1 `WStarAlgebra (B(H))` instance — realization layer, `WStarAlgebra/`

**Status: the Hilbert–Schmidt/polar-decomposition prerequisite stack is now ported, and
`HilbertSpace/TraceClass/Banach.lean` is fully sorry-free and wired into `PhyslibAlpha.lean`;
`WStarAlgebra/HilbertSpaceInstance.lean` has 8 of its original 11 gaps closed, 3 remain (genuinely
blocked on a further, separate density/approximation theorem), so it stays unwired per house
style.**

The missing Hilbert–Schmidt/polar-decomposition infrastructure — confirmed absent from Mathlib by
exhaustive grep (no `Schatten`, `HilbertSchmidt`, or `PolarDecomposition` declaration anywhere) —
is now ported as five new files under `HilbertSpace/TraceClass/`, restated directly against this
repo's own predicate-based `IsTraceClass`/`H →L[ℂ] H` (no bundled-subtype translation was actually
needed: `unbounded-alpha-public`'s own top-level `TraceClass.lean` already used the identical
predicate convention this repo's `Basic.lean` does):

* `HilbertSchmidt.lean` — the Hilbert–Schmidt predicate, its basis-independence and algebraic
  closure (ported from `TraceClass/{HilbertSchmidt,HSAlgebra,HSEstimate}.lean`), plus the
  Cauchy–Schwarz diagonal-summability estimates (ported from `TraceClass/TraceProduct.lean`).
* `Polar.lean` — the polar factor `polarFactor T` and the general partial-isometry identity
  `star (polarFactor T) * T = |T|` for *every* bounded `T` (ported from `TraceClass/Polar.lean`).
* `GeneralIdeal.lean` — the unconditional (non-self-adjoint) basis-independent trace
  `trace_eq_of_hilbertBasis`, crossing the boundary `Basic.lean`'s own self-adjoint-only theorem
  left open (ported from `TraceClass/GeneralIdeal.lean`).
* `GeneralProduct.lean` — the master lemma that a product of two Hilbert–Schmidt operators is
  trace class, and its two consequences `isTraceClass_add`/`isTraceClass_mul_mul` (the general
  two-sided ideal estimate) (ported from `TraceClass/GeneralProduct.lean`).
* `IdealNorm.lean` — the quantitative duality bound and its consequences `traceNorm_add_le`
  (subadditivity) and `traceNorm_mul_mul_le` (the quantitative two-sided ideal estimate) (ported
  from `TraceClass/IdealNorm.lean`).

Using this stack, `Banach.lean`'s three remaining gaps (`isTraceClass_add`, `traceNorm_add_le`,
`instCompleteSpace`) are now closed — the last via the absolutely-convergent-series criterion,
following `unbounded-alpha-public`'s `TraceClass/Completeness.lean` directly (ported inline into
`Banach.lean` rather than as a separate file, since it only extends the `TraceClass H` Banach-space
API already assembled there). `Banach.lean` is genuinely sorry-free and now wired into
`PhyslibAlpha.lean`, along with the five new supporting files.

`HilbertSpaceInstance.lean`'s five algebraic gaps (`isTraceClass_mul_coe`, `norm_trace_le`,
`trace_add`, `trace_smul`, `traceNorm_mul_mul_le`) are direct specializations of the newly-ported
general theorems, and the isometry half of `toDual` (`norm_tracePairing : ‖tracePairing A‖ = ‖A‖`)
is now also closed, ported from `unbounded-alpha-public`'s `WStarAlgebra/TracePairingNorm.lean`'s
rank-one test-vector argument. **3 gaps remain**, all reducing to one genuinely separate analytic
theorem not undertaken this pass: `rankOneSpan_dense` (every trace-class operator is a norm-limit
of finite-rank operators, via Hilbert–Schmidt truncation — source: `WStarAlgebra/
TracePairingSurj.lean`), which `tracePairing_surjective_of_rankOneSpan_dense` and hence
`tracePairingEquiv`/`tracePairingEquiv_apply` and the final instance all depend on. This is a
substantial, self-contained approximation theorem in its own right (not a short corollary of the
infrastructure just ported) and is the correctly-scoped next slice. **Priority 1, continue as
scoped**: prove `rankOneSpan_dense`, as its own dedicated piece of work.

### 3.2 Naimark's dilation theorem — realization layer, `Representation/`

**Status: in progress, paused mid-fix per explicit instruction.** `Representation/
DiscreteNaimark.lean` (525 lines, 0 sorry, does not yet compile — 7 itemized mechanical Lean-API
fixes remain, none structural). Correctly scoped and named as the *discrete/countable* case only
(per the user's own correction: the general theorem is for an arbitrary measurable POVM
`M : Σ → Eff(H)`, and the deepest frame is that Naimark is a corollary of **Stinespring dilation**
applied to the commutative operator algebra of bounded measurable functions on the outcome space —
commutativity makes positivity automatically complete positivity, so Stinespring's `Φ(f)=V*π(f)V`
specializes via indicator functions to `M(A)=V*P(A)V`).

**Stinespring dilation — DONE this session.** Ported from `unbounded-alpha-public`'s
`Unbounded/OperatorAlgebra/Dynamics/Stinespring/Core.lean` (the `QuantumMechanics/
StinespringDilation.lean` file turned out to be an unrelated finite-dimensional `Matrix`/Kraus-
operator treatment, entirely class-agnostic already but not the operator-algebraic theorem wanted
here; not ported). The real content was built on the old `OperatorAlgebra` class (`[OperatorAlgebra
A]`, `A →CP B(H)` via `OperatorAlgebra.Representation A H := A →⋆ₐ[ℂ] B(H)`), confirmed
field-isomorphic to this repo's `[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]` — exactly
the hypotheses this repo's own `CStarAlgebra/Channel.lean` already uses for Mathlib's own
`CompletelyPositiveMap` (`A₁ →CP A₂`) — so the translation was a mechanical restatement, not new
mathematics. New files: `CStarAlgebra/Stinespring/Kernel.lean` (the `blockMatrixMap`
finite-block-operator API, the CP-kernel positivity chain `gramMatrix`/`cpKernel_inner_nonneg*`,
and the `StinespringWitness A H K J` structure) and `CStarAlgebra/Stinespring/Dilation.lean` (the
tensor-product GNS-style construction on `A ⊗[ℂ] H`, culminating in
`Stinespring.Canonical.canonical_stinespring_identity : J a = V⋆ π(a) V` and the existence theorem
`Stinespring.exists_stinespringWitness`). Generality matches the source exactly (arbitrary unital
`A`, codomain fixed to `H →L[ℂ] H` — going further would need an abstract notion of `⋆`-
representation into a general `WStarAlgebra`, real new math out of scope here). `lake build
PhyslibAlpha` clean, 0 sorry/admit/new axiom, 0 warnings in the new files, wired into
`PhyslibAlpha.lean`. This is the route to the fully general Naimark theorem (a POVM is a CP map on
the commutative algebra of bounded measurable functions; positivity there is automatically complete
positivity, and indicator functions recover the projection-valued dilation from `π`) — specializing
`exists_stinespringWitness` to that commutative case is future work, kept separate from this task.
`DiscreteNaimark.lean`'s 7 mechanical fixes remain **paused per direct instruction** (§6) and were
not touched.

### 3.3 Tomita–Takesaki modular theory + KMS — `WStarAlgebra/`, large, sequence later

Unchanged from the previous version of this plan: absent from both trees entirely; Spectra's own
`Modular/*` (~40 files) has the construction up to the modular operator/flow/conjugation/KMS
condition, with the final commutation theorem (`JMJ=M'`) as Spectra's own acknowledged open
research target. Belongs at the `WStarAlgebra/` layer (needs a predual + cyclic separating vector,
same as `WStarAlgebraStructure`/`NormalState`). **Priority 3**, sequence after 3.1/3.2, scope as its
own dedicated multi-file effort — do not start opportunistically.

### 3.4 Essential spectrum + Weyl's theorem — DONE this session

`HilbertSpace/Unbounded/EssentialSpectrum/{Defs,WeakCompact,Closed,Smul,Weyl,Discrete}.lean` — all
six files build clean, 0 sorry/admit/axiom, restated against this repo's own `LinearPMap`/
self-adjoint operator type (no second spectral-measure hierarchy introduced). One honest
hypothesis-level gap (`IsResolventAt`, packaging "total + continuous resolvent" as a hypothesis
pending a closed-graph-theorem bridge lemma this repo doesn't have yet) and one deliberately
unported theorem (`Discrete.lean`'s hard half, which needs Spectra's own bespoke `ProjValMeasure`
machinery to re-derive against this repo's spectral apparatus — left as a documentation-only file
recording the exact bridge). **No further action needed here** beyond, eventually, building the
resolvent-to-CLM bridge lemma (a well-scoped, independently useful item) to discharge `IsResolventAt`
for real. Note: the earlier version of this plan's claim that `JordanOrderUnit/SpectralDecomposition.
lean`'s `discreteSpectrum` names the motivating gap was **checked and found wrong this session** —
no file or declaration by that name exists anywhere in this checkout; only this plan document's own
prose mentioned it. Correcting the record here rather than repeating the error.

## 4. `Cobord/JordanAlgebra` — investigated in full, and this is the real find

`unbounded-alpha-public`'s old `Observables/Jordan.lean` carried a standing `TODO`: *"Investigate
`https://github.com/Cobord/JordanAlgebra/` and determine which general Jordan-algebra results are
relevant for quantum mechanics."* Read in full this session (`gh api`, all 19 `Jordan/*.lean` files,
sorry/axiom-counted individually). Small (~4200 lines, 1 star, last pushed 2026-08-24, Lean
`v4.31.0`), **essentially sorry-free — exactly ONE `sorry` in the entire library**, and unlike
Spectra (zero Jordan-algebra content in 373 files, purely Cstar/Hilbert-space theory), this is a
library specifically about abstract commutative Jordan algebras. It is directly on the critical
path, not adjacent to it.

### 4.1 It already proves McCrimmon's linearized fundamental formula — cross-check target

`Jordan/JordanAlgebra.lean`'s `lmul_mul_mul_eq` (sorry-free, `[Invertible (2:R)]` on a bare
`CommRing R`/`JordanAlgebra R M`, no real-number specificity):

```text
L((b*d)*c) = L(b*d)∘L(c) + L(c*d)∘L(b) + L(b*c)∘L(d) − L(b)∘L(c)∘L(d) − L(d)∘L(c)∘L(b)
```

proved via McCrimmon's two-stage linearization (`jax2_prime`, `jax2_double_prime`) of the bare
Jordan identity — genuinely more general than this repo's `[NonAssocCommRing E][Module ℝ E]`
setup (works over any commutative ring with `2` invertible) and reaches, in one file, essentially
the same territory `Quadratic/Fundamental.lean`'s `mulLeft_quadRep_normalize`/
`quadRep_quadRep_eq` spent multiple sessions building toward from first principles. **Action**:
cross-check this repo's own linearized identities against `lmul_mul_mul_eq` (do the two match up
to notation, and does theirs shorten anything here?) before further from-scratch operator-
normalization work in this file.

### 4.2 It got stuck at the EXACT SAME theorem this repo just solved — worth reporting back

`Jordan/JordanTriple.lean`'s only `sorry` is in the `JordanAlgebra ⟹ JordanTriple` instance's
`triple_identity` field — **the same Jordan-triple-system fundamental identity**
`tripleOperator_comm` proves in this repo (§ this session's `quadRep_fundamental` work). Cobord's
own approach is term-cancellation search (`find_cancel.py`, reducing to "40 raw multiplication
terms" needing explicit `jordan_mul_comm` rewrites), left stuck and sorry'd with a detailed TODO.
This repo's derivation-operator route (`D_{a,b}:=[L_a,L_b]` is a genuine Jordan-product derivation,
`V_{a,b}:=L_{a*b}+D_{a,b}`, `[V_{a,b},V_{c,d}]=V_{\{a,b,c\},d}-V_{c,\{b,a,d\}}`) closed it cleanly.
**This is worth turning into an actual upstream contribution** — closing Cobord's one remaining
`sorry` with this repo's own already-proved technique, translated to their bare-`CommRing`
generality, is a small, concrete, high-goodwill open-source contribution and a genuine correctness
cross-check of this repo's own proof. Not urgent, but flag it as a live option.

### 4.3 `StructureAlgebra.lean` — the textbook version of this session's `innerDerivation`/`tripleOperator`

`JordanDerivation R M` (`R`-linear, Leibniz rule `D(a*b)=a*D(b)+D(a)*b`), `inner` (the inner
derivation constructor — **matches this repo's `innerDerivation` field-for-field**, `leibniz`
matches `innerDerivation_mul`), the commutator Lie algebra on derivations (matches
`innerDerivation_comm`), and `StructureAlgebra R M := M × JordanDerivation R M` (**exactly**
`V_{a,b} := L_{a*b} + D_{a,b}`, packaged as `Jacobson`/`Meyberg`'s classical "structure algebra" of
a Jordan algebra, its own Lie algebra via `toEnd`). All sorry-free. This is strong independent
confirmation that this session's from-scratch `innerDerivation`/`tripleOperator` construction is
not an ad-hoc trick but the standard textbook object (the structure algebra) — worth citing by that
name in `Quadratic/Fundamental.lean`'s docstrings, and worth reading this file directly before any
further structure-algebra-adjacent work here (Peirce theory, generated subalgebras) to reuse its
naming/lemma shape rather than re-deriving.

### 4.4 `AlbertAlgebra.lean` + `SpinFactor.lean` — the missing non-special concrete instances

Both fully sorry/axiom-free (890 and 276 lines). `AlbertAlgebra` (3×3 Hermitian octonionic
matrices, via `hermitian_jordan_identity`'s fully generic `H₃(D,-)` construction for any `D` with
`[IsAlternative D][StarRing D][IsNuclearInvolution D]`) and `SpinFactor` (`V × R` from a symmetric
bilinear form) are, respectively, **the** exceptional simple JB algebra and **the** other classical
non-matrix simple JB algebra family — genuinely NOT special (no faithful embedding into any
associative/Cstar algebra exists for the Albert algebra). `AlgebraicFramework`'s only concrete
instances today are all Cstar-based (`selfAdjoint A`) — i.e. all *special*. Getting even one
genuinely exceptional instance (`AlbertAlgebra`) to satisfy `IsJordanOrderUnit`/`JBAlgebra` would be
the strongest possible validation that this repo's abstract layer is not secretly just disguised
C\*-algebra theory, and both already have `isFormallyReal`/`detTrace` (trace/determinant, state
cone) built — directly comparable to `IsJordanOrderUnit`'s own positivity axiom. **High-value,
self-contained future task**: instantiate `AlbertAlgebra`/`SpinFactor` against
`JordanOrderUnit`'s abstract classes and see how far the existing abstract theorems (Stage A's now-
complete fundamental formula, Stage C.2's root uniqueness) carry over immediately for free.

### 4.5 `FormallyReal.lean` — cross-check for the abstract state/order theory

`IsFormallyReal`, `states`/`pureStates` (the cone of squares cut by `trace x = 1`, and its
idempotent extreme points), `expect` (linear expectation-value functional) — parallels this repo's
own `IsJordanOrderUnit`/state-cone/effect theory closely enough to be worth a direct side-by-side
read before extending `OrderUnit/State/*` further, as a second independent formulation to check
against (not a port target by itself — the content is comparable in scope to what's already here,
not larger).

### 4.6 What NOT to take from Cobord

`Octonion.lean`/`OctonionMatrix.lean`/`MatrixAssociator.lean`/`NuclearInvolution.lean`/
`HermitianMatrixAssociator.lean`/`MooreDeterminant.lean` are load-bearing *infrastructure* for
`AlbertAlgebra.lean` (§4.4) but not independently interesting for `AlgebraicFramework` — port them
only as part of porting `AlbertAlgebra` itself, not standalone. `Alternative.lean`,
`RealQM.lean`/`ComplexQM.lean`/`QuaternionicQM.lean` (the non-exceptional Hermitian-matrix Jordan
algebras) are lower priority than `AlbertAlgebra`/`SpinFactor` — special Jordan algebras this
repo's Cstar-realization branch already covers in substance via `selfAdjoint A`. `CommNonAssocNF.lean`
is design notes only, no code.

## 5. What NOT to reuse (unchanged, reaffirmed)

- Spectra's `ProjValMeasure`/`POVM` bespoke wrapper types, or `unbounded-alpha-public`'s
  `OperatorAlgebra`/`OperatorAlgebra.WStarAlgebra` classes themselves (upstream-superseded, PR
  #1622) — only proof *content* built on them is ever reused, restated against this repo's own
  types/classes.
- Spectra's Hydrogen atom / Dirac equation / Bell inequalities / Fock & Krein spaces /
  **information geometry, Bochner/Herglotz/positive-definite-function theory, Fenchel–Legendre
  convex analysis** (read this session: `InformationGeometry/{CramerRao,Divergence,Fisher}/*`,
  `Bochner/GNS/PosDefFun.lean`, `Herglotz/Basic.lean`, `PositiveDefinite/Basic.lean`,
  `Analysis/Convex/Fenchel/Conjugate.lean` — all genuine, well-written mathematics, but targeting
  statistical-manifold/DFT physics, orthogonal to `AlgebraicFramework`'s Jordan/order-unit/JB/JBW
  scope). Not part of this plan.
- A full branch merge of `unbounded-alpha-public` — confirmed low mechanical-conflict-risk (3
  shared files) but genuinely low-value now that §2 shows almost everything worth taking is either
  already superseded or covered by the two targeted items in §3.1/3.2.

## 6. Priority order — re-ranked by what enables general QM theorems, not by abstract-algebra novelty

The governing question for this section is: what unlocks a genuinely general quantum-mechanical
theorem, not what is the most mathematically interesting abstract-algebra fact available. Re-ranked
accordingly (an earlier version of this section got this backwards — corrected here):

1. **Finish `WStarAlgebra(B(H))`** (§3.1) — the actual QM-enabling item. Without a predual there is
   no abstract notion of a normal state / general (infinite-dimensional) mixed quantum state, no
   density-operator description at the right level of generality. **16 of the original 19 named
   sorries are now closed** (`Banach.lean` fully sorry-free and wired in; `HilbertSpaceInstance.lean`
   8/11 closed). The remaining 3 all reduce to one substantial standalone theorem,
   `rankOneSpan_dense` (Hilbert–Schmidt truncation/density), the correctly-scoped next slice.
2. **Port Stinespring dilation** from `unbounded-alpha-public` (§3.2) — **done this session**
   (`CStarAlgebra/Stinespring/{Kernel,Dilation}.lean`). The general theorem that every physical
   quantum operation (channel, measurement, decoherence process) arises from coupling to a larger
   system and ordinary unitary dynamics. This is the actual general QM theorem worth having; it
   subsumes Naimark's theorem as the commutative special case, so it supersedes rather than depends
   on the discrete-Naimark work below. Specializing it to the commutative case to recover general
   Naimark is the natural next step, scoped as its own future task.
3. **Tomita–Takesaki/KMS** (§3.3) — large, but this is real physics generality: the general
   framework for thermal/equilibrium quantum states and algebraic QFT. Sequence after 1–2, scope as
   its own dedicated effort.

**Explicitly paused, not "to finish," per direct instruction**: `DiscreteNaimark.lean`'s 7
mechanical compile fixes (§3.2a). The user stopped this work mid-fix and it should not be resumed
without being asked — the general Stinespring route (item 2 above) is the actual priority and
subsumes it; do not schedule the discrete case as upcoming work.

**Explicitly deprioritized, not urgent**: `AlbertAlgebra`/`SpinFactor` instantiation (§4.4) and the
Cobord cross-checks (§4.1, §4.2) — genuinely interesting for validating the abstract layer's
generality in the pure-mathematics sense, but not something enabling a QM theorem anyone needs
right now. Revisit later, not as current work. `StructureAlgebra.lean` (§4.3) and
`FormallyReal.lean` (§4.5) remain worth reading as background before touching `Quadratic/`- or
`OrderUnit/State/*`-adjacent code respectively, but are not standalone tasks.

Essential spectrum + Weyl (§3.4) is done — this is also a genuine physics-enabling item (real
Hamiltonians with continuous spectrum, not just toy finite-dimensional ones), already delivered.

## 7. Per-library file inventory (quick reference)

One table per source library. "Detail" points at the section above with the full reasoning; read
that before acting on any row, this table is an index, not a substitute.

### 7.1 `unbounded-alpha-public` (`physlib-dev`, branch `unbounded-alpha-public-no-quantuminfo`)

| File(s) | Verdict | Port target / status | Detail |
|---|---|---|---|
| `Observables/Jordan.lean` | Superseded, this repo's version is more general | — do not port | §2 |
| `Observables/Lie.lean` | Superseded, this repo's version is more general | — do not port | §2 |
| `Dynamics/{Automorphism,AutomorphismGroup}.lean` | Superseded on both the abstract and concrete half | — do not port | §2 |
| `Core/AnalyticVector/{Basic,Local,Nelson}.lean` | Already exists here independently | — do not port | §2 |
| `Affil/SpectralTheorem.lean`, `Spec/Cayley*.lean`, `Spec/CayleySpectralData*.lean` | Already exists here, stronger package | — do not port | §2 |
| `Flow/{Stone,StoneAPI,StoneInvariance}.lean` | Already exists here | — do not port | §2 |
| `TraceClass/{HilbertSchmidt,HSAlgebra,HSEstimate,TraceProduct}.lean` | Genuine gap, missing Mathlib prerequisite | **Done this session** — ported as `HilbertSpace/TraceClass/HilbertSchmidt.lean`, clean build, 0 sorry, wired into `PhyslibAlpha.lean` | §3.1, §6 |
| `TraceClass/Polar.lean` | Genuine gap, missing Mathlib prerequisite | **Done this session** — ported as `HilbertSpace/TraceClass/Polar.lean`, clean build, 0 sorry, wired into `PhyslibAlpha.lean` | §3.1, §6 |
| `TraceClass/GeneralIdeal.lean` | Genuine gap, missing Mathlib prerequisite | **Done this session** — ported as `HilbertSpace/TraceClass/GeneralIdeal.lean`, clean build, 0 sorry, wired into `PhyslibAlpha.lean` | §3.1, §6 |
| `TraceClass/GeneralProduct.lean` | Genuine gap, missing Mathlib prerequisite | **Done this session** — ported as `HilbertSpace/TraceClass/GeneralProduct.lean`, clean build, 0 sorry, wired into `PhyslibAlpha.lean` | §3.1, §6 |
| `TraceClass/IdealNorm.lean` | Genuine gap, missing Mathlib prerequisite | **Done this session** — ported as `HilbertSpace/TraceClass/IdealNorm.lean`, clean build, 0 sorry, wired into `PhyslibAlpha.lean` | §3.1, §6 |
| `TraceClass/Completeness.lean` | Genuine gap, missing Mathlib prerequisite | **Done this session** — ported inline into `HilbertSpace/TraceClass/Banach.lean`'s `instCompleteSpace`; `Banach.lean` is now fully sorry-free and wired into `PhyslibAlpha.lean` | §3.1, §6 |
| `TraceClass/PositiveIdeal.lean` | Superseded — `Basic.lean` already has the self-adjoint/positive case (`trace_eq_of_hilbertBasis_of_nonneg`/`_of_isSelfAdjoint`) without polar decomposition | Not ported (not needed for the remaining gaps) | §3.1 |
| `WStarAlgebra/{InfiniteDim,TracePairingNorm}.lean` | Genuine gap | **Done this session** — `InfiniteDim.lean`'s field-mapping realized as `WStarAlgebra/HilbertSpaceInstance.lean` (8/11 file-local gaps closed using the newly-ported stack above); `TracePairingNorm.lean`'s isometry argument ported directly (`norm_tracePairing`) | §3.1, §6 |
| `WStarAlgebra/TracePairingSurj.lean` | Genuine gap, substantial standalone analysis (Hilbert–Schmidt truncation/density) | **Not ported this session** — `rankOneSpan_dense` remains the one open gap; `tracePairing_surjective_of_rankOneSpan_dense`'s easy Riesz-representation half is ported, density kept as an explicit hypothesis | §3.1, §6 |
| `Unbounded/OperatorAlgebra/Dynamics/Stinespring/Core.lean` | Genuine gap, was absent from `AlgebraicFramework` entirely | **Done this session** — `CStarAlgebra/Stinespring/{Kernel,Dilation}.lean`, clean build, 0 sorry, wired in | §3.2, §6 |
| `QuantumMechanics/StinespringDilation.lean` | Unrelated finite-`Matrix`/Kraus-operator treatment, already class-agnostic but not the operator-algebraic theorem needed here | Not ported (out of scope, different theorem) | §3.2, §6 |
| `Unbounded/OperatorAlgebra/Dynamics/Stinespring/{Canonical,Converse}.lean` | Christensen–Evans/Lindblad-generator applications of the core Stinespring construction, not the dilation theorem itself | Not ported (separate task if Lindblad dynamics content is wanted later) | §3.2, §6 |
| `Representation/PVM.lean`-style bare family (led to `Representation/DiscreteNaimark.lean`) | Correct but narrow; superseded in priority by Stinespring | **Paused per instruction**, not upcoming work | §3.2, §6 |

### 7.2 `adambornemann-glitch/Spectra` (GitHub, Apache 2.0)

| File(s) | Verdict | Port target / status | Detail |
|---|---|---|---|
| `Operator/{DeficiencyIndex,SelfAdjointExtension*,VonNeumannExtension*,KatoRellich}.lean`, `CayleyTransform/*`, `StoneBridge/*`, `YosidaHille/*` | Already exists here (`HilbertSpace/Unbounded/`), independently built, stronger package | — do not port | §2 (via the `unbounded-alpha-public` comparison; Spectra reaches the same ground) |
| `SpectralTheory/Essential/{Closed,Defs,Discrete,Smul,WeakCompact,Weyl}.lean` | Genuine gap, real content | **Done this session** — `HilbertSpace/Unbounded/EssentialSpectrum/*`, clean build, one hypothesis-level gap (`IsResolventAt`) | §3.4 |
| `QuantumMechanics/BornRule/Naimark.lean`, `ProjValMeasure/{Basic,General}.lean` | Correct discrete construction, but wrong normalization hypothesis as first drafted (operator-norm vs. scalar/weak — user's own correction), and the wrong generality target (discrete case, not general Naimark/Stinespring) | Superseded in priority by porting `unbounded-alpha-public`'s Stinespring instead; discrete work paused | §3.2, §6 |
| `Modular/{Cocycle,KMS,Tomita,TomitaTakesaki}/*` (~40 files) | Genuine gap, real content, source's own endgame theorem still open upstream | **Priority 3**, large, not started | §3.3 |
| `InformationGeometry/*`, `Bochner/GNS/PosDefFun.lean`, `Herglotz/*`, `PositiveDefinite/Basic.lean`, `Analysis/Convex/Fenchel/Conjugate.lean` | Real mathematics, wrong scope (statistical-manifold/DFT physics, not Jordan/order-unit/JB/JBW) | Not part of this plan | §5 |
| Hydrogen atom / Dirac equation / Bell inequalities / Fock & Krein spaces | Real physics, wrong scope for `AlgebraicFramework` specifically | Not part of this plan | §5 |
| `ProjValMeasure`/`POVM` wrapper types themselves (as opposed to proof content built on them) | Would be a second competing PVM hierarchy | Never reuse the types, only translated proof content | §1, §5 |

### 7.3 `Cobord/JordanAlgebra` (GitHub, Apache 2.0, small — ~4200 lines, 1 sorry total)

| File(s) | Verdict | Port target / status | Detail |
|---|---|---|---|
| `Jordan/JordanAlgebra.lean` (`lmul_mul_mul_eq`, McCrimmon's linearized fundamental formula) | Genuinely more general than this repo's own version, real cross-check value | Deprioritized for now (not QM-enabling) — cross-check when convenient | §4.1, §6 |
| `Jordan/JordanTriple.lean` (the one library-wide `sorry`, same identity as `tripleOperator_comm`) | This repo already solved it independently; closing theirs is a possible small upstream contribution | Deprioritized, optional, low-urgency | §4.2, §6 |
| `Jordan/StructureAlgebra.lean` (`JordanDerivation`, `StructureAlgebra R M`) | Textbook confirmation of this repo's `innerDerivation`/`tripleOperator` — not a port target, a citation/background source | Read before further `Quadratic/`-adjacent work, not a standalone task | §4.3, §6 |
| `Jordan/{AlbertAlgebra,SpinFactor}.lean` | Real, sorry-free, the missing non-special concrete `JBAlgebra` examples | **Deprioritized per direct instruction** — high pure-math value, not currently a physics priority | §4.4, §6 |
| `Jordan/FormallyReal.lean` | Comparable in scope to this repo's own state/order theory, cross-check only | Read before extending `OrderUnit/State/*`, not a standalone task | §4.5, §6 |
| `Jordan/{Octonion,OctonionMatrix,MatrixAssociator,NuclearInvolution,HermitianMatrixAssociator,MooreDeterminant,Alternative,RealQM,ComplexQM,QuaternionicQM,CommNonAssocNF}.lean` | Infrastructure for `AlbertAlgebra`, or lower-priority special-Jordan-algebra content this repo already covers via `selfAdjoint A` | Not part of this plan | §4.6 |
