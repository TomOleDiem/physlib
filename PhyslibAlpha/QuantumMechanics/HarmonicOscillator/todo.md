# Finishing the harmonic oscillator: scope and ranking

Six things stand between the current state of `HarmonicOscillator/` (+ `LadderSystem/`) and a
genuinely "finished" story. This file scopes each one and ranks them by how much new theory has
to be built before they're even tractable, easiest first.

**Deliberately out of scope as a shortcut**: `OneDimension/HarmonicOscillator` (the older
Hermite/wave-mechanics formalization) is *not* to be generalized or reused as infrastructure here.
Where it has genuinely reusable content (`Physlib.Mathematics.SpecialFunctions.PhysHermite`, which
is general-purpose, not oscillator-specific), that's cited below. The wave-mechanics `eigenfunction`/
`eigenValue`/`schrodingerOperator` machinery itself is not.

## Ranking

| # | Item | Tier | Status |
|---|---|---|---|
| 1 | `potentialOperator_isSelfAdjoint` | Trivial | **Done** |
| 2 | `vacuumSpan` irreducibility | Easy | **Done** |
| 3 | Cartesian/Hermite basis (native) | Medium | Self-contained new computation, real special-function scaffolding exists |
| 4 | Hamiltonian: number-op form ↔ K+T bridge | Medium/Hard | CLM-level algebra is doable now; full bridge needs #5's infrastructure |
| 5 | Ladder-operator adjointness | Hard | Needs new unbounded-operator promotion + domain-matching machinery |
| 6 | Spherical basis | Hardest | No spherical-harmonics infrastructure exists in physlib at all yet |

---

## 1. `potentialOperator_isSelfAdjoint` (Trivial) — ✅ Done

Both `informal_lemma` stubs are now real, zero-`sorry` theorems in `HarmonicOscillator/Basic.lean`:
`potentialFunction_apply` (the explicit closed form `½m · ∑ᵢ ωᵢ²xᵢ²`, via `Matrix.toQuadraticForm'`
unfolded against the already-proven `potentialMatrix_mulVec`), `potentialFunction_continuous`,
`potentialFunction_aestronglyMeasurable`, and `potentialOperator_isSelfAdjoint` itself via
`mulOperator_isSelfAdjoint_ofReal`, exactly as planned.

---

## 2. `vacuumSpan` irreducibility (Easy) — ✅ Done

Proved in the new `Physlib/Mathematics/LadderSystem/Irreducibility.lean`
(`vacuumSpan_eq_of_ne_bot`), following the sketch below closely for parts A-B; part C
(connectivity) turned out to need more bookkeeping than "easy" suggested -- a `moveOneTo`
count-function combinator, its reversibility (`moveOneTo_moveOneTo`), and two strong inductions
(push every word to an "everything in mode 0" hub, and the hub back out to any word) rather than a
one-line consequence of `0 < d`. Still zero `sorry`, zero new Mathlib gaps -- just more induction
than the one-paragraph sketch implied.

**Original sketch, for context** (superseded by the theorem above):
full proof sketch already written out, right before `namespace LadderSystem`.

**Plan** (already scoped in the TODO text, repeated here for convenience):
1. A transfer formula `E i j (word (countWord α) Ω) = α j • word (countWord (α with one moved
   j→i)) Ω`, from `E_word` + `count_countWord` + `word_perm` (all in `LadderSystem/Vacuum.lean`,
   already proven).
2. Given `W ≠ ⊥` invariant under every `E i j`, `W` is invariant under the diagonal operator
   `M := ∑ᵢ(n+1)^i • Nᵢ` from `OccupationBasis.lean`'s `hasEigenvector_word_countWord`, whose
   eigenvalues (`countEncode`) are pairwise distinct (`countEncode_injOn`) — a
   Lagrange-interpolation polynomial in `M` projects any nonzero `w ∈ W` onto a single nonzero
   `vacuumBasis` vector, landing it in `W`.
3. Repeatedly applying `E 0 j`/`E j 0` (using `0 < d`) connects every basis vector to every other,
   so `W` contains the whole `vacuumBasis`, i.e. `W = ⊤`.

**New theory needed**: none — every ingredient (steps 1 and the eigenvector fact in step 2) is
already proven. This is execution, not research.

**Files**: `LadderSystem/Vacuum.lean` (the theorem itself likely wants to live here or in a new
`LadderSystem/Irreducibility.lean` if the proof turns out long).

---

## 3. Cartesian/Hermite basis, native to the ladder framework (Medium)

**Current state**: `Basic.lean`'s TODO — "Determine the energy eigenstates ... in the 'Cartesian
basis' in terms of Hermite polynomials" — untouched for the `d`-dim structure. The abstract
occupation-number basis (`LadderSystem.vacuumBasis`, indexed by count functions `α : Fin d → ℕ`)
already exists; what's missing is the explicit pointwise formula for each basis vector.

**Plan**: build this directly against `vacuumGaussian`/`annihilationCLM`/`creationCLM`, mode by
mode — *not* by generalizing `OneDimension`'s file.
1. `Physlib.Mathematics.SpecialFunctions.PhysHermite` already has the Rodrigues-type identity that
   makes this tractable: `deriv_gaussian_eq_physHermite_mul_gaussian` /
   `physHermite_eq_deriv_gaussian` / `physHermite_eq_deriv_gaussian'` relate derivatives of a
   Gaussian to Hermite polynomials times the Gaussian. This is general-purpose special-function
   content, safe to reuse (it isn't part of the `OneDimension` oscillator formalization).
2. Since `annihilationCLM i`/`creationCLM i` only touch coordinate `i` (via `𝐱 i`, `𝐩 i`,
   `Space.deriv i`), the natural route is a per-mode induction on occupation number `α i`, holding
   the other coordinates fixed, showing `creationCLM i` applied to
   `(polynomial in xᵢ) * vacuumGaussian` raises the polynomial's Hermite degree by one in that
   coordinate — mirroring `PhysHermite`'s own Rodrigues identity, not `OneDimension`'s derivation of
   it.
3. Assemble: `word (countWord d α) vacuumGaussian` should equal an explicit constant times
   `(∏ᵢ physHermite (α i) (xᵢ/ξᵢ)) * vacuumGaussian`'s pointwise value, normalized the same way
   `vacuumBasis` is. This connects `LadderSystem.vacuumBasis` (abstract) to explicit formulas.
4. The normalization constant and orthonormality can likely reuse `PhysHermite`'s
   `physHermite_norm_cons`/`physHermite_orthogonal_cons`-style facts per coordinate, combined via
   `Fubini`/product-measure reasoning over `Space d`.

**New theory needed**: a genuine (if self-contained) induction connecting the ladder-operator
action to Hermite-polynomial degree-raising in the `d`-dim Schwartz setting. No missing Mathlib or
physlib prerequisites — the special-function facts already exist, this is assembling them into the
oscillator's own operators.

**Files**: new `HarmonicOscillator/CartesianBasis.lean` (or similar), importing
`LadderOperators.lean`, `Vacuum.lean`, and `PhysHermite`.

---

## 4. Hamiltonian in number-operator terms, bridged to the K+T Hamiltonian (Medium/Hard)

**Current state**: `LadderOperators.lean` has five TODOs strung together (define the Hamiltonian
from number operators; its commutation relations; relate it to `kineticOperator +
potentialOperator`; prove the two define the same quantum system). `Basic.lean`'s K+T Hamiltonian
already exists as a `LinearPMap`, but its self-adjointness is still an `informal_lemma`.

**Plan, two phases with different difficulty**:

**Phase A — CLM level (doable now, no unbounded-operator promotion needed)**: `annihilationCLM`/
`creationCLM` are already explicit linear combinations of `positionCLM`/`momentumCLM`. Expanding
`∑ᵢ ℏωᵢ(numberCLM i + 2⁻¹ • 1)` algebraically in terms of `𝐱ᵢ`, `𝐩ᵢ` should produce exactly
`(2m)⁻¹ • ∑ᵢ 𝐩ᵢ² + (m/2) • ∑ᵢ ωᵢ²𝐱ᵢ²` — the standard oscillator identity — entirely as an identity
of continuous linear maps on `𝓢(Space d, ℂ)`. This is a finite computation (no domain/adjoint
subtleties at the CLM level) and can be done as soon as `Basic.lean`'s `kineticOperator`/
`potentialOperator` are restated at the CLM level (or a Schwartz-level `kineticCLM`/`potentialCLM`
pair is introduced alongside them).

**Phase B — partial-operator level**: promoting the number-operator Hamiltonian to a genuine
`Q.HS →ₗ.[ℂ] Q.HS` and showing it equals (or is a restriction of) `Q.hamiltonian` needs the same
`SchwartzSubmodule`-based promotion machinery that item 5 needs for the ladder operators — so full
completion of this item is gated behind item 5's groundwork, even though Phase A is independent
and can land first.

**New theory needed**: Phase A is pure computation; Phase B inherits item 5's requirements.

**Files**: `LadderOperators.lean` (Phase A, new section), `HarmonicOscillator/Basic.lean` (Phase B).

---

## 5. Ladder-operator adjointness (Hard)

**Current state**: open TODO in `LadderOperators.lean`, previously assessed non-trivial this
session and not attempted.

**Plan**:
1. Promote `annihilationCLM i`/`creationCLM i` from Schwartz-space CLMs to genuine
   `Q.HS →ₗ.[ℂ] Q.HS` partial operators, following `Operators/Momentum.lean`'s exact template for
   `momentumOperator`: domain `SchwartzSubmodule d`, `toFun := (schwartzIncl volume).1 ∘ₗ
   (ladderCLM).1 ∘ₗ (schwartzEquiv volume).symm.1`.
2. Establish the formal-adjoint relation `𝐚ᵢ ⊆ (𝐚ᵢ⁺)†` (in the `IsFormalAdjoint`/`†` sense from
   `Operators/Unbounded.lean`) directly, by the same style of integration-by-parts argument
   `momentumOperator_isSymmetric` already carries out for `𝐩ᵢ`.

**Why this is genuinely harder than it looks**: `𝐱ᵢ` is proven self-adjoint
(`positionOperator_isSelfAdjoint`), but `𝐩ᵢ` is currently proven **symmetric only**
(`momentumOperator_isSymmetric`), not (essentially) self-adjoint. Since `annihilationCLM`/
`creationCLM` are complex linear combinations of both, and *both* are unbounded
(`positionOperator_isUnbounded`, `momentumOperator_isUnbounded`), the cheap combination lemmas in
`Unbounded.lean` (`HasDenseDomain.adjoint_add_continuous`/`adjoint_sub_continuous`) don't apply —
those require one summand continuous. Only the weaker, domain-inclusion-only
`adjoint_add_le_add_adjoint`/`adjoint_sub_le_sub_adjoint` are available generically, which isn't
enough to conclude equality. A real domain-matching argument is needed, most likely by mimicking
`momentumOperator_isSymmetric`'s direct integration-by-parts proof for the specific combination
`𝐚ᵢ`/`𝐚ᵢ⁺` rather than composing existing self-adjointness facts formally.

**New theory needed**: the `SchwartzSubmodule`-promotion step is templated and low-risk; the
adjoint argument itself is genuinely new unbounded-operator work, and is also a prerequisite for
item 4's Phase B and for eventually promoting `numberCLM`/the Hamiltonian itself off the Schwartz
space.

**Files**: new `HarmonicOscillator/LadderOperatorsUnbounded.lean` (or extend
`LadderOperators.lean` directly), building on `Operators/Momentum.lean`'s pattern.

---

## 6. Spherical basis (Hardest)

**Current state**: `Basic.lean`'s TODO — "Determine the energy eigenstates of the isotropic
quantum harmonic oscillator in the 'spherical basis' in terms of spherical harmonics." No
spherical-harmonics infrastructure exists anywhere in physlib today (checked: no file matching
`*Spherical*` under `Physlib/`).

**Plan**:
1. Formalize spherical harmonics from scratch (or confirm there's truly nothing reusable from the
   Hydrogen/LRL angular-momentum work — that work proves commutation relations for `𝐋`, it doesn't
   construct actual spherical-harmonic functions, so this is likely a genuine gap, not a
   duplication risk).
2. Restrict to `Q.IsIsotropic` (already defined in `Basic.lean`) and build the angular-momentum
   operators for the oscillator from the existing `LadderSystem`/`toGlHom` machinery (angular
   momentum sits inside `gl(d)` as the antisymmetric generators, i.e. `so(d) ⊂ gl(d)` via
   `E i j - E j i`).
3. Construct the explicit change-of-basis (a Clebsch-Gordan-style unitary map) between the
   Cartesian Fock basis (`LadderSystem.vacuumBasis`, or item 3's explicit Hermite version) and an
   `(n, l, m)`-indexed spherical basis, at fixed total excitation number `n`.

**New theory needed**: the most of any item here — spherical harmonics as actual functions (not
just angular-momentum commutation relations), plus the isotropic-specific `so(d)`-representation
decomposition of each `vacuumSpan` sector. Should be scoped as its own multi-file effort once items
1-5 are further along, not attempted first.

**Files**: likely a new `Physlib/Mathematics/SphericalHarmonics/` directory plus
`HarmonicOscillator/SphericalBasis.lean`.
