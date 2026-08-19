# Abstract Qubit — roadmap

See also `notes.md` for research notes on where this is headed (Jordan/Lie structure, CCR/Fock
for the oscillator, the Lindblad hierarchy) — not all queued yet, but the map of the territory.

Formalize the qubit from its abstract observable-algebra structure first; matrices are a
concrete instance added last. See individual `TODO "..."` entries in each file for the
proof obligations of what is already stubbed.

Working step by step; only what is checked off below has been started.

- [x] **`Basic.lean`** — `QubitAlgebra` class (generators, relations, `pauliBasis`),
      reversed products `YX/ZY/XZ` (stubbed).
- [x] **`PauliVector.lean`** — `σ(v)`, the product identity `σ(u)σ(v) = (u·v)1 + iσ(u×v)`,
      the square identity, the commutator identity (all stubbed).
- [x] **`Observable.lean`** — `coeff` (real, from `pauliBasis.repr`, uniqueness is free); the
      self-adjoint ⇔ real-coefficients characterization and `observableEquiv : Observable A
      ≃ₗ[ℝ] ℝ × (Fin 3 → ℝ)` via `(a₀, v) ↦ a₀ • 1 + σ v` (both stubbed).
- [x] **`Spectrum.lean`** — `spectrum ℝ (a₀ • 1 + σ v) = {a₀ ± ‖v‖}` and the positivity criterion
      `0 ≤ a₀ • 1 + σ v ↔ ‖v‖ ≤ a₀` (both stubbed). Norms of `v : Fin 3 → ℝ` go through
      `WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3)` — see the open decision below, now resolved.
- [x] **`Effect.lean`** — effects `0 ≤ E ≤ 1` iff `‖v‖ ≤ min a₀ (1 - a₀)`; projections
      (`IsStarProjection`) iff spectrum `⊆ {0, 1}`; the nontrivial ones forced to `a₀ = ‖v‖ =
      1/2` — rank-one projections, one per direction on the Bloch sphere of radius `1/2` (all
      stubbed). This finishes roadmap §4.
- [x] **`Physlib/Mathematics/OperatorAlgebra/State.lean`** — ported in, trimmed to exactly what
      `Qubit/State.lean` needs: `instCoeFun`, `apply_one`, `apply_nonneg`,
      `apply_selfAdjoint_im_eq_zero`/`observable_im_eq_zero`, `mix`, `IsPure`. All real, proven
      (not stubs) — probabilities-of-effects and pullback-of-states were left out, not needed
      here; pull them back in from physlib's history if something later needs them.
- [x] **`Qubit/State.lean`** — `r` (real, Bloch vector); `norm_r_le_one`; the converse
      `ofBlochVector`/`r_ofBlochVector`; the main theorem `stateEquivClosedBall : State A ≃
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1`; purity
      `isPure_iff_norm_r_eq_one : ω.IsPure ↔ ‖r ω‖ = 1` (all stubbed). Finishes roadmap §5–6.
- [x] **`Lie.lean`** — `τ v = -i/2 • σ v` (the `su(2)`-normalized generator), skew-adjoint
      (stubbed); `τ u * τ v - τ v * τ u = τ (u ⨯₃ v)` *exactly*, no leftover scalar (stubbed) —
      `τ` is a genuine Lie ring homomorphism from `Cross.lieRing` on `Fin 3 → ℝ` to `A`'s
      commutator. Also added `Qubit.isSelfAdjoint_σ` to `PauliVector.lean` as a small
      prerequisite. Kept separate from the C⋆-representation notion, per the roadmap.
- [x] **`Physlib/Mathematics/OperatorAlgebra/Unitary.lean`** — ported in, trimmed to
      `automorphism`/`automorphism_apply`/`observable`/`coe_observable(_eq)`. Real, proven, not
      stubs (mostly just Mathlib's `Unitary.conjStarAlgAut` repackaged). Effects/projections
      left out, not needed here.
- [x] **`Qubit/Unitary.lean`** — `R U : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)` characterized by
      `coe_R : U σ(v) U⋆ = σ(R U v)`; isometry (`norm_R_apply`); composition law `R (U*V) = (R
      U).comp (R V)` (verified the order from `Unitary.conjStarAlgAut`'s `map_mul'` before
      stating it); `R_one`. All stubbed.
- [x] **`SO(3)`, abstractly, no matrices** — `det_R_eq_one` (`LinearMap.det` is already
      basis-independent) and `IsRotation`/`isRotation_R` (norm-preserving + `det = 1`; the
      latter is a real, non-stubbed corollary — just tupling the two stubbed facts, no new
      axiom). Still not started: identifying the kernel with the scalar unitaries — the `SU(2)
      → SO(3)` double cover, kernel `{±1}`.
- [x] **`Physlib/Mathematics/OperatorAlgebra/Dynamics.lean`** (new, general, not qubit-specific)
      — the levels of dynamics: `Channel A A` (already existed, timeless/no time index, the
      baseline) ⊂ `DynamicalSemigroup A` (`ℝ≥0 → Channel A A`, semigroup law, possibly
      irreversible) ⊂ `AutomorphismGroup A` (`ℝ → (A ≃⋆ₐ[ℂ] A)`, group law, fully reversible —
      where Hamiltonian/unitary evolution lives). Structures only, real (not stubbed) — the
      *inclusion* `AutomorphismGroup A → DynamicalSemigroup A` is logged as a TODO in the file
      itself, blocked on "⋆-algebra automorphisms are completely positive" not yet being in
      Mathlib.
- [x] **`Qubit/Dynamics.lean`** — `unitaryEvolution Hobs t = exp(-it Hobs)`, built directly from
      Mathlib's `selfAdjoint.expUnitary` (not `OneParameterSubgroups.Unitary`, which turned out
      to be Hilbert-space-specific, `H →L[ℂ] H` — `expUnitary` is genuinely abstract, works
      for any `CStarAlgebra A`, and is a better fit). `unitaryEvolution_zero/_add` (group law);
      `hamiltonianFlow : AutomorphismGroup A`; `blochTrajectory`; the Bloch equation
      `hasDerivAt_blochTrajectory : dr/dt = 2 h ⨯₃ r`, TODO spells out why only the traceless
      part `h` survives. All stubbed. Finishes roadmap §9.
- [x] **`Physlib/Mathematics/OperatorAlgebra/JordanLie.lean`** (renamed from `Jordan.lean`; new,
      general, not qubit-specific) — the Jordan product `jordan a b = ½(ab+ba)` and observable Lie
      bracket `obsBracket a b = -i(ab-ba)` on `Observable A`, and `mul_eq_jordan_add_obsBracket :
      ab = a∘b + (i/2)⁅a,b⁆ₒ`. **Fully proved, no `sorry`s.** Then: `⁅·,·⁆ₒ` is registered as a
      genuine `LieRing (Observable A)`/`LieAlgebra ℝ (Observable A)` instance (Mathlib's real
      notion, `Mathlib.Algebra.Lie.OfAssociative`), Jacobi identity transported from the ring
      commutator on `A`; and `jordan_comm`/`jordan_jordan_identity` prove the Jordan identity
      `(a∘a)∘(b∘a) = ((a∘a)∘b)∘a` directly (not via a registered `IsCommJordan` instance — that's
      logged as a `TODO` in the file: needs `Invertible (2 : A)` and care to avoid a `Mul`
      diamond with `selfAdjoint`'s own instance when `A` is commutative). **Correction:** an
      earlier pass invented a bespoke `JordanRing`/`JordanAlgebra` class before realizing Mathlib
      already has `IsJordan`/`IsCommJordan`/`SymAlg` (`Mathlib.Algebra.Jordan.Basic`,
      `Mathlib.Algebra.Symmetrized`) — the invented class was removed, the concrete lemmas kept.
      See `notes.md` §1–2 for how this connects to the qubit's dot/cross product (not yet formally
      connected).
- [x] **`Qubit/AdjointAction.lean`** — Stone's theorem for `SO(3)`: `adjointAction Hobs : v ↦ 2 •
      (h ⨯₃ v)` (real, no proof needed — `2 •` a partially-applied `crossProduct` is linear for
      free) is the generator of `rotationFlow Hobs t := R (unitaryEvolution Hobs t)`, the
      one-parameter rotation group `Qubit.R` pushes `Qubit.unitaryEvolution` down to.
      `isRotation_rotationFlow` is real (from `isRotation_R`); `rotationFlow_zero`/`_add` and
      `hasDerivAt_rotationFlow_apply` (restating `hasDerivAt_blochTrajectory` around the named
      generator) are stubbed. Noted, not yet checked: the relationship between `adjointAction` and
      the abstract Lie-algebra `ad` that `JordanLie.lean`'s new `LieAlgebra ℝ (Observable A)`
      instance now makes available.
- [ ] **`SO(3)` kernel/double cover** — identifying `Qubit.R`'s kernel with the scalar unitaries,
      `SU(2) → SO(3)`, kernel `{±1}`. Not started.
- [ ] **`Matrix.lean`** — last. `𝒜[Fin 2] = B(ℂ²)`, Pauli matrices, `QubitAlgebra` instance,
      then everything above specializes for free.
- [ ] **Representations** (possibly `Representation.lean`, or folded elsewhere) — keep the
      C⋆-representation `π : A → B(ℋ)` and the Lie/group representation `SU(2) → U(ℋ)` /
      `SU(2) → SO(3)` explicitly distinct; note the covariance relation
      `π(α_g a) = U_g π(a) U_g⋆`.

## Resolved decisions

- Bloch-vector type: stayed with `Fin 3 → ℝ` (has `⬝ᵥ`, `⨯₃` natively) rather than switching to
  `EuclideanSpace ℝ (Fin 3)`. Norms are only ever needed at the boundary (spectrum, positivity,
  later the Bloch ball and `SO(3)`), so those statements wrap the vector in `WithLp.toLp 2 v :
  EuclideanSpace ℝ (Fin 3)` locally instead of changing the type everywhere — this is the same
  pattern Mathlib itself uses in `InnerProductGeometry.norm_toLp_symm_crossProduct`. Keeps
  `Basic.lean`/`PauliVector.lean`/`Observable.lean` untouched and avoids ever writing a bare
  `‖v‖` for `v : Fin 3 → ℝ`, which would silently pick up the wrong (sup) norm if one were ever
  registered for that type.
