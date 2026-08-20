# Abstract Qubit — roadmap

See also `notes.md` for research notes on where this is headed (Jordan/Lie structure, CCR/Fock
for the oscillator, the Lindblad hierarchy) — not all queued yet, but the map of the territory.

Formalize the qubit from its abstract observable-algebra structure first; matrices are a
concrete instance added last. See individual `TODO "..."` entries in each file for the
proof obligations of what is already stubbed.

Working step by step; only what is checked off below has been started.

- [x] **`Basic.lean`** — `QubitAlgebra` class now extends `[OperatorAlgebra A]` (the bundled
      C⋆-algebra + order class from `Physlib/QuantumMechanics/OperatorAlgebra/Basic.lean`,
      after that file's move out of `Mathematics/`) instead of the separate
      `[CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]` trio; propagated through every
      other qubit file. Reversed products `YX/ZY/XZ` (`gen_mul_cyc_symm`) — **fully proved**, not
      stubbed, from `star`-ing `gen_mul_cyc` and self-adjointness of each generator.
      `pauliBasis`/`pauliBasis_eq` stay class fields — a pass restating them as
      `finrank_eq_four` + `linearIndependent_cons_gen` and deriving `pauliBasis` from
      `basisOfLinearIndependentOfCardEqFinrank` was tried and reverted: dimension-count +
      independence is exactly as strong as "is a basis", just spelled differently, so nothing
      was actually derived. See the next item for the real way to earn this as a theorem.
- [x] **`Presentation.lean` — construct the qubit algebra from generators and relations.**
      `PauliAlgebra := QuaternionAlgebra ℂ (-1) 0 (-1)` (Hamilton's quaternions with complex
      coefficients — *not* matrices): `gen i := I • (the i-th quaternion unit)` satisfies
      `gen_sq`/`gen_mul_cyc`/`gen_mul_cyc_symm`, and `pauliBasis`/`pauliBasis_eq` are **proved**
      (`1, gen 0, gen 1, gen 2` genuinely a basis), not assumed — via an explicit coordinate
      `LinearEquiv` to `Fin 4 → ℂ` transporting the standard basis. **Fully proved, no `sorry`s,
      no matrices.** The associativity/spanning/independence content that a from-scratch
      `FreeAlgebra`-quotient-plus-confluence argument would have to establish by hand comes for
      free by recognizing the Pauli relations as a relabelling of an algebra Mathlib already
      built and proved associative. See the module docstring for why this isn't in tension with
      the earlier `SO(3)`/`{±1}`-kernel "no matrices" correction (that was about *definitions* on
      a general `A`; here there is no general `A`), and for exactly where a genuine matrix
      representation *would* still be needed (promoting `PauliAlgebra` to an actual
      `QubitAlgebra` instance needs a C⋆-norm, forced by C⋆-norm uniqueness to be the transport
      of `Matrix (Fin 2) (Fin 2) ℂ`'s operator norm — that's `Qubit/Matrix.lean`, not done here).
      Doesn't change `QubitAlgebra`'s fields — an existence witness, not a replacement for
      `pauliBasis` as a hypothesis; an arbitrary `QubitAlgebra A` can still be a strictly larger
      algebra.
- [x] **`PauliVector.lean`** — `σ(v)`, the product identity `σ(u)σ(v) = (u·v)1 + iσ(u×v)`,
      the square identity, the commutator identity. **Fully proved, no `sorry`s**: expand `σ u`,
      `σ v` into their three generator terms (`Fin.sum_univ_three`), substitute the Pauli
      relations on each of the 9 generator products, close with `module`. Also proved
      `isSelfAdjoint_σ` and a small `σ_neg` helper.
- [x] **`Observable.lean`** — `coeff` (real, from `pauliBasis.repr`, uniqueness is free); the
      self-adjoint ⇔ real-coefficients characterization (`isSelfAdjoint_iff_coeff`) and
      `observableEquiv : Observable A ≃ₗ[ℝ] ℝ × (Fin 3 → ℝ)` via `(a₀, v) ↦ a₀ • 1 + σ v`.
      **Fully proved, no `sorry`s.** New helper lemmas along the way: `isSelfAdjoint_pauliBasis`
      (every basis element is `1` or a generator, hence self-adjoint), `coeff_eq_of_eq_sum` (read
      off coefficients from *any* explicit `pauliBasis` combination, not just the canonical
      `Basis.repr` one — used repeatedly), `coeff_star` (`star` conjugates every coefficient),
      `real_smul_eq_ofReal_smul` (bridges the `ℝ`- and `ℂ`-scalar actions on `A`, needed for
      `observableEquiv`'s `map_smul'`).
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
      (`τ_mem_skewAdjoint`); `τ u * τ v - τ v * τ u = τ (u ⨯₃ v)` *exactly*, no leftover scalar
      (`τ_mul_sub_mul`). **Fully proved, no `sorry`s.** Initially left as just this
      bracket-compatibility fact, which the user correctly pointed out is not yet an
      *isomorphism* — fixed by adding `τ_injective` (from `σ`'s injectivity, itself from the
      three generators being a linearly-independent sub-family of `QubitAlgebra.pauliBasis`),
      registering `Fin 3 → ℝ` as a genuine `LieAlgebra ℝ` (`Cross.lieRing` is only a `LieRing` in
      Mathlib) and bringing `A`'s commutator into scope via `LieRing.ofAssociativeRing`, bundling
      `τ` as an actual `LieHom` (`τHom`), and concluding with `τLieEquiv : (Fin 3 → ℝ) ≃ₗ⁅ℝ⁆
      τHom.range` via `LieEquiv.ofInjective` — a genuine, checked `LieEquiv`, not just a
      bracket-compatible map. Kept separate from the C⋆-representation notion, per the roadmap.
- [x] **`Physlib/Mathematics/OperatorAlgebra/Unitary.lean`** — ported in, trimmed to
      `automorphism`/`automorphism_apply`/`observable`/`coe_observable(_eq)`. Real, proven, not
      stubs (mostly just Mathlib's `Unitary.conjStarAlgAut` repackaged). Effects/projections
      left out, not needed here.
- [x] **`Qubit/Unitary.lean`** — `R U : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)` characterized by
      `coe_R : U σ(v) U⋆ = σ(R U v)`; isometry (`norm_R_apply`); composition law `R (U*V) = (R
      U).comp (R V)` (verified the order from `Unitary.conjStarAlgAut`'s `map_mul'` before
      stating it); `R_one`. All stubbed. **`R`'s TODO was sharpened** once `observableEquiv`
      became available: `R U v := (observableEquiv ⟨automorphism U (σ v), _⟩).2`, and the one
      remaining piece of content is that the *scalar* component of `observableEquiv (...)` is `0`
      — which reduces to `trace` being conjugation-invariant (`trace (U a U⋆) = trace a`, from
      cyclicity `trace (x y) = trace (y x)` plus `U⋆ U = 1`), and cyclicity itself is checkable
      abstractly by bilinear extension from the four `pauliBasis` elements (no matrices; see the
      TODO in the file for the full worked argument). The math is checked and correct; the Lean
      formalization of the bilinear-extension bookkeeping is not yet done — a first attempt got
      tangled in `Finset.sum`/`Basis.repr` manipulation and was reverted rather than left broken.
- [x] **`SO(3)`, abstractly, no matrices** — `det_R_eq_one` (`LinearMap.det` is already
      basis-independent) and `IsRotation`/`isRotation_R` (norm-preserving + `det = 1`; the
      latter is a real, non-stubbed corollary — just tupling the two stubbed facts, no new
      axiom).
- [x] **`Qubit/Observable.lean`: trace and determinant, still no matrices** — `trace a = 2 *
      coeff a 0` and `det a = (trace a ^ 2 - trace (a * a)) / 2` (the `2 × 2` Cayley–Hamilton
      formula). **Both fully proved, real defs, no `sorry`s** — a determinant is exactly as
      abstract as `SO(3)` already was: just a formula in `Qubit.coeff`/`QubitAlgebra.pauliBasis`,
      no chosen matrix representation. Also proved: `pauliBasis_zero`, `coeff_one_zero`,
      `trace_one`, `trace_smul`, `det_smul_one : det (c • 1) = c ^ 2`.
- [x] **Kernel of `R`** — `IsScalarUnitary` (real def: `U = c • 1`, `‖c‖ = 1`) and
      `R_eq_id_iff_isScalarUnitary : R U = LinearMap.id ↔ IsScalarUnitary U` (one `sorry`; TODO
      spells out both directions — the reverse is easy, the forward needs "`A`'s center is
      exactly the scalars," a form of Schur's lemma not yet available): this is the honest kernel
      for `Unitary A`, the *full* unitary group — an abstract circle `U(1)`, not `{±1}`.
      `IsSpecialUnitary U := det (U:A) = 1` (real def) then gives the familiar textbook statement,
      `R_eq_id_iff_eq_one_or_eq_neg_one_of_isSpecialUnitary` (stubbed): among special unitaries,
      `R`'s kernel is exactly `{1, -1}` — genuinely the `SU(2) → SO(3)` double cover, entirely
      matrix-free. (An earlier pass wrongly claimed this last step needed `Matrix.lean`; it
      doesn't — corrected once caught.)
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
      for any `CStarAlgebra A`, and is a better fit). `unitaryEvolution_zero/_add` (group law) and
      `hamiltonianFlow : AutomorphismGroup A` — **fully proved/constructed, no `sorry`s**, from
      `selfAdjoint.expUnitary_zero`/`Commute.expUnitary_add` and `automorphism`'s multiplicativity.
      `blochTrajectory` (built from `Qubit.R`, so still tagged `sorryful`) and the Bloch equation
      `hasDerivAt_blochTrajectory : dr/dt = 2 h ⨯₃ r` (blocked on `Qubit.R`, TODO spells out why
      only the traceless part `h` survives) remain stubbed. Finishes roadmap §9.
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
      (h ⨯₃ v)` is the generator of `rotationFlow Hobs t := R (unitaryEvolution Hobs t)`, the
      one-parameter rotation group `Qubit.R` pushes `Qubit.unitaryEvolution` down to.
      `adjointAction`/`adjointAction_apply` are now **fully proved, no `sorry`s** — they were only
      tagged `sorryful` because they depend on `Qubit.observableEquiv`, which is now real;
      untagged once `Observable.lean`'s work landed. `rotationFlow`/`isRotation_rotationFlow` (via
      `Qubit.R`/`isRotation_R`) and `rotationFlow_zero`/`_add`/`hasDerivAt_rotationFlow_apply`
      remain blocked on `Qubit.R`. Noted, not yet checked: the relationship between
      `adjointAction` and the abstract Lie-algebra `ad` that `JordanLie.lean`'s
      `LieAlgebra ℝ (Observable A)` instance now makes available.
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
