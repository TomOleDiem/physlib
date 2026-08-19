# Abstract Qubit — roadmap

Formalize the qubit from its abstract observable-algebra structure first; matrices are a
concrete instance added last. See individual `TODO "..."` entries in each file for the
proof obligations of what is already stubbed.

Working step by step; only what is checked off below has been started.

- [x] **`Basic.lean`** — `QubitAlgebra` class (generators, relations, `pauliBasis`),
      reversed products `YX/ZY/XZ` (stubbed).
- [x] **`PauliVector.lean`** — `σ(v)`, the product identity `σ(u)σ(v) = (u·v)1 + iσ(u×v)`,
      the square identity, the commutator identity (all stubbed).
- [ ] **`Observable.lean`** — uniqueness of the Pauli decomposition `a = c₀1 + c₁X + c₂Y + c₃Z`
      from `pauliBasis`; self-adjoint ⇔ real coefficients; the real-linear equivalence
      `Observable A ≃ₗ[ℝ] ℝ × (Fin 3 → ℝ)` via `(a₀, v) ↦ a₀ • 1 + σ v`.
- [ ] **Spectral/order structure** (file TBD, maybe folds into `Observable.lean`) — spectrum of
      `a₀ • 1 + σ v` is `{a₀ ± ‖v‖}` (needs deciding: `Fin 3 → ℝ` with `v ⬝ᵥ v`, or switch to
      `EuclideanSpace ℝ (Fin 3)` for a genuine norm — see the note in `PauliVector.lean`);
      positivity criterion `0 ≤ a₀1 + σ v ↔ ‖v‖ ≤ a₀`; effects, projections.
- [ ] **`State.lean`** — needs `OperatorAlgebra.State.mix`/`.IsPure` ported in (minimally
      trimmed) from the abandoned `operator-algebra` branch first. Bloch vector
      `r(ω) = (ω X, ω Y, ω Z)`; `‖r(ω)‖ ≤ 1`; the converse construction `ωᵣ`; main theorem
      `State A ≃ closedBall (0 : ℝ³) 1`.
- [ ] **Pure states** — `ω.IsPure ↔ ‖r(ω)‖ = 1` (Bloch sphere).
- [ ] **`Lie.lean`** — traceless observable sector / `skewAdjoint` copy of `i • σ(v)` as a Lie
      algebra under the commutator, identified with `(Fin 3 → ℝ, ⨯₃)`'s existing `Cross.lieRing`
      instance (`su(2)` picture). Keep separate from the C⋆-representation notion.
- [ ] **`Unitary.lean`** — needs `OperatorAlgebra.Unitary.automorphism`/`.observable` ported in
      from the abandoned branch first (wraps Mathlib's `Unitary.conjStarAlgAut`). `R_U : ℝ³ → ℝ³`
      from `U σ(v) U⋆ = σ(R_U v)`; orthogonality; lands in `Matrix.specialOrthogonalGroup (Fin 3)
      ℝ`; `R_(UV) = R_U R_V`; kernel = scalar unitaries (double cover, kernel `{±1}`).
- [ ] **`Dynamics.lean`** — `H = h₀1 + σ h`; Bloch equation `dr/dt = 2h × r` from the Pauli
      commutator, hooked into `Physlib.Mathematics.OneParameterSubgroups.Unitary` (already on
      `upstream/master`, no Stone/exponential theory to redevelop). Finite-time evolution as a
      rotation.
- [ ] **`Matrix.lean`** — last. `𝒜[Fin 2] = B(ℂ²)`, Pauli matrices, `QubitAlgebra` instance,
      then everything above specializes for free.
- [ ] **Representations** (possibly `Representation.lean`, or folded elsewhere) — keep the
      C⋆-representation `π : A → B(ℋ)` and the Lie/group representation `SU(2) → U(ℋ)` /
      `SU(2) → SO(3)` explicitly distinct; note the covariance relation
      `π(α_g a) = U_g π(a) U_g⋆`.

## Open decisions

- Bloch-vector type: currently plain `Fin 3 → ℝ` (has `⬝ᵥ`, `⨯₃` natively). Revisit once norms
  are needed — either state everything via `v ⬝ᵥ v` instead of `‖v‖²`, or switch to
  `EuclideanSpace ℝ (Fin 3)` and transport `⨯₃` through `Mathlib`'s existing
  `norm_ofLp_crossProduct`/`toLp`/`ofLp` bridge.
