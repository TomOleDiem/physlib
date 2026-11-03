# Goal: infinite-volume dynamics of the Bose-Hubbard model with pairing

Status file for the thermodynamic-limit construction. Code lives under
`PhyslibAlpha/QuantumMechanics/InfiniteBosons/`. Nothing here is done until it builds without
`sorry` and passes the linters. This is a research program, not a verified theorem statement.

## Setting

- Geometry. `L` with a `SimpleGraph` of degree at most `d` and polynomial volume growth
  `|B_R(x)| ≤ C (1+R)^ν` for all `x`, `R`. These are separate hypotheses on the existing crystal
  and graph structures, not part of the local-net definition. Bounded degree alone is not enough
  for the cutoff argument: on a regular tree `|B_R| ~ 2^R` and polynomial cutoffs fail. General
  bounded-degree graphs are a later extension.
- Hamiltonian `H_Λ = D_Λ(N) + B_Λ` on a finite region `Λ`.
  - `D_Λ = Σ_{x∈Λ} D_x(N_x)` with arbitrary real functions `D_x : ℕ → ℝ`. No sign condition in the
    dynamical theorems. `D_Λ` commutes with every `F(N_x)`.
  - `B_Λ = Σ_{x~y} (h_xy a_x† a_y + Δ_xy a_x† a_y† + h.c.)`, nearest neighbour,
    `|h_xy|, |Δ_xy| ≤ K`. Translation-invariant pairing is allowed. Particle number is not
    conserved.
- Observables. The net `tensorNet (fun _ => ℕ)`, `A(X) = B(ℓ²(ℕ^X))`. First for local finite-rank
  operators in the occupation basis, then for other bounded local operators.
- States. `S_{p,M}`: locally normal states with `sup_x ω((N_x+1)^p) ≤ M`. Working moment order
  `p > 2ν + 2` (the Deuchert-Lampart-Lemm value); pairing may force a larger `p`, which is then
  recorded here.

## Theorems, in dependency order

T0. Finite-volume dynamics. `H_Λ` is essentially self-adjoint on finite vectors for arbitrary real
`D`. Route: total-number sectors are finite-dimensional, `D` and hopping act inside a sector,
pairing couples `n` to `n ± 2` with blocks of norm `O(|Λ| (n+1))`, so a block-Jacobi Carleman
criterion applies (to be checked: Berezanskii's operator-valued version). Kato-Rellich is not used.
Defines `α_t^Λ`.

T1. Uniform moments. `sup_x ω(α_t^Λ((N_x+1)^p)) ≤ e^{c_p|t|} M` for `ω ∈ S_{p,M}`, with `c_p`
depending only on `p`, `d`, `K`, not on `Λ` or `D`. Proof through the commutator bound
`±i[B_xy,(N_x+1)^p] ≤ C_p(|h_xy|+|Δ_xy|)((N_x+1)^p+(N_y+1)^p)` and Grönwall. An occupation
truncation `K_max` may be used as a proof device and is removed inside this theorem.

T2. Cutoff-locality estimate (central, new). For local finite-rank `A ∈ A(X)`,

    lim_{R→∞} sup_{|t|≤T, ω∈S_{p,M}, ‖B‖≤1} |ω((α_t^Λ(A) - α_t^{X_R}(A)) B)| = 0

uniformly in finite `Λ ⊇ X_R`. Ingredients: cutoff projections `P_{Y,k}` with error controlled by
T1, interaction picture with respect to `D` (supports preserved, truncated strength `O(k)`), a
Lieb-Robinson bound for the truncated time-dependent interaction, `k = R^α`. Analogue of
Deuchert-Lampart-Lemm Theorem 4.1 without number conservation.

T3. State evolution. For `ω ∈ S_{p,M}`, `ω_t(A) = lim_{Λ↑L} ω(α_t^Λ(A))` exists, is independent
of the exhaustion, uniform for `|t| ≤ T`, and `ω_t ∈ S_{p, e^{c_p|t|}M}`. The group law
`(ω_t)_s = ω_{t+s}` and continuity in `t` are proved from T2, not from one-point convergence.

T4. Observable dynamics. For `ω ∈ S_{p,M}`, the finite-volume evolutions `α_t^Λ(A)` converge in
the GNS seminorm `‖A‖_{2,ω} = ω(A†A)^{1/2}` on an explicitly defined algebra. Composition and
continuity in this topology.

T5. GNS implementation. For an invariant `ω`, `U_ω(t) π_ω(A) Ω_ω = π_ω(α_t(A)) Ω_ω` defines a
strongly continuous unitary group. Its generator comes from Stone's theorem.

T6. Consistency. For `Δ = 0` the dynamics agrees with the number-conserving construction
(Deuchert-Lampart-Lemm; Buchholz algebra branch `claude/buchholz-import`).

Equilibrium (separate). Ground and KMS states need their own hypotheses: stability such as
`D_x(n) ≥ c n² - C`, and moment bounds for finite-volume Gibbs states. With `U < 0` the finite
volume Hamiltonian is unbounded below and `e^{-βH_Λ}` is not trace class.

## Milestones

| # | Content | Status |
|---|---|---|
| 0 | ℓ² no-go: pairing bounded away from zero on infinitely many disjoint bonds gives `hamDomainAlg = ⊥` (`BoseHubbardData.hamDomainAlg_eq_bot`, ModelHamiltonians.lean) | done |
| 1 | T0: block-Jacobi Carleman criterion (`blockJacobi_no_l2_solution`, JacobiCarleman.lean) and `BoseHubbardData.finiteHam_isEssentiallySelfAdjoint` for arbitrary real on-site `V` (FiniteVolume.lean) | done |
| 2 | T1: commutator bound | open |
| 3 | T1: moment Grönwall | open |
| 4 | T2: cutoff projections and cutoff error | open |
| 5 | T2: interaction picture with respect to `D` | open |
| 6 | T2: Lieb-Robinson bound for the truncated interaction | open |
| 7 | T2: assembly with `k = R^α` | open |
| 8 | T3 | open |
| 9 | T4 | open |
| 10 | T5 | open |
| 11 | T6 | open |

Milestones 0 to 3 are intermediate. They are not evidence that T2 holds.

## Where Deuchert-Lampart-Lemm use number conservation

Read from arXiv:2505.13170 (graph `d`-dimensional with surface parameter σ, `p > 2d + 2`):

1. Prop. 4.10, eq. (49): the moment Grönwall is run on the regularized state
   `1_{N ≤ K} ρ 1_{N ≤ K}`, which needs `[H, N] = 0`. The commutator bound (52)-(53) itself does
   not use conservation. Replacement here: truncate `H_Λ` at `K_max` per site (finite-dimensional),
   prove the moment bound uniformly in `K_max`, and remove the truncation by strong resolvent
   convergence on the finite-vector core. This step uses T0.
2. Lemma 4.11 (cutoff `P_{Y,λ}`, eq. (59)) and Theorem 4.3: the observable `A ∈ R^inv_X` commutes
   with `N_X`. Replacement: observables of finite occupation transfer; the error terms then pick
   up a bounded number of extra factors of `(N_x + 1)^{1/2}`, to be absorbed by higher moments.
3. Their observables live in the invariant resolvent algebra and states on the Buchholz algebra.
   With pairing the gauge-invariant algebras are not preserved; use `tensorNet (fun _ => ℕ)`.

## Known risk

T2 with pairing is not in the literature. The published construction uses particle-number
conservation and gauge-invariant observables in the cutoff-locality estimate. T1 is the reason to
expect the extension to work. If an estimate fails, it is recorded here with the failing step, not
replaced by a hypothesis.

## References

- A. Deuchert, J. Lampart, M. Lemm, Dynamics and equilibrium states of infinite systems of lattice
  bosons, arXiv:2505.13170.
- D. Buchholz, The resolvent algebra of non-relativistic Bose fields, Commun. Math. Phys. 362 (2018).
- Tong, Kuwahara, Gong, Clustering theorem for Bose-Hubbard class Gibbs states, Commun. Math. Phys.
  (2026). Not yet checked; relevant for T0, T1 and equilibrium.
