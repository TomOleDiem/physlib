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
| 2 | T1: commutator bound: `expect_le_exp_mul`, `norm_commutator_diag_le` (MomentBound.lean); move estimates and `BoseHubbardData.sum_finiteHam_le` (LocalMoments.lean) | done |
| 3 | T1: moment Grönwall. Truncated version done: `BoseHubbardData.truncated_moment_le` (any finite set `S` of states, rate `8dK(p+1)2^{p+1}(1+ρ)` independent of `V`, `Λ`, `S`). Uniform local bound done: `BoseHubbardData.truncated_localMoment_uniform` (exponential weights, polynomial growth, constants independent of `V`, `Λ`, `S`). Open: removal of the truncation (strong resolvent convergence via T0) | in progress |
| 4 | T2: cutoff projections and cutoff error | open |
| 5 | T2: interaction picture with respect to `D` | open |
| 6 | T2: Lieb-Robinson bound for the truncated interaction | open |
| 7 | T2: assembly with `k = R^α` | open |
| 8 | T3 | open |
| 9 | T4 | open |
| 10 | T5 | open |
| 11 | T6 | open |

Milestones 0 to 3 are intermediate. They are not evidence that T2 holds.

## T1 working plan (next steps, in order)

1. Done: `expect_le_exp_mul` (MomentBound.lean). If `Re⟨φ, i[H,A]φ⟩ ≤ c Re⟨φ,Aφ⟩` for all `φ`
   (bounded `H`, `A`), then `⟨ψ_t, A ψ_t⟩ ≤ e^{ct} ⟨ψ, A ψ⟩` for `t ≥ 0`. Linear in the state, so it
   passes to density matrices and locally normal states.
2. Weighted moment. For a centre `x₀` take `A = Σ_{x∈Λ} w_x (N_x+1)^p` with
   `w_x = e^{-μ d(x, x₀)}`, so `w_x ≤ e^μ w_y` for `x ~ y` and `w_{x₀} = 1`. Then
   `ν_{x₀}(t) ≤ ⟨ψ_t, A ψ_t⟩ ≤ e^{ct} Σ_x w_x ν_x(0) ≤ e^{ct} M W`, where
   `W = sup_{x₀} Σ_x e^{-μ d(x,x₀)} < ∞` on graphs of polynomial growth (any `μ > 0`). This avoids
   Grönwall for a supremum over sites; the factor `W` is harmless.
3. Commutator form bound (pure matrix-element estimate, occupation basis). For a diagonal `F` and
   a term `T`, `|⟨φ, [T, F] φ⟩| ≤ Σ_{α,β} |T_{αβ}| |F(α) - F(β)| |φ_α| |φ_β|`, then AM-GM and row sums
   (Schur, as in `norm_sum_conj_mul_le`). For hopping and pairing on `x ~ y` each basis state has at
   most two partners, and `|T_{αβ}| |F_x(α) - F_x(β)| ≤ C_p (G_x + G_y)` at both `α` and `β`, with
   `F_x = (N_x+1)^p` and `G_z = (N_z+1)^p`, using `(n+2)^p - (n+1)^p ≤ p (n+2)^{p-1}`, Young, and
   `G(α) ≤ 2^p G(β)` for states differing by one or two bosons. The on-site `D(N)` commutes with
   every `F_x`, so it drops out (`c` independent of `D` and `U`).
4. Bounded model for step 1. Truncate each site of `Λ` at `K_max` (`P_K` diagonal). `P_K H_Λ P_K`
   acts on the occupations of `Λ` only, the same finite matrix on every outside fibre, so it is a
   bounded operator; `P_K` commutes with `D` and all `F_x`, and the truncated hopping and pairing
   terms obey the same matrix-element bounds, so step 3 holds uniformly in `K_max`.
5. Remove the truncation (no Trotter-Kato needed; PhyslibAlpha has Stone but no strong resolvent
   convergence). Take `S_K` = states supported in `Λ` with all occupations `≤ K`, `H_K` =
   `truncHam` on `S_K`, `φ_s = e^{-isH_K} ψ` (a finite vector, so in the domain of `H_Λ`), and
   `U_t` the unitary group of the closure of `H_Λ` (T0 + Stone, as in `hamPMap_dynamics`). Duhamel:
   `U_t ψ - φ_t = -i ∫_0^t U_{t-s} (H_Λ - H_K) φ_s ds`, so
   `‖U_t ψ - φ_t‖ ≤ t sup_s ‖(1 - P_{S_K}) H_Λ φ_s‖`. Only moves that raise an occupation from `K`
   to `K + 1` leave `S_K`, with amplitude `O(K)`, so
   `‖(1 - P_{S_K}) H_Λ φ_s‖² ≤ C_Λ K² Σ_x ⟨φ_s, 1_{N_x ≥ K} φ_s⟩ ≤ C_Λ K² |Λ| W M e^{cs} / K^{p+1}`
   by Chebyshev and `truncated_localMoment_uniform`. For `p + 1 > 2` this tends to `0` as
   `K → ∞`, uniformly on `[0, T]`. Then bounded cutoffs `min(G_x, R)` of the moments pass to the
   limit and `R → ∞` by monotone convergence gives T1 for `U_t`. Uses only truncated moments, so it
   is not circular.

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

## Cleanup

- `alphaPythonLinters.sh` reports about 60 lines over 100 characters and 3 non-terminal `simp`
  calls in pre-existing `InfiniteBosons` files (AtomPhoton*, BoseHubbard*, Field*, Fock*, GraphNorm,
  EssentialSelfAdjoint, ...). The files added for T0 pass. To be fixed before a PR.
- `lake exe runPhyslibAlphaLinters` (full PhyslibAlpha build, 2026-11-03): 65 findings, all in
  pre-existing `InfiniteBosons` files (unused `DecidableEq`/section arguments, one missing
  docstring in `TensorNet.splitEquiv`). None in FiniteVolume, JacobiCarleman, ModelHamiltonians,
  MomentBound.

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
