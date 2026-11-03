# Goal: infinite-volume dynamics of interacting lattice fermions

Status file. Code under `PhyslibAlpha/QuantumMechanics/LatticeFermions/` unless an audit finds a
better existing home. Nothing is done until it builds without `sorry` and passes the linters.

## Target theorem

`Γ` a countable graph of uniformly bounded degree, finitely many fermionic modes per vertex.
`H_Λ = Σ_{x∈Λ} D_x + Σ_{X⊆Λ} Φ(X)` with

- `D_x` arbitrary even self-adjoint on-site operators (each bounded since a site has finitely many
  modes; no uniform bound, no sign condition);
- `Φ(X)` even self-adjoint interactions of uniformly bounded finite range and strength,
  `J = sup_x Σ_{X∋x} |X| ‖Φ(X)‖ < ∞` (the `D_x` do not enter `J`);
- no particle-number conservation.

Main theorem (completion criterion, milestone 6). For every local CAR observable `A`,
`α_t(A) = lim_{Λ↑Γ} e^{itH_Λ} A e^{-itH_Λ}` exists in operator norm, uniformly for `t` in compact
intervals, and

1. the limit is independent of the exhaustion;
2. `(α_t)` is a strongly continuous group of *-automorphisms of the quasi-local CAR algebra;
3. it preserves parity;
4. local observables lie in the domain of the generator,
   `δ(A) = i Σ_{X ∩ supp A ≠ ∅} [Φ(X), A] + i Σ_{x ∈ supp A} [D_x, A]`.

Afterwards (milestone 7): `ω_t = ω ∘ α_t` for every state; invariant states give strongly continuous
unitary implementations in their GNS representations (Stone's theorem for the generator).

Examples (milestone 8): Hubbard with arbitrary `U_x`, `μ_x`; extended Hubbard with `V_xy n_x n_y`;
translation-invariant pairing `Δ c†_{x↑} c†_{y↓} + h.c.`; one model with quartic interaction and
nonzero pairing together.

## Key simplifications

- Interaction picture with respect to `D_Λ = Σ D_x`: `Φ̃_t(X) = e^{itD} Φ(X) e^{-itD}` keeps
  support `X` and norm `‖Φ(X)‖`. The Lieb-Robinson velocity is independent of the on-site terms.
- For the thermodynamic limit only even-odd locality is needed:
  `X ∩ Y = ∅, A ∈ 𝒜_X, B ∈ 𝒜_Y^even ⟹ [A, B] = 0`. All interaction terms are even, so ordinary
  commutators suffice in the Duhamel argument even for odd `A`. Abstraction: local C*-algebras with a
  distinguished even part commuting with disjoint local algebras. Spin systems are the case where
  everything is even. The full graded Lieb-Robinson bound must not block milestone 6.

## Milestones

| # | Content | Status |
|---|---|---|
| 0 | Audit: existing CAR, Fock, local-net, quasi-local and inductive-limit C*-code in Physlib and PhyslibAlpha | done (see Audit) |
| 1 | Finite local CAR algebras `𝒜_X`, inclusions, CAR relations across sites, parity `Θ`, even-odd locality, quasi-local C*-algebra | done: `FockSpace`, `CARNet` (`carNet`, `carLocal`), `GradedLocalNet` (`quasiLocal`, `ofClosure`) |
| 2 | Interactions `Φ(X) ∈ 𝒜_X`: even, self-adjoint, finite range, norm `J`; on-site `D_x` separate; hopping, pairing, Hubbard, density terms instantiate it | done: `Interaction` (`hamiltonian`, `IsBoundedBy`, `LocallyFinite`), `CARDynamics.HasFiniteRange`, terms `hopTerm`, `pairTerm`, `numOp`, `Hubbard.density` |
| 3 | Finite-volume dynamics `α_t^Λ`: group law, isometry, parity, Heisenberg equation (finite-dimensional) | done: `FiniteDynamics` (any bounded `H` in a C*-algebra) |
| 4 | Lieb-Robinson bound `‖[α_t^Λ(A), B]‖ ≤ C e^{v|t| - μ d(X,Y)}` for `B` even, constants independent of `Λ` and of `D` | done in chain form: `LiebRobinson.lieb_robinson`; metric form `CARDynamics.lieb_robinson_exp_abs` (`C e^{v|t| - μ n}`, `v = 2 J e^{μR}`);, `‖[α_t A, B]‖ ≤ 2‖A‖‖B‖ Σ_k (2t)^k/k! w_k(X,Y)` (no `D`); metric form is a corollary not needed for 5-6 |
| 5 | Duhamel Cauchy estimate, norm convergence and exhaustion independence | done: `ThermodynamicLimit` (`norm_evolution_sub_evolution_le`, `norm_evolution_sub_le_tail_abs`, `uniformCauchySeqOn_evolution`); limits in milestone 6 |
| 6 | Infinite-volume automorphism group and generator on local elements | done: `InfiniteDynamics` (abstract) and `CARDynamics.car_dynamics` (CAR net, finite range on a locally finite graph, `IsBoundedBy J`, arbitrary on-site terms) |
| 7 | States and GNS unitary implementation | done: `StateDynamics` (`evolveState`, `gnsEvolution`, unitarity, covariance, strong continuity; Stone: `gnsGenerator`, `isSelfAdjoint_gnsGenerator`, `gnsEvolution_eq_exp`, `Interaction.gnsGenerator_local`) |
| 8 | Physical model instances, including a non-number-conserving one | done: `HubbardModels` (`interaction`, `hasFiniteRange`, `isBoundedBy`, `dynamics_exists`; examples `hubbard`, `extendedHubbard`, `pairing` (no number conservation), `hubbardPairing`) |

Not needed initially: infinite-volume Fock operators, formal Hamiltonians, occupation cutoffs,
Gibbs states, conditional expectations, spectral flow.

## Open items

- Metric Lieb-Robinson bound on graphs: done for all times (`CARDynamics.lieb_robinson_exp`,
  `lieb_robinson_exp_abs`).
- The graded (odd-odd) Lieb-Robinson bound is not needed and not done.
- The main theorem holds for any locally finite graph and any set of modes; bounded degree and
  finitely many modes per vertex enter only through `IsBoundedBy J` (e.g. `Hubbard.isBoundedBy`).

## Next physics targets (not started)

Infinite-volume ground states, KMS states, translation covariance, symmetry breaking.

## Design notes (milestones 1-4)

- Local algebras are norm closed (`GradedLocalNet.isClosed_loc`); the CAR local algebra is the
  closure of the generated star algebra (`GradedLocalNet.ofClosure`), so no finite-dimensionality
  argument is needed.
- `FockSpace M` is a type synonym (`def`) of `ℓ²(Finset M)` with its instances re-declared: with
  `abbrev`, `star_neg`/`neg_mul` fail to rewrite on `FockSpace M →L[ℂ] FockSpace M` because two
  instance paths for the additive structure of `lp` are not reducibly equal.
- Interaction picture: the step of the LR bound uses `β_t` = dynamics of `H_Λ - K_X`, which on
  `𝒜_X` equals the dynamics of `D_X` (`Interaction.evolution_sub_interactionAt_mem`), and the
  identity `‖[α_t A, B]‖ = ‖[β_t A, β_t α_{-t} B]‖`. The derivative of `s ↦ β_s α_{-s} B` has
  norm `‖[α_s K_X, B]‖`, independent of `D`.
- The LR bound is in chain-weight form; with local finiteness (`Interaction.LocallyFinite`) and
  `IsBoundedBy J` this suffices for the thermodynamic limit, without a graph metric. The graph
  hypotheses (bounded degree, finite range) imply local finiteness.

## Audit (milestone 0)

What exists, and whether it is reused:

- `PhyslibAlpha/ProbabilisticTheory/QuasiLocal/{AlgebraNet,State,Limit}`: nets of unital
  `*`-algebras over `Finset S` with the algebraic direct limit (`Mathlib.Algebra.Colimit`).
  No norm, no completion, no grading. States of the direct limit from compatible local states.
  Not usable for norm limits of dynamics as it stands (no C*-norm on the direct limit).
- `PhyslibAlpha/CondensedMatter/QuasiLocal/{Local,Instances,Interaction,Gibbs,...}`: tensor
  product (spin) nets `Matrix (Cfg Ω X) (Cfg Ω X) ℂ` with `M ↦ M ⊗ 1`; `Interaction` = Hermitian
  term per region; finite-volume Hamiltonian and Gibbs states. Ungraded: the inclusions `M ↦ M ⊗ 1`
  are wrong for fermions (Jordan-Wigner strings are not local), so not reused for the CAR net.
- `PhyslibAlpha/QuantumMechanics/InfiniteBosons/`: `HilbertSp B = lp (fun _ : B => ℂ) 2`,
  `TensorNet` (net `B(ℓ²(Ω^X))` by amplification), `LocalAlgebra.LocalGenerators` (star
  subalgebras of an ambient algebra generated by site generators, commutation of disjoint
  supports, formal derivation `delta`), unbounded-operator machinery for bosons. The ambient-
  algebra pattern of `LocalGenerators` is the one adopted here; the bosonic files themselves are
  not imported (all-commuting generators, unbounded operators).
- `PhyslibAlpha/ProbabilisticTheory/CStarAlgebra/Automorphism`: `AutomorphismGroup A`, a
  one-parameter group of `⋆`-automorphisms (no continuity). Target for milestone 6.
- Physlib `QFT/PerturbationTheory` (`FieldSpecification`, `WickAlgebra`, `superCommute`, Koszul
  signs): an abstract free algebra modulo super-commutation for Wick's theorem; no operators, no
  norm. Not reused.
- No CAR algebra, Jordan-Wigner transformation, fermionic Fock space, Lieb-Robinson bound or
  C*-inductive limit exists in Physlib, PhyslibAlpha or Mathlib. Mathlib has `CliffordAlgebra`
  and `ExteriorAlgebra` (purely algebraic, no C*-norm), `CStarAlgebra (E →L[ℂ] E)` for a Hilbert
  space `E`, `lp` Hilbert spaces with `lp.single`, `selfAdjoint.expUnitary`,
  `Unitary.conjStarAlgAut`, `StarSubalgebra.topologicalClosure`, `StarSubalgebra.centralizer`.

Design decision. Rather than a C*-inductive limit of finite matrix algebras with Jordan-Wigner
inclusions (needs a norm on a direct limit and a completion, neither in Mathlib), the CAR
operators are realised in one ambient C*-algebra: the bounded operators on the fermionic Fock
space `ℓ²(Finset M)` over the set of modes `M` (with a linear order for the Jordan-Wigner signs).
The local algebra of a finite region `X` is the star subalgebra generated by the annihilators of
the modes at `X`; the quasi-local algebra is the norm closure of their union, a C*-subalgebra.
Inclusions are then literal inclusions of subalgebras, completeness is that of `E →L[ℂ] E`, and
the dynamics `e^{itH} A e^{-itH}` is computed in the ambient algebra. The abstract layer
(`GradedLocalNet`) only asks for a C*-algebra, monotone local star subalgebras, an involutive
parity automorphism preserving them, and even-odd locality; spin systems are the case of
trivial parity.

## References

- B. Nachtergaele, R. Sims, A. Young, Lieb-Robinson bounds, the spectral flow, and stability of the
  spectral gap for lattice fermion systems, arXiv:1705.08553.
- B. Nachtergaele, R. Sims, A. Young, Quasi-locality bounds for quantum lattice systems. Part I,
  arXiv:1810.02428.
- O. Bratteli, D. W. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, Sec. 6.2.
