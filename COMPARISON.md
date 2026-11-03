# Comparison of the three infinite-lattice experiments

Report of 2026-11-03. All Lean files are under `PhyslibAlpha/QuantumMechanics/InfiniteBosons/`. Each statement below is proved without `sorry`. Tom judges the quality.

## 1. Overview

Three models were built before any shared API was fixed. E1 is the oscillator lattice. E2 is the Bose-Hubbard lattice with pairing. E3 is the atom-photon lattice with Jaynes-Cummings coupling. All three live on an arbitrary lattice. No finite volume and no particle-number sector enters a definition.

## 2. What each experiment contains

| Layer | E1 oscillators | E2 Bose-Hubbard | E3 atom-photon |
|---|---|---|---|
| Polynomial algebra | not used | `Adjointable (Occ L)`, `BoseHubbard.lean` | `Adjointable (Occ L × Finset L)`, `SpinBoson.lean` |
| Locality and derivation | Weyl locality, `OscillatorLattice.lean` | `LocalInteraction`, Leibniz and star rules | same, `AtomPhotonLattice.lean` |
| Growth bounds and graph norm | not used | `BoseHubbardBounds.lean`, `ReferenceOperator.lean`, `GraphNorm.lean` | `AtomPhotonBounds.lean` |
| Local net | Weyl C*-net, `WeylCStar.lean`; `tensorNet` with `onSiteFlow` | `tensorNet` with local type `ℕ` | `atomPhotonNet` with local type `ℕ × Bool` |
| Dynamics | symplectic rotation group; `onSiteFlow` for any real on-site energy | local Heisenberg derivation | free `onSiteFlow`; local derivation |
| Representation | `fockRep` | `fockRep` | `sbFockRep` (`AtomPhotonFock.lean`) |
| Bridge to bounded | `fockRep_harmonicFlow` | `numberOp_resolvent_local`, `hop_resolvent`, `siteTerm_resolvent`, `refOp_resolvent` | `jaynesCummings_resolvent` |

## 3. Abstractions that removed duplicated mathematics

1. `Adjointable B`, `pair` and `qform` for any basis type. E2 and E3 used to prove adjointness and quadratic-form bounds separately.
2. `LocalGenerators` and `LocalInteraction` with the Heisenberg derivation. E2 and E3 share the Leibniz and star proofs. The earlier `Derivation.lean` of E2 was deleted.
3. `tensorNet`, `inclE`, `inclE_comp` and `phaseAut`. E1 harmonic dynamics and E3 free dynamics are instances of `onSiteFlow`.
4. `shiftMap` and `exists_resolvent` with the finite-block criterion. Hopping and Jaynes-Cummings use the same density lemma.

## 4. What stayed model-specific

- The Weyl C*-net needs a symplectic space. It appears only in E1.
- The spin-boson algebra with atoms as a finite set is needed only in E3.
- The invariant blocks differ: `hopBlock` is a sum over a line of occupations and `jcBlock` has two elements.

## 5. Open points

- The pairing term has no finite blocks. Its essential self-adjointness is proved by Carleman's criterion along occupation lines (`PairingSelfAdjoint.lean`). The full Hamiltonian as a sum is open.
- The Weyl net and the polynomial algebra are linked at the commutator level (`fieldOp_commutator_oscSymp`, `FieldOperator.lean`). The comparison with the local `B(H)` net needs `W(f) = exp(iφ(f))` as an element of `A({x})`.
- The Fock-type representation of the atom-photon net exists (`AtomPhotonFock.lean`). Diagonal and Jaynes-Cummings observables are not yet shown in it.
- The tensor product with a finite matrix algebra is built (`MatrixTensor.lean`) with the product map `kronTensor`. It does not reproduce the `SBBasis` algebra of E3 in general because the atoms there form a finite set over many sites.
- Resolvents of region-local operators lie in `fockRep X` only for `N_x` (`numberOp_resolvent_local`). Hopping and Jaynes-Cummings are open.
- Norm continuity of the dynamics is not asserted. It is a separate statement from the algebraic automorphism property.

## 5a. Link to Physlib spectral theory

`FieldNelson.lean` proves essential self-adjointness of every multi-mode field operator `φ(f)` by Nelson's theorem and builds the Weyl operators `exp(i t φ(f))` from the unbounded spectral theorem of the Alpha tree. `QuadratureSelfAdjoint.lean` proves essential self-adjointness of the quadrature `a_x + a_x†` through Carleman's criterion (`JacobiCarleman.lean`). `EssentialSelfAdjoint.lean` shows `IsEssentiallySelfAdjoint` in the sense of `Physlib.QuantumMechanics.Operators.SpectralTheory` for `N_x`, hopping, the Jaynes-Cummings coupling and `K_X`. The spectral theorem and Stone's theorem are open in Physlib.

## 5b. The two spaces

The Hamiltonian of an infinite lattice is not an element of the polynomial algebra. It lives in two
spaces. The first is the space of formal vectors `Formal β = β → ℂ`. The Hamiltonian `Σ_i Φ_i` of a
row finite family of local terms is a linear map from the finite vectors into it
(`FormalHamiltonian.lean`). The second is the Hilbert space `ℓ²(β)`. The Hamiltonian acts there as
the operator `hamPMap` on the domain of finite vectors with square summable formal image, and it is
symmetric. The three systems use the same API:

| | E1 oscillators | E2 Bose-Hubbard | E3 atom-photon |
|---|---|---|---|
| Formal Hamiltonian | `BoseHubbardData.formalHam` | `BoseHubbardData.formalHam` | `AtomPhotonData.formalHam` |
| Operator on `ℓ²` | `BoseHubbardData.hamOp` | `BoseHubbardData.hamOp` | `AtomPhotonData.hamOp` |
| Symmetric | `hamOp_isSymmetric` | `hamOp_isSymmetric` | `hamOp_isSymmetric` |
| Dense domain | explicit hypothesis | explicit hypothesis | `hamOp_dense` |
| Dynamics, decoupled | `dynamics_decoupled` | `dynamics_decoupled` | `dynamics_decoupled` |
| Dynamics, coupled | `dynamics_of_essentiallySelfAdjoint` | same | same |

## 6. Reading of the result

The bridge hypothesis is proved for every term of the benchmark Hamiltonian taken singly. Number-conserving terms use finite invariant blocks. Diagonal terms use real eigenvalues. The field operators use Nelson's theorem. The pairing term uses Carleman's criterion along occupation lines. The sum of the terms is not covered. The Weyl relation and the local landing of the resolvents remain open.
