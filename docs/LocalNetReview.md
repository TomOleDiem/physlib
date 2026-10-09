# Local net contribution ready for human review

The contribution describes local observables, compatible states, translations, and the algebraic
local-to-global construction. Classical Gibbs states, periodic lattice waves, and local analytic
thermal correlations instantiate the general constructions.

## Proposed PR sequence

| Branch | Concept | Review starting point |
|---|---|---|
| `local-net-alpha-01` | Local nets and restriction of states | `LocalNet/Net.lean` |
| `local-net-alpha-02` | Net symmetries and compatible local states | `LocalNet/State.lean` |
| `local-net-alpha-03` | Global realization of compatible local observables and states | `LocalNet/GlobalRealization.lean` |
| `local-net-alpha-04` | Classical product states and Ising thermodynamic limits | `IsingModel/ClassicalExamples.lean` |
| `local-net-alpha-05` | Bloch reduction and two-component periodic wave dispersion | `SpinLattice/PeriodicWaves.lean` |
| `local-net-alpha-06` | Local analytic thermal identities for arbitrary Ising limit states | `SpinLattice/ThermalLimit.lean` |

Each branch depends on the previous branch. The cumulative implementation contains inherited work
from the previous agent plus the narrowing, refactors, examples, and general thermal-limit theorem
added in this session. The stack should be reviewed in order. The declaration inventory is in
[LocalNetAPI.md](LocalNetAPI.md); no existing tracked Lean declarations are removed.

## Concrete results

- Independent Gibbs probabilities factor, finite-volume marginals agree, and the thermodynamic
  limit is the explicit product net state. Identical product states are invariant under site actions.
- The uniform Ising chain has nearest-neighbor couplings invariant under translation. Its Gibbs
  limit is a compatible state of the classical net and hence of the algebraic global system.
- Grouping sites into cells is a general unit-cell construction. A two-component sector of actual
  local spin observables instantiates it. A homogeneous lattice wave operator has the two explicit
  Bloch branches `mass b + stiffness * (2 - 2 cos k)`.
- Exact local analytic evolution passes finite-volume thermal boundary identities to every
  thermodynamic limit state of an exhausting family. Ising evolution instantiates the assumptions;
  the quantum longitudinal chain is a concrete application.

## Limits of the statements

The global system is algebraic, without norm completion. Thermodynamic limits are along a chosen
exhausting ultrafilter; the interacting chain has no uniqueness or full-sequence convergence theorem
here. Translation invariance of its couplings is proved, but invariance of its chosen limit state is
not asserted. The wave eigenvalues are squared frequencies for second-order wave dynamics; a
physical time evolution of the full net is not constructed. The KMS application proves local
analytic boundary identities, without strip boundedness or a completed-algebra KMS theorem.
Classical DLR consistency and general noncommuting-interaction dynamics are subsequent work.

The deferred composition, propagation, time-evolution-channel, spacetime, and Minkowski files remain
in the original working directory and are excluded from the proposed committed stack.

## Validation

`lake exe cache get`, `lake build`, and `lake build PhyslibAlpha` completed successfully. The auxiliary
script tests, ForMathlib checks, documentation check, and Alpha import checks passed. The central
new results were checked with `#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound`
appear, with no `sorryAx` or reduction shortcut.

The full `lake exe lint_all` run passed its build, imports, TODO, sorry, and Physlib/QuantumInfo
Lean checks. Its redundant-import phase reported existing issues in untouched `Physlib` files,
including FreeParticle, FLRW, calculus, distribution, Gaussian, QFT, Hilbert-space, parity, and time
modules. Those files have no changes in this contribution. The executable returns zero even when
that phase reports issues, so its exit status alone is not a clean-lint certificate.

The final Alpha declaration linters and both committed-file Python style scripts passed.
The proposed PR snapshots preserve the original bibliography order and add only referenced entries.

## Before opening a PR

AI-POLICY.md requires the human author to vouch for the statements and proofs (§1.7), verify the
bibliographic references personally (§2.1), and confirm compliance before opening the PR (§2.2).
These checks cannot be replaced by a successful build or delegated reference verification.
No PR has been opened and no branch has been pushed.
