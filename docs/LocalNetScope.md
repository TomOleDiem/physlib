# Local nets for periodic systems

The current scope is a net description of extended lattice systems, its application to periodic
systems, and thermodynamic limits of finite-volume states. The framework should be motivated by
local measurements, their marginals, and translation symmetry. Mathematical constructions belong
where they establish these connections.

The intended narrative is:

1. Each finite region has observables. Enlarging the region preserves their interpretation.
2. A state assigns local expectations that agree under restriction.
3. Translations move regions and observables. Periodicity of the system and invariance of a state
   are separate properties.
4. Compatible local observables form an algebraic global system; compatible states are exactly
   states of that system.
5. Finite-volume states can have compatible limit points even when they are not themselves
   compatible under restriction.

## Core and reading order

- `LocalNet/Net.lean`: inclusions of observables and restriction of states.
- `LocalNet/Symmetry.lean` and `LocalNet/Lattice.lean`: translations of finite regions and their
  observables; neighborhoods are geometry, independent of time evolution.
- `LocalNet/State.lean`: compatible expectations and translation-invariant states.
- `LocalNet/GlobalRealization.lean` and `LocalNet/GlobalSymmetry.lean`: the global system and the
  local-to-global correspondence, including translations.
- `LocalNet/Thermodynamic.lean`: limit points of finite-volume expectations and inheritance of
  translation invariance when asymptotic invariance has been established.

Maps, transport, and representations support these constructions. They should supply the API
needed by this narrative rather than introduce independent research directions.

## Examples to develop

**Classical Ising.** Use `SpinLattice/ClassicalSpins.lean`, `IsingModel/Basic.lean`, and the classical
part of `IsingModel/GibbsStates.lean`. Start with a uniform nearest-neighbor chain: identify the
local observables, finite-volume energy, Gibbs expectations, and the compatible infinite-volume
limit point. Add explicit translation invariance of the interaction. Invariance of the limiting
state needs its own proof; it is not a consequence of periodic couplings alone. The classical Gibbs construction is isolated in `ClassicalGibbs.lean`;
`ClassicalExamples.lean` defines independent spins and the uniform chain. Independent Gibbs states
are proved to be the general product state, including in the thermodynamic limit.

**Periodic linear systems and bands.** Use the translation action and the unit-cell reduction in
`LocalNet/Bloch.lean` and `Crystal/BlochTheorem.lean`. The linear spin-observable sector in
`SpinLattice/SpinWaves.lean` supplies an existing bridge to an actual net. `SpinLattice/PeriodicWaves.lean` now groups sites into two-component cells and proves the Bloch
relation and the two real dispersion branches for a lattice wave operator. A band-theory example must specify
its amplitude space, Hamiltonian, and relation to the observable net. A general linear Bloch map
alone is not a band Hamiltonian. No direct tight-binding connection is part of this scope.

**Thermodynamic limits.** Make the classical Ising example demonstrate the general theorem:
local finite-volume expectations converge along an exhausting ultrafilter, their limits agree
under restriction, and the resulting net state is a state on the algebraic global system.
Distinguish existence of limit points from convergence of an entire sequence and from uniqueness.

## Deferred work

Spacetime nets, Minkowski diamonds, additivity, time-slice properties, quantum Ising time-evolution channels,
general noncommuting KMS theory, general causal propagation, and a full spectral decomposition are outside the
current development scope. Existing files are retained. Their presence in `PhyslibAlpha.lean`
does not make them requirements for these examples.

Norm completion and analytic propagation estimates are also deferred. The current global system
contains observables supported in individual regions; it is not a completed quasi-local algebra.

## Local thermal correlations

The approved thermal application is `SpinLattice/ThermalLimit.lean`: exact complex-time local
stabilization passes finite-volume thermal boundary identities to any thermodynamic limit state.
The Ising analytic evolution instantiates this theorem, and the uniform quantum longitudinal chain
is a concrete application. This proves the local analytic boundary condition. Strip boundedness,
completion, and the standard completed-algebra KMS condition remain deferred.
