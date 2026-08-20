/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Qubit.backup.Effect
public import Physlib.Mathematics.OperatorAlgebra.State

/-!

# The Bloch ball

For a state `ω`, its Bloch vector `r ω = (ω (gen 0), ω (gen 1), ω (gen 2))` is real (the
generators are observables) and satisfies `‖r ω‖ ≤ 1`; conversely every `r` with `‖r‖ ≤ 1`
comes from a unique state `ωᵣ(a₀ • 1 + σ v) = a₀ + r ⬝ᵥ v`. This gives the main theorem of the
abstract qubit theory: `State A ≃ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1`.

Pure states are exactly those on the boundary sphere (`State.IsPure ↔ ‖r ω‖ = 1`), so:

`all states  ↔ Bloch ball`
`pure states ↔ Bloch sphere`

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra
open Module OperatorAlgebra

namespace Qubit

variable {A : Type*} [OperatorAlgebra A] [QubitAlgebra A]

/-- The Bloch vector of a state: its expectation values on the three Pauli generators. -/
noncomputable def r (ω : State A) : Fin 3 → ℝ :=
  fun i => (ω (QubitAlgebra.gen (A := A) i : A)).re

/-- Every Bloch vector lies in the closed unit ball. -/
@[sorryful]
lemma norm_r_le_one (ω : State A) :
    ‖(WithLp.toLp 2 (r ω) : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 :=
  sorry

TODO "Prove `Qubit.norm_r_le_one`. For a unit vector `n`, positivity of `1 - σ n` and `1 + σ n`
  (from `Qubit.nonneg_scalar_add_σ_iff` with `a₀ = 1`, `‖n‖ = 1`) gives, via `State.apply_nonneg`,
  `-1 ≤ ⟪n, r ω⟫ ≤ 1` (i.e. `n ⬝ᵥ r ω`, expanding `ω (σ n)` linearly against `ω (gen i)`, real by
  `State.observable_im_eq_zero`). Take `n = r ω / ‖r ω‖` (when `r ω ≠ 0`) to get `‖r ω‖ ≤ 1`."

/-- The state with Bloch vector `v`, `‖v‖ ≤ 1`: `ωᵥ(a₀ • 1 + σ w) = a₀ + v ⬝ᵥ w`. -/
@[sorryful]
noncomputable def ofBlochVector (v : Fin 3 → ℝ)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ ≤ 1) : State A :=
  sorry

TODO "Construct `Qubit.ofBlochVector`. The underlying functional is `a₀ • 1 + σ w ↦ (a₀ + v ⬝ᵥ w
  : ℂ)`, well-defined and ℂ-linear via `QubitAlgebra.pauliBasis`'s coordinates (`Qubit.coeff`).
  Positivity: if `0 ≤ a₀ • 1 + σ w` then `‖w‖ ≤ a₀` (`Qubit.nonneg_scalar_add_σ_iff`), and
  Cauchy-Schwarz gives `|v ⬝ᵥ w| ≤ ‖v‖ * ‖w‖ ≤ ‖w‖ ≤ a₀` (using `hv : ‖v‖ ≤ 1`), so `a₀ + v ⬝ᵥ w
  ≥ a₀ - ‖w‖ ≥ 0`. Normalization: `a₀ = 1, w = 0` gives `1 + v ⬝ᵥ 0 = 1`."

/-- The Bloch vector of `Qubit.ofBlochVector v hv` is `v`. -/
@[sorryful]
lemma r_ofBlochVector (v : Fin 3 → ℝ)
    (hv : ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ ≤ 1) :
    (r (A := A) (ofBlochVector v hv)) = v :=
  sorry

TODO "Prove `Qubit.r_ofBlochVector` by evaluating `Qubit.ofBlochVector v hv` on each generator
  `gen i = 0 • 1 + σ (Pi.single i 1)` and matching against the defining formula `a₀ + v ⬝ᵥ w`."

/-- The main theorem: states of a qubit observable algebra correspond exactly to points of the
closed unit ball, via the Bloch vector. -/
@[sorryful]
noncomputable def stateEquivClosedBall :
    State A ≃ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  sorry

TODO "Construct `Qubit.stateEquivClosedBall` from `Qubit.r`/`Qubit.norm_r_le_one` (forward) and
  `Qubit.ofBlochVector` (backward), using `Qubit.r_ofBlochVector` for one round trip and
  uniqueness of the decomposition `a₀ • 1 + σ v` (`QubitAlgebra.pauliBasis`, `State.ext`-style
  reasoning: a state is determined by its values on `1` and the three generators) for the other."

/-!
## Pure states
-/

/-- A state is pure iff its Bloch vector has norm exactly `1`, i.e. lies on the Bloch sphere. -/
@[sorryful]
lemma isPure_iff_norm_r_eq_one (ω : State A) :
    ω.IsPure ↔ ‖(WithLp.toLp 2 (r ω) : EuclideanSpace ℝ (Fin 3))‖ = 1 :=
  sorry

TODO "Prove `Qubit.isPure_iff_norm_r_eq_one`. `‖r ω‖ < 1`: exhibit a genuine convex decomposition
  by moving `r ω` a little in two opposite directions and pulling back through
  `Qubit.ofBlochVector`, refuting purity. `‖r ω‖ = 1`: any convex decomposition `mix φ ψ t = ω`
  gives `r ω = t • r φ + (1 - t) • r ψ` with `r φ, r ψ` in the closed unit ball; a boundary point
  of a ball is only reached this way when `r φ = r ψ = r ω`, then `φ = ψ = ω` by
  `Qubit.stateEquivClosedBall`'s injectivity."

end Qubit
