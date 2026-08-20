/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Qubit.Spectrum
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.Projection

/-!

# Effects and projections among qubit observables

Effects (`0 ≤ E ≤ 1`) and projections are characterized in Pauli coordinates directly from
`Qubit.nonneg_scalar_add_σ_iff` and `Qubit.spectrum_scalar_add_σ`.

* An observable `a₀ • 1 + σ v` is an effect iff `‖v‖ ≤ min a₀ (1 - a₀)`: it and `1 - a₀ • 1 -
  σ v` must both be nonnegative.
* It is a projection (`IsStarProjection`, i.e. self-adjoint and idempotent) iff its spectrum
  `{a₀ + ‖v‖, a₀ - ‖v‖}` sits inside `{0, 1}`. The trivial solutions are `v = 0`, `a₀ ∈ {0, 1}`
  (the zero and identity projections); the nontrivial ones force `a₀ = ‖v‖ = 1/2` — the rank-one
  projections, one for every direction on the Bloch sphere of radius `1/2`. This is the first
  place a *sphere*, rather than the whole ball, appears.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra
open Module OperatorAlgebra

namespace Qubit

variable {A : Type*} [OperatorAlgebra A] [QubitAlgebra A]

/-- `a₀ • 1 + σ v` is an effect (`0 ≤ · ≤ 1`) iff `‖v‖ ≤ min a₀ (1 - a₀)`. -/
@[sorryful]
lemma nonneg_and_le_one_scalar_add_σ_iff (a₀ : ℝ) (v : Fin 3 → ℝ) :
    (0 ≤ a₀ • (1 : A) + σ v ∧ a₀ • (1 : A) + σ v ≤ 1) ↔
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ ≤ min a₀ (1 - a₀) :=
  sorry

TODO "Prove `Qubit.nonneg_and_le_one_scalar_add_σ_iff` from `Qubit.nonneg_scalar_add_σ_iff`
  applied twice: once directly (`0 ≤ a₀ • 1 + σ v ↔ ‖v‖ ≤ a₀`), once to `1 - (a₀ • 1 + σ v) =
  (1 - a₀) • 1 + σ (-v)` (`‖-v‖ = ‖v‖`, giving `0 ≤ 1 - (a₀ • 1 + σ v) ↔ ‖v‖ ≤ 1 - a₀`).
  Combine with `le_min_iff`."

/-- `a₀ • 1 + σ v` is a projection iff its spectrum `{a₀ + ‖v‖, a₀ - ‖v‖}` lies in `{0, 1}`. -/
@[sorryful]
lemma isStarProjection_scalar_add_σ_iff (a₀ : ℝ) (v : Fin 3 → ℝ) :
    IsStarProjection (a₀ • (1 : A) + σ v) ↔
      {a₀ + ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖,
        a₀ - ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖} ⊆ ({0, 1} : Set ℝ) :=
  sorry

TODO "Prove `Qubit.isStarProjection_scalar_add_σ_iff` via
  `isStarProjection_iff_spectrum_subset_and_isSelfAdjoint`
  (`Mathlib.Analysis.CStarAlgebra.Projection`) together with `Qubit.spectrum_scalar_add_σ`;
  self-adjointness of `a₀ • 1 + σ v` is automatic (real combination of self-adjoint elements),
  so only the spectrum-inclusion side carries content."

/-- The nontrivial (rank-one) projections among `a₀ • 1 + σ v` are exactly those with `a₀ =
‖v‖ = 1/2` — one for every direction on the Bloch sphere of radius `1/2`. -/
@[sorryful]
lemma isStarProjection_scalar_add_σ_iff_of_ne_zero {v : Fin 3 → ℝ} (hv : v ≠ 0) (a₀ : ℝ) :
    IsStarProjection (a₀ • (1 : A) + σ v) ↔
      a₀ = 1 / 2 ∧ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ = 1 / 2 :=
  sorry

TODO "Prove `Qubit.isStarProjection_scalar_add_σ_iff_of_ne_zero` as the `v ≠ 0` case of
  `Qubit.isStarProjection_scalar_add_σ_iff`: with `‖v‖ > 0`, the two spectral values `a₀ ±
  ‖v‖` are distinct, so `{a₀ + ‖v‖, a₀ - ‖v‖} ⊆ {0, 1}` forces the pairing `a₀ + ‖v‖ = 1` and
  `a₀ - ‖v‖ = 0` (the other pairing contradicts `‖v‖ > 0`), i.e. `a₀ = ‖v‖ = 1/2`."

end Qubit
