/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Qubit.backup.Observable
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!

# Spectrum and positivity of qubit observables

`σ(v)² = ‖v‖² • 1` (`Qubit.σ_sq`) already pins down the spectrum of any observable of the form
`a₀ • 1 + σ v`: it is `{a₀ + ‖v‖, a₀ - ‖v‖}`. From there, positivity of `a₀ • 1 + σ v` is exactly
`‖v‖ ≤ a₀` — the Bloch-ball picture starts here. This should use the existing C⋆-algebra
functional-calculus/order API (`Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order`)
rather than redeveloping spectral theory for the qubit specifically.

## Note

Norms of Pauli vectors are computed by viewing `v : Fin 3 → ℝ` through
`WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3)`, which is where a genuine (Euclidean) norm lives;
`Fin 3 → ℝ` itself is only ever used algebraically, through `⬝ᵥ` and `⨯₃`. This is the same
convention already used in Mathlib's own `InnerProductGeometry.norm_toLp_symm_crossProduct`.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra
open Module OperatorAlgebra

namespace Qubit

variable {A : Type*} [OperatorAlgebra A] [QubitAlgebra A]

/-- The spectrum of `a₀ • 1 + σ v` is `{a₀ + ‖v‖, a₀ - ‖v‖}`. -/
@[sorryful]
lemma spectrum_scalar_add_σ (a₀ : ℝ) (v : Fin 3 → ℝ) :
    spectrum ℝ (a₀ • (1 : A) + σ v) =
      {a₀ + ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖,
        a₀ - ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖} :=
  sorry

TODO "Prove `Qubit.spectrum_scalar_add_σ`. From `Qubit.σ_sq`, `(σ v - ‖v‖ • 1) * (σ v + ‖v‖ • 1)
  = σ v * σ v - ‖v‖^2 • 1 = 0` (using `Complex.normSq`/`⬝ᵥ` self dot product equals `‖v‖^2` via
  `EuclideanSpace.norm_eq`/`PiLp.inner_apply`), so `σ v` has spectrum `⊆ {‖v‖, -‖v‖}`; equality on
  both sides then needs a nondegeneracy argument (e.g. via `QubitAlgebra.pauliBasis`, `σ v ≠ ±‖v‖ •
  1` unless `v = 0`). Shift by `a₀ • 1` using `spectrum.add_eq`-style translation lemmas."

/-- Positivity criterion: `a₀ • 1 + σ v` is a positive element iff `‖v‖ ≤ a₀`. -/
@[sorryful]
lemma nonneg_scalar_add_σ_iff (a₀ : ℝ) (v : Fin 3 → ℝ) :
    0 ≤ a₀ • (1 : A) + σ v ↔ ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ ≤ a₀ :=
  sorry

TODO "Prove `Qubit.nonneg_scalar_add_σ_iff` from `Qubit.spectrum_scalar_add_σ` together with a
  self-adjoint-element positivity-via-spectrum lemma such as
  `nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts`
  (`Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances`) or the unital
  `spectrum ⊆ ℝ≥0` characterization nearby in `...ContinuousFunctionalCalculus.Order`: `a₀ • 1 +
  σ v` is self-adjoint (sum of self-adjoint elements, `Qubit.σ` is self-adjoint since `v` is
  real), and its spectrum `{a₀ ± ‖v‖} ⊆ [0, ∞) ↔ a₀ - ‖v‖ ≥ 0 ↔ ‖v‖ ≤ a₀`."

end Qubit
