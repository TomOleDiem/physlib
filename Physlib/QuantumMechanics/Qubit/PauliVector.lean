/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Qubit.Basic
public import Mathlib.LinearAlgebra.CrossProduct

/-!

# The Pauli vector

For `v : Fin 3 → ℝ`, the Pauli vector `σ(v) = ∑ᵢ vᵢ genᵢ` packages the three Pauli generators
into a single ℝ³-indexed family of observables. Its defining product identity

`σ(u) σ(v) = (u ⬝ᵥ v) • 1 + i • σ(u ⨯₃ v)`

is the main algebraic interface for the rest of the development; the square and commutator
identities are immediate corollaries.

## Note

Bloch vectors are represented here as plain `Fin 3 → ℝ`, using the dot product `⬝ᵥ` and cross
product `⨯₃` already available for that type, rather than `EuclideanSpace ℝ (Fin 3)`. This
avoids committing to a norm instance before it is needed; see `Qubit/todo.md`.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra Matrix
open OperatorAlgebra

namespace Qubit

variable {A : Type*} [OperatorAlgebra A] [QubitAlgebra A]

/-- The Pauli vector `σ(v) = ∑ᵢ vᵢ genᵢ` associated with `v : Fin 3 → ℝ`. -/
noncomputable def σ (v : Fin 3 → ℝ) : A :=
  ∑ i, (v i : ℂ) • (QubitAlgebra.gen (A := A) i : A)

/-- `σ(v)` is self-adjoint: a real-linear combination of the self-adjoint generators. -/
@[sorryful]
theorem isSelfAdjoint_σ (v : Fin 3 → ℝ) : IsSelfAdjoint (σ v : A) :=
  sorry

TODO "Prove `Qubit.isSelfAdjoint_σ`. Each summand `(v i : ℂ) • (gen i : A)` is self-adjoint:
  `v i` is a real scalar (fixed by complex conjugation) and `gen i` is self-adjoint by
  definition (`Observable A = selfAdjoint A`). A finite sum of self-adjoint elements is
  self-adjoint (`IsSelfAdjoint.add`/`Finset.sum`)."

/-- The fundamental Pauli vector identity: `σ(u) σ(v) = (u ⬝ᵥ v) • 1 + i • σ(u ⨯₃ v)`. -/
@[sorryful]
theorem σ_mul_σ (u v : Fin 3 → ℝ) :
    (σ u : A) * σ v = ((u ⬝ᵥ v : ℝ) : ℂ) • (1 : A) + Complex.I • (σ (u ⨯₃ v) : A) :=
  sorry

TODO "Prove `Qubit.σ_mul_σ` by expanding `σ u`, `σ v` bilinearly against `QubitAlgebra.gen_sq`,
  `QubitAlgebra.gen_mul_cyc`, and `Qubit.gen_mul_cyc_symm`, then matching coefficients against
  the definitions of `⬝ᵥ` and `⨯₃`."

/-- `σ(v)² = ‖v‖² • 1`, i.e. `σ(v) * σ(v) = (v ⬝ᵥ v) • 1`. -/
@[sorryful]
theorem σ_sq (v : Fin 3 → ℝ) :
    (σ v : A) * σ v = ((v ⬝ᵥ v : ℝ) : ℂ) • (1 : A) :=
  sorry

TODO "Prove `Qubit.σ_sq` as the `u = v` specialization of `Qubit.σ_mul_σ`, using
  `Matrix.cross_self` to kill the cross-product term."

/-- The Pauli commutator: `[σ(u), σ(v)] = 2i • σ(u ⨯₃ v)`. -/
@[sorryful]
theorem σ_commutator (u v : Fin 3 → ℝ) :
    (σ u : A) * σ v - σ v * σ u = (2 * Complex.I) • (σ (u ⨯₃ v) : A) :=
  sorry

TODO "Prove `Qubit.σ_commutator` from `Qubit.σ_mul_σ` applied to `(u, v)` and `(v, u)`,
  using `Matrix.cross_anticomm` to combine the two `(u ⬝ᵥ v) • 1` terms cancelling and the
  cross-product terms adding."

end Qubit
