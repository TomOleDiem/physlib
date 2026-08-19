/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Qubit.PauliVector
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.LinearAlgebra.CrossProduct

/-!

# The traceless sector as `su(2)`

The Pauli commutator `⁅σ u, σ v⁆ = 2i • σ (u ⨯₃ v)` (`Qubit.σ_commutator`) exhibits the traceless
observable sector, after the conventional normalization `τ v = -i/2 • σ v`, as the Lie algebra
`su(2)`: `τ` sends `u ⨯₃ v` to `⁅τ u, τ v⁆` on the nose, no leftover scalar factor, and every
`τ v` is skew-adjoint.

The conceptual identification is

`ℝ³ with cross product ≃ su(2) ≃ skew-adjoint traceless qubit generators`.

`Fin 3 → ℝ` already carries this Lie ring structure as `Cross.lieRing`
(`Mathlib.LinearAlgebra.CrossProduct`); `A` carries its commutator bracket generically via
`LieRing.ofAssociativeRing`. `τ` is the bridge between them.

This is a *different* notion of representation from the C⋆-algebra representation `A → B(ℋ)`
of `Qubit/Basic.lean`'s ambient algebra: keep the two separate (see `Qubit/todo.md`, §11).

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra Matrix
open Module OperatorAlgebra

namespace Qubit

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [QubitAlgebra A]

/-- The `su(2)`-normalized generator associated with a Pauli vector `v`: `τ v = -i/2 • σ v`. -/
noncomputable def τ (v : Fin 3 → ℝ) : A :=
  (-Complex.I / 2) • σ v

/-- Every `τ v` is skew-adjoint. -/
@[sorryful]
theorem τ_mem_skewAdjoint (v : Fin 3 → ℝ) : (τ v : A) ∈ skewAdjoint A :=
  sorry

TODO "Prove `Qubit.τ_mem_skewAdjoint` from `Qubit.isSelfAdjoint_σ v` and
  `IsSelfAdjoint.smul_mem_skewAdjoint` (`Mathlib.Algebra.Star.SelfAdjoint`), using that `-i/2 ∈
  skewAdjoint ℂ` (`star (-i/2) = -(-i/2)`)."

/-- `τ` exactly intertwines the cross product with the commutator bracket: this is the
identification `ℝ³ with cross product ≃ su(2) ≃ skew-adjoint traceless qubit generators`. -/
@[sorryful]
theorem τ_mul_sub_mul (u v : Fin 3 → ℝ) :
    (τ u : A) * τ v - τ v * τ u = τ (u ⨯₃ v) :=
  sorry

TODO "Prove `Qubit.τ_mul_sub_mul` by expanding `τ u * τ v - τ v * τ u = (-i/2)² • (σ u * σ v -
  σ v * σ u)` and applying `Qubit.σ_commutator`: `(-i/2)² * 2i = -i/2`, matching `τ (u ⨯₃ v) =
  (-i/2) • σ (u ⨯₃ v)` exactly, with no leftover scalar. Once proved, this says `τ` is a genuine
  `LieRing` homomorphism from `Cross.lieRing` on `Fin 3 → ℝ` to `A`'s commutator bracket
  (`LieRing.ofAssociativeRing`, a local instance in Mathlib — see whether it's worth packaging
  `τ` as an explicit `LieHom` once both are in scope, for §11's Lie-representation reuse)."

end Qubit
