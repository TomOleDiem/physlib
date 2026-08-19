/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Qubit.PauliVector

/-!

# Pauli decomposition of qubit observables

Every element of a qubit observable algebra decomposes uniquely as `c₀ 1 + c₁ gen 0 + c₂ gen 1
+ c₃ gen 2` with complex coefficients — this is immediate from `QubitAlgebra.pauliBasis` being a
basis, not a separate theorem. What is not immediate: an element is self-adjoint exactly when
all four coefficients are real, and consequently every *observable* (not just every algebra
element) coordinatizes as a real scalar part plus a Pauli vector, giving a real-linear
equivalence `Observable A ≃ₗ[ℝ] ℝ × (Fin 3 → ℝ)`, `(a₀, v) ↦ a₀ • 1 + σ v`.

This equivalence is the primary coordinate system for qubit observables: the traceless/non-scalar
sector is naturally `Fin 3 → ℝ`, and downstream sections (states, positivity, dynamics) are
built on top of it rather than on the four raw complex coefficients.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra
open Module OperatorAlgebra

namespace Qubit

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [QubitAlgebra A]

/-- The Pauli coefficients of an algebra element: `coeff a 0` is the scalar part, `coeff a
(i.succ)` is the coefficient of `gen i`. Unique since `pauliBasis` is a basis. -/
noncomputable def coeff (a : A) : Fin 4 → ℂ :=
  QubitAlgebra.pauliBasis.repr a

/-- An algebra element is self-adjoint iff all four of its Pauli coefficients are real. -/
@[sorryful]
theorem isSelfAdjoint_iff_coeff (a : A) :
    IsSelfAdjoint a ↔ ∀ i, (coeff (A := A) a i).im = 0 :=
  sorry

TODO "Prove `Qubit.isSelfAdjoint_iff_coeff`. Forward: apply `star` to the basis expansion of `a`
  and use that `1, gen 0, gen 1, gen 2` are each self-adjoint together with uniqueness of the
  `pauliBasis` decomposition to force `conj (coeff a i) = coeff a i`. Backward: a real linear
  combination of self-adjoint elements is self-adjoint."

/-- The real-linear equivalence between observables and `ℝ × (Fin 3 → ℝ)`: the scalar part `a₀`
and Pauli vector `v` of `a₀ • 1 + σ v`. -/
@[sorryful]
noncomputable def observableEquiv : Observable A ≃ₗ[ℝ] ℝ × (Fin 3 → ℝ) :=
  sorry

TODO "Construct `Qubit.observableEquiv`. Forward map: from `Qubit.isSelfAdjoint_iff_coeff`, an
  observable's `coeff` at `0` and at `i.succ` (for `i : Fin 3`) are real; take those real parts
  as `(a₀, v)`. Inverse map: `(a₀, v) ↦ ⟨a₀ • 1 + σ v, _⟩`, self-adjoint since `1` and each
  `gen i` are self-adjoint and self-adjoint elements are closed under real-linear combinations.
  Left/right inverse and ℝ-linearity both reduce to uniqueness of the `pauliBasis` decomposition."

end Qubit
