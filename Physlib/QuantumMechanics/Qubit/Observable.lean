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

/-- `pauliBasis 0 = 1`, i.e. `coeff a 0` really is the scalar (`1`-)coefficient — the fact
`Qubit.trace`, below, is built on. -/
theorem pauliBasis_zero : (QubitAlgebra.pauliBasis (A := A) : Fin 4 → A) 0 = 1 := by
  rw [QubitAlgebra.pauliBasis_eq, Fin.cons_zero]

/-- The coefficient of `1` in an algebra element's Pauli decomposition. -/
theorem coeff_one_zero : coeff (1 : A) 0 = 1 := by
  rw [coeff, ← pauliBasis_zero, Basis.repr_self, Finsupp.single_eq_same]

/-- The trace of an algebra element: twice its scalar (`1`-)coefficient, matching the physical
normalization `trace (1 : A) = 2`, `trace (gen i : A) = 0` — the trace of a `2 × 2` identity and
of a traceless Pauli matrix. Purely algebraic, no matrices: `coeff` already comes from
`QubitAlgebra.pauliBasis` being a basis. -/
noncomputable def trace (a : A) : ℂ :=
  2 * coeff a 0

@[simp]
theorem trace_one : trace (1 : A) = 2 := by
  rw [trace, coeff_one_zero, mul_one]

theorem trace_smul (c : ℂ) (a : A) : trace (c • a) = c * trace a := by
  rw [trace, trace, coeff, coeff, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_left_comm]

/-- The determinant of an algebra element, via the `2 × 2` Cayley–Hamilton formula `det a =
(trace a ^ 2 - trace (a * a)) / 2` — purely a formula in the trace, so needs no separate proof of
existence and no matrices. (That this is genuinely multiplicative, or agrees with the usual
determinant once `Qubit/Matrix.lean` identifies `A` with `Matrix (Fin 2) (Fin 2) ℂ`, is not
needed below and not yet checked.) -/
noncomputable def det (a : A) : ℂ :=
  (trace a ^ 2 - trace (a * a)) / 2

/-- The determinant of a scalar element: `det (c • 1) = c ^ 2`, matching `det (c • I) = c ^ 2`
for `2 × 2` matrices. -/
theorem det_smul_one (c : ℂ) : det (c • (1 : A)) = c ^ 2 := by
  have h1 : (c • (1 : A)) * (c • (1 : A)) = c ^ 2 • (1 : A) := by
    rw [smul_mul_smul_comm, mul_one, sq]
  rw [det, trace_smul, trace_one, h1, trace_smul, trace_one]
  ring

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
