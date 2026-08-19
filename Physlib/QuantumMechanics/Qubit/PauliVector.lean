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

omit [QubitAlgebra A] in
/-- A real scalar acts on `A` the same way whether taken through `ℝ` directly or through `ℂ`. -/
theorem real_smul_eq_ofReal_smul (x : ℝ) (b : A) : x • b = (x : ℂ) • b := by
  have : (x : ℂ) = algebraMap ℝ ℂ x := by norm_cast
  rw [this, IsScalarTower.algebraMap_smul]

/-- `σ` is additive. -/
theorem σ_add (u v : Fin 3 → ℝ) : (σ (u + v) : A) = σ u + σ v := by
  simp only [σ, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

/-- `σ` is ℝ-homogeneous. -/
theorem σ_smul (r : ℝ) (v : Fin 3 → ℝ) : (σ (r • v) : A) = r • σ v := by
  simp only [σ, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_smul, real_smul_eq_ofReal_smul,
    Finset.smul_sum]

/-- `σ(v)` is self-adjoint: a real-linear combination of the self-adjoint generators. -/
theorem isSelfAdjoint_σ (v : Fin 3 → ℝ) : IsSelfAdjoint (σ v : A) := by
  rw [σ]
  refine isSelfAdjoint_sum _ fun i _ => ?_
  rw [IsSelfAdjoint, star_smul]
  simp [(QubitAlgebra.gen (A := A) i).2.star_eq]

/-- The fundamental Pauli vector identity: `σ(u) σ(v) = (u ⬝ᵥ v) • 1 + i • σ(u ⨯₃ v)`. -/
theorem σ_mul_σ (u v : Fin 3 → ℝ) :
    (σ u : A) * σ v = ((u ⬝ᵥ v : ℝ) : ℂ) • (1 : A) + Complex.I • (σ (u ⨯₃ v) : A) := by
  have hu : (σ u : A) = (u 0 : ℂ) • (QubitAlgebra.gen (A := A) 0 : A)
      + (u 1 : ℂ) • (QubitAlgebra.gen (A := A) 1 : A)
      + (u 2 : ℂ) • (QubitAlgebra.gen (A := A) 2 : A) := by
    rw [σ, Fin.sum_univ_three]
  have hv : (σ v : A) = (v 0 : ℂ) • (QubitAlgebra.gen (A := A) 0 : A)
      + (v 1 : ℂ) • (QubitAlgebra.gen (A := A) 1 : A)
      + (v 2 : ℂ) • (QubitAlgebra.gen (A := A) 2 : A) := by
    rw [σ, Fin.sum_univ_three]
  have h00 := QubitAlgebra.gen_sq (A := A) 0
  have h11 := QubitAlgebra.gen_sq (A := A) 1
  have h22 := QubitAlgebra.gen_sq (A := A) 2
  have h01 : (QubitAlgebra.gen (A := A) 0 : A) * QubitAlgebra.gen (A := A) 1 =
      Complex.I • (QubitAlgebra.gen (A := A) 2 : A) := QubitAlgebra.gen_mul_cyc (A := A) 0
  have h12 : (QubitAlgebra.gen (A := A) 1 : A) * QubitAlgebra.gen (A := A) 2 =
      Complex.I • (QubitAlgebra.gen (A := A) 0 : A) := QubitAlgebra.gen_mul_cyc (A := A) 1
  have h20 : (QubitAlgebra.gen (A := A) 2 : A) * QubitAlgebra.gen (A := A) 0 =
      Complex.I • (QubitAlgebra.gen (A := A) 1 : A) := QubitAlgebra.gen_mul_cyc (A := A) 2
  have h10 : (QubitAlgebra.gen (A := A) 1 : A) * QubitAlgebra.gen (A := A) 0 =
      -Complex.I • (QubitAlgebra.gen (A := A) 2 : A) := gen_mul_cyc_symm (A := A) 0
  have h21 : (QubitAlgebra.gen (A := A) 2 : A) * QubitAlgebra.gen (A := A) 1 =
      -Complex.I • (QubitAlgebra.gen (A := A) 0 : A) := gen_mul_cyc_symm (A := A) 1
  have h02 : (QubitAlgebra.gen (A := A) 0 : A) * QubitAlgebra.gen (A := A) 2 =
      -Complex.I • (QubitAlgebra.gen (A := A) 1 : A) := gen_mul_cyc_symm (A := A) 2
  have hrhs1 : ((u ⬝ᵥ v : ℝ) : ℂ) = (u 0 : ℂ) * v 0 + (u 1 : ℂ) * v 1 + (u 2 : ℂ) * v 2 := by
    rw [dotProduct, Fin.sum_univ_three]; push_cast; ring
  have hrhs2 : (σ (u ⨯₃ v) : A) = ((u ⨯₃ v) 0 : ℂ) • (QubitAlgebra.gen (A := A) 0 : A)
      + ((u ⨯₃ v) 1 : ℂ) • (QubitAlgebra.gen (A := A) 1 : A)
      + ((u ⨯₃ v) 2 : ℂ) • (QubitAlgebra.gen (A := A) 2 : A) := by
    rw [σ, Fin.sum_univ_three]
  rw [hu, hv, hrhs1, hrhs2, cross_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  push_cast
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, h00, h11, h22, h01, h12,
    h20, h10, h21, h02]
  module

/-- `σ(v)² = ‖v‖² • 1`, i.e. `σ(v) * σ(v) = (v ⬝ᵥ v) • 1`. -/
theorem σ_sq (v : Fin 3 → ℝ) :
    (σ v : A) * σ v = ((v ⬝ᵥ v : ℝ) : ℂ) • (1 : A) := by
  rw [σ_mul_σ, cross_self]
  simp [σ]

/-- `σ` is odd: `σ(-w) = -σ(w)`. -/
theorem σ_neg (w : Fin 3 → ℝ) : (σ (-w) : A) = -σ w := by
  simp only [σ, Pi.neg_apply, Complex.ofReal_neg, neg_smul]
  rw [Finset.sum_neg_distrib]

/-- The Pauli commutator: `[σ(u), σ(v)] = 2i • σ(u ⨯₃ v)`. -/
theorem σ_commutator (u v : Fin 3 → ℝ) :
    (σ u : A) * σ v - σ v * σ u = (2 * Complex.I) • (σ (u ⨯₃ v) : A) := by
  rw [σ_mul_σ, σ_mul_σ, dotProduct_comm v u, ← cross_anticomm u v, σ_neg]
  module

end Qubit
