/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.HilbertSpace
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.Expectation

/-!

# Vector states on bounded operators

On any complex Hilbert space `H`, a unit vector `ψ` defines a state on `B(H)` by
`A ↦ ⟪ψ, Aψ⟫_ℂ`. This is the bridge from the abstract `OperatorAlgebra.State` API to ordinary
Hilbert-space expectation values.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The state defined by a unit vector, `A ↦ ⟪ψ, Aψ⟫_ℂ`. -/
noncomputable def vectorState (ψ : H) (hψ : ‖ψ‖ = 1) : State (B(H)) where
  toPositiveLinearMap := PositiveLinearMap.mk₀
    { toFun := fun A => ⟪ψ, A ψ⟫_ℂ
      map_add' := fun A B => by simp
      map_smul' := fun c A => by simp }
    (fun A hA => ((operator_nonneg_iff_isPositive A).mp hA).inner_nonneg_right ψ)
  map_one := by
    show ⟪ψ, (1 : B(H)) ψ⟫_ℂ = 1
    rw [one_apply_eq_self, inner_self_eq_norm_sq_to_K, hψ]
    norm_num

/-- The main bridge from abstract states to the usual Hilbert-space expectation value. -/
@[simp]
lemma vectorState_apply (ψ : H) (hψ : ‖ψ‖ = 1) (A : B(H)) :
    vectorState ψ hψ A = ⟪ψ, A ψ⟫_ℂ :=
  rfl

/-- The real (`States.Expectation`) expectation of an observable in a vector state is the usual
Hilbert-space expectation value. -/
@[simp]
lemma vectorState_expectation (ψ : H) (hψ : ‖ψ‖ = 1) (a : Observable (B(H))) :
    (vectorState ψ hψ)⟨a⟩ = (⟪ψ, (a : B(H)) ψ⟫_ℂ).re :=
  rfl

end OperatorAlgebra
