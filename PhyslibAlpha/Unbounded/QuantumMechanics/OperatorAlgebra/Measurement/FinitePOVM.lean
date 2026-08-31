/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.Basic

/-!
# Finite-outcome POVMs

`FinitePOVM` is the discrete measurement interface: one effect for each outcome, with the effects
adding to the identity. The general measurable-space interface is `POVM`; this file contains only
the finite specialization so finite-dimensional and finite-outcome developments can depend on it
without importing the full measure-theoretic layer.
-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder CStarAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- A finite-outcome POVM: effects indexed by `X` and resolving the identity. -/
structure FinitePOVM (A : Type*) [OperatorAlgebra A] (X : Type*) [Fintype X] where
  /-- The effect associated with each measurement outcome. -/
  effect : X → Effect A
  /-- The effects resolve the identity. -/
  sum_effect : ∑ x, (effect x : A) = 1

namespace FinitePOVM

/-- The finite Born probability vector obtained by evaluating each effect in a state. -/
noncomputable def probability {X : Type*} [Fintype X]
    (M : FinitePOVM A X) (ω : State A) : X → ℝ :=
  fun x => (ω (M.effect x : A)).re

lemma probability_nonneg {X : Type*} [Fintype X]
    (M : FinitePOVM A X) (ω : State A) (x : X) :
    0 ≤ M.probability ω x := by
  exact (Complex.le_def.mp
    (ω.toPositiveLinearMap.map_nonneg (M.effect x).2.1)).1

/-- The finite Born probabilities are normalized. -/
lemma sum_probability {X : Type*} [Fintype X]
    (M : FinitePOVM A X) (ω : State A) :
    ∑ x, M.probability ω x = 1 := by
  calc
    ∑ x, M.probability ω x =
        (ω.toPositiveLinearMap (∑ x, (M.effect x : A))).re := by
      simp [probability, map_sum]
    _ = (ω.toPositiveLinearMap (1 : A)).re := by rw [M.sum_effect]
    _ = 1 := by rw [ω.map_one]; norm_num

end FinitePOVM

end OperatorAlgebra
