/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.Example.Schwartz
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.InvariantCore
public import PhyslibAlpha.Mathematics.LadderSystem.Basic

/-!

# Testing the API: a `LadderSystem` and an `InvariantCore` from `Q`, `P`

`Schwartz.lean` proves `[Q,P] = iℏ` and `[a,a†] = 1` directly. This file packages that same data
through two *general* pieces of reusable infrastructure — `PhyslibAlpha.Mathematics.LadderSystem`
and this project's own `OperatorAlgebra.Unbounded.InvariantCore` — to check both actually accept a
real construction, not just type-check in the abstract.

Deliberately built from nothing but `Schwartz.lean`'s `ladderA`/`ladderAdag`/`ladder_comm` (which
themselves use only Mathlib, `𝓢(ℝ, ℂ)`, and `positionOperatorSchwartz`/`momentumOperatorSchwartz`):
no other part of `Physlib` (in particular no `d`-dimensional `HarmonicOscillator`/`ξ`/mass-and-
frequency apparatus) is used here.

## Key results

- `toLadderSystem` : `ladderA`/`ladderAdag`, bundled as a genuine one-mode `LadderSystem`. Its
  number operator, `gl(1)`-module structure, and commutation relations are then free.
- `toInvariantCore` : `Q`/`P` (as plain `Module.End`s, i.e. forgetting continuity), bundled as an
  `InvariantCore` for any indexed placeholder family `T : Fin 2 → β` — `InvariantCore` does not
  constrain `T` beyond indexing it, so this is a genuine, non-vacuous instantiation of the
  structure.
- `restrictCommutator_toInvariantCore` : `core.restrictCommutator 0 1 = (iℏ) • 1` — the "ordinary
  `Module.End` algebra" `InvariantCore`'s docstring promises, computed for real from `ccr`, not
  merely asserted.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder
open QuantumMechanics OneDimension Constants SchwartzMap
open OperatorAlgebra OperatorAlgebra.Unbounded.Example

namespace OperatorAlgebra.Unbounded.Example

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## A `LadderSystem` from `ladderA`/`ladderAdag` -/

variable (m ω : ℝ) (hm : 0 < m) (hω : 0 < ω)

/-- `ladderA`/`ladderAdag`, bundled as a one-mode `LadderSystem` — `PhyslibAlpha`'s general
ladder-operator abstraction applied to this project's own `Q`/`P`-derived operators, exercising
that it genuinely accepts a fresh, non-`HarmonicOscillator` construction. -/
def toLadderSystem (m ω : ℝ) (hm : 0 < m) (hω : 0 < ω) :
    LadderSystem ℂ (𝓢(ℝ, ℂ)) 1 where
  a _ := (ladderA m ω).toLinearMap
  ac _ := (ladderAdag m ω).toLinearMap
  comm_a_ac i j := by
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp only []
    have h := ladder_comm m ω hm hω
    apply_fun ContinuousLinearMap.toLinearMap at h
    simpa [LieRing.of_associative_ring_bracket, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.coe_comp, Module.End.mul_eq_comp, Module.End.one_eq_id,
      ContinuousLinearMap.one_def] using h
  comm_a_a _ _ := lie_self _
  comm_ac_ac _ _ := lie_self _

/-! ## An `InvariantCore` from `Q`/`P` -/

variable {β : Type*}

/-- `Q`/`P`, forgetting continuity, bundled as an `InvariantCore` for *any* placeholder family
`T : Fin 2 → AffiliatedOperator A` — `InvariantCore` deliberately does not require `T` to be
verified as "really" `Q`/`P` (see `Core.lean`'s module docstring), only that a core `D` and a
`restrict` family exist, so this is a genuine, concrete instance for an arbitrary `A`. -/
def toInvariantCore (T : Fin 2 → β) : InvariantCore T where
  D := 𝓢(ℝ, ℂ)
  instAddCommGroup := inferInstance
  instModule := inferInstance
  restrict := ![positionOperatorSchwartz.toLinearMap, momentumOperatorSchwartz.toLinearMap]

/-- **The payoff.** `core.restrictCommutator 0 1`, the commutator `[Q, P]` computed purely as
`Module.End ℂ D` algebra via `InvariantCore`'s API, equals `(iℏ) • 1` — recovering `ccr` through
  the general abstraction rather than by hand, exactly the ordinary-algebra interface promised by
  `InvariantCore`. -/
theorem restrictCommutator_toInvariantCore (T : Fin 2 → β) :
    (toInvariantCore T).restrictCommutator 0 1 = (Complex.I * (ℏ : ℂ)) • (1 : Module.End ℂ (𝓢(ℝ, ℂ))) := by
  have h := ccr
  apply_fun ContinuousLinearMap.toLinearMap at h
  simp only [toInvariantCore, InvariantCore.restrictCommutator, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  simp only [ContinuousLinearMap.toLinearMap_sub, ContinuousLinearMap.toLinearMap_mul,
    ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.one_def] at h
  show (positionOperatorSchwartz : 𝓢(ℝ, ℂ) →ₗ[ℂ] 𝓢(ℝ, ℂ)) * momentumOperatorSchwartz -
      (momentumOperatorSchwartz : 𝓢(ℝ, ℂ) →ₗ[ℂ] 𝓢(ℝ, ℂ)) * positionOperatorSchwartz =
      (Complex.I * (ℏ : ℂ)) • (1 : Module.End ℂ (𝓢(ℝ, ℂ)))
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, Module.End.one_eq_id]
  exact h

end OperatorAlgebra.Unbounded.Example
