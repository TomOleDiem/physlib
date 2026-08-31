/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.WStarAlgebra
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.Basic

/-!
# Normal states

A normal state is a state continuous for the weak-* topology supplied by a `WStarAlgebra`. Keeping
this definition in `States` makes the dependency direction explicit: the W⋆ algebra supplies the
topology, while measurements consume normal states to produce scalar probability measures.
-/

@[expose] public section

namespace OperatorAlgebra

open scoped Topology

structure NormalState (A : Type*) [WStarAlgebra A] extends State A where
  /-- The state is continuous for the chosen weak-* topology. -/
  weakStar_continuous :
    Continuous[WStarAlgebra.weakStarTopology A, inferInstance] (⇑toState : A → ℂ)

namespace NormalState

variable {A : Type*} [WStarAlgebra A]

noncomputable instance : CoeFun (NormalState A) (fun _ => A → ℂ) where
  coe ω := ω.toState

@[simp, nolint synTaut]
lemma toState_apply (ω : NormalState A) (a : A) : ω.toState a = ω a := rfl

/-- Weak-* continuity implies ordinary norm continuity because the weak-* topology is coarser. -/
theorem continuous (ω : NormalState A) : Continuous (ω : A → ℂ) :=
  continuous_le_dom (WStarAlgebra.norm_le_weakStarTopology A) ω.weakStar_continuous

end NormalState

end OperatorAlgebra
