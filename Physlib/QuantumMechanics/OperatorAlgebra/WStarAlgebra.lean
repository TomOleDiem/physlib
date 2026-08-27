/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Measurement.State
public import Mathlib.Analysis.Normed.Module.WeakDual

/-!

# W⋆-algebras: predual and the weak-⋆ topology

Mathlib has no predual/weak-⋆ topology infrastructure for operator algebras — `Unbounded/
NormalState.lean`'s honesty note flagged this as a genuine gap and, on the user's instruction, we
build it ourselves rather than continue to route around it. This file gives Sakai's Banach-space
definition of a W⋆-algebra (there is no need for any Hilbert-space representation, or even for `A`
to be an algebra of operators at all): `A` is a W⋆-algebra iff it is isometrically the dual of
*some* Banach space, its predual. Mathlib's own weak-⋆ topology machinery for the dual of a normed
space (`Mathlib.Analysis.Normed.Module.WeakDual`, `WeakDual`/`StrongDual`) does essentially all of
the topological work once that identification is in hand — genuinely no new topology needed, only
the identification and its transport back along it.

## Definitions

- `WStarAlgebra A` : `A` together with a chosen predual `Predual A` and an isometric linear
  identification `toDual : A ≃ₗᵢ[ℂ] StrongDual ℂ (Predual A)`. Sakai's theorem (not needed here)
  says the predual, when it exists, is unique up to isometric isomorphism but *not* canonical —
  matching that, `WStarAlgebra A` is data (a `class`, one chosen witness), not a `Prop`.
- `WStarAlgebra.weakStarTopology A` : the weak-⋆ topology on `A`, pulled back through `toDual` from
  `WeakDual ℂ (Predual A)`. Deliberately *not* a `TopologicalSpace A` instance — `A` already has
  its norm topology (from `CStarAlgebra`), and the entire point here is to compare the two, so
  they must coexist rather than compete for instance resolution.
- `WStarAlgebra.norm_le_weakStarTopology` : the weak-⋆ topology is coarser than the norm topology
  — proved outright from Mathlib's `toDual`-is-an-isometry and `StrongDual.toWeakDual`-is-
  continuous facts, no new hard analysis needed.
- `NormalState A` : a state continuous for `weakStarTopology` — the actual, Sakai-honest
  definition of "normal state" this development previously could not state (see `Unbounded/
  NormalState.lean`'s history). `NormalState.continuous` recovers norm-continuity as a corollary,
  for free, from `norm_le_weakStarTopology`.

## Concrete realization

The companion module `WStarAlgebra/InfiniteDimensional.lean` supplies the canonical concrete
instance for `B(H)`. Its predual is the completed trace-class space `TraceClass H`, and its
isometric dual identification is the trace pairing `A ↦ (ρ ↦ Tr(Aρ))`. The proof is split across
`TraceClass/Completeness.lean` and `WStarAlgebra/TracePairingSurjectivity.lean`; this file remains
the abstract weak-⋆ and normal-state layer.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra Topology
open TopologicalSpace
open Filter

namespace OperatorAlgebra

/-! ## W⋆-algebras -/

/-- **A W⋆-algebra**: an operator algebra `A` that is, isometrically, the Banach-space dual of
some other Banach space `Predual A` — Sakai's characterization of a von Neumann algebra, purely in
Banach-space terms. A `WStarAlgebra A` instance packages one specific choice of predual (Sakai's
theorem, not needed here, says any two choices are isometrically isomorphic), which is exactly the
data needed to write down the weak-⋆ topology `A` inherits from it
(`WStarAlgebra.weakStarTopology`). -/
class WStarAlgebra (A : Type*) extends OperatorAlgebra A where
  /-- The predual: a Banach space `E` with `A ≃ₗᵢ[ℂ] StrongDual ℂ E` isometrically. -/
  Predual : Type*
  predual_normedAddCommGroup : NormedAddCommGroup Predual
  predual_normedSpace : NormedSpace ℂ Predual
  predual_completeSpace : CompleteSpace Predual
  /-- The defining isometric identification `A ≃ₗᵢ[ℂ] StrongDual ℂ (Predual A)`, `a ↦ (ξ ↦
  ⟨a, ξ⟩)` for the duality pairing `A` inherits from being `Predual A`'s dual. -/
  toDual : A ≃ₗᵢ[ℂ] StrongDual ℂ Predual

attribute [instance] WStarAlgebra.predual_normedAddCommGroup WStarAlgebra.predual_normedSpace
  WStarAlgebra.predual_completeSpace

namespace WStarAlgebra

variable (A : Type*) [WStarAlgebra A]

/-- **The weak-⋆ topology on `A`**: pulled back, through the defining predual isometry `toDual`,
from the weak-⋆ topology on `WeakDual ℂ (Predual A)` (Mathlib's `WeakDual`, the coarsest topology
making every evaluation `f ↦ f ξ`, `ξ : Predual A`, continuous). This models the physically correct
notion of "converges weakly" for states/observables on `A` — e.g. it is exactly the topology in
which a sequence of density operators `ρₙ → ρ` weak-⋆ iff `Tr(ρₙ A) → Tr(ρA)` for every bounded
`A`, the usual sense of convergence of quantum states.

Deliberately *not* registered as a `TopologicalSpace A` instance: see the module docstring. -/
def weakStarTopology : TopologicalSpace A :=
  TopologicalSpace.induced (fun a => StrongDual.toWeakDual (toDual a)) inferInstance

/-- **The weak-⋆ topology is coarser than the norm topology.** The basic sanity fact making
`weakStarTopology` a genuine weakening of the topology `A` already carries as a C⋆-algebra: the
identity map `A → A`, viewed as `(A, ‖·‖) → (A, \text{weak-⋆})`, is continuous. Proved from two
continuity facts already in Mathlib — `toDual` is a (linear) isometry, hence norm-continuous
(`LinearIsometryEquiv.continuous`), and `StrongDual.toWeakDual` is continuous
(`NormedSpace.Dual.toWeakDual_continuous`) — composing gives continuity of `weakStarTopology`'s
defining map for the *norm* topology on the domain, which is exactly what "coarser" means via
`continuous_iff_le_induced`. No genuinely new analysis: this is Mathlib's own comparison theorem
for the weak-⋆ topology on a dual space, transported along `toDual`. -/
theorem norm_le_weakStarTopology :
    (inferInstance : TopologicalSpace A) ≤ weakStarTopology A :=
  continuous_iff_le_induced.mp
    (NormedSpace.Dual.toWeakDual_continuous.comp (toDual (A := A)).continuous)

end WStarAlgebra

/-! ## The predual pairing -/

namespace WStarAlgebra

variable {A : Type*} [WStarAlgebra A]

/-- The canonical continuous functional on `A` associated with a predual vector.  This is the
pairing that later concrete normality theorems use; spelling it out here avoids repeatedly
reconstructing the evaluation map through `toDual`. -/
def predualPairing (ξ : WStarAlgebra.Predual A) : A →L[ℂ] ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ ξ).comp
    ((toDual (A := A)).toLinearIsometry.toContinuousLinearMap)

@[simp]
lemma predualPairing_apply (ξ : WStarAlgebra.Predual A) (a : A) :
    predualPairing ξ a = toDual a ξ := rfl

lemma norm_predualPairing_apply (ξ : WStarAlgebra.Predual A) (a : A) :
    ‖predualPairing ξ a‖ ≤ ‖a‖ * ‖ξ‖ := by
  have h := ContinuousLinearMap.le_opNorm (toDual a) ξ
  simpa [predualPairing] using h

/-- The predual pairing is continuous for the weak-* topology by construction.

This is the basic normal-functional fact behind the von Neumann boundary: unlike a normal state,
which is a positive normalized functional, a predual vector gives an arbitrary (not necessarily
positive) weak-* continuous functional.  Keeping this lemma explicit prevents later spectral
measure arguments from silently replacing additivity against all predual functionals by the weaker
statement for states alone. -/
theorem predualPairing_weakStar_continuous (ξ : WStarAlgebra.Predual A) :
    Continuous[WStarAlgebra.weakStarTopology A, inferInstance]
      (predualPairing ξ) := by
  change Continuous[TopologicalSpace.induced
      (fun a => StrongDual.toWeakDual (toDual a)) inferInstance, inferInstance]
      (fun a => (StrongDual.toWeakDual (toDual a)) ξ)
  have hmap : Continuous[TopologicalSpace.induced
      (fun a => StrongDual.toWeakDual (toDual a)) inferInstance, inferInstance]
      (fun a => StrongDual.toWeakDual (toDual a)) :=
    (continuous_induced_dom (f := fun a : A =>
      StrongDual.toWeakDual (toDual a)))
  have heval : Continuous[
      (inferInstance : TopologicalSpace (WeakDual ℂ (WStarAlgebra.Predual A))), inferInstance]
      (fun z : WeakDual ℂ (WStarAlgebra.Predual A) => z ξ) :=
    WeakBilin.eval_continuous _ _
  exact @Continuous.comp A (WeakDual ℂ (WStarAlgebra.Predual A)) ℂ
    (TopologicalSpace.induced (fun a => StrongDual.toWeakDual (toDual a)) inferInstance)
    inferInstance inferInstance _ _ heval hmap

/-- The predual pairings separate points of a W⋆-algebra.

This is the algebraic half of the weak-* interface: equality can be checked against every
predual vector.  It is useful when an operator-valued construction is first identified through
its normal matrix coefficients and only then packaged as an element of `A`. -/
theorem ext_of_forall_predualPairing_eq {a b : A}
    (h : ∀ ξ : WStarAlgebra.Predual A, predualPairing ξ a = predualPairing ξ b) :
    a = b := by
  apply (toDual (A := A)).injective
  ext ξ
  exact h ξ

/-! The topology is equivalently characterized by convergence of all canonical predual pairings.
This formulation is deliberately filter-based, so it applies to nets as well as sequences. -/

theorem tendsto_weakStar_iff_forall_predualPairing_tendsto
    {α : Type*} {l : Filter α} {f : α → A} {a : A} :
    Tendsto f l (@nhds A (WStarAlgebra.weakStarTopology A) a) ↔
      ∀ ξ : WStarAlgebra.Predual A,
        Tendsto (fun i => predualPairing ξ (f i)) l
          (𝓝 (predualPairing ξ a)) := by
  change Tendsto f l (@nhds A
      (TopologicalSpace.induced
        (fun b => StrongDual.toWeakDual (toDual b)) inferInstance) a) ↔ _
  rw [nhds_induced, Filter.tendsto_comap_iff]
  change Tendsto (fun i => StrongDual.toWeakDual (toDual (f i))) l
      (𝓝 (StrongDual.toWeakDual (toDual a))) ↔
    ∀ ξ : WStarAlgebra.Predual A,
      Tendsto (fun i => (toDual (f i)) ξ) l (𝓝 ((toDual a) ξ))
  exact tendsto_iff_forall_eval_tendsto_topDualPairing
    (𝕜 := ℂ) (E := WStarAlgebra.Predual A) (l := l)
    (f := fun i => StrongDual.toWeakDual (toDual (f i)))
    (x := StrongDual.toWeakDual (toDual a))

end WStarAlgebra

/-! ## Normal states -/

/-- **A normal state on a W⋆-algebra `A`**: a state continuous for the weak-⋆ topology
`WStarAlgebra.weakStarTopology` induced by `A`'s chosen predual — Sakai's actual definition of
"normal", now stated honestly rather than as the placeholder `Unbounded/NormalState.lean`
previously used (see that file's history and this file's module docstring). Concretely, for `A =
B(H)`, this is exactly "continuous under `ρₙ → ρ` weak-⋆", the condition singling out states given
by density operators (`Unbounded/DensityOperator.lean`) among all (not-necessarily-normal) states;
the concrete `B(H)` instance is supplied by `WStarAlgebra/InfiniteDimensional.lean`. -/
structure NormalState (A : Type*) [WStarAlgebra A] extends State A where
  /-- The defining condition: `toState` is continuous for the weak-⋆ topology, not merely as an
  abstract linear functional. -/
  weakStar_continuous :
    Continuous[WStarAlgebra.weakStarTopology A, inferInstance] (⇑toState : A → ℂ)

namespace NormalState

variable {A : Type*} [WStarAlgebra A]

noncomputable instance : CoeFun (NormalState A) (fun _ => A → ℂ) where
  coe ω := ω.toState

@[simp]
lemma toState_apply (ω : NormalState A) (a : A) : ω.toState a = ω a := rfl

/-- **Every normal state is automatically norm-continuous.** Weak-⋆ continuity is, on its face, a
different (in fact strictly weaker a priori, since the weak-⋆ topology has fewer open sets to
check) condition than norm continuity — but a map continuous for a *coarser* domain topology is
automatically continuous for any *finer* one (`continuous_le_dom`), and the weak-⋆ topology is
coarser than the norm topology (`WStarAlgebra.norm_le_weakStarTopology`). So normality, despite
being the more honest and more restrictive physical condition on states, costs nothing in terms of
the ordinary continuity `Measurement/State.lean`'s API implicitly relies on. -/
theorem continuous (ω : NormalState A) : Continuous (ω : A → ℂ) :=
  continuous_le_dom (WStarAlgebra.norm_le_weakStarTopology A) ω.weakStar_continuous

end NormalState

end OperatorAlgebra
