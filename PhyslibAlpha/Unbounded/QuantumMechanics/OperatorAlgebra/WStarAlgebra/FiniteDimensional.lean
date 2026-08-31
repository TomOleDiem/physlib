/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.WStarAlgebra
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.NormalState
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.HilbertSpace
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The finite-dimensional `B(H)` W⋆-algebra

In finite dimension the canonical embedding into the bidual is onto.  This gives a completely
proved concrete `WStarAlgebra (B(H))` instance, with predual `StrongDual ℂ B(H)`.  It is not the
infinite-dimensional trace-class predual: that remains a separate analytic construction.  The
finite-dimensional instance is nevertheless useful for testing the abstract normal-affiliation
API against an actual operator algebra, and it records the exact finite-dimensional argument
instead of leaving an unqualified `B(H)` instance in the typeclass search.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra

namespace OperatorAlgebra

namespace FiniteDimensionalWStar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]

/-- In finite dimension, continuous linear functionals and algebraic linear functionals have the
same dimension. -/
@[nolint unusedArguments]
lemma finrank_strongDual_eq :
    Module.finrank ℂ (StrongDual ℂ E) = Module.finrank ℂ E := by
  rw [← (LinearMap.toContinuousLinearMap (E := E) (F' := ℂ)).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- The canonical bidual embedding is onto in finite dimension. -/
lemma inclusionInDoubleDual_surjective :
    Function.Surjective
      (NormedSpace.inclusionInDoubleDualLi ℂ (E := E)) := by
  let f := NormedSpace.inclusionInDoubleDualLi ℂ (E := E)
  have hdim : Module.finrank ℂ E =
      Module.finrank ℂ (StrongDual ℂ (StrongDual ℂ E)) := by
    calc
      Module.finrank ℂ E = Module.finrank ℂ (StrongDual ℂ E) :=
        (finrank_strongDual_eq (E := E)).symm
      _ = Module.finrank ℂ (StrongDual ℂ (StrongDual ℂ E)) :=
        (finrank_strongDual_eq (E := StrongDual ℂ E)).symm
  have hinj : Function.Injective f.toLinearMap := by
    intro x y hxy
    exact LinearIsometry.injective f hxy
  have hiff : Function.Injective f.toLinearMap ↔ Function.Surjective f.toLinearMap :=
    LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (V := E) (V₂ := StrongDual ℂ (StrongDual ℂ E)) hdim
  exact hiff.mp hinj

/-- The finite-dimensional bidual isometry, bundled as an equivalence. -/
noncomputable def bidualEquiv :
    E ≃ₗᵢ[ℂ] StrongDual ℂ (StrongDual ℂ E) :=
  LinearIsometryEquiv.ofSurjective
    (NormedSpace.inclusionInDoubleDualLi ℂ (E := E))
    inclusionInDoubleDual_surjective

end FiniteDimensionalWStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- A concrete finite-dimensional W⋆-algebra instance for bounded operators.

The chosen predual is the strong dual of `B(H)`.  The defining isometry is the canonical bidual
embedding, which is onto because `B(H)` is finite-dimensional.  In infinite dimension this
construction is unavailable, so this instance deliberately carries the finite-dimensional
hypothesis rather than claiming to solve the trace-class predual problem. -/
noncomputable instance instWStarAlgebraBoundedOperatorsFiniteDimensional :
    WStarAlgebra B(H) where
  Predual := StrongDual ℂ B(H)
  predualNormedAddCommGroup := inferInstance
  predualNormedSpace := inferInstance
  predualCompleteSpace := inferInstance
  toDual := FiniteDimensionalWStar.bidualEquiv (E := B(H))

/-! ## Finite-dimensional normal states -/

namespace WStarAlgebra

variable {A : Type*} [WStarAlgebra A] [FiniteDimensional ℂ A]

/-- In finite dimension every state is normal for the chosen weak-* topology.

The proof makes the topology transport explicit.  The weak-* topology is induced by the linear
embedding `A → WeakDual ℂ (Predual A)`, hence is Hausdorff; finite-dimensional topological vector
spaces over `ℂ` carry their usual module topology, so every linear state is continuous. -/
noncomputable def NormalState.ofStateFiniteDimensional (ω : State A) : NormalState A := by
  letI : TopologicalSpace A := WStarAlgebra.weakStarTopology A
  let f : A →ₗ[ℂ] WeakDual ℂ (WStarAlgebra.Predual A) :=
    (StrongDual.toWeakDual (𝕜 := ℂ)).toLinearMap.comp
      (WStarAlgebra.toDual (A := A)).toLinearEquiv.toLinearMap
  letI : IsTopologicalAddGroup A := topologicalAddGroup_induced f
  letI : ContinuousSMul ℂ A := continuousSMul_induced f
  have htop : Topology.IsEmbedding f := by
    refine ⟨?_, ?_⟩
    · constructor
      change WStarAlgebra.weakStarTopology A = TopologicalSpace.induced f inferInstance
      rfl
    · intro a b hab
      apply (WStarAlgebra.toDual (A := A)).injective
      exact StrongDual.toWeakDual.injective (show f a = f b from hab)
  letI : T2Space A := htop.t2Space
  refine { toState := ω, weakStar_continuous := ?_ }
  exact LinearMap.continuous_of_finiteDimensional ω.toPositiveLinearMap.toLinearMap

@[simp]
lemma NormalState.ofStateFiniteDimensional_toState (ω : State A) :
    (NormalState.ofStateFiniteDimensional ω).toState = ω := by
  rfl

end WStarAlgebra

/-!
The implementation above lives in the `WStarAlgebra` namespace because it
constructs the weak-star topology explicitly.  Re-export the constructor in
the public `NormalState` namespace as well; this is the name users should
normally see when turning a finite-dimensional state into a normal state.
-/

namespace NormalState

variable {A : Type*} [WStarAlgebra A] [FiniteDimensional ℂ A]

/-- The normal state built from an arbitrary state, in finite dimension (every state is
automatically normal there). -/
noncomputable def ofStateFiniteDimensional (ω : State A) : NormalState A :=
  WStarAlgebra.NormalState.ofStateFiniteDimensional ω

@[simp]
lemma ofStateFiniteDimensional_toState (ω : State A) :
    (ofStateFiniteDimensional ω).toState = ω := by
  rfl

end NormalState

@[simp]
lemma finiteDimensionalWStar_toDual_apply (A : B(H))
    (ρ : StrongDual ℂ B(H)) :
    WStarAlgebra.toDual A ρ = ρ A := rfl

end OperatorAlgebra
