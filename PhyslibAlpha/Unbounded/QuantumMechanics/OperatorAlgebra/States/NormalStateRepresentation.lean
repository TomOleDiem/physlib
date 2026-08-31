/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.DensityOperator
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.WStarAlgebra.RankOnePairing
public import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
# Representation of normal states by the concrete trace-class predual

This module closes the concrete `B(H)` normal-state boundary.  Weak-* continuity is converted by
Mathlib's weak representation theorem into a predual vector; rank-one observables then identify
that vector with a positive trace-class operator of trace one.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra InnerProductSpace Topology
open OperatorAlgebra TopologicalSpace

namespace OperatorAlgebra

variable {A : Type*} [WStarAlgebra A]

/-- Every weak-* continuous linear functional is represented by a vector in the selected predual.
This is the weak representation theorem transported through `WStarAlgebra.toDual`; unlike the
state-specific result below, it does not use positivity or the concrete Hilbert-space model. -/
theorem NormalState.predual_representation (ω : NormalState A) :
    ∃ ξ : WStarAlgebra.Predual A,
      ∀ a : A, WStarAlgebra.predualPairing ξ a = ω a := by
  let B : A →ₗ[ℂ] WStarAlgebra.Predual A →ₗ[ℂ] ℂ :=
    { toFun := fun a => (WStarAlgebra.toDual a).toLinearMap
      map_add' := fun a b => by ext ξ; simp
      map_smul' := fun c a => by ext ξ; simp }
  have hcont : Continuous (fun a : WeakBilin B => ω a) := by
    have hg : Continuous[
        (inferInstance : TopologicalSpace (WeakBilin B)),
        (inferInstance : TopologicalSpace (WeakDual ℂ (WStarAlgebra.Predual A)))]
        (fun a : WeakBilin B => StrongDual.toWeakDual (WStarAlgebra.toDual a)) := by
      apply WeakBilin.continuous_of_continuous_eval
      intro ξ
      change Continuous[
        (inferInstance : TopologicalSpace (WeakBilin B)), inferInstance]
        (fun a : WeakBilin B => B a ξ)
      exact WeakBilin.eval_continuous B ξ
    have hle : (inferInstance : TopologicalSpace (WeakBilin B)) ≤
        WStarAlgebra.weakStarTopology A := by
      change (inferInstance : TopologicalSpace (WeakBilin B)) ≤
        TopologicalSpace.induced
          (fun a : A => StrongDual.toWeakDual (WStarAlgebra.toDual a)) inferInstance
      exact continuous_iff_le_induced.mp hg
    exact continuous_le_dom
      (t₁ := WStarAlgebra.weakStarTopology A)
      (t₂ := (inferInstance : TopologicalSpace (WeakBilin B)))
      (t₃ := (inferInstance : TopologicalSpace ℂ))
      (f := fun a : A => ω a) hle ω.weakStar_continuous
  let f : StrongDual ℂ (WeakBilin B) :=
    { toFun := fun a => ω a
      map_add' := fun a b => map_add ω.toState.toPositiveLinearMap a b
      map_smul' := fun c a => map_smul ω.toState.toPositiveLinearMap c a
      cont := hcont }
  obtain ⟨ξ, hξ⟩ := LinearMap.dualEmbedding_surjective B f
  refine ⟨ξ, ?_⟩
  intro a
  have ha := congrArg (fun g : StrongDual ℂ (WeakBilin B) => g a) hξ
  change (B a) ξ = ω a at ha
  simpa [WStarAlgebra.predualPairing, B] using ha

end OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The trace-class representative of a normal state is unique.

Uniqueness uses surjectivity of the concrete trace pairing: equality on all bounded observables is
equality against every continuous linear functional on `TraceClass H`, and the dual separates the
trace-class Banach space. -/
theorem DensityOperator.ext_of_predualPairing_eq
    {ρ σ : DensityOperator H}
    (h : ∀ A : B(H),
      WStarAlgebra.predualPairing
          (TraceClass.ofOperator ρ.ρ ρ.traceClass) A =
        WStarAlgebra.predualPairing
          (TraceClass.ofOperator σ.ρ σ.traceClass) A) :
    ρ = σ := by
  have hξ : TraceClass.ofOperator ρ.ρ ρ.traceClass =
      TraceClass.ofOperator σ.ρ σ.traceClass := by
    apply (SeparatingDual.eq_iff_forall_dual_eq
      (R := ℂ) (V := TraceClass H)).mpr
    intro φ
    obtain ⟨A, rfl⟩ := (TraceClass.tracePairingEquiv (H := H)).surjective φ
    exact h A
  have hρ : ρ.ρ = σ.ρ := congrArg Subtype.val hξ
  cases ρ with
  | mk ρ hρpos hρclass hρtrace =>
    cases σ with
    | mk σ hσpos hσclass hσtrace =>
      simp_all

end OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A normal state on `B(H)` has a positive trace-class representative.

The weak-* representation theorem supplies the trace-class element.  Positivity is not imported
as a black box: rank-one observables test every diagonal matrix coefficient, and the complex
positive-operator criterion then gives positivity of the representing bounded operator. -/
theorem NormalState.exists_densityOperator (ω : NormalState (B(H))) :
    ∃ ρ : DensityOperator H,
      ∀ A : B(H),
        WStarAlgebra.predualPairing
            (TraceClass.ofOperator ρ.ρ ρ.traceClass) A = ω A := by
  obtain ⟨ξ, hξ⟩ := NormalState.predual_representation ω
  let T : B(H) := ξ.1
  have hTpos : 0 ≤ T := by
    apply (operator_nonneg_iff_isPositive T).mpr
    apply (ContinuousLinearMap.isPositive_iff_complex T).mpr
    intro x
    have hcoeff : ω (InnerProductSpace.rankOne ℂ x x) =
        ⟪x, T x⟫_ℂ := by
      have h := hξ (InnerProductSpace.rankOne ℂ x x)
      change WStarAlgebra.predualPairing ξ
          (InnerProductSpace.rankOne ℂ x x) = ω _ at h
      rw [WStarAlgebra.predualPairing_apply] at h
      change TraceClass.tracePairing (InnerProductSpace.rankOne ℂ x x) ξ = ω _ at h
      rw [TraceClass.tracePairing_rankOne_left ξ x x] at h
      exact h.symm
    have hω : 0 ≤ ω (InnerProductSpace.rankOne ℂ x x) :=
      ω.toState.toPositiveLinearMap.map_nonneg
        ((operator_nonneg_iff_isPositive _).mpr
          (InnerProductSpace.isPositive_rankOne_self x))
    have hq : 0 ≤ ⟪x, T x⟫_ℂ := hcoeff ▸ hω
    have hqre : 0 ≤ (⟪x, T x⟫_ℂ).re := (Complex.le_def.mp hq).1
    have hqim : (⟪x, T x⟫_ℂ).im = 0 := ((Complex.le_def.mp hq).2).symm
    have hinner : ⟪T x, x⟫_ℂ = ⟪x, T x⟫_ℂ := by
      rw [← inner_conj_symm (T x) x]
      apply Complex.ext
      · exact Complex.conj_re _
      · rw [Complex.conj_im, hqim]
        simp
    refine ⟨?_, ?_⟩
    · rw [hinner]
      apply Complex.ext <;> simp [hqim]
    · rw [hinner]
      exact hqre
  have htrace : trace T ξ.2 = 1 := by
    have h := hξ (1 : B(H))
    change WStarAlgebra.predualPairing ξ (1 : B(H)) = ω 1 at h
    rw [WStarAlgebra.predualPairing_apply] at h
    change TraceClass.tracePairing (1 : B(H)) ξ = ω 1 at h
    rw [TraceClass.tracePairing_apply] at h
    have h' : trace ξ.1 ξ.2 = ω 1 := by simpa using h
    calc
      trace T ξ.2 = trace ξ.1 ξ.2 := rfl
      _ = ω 1 := h'
      _ = 1 := ω.toState.map_one
  refine ⟨⟨T, hTpos, ξ.2, htrace⟩, ?_⟩
  intro A
  exact hξ A

end OperatorAlgebra
