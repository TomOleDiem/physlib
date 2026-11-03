/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.LatticeFermions.InfiniteDynamics
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!

# Dynamics of states and its unitary implementation

The dynamics of states `ω_t = ω ∘ α_t`, and for invariant states the strongly continuous unitary
group implementing the dynamics in the GNS representation.

## i. Overview

Let `(α_t)` be a one-parameter group of `⋆`-automorphisms of a C⋆-algebra `𝔅`. A positive linear
functional `ω` evolves to `ω_t = ω ∘ α_t`; this is again positive, `ω_{s+t} = (ω_s)_t`, and
`t ↦ ω_t(a)` is continuous when `α` is strongly continuous.

If `ω` is invariant, `ω ∘ α_t = ω`, then `U_t [a] = [α_t(a)]` is isometric on the pre-GNS space:
`‖[α_t(a)]‖² = ω(α_t(a* a)) = ω(a* a) = ‖[a]‖²`. It extends to the GNS Hilbert space, and
`U_{s+t} = U_s U_t`, `U_0 = 1`, so every `U_t` is unitary. It implements the dynamics,
`π(α_t(a)) U_t = U_t π(a)`, and leaves the GNS vector `[1]` fixed. If `α` is strongly
continuous, so is `U`: on the dense set of vectors `[a]`, `t ↦ [α_t(a)]` is continuous because
`‖[b]‖ ≤ ‖ω‖^{1/2} ‖b‖`, and the `U_t` are uniformly bounded.

The results are applied to the infinite-volume dynamics of a graded local net, on the quasi-local
algebra with its spectral order.

Stone's theorem, which would identify the self-adjoint generator of `U_t`, is not available in
Mathlib; the generator is therefore not constructed here.

## ii. Key results

- `LatticeFermions.evolveState` : the evolved functional `ω_t = ω ∘ α_t`.
- `LatticeFermions.gnsEvolution` : the unitary implementation `U_t` on the GNS space.
- `LatticeFermions.gnsEvolution_mem_unitary` : `U_t` is unitary.
- `LatticeFermions.gnsEvolution_covariant` : `π(α_t(a)) U_t = U_t π(a)`.
- `LatticeFermions.continuous_gnsEvolution` : strong continuity of `U_t`.
- `LatticeFermions.Interaction.continuous_gnsEvolution_dynamics` : the lattice dynamics.

## iii. Table of contents

- A. Evolution of states
- B. The unitary implementation on the GNS space
- C. Strong continuity
- D. The dynamics of a graded local net

## iv. References

* O. Bratteli, D. W. Robinson, Operator Algebras and Quantum Statistical Mechanics 1,
  Corollary 2.3.17.

-/

@[expose] public section

noncomputable section

namespace LatticeFermions

open ProbabilisticTheory UniformSpace PositiveLinearMap
open scoped ComplexOrder

variable {𝔅 : Type*} [CStarAlgebra 𝔅] [PartialOrder 𝔅] [StarOrderedRing 𝔅]

/-!

## A. Evolution of states

-/

/-- The evolved functional `ω_t = ω ∘ α_t`. -/
def evolveState (α : AutomorphismGroup 𝔅) (ω : 𝔅 →ₚ[ℂ] ℂ) (t : ℝ) : 𝔅 →ₚ[ℂ] ℂ :=
  ω.comp (PositiveLinearMap.ofClass (α.toFun t))

variable (α : AutomorphismGroup 𝔅)

@[simp]
lemma evolveState_apply (ω : 𝔅 →ₚ[ℂ] ℂ) (t : ℝ) (a : 𝔅) :
    evolveState α ω t a = ω (α.toFun t a) := rfl

lemma evolveState_zero (ω : 𝔅 →ₚ[ℂ] ℂ) (a : 𝔅) : evolveState α ω 0 a = ω a := by
  rw [evolveState_apply, α.map_zero_apply]

/-- The group law of the evolution of states: `ω_{s+t} = (ω_s)_t`. -/
lemma evolveState_add (ω : 𝔅 →ₚ[ℂ] ℂ) (s t : ℝ) (a : 𝔅) :
    evolveState α ω (s + t) a = evolveState α (evolveState α ω s) t a := by
  simp [α.map_add_apply]

/-- The evolution of states preserves the normalization `ω(1) = 1`. -/
lemma evolveState_one (ω : 𝔅 →ₚ[ℂ] ℂ) (t : ℝ) : evolveState α ω t 1 = ω 1 := by
  simp

lemma continuous_evolveState (hα : ∀ a, Continuous fun t => α.toFun t a) (ω : 𝔅 →ₚ[ℂ] ℂ)
    (a : 𝔅) : Continuous fun t => evolveState α ω t a :=
  (map_continuous ω).comp (hα a)

/-- A functional is invariant if `ω ∘ α_t = ω` for all `t`. -/
def IsInvariantState (ω : 𝔅 →ₚ[ℂ] ℂ) : Prop := ∀ t a, ω (α.toFun t a) = ω a

/-!

## B. The unitary implementation on the GNS space

-/

variable {α} {ω : 𝔅 →ₚ[ℂ] ℂ} (hω : IsInvariantState α ω)

include hω in
lemma norm_toPreGNS_map (t : ℝ) (x : ω.PreGNS) :
    ‖ω.toPreGNS (α.toFun t (ω.ofPreGNS x))‖ = ‖x‖ := by
  rw [preGNS_norm_def, preGNS_norm_def, ofPreGNS_toPreGNS, ← map_star, ← map_mul, hω]

/-- The unitary implementation `[a] ↦ [α_t(a)]` on the pre-GNS space. -/
def gnsEvolutionPre (t : ℝ) : ω.PreGNS →L[ℂ] ω.PreGNS :=
  LinearMap.mkContinuous (ω.toPreGNS.toLinearMap ∘ₗ (α.toFun t).toAlgEquiv.toLinearMap ∘ₗ
    ω.ofPreGNS.toLinearMap) 1 fun x => by
      simp only [LinearMap.coe_comp, Function.comp_apply, one_mul]
      exact (norm_toPreGNS_map hω t x).le

lemma gnsEvolutionPre_apply (t : ℝ) (x : ω.PreGNS) :
    gnsEvolutionPre hω t x = ω.toPreGNS (α.toFun t (ω.ofPreGNS x)) := rfl

/-- The unitary implementation `U_t` of the dynamics on the GNS Hilbert space. -/
def gnsEvolution (t : ℝ) : ω.GNS →L[ℂ] ω.GNS := (gnsEvolutionPre hω t).completion

lemma gnsEvolution_coe (t : ℝ) (x : ω.PreGNS) :
    gnsEvolution hω t x = ((ω.toPreGNS (α.toFun t (ω.ofPreGNS x)) : ω.PreGNS) : ω.GNS) :=
  ContinuousLinearMap.completion_apply_coe _ x

lemma norm_gnsEvolution (t : ℝ) (ψ : ω.GNS) : ‖gnsEvolution hω t ψ‖ = ‖ψ‖ := by
  induction ψ using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp (gnsEvolution hω t).continuous) continuous_norm
  | ih x => rw [gnsEvolution_coe, Completion.norm_coe, Completion.norm_coe, norm_toPreGNS_map hω]

/-- The group law `U_{s+t} = U_s U_t`. -/
lemma gnsEvolution_add (s t : ℝ) :
    gnsEvolution hω (s + t) = gnsEvolution hω s * gnsEvolution hω t := by
  ext ψ
  induction ψ using Completion.induction_on with
  | hp => apply isClosed_eq <;> exact ContinuousLinearMap.continuous _
  | ih x =>
    show gnsEvolution hω (s + t) x = gnsEvolution hω s (gnsEvolution hω t x)
    rw [gnsEvolution_coe, gnsEvolution_coe, gnsEvolution_coe, ofPreGNS_toPreGNS,
      α.map_add_apply]

lemma gnsEvolution_zero : gnsEvolution hω 0 = 1 := by
  ext ψ
  induction ψ using Completion.induction_on with
  | hp => exact isClosed_eq (gnsEvolution hω 0).continuous continuous_id
  | ih x => rw [gnsEvolution_coe, α.map_zero_apply]; rfl

/-- Every `U_t` is unitary. -/
lemma gnsEvolution_mem_unitary (t : ℝ) :
    gnsEvolution hω t ∈ unitary (ω.GNS →L[ℂ] ω.GNS) := by
  have h1 : star (gnsEvolution hω t) * gnsEvolution hω t = 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (norm_gnsEvolution hω t)
  have h2 : gnsEvolution hω t * gnsEvolution hω (-t) = 1 := by
    rw [← gnsEvolution_add, add_neg_cancel, gnsEvolution_zero]
  have h3 : star (gnsEvolution hω t) = gnsEvolution hω (-t) := by
    rw [← mul_one (star _), ← h2, ← mul_assoc, h1, one_mul]
  exact Unitary.mem_iff.mpr ⟨h1, by rw [h3, h2]⟩

omit [PartialOrder 𝔅] [StarOrderedRing 𝔅] in
lemma gnsStarAlgHom_coe [PartialOrder 𝔅] [StarOrderedRing 𝔅] (ω : 𝔅 →ₚ[ℂ] ℂ) (b : 𝔅)
    (y : ω.PreGNS) :
    ω.gnsStarAlgHom b (y : ω.GNS) = ((ω.toPreGNS (b * ω.ofPreGNS y) : ω.PreGNS) : ω.GNS) := by
  show ω.gnsNonUnitalStarAlgHom b y = _
  simp

/-- The covariance `π(α_t(a)) U_t = U_t π(a)`: `U_t` implements the dynamics in the GNS
representation. -/
lemma gnsEvolution_covariant (t : ℝ) (a : 𝔅) :
    ω.gnsStarAlgHom (α.toFun t a) * gnsEvolution hω t =
      gnsEvolution hω t * ω.gnsStarAlgHom a := by
  ext ψ
  induction ψ using Completion.induction_on with
  | hp => apply isClosed_eq <;> exact ContinuousLinearMap.continuous _
  | ih x =>
    show ω.gnsStarAlgHom (α.toFun t a) (gnsEvolution hω t x) =
      gnsEvolution hω t (ω.gnsStarAlgHom a x)
    rw [gnsEvolution_coe, gnsStarAlgHom_coe, gnsStarAlgHom_coe, gnsEvolution_coe,
      ofPreGNS_toPreGNS, ofPreGNS_toPreGNS, map_mul (α.toFun t)]

/-- The GNS vector `[1]` is invariant. -/
lemma gnsEvolution_one (t : ℝ) :
    gnsEvolution hω t ((ω.toPreGNS 1 : ω.PreGNS) : ω.GNS) =
      ((ω.toPreGNS 1 : ω.PreGNS) : ω.GNS) := by
  rw [gnsEvolution_coe, ofPreGNS_toPreGNS, map_one]

/-!

## C. Strong continuity

-/

omit [StarOrderedRing 𝔅] in
lemma continuous_toPreGNS (ω : 𝔅 →ₚ[ℂ] ℂ) [StarOrderedRing 𝔅] :
    Continuous fun a : 𝔅 => ω.toPreGNS a := by
  let ωL : 𝔅 →L[ℂ] ℂ := ⟨ω.toLinearMap, map_continuous ω⟩
  have hb : ∀ a : 𝔅, ‖ω.toPreGNS.toLinearMap a‖ ≤ √‖ωL‖ * ‖a‖ := fun a => by
    rw [LinearEquiv.coe_coe, preGNS_norm_def', ofPreGNS_toPreGNS]
    calc √‖ω (star a * a)‖ ≤ √(‖ωL‖ * ‖a‖ ^ 2) := Real.sqrt_le_sqrt
          ((ωL.le_opNorm (star a * a)).trans (by rw [CStarRing.norm_star_mul_self, sq]))
      _ = √‖ωL‖ * ‖a‖ := by rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  exact (ω.toPreGNS.toLinearMap.mkContinuous _ hb).continuous

/-- Strong continuity of the unitary implementation, for a strongly continuous dynamics. -/
lemma continuous_gnsEvolution (hα : ∀ a, Continuous fun t => α.toFun t a) (ψ : ω.GNS) :
    Continuous fun t => gnsEvolution hω t ψ := by
  refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  obtain ⟨x, hx⟩ := Completion.denseRange_coe.exists_dist_lt ψ hε
  refine ⟨fun t => gnsEvolution hω t (x : ω.GNS), ?_, fun t => hεu ?_⟩
  · simp only [gnsEvolution_coe]
    exact Completion.continuous_coe _ |>.comp ((continuous_toPreGNS ω).comp (hα _))
  · rw [dist_eq_norm, ← map_sub, norm_gnsEvolution, ← dist_eq_norm]
    exact hx

/-!

## D. The dynamics of a graded local net

The quasi-local algebra is a closed star subalgebra, hence a C⋆-algebra, ordered by its spectral
order.

-/

namespace Interaction

variable {V : Type*} [DecidableEq V] {𝔄 : Type*} [CStarAlgebra 𝔄] {N : GradedLocalNet V 𝔄}

/-- The quasi-local algebra is closed. -/
instance _root_.LatticeFermions.GradedLocalNet.instIsClosedQuasiLocal (N : GradedLocalNet V 𝔄) :
    IsClosed (N.quasiLocal : Set 𝔄) :=
  N.isClosed_quasiLocal

/-- The spectral order on the quasi-local algebra. -/
abbrev quasiLocalOrder (N : GradedLocalNet V 𝔄) : PartialOrder N.quasiLocal :=
  CStarAlgebra.spectralOrder _

attribute [local instance] quasiLocalOrder

omit [DecidableEq V] in
/-- The spectral order makes the quasi-local algebra a star ordered ring. -/
lemma quasiLocal_starOrderedRing (N : GradedLocalNet V 𝔄) : StarOrderedRing N.quasiLocal :=
  CStarAlgebra.spectralOrderedRing _

attribute [local instance] quasiLocal_starOrderedRing

variable {Φ : Interaction N} {J : ℝ} (hJ : Φ.IsBoundedBy J) (hfin : Φ.LocallyFinite)

/-- The evolution `t ↦ ω(α_t(a))` of a positive functional on the quasi-local algebra under the
infinite-volume dynamics is continuous. -/
lemma continuous_evolveState_dynamics (ω : N.quasiLocal →ₚ[ℂ] ℂ) (a : N.quasiLocal) :
    Continuous fun t => evolveState (dynamicsGroup hJ hfin) ω t a :=
  continuous_evolveState _ (continuous_dynamicsAut hJ hfin) ω a

/-- For a positive functional invariant under the infinite-volume dynamics, the dynamics is
implemented in the GNS representation by the strongly continuous unitary group `U_t`. -/
lemma continuous_gnsEvolution_dynamics {ω : N.quasiLocal →ₚ[ℂ] ℂ}
    (hω : IsInvariantState (dynamicsGroup hJ hfin) ω) (ψ : ω.GNS) :
    Continuous fun t => gnsEvolution hω t ψ :=
  continuous_gnsEvolution hω (continuous_dynamicsAut hJ hfin) ψ

end Interaction

end LatticeFermions
