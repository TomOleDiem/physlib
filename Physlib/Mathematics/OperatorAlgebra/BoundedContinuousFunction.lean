/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OperatorAlgebra.State
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!

# Bounded continuous functions as a commutative observable algebra

For any topological space `X`, the bounded continuous complex-valued functions `X →ᵇ ℂ` form a
commutative unital C⋆-algebra (this instance already exists in Mathlib). This file supplies the
two pieces of generic machinery that a classical observable algebra of this shape needs and that
Mathlib does not provide directly:

* precomposition by a homeomorphism of `X`, bundled as a ⋆-algebra automorphism, used to turn a
  flow on phase space into a one-parameter group of algebra automorphisms;
* the state obtained by integrating against a probability measure on `X`, used to turn a
  probability measure on phase space (a point mass, a Gaussian, a Gibbs distribution, ...) into a
  state of the observable algebra.

Neither construction is specific to any particular classical system: both belong here rather than
under a specific system's directory.

## Main definitions

* `BoundedContinuousFunction.compHomeomorphStarAlgEquiv`: precomposition by a homeomorphism, as a
  ⋆-algebra automorphism.
* `BoundedContinuousFunction.evalStarAlgHom`: evaluation at a point, as a ⋆-algebra homomorphism.
* `BoundedContinuousFunction.probState`: the state `f ↦ ∫ f dμ` associated with a probability
  measure `μ`.

-/

@[expose] public section

noncomputable section

open scoped BoundedContinuousFunction ComplexOrder
open OperatorAlgebra MeasureTheory

namespace BoundedContinuousFunction

/-!
## Precomposition by a homeomorphism
-/

section CompHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Precomposition by a homeomorphism, `f ↦ f ∘ e`, as a ⋆-algebra automorphism of complex-valued
bounded continuous functions. Every algebraic compatibility obligation is pointwise and therefore
definitional, exactly as for the corresponding automorphism of `C(X, A)`
(`Homeomorph.compStarAlgEquiv'`). -/
def compHomeomorphStarAlgEquiv (e : X ≃ₜ Y) : (Y →ᵇ ℂ) ≃⋆ₐ[ℂ] (X →ᵇ ℂ) where
  toFun f := f.compContinuous (e : C(X, Y))
  invFun g := g.compContinuous (e.symm : C(Y, X))
  left_inv f := ext fun x => by simp
  right_inv g := ext fun x => by simp
  map_mul' _ _ := ext fun _ => rfl
  map_add' _ _ := ext fun _ => rfl
  map_star' _ := ext fun _ => rfl
  map_smul' _ _ := ext fun _ => rfl

@[simp]
lemma compHomeomorphStarAlgEquiv_apply (e : X ≃ₜ Y) (f : Y →ᵇ ℂ) (x : X) :
    compHomeomorphStarAlgEquiv e f x = f (e x) :=
  rfl

end CompHomeomorph

/-!
## Evaluation at a point
-/

section Eval

variable {X : Type*} [TopologicalSpace X]

/-- Evaluation at a point, as a ⋆-algebra homomorphism into `ℂ`. -/
def evalStarAlgHom (x : X) : (X →ᵇ ℂ) →⋆ₐ[ℂ] ℂ :=
  (ContinuousMap.evalStarAlgHom ℂ ℂ x).comp (toContinuousMapStarₐ ℂ)

@[simp]
lemma evalStarAlgHom_apply (x : X) (f : X →ᵇ ℂ) :
    evalStarAlgHom x f = f x :=
  rfl

end Eval

/-!
## Order structure

`X →ᵇ ℂ` inherits `CommCStarAlgebra` from Mathlib for any topological space `X`, but Mathlib does
not choose a canonical order for it. We use the generic spectral order, which is available on
*any* C⋆-algebra and needs no pointwise-order compatibility work (unlike the natural pointwise
order on `X →ᵇ ℂ`, which Mathlib has not developed for bounded, as opposed to compactly supported
or arbitrary, continuous functions).
-/

section Order

variable (X : Type*) [TopologicalSpace X]

noncomputable instance instSpectralPartialOrder : PartialOrder (X →ᵇ ℂ) :=
  CStarAlgebra.spectralOrder _

noncomputable instance instSpectralStarOrderedRing : StarOrderedRing (X →ᵇ ℂ) :=
  CStarAlgebra.spectralOrderedRing _

end Order

/-!
## States from probability measures

Integration against a probability measure on `X` is a state of `X →ᵇ ℂ`, for *any* probability
measure: positivity is entirely generic (it only uses that `star` on `X →ᵇ ℂ` is pointwise
conjugation, together with the abstract characterization of the C⋆-algebra order as the closure of
squares), independently of which measure is integrated. This single construction is the shared
building block behind point states, Gaussian states, and Gibbs states of a classical system.
-/

section ProbState

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

/-- Integration against a probability measure, as a `ℂ`-linear map on `X →ᵇ ℂ`. -/
def integralLM : (X →ᵇ ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f x ∂μ
  map_add' f g := integral_add (f.integrable μ) (g.integrable μ)
  map_smul' c f := by
    show ∫ x, (c • f) x ∂μ = c • ∫ x, f x ∂μ
    simp_rw [smul_apply]
    exact integral_smul c f

@[simp]
lemma integralLM_apply (f : X →ᵇ ℂ) : integralLM μ f = ∫ x, f x ∂μ :=
  rfl

lemma integralLM_nonneg (f : X →ᵇ ℂ) (hf : 0 ≤ f) : 0 ≤ integralLM μ f := by
  rw [StarOrderedRing.nonneg_iff] at hf
  induction hf using AddSubmonoid.closure_induction with
  | mem a ha =>
    obtain ⟨s, rfl⟩ := ha
    have hpt : ∀ x, 0 ≤ (star s * s) x := fun x => by
      rw [mul_apply, star_apply]
      exact star_mul_self_nonneg (s x)
    have hint : Integrable (⇑(star s * s)) μ := (star s * s).integrable μ
    rw [RCLike.nonneg_iff]
    refine ⟨?_, ?_⟩
    · show 0 ≤ RCLike.re (integralLM μ (star s * s))
      rw [integralLM_apply, ← integral_re hint]
      exact integral_nonneg fun x => (hpt x).1
    · show RCLike.im (integralLM μ (star s * s)) = 0
      rw [integralLM_apply, ← integral_im hint]
      have himeq : (fun x => RCLike.im ((star s * s) x)) = fun _ => (0 : ℝ) := by
        funext x; exact (hpt x).2.symm
      rw [himeq, integral_zero]
  | zero => simp [map_zero]
  | add a b _ _ iha ihb => rw [map_add]; exact add_nonneg iha ihb

/-- Integration against a probability measure, as a positive linear map. -/
def integralPLM : (X →ᵇ ℂ) →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (integralLM μ) (integralLM_nonneg μ)

@[simp]
lemma integralPLM_apply (f : X →ᵇ ℂ) : integralPLM μ f = ∫ x, f x ∂μ :=
  rfl

/-- The state of `X →ᵇ ℂ` given by integration against a probability measure. -/
def probState : State (X →ᵇ ℂ) where
  toPositiveLinearMap := integralPLM μ
  map_one := by simp

@[simp]
lemma probState_apply (f : X →ᵇ ℂ) : probState μ f = ∫ x, f x ∂μ :=
  rfl

end ProbState

end BoundedContinuousFunction
