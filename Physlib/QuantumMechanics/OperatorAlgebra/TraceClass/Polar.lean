/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.TraceClass
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Polar-decomposition support for trace-class operators

This module starts the missing general trace-ideal construction.  For a bounded operator `T`, its
absolute value `S = |T|` satisfies `‖T x‖ = ‖S x‖`.  The resulting isometry from `range S` to `H`
is extended to the closure of that range.  This is the concrete Hilbert-space construction behind
the polar factor; it is kept separate from `TraceClass.lean` while the public ideal API is being
assembled.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Polar

/-- The absolute value used in the polar construction. -/
noncomputable def absOperator (T : B(H)) : B(H) := CFC.abs T

/-- The closed range subspace of the absolute value. -/
noncomputable def rangeClosure (T : B(H)) : Submodule ℂ H :=
  (LinearMap.range (absOperator T).toLinearMap).topologicalClosure

/-- The absolute value, with codomain restricted to its closed range. -/
noncomputable def absIntoRange (T : B(H)) : H →ₗ[ℂ] rangeClosure T :=
  (absOperator T).toLinearMap.codRestrict (rangeClosure T) (by
    intro x
    exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x))

/-- The inclusion of `range |T|` into its closed range, bundled continuously. -/
noncomputable def rangeInClosure (T : B(H)) :
    (LinearMap.range (absOperator T).toLinearMap) →L[ℂ] rangeClosure T :=
  (LinearMap.range (absOperator T).toLinearMap).subtypeL.codRestrict
    (rangeClosure T) (by
      intro x
      exact Submodule.le_topologicalClosure _ x.property)

lemma rangeInClosure_apply (T : B(H))
    (x : LinearMap.range (absOperator T).toLinearMap) :
    (rangeInClosure T x : H) = x := rfl

lemma denseRange_rangeInClosure (T : B(H)) :
    DenseRange (rangeInClosure T) := by
  rw [denseRange_iff_closure_range]
  ext y
  rw [closure_subtype]
  have hrange :
      (Subtype.val '' Set.range (rangeInClosure T)) =
        (LinearMap.range (absOperator T).toLinearMap : Set H) := by
    ext x
    constructor
    · rintro ⟨z, ⟨y, hy⟩, rfl⟩
      rw [← hy]
      change (y : H) ∈ LinearMap.range (absOperator T).toLinearMap
      exact y.property
    · intro hx
      let y : LinearMap.range (absOperator T).toLinearMap := ⟨x, hx⟩
      refine ⟨⟨x, Submodule.le_topologicalClosure _ hx⟩, ⟨y, ?_⟩, ?_⟩
      · apply Subtype.ext
        rfl
      · rfl
  rw [hrange, ← Submodule.topologicalClosure_coe]
  simp only [Set.mem_univ, iff_true]
  exact y.property

lemma absIntoRange_factor (T : B(H)) (x : H) :
    absIntoRange T x = rangeInClosure T
      ⟨absOperator T x, LinearMap.mem_range_self _ x⟩ := by
  rfl

lemma denseRange_absIntoRange (T : B(H)) :
    DenseRange (absIntoRange T) := by
  let r : H →L[ℂ] (LinearMap.range (absOperator T).toLinearMap) :=
    (absOperator T).toLinearMap.codRestrict
      (LinearMap.range (absOperator T).toLinearMap)
      (fun x => LinearMap.mem_range_self _ x) |>.mkContinuous
        ‖absOperator T‖ (by intro x; exact (absOperator T).le_opNorm x)
  have hr : DenseRange r := by
    apply Function.Surjective.denseRange
    intro y
    rcases y with ⟨y, ⟨x, hx⟩⟩
    refine ⟨x, ?_⟩
    exact Subtype.ext hx
  have hcomp := DenseRange.comp (denseRange_rangeInClosure T) hr
    (rangeInClosure T).continuous
  have heq : (rangeInClosure T ∘ r) = absIntoRange T := by
    funext x
    apply Subtype.ext
    rfl
  rw [← heq]
  exact hcomp

lemma absIntoRange_apply (T : B(H)) (x : H) :
    (absIntoRange T x : H) = absOperator T x := rfl

lemma norm_apply_eq_norm_abs_apply (T : B(H)) (x : H) :
    ‖T x‖ = ‖absOperator T x‖ := by
  have hsq : ‖T x‖ ^ 2 = ‖absOperator T x‖ ^ 2 := by
    have hnormT : ‖T x‖ ^ 2 = (⟪T x, T x⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    have hnormS : ‖absOperator T x‖ ^ 2 =
        (⟪absOperator T x, absOperator T x⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    have hT :
        ⟪T x, T x⟫_ℂ =
          ⟪x, (ContinuousLinearMap.adjoint T) (T x)⟫_ℂ := by
      exact (ContinuousLinearMap.adjoint_inner_right T x (T x)).symm
    have hstar : ContinuousLinearMap.adjoint T = star T :=
      (ContinuousLinearMap.star_eq_adjoint T).symm
    have habs : absOperator T * absOperator T = star T * T := by
      unfold absOperator
      exact CFC.abs_mul_abs T
    have habsSelf : IsSelfAdjoint (absOperator T) :=
      .of_nonneg (CFC.abs_nonneg T)
    rw [hnormT, hnormS]
    calc
      (⟪T x, T x⟫_ℂ).re =
          (⟪x, (star T * T) x⟫_ℂ).re := by
            rw [hT, hstar]
            simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      _ = (⟪x, (absOperator T * absOperator T) x⟫_ℂ).re := by rw [habs]
      _ = (⟪absOperator T x, absOperator T x⟫_ℂ).re := by
        rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
        rw [← ContinuousLinearMap.adjoint_inner_left (absOperator T)
          (absOperator T x) x]
        rw [(ContinuousLinearMap.star_eq_adjoint (absOperator T)).symm.trans habsSelf]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

lemma norm_absIntoRange_apply (T : B(H)) (x : H) :
    ‖absIntoRange T x‖ = ‖absOperator T x‖ := by
  rfl

/-- The closed-range subspace is complete, so it admits the orthogonal projection used to define
the bounded polar factor. -/
noncomputable instance instCompleteSpaceRangeClosure (T : B(H)) :
    CompleteSpace (rangeClosure T) :=
  by
    letI : IsClosed (rangeClosure T : Set H) :=
      Submodule.isClosed_topologicalClosure _
    exact IsClosed.completeSpace_coe

/-- The polar factor on the closed range of `|T|`. -/
noncomputable def polarOnRange (T : B(H)) : rangeClosure T →L[ℂ] H :=
  T.toLinearMap.extendOfNorm (absIntoRange T)

lemma polarOnRange_eq_on_abs (T : B(H)) (x : H) :
    polarOnRange T (absIntoRange T x) = T x := by
  apply LinearMap.extendOfNorm_eq (denseRange_absIntoRange T)
    ⟨1, fun y => by
      rw [one_mul, norm_absIntoRange_apply]
      exact (norm_apply_eq_norm_abs_apply T y).le⟩

lemma polarOnRange_norm_le (T : B(H)) (x : rangeClosure T) :
    ‖polarOnRange T x‖ ≤ ‖x‖ := by
  have hnorm : ∀ y : H, ‖T y‖ ≤ 1 * ‖absIntoRange T y‖ := by
    intro y
    rw [one_mul, norm_absIntoRange_apply]
    exact (norm_apply_eq_norm_abs_apply T y).le
  change ‖T.toLinearMap.extendOfNorm (absIntoRange T) x‖ ≤ ‖x‖
  simpa only [one_mul] using
    (LinearMap.norm_extendOfNorm_apply_le (denseRange_absIntoRange T) 1 hnorm x)

/-- The bounded polar factor, obtained by extending the range isometry by zero on the orthogonal
complement of `closure (range |T|)`. -/
noncomputable def polarFactor (T : B(H)) : B(H) :=
  polarOnRange T ∘L (rangeClosure T).orthogonalProjectionOnto

lemma polarFactor_eq_on_abs (T : B(H)) (x : H) :
    polarFactor T (absOperator T x) = T x := by
  unfold polarFactor
  rw [ContinuousLinearMap.comp_apply]
  have hx : absOperator T x ∈ rangeClosure T :=
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)
  have hp := (rangeClosure T).orthogonalProjectionOnto_mem_subspace_eq_self
    ⟨absOperator T x, hx⟩
  rw [hp]
  exact polarOnRange_eq_on_abs T x

lemma polarFactor_norm_le (T : B(H)) (x : H) :
    ‖polarFactor T x‖ ≤ ‖x‖ := by
  unfold polarFactor
  rw [ContinuousLinearMap.comp_apply]
  calc
    ‖polarOnRange T ((rangeClosure T).orthogonalProjectionOnto x)‖ ≤
        ‖(rangeClosure T).orthogonalProjectionOnto x‖ :=
      polarOnRange_norm_le T _
    _ ≤ ‖x‖ := (rangeClosure T).norm_orthogonalProjectionOnto_apply_le x

lemma polarFactor_opNorm_le (T : B(H)) : ‖polarFactor T‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  simpa only [one_mul] using polarFactor_norm_le T

lemma polarFactor_mul_absOperator (T : B(H)) :
    polarFactor T * absOperator T = T := by
  ext x
  exact polarFactor_eq_on_abs T x

/-! ### The partial-isometry adjoint identity

The remaining fact needed to cross from the positive/self-adjoint trace theory to a genuine
two-sided ideal is that `polarFactor T` is not merely a contraction but an honest partial isometry
on `rangeClosure T`: its adjoint undoes it exactly there.  This is what lets `star (polarFactor T)`
recover `|T|` from `T`, for *every* bounded `T` (no self-adjointness or trace-class hypothesis is
used here). -/

/-- `polarOnRange T` is norm-preserving, not merely a contraction.  The two sides agree on the
dense image of `absIntoRange T` (`polarOnRange_eq_on_abs` plus the defining isometry property of
`absOperator`), so they agree everywhere by continuity. -/
theorem polarOnRange_norm_eq (T : B(H)) (y : rangeClosure T) :
    ‖polarOnRange T y‖ = ‖y‖ := by
  have heq : (fun y : rangeClosure T => ‖polarOnRange T y‖) ∘ (absIntoRange T) =
      (fun y : rangeClosure T => ‖y‖) ∘ (absIntoRange T) := by
    funext x
    show ‖polarOnRange T (absIntoRange T x)‖ = ‖absIntoRange T x‖
    rw [polarOnRange_eq_on_abs, norm_apply_eq_norm_abs_apply, norm_absIntoRange_apply]
  have hres := (denseRange_absIntoRange T).equalizer
    ((polarOnRange T).continuous.norm) continuous_norm heq
  exact congrFun hres y

/-- `polarOnRange T` is a genuine isometry of `rangeClosure T` into `H`: its adjoint is a left
inverse. -/
theorem adjoint_polarOnRange_comp_self (T : B(H)) :
    ContinuousLinearMap.adjoint (polarOnRange T) ∘L polarOnRange T = 1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (polarOnRange T)).mp
    (polarOnRange_norm_eq T)

/-- `star (polarFactor T) * polarFactor T` is exactly the orthogonal projection onto
`rangeClosure T`: composing the isometry `polarOnRange T` with its adjoint on the left cancels to
the identity, leaving only the orthogonal-projection factor from `polarFactor`'s definition. -/
theorem star_polarFactor_mul_polarFactor (T : B(H)) :
    star (polarFactor T) * polarFactor T = (rangeClosure T).starProjection := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  show ContinuousLinearMap.adjoint
      (polarOnRange T ∘L (rangeClosure T).orthogonalProjectionOnto) *
    (polarOnRange T ∘L (rangeClosure T).orthogonalProjectionOnto) =
      (rangeClosure T).starProjection
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (ContinuousLinearMap.adjoint (polarOnRange T)),
    adjoint_polarOnRange_comp_self, ContinuousLinearMap.one_def,
    Submodule.adjoint_orthogonalProjectionOnto]
  simp only [ContinuousLinearMap.id_comp]
  rfl

/-- **The general partial-isometry identity**: `star (polarFactor T) * T = |T|`, for *every*
bounded `T`.  This is the fact that finally lets the trace ideal cross the non-self-adjoint
boundary: conjugating `T` on the left by `star (polarFactor T)` recovers the absolute value
exactly, not merely up to a norm bound. -/
theorem star_polarFactor_mul_self (T : B(H)) :
    star (polarFactor T) * T = absOperator T := by
  have hT : polarFactor T * absOperator T = T := polarFactor_mul_absOperator T
  have hproj : star (polarFactor T) * T =
      (rangeClosure T).starProjection * absOperator T := by
    calc
      star (polarFactor T) * T =
          star (polarFactor T) * (polarFactor T * absOperator T) := by rw [hT]
      _ = (star (polarFactor T) * polarFactor T) * absOperator T := by rw [mul_assoc]
      _ = (rangeClosure T).starProjection * absOperator T := by
        rw [star_polarFactor_mul_polarFactor]
  rw [hproj]
  ext x
  show (rangeClosure T).starProjection (absOperator T x) = absOperator T x
  exact Submodule.starProjection_eq_self_iff.mpr
    (Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x))

end Polar

end OperatorAlgebra
