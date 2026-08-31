/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Dynamics.Stinespring.Core

/-!
# Stinespring's construction (part 2 of 3: the canonical GNS representation)

Continuation of `Stinespring/Core.lean`; see `Stinespring.lean` for the full module overview.
This part represents a positive-operator kernel on its completion
(`PositiveOperatorKernelData.Canonical`) and the resulting canonical Stinespring witness.
-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra TensorProduct
open OperatorAlgebra
noncomputable section

namespace OperatorAlgebra


namespace PositiveOperatorKernelData.Canonical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open ContinuousLinearMap

/-! ### The Evans--Lewis cocycle action

For an Evans--Lewis kernel the canonical vectors satisfy a cocycle identity.  The resulting action
is the representation action on the defect space; its bounded extension is developed below. -/

/-- The cocycle identity an Evans--Lewis kernel satisfies: the defining algebraic relation
between the kernel's two shifted forms, needed to build a genuine representation action on the
kernel's GNS space. -/
def HasKernelCocycle
    (K : PositiveOperatorKernelData (A := B(H)) (H := H)) : Prop :=
  ∀ a c d : B(H),
    K.kernel (a * c) d - star c * K.kernel a d =
      K.kernel c (star a * d) - K.kernel c (star a) * d

/-- The kernel vanishes whenever either argument is `1`. -/
def HasKernelZeroOne
    (K : PositiveOperatorKernelData (A := B(H)) (H := H)) : Prop :=
  (∀ b : B(H), K.kernel 1 b = 0) ∧ (∀ a : B(H), K.kernel a 1 = 0)

/-- The candidate representation action of `a : B(H)` on `Pre K`, built from the cocycle
identity. -/
noncomputable def actionPre
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
  (a : B(H)) : Pre K →ₗ[ℂ] Pre K :=
  Finsupp.lsum ℂ (fun c =>
    preEmbedding K (a * c) +
      -((preEmbedding K a).comp (ContinuousLinearMap.toLinearMap c)))

@[simp]
lemma actionPre_single
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (a c : B(H)) (x : H) :
    actionPre K a (Finsupp.single c x) =
      Finsupp.single (a * c) x - Finsupp.single a (c x) := by
  simp [actionPre, preEmbedding, sub_eq_add_neg]

lemma actionPre_mul
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (a b : B(H)) :
    actionPre K (a * b) = (actionPre K a).comp (actionPre K b) := by
  apply LinearMap.ext
  intro z
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp [hz, hw, add_assoc, add_left_comm, add_comm]
  | single c x =>
      simp only [LinearMap.comp_apply, map_sub, actionPre_single]
      simp [sub_eq_add_neg, mul_assoc, mul_apply_eq_comp]

lemma actionPre_inner_single
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (a c d : B(H)) (x y : H) :
    letI : SeminormedAddCommGroup (Pre K) := K.seminormed
    letI : InnerProductSpace ℂ (Pre K) := K.innerProductSpace
    inner ℂ (actionPre K a (Finsupp.single c x)) (Finsupp.single d y) =
      inner ℂ (Finsupp.single c x) (actionPre K (star a) (Finsupp.single d y)) := by
  rw [actionPre_single, actionPre_single]
  change K.kernelInner
      (Finsupp.single (a * c) x - Finsupp.single a (c x)) (Finsupp.single d y) =
    K.kernelInner (Finsupp.single c x)
      (Finsupp.single (star a * d) y - Finsupp.single (star a) (d y))
  simp only [sub_eq_add_neg]
  rw [← neg_one_smul ℂ (Finsupp.single a (c x))]
  rw [← neg_one_smul ℂ (Finsupp.single (star a) (d y))]
  simp only [K.kernelInner_add_left, K.kernelInner_add_right,
    K.kernelInner_smul_left, K.kernelInner_smul_right,
    K.kernelInner_single_single]
  have hcx : inner ℂ (c x) ((K.kernel a d) y) =
      inner ℂ x ((star c * K.kernel a d) y) := by
    simpa [ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp] using
      (ContinuousLinearMap.adjoint_inner_right c x ((K.kernel a d) y)).symm
  rw [hcx]
  simp only [starRingEnd_apply, neg_one_mul]
  have h := congrArg (fun T : B(H) => inner ℂ x (T y)) (hK a c d)
  simpa [sub_apply, inner_sub_right, sub_eq_add_neg] using h

lemma actionPre_inner
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (a : B(H)) (z w : Pre K) :
    letI : SeminormedAddCommGroup (Pre K) := K.seminormed
    letI : InnerProductSpace ℂ (Pre K) := K.innerProductSpace
    inner ℂ (actionPre K a z) w = inner ℂ z (actionPre K (star a) w) := by
  change K.kernelInner (actionPre K a z) w =
    K.kernelInner z (actionPre K (star a) w)
  induction z using Finsupp.induction_linear with
  | zero => simp [PositiveOperatorKernelData.kernelInner]
  | add z z' hz hz' =>
      rw [map_add, K.kernelInner_add_left, K.kernelInner_add_left, hz, hz']
  | single c x =>
      induction w using Finsupp.induction_linear with
      | zero => simp [PositiveOperatorKernelData.kernelInner]
      | add w w' hw hw' =>
          rw [map_add, K.kernelInner_add_right, K.kernelInner_add_right, hw, hw']
      | single d y => exact actionPre_inner_single K hK a c d x y

lemma actionPre_add_parameter_inner_single
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (a b c d : B(H)) (x y : H) :
    K.kernelInner (Finsupp.single c x)
        (actionPre K (a + b) (Finsupp.single d y)) =
      K.kernelInner (Finsupp.single c x)
        ((actionPre K a + actionPre K b) (Finsupp.single d y)) := by
  rw [actionPre_single, LinearMap.add_apply, actionPre_single, actionPre_single]
  change K.kernelInner (Finsupp.single c x)
      (Finsupp.single ((a + b) * d) y - Finsupp.single (a + b) (d y)) =
    K.kernelInner (Finsupp.single c x)
      ((Finsupp.single (a * d) y - Finsupp.single a (d y)) +
        (Finsupp.single (b * d) y - Finsupp.single b (d y)))
  simp only [sub_eq_add_neg]
  rw [← neg_one_smul ℂ (Finsupp.single (a + b) (d y))]
  rw [← neg_one_smul ℂ (Finsupp.single a (d y))]
  rw [← neg_one_smul ℂ (Finsupp.single b (d y))]
  simp only [K.kernelInner_add_right, K.kernelInner_smul_right,
    K.kernelInner_single_single]
  rw [add_mul]
  rw [K.kernel_add_right c (a * d) (b * d), K.kernel_add_right c a b]
  simp only [ContinuousLinearMap.add_apply, inner_add_right]
  ring

lemma actionPre_add_parameter_inner
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (a b : B(H)) (z w : Pre K) :
    K.kernelInner z (actionPre K (a + b) w) =
      K.kernelInner z ((actionPre K a + actionPre K b) w) := by
  induction z using Finsupp.induction_linear with
  | zero => simp [PositiveOperatorKernelData.kernelInner]
  | add z z' hz hz' =>
      rw [K.kernelInner_add_left, hz, hz', K.kernelInner_add_left]
  | single c x =>
      induction w using Finsupp.induction_linear with
      | zero => simp [PositiveOperatorKernelData.kernelInner]
      | add w w' hw hw' =>
          simp only [LinearMap.add_apply, map_add, K.kernelInner_add_right, hw, hw']
      | single d y => exact actionPre_add_parameter_inner_single K a b c d x y

lemma actionPre_smul_parameter_inner_single
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (r : ℂ) (a c d : B(H)) (x y : H) :
    K.kernelInner (Finsupp.single c x)
        (actionPre K (r • a) (Finsupp.single d y)) =
      K.kernelInner (Finsupp.single c x)
        (r • actionPre K a (Finsupp.single d y)) := by
  rw [actionPre_single, actionPre_single]
  change K.kernelInner (Finsupp.single c x)
      (Finsupp.single ((r • a) * d) y - Finsupp.single (r • a) (d y)) =
    K.kernelInner (Finsupp.single c x)
      (r • (Finsupp.single (a * d) y - Finsupp.single a (d y)))
  rw [smul_mul_assoc]
  simp only [sub_eq_add_neg]
  rw [← neg_one_smul ℂ (Finsupp.single (r • a) (d y))]
  rw [← neg_one_smul ℂ (Finsupp.single a (d y))]
  simp only [K.kernelInner_add_right, K.kernelInner_smul_right,
    K.kernelInner_single_single, smul_eq_mul]
  rw [K.kernel_smul_right r c (a * d), K.kernel_smul_right r c a]
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right, smul_eq_mul]
  ring

lemma actionPre_smul_parameter_inner
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (r : ℂ) (a : B(H)) (z w : Pre K) :
    K.kernelInner z (actionPre K (r • a) w) =
      K.kernelInner z (r • actionPre K a w) := by
  induction z using Finsupp.induction_linear with
  | zero => simp [PositiveOperatorKernelData.kernelInner]
  | add z z' hz hz' =>
      rw [K.kernelInner_add_left, hz, hz', K.kernelInner_add_left]
  | single c x =>
      induction w using Finsupp.induction_linear with
      | zero => simp [PositiveOperatorKernelData.kernelInner]
      | add w w' hw hw' =>
          rw [map_add, K.kernelInner_add_right, hw, hw']
          rw [map_add, smul_add, K.kernelInner_add_right]
      | single d y => exact actionPre_smul_parameter_inner_single K r a c d x y

lemma actionPre_one_inner_single
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelZeroOne K) (c d : B(H)) (x y : H) :
    K.kernelInner (Finsupp.single c x)
        (actionPre K 1 (Finsupp.single d y)) =
      K.kernelInner (Finsupp.single c x) (Finsupp.single d y) := by
  rw [actionPre_single]
  change K.kernelInner (Finsupp.single c x)
      (Finsupp.single (1 * d) y - Finsupp.single 1 (d y)) =
    K.kernelInner (Finsupp.single c x) (Finsupp.single d y)
  rw [one_mul]
  simp only [sub_eq_add_neg]
  rw [← neg_one_smul ℂ (Finsupp.single 1 (d y))]
  simp only [K.kernelInner_add_right, K.kernelInner_smul_right,
    K.kernelInner_single_single, neg_one_mul]
  simp only [hK.2 c, map_zero, zero_apply, inner_zero_right, neg_zero, add_zero]

lemma actionPre_one_inner
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelZeroOne K) (z w : Pre K) :
    K.kernelInner z (actionPre K 1 w) = K.kernelInner z w := by
  induction z using Finsupp.induction_linear with
  | zero => simp [PositiveOperatorKernelData.kernelInner]
  | add z z' hz hz' =>
      rw [K.kernelInner_add_left, hz, hz', K.kernelInner_add_left]
  | single c x =>
      induction w using Finsupp.induction_linear with
      | zero => simp [PositiveOperatorKernelData.kernelInner]
      | add w w' hw hw' =>
          rw [map_add, K.kernelInner_add_right, hw, hw',
            K.kernelInner_add_right]
      | single d y => exact actionPre_one_inner_single K hK c d x y

lemma norm_sq_sub_star_mul_nonneg (a : B(H)) :
    0 ≤ (‖a‖ ^ 2 : ℝ) • (1 : B(H)) - star a * a := by
  have hle : star a * a ≤ algebraMap ℝ (B(H)) ‖star a * a‖ := by
    exact (CStarAlgebra.norm_le_iff_le_algebraMap (star a * a)
      (norm_nonneg _)).mp le_rfl
  rw [CStarRing.norm_star_mul_self] at hle
  simpa [sq, Algebra.algebraMap_eq_smul_one] using (sub_nonneg.mpr hle)

lemma actionPre_add_parameter_inner_left
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (a b : B(H)) (z w : Pre K) :
    K.kernelInner (actionPre K (a + b) z) w =
      K.kernelInner ((actionPre K a + actionPre K b) z) w := by
  calc
    K.kernelInner (actionPre K (a + b) z) w =
        starRingEnd ℂ (K.kernelInner w (actionPre K (a + b) z)) :=
      (K.kernelInner_conj_symm (actionPre K (a + b) z) w).symm
    _ = starRingEnd ℂ (K.kernelInner w
        ((actionPre K a + actionPre K b) z)) := by
      rw [actionPre_add_parameter_inner K a b w z]
    _ = K.kernelInner ((actionPre K a + actionPre K b) z) w :=
      K.kernelInner_conj_symm _ _

lemma actionPre_smul_parameter_inner_left
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (r : ℂ) (a : B(H)) (z w : Pre K) :
    K.kernelInner (actionPre K (r • a) z) w =
      K.kernelInner (r • actionPre K a z) w := by
  calc
    K.kernelInner (actionPre K (r • a) z) w =
        starRingEnd ℂ (K.kernelInner w (actionPre K (r • a) z)) :=
      (K.kernelInner_conj_symm (actionPre K (r • a) z) w).symm
    _ = starRingEnd ℂ (K.kernelInner w (r • actionPre K a z)) := by
      rw [actionPre_smul_parameter_inner K r a w z]
    _ = K.kernelInner (r • actionPre K a z) w :=
      K.kernelInner_conj_symm _ _

lemma actionPre_one_inner_left
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelZeroOne K) (z w : Pre K) :
    K.kernelInner (actionPre K 1 z) w = K.kernelInner z w := by
  calc
    K.kernelInner (actionPre K 1 z) w =
        starRingEnd ℂ (K.kernelInner w (actionPre K 1 z)) :=
      (K.kernelInner_conj_symm (actionPre K 1 z) w).symm
    _ = starRingEnd ℂ (K.kernelInner w z) := by
      rw [actionPre_one_inner K hK]
    _ = K.kernelInner z w := K.kernelInner_conj_symm _ _

lemma kernelInner_eq_inner
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (z w : Pre K) : inner ℂ z w = K.kernelInner z w := rfl

lemma actionPre_quadratic_nonneg
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) {q : B(H)} (hq : 0 ≤ q) (z : Pre K) :
    0 ≤ Complex.re (K.kernelInner (actionPre K q z) z) := by
  let s : B(H) := CFC.sqrt q
  have hs : star s = s := by
    dsimp [s]
    exact (CFC.sqrt_nonneg q).isSelfAdjoint.star_eq
  have hsq : star s * s = q := by
    dsimp [s]
    rw [(CFC.sqrt_nonneg q).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self q hq
  have hinner : inner ℂ (actionPre K q z) z =
      inner ℂ (actionPre K s z) (actionPre K s z) := by
    rw [← hsq, actionPre_mul]
    have h := actionPre_inner K hK (star s) (actionPre K s z) z
    simpa only [LinearMap.comp_apply, star_star] using h
  change 0 ≤ Complex.re (inner ℂ (actionPre K q z) z)
  rw [hinner]
  exact inner_self_nonneg (𝕜 := ℂ) (E := Pre K) (x := actionPre K s z)

lemma actionPre_norm_le
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K)
    (a : B(H)) (z : Pre K) :
    ‖actionPre K a z‖ ≤ ‖a‖ * ‖z‖ := by
  let q : B(H) := (‖a‖ ^ 2 : ℝ) • (1 : B(H)) - star a * a
  have hq : 0 ≤ q := by
    exact norm_sq_sub_star_mul_nonneg a
  have hpos := actionPre_quadratic_nonneg K hK hq z
  have hqscalar : (‖a‖ ^ 2 : ℝ) • (1 : B(H)) =
      (‖a‖ ^ 2 : ℂ) • (1 : B(H)) := by
    simp [Algebra.smul_def, IsScalarTower.algebraMap_apply ℝ ℂ (B(H))]
  have hqform : K.kernelInner (actionPre K q z) z =
      (‖a‖ ^ 2 : ℂ) * K.kernelInner z z -
        K.kernelInner (actionPre K a z) (actionPre K a z) := by
    change K.kernelInner
      (actionPre K ((‖a‖ ^ 2 : ℝ) • (1 : B(H)) - star a * a) z) z = _
    rw [hqscalar]
    rw [sub_eq_add_neg]
    rw [actionPre_add_parameter_inner_left K ((‖a‖ ^ 2 : ℂ) • (1 : B(H)))
      (-(star a * a)) z z]
    rw [LinearMap.add_apply, K.kernelInner_add_left]
    rw [actionPre_smul_parameter_inner_left K (‖a‖ ^ 2 : ℂ) 1 z z]
    rw [K.kernelInner_smul_left, actionPre_one_inner_left K h1]
    rw [← neg_one_smul ℂ (star a * a)]
    rw [actionPre_smul_parameter_inner_left K (-1 : ℂ) (star a * a) z z]
    rw [K.kernelInner_smul_left]
    rw [actionPre_mul K (star a) a]
    have hinner := actionPre_inner K hK (star a) (actionPre K a z) z
    change K.kernelInner (actionPre K (star a) (actionPre K a z)) z = _ at hinner
    rw [kernelInner_eq_inner] at hinner
    simp only [star_star] at hinner
    rw [show (actionPre K (star a) ∘ₗ actionPre K a) z =
      actionPre K (star a) (actionPre K a z) by rfl]
    rw [hinner]
    rw [show starRingEnd ℂ (‖a‖ ^ 2 : ℂ) = (‖a‖ ^ 2 : ℂ) by simp]
    rw [show starRingEnd ℂ (-1 : ℂ) = (-1 : ℂ) by norm_num]
    ring
  rw [hqform] at hpos
  have hreal := (RCLike.nonneg_iff.mp hpos).1
  have hselfz : Complex.re (K.kernelInner z z) = ‖z‖ ^ 2 := by
    have hnorm :=
      (InnerProductSpace.Core.inner_self_eq_norm_mul_norm
        (c := K.core) z)
    change Complex.re (K.kernelInner z z) = ‖z‖ * ‖z‖ at hnorm
    rw [pow_two]
    exact hnorm
  have hselfa : Complex.re
      (K.kernelInner (actionPre K a z) (actionPre K a z)) =
        ‖actionPre K a z‖ ^ 2 := by
    have hnorm :=
      (InnerProductSpace.Core.inner_self_eq_norm_mul_norm
        (c := K.core) (actionPre K a z))
    change Complex.re
        (K.kernelInner (actionPre K a z) (actionPre K a z)) =
      ‖actionPre K a z‖ * ‖actionPre K a z‖ at hnorm
    rw [pow_two]
    exact hnorm
  simp [Complex.mul_re, hselfz, hselfa] at hreal
  simp [pow_two, Complex.mul_re, Complex.mul_im] at hreal
  have hreal' : ‖actionPre K a z‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖z‖ ^ 2 := by
    simpa only [zero_mul, sub_zero, pow_two, mul_assoc] using hreal
  have hax : 0 ≤ ‖a‖ * ‖z‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [hreal']

/-- `actionPre a`, bundled as a continuous linear map (its norm is controlled given the
cocycle and zero-one hypotheses). -/
noncomputable def actionPreCLM
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K) (a : B(H)) :
    Pre K →L[ℂ] Pre K :=
  (actionPre K a).mkContinuous ‖a‖ (actionPre_norm_le K hK h1 a)

@[simp]
lemma actionPreCLM_apply
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K)
    (a : B(H)) (z : Pre K) :
    actionPreCLM K hK h1 a z = actionPre K a z := rfl

/-- The continuous extension of `actionPreCLM` to the completion. -/
noncomputable def actionCompletion
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K) (a : B(H)) :
    Completion K →L[ℂ] Completion K := by
  letI : SeminormedAddCommGroup (Pre K) := K.seminormed
  letI : InnerProductSpace ℂ (Pre K) := K.innerProductSpace
  letI : IsBoundedSMul ℂ (Pre K) := NormSMulClass.toIsBoundedSMul
  letI : UniformContinuousConstSMul ℂ (Pre K) :=
    IsBoundedSMul.toUniformContinuousConstSMul
  exact (actionPreCLM K hK h1 a).completion

@[simp]
lemma actionCompletion_apply_coe
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K)
    (a : B(H)) (z : Pre K) :
    actionCompletion K hK h1 a z = actionPre K a z := by
  change (actionPreCLM K hK h1 a).completion z = actionPre K a z
  rw [ContinuousLinearMap.completion_apply_coe, actionPreCLM_apply]

lemma actionCompletion_ext
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    {f g : Completion K →L[ℂ] Completion K}
    (h : ∀ z : Pre K, f z = g z) : f = g := by
  apply ContinuousLinearMap.ext
  intro z
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq f.continuous g.continuous) ?_
  intro z
  exact h z

lemma actionCompletion_mul
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K)
    (a b : B(H)) :
    actionCompletion K hK h1 (a * b) =
      (actionCompletion K hK h1 a).comp (actionCompletion K hK h1 b) := by
  apply actionCompletion_ext K
  intro z
  change (actionCompletion K hK h1 (a * b)) (z : Completion K) =
    actionCompletion K hK h1 a
      (actionCompletion K hK h1 b (z : Completion K))
  rw [actionCompletion_apply_coe K hK h1 (a * b) z]
  rw [actionCompletion_apply_coe K hK h1 b z]
  rw [actionCompletion_apply_coe K hK h1 a (actionPre K b z)]
  rw [actionPre_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma actionCompletion_star
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K)
    (a : B(H)) :
    actionCompletion K hK h1 (star a) =
      (actionCompletion K hK h1 a).adjoint := by
  refine (eq_adjoint_iff (actionCompletion K hK h1 (star a))
    (actionCompletion K hK h1 a)).mpr ?_
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
      have h := actionPre_inner K hK (star a) x y
      change K.kernelInner (actionPre K (star a) x) y = _ at h
      rw [actionCompletion_apply_coe K hK h1 (star a) x,
        UniformSpace.Completion.inner_coe,
        actionCompletion_apply_coe K hK h1 a y,
        UniformSpace.Completion.inner_coe]
      simpa [kernelInner_eq_inner, star_star] using h

lemma actionPre_one_coe_eq
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (h1 : HasKernelZeroOne K) (z : Pre K) :
    (actionPre K 1 z : Completion K) = (z : Completion K) := by
  letI : SeminormedAddCommGroup (Pre K) := K.seminormed
  letI : InnerProductSpace ℂ (Pre K) := K.innerProductSpace
  let T : Pre K := actionPre K 1 z
  have hzero : K.kernelInner (T - z) (T - z) = 0 := by
    change K.kernelInner ((actionPre K 1 z) - z) ((actionPre K 1 z) - z) = 0
    rw [sub_eq_add_neg, ← neg_one_smul ℂ z, K.kernelInner_add_left,
      K.kernelInner_smul_left]
    rw [actionPre_one_inner_left K h1 z ((actionPre K 1 z) + -1 • z)]
    simp [starRingEnd_apply]
  rw [← sub_eq_zero]
  apply norm_eq_zero.mp
  rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]
  have hnorm : ‖T - z‖ ^ 2 = 0 := by
    rw [@norm_sq_eq_re_inner ℂ (Pre K) _ _]
    change Complex.re (K.kernelInner (T - z) (T - z)) = 0
    rw [hzero]
    rfl
  exact (sq_eq_zero_iff.mp hnorm)

lemma actionPre_add_coe_eq
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (a b : B(H)) (z : Pre K) :
    (actionPre K (a + b) z : Completion K) =
      ((actionPre K a + actionPre K b) z : Completion K) := by
  letI : SeminormedAddCommGroup (Pre K) := K.seminormed
  letI : InnerProductSpace ℂ (Pre K) := K.innerProductSpace
  let T : Pre K := actionPre K (a + b) z
  let U : Pre K := (actionPre K a + actionPre K b) z
  have hzero : K.kernelInner (T - U) (T - U) = 0 := by
    change K.kernelInner
      (actionPre K (a + b) z - (actionPre K a + actionPre K b) z)
      (actionPre K (a + b) z - (actionPre K a + actionPre K b) z) = 0
    rw [sub_eq_add_neg, ← neg_one_smul ℂ ((actionPre K a + actionPre K b) z),
      K.kernelInner_add_left, K.kernelInner_smul_left]
    rw [actionPre_add_parameter_inner_left K a b z
      ((actionPre K (a + b) z) + -1 • ((actionPre K a + actionPre K b) z))]
    simp [starRingEnd_apply]
  rw [← sub_eq_zero]
  apply norm_eq_zero.mp
  rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]
  have hnorm : ‖T - U‖ ^ 2 = 0 := by
    rw [@norm_sq_eq_re_inner ℂ (Pre K) _ _]
    change Complex.re (K.kernelInner (T - U) (T - U)) = 0
    rw [hzero]
    rfl
  exact (sq_eq_zero_iff.mp hnorm)

lemma actionCompletion_add
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K)
    (a b : B(H)) :
    actionCompletion K hK h1 (a + b) =
      actionCompletion K hK h1 a + actionCompletion K hK h1 b := by
  apply actionCompletion_ext K
  intro z
  change actionCompletion K hK h1 (a + b) (z : Completion K) =
    (actionCompletion K hK h1 a + actionCompletion K hK h1 b) (z : Completion K)
  rw [actionCompletion_apply_coe K hK h1 (a + b) z]
  rw [ContinuousLinearMap.add_apply,
    actionCompletion_apply_coe K hK h1 a z,
    actionCompletion_apply_coe K hK h1 b z]
  rw [← UniformSpace.Completion.coe_add]
  exact actionPre_add_coe_eq K a b z

lemma actionPre_smul_coe_eq
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (r : ℂ) (a : B(H)) (z : Pre K) :
    (actionPre K (r • a) z : Completion K) =
      (r • actionPre K a z : Completion K) := by
  letI : SeminormedAddCommGroup (Pre K) := K.seminormed
  letI : InnerProductSpace ℂ (Pre K) := K.innerProductSpace
  let T : Pre K := actionPre K (r • a) z
  let U : Pre K := r • actionPre K a z
  have hzero : K.kernelInner (T - U) (T - U) = 0 := by
    change K.kernelInner
      (actionPre K (r • a) z - r • actionPre K a z)
      (actionPre K (r • a) z - r • actionPre K a z) = 0
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (r • actionPre K a z),
      K.kernelInner_add_left, K.kernelInner_smul_left]
    rw [actionPre_smul_parameter_inner_left K r a z
      ((actionPre K (r • a) z) + -1 • (r • actionPre K a z))]
    simp [starRingEnd_apply]
  rw [← sub_eq_zero]
  apply norm_eq_zero.mp
  rw [← UniformSpace.Completion.coe_smul]
  rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]
  have hnorm : ‖T - U‖ ^ 2 = 0 := by
    rw [@norm_sq_eq_re_inner ℂ (Pre K) _ _]
    change Complex.re (K.kernelInner (T - U) (T - U)) = 0
    rw [hzero]
    rfl
  exact (sq_eq_zero_iff.mp hnorm)

lemma actionCompletion_smul
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K)
    (r : ℂ) (a : B(H)) :
    actionCompletion K hK h1 (r • a) =
      r • actionCompletion K hK h1 a := by
  apply actionCompletion_ext K
  intro z
  change actionCompletion K hK h1 (r • a) (z : Completion K) =
    (r • actionCompletion K hK h1 a) (z : Completion K)
  rw [actionCompletion_apply_coe K hK h1 (r • a) z,
    ContinuousLinearMap.smul_apply,
    actionCompletion_apply_coe K hK h1 a z]
  exact actionPre_smul_coe_eq K r a z

lemma actionCompletion_one
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K) :
    actionCompletion K hK h1 1 = ContinuousLinearMap.id ℂ (Completion K) := by
  apply actionCompletion_ext K
  intro z
  rw [actionCompletion_apply_coe K hK h1 1 z]
  exact actionPre_one_coe_eq K h1 z

/-- The unital star representation carried by the Evans--Lewis defect completion. -/
structure CompletionAction
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K) where
  /-- The underlying map `B(H) → Completion K →L[ℂ] Completion K`. -/
  map : B(H) → Completion K →L[ℂ] Completion K
  map_add : ∀ a b, map (a + b) = map a + map b
  map_smul : ∀ (r : ℂ) (a : B(H)), map (r • a) = r • map a
  map_mul : ∀ a b, map (a * b) = (map a).comp (map b)
  map_star : ∀ a, map (star a) = (map a).adjoint
  map_one : map 1 = ContinuousLinearMap.id ℂ (Completion K)

/-- The unital star representation `actionCompletion` packaged as a `CompletionAction`. -/
noncomputable def completionAction
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K) :
    CompletionAction K hK h1 where
  map := actionCompletion K hK h1
  map_add := actionCompletion_add K hK h1
  map_smul := actionCompletion_smul K hK h1
  map_mul := actionCompletion_mul K hK h1
  map_star := actionCompletion_star K hK h1
  map_one := actionCompletion_one K hK h1

/-- Turn the packaged completion action into Mathlib's unital star-algebra homomorphism. -/
def CompletionAction.representation
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K)
    (A : CompletionAction K hK h1) : Representation (B(H)) (Completion K) := by
  set_option backward.isDefEq.respectTransparency false in
  exact {
    toFun := A.map
    map_one' := A.map_one
    map_mul' := A.map_mul
    map_zero' := by
      have h := A.map_add (0 : B(H)) 0
      have h' := congrArg (fun x => x - A.map 0) h
      simpa using h'.symm
    map_add' := A.map_add
    commutes' := by
      intro r
      change A.map ((algebraMap ℂ (B(H))) r) = algebraMap ℂ (B(Completion K)) r
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        A.map_smul, A.map_one]
      rfl
    map_star' := by
      intro a
      change A.map (star a) = (A.map a).adjoint
      exact A.map_star a }

set_option backward.isDefEq.respectTransparency false in
lemma actionCompletion_embedding_cocycle
    (K : PositiveOperatorKernelData (A := B(H)) (H := H))
    (hK : HasKernelCocycle K) (h1 : HasKernelZeroOne K)
    (a b : B(H)) :
    (actionCompletion K hK h1 a).comp (embedding K b) =
      embedding K (a * b) - (embedding K a).comp b := by
  apply ContinuousLinearMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply]
  rw [embedding_apply]
  rw [actionCompletion_apply_coe K hK h1 a (preEmbedding K b x)]
  rw [preEmbedding_apply]
  rw [actionPre_single]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    embedding_apply, embedding_apply]
  rw [← UniformSpace.Completion.coe_sub, preEmbedding_apply, preEmbedding_apply]

end PositiveOperatorKernelData.Canonical

namespace StinespringWitness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! The canonical Kolmogorov factorisation of the Evans--Lewis kernel.  This is deliberately
representation-free: it packages exactly what conditional complete positivity gives before one
asks for the extra multiplicative structure required by a Christensen--Evans jump map. -/

/-- The Evans--Lewis kernel of a generator `L`, packaged as `PositiveOperatorKernelData`. -/
noncomputable def evansLewisKernelData
    (L : B(H) →L[ℂ] B(H))
    (hstar : ∀ a : B(H), star (L a) = L (star a))
    (hpositive : IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b)) :
    PositiveOperatorKernelData (A := B(H)) (H := H) where
  kernel := fun a b => evansLewisKernel L a b
  isPositive := hpositive
  kernel_star := by
    intro a b
    exact evansLewisKernel_star L hstar a b
  kernel_add_left := by
    intro a b c
    simp [evansLewisKernel, star_add, add_mul, mul_add, map_add]
    noncomm_ring
  kernel_smul_left := by
    intro r a b
    simp [evansLewisKernel, star_smul, map_smul, smul_mul_assoc, mul_smul_comm]
    module
  kernel_add_right := by
    intro a b c
    simp [evansLewisKernel, add_mul, mul_add, map_add]
    noncomm_ring
  kernel_smul_right := by
    intro r a b
    simp [evansLewisKernel, map_smul, smul_mul_assoc, mul_smul_comm]
    module

lemma evansLewisKernelData_hasKernelZeroOne
    (L : B(H) →L[ℂ] B(H))
    (hstar : ∀ a : B(H), star (L a) = L (star a))
    (hpositive : IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b)) :
    PositiveOperatorKernelData.Canonical.HasKernelZeroOne
      (evansLewisKernelData L hstar hpositive) := by
  constructor
  · intro b
    exact evansLewisKernel_apply_one_left L b
  · intro a
    exact evansLewisKernel_apply_one_right L a

lemma evansLewisKernelData_kernel
    (L : B(H) →L[ℂ] B(H))
    (hstar : ∀ a : B(H), star (L a) = L (star a))
    (hpositive : IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b))
    (a b : B(H)) :
    (evansLewisKernelData L hstar hpositive).kernel a b = evansLewisKernel L a b := rfl

lemma evansLewisKernelData_hasKernelCocycle
    (L : B(H) →L[ℂ] B(H))
    (hstar : ∀ a : B(H), star (L a) = L (star a))
    (hpositive : IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b)) :
    PositiveOperatorKernelData.Canonical.HasKernelCocycle
      (evansLewisKernelData L hstar hpositive) := by
  intro a c d
  change evansLewisKernel L (a * c) d - star c * evansLewisKernel L a d =
    evansLewisKernel L c (star a * d) - evansLewisKernel L c (star a) * d
  simp [evansLewisKernel, star_mul, mul_assoc, mul_left_comm, mul_comm]
  noncomm_ring

/-- The completion of the Evans--Lewis kernel's `Pre` space: its GNS Hilbert space. -/
abbrev EvansLewisKernelHilbert
    (L : B(H) →L[ℂ] B(H))
    (hstar : ∀ a : B(H), star (L a) = L (star a))
    (hpositive : IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b)) :=
  PositiveOperatorKernelData.Canonical.Completion
    (evansLewisKernelData L hstar hpositive)

/-- The canonical embedding of `H` into `EvansLewisKernelHilbert`. -/
noncomputable def evansLewisKernelEmbedding
    (L : B(H) →L[ℂ] B(H))
    (hstar : ∀ a : B(H), star (L a) = L (star a))
    (hpositive : IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b))
    (a : B(H)) : H →L[ℂ] EvansLewisKernelHilbert L hstar hpositive :=
  PositiveOperatorKernelData.Canonical.embedding
    (evansLewisKernelData L hstar hpositive) a

lemma evansLewisKernelEmbedding_inner
    (L : B(H) →L[ℂ] B(H))
    (hstar : ∀ a : B(H), star (L a) = L (star a))
    (hpositive : IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b))
    (a b : B(H)) (x y : H) :
    inner ℂ (evansLewisKernelEmbedding L hstar hpositive a x)
        (evansLewisKernelEmbedding L hstar hpositive b y) =
      inner ℂ x (evansLewisKernel L a b y) := by
  exact PositiveOperatorKernelData.Canonical.embedding_inner
    (evansLewisKernelData L hstar hpositive) a b x y

lemma evansLewisKernel_norm_le
    (L : B(H) →L[ℂ] B(H)) (hL1 : L 1 = 0)
    (a b : B(H)) :
    ‖evansLewisKernel L a b‖ ≤ 3 * ‖L‖ * ‖a‖ * ‖b‖ := by
  rw [evansLewisKernel, hL1]
  simp only [mul_zero, zero_mul, add_zero, sub_zero]
  have h₁ : ‖L (star a * b)‖ ≤ ‖L‖ * (‖a‖ * ‖b‖) := by
    calc
      ‖L (star a * b)‖ ≤ ‖L‖ * ‖star a * b‖ :=
        ContinuousLinearMap.le_opNorm L _
      _ ≤ ‖L‖ * (‖a‖ * ‖b‖) := by
        gcongr
        calc
          ‖star a * b‖ ≤ ‖star a‖ * ‖b‖ := norm_mul_le _ _
          _ = ‖a‖ * ‖b‖ := by rw [norm_star]
  have h₂ : ‖L (star a) * b‖ ≤ (‖L‖ * ‖a‖) * ‖b‖ := by
    calc
      ‖L (star a) * b‖ ≤ ‖L (star a)‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ (‖L‖ * ‖a‖) * ‖b‖ := by
        gcongr
        simpa only [norm_star] using ContinuousLinearMap.le_opNorm L (star a)
  have h₃ : ‖star a * L b‖ ≤ ‖a‖ * (‖L‖ * ‖b‖) := by
    calc
      ‖star a * L b‖ ≤ ‖star a‖ * ‖L b‖ := norm_mul_le _ _
      _ ≤ ‖a‖ * (‖L‖ * ‖b‖) := by
        gcongr
        · rw [norm_star]
        · exact ContinuousLinearMap.le_opNorm L b
  calc
    ‖L (star a * b) - L (star a) * b - star a * L b‖ ≤
        (‖L (star a * b)‖ + ‖L (star a) * b‖) + ‖star a * L b‖ := by
      calc
        ‖L (star a * b) - L (star a) * b - star a * L b‖ ≤
            ‖L (star a * b) - L (star a) * b‖ + ‖star a * L b‖ :=
          norm_sub_le _ _
        _ ≤ (‖L (star a * b)‖ + ‖L (star a) * b‖) + ‖star a * L b‖ := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ (‖L‖ * (‖a‖ * ‖b‖) + (‖L‖ * ‖a‖) * ‖b‖) +
        ‖a‖ * (‖L‖ * ‖b‖) := by
      exact add_le_add (add_le_add h₁ h₂) h₃
    _ = 3 * ‖L‖ * ‖a‖ * ‖b‖ := by ring

set_option maxHeartbeats 800000 in
lemma exists_evansLewis_kernel_implementer
    [Nontrivial H]
    (L : B(H) →L[ℂ] B(H)) (hL1 : L 1 = 0)
    (hstar : ∀ a : B(H), star (L a) = L (star a))
    (hpositive : IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b)) :
    ∃ V : H →L[ℂ] EvansLewisKernelHilbert L hstar hpositive,
      ∀ (a : B(H)) (x : H),
        evansLewisKernelEmbedding L hstar hpositive a x =
          PositiveOperatorKernelData.Canonical.actionCompletion
            (evansLewisKernelData L hstar hpositive)
            (evansLewisKernelData_hasKernelCocycle L hstar hpositive)
            (evansLewisKernelData_hasKernelZeroOne L hstar hpositive) a (V x) -
            V (a x) := by
  let K := evansLewisKernelData L hstar hpositive
  let hK := evansLewisKernelData_hasKernelCocycle L hstar hpositive
  let h1 := evansLewisKernelData_hasKernelZeroOne L hstar hpositive
  let e₀ : H := Classical.choose (exists_ne (0 : H))
  have he₀ : e₀ ≠ 0 := Classical.choose_spec (exists_ne (0 : H))
  let e : H := ‖e₀‖⁻¹ • e₀
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, norm_inv]
    simp [norm_ne_zero_iff.mpr he₀]
  let R : H →ₗ[ℂ] B(H) :=
    { toFun := fun x => InnerProductSpace.rankOne ℂ x e
      map_add' := by
        intro x y
        ext z
        simp [InnerProductSpace.rankOne_apply, add_smul]
      map_smul' := by
        intro r x
        ext z
        simp [InnerProductSpace.rankOne_apply, smul_smul] }
  have hRnorm (x : H) : ‖R x‖ = ‖x‖ := by
    change ‖InnerProductSpace.rankOne ℂ x e‖ = ‖x‖
    rw [InnerProductSpace.norm_rankOne, he]
    ring
  let Vlin : H →ₗ[ℂ] PositiveOperatorKernelData.Canonical.Completion K :=
    { toFun := fun x => -PositiveOperatorKernelData.Canonical.embedding K (R x) e
      map_add' := by
        intro x y
        have hR : R (x + y) = R x + R y := R.map_add x y
        rw [hR, PositiveOperatorKernelData.Canonical.embedding_add_apply]
        abel
      map_smul' := by
        intro r x
        have hR : R (r • x) = r • R x := R.map_smul r x
        rw [hR, PositiveOperatorKernelData.Canonical.embedding_smul_apply]
        simp }
  have hVbound (x : H) : ‖Vlin x‖ ≤ Real.sqrt (3 * ‖L‖) * ‖x‖ := by
    calc
      ‖Vlin x‖ = ‖PositiveOperatorKernelData.Canonical.embedding K (R x) e‖ := by
        change ‖-(PositiveOperatorKernelData.Canonical.embedding K (R x) e)‖ = _
        exact norm_neg _
      _ = ‖PositiveOperatorKernelData.Canonical.preEmbedding K (R x) e‖ := by
        rw [PositiveOperatorKernelData.Canonical.embedding_apply,
          UniformSpace.Completion.norm_coe]
      _ ≤ Real.sqrt ‖K.kernel (R x) (R x)‖ * ‖e‖ :=
        PositiveOperatorKernelData.Canonical.preEmbedding_norm_le K (R x) e
      _ ≤ Real.sqrt (3 * ‖L‖ * ‖x‖ * ‖x‖) := by
        rw [he]
        have hk : ‖K.kernel (R x) (R x)‖ ≤
            3 * ‖L‖ * ‖x‖ * ‖x‖ := by
          change ‖evansLewisKernel L (R x) (R x)‖ ≤ _
          simpa [hRnorm] using evansLewisKernel_norm_le L hL1 (R x) (R x)
        simpa using Real.sqrt_le_sqrt hk
      _ = Real.sqrt (3 * ‖L‖) * ‖x‖ := by
        rw [show 3 * ‖L‖ * ‖x‖ * ‖x‖ =
            (3 * ‖L‖) * (‖x‖ ^ 2) by ring]
        rw [Real.sqrt_mul (by positivity : 0 ≤ 3 * ‖L‖)]
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
  let V : H →L[ℂ] PositiveOperatorKernelData.Canonical.Completion K :=
    Vlin.mkContinuous (Real.sqrt (3 * ‖L‖)) hVbound
  have hV_apply (x : H) : V x = Vlin x := rfl
  refine ⟨V, ?_⟩
  intro a x
  let r : B(H) := InnerProductSpace.rankOne ℂ x e
  have hra : a * r = InnerProductSpace.rankOne ℂ (a x) e := by
    ext z
    simp [r, mul_apply_eq_comp, InnerProductSpace.rankOne_apply]
  have hre : r e = x := by
    simp [r, InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, he]
  have hcocycle :=
    PositiveOperatorKernelData.Canonical.actionCompletion_embedding_cocycle K hK h1 a r
  have hcocycle' := congrArg (fun f : H →L[ℂ]
      PositiveOperatorKernelData.Canonical.Completion K => f e) hcocycle
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply] at hcocycle'
  rw [hra, hre] at hcocycle'
  rw [hV_apply x, hV_apply (a x)]
  change PositiveOperatorKernelData.Canonical.embedding K a x =
    PositiveOperatorKernelData.Canonical.actionCompletion K hK h1 a
        (-(PositiveOperatorKernelData.Canonical.embedding K r e)) -
        (-(PositiveOperatorKernelData.Canonical.embedding K
        (InnerProductSpace.rankOne ℂ (a x) e) e))
  simp only [map_neg, sub_neg_eq_add]
  rw [hcocycle']
  abel

end StinespringWitness

namespace CCPMatrix

variable {A : Type*} [OperatorAlgebra A]

/-- The matrix with `a` as its first row and zero elsewhere. -/
def row {n : ℕ} (a : Fin (n + 1) → A) :
    CStarMatrix (Fin (n + 1)) (Fin (n + 1)) A :=
  fun i j => if i = 0 then a j else 0

/-- The matrix with `c` as its first column and zero elsewhere. -/
def column {n : ℕ} (c : Fin (n + 1) → A) :
    CStarMatrix (Fin (n + 1)) (Fin (n + 1)) A :=
  fun i j => if j = 0 then c i else 0

/-- The only possibly nonzero entry of a row-column product is the `(0,0)` entry. -/
lemma row_mul_column_apply (a c : Fin (n + 1) → A) (i j : Fin (n + 1)) :
    (row a * column c) i j = if i = 0 ∧ j = 0 then ∑ k, a k * c k else 0 := by
  change ∑ k, (if i = 0 then a k else 0) * (if j = 0 then c k else 0) = _
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj, Finset.mul_sum]

/-- A vanishing column contraction makes the corresponding row-column product zero. -/
lemma row_mul_column_eq_zero (a c : Fin (n + 1) → A)
    (h : ∑ k, a k * c k = 0) : row a * column c = 0 := by
  ext i j
  rw [row_mul_column_apply]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj, h]

/-- The first diagonal entry of a compressed matrix Gram form is the column quadratic form. -/
lemma column_gram_compression_apply_zero (L : A →L[ℂ] A)
    (a c : Fin (n + 1) → A) :
    (CStarMatrix.conjTranspose (column c) *
      ((CStarMatrix.conjTranspose (row a) * row a).map L) * column c) 0 0 =
      ∑ i, ∑ j, star (c i) * L (star (a i) * a j) * c j := by
  simp only [CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply,
    CStarMatrix.map_apply, row, column]
  simp [Finset.sum_mul, Finset.mul_sum, star_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Matrix CCP tested on a row and a column gives the finite-column compression inequality. -/
lemma ccp_column_compression
    (L : A →L[ℂ] A)
    (hccp : IsConditionallyCompletelyPositiveBounded L)
    {n : ℕ} (a c : Fin (n + 1) → A)
    (hzero : ∑ i, a i * c i = 0)
    (f : CStarMatrix (Fin (n + 1)) (Fin (n + 1)) A →ₚ[ℂ] ℂ) :
    0 ≤ Complex.re (f (CStarMatrix.conjTranspose (column c) *
      ((CStarMatrix.conjTranspose (row a) * row a).map L) * column c)) := by
  exact hccp (n + 1) (row a) (column c)
    (row_mul_column_eq_zero a c hzero) f

end CCPMatrix

end OperatorAlgebra
