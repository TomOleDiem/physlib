/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Dynamics.ChristensenEvans
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Analysis.InnerProductSpace.Completion
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.VectorState

/-!
# Stinespring's construction (part 1 of 3: the tensor-product core)

Split out of `Stinespring.lean` to stay under the file-length style limit; see `Stinespring.lean`
for the full module overview. This part builds the canonical positive kernel on `A ⊗ H`, its
seminormed completion, the canonical Stinespring witness, and the `PositiveOperatorKernelData`
GNS/Kolmogorov factorization setup.
-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra TensorProduct
open OperatorAlgebra
noncomputable section

namespace OperatorAlgebra

namespace TensorStinespring

variable {A H : Type*} [OperatorAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The tensor-product carrier `A ⊗[ℂ] H` the whole construction below lives on. -/
@[nolint unusedArguments]
abbrev T (A H : Type*) [OperatorAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] := A ⊗[ℂ] H

/-- The functional `b ⊗ k ↦ ⟪h, J(a⋆b) k⟫`, the building block of the kernel inner product. -/
noncomputable def baseFunctional (J : A →CP B(H)) (a : A) (h : H) :
    T A H →ₗ[ℂ] ℂ :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun b k => inner ℂ h (J (star a * b) k))
    (by intro b₁ b₂ k; simp [mul_add, map_add])
    (by
      intro c b k
      rw [mul_smul_comm, map_smul]
      change inner ℂ h (c • (J (star a * b) k)) = _
      rw [inner_smul_right]
      rfl)
    (by intro b k₁ k₂; simp [map_add])
    (by
      intro c b k
      rw [map_smul]
      rw [inner_smul_right]
      rfl))

@[simp]
lemma baseFunctional_tmul (J : A →CP B(H)) (a b : A) (h k : H) :
    baseFunctional J a h (b ⊗ₜ[ℂ] k) = inner ℂ h (J (star a * b) k) := by
  rfl

/-- `baseFunctional`, packaged as a sesquilinear map in `(a, h)`. -/
noncomputable def sesquiBilinear (J : A →CP B(H)) :
    A →ₛₗ[starRingEnd ℂ] H →ₛₗ[starRingEnd ℂ] (T A H →ₗ[ℂ] ℂ) :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (starRingEnd ℂ)
    (fun a h => baseFunctional J a h)
    (by intro a₁ a₂ h; ext x; simp [baseFunctional, star_add, add_mul, map_add])
    (by intro c a h; ext x; simp [baseFunctional, star_smul, map_smul])
    (by intro a h₁ h₂; ext x; simp [baseFunctional])
    (by intro c a h; ext x; simp [baseFunctional]; ring)

/-- The (possibly degenerate) sesquilinear form on `T A H` induced by lifting `sesquiBilinear`
through the tensor product. -/
noncomputable def tensorInner (J : A →CP B(H)) :
    T A H →ₛₗ[starRingEnd ℂ] (T A H →ₗ[ℂ] ℂ) :=
  TensorProduct.lift (sesquiBilinear J)

@[simp]
lemma tensorInner_tmul (J : A →CP B(H)) (a b : A) (h k : H) :
    tensorInner J (a ⊗ₜ[ℂ] h) (b ⊗ₜ[ℂ] k) =
      inner ℂ h (J (star a * b) k) := by
  rfl

lemma tensorInner_conj_symm_tmul (J : A →CP B(H)) (a b : A) (h k : H) :
    starRingEnd ℂ (tensorInner J (a ⊗ₜ[ℂ] h) (b ⊗ₜ[ℂ] k)) =
      tensorInner J (b ⊗ₜ[ℂ] k) (a ⊗ₜ[ℂ] h) := by
  rw [tensorInner_tmul, tensorInner_tmul]
  rw [inner_conj_symm]
  have hstar : J (star b * a) =
      ContinuousLinearMap.adjoint (J (star a * b)) := by
    calc
      J (star b * a) = J (star (star a * b)) := by
        congr 1
        simp [star_mul]
      _ = star (J (star a * b)) :=
        (OperatorAlgebra.completelyPositiveMap_map_star_general J _).symm
      _ = ContinuousLinearMap.adjoint (J (star a * b)) := by rfl
  rw [hstar]
  exact (ContinuousLinearMap.adjoint_inner_right _ _ _).symm

lemma tensorInner_conj_symm (J : A →CP B(H)) (x y : T A H) :
    starRingEnd ℂ (tensorInner J x y) = tensorInner J y x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a h
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp
    · intro b k
      exact tensorInner_conj_symm_tmul J a b h k
    · intro y z ihy ihz
      simp only [map_add, ihy, ihz]
      rw [LinearMap.add_apply]
  · intro x y ihx ihy
    rw [(tensorInner J).map_add]
    rw [LinearMap.add_apply]
    rw [map_add, ihx, ihy]
    rw [map_add]

lemma tensorInner_nonneg (J : A →CP B(H)) (x : T A H) :
    0 ≤ tensorInner J x x := by
  obtain ⟨n, a, h, rfl⟩ := TensorProduct.exists_sum_tmul_eq x
  let v : PiLp 2 (fun _ : Fin n => H) := WithLp.toLp 2 h
  have hv (i : Fin n) : v.ofLp i = h i := rfl
  have hp := StinespringWitness.cpKernel_inner_nonneg_natural' J a v
  rw [Finset.sum_comm] at hp
  simpa [tensorInner, sesquiBilinear, baseFunctional, v, hv,
    Finset.sum_apply, inner_sum, sum_inner] using hp

/-- `tensorInner`, packaged as a `PreInnerProductSpace.Core` on `T A H`. -/
noncomputable def tensorCore (J : A →CP B(H)) :
    PreInnerProductSpace.Core ℂ (T A H) where
  inner := fun x y => tensorInner J x y
  conj_inner_symm := by
    intro x y
    exact tensorInner_conj_symm J y x
  re_inner_nonneg := by
    intro x
    exact (tensorInner_nonneg J x).1
  add_left := by
    intro x y z
    exact congrArg (fun f => f z) ((tensorInner J).map_add x y)
  smul_left := by
    intro x y r
    have hs := congrArg (fun f : T A H →ₗ[ℂ] ℂ => f y)
      ((tensorInner J).map_smulₛₗ r x)
    simpa [smul_eq_mul] using hs

/-- Left multiplication by `a` on the algebra factor of `T A H`. -/
noncomputable def leftMul (a : A) : T A H →ₗ[ℂ] T A H :=
  TensorProduct.map (LinearMap.mulLeft ℂ a) (LinearMap.id)

@[simp]
lemma leftMul_tmul (a b : A) (h : H) :
    leftMul a (b ⊗ₜ[ℂ] h) = (a * b) ⊗ₜ[ℂ] h := by
  simp [leftMul]

lemma tensorInner_leftMul (J : A →CP B(H)) (a : A) (x y : T A H) :
    tensorInner J (leftMul a x) y = tensorInner J x (leftMul (star a) y) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro b h
    refine TensorProduct.induction_on y ?_ ?_ ?_
    · simp
    · intro c k
      simp [leftMul, star_mul, mul_assoc]
    · intro y z ihy ihz
      simp only [map_add, ihy, ihz]
  · intro x z ihx ihz
    rw [(leftMul a).map_add, (tensorInner J).map_add]
    simp only [LinearMap.add_apply, map_add, ihx, ihz]

lemma leftMul_mul (a b : A) (x : T A H) :
    leftMul (a * b) x = leftMul a (leftMul b x) := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro c h
    simp [leftMul]
  · intro x y ihx ihy
    simp only [map_add, ihx, ihy]

lemma leftMul_add (a b : A) (x : T A H) :
    leftMul (a + b) x = leftMul a x + leftMul b x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro c h
    simp [leftMul, add_mul, TensorProduct.add_tmul]
  · intro x y ihx ihy
    rw [(leftMul (a + b)).map_add, (leftMul a).map_add, (leftMul b).map_add,
      ihx, ihy]
    abel

lemma leftMul_smul (r : ℂ) (a : A) (x : T A H) :
    leftMul (r • a) x = r • leftMul a x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro b h
    rw [leftMul_tmul, leftMul_tmul]
    rw [smul_mul_assoc]
    rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  · intro x y ihx ihy
    rw [(leftMul (r • a)).map_add, (leftMul a).map_add, ihx, ihy, smul_add]

lemma leftMul_one (x : T A H) : leftMul (1 : A) x = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro a h
    simp [leftMul]
  · intro x y ihx ihy
    simp only [map_add, ihx, ihy]

lemma leftMul_norm_sub (a : A) (x : T A H) :
    leftMul ((‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a) x =
      (‖a‖ ^ 2 : ℂ) • x - leftMul (star a * a) x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro b h
    simp [leftMul, Algebra.smul_def, sub_mul, TensorProduct.sub_tmul]
    simp [Algebra.smul_def, TensorProduct.smul_tmul']
    rw [IsScalarTower.algebraMap_apply ℝ ℂ A]
    simp [map_pow, mul_assoc]
  · intro x y ihx ihy
    rw [(leftMul ((‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a)).map_add,
      map_add, ihx, ihy]
    simp only [smul_add]
    abel

lemma tensorInner_leftMul_selfadjoint (J : A →CP B(H)) {q : A} (hq : star q = q)
    (x : T A H) :
    tensorInner J (leftMul q x) x = tensorInner J x (leftMul q x) := by
  rw [tensorInner_leftMul J q x x, hq]

lemma tensorInner_leftMul_nonneg (J : A →CP B(H)) {q : A} (hq : 0 ≤ q)
    (x : T A H) : 0 ≤ tensorInner J (leftMul q x) x := by
  let s : A := CFC.sqrt q
  have hs : star s = s := by
    dsimp [s]
    exact (CFC.sqrt_nonneg q).isSelfAdjoint.star_eq
  have hsq : star s * s = q := by
    dsimp [s]
    rw [(CFC.sqrt_nonneg q).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self q hq
  have hinner : tensorInner J (leftMul q x) x =
      tensorInner J (leftMul s x) (leftMul s x) := by
    rw [← hsq, leftMul_mul]
    rw [tensorInner_leftMul J (star s) (leftMul s x) x]
    simp [hs]
  rw [hinner]
  exact tensorInner_nonneg J _

/-! The seminorm and pre-Hilbert structures induced by the kernel. -/

/-- The seminormed-group structure `T A H` inherits from `tensorCore`'s (possibly degenerate)
inner product. -/
noncomputable def tensorSeminormed (J : A →CP B(H)) :
    SeminormedAddCommGroup (T A H) :=
  letI : PreInnerProductSpace.Core ℂ (T A H) := tensorCore J
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := tensorCore J)

/-- The inner product space structure on `T A H`, with respect to `tensorSeminormed`, coming
from `tensorCore`. -/
noncomputable def tensorInnerProductSpace (J : A →CP B(H)) :
    @InnerProductSpace ℂ (T A H) inferInstance (tensorSeminormed J) := by
  letI : PreInnerProductSpace.Core ℂ (T A H) := tensorCore J
  letI : Inner ℂ (T A H) := ⟨fun x y => tensorInner J x y⟩
  letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  exact
    { toNormedSpace := InnerProductSpace.Core.toNormedSpace (c := tensorCore J)
      inner := fun x y => tensorInner J x y
      norm_sq_eq_re_inner := by
        intro x
        have hnorm :=
          (InnerProductSpace.Core.inner_self_eq_norm_mul_norm (c := tensorCore J) x)
        change RCLike.re ((tensorCore J).inner x x) = ‖x‖ * ‖x‖ at hnorm
        rw [pow_two]
        change ‖x‖ * ‖x‖ = RCLike.re ((tensorCore J).inner x x)
        simpa [pow_two] using hnorm.symm
      conj_inner_symm := by
        intro x y
        exact tensorInner_conj_symm J y x
      add_left := by
        intro x y z
        exact congrArg (fun f => f z) ((tensorInner J).map_add x y)
      smul_left := by
        intro x y r
        have hs := congrArg (fun f : T A H →ₗ[ℂ] ℂ => f y)
          ((tensorInner J).map_smulₛₗ r x)
        simpa only [LinearMap.smul_apply, smul_eq_mul] using hs }

lemma leftMul_norm_le (a : A) (J : A →CP B(H)) (x : T A H) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    ‖leftMul a x‖ ≤ ‖a‖ * ‖x‖ := by
  letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  let q : A := (‖a‖ ^ 2 : ℝ) • (1 : A) - star a * a
  have hq : 0 ≤ q := by
    dsimp [q]
    have hle : star a * a ≤ algebraMap ℝ A ‖star a * a‖ := by
      exact (CStarAlgebra.norm_le_iff_le_algebraMap (star a * a)
        (norm_nonneg _)).mp le_rfl
    rw [CStarRing.norm_star_mul_self] at hle
    simpa [sq, Algebra.algebraMap_eq_smul_one] using (sub_nonneg.mpr hle)
  have hpos := tensorInner_leftMul_nonneg J hq x
  rw [leftMul_norm_sub] at hpos
  have hleft : tensorInner J (leftMul (star a * a) x) x =
      tensorInner J (leftMul a x) (leftMul a x) := by
    rw [tensorInner_leftMul J (star a * a) x x]
    simp only [star_mul, star_star]
    rw [tensorInner_leftMul J a x (leftMul a x)]
    rw [← leftMul_mul]
  have hident : tensorInner J
      ((‖a‖ ^ 2 : ℂ) • x - leftMul (star a * a) x) x =
      (‖a‖ ^ 2 : ℝ) * tensorInner J x x -
        tensorInner J (leftMul a x) (leftMul a x) := by
    rw [sub_eq_add_neg, (tensorInner J).map_add]
    rw [LinearMap.add_apply, (tensorInner J).map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul]
    rw [← neg_one_smul ℂ, (tensorInner J).map_smulₛₗ,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hleft]
    rw [show starRingEnd ℂ (‖a‖ ^ 2 : ℂ) = (‖a‖ ^ 2 : ℂ) by simp]
    rw [show starRingEnd ℂ (-1 : ℂ) = (-1 : ℂ) by norm_num]
    simp [sub_eq_add_neg]
  rw [hident] at hpos
  have hreal := (RCLike.nonneg_iff.mp hpos).1
  have hselfx : RCLike.re (tensorInner J x x) = ‖x‖ ^ 2 := by
    have hnorm :=
      (InnerProductSpace.Core.inner_self_eq_norm_mul_norm (c := tensorCore J) x)
    change RCLike.re ((tensorCore J).inner x x) = ‖x‖ * ‖x‖ at hnorm
    rw [pow_two]
    change RCLike.re ((tensorCore J).inner x x) = ‖x‖ * ‖x‖
    exact hnorm
  have hselfa : RCLike.re (tensorInner J (leftMul a x) (leftMul a x)) =
      ‖leftMul a x‖ ^ 2 := by
    have hnorm :=
      (InnerProductSpace.Core.inner_self_eq_norm_mul_norm (c := tensorCore J)
        (leftMul a x))
    change RCLike.re ((tensorCore J).inner (leftMul a x) (leftMul a x)) =
      ‖leftMul a x‖ * ‖leftMul a x‖ at hnorm
    rw [pow_two]
    change RCLike.re ((tensorCore J).inner (leftMul a x) (leftMul a x)) =
      ‖leftMul a x‖ * ‖leftMul a x‖
    exact hnorm
  simp [map_sub, Complex.mul_re, hselfx, hselfa] at hreal
  simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im] at hreal
  have hreal' : ‖leftMul a x‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖x‖ ^ 2 := by
    simpa only [zero_mul, sub_zero, pow_two, mul_assoc] using hreal
  have hax : 0 ≤ ‖a‖ * ‖x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [hreal']

lemma uniformContinuous_add (J : A →CP B(H)) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
    UniformContinuous fun p : T A H × T A H => p.1 + p.2 := by
  letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
  refine LipschitzWith.uniformContinuous (K := (2 : NNReal)) ?_
  apply LipschitzWith.of_dist_le_mul (K := (2 : NNReal))
  intro p q
  rw [Prod.dist_eq]
  calc
    dist (p.1 + p.2) (q.1 + q.2) ≤ dist p.1 q.1 + dist p.2 q.2 :=
      dist_add_add_le _ _ _ _
    _ ≤ 2 * max (dist p.1 q.1) (dist p.2 q.2) := by
      nlinarith [le_max_left (dist p.1 q.1) (dist p.2 q.2),
        le_max_right (dist p.1 q.1) (dist p.2 q.2)]

lemma uniformContinuous_neg (J : A →CP B(H)) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
    UniformContinuous fun x : T A H => -x := by
  letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
  refine LipschitzWith.uniformContinuous (K := (1 : NNReal)) ?_
  apply LipschitzWith.of_dist_le_mul (K := (1 : NNReal))
  intro x y
  rw [SeminormedAddCommGroup.dist_eq, SeminormedAddCommGroup.dist_eq]
  calc
    ‖- -x + -y‖ = ‖-((-x) + y)‖ := by rw [neg_add_rev]; simp [add_comm]
    _ = ‖-x + y‖ := norm_neg _
  simp only [NNReal.coe_one, one_mul]
  exact le_rfl

/-- `leftMul a`, bundled as a continuous linear map for the kernel seminorm. -/
noncomputable def leftMulCLM (J : A →CP B(H)) (a : A) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
    T A H →L[ℂ] T A H := by
  letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
  exact (leftMul a).mkContinuous ‖a‖ (fun x => leftMul_norm_le a J x)

lemma leftMulCLM_apply (J : A →CP B(H)) (a : A) (x : T A H) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
    leftMulCLM J a x = leftMul a x := by
  letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
  rfl

/-- The continuous extension of `leftMulCLM` to the completion of `T A H`. -/
noncomputable def leftMulCompletion (J : A →CP B(H)) (a : A) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
    letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
    letI : NormedSpace ℂ (T A H) := (tensorInnerProductSpace J).toNormedSpace
    UniformSpace.Completion (T A H) →L[ℂ] UniformSpace.Completion (T A H) := by
  letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
  letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
  letI : NormedSpace ℂ (T A H) := (tensorInnerProductSpace J).toNormedSpace
  letI : IsUniformAddGroup (T A H) := IsUniformAddGroup.mk'
    (uniformContinuous_add J) (uniformContinuous_neg J)
  letI : IsBoundedSMul ℂ (T A H) := NormSMulClass.toIsBoundedSMul
  letI : UniformContinuousConstSMul ℂ (T A H) :=
    IsBoundedSMul.toUniformContinuousConstSMul
  exact (leftMulCLM J a).completion

@[simp]
lemma leftMulCompletion_coe (J : A →CP B(H)) (a : A) (x : T A H) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
    letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
    leftMulCompletion J a (x : UniformSpace.Completion (T A H)) = leftMulCLM J a x := by
  letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
  letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
  letI : NormedSpace ℂ (T A H) := (tensorInnerProductSpace J).toNormedSpace
  letI : IsUniformAddGroup (T A H) := IsUniformAddGroup.mk'
    (uniformContinuous_add J) (uniformContinuous_neg J)
  letI : IsBoundedSMul ℂ (T A H) := NormSMulClass.toIsBoundedSMul
  letI : UniformContinuousConstSMul ℂ (T A H) :=
    IsBoundedSMul.toUniformContinuousConstSMul
  change (leftMulCLM J a).completion (x : UniformSpace.Completion (T A H)) =
    (leftMulCLM J a) x
  exact ContinuousLinearMap.completion_apply_coe (leftMulCLM J a) x

lemma leftMulCompletion_mul (J : A →CP B(H)) (a b : A) :
    letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
    letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
    letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
    letI : NormedSpace ℂ (T A H) := (tensorInnerProductSpace J).toNormedSpace
    leftMulCompletion J (a * b) =
      (leftMulCompletion J a).comp (leftMulCompletion J b) := by
  letI : SeminormedAddCommGroup (T A H) := tensorSeminormed J
  letI : PseudoMetricSpace (T A H) := SeminormedAddCommGroup.toPseudoMetricSpace
  letI : InnerProductSpace ℂ (T A H) := tensorInnerProductSpace J
  letI : NormedSpace ℂ (T A H) := (tensorInnerProductSpace J).toNormedSpace
  letI : IsUniformAddGroup (T A H) := IsUniformAddGroup.mk'
    (uniformContinuous_add J) (uniformContinuous_neg J)
  letI : IsBoundedSMul ℂ (T A H) := NormSMulClass.toIsBoundedSMul
  letI : UniformContinuousConstSMul ℂ (T A H) :=
    IsBoundedSMul.toUniformContinuousConstSMul
  apply ContinuousLinearMap.ext
  intro z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · apply isClosed_eq
    · exact (leftMulCompletion J (a * b)).continuous
    · exact ((leftMulCompletion J a).comp (leftMulCompletion J b)).continuous
  · intro x
    change (leftMulCLM J (a * b)).completion (x : UniformSpace.Completion (T A H)) =
      (leftMulCLM J a).completion
        ((leftMulCLM J b).completion (x : UniformSpace.Completion (T A H)))
    rw [ContinuousLinearMap.completion_apply_coe]
    rw [ContinuousLinearMap.completion_apply_coe]
    rw [ContinuousLinearMap.completion_apply_coe]
    rw [leftMulCLM_apply, leftMulCLM_apply, leftMulCLM_apply]
    exact congrArg (fun y : T A H => (y : UniformSpace.Completion (T A H)))
      (leftMul_mul a b x)

/-! ## The canonical CP-dependent Hilbert space

The CP kernel changes the norm, so its pre-Hilbert space is made a type synonym.  This is the same
pattern used by Mathlib's GNS construction: the synonym lets the tensor product retain its original
module structure while carrying a CP-dependent seminorm and inner product. -/

namespace Canonical

open ContinuousLinearMap

/-- A type synonym for `T A H` carrying the CP-kernel-dependent seminorm and inner product,
kept separate so the tensor product retains its own module structure. -/
@[nolint unusedArguments]
def Pre (J : A →CP B(H)) := T A H

instance (J : A →CP B(H)) : AddCommGroup (Pre J) :=
  inferInstanceAs (AddCommGroup (T A H))

instance (J : A →CP B(H)) : Module ℂ (Pre J) :=
  inferInstanceAs (Module ℂ (T A H))

noncomputable instance (J : A →CP B(H)) : SeminormedAddCommGroup (Pre J) :=
  tensorSeminormed J

noncomputable instance (J : A →CP B(H)) : InnerProductSpace ℂ (Pre J) :=
  InnerProductSpace.ofCore (tensorCore J)

noncomputable instance (J : A →CP B(H)) : IsUniformAddGroup (Pre J) :=
  IsUniformAddGroup.mk' (uniformContinuous_add J) (uniformContinuous_neg J)

noncomputable instance (J : A →CP B(H)) : IsBoundedSMul ℂ (Pre J) :=
  NormSMulClass.toIsBoundedSMul

noncomputable instance (J : A →CP B(H)) : UniformContinuousConstSMul ℂ (Pre J) :=
  IsBoundedSMul.toUniformContinuousConstSMul

/-- The completion of `Pre J`: the canonical Stinespring Hilbert space attached to `J`. -/
abbrev K (J : A →CP B(H)) := UniformSpace.Completion (Pre J)

/-- `leftMul a`, viewed as an operator on `Pre J`. -/
noncomputable def preLeftMul (J : A →CP B(H)) (a : A) :
    Pre J →ₗ[ℂ] Pre J := leftMul a

@[simp]
lemma preLeftMul_apply (J : A →CP B(H)) (a : A) (x : Pre J) :
    preLeftMul J a x = leftMul a x := rfl

/-- `preLeftMul`, bundled as a continuous linear map. -/
noncomputable def preLeftMulCLM (J : A →CP B(H)) (a : A) :
    Pre J →L[ℂ] Pre J :=
  (preLeftMul J a).mkContinuous ‖a‖ (fun x => leftMul_norm_le a J x)

@[simp]
lemma preLeftMulCLM_apply (J : A →CP B(H)) (a : A) (x : Pre J) :
    preLeftMulCLM J a x = preLeftMul J a x := rfl

lemma completion_leftMul_norm_le (J : A →CP B(H)) (a : A) (x : K J) :
    ‖(preLeftMulCLM J a).completion x‖ ≤ ‖a‖ * ‖x‖ := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · apply isClosed_le
    · exact (preLeftMulCLM J a).completion.continuous.norm
    · exact (continuous_const.mul continuous_norm)
  · intro y
    rw [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe,
      preLeftMulCLM_apply, preLeftMul_apply, UniformSpace.Completion.norm_coe]
    exact leftMul_norm_le a J y

/-- The continuous extension of `preLeftMulCLM` to the completion `K J`. -/
noncomputable def leftMulK (J : A →CP B(H)) (a : A) : K J →L[ℂ] K J :=
  ((preLeftMulCLM J a).completion.toLinearMap).mkContinuous ‖a‖
    (completion_leftMul_norm_le J a)

@[simp]
lemma leftMulK_coe (J : A →CP B(H)) (a : A) (x : Pre J) :
    leftMulK J a (x : K J) = preLeftMulCLM J a x := by
  exact ContinuousLinearMap.completion_apply_coe (preLeftMulCLM J a) x

lemma leftMulK_mul (J : A →CP B(H)) (a b : A) :
    leftMulK J (a * b) = (leftMulK J a).comp (leftMulK J b) := by
  apply ContinuousLinearMap.ext
  intro z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · apply isClosed_eq
    · exact (leftMulK J (a * b)).continuous
    · exact ((leftMulK J a).comp (leftMulK J b)).continuous
  · intro x
    rw [leftMulK_coe, ContinuousLinearMap.comp_apply, leftMulK_coe, leftMulK_coe]
    rw [preLeftMulCLM_apply, preLeftMulCLM_apply, preLeftMulCLM_apply]
    exact congrArg (fun y : Pre J => (y : K J)) (leftMul_mul a b x)

lemma leftMulK_one (J : A →CP B(H)) :
    leftMulK J (1 : A) = ContinuousLinearMap.id ℂ (K J) := by
  apply ContinuousLinearMap.ext
  intro z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · apply isClosed_eq
    · exact (leftMulK J (1 : A)).continuous
    · fun_prop
  · intro x
    rw [leftMulK_coe]
    change ((preLeftMulCLM J (1 : A)) x : K J) = (x : K J)
    rw [preLeftMulCLM_apply, preLeftMul_apply]
    exact congrArg (fun y : Pre J => (y : K J)) (leftMul_one x)

lemma leftMulK_add (J : A →CP B(H)) (a b : A) :
    leftMulK J (a + b) = leftMulK J a + leftMulK J b := by
  apply ContinuousLinearMap.ext
  intro z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · apply isClosed_eq
    · exact (leftMulK J (a + b)).continuous
    · fun_prop
  · intro x
    rw [leftMulK_coe]
    rw [ContinuousLinearMap.add_apply, leftMulK_coe, leftMulK_coe]
    rw [preLeftMulCLM_apply, preLeftMulCLM_apply, preLeftMulCLM_apply]
    rw [← UniformSpace.Completion.coe_add]
    exact congrArg (fun y : Pre J => (y : K J)) (leftMul_add a b x)

lemma leftMulK_smul (J : A →CP B(H)) (r : ℂ) (a : A) :
    leftMulK J (r • a) = r • leftMulK J a := by
  apply ContinuousLinearMap.ext
  intro z
  refine UniformSpace.Completion.induction_on z ?_ ?_
  · apply isClosed_eq
    · exact (leftMulK J (r • a)).continuous
    · exact (leftMulK J a).continuous.const_smul r
  · intro x
    rw [leftMulK_coe]
    rw [ContinuousLinearMap.smul_apply, leftMulK_coe]
    rw [preLeftMulCLM_apply, preLeftMulCLM_apply]
    rw [← UniformSpace.Completion.coe_smul]
    exact congrArg (fun y : Pre J => (y : K J)) (leftMul_smul r a x)

set_option backward.isDefEq.respectTransparency false in
lemma leftMulK_star (J : A →CP B(H)) (a : A) :
    leftMulK J (star a) = (leftMulK J a).adjoint := by
  refine (eq_adjoint_iff (leftMulK J (star a)) (leftMulK J a)).mpr ?_
  intro x y
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · apply isClosed_eq
    · fun_prop
    · fun_prop
  · intro u v
    rw [leftMulK_coe, UniformSpace.Completion.inner_coe,
      leftMulK_coe, UniformSpace.Completion.inner_coe]
    rw [preLeftMulCLM_apply, preLeftMulCLM_apply]
    change tensorInner J (leftMul (star a) u) v = tensorInner J u (leftMul a v)
    rw [tensorInner_leftMul]
    simp only [star_star]

/-- The canonical embedding `H → Pre J`, `h ↦ 1 ⊗ h`. -/
noncomputable def preEmbedding (J : A →CP B(H)) : H →ₗ[ℂ] Pre J :=
  (TensorProduct.mk ℂ A H) 1

@[simp]
lemma preEmbedding_apply (J : A →CP B(H)) (h : H) :
    preEmbedding J h = (1 : A) ⊗ₜ[ℂ] h := rfl

lemma preEmbedding_norm_sq (J : A →CP B(H)) (h : H) :
    ‖preEmbedding J h‖ ^ 2 = RCLike.re (inner ℂ h (J (1 : A) h)) := by
  rw [@norm_sq_eq_re_inner ℂ (Pre J) _ _]
  change RCLike.re (tensorInner J ((1 : A) ⊗ₜ[ℂ] h) ((1 : A) ⊗ₜ[ℂ] h)) = _
  rw [tensorInner_tmul]
  simp

lemma preEmbedding_norm_le (J : A →CP B(H)) (h : H) :
    ‖preEmbedding J h‖ ≤ Real.sqrt ‖J (1 : A)‖ * ‖h‖ := by
  have hsq : ‖preEmbedding J h‖ ^ 2 ≤
      (Real.sqrt ‖J (1 : A)‖ * ‖h‖) ^ 2 := by
    rw [preEmbedding_norm_sq]
    calc
      RCLike.re (inner ℂ h (J (1 : A) h)) ≤ ‖inner ℂ h (J (1 : A) h)‖ :=
        RCLike.re_le_norm _
      _ ≤ ‖h‖ * ‖J (1 : A) h‖ := norm_inner_le_norm _ _
      _ ≤ ‖h‖ * (‖J (1 : A)‖ * ‖h‖) := by
        exact mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.le_opNorm (J (1 : A)) h) (norm_nonneg _)
      _ = (Real.sqrt ‖J (1 : A)‖ * ‖h‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (norm_nonneg _))).mp hsq

/-- `preEmbedding`, bundled as a continuous linear map. -/
noncomputable def preEmbeddingCLM (J : A →CP B(H)) : H →L[ℂ] Pre J :=
  (preEmbedding J).mkContinuous (Real.sqrt ‖J (1 : A)‖) (preEmbedding_norm_le J)

/-- The canonical embedding `H → K J` into the completed Stinespring space. -/
noncomputable def embedding (J : A →CP B(H)) : H →L[ℂ] K J :=
  (UniformSpace.Completion.toComplL : Pre J →L[ℂ] K J).comp (preEmbeddingCLM J)

@[simp]
lemma embedding_apply (J : A →CP B(H)) (h : H) :
    embedding J h = (preEmbedding J h : K J) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The representation of `A` on `K J` by (extended) left multiplication. -/
noncomputable def canonicalRepresentation (J : A →CP B(H)) :
    Representation A (K J) where
  toFun := leftMulK J
  map_one' := leftMulK_one J
  map_mul' := leftMulK_mul J
  map_zero' := by
    simpa only [map_zero, zero_smul] using (leftMulK_smul J 0 0)
  map_add' := leftMulK_add J
  commutes' := by
    intro r
    calc
      leftMulK J ((algebraMap ℂ A) r) = r • leftMulK J (1 : A) := by
        simpa [Algebra.smul_def] using (leftMulK_smul J r (1 : A))
      _ = (algebraMap ℂ (K J →L[ℂ] K J)) r := by
        rw [leftMulK_one]
        simp [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_def]
  map_star' := leftMulK_star J

set_option backward.isDefEq.respectTransparency false in
lemma canonical_stinespring_identity (J : A →CP B(H)) (a : A) :
    J a = ContinuousLinearMap.adjoint (embedding J) ∘L
      (canonicalRepresentation J a) ∘L embedding J := by
  apply ContinuousLinearMap.ext
  intro x
  rw [@ext_iff_inner_left ℂ H _ _]
  intro y
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]
  rw [embedding_apply, embedding_apply]
  change inner ℂ y (J a x) =
    inner ℂ (preEmbedding J y : K J) (leftMulK J a (preEmbedding J x : K J))
  rw [leftMulK_coe]
  rw [UniformSpace.Completion.inner_coe]
  rw [preLeftMulCLM_apply, preLeftMul_apply]
  rw [preEmbedding_apply, preEmbedding_apply]
  change inner ℂ y (J a x) =
    tensorInner J ((1 : A) ⊗ₜ[ℂ] y) (leftMul a ((1 : A) ⊗ₜ[ℂ] x))
  rw [leftMul_tmul, tensorInner_tmul]
  simp

/-- The canonical Stinespring witness assembled from `canonicalRepresentation` and
`embedding`. -/
noncomputable def canonicalWitness (J : A →CP B(H)) :
    StinespringWitness A H (K J) J where
  representation := canonicalRepresentation J
  implementing := embedding J
  map_eq := canonical_stinespring_identity J

end Canonical

end TensorStinespring

namespace TensorStinespring.Canonical

/-! ### The canonical B(H) operator form

The construction above is canonical once the completely positive jump map is fixed.  This is the
point at which the representation-free Christensen--Evans formula becomes an honest
bounded-operator formula.  The `B(H)` converse is proved below by constructing the completely
positive jump map from the Evans--Lewis kernel completion.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma canonical_generator_apply_operator_form
    (D : ChristensenEvansData (B(H))) (a : B(H)) :
    D.generator a =
      Complex.I • ((D.hamiltonian : B(H)) * a - a * (D.hamiltonian : B(H))) +
        (ContinuousLinearMap.adjoint (embedding D.jump) ∘L
          (canonicalRepresentation D.jump a) ∘L embedding D.jump) -
        (2 : ℂ)⁻¹ •
          ((ContinuousLinearMap.adjoint (embedding D.jump) ∘L
            (canonicalRepresentation D.jump (1 : B(H))) ∘L embedding D.jump) * a +
            a * (ContinuousLinearMap.adjoint (embedding D.jump) ∘L
              (canonicalRepresentation D.jump (1 : B(H))) ∘L embedding D.jump)) := by
  rw [ChristensenEvansData.generator_apply]
  rw [canonical_stinespring_identity D.jump a]
  rw [canonical_stinespring_identity D.jump (1 : B(H))]

end TensorStinespring.Canonical

namespace StinespringWitness

/-! ### The Evans--Lewis defect factorisation

For a Stinespring witness `J a = V⋆ π(a) V`, the completely positive kernel associated with
the Christensen--Evans expression is a Gram kernel.  Its vectors are the defects
`π(a)V - Va`.  This is the reusable bridge from a CP kernel to the bounded operator form.
-/

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {J : B(H) →CP B(H)}

/-- The Stinespring defect of an operator `a` relative to a witness `W`. -/
noncomputable def defect (W : StinespringWitness (B(H)) H K J) (a : B(H)) : H →L[ℂ] K :=
  (W.representation a) ∘L W.implementing - W.implementing ∘L a

@[simp]
lemma defect_apply (W : StinespringWitness (B(H)) H K J) (a : B(H)) (x : H) :
    W.defect a x = W.representation a (W.implementing x) - W.implementing (a x) := by
  rfl

/-- The CP kernel of a Stinespring map is the Gram kernel of its defects. -/
lemma cpKernel_eq_defect_gram
    (W : StinespringWitness (B(H)) H K J) (a b : B(H)) :
    J (star a * b) - J (star a) * b - star a * J b + star a * J 1 * b =
      ContinuousLinearMap.adjoint (W.defect a) ∘L W.defect b := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [W.map_eq_apply, W.map_eq_apply, W.map_eq_apply, W.map_eq_apply]
  simp only [defect_apply]
  simp only [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right,
    ContinuousLinearMap.comp_apply, mul_apply_eq_comp, sub_apply, add_apply]
  have hV (u : K) (v : H) :
      inner ℂ ((ContinuousLinearMap.adjoint W.implementing) u) v =
        inner ℂ u (W.implementing v) := by
    rw [ContinuousLinearMap.adjoint_inner_left]
  have hπ (c : B(H)) (u v : K) :
      inner ℂ ((W.representation (star c)) u) v =
        inner ℂ u ((W.representation c) v) := by
    have hstar : W.representation (star c) = star (W.representation c) :=
      map_star W.representation c
    rw [hstar, ContinuousLinearMap.star_eq_adjoint]
    exact ContinuousLinearMap.adjoint_inner_left (W.representation c) v u
  have ha (u v : H) :
      inner ℂ ((star a) u) v = inner ℂ u (a v) := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have hmul : W.representation (star a * b) =
      W.representation (star a) * W.representation b :=
    W.representation.map_mul (star a) b
  rw [hV, hmul]
  simp only [mul_apply_eq_comp]
  rw [hπ, hV, hπ, ha, hV, ha, hV]
  have hone : W.representation (1 : B(H)) = 1 := map_one W.representation
  rw [hone]
  have hone_apply (z : K) : (1 : K →L[ℂ] K) z = z := by rfl
  rw [hone_apply]
  ring

lemma evansLewisKernel_generator_eq_cpKernel
    (W : StinespringWitness (B(H)) H K J) (h : Observable B(H)) (a b : B(H)) :
    evansLewisKernel (W.toChristensenEvansData h).generator a b =
      J (star a * b) - J (star a) * b - star a * J b + star a * J 1 * b := by
  rw [evansLewisKernel, ChristensenEvansData.generator_apply]
  change
    (Complex.I • (h * (star a * b) - (star a * b) * h) + J (star a * b) -
        (2 : ℂ)⁻¹ • (J 1 * (star a * b) + (star a * b) * J 1)) -
      (Complex.I • (h * star a - star a * h) + J (star a) -
        (2 : ℂ)⁻¹ • (J 1 * star a + star a * J 1)) * b -
      star a * (Complex.I • (h * b - b * h) + J b -
        (2 : ℂ)⁻¹ • (J 1 * b + b * J 1)) +
      star a * (Complex.I • (h * 1 - 1 * h) + J 1 -
        (2 : ℂ)⁻¹ • (J 1 * 1 + 1 * J 1)) * b = _
  simp only [map_add, map_sub, map_smul, sub_eq_add_neg, smul_add, smul_sub,
    add_mul, sub_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm]
  noncomm_ring

lemma evansLewisKernel_generator_eq_defect_gram
    (W : StinespringWitness (B(H)) H K J) (h : Observable B(H)) (a b : B(H)) :
    evansLewisKernel (W.toChristensenEvansData h).generator a b =
      ContinuousLinearMap.adjoint (W.defect a) ∘L W.defect b := by
  rw [W.evansLewisKernel_generator_eq_cpKernel h, W.cpKernel_eq_defect_gram]

end StinespringWitness

/-- Positivity of an operator-valued kernel, tested on all finite families. -/
@[nolint unusedArguments]
def IsPositiveOperatorKernel
    {A H : Type*} [OperatorAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : A → A → B(H)) : Prop :=
  ∀ (n : ℕ) (a : Fin n → A) (x : Fin n → H),
    0 ≤ Complex.re (∑ i, ∑ j, inner ℂ (x i) (K (a i) (a j) (x j)))

/-! ### GNS factorisation of a positive operator kernel

The positivity statement alone is not enough to recover a Christensen--Evans generator: the
kernel must also be sesquilinear in its algebra variables.  This structure records precisely
those algebraic laws.  Its completion is the reusable Kolmogorov/GNS factorisation layer; the
additional multiplicative cocycle identities needed for the full Evans--Lewis converse are kept
separate below. -/

/-- A positivity-and-sesquilinearity package for an operator-valued kernel `A → A → B(H)`,
the reusable input to the GNS/Kolmogorov factorisation below. -/
structure PositiveOperatorKernelData
    {A H : Type*} [OperatorAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The operator-valued kernel. -/
  kernel : A → A → B(H)
  /-- Positivity on finite families. -/
  isPositive : IsPositiveOperatorKernel kernel
  /-- Hermitian symmetry of the kernel. -/
  kernel_star : ∀ a b, star (kernel a b) = kernel b a
  /-- Additivity in the first algebra variable. -/
  kernel_add_left : ∀ a b c, kernel (a + b) c = kernel a c + kernel b c
  /-- Conjugate homogeneity in the first algebra variable. -/
  kernel_smul_left : ∀ r a b, kernel (r • a) b = starRingEnd ℂ r • kernel a b
  /-- Additivity in the second algebra variable. -/
  kernel_add_right : ∀ a b c, kernel a (b + c) = kernel a b + kernel a c
  /-- Homogeneity in the second algebra variable. -/
  kernel_smul_right : ∀ (r : ℂ) (a b : A), kernel a (r • b) = r • kernel a b

namespace PositiveOperatorKernelData

variable {A H : Type*} [OperatorAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The (possibly indefinite) sesquilinear form on `A →₀ H` induced by the kernel. -/
noncomputable def kernelInner (K : PositiveOperatorKernelData (A := A) (H := H))
    (x y : A →₀ H) : ℂ :=
  x.sum fun a u => y.sum fun b v => inner ℂ u (K.kernel a b v)

lemma kernelInner_add_left (K : PositiveOperatorKernelData (A := A) (H := H))
    (x y z : A →₀ H) : K.kernelInner (x + y) z = K.kernelInner x z + K.kernelInner y z := by
  classical
  unfold kernelInner
  rw [Finsupp.sum_add_index']
  · simp
  · intro a b₁ b₂
    simp

lemma kernelInner_smul_left (K : PositiveOperatorKernelData (A := A) (H := H))
    (r : ℂ) (x y : A →₀ H) :
    K.kernelInner (r • x) y = starRingEnd ℂ r * K.kernelInner x y := by
  classical
  unfold kernelInner
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp_rw [_root_.inner_smul_left]
  simp only [Finsupp.sum]
  simp_rw [← Finset.mul_sum]

lemma kernelInner_conj_symm (K : PositiveOperatorKernelData (A := A) (H := H))
    (x y : A →₀ H) : starRingEnd ℂ (K.kernelInner y x) = K.kernelInner x y := by
  classical
  unfold kernelInner
  simp only [Finsupp.sum]
  simp_rw [map_sum, _root_.inner_conj_symm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hop : K.kernel b a =
      ContinuousLinearMap.adjoint (K.kernel a b) := by
    calc
      K.kernel b a = star (K.kernel a b) := (K.kernel_star a b).symm
      _ = ContinuousLinearMap.adjoint (K.kernel a b) := by rfl
  rw [hop]
  rw [ContinuousLinearMap.adjoint_inner_left]

lemma kernelInner_add_right (K : PositiveOperatorKernelData (A := A) (H := H))
    (x y z : A →₀ H) : K.kernelInner x (y + z) = K.kernelInner x y + K.kernelInner x z := by
  calc
    K.kernelInner x (y + z) =
        starRingEnd ℂ (K.kernelInner (y + z) x) :=
      (K.kernelInner_conj_symm x (y + z)).symm
    _ = starRingEnd ℂ (K.kernelInner y x + K.kernelInner z x) := by
      rw [K.kernelInner_add_left]
    _ = starRingEnd ℂ (K.kernelInner y x) +
        starRingEnd ℂ (K.kernelInner z x) := by simp
    _ = K.kernelInner x y + K.kernelInner x z := by
      rw [K.kernelInner_conj_symm, K.kernelInner_conj_symm]

lemma kernelInner_smul_right (K : PositiveOperatorKernelData (A := A) (H := H))
    (r : ℂ) (x y : A →₀ H) : K.kernelInner x (r • y) = r * K.kernelInner x y := by
  calc
    K.kernelInner x (r • y) =
        starRingEnd ℂ (K.kernelInner (r • y) x) :=
      (K.kernelInner_conj_symm x (r • y)).symm
    _ = starRingEnd ℂ (starRingEnd ℂ r * K.kernelInner y x) := by
      rw [K.kernelInner_smul_left]
    _ = r * starRingEnd ℂ (K.kernelInner y x) := by simp
    _ = r * K.kernelInner x y := by rw [K.kernelInner_conj_symm]

lemma kernelInner_single_single (K : PositiveOperatorKernelData (A := A) (H := H))
    (a b : A) (x y : H) :
    K.kernelInner (Finsupp.single a x) (Finsupp.single b y) =
      inner ℂ x (K.kernel a b y) := by
  classical
  simp [kernelInner, Finsupp.sum_single_index]

lemma kernelInner_nonneg (K : PositiveOperatorKernelData (A := A) (H := H))
    (x : A →₀ H) : 0 ≤ Complex.re (K.kernelInner x x) := by
  classical
  let s := x.support
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let v : Fin (Fintype.card s) → H := fun i => x (e.symm i)
  have h := K.isPositive (Fintype.card s) (fun i => (e.symm i : A)) (fun i => v i)
  dsimp [kernelInner]
  simp only [Finsupp.sum]
  rw [← Finset.sum_attach x.support]
  simp_rw [← Finset.sum_attach x.support]
  simp_rw [Complex.re_sum]
  change 0 ≤ ∑ a : s, ∑ b : s,
    (inner ℂ (x a) (K.kernel (a : A) (b : A) (x b))).re
  rw [← e.symm.sum_comp]
  simp_rw [← e.symm.sum_comp]
  simpa [s, v, map_sum] using h

/-- `kernelInner`, packaged as a `PreInnerProductSpace.Core` on `A →₀ H`. -/
noncomputable def core (K : PositiveOperatorKernelData (A := A) (H := H)) :
    PreInnerProductSpace.Core ℂ (A →₀ H) where
  inner := K.kernelInner
  conj_inner_symm := K.kernelInner_conj_symm
  re_inner_nonneg := by
    intro x
    exact K.kernelInner_nonneg x
  add_left := K.kernelInner_add_left
  smul_left := by
    intro x y r
    simpa only [starRingEnd_apply] using K.kernelInner_smul_left r x y

/-! The completion and the canonical kernel vectors. -/

/-- The seminormed-group structure `A →₀ H` inherits from `core`'s inner product. -/
noncomputable def seminormed (K : PositiveOperatorKernelData (A := A) (H := H)) :
    SeminormedAddCommGroup (A →₀ H) :=
  letI : PreInnerProductSpace.Core ℂ (A →₀ H) := K.core
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := K.core)

/-- The inner product space structure on `A →₀ H`, with respect to `seminormed`, coming from
`core`. -/
noncomputable def innerProductSpace (K : PositiveOperatorKernelData (A := A) (H := H)) :
    @InnerProductSpace ℂ (A →₀ H) inferInstance (K.seminormed) := by
  letI : PreInnerProductSpace.Core ℂ (A →₀ H) := K.core
  letI : Inner ℂ (A →₀ H) := ⟨K.kernelInner⟩
  letI : SeminormedAddCommGroup (A →₀ H) := K.seminormed
  exact InnerProductSpace.ofCore K.core

namespace Canonical

/-- A type synonym for `A →₀ H` carrying the kernel-dependent seminorm and inner product. -/
@[nolint unusedArguments]
abbrev Pre (K : PositiveOperatorKernelData (A := A) (H := H)) := A →₀ H

noncomputable instance (K : PositiveOperatorKernelData (A := A) (H := H)) :
    SeminormedAddCommGroup (Pre K) := K.seminormed

noncomputable instance (K : PositiveOperatorKernelData (A := A) (H := H)) :
    InnerProductSpace ℂ (Pre K) := K.innerProductSpace

noncomputable instance (K : PositiveOperatorKernelData (A := A) (H := H)) :
    IsBoundedSMul ℂ (Pre K) := NormSMulClass.toIsBoundedSMul

noncomputable instance (K : PositiveOperatorKernelData (A := A) (H := H)) :
    UniformContinuousConstSMul ℂ (Pre K) :=
  IsBoundedSMul.toUniformContinuousConstSMul

/-- The completion of `Pre K`: the GNS Hilbert space of the kernel `K`. -/
abbrev Completion (K : PositiveOperatorKernelData (A := A) (H := H)) :=
  UniformSpace.Completion (Pre K)

lemma uniformContinuous_add (K : PositiveOperatorKernelData (A := A) (H := H)) :
    letI : SeminormedAddCommGroup (Pre K) := K.seminormed
    letI : PseudoMetricSpace (Pre K) := SeminormedAddCommGroup.toPseudoMetricSpace
    UniformContinuous fun p : Pre K × Pre K => p.1 + p.2 := by
  letI : SeminormedAddCommGroup (Pre K) := K.seminormed
  letI : PseudoMetricSpace (Pre K) := SeminormedAddCommGroup.toPseudoMetricSpace
  refine LipschitzWith.uniformContinuous (K := (2 : NNReal)) ?_
  apply LipschitzWith.of_dist_le_mul (K := (2 : NNReal))
  intro p q
  rw [Prod.dist_eq]
  calc
    dist (p.1 + p.2) (q.1 + q.2) ≤ dist p.1 q.1 + dist p.2 q.2 :=
      dist_add_add_le _ _ _ _
    _ ≤ 2 * max (dist p.1 q.1) (dist p.2 q.2) := by
      nlinarith [le_max_left (dist p.1 q.1) (dist p.2 q.2),
        le_max_right (dist p.1 q.1) (dist p.2 q.2)]

lemma uniformContinuous_neg (K : PositiveOperatorKernelData (A := A) (H := H)) :
    letI : SeminormedAddCommGroup (Pre K) := K.seminormed
    letI : PseudoMetricSpace (Pre K) := SeminormedAddCommGroup.toPseudoMetricSpace
    UniformContinuous fun x : Pre K => -x := by
  letI : SeminormedAddCommGroup (Pre K) := K.seminormed
  letI : PseudoMetricSpace (Pre K) := SeminormedAddCommGroup.toPseudoMetricSpace
  refine LipschitzWith.uniformContinuous (K := (1 : NNReal)) ?_
  apply LipschitzWith.of_dist_le_mul (K := (1 : NNReal))
  intro x y
  rw [SeminormedAddCommGroup.dist_eq, SeminormedAddCommGroup.dist_eq]
  calc
    ‖- -x + -y‖ = ‖-((-x) + y)‖ := by rw [neg_add_rev]; simp [add_comm]
    _ = ‖-x + y‖ := norm_neg _
  simp only [NNReal.coe_one, one_mul]
  exact le_rfl

noncomputable instance (K : PositiveOperatorKernelData (A := A) (H := H)) :
    IsUniformAddGroup (Pre K) := IsUniformAddGroup.mk'
      (uniformContinuous_add K) (uniformContinuous_neg K)

/-- The canonical embedding `H → Pre K` at the algebra point `a`, `x ↦ single a x`. -/
noncomputable def preEmbedding (K : PositiveOperatorKernelData (A := A) (H := H))
    (a : A) : H →ₗ[ℂ] Pre K :=
  Finsupp.lsingle a

@[simp]
lemma preEmbedding_apply (K : PositiveOperatorKernelData (A := A) (H := H))
    (a : A) (x : H) : preEmbedding K a x = Finsupp.single a x := rfl

lemma preEmbedding_norm_sq (K : PositiveOperatorKernelData (A := A) (H := H))
    (a : A) (x : H) :
    ‖preEmbedding K a x‖ ^ 2 =
      Complex.re (inner ℂ x (K.kernel a a x)) := by
  rw [@norm_sq_eq_re_inner ℂ (Pre K) _ _]
  rw [preEmbedding_apply]
  change Complex.re
      (K.kernelInner (Finsupp.single a x) (Finsupp.single a x)) =
    Complex.re (inner ℂ x (K.kernel a a x))
  rw [K.kernelInner_single_single]

lemma preEmbedding_norm_le (K : PositiveOperatorKernelData (A := A) (H := H))
    (a : A) (x : H) :
    ‖preEmbedding K a x‖ ≤ Real.sqrt ‖K.kernel a a‖ * ‖x‖ := by
  have hsq : ‖preEmbedding K a x‖ ^ 2 ≤
      (Real.sqrt ‖K.kernel a a‖ * ‖x‖) ^ 2 := by
    rw [preEmbedding_norm_sq K]
    calc
      Complex.re (inner ℂ x (K.kernel a a x)) ≤
          ‖inner ℂ x (K.kernel a a x)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖ * ‖K.kernel a a x‖ := norm_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖K.kernel a a‖ * ‖x‖) := by
        exact mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.le_opNorm (K.kernel a a) x) (norm_nonneg _)
      _ = (Real.sqrt ‖K.kernel a a‖ * ‖x‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
    (norm_nonneg _))).mp hsq

/-- `preEmbedding`, bundled as a continuous linear map. -/
noncomputable def preEmbeddingCLM (K : PositiveOperatorKernelData (A := A) (H := H))
    (a : A) : H →L[ℂ] Pre K :=
  (preEmbedding K a).mkContinuous (Real.sqrt ‖K.kernel a a‖)
    (preEmbedding_norm_le K a)

/-- The canonical embedding `H → Completion K` at the algebra point `a`. -/
noncomputable def embedding (K : PositiveOperatorKernelData (A := A) (H := H))
    (a : A) : H →L[ℂ] Completion K :=
  letI : SeminormedAddCommGroup (Pre K) := K.seminormed
  letI : InnerProductSpace ℂ (Pre K) := K.innerProductSpace
  letI : IsUniformAddGroup (Pre K) := IsUniformAddGroup.mk'
    (uniformContinuous_add K) (uniformContinuous_neg K)
  letI : IsBoundedSMul ℂ (Pre K) := NormSMulClass.toIsBoundedSMul
  letI : UniformContinuousConstSMul ℂ (Pre K) :=
    IsBoundedSMul.toUniformContinuousConstSMul
  (UniformSpace.Completion.toComplL).comp (preEmbeddingCLM K a)

@[simp]
lemma embedding_apply (K : PositiveOperatorKernelData (A := A) (H := H))
    (a : A) (x : H) : embedding K a x = (preEmbedding K a x : Completion K) := rfl

lemma embedding_inner (K : PositiveOperatorKernelData (A := A) (H := H))
    (a b : A) (x y : H) :
    inner ℂ (embedding K a x) (embedding K b y) =
      inner ℂ x (K.kernel a b y) := by
  rw [embedding_apply, embedding_apply, UniformSpace.Completion.inner_coe]
  exact K.kernelInner_single_single a b x y

set_option backward.isDefEq.respectTransparency false in
lemma embedding_add_apply (K : PositiveOperatorKernelData (A := A) (H := H))
    (a b : A) (x : H) :
    embedding K (a + b) x = embedding K a x + embedding K b x := by
  rw [← sub_eq_zero]
  apply (_root_.inner_self_eq_zero (𝕜 := ℂ) (E := Completion K)).mp
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right]
  simp only [embedding_inner]
  simp only [K.kernel_add_left, K.kernel_add_right]
  simp only [ContinuousLinearMap.add_apply, inner_add_right]
  ring

set_option backward.isDefEq.respectTransparency false in
lemma embedding_smul_apply (K : PositiveOperatorKernelData (A := A) (H := H))
    (r : ℂ) (a : A) (x : H) :
    embedding K (r • a) x = r • embedding K a x := by
  rw [← sub_eq_zero]
  apply (_root_.inner_self_eq_zero (𝕜 := ℂ) (E := Completion K)).mp
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  simp only [embedding_inner]
  simp only [K.kernel_smul_left, K.kernel_smul_right]
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
    starRingEnd_apply]
  ring

end Canonical

end PositiveOperatorKernelData

end OperatorAlgebra
