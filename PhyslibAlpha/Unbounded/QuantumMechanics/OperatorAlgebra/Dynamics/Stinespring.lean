/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Dynamics.ChristensenEvans
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Analysis.InnerProductSpace.Completion
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.VectorState

/-!
# The tensor-product core of Stinespring's construction

For a completely positive map `J : A →CP B(H)`, the algebraic tensor product `A ⊗ H` carries the
canonical positive kernel

`⟪a ⊗ ξ, b ⊗ η⟫ = ⟪ξ, J(a* b) η⟫`.

The file develops this core through its seminormed completion and the resulting canonical
Stinespring witness.  For `B(H)`, the complete bounded Christensen--Evans converse is proved below:
the positive Evans--Lewis kernel is represented on its completion and compressed back to a CP
jump map.  The analogous converse for an arbitrary C⋆-algebra remains a separate question.
Using `TensorProduct` is essential:
a raw finitely-supported family indexed by `A` does not impose the relations expressing linearity
in the algebra factor.
-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra TensorProduct
open OperatorAlgebra
noncomputable section

namespace OperatorAlgebra.TensorStinespring

variable {A H : Type*} [OperatorAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev T (A H : Type*) [OperatorAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] := A ⊗[ℂ] H

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

noncomputable def sesquiBilinear (J : A →CP B(H)) :
    A →ₛₗ[starRingEnd ℂ] H →ₛₗ[starRingEnd ℂ] (T A H →ₗ[ℂ] ℂ) :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (starRingEnd ℂ)
    (fun a h => baseFunctional J a h)
    (by intro a₁ a₂ h; ext x; simp [baseFunctional, star_add, add_mul, map_add])
    (by intro c a h; ext x; simp [baseFunctional, star_smul, map_smul])
    (by intro a h₁ h₂; ext x; simp [baseFunctional])
    (by intro c a h; ext x; simp [baseFunctional]; ring)

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

noncomputable def tensorSeminormed (J : A →CP B(H)) :
    SeminormedAddCommGroup (T A H) :=
  letI : PreInnerProductSpace.Core ℂ (T A H) := tensorCore J
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := tensorCore J)

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

abbrev K (J : A →CP B(H)) := UniformSpace.Completion (Pre J)

noncomputable def preLeftMul (J : A →CP B(H)) (a : A) :
    Pre J →ₗ[ℂ] Pre J := leftMul a

@[simp]
lemma preLeftMul_apply (J : A →CP B(H)) (a : A) (x : Pre J) :
    preLeftMul J a x = leftMul a x := rfl

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

noncomputable def preEmbeddingCLM (J : A →CP B(H)) : H →L[ℂ] Pre J :=
  (preEmbedding J).mkContinuous (Real.sqrt ‖J (1 : A)‖) (preEmbedding_norm_le J)

noncomputable def embedding (J : A →CP B(H)) : H →L[ℂ] K J :=
  (UniformSpace.Completion.toComplL : Pre J →L[ℂ] K J).comp (preEmbeddingCLM J)

@[simp]
lemma embedding_apply (J : A →CP B(H)) (h : H) :
    embedding J h = (preEmbedding J h : K J) := rfl

set_option backward.isDefEq.respectTransparency false in
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

noncomputable def seminormed (K : PositiveOperatorKernelData (A := A) (H := H)) :
    SeminormedAddCommGroup (A →₀ H) :=
  letI : PreInnerProductSpace.Core ℂ (A →₀ H) := K.core
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := K.core)

noncomputable def innerProductSpace (K : PositiveOperatorKernelData (A := A) (H := H)) :
    @InnerProductSpace ℂ (A →₀ H) inferInstance (K.seminormed) := by
  letI : PreInnerProductSpace.Core ℂ (A →₀ H) := K.core
  letI : Inner ℂ (A →₀ H) := ⟨K.kernelInner⟩
  letI : SeminormedAddCommGroup (A →₀ H) := K.seminormed
  exact InnerProductSpace.ofCore K.core

namespace Canonical

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

noncomputable def preEmbeddingCLM (K : PositiveOperatorKernelData (A := A) (H := H))
    (a : A) : H →L[ℂ] Pre K :=
  (preEmbedding K a).mkContinuous (Real.sqrt ‖K.kernel a a‖)
    (preEmbedding_norm_le K a)

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

namespace PositiveOperatorKernelData.Canonical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open ContinuousLinearMap

/-! ### The Evans--Lewis cocycle action

For an Evans--Lewis kernel the canonical vectors satisfy a cocycle identity.  The resulting action
is the representation action on the defect space; its bounded extension is developed below. -/

def HasKernelCocycle
    (K : PositiveOperatorKernelData (A := B(H)) (H := H)) : Prop :=
  ∀ a c d : B(H),
    K.kernel (a * c) d - star c * K.kernel a d =
      K.kernel c (star a * d) - K.kernel c (star a) * d

def HasKernelZeroOne
    (K : PositiveOperatorKernelData (A := B(H)) (H := H)) : Prop :=
  (∀ b : B(H), K.kernel 1 b = 0) ∧ (∀ a : B(H), K.kernel a 1 = 0)

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
  map : B(H) → Completion K →L[ℂ] Completion K
  map_add : ∀ a b, map (a + b) = map a + map b
  map_smul : ∀ (r : ℂ) (a : B(H)), map (r • a) = r • map a
  map_mul : ∀ a b, map (a * b) = (map a).comp (map b)
  map_star : ∀ a, map (star a) = (map a).adjoint
  map_one : map 1 = ContinuousLinearMap.id ℂ (Completion K)

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

abbrev EvansLewisKernelHilbert
    (L : B(H) →L[ℂ] B(H))
    (hstar : ∀ a : B(H), star (L a) = L (star a))
    (hpositive : IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b)) :=
  PositiveOperatorKernelData.Canonical.Completion
    (evansLewisKernelData L hstar hpositive)

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

namespace MatrixVectorState

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The vector-state functional obtained by evaluating a matrix at one diagonal entry.

This is the concrete positive functional used to turn matrix-compression CCP into Hilbert-space
quadratic inequalities.  Positivity of the selected diagonal entry is proved directly from the
`StarOrderedRing` description of the positive cone. -/
noncomputable def diagonal
    {n : Type*} [Fintype n] [DecidableEq n]
    (ψ : H) (hψ : ‖ψ‖ = 1) (i : n) :
    CStarMatrix n n (B(H)) →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun M => vectorState ψ hψ (M i i)
      map_add' := by
        intro M N
        simp
      map_smul' := by
        intro c M
        simp }
    (by
      intro M hM
      have hentry : 0 ≤ M i i := by
        rw [StarOrderedRing.nonneg_iff] at hM
        induction hM using AddSubmonoid.closure_induction with
        | mem x hx =>
            obtain ⟨s, rfl⟩ := hx
            change 0 ≤ (star s * s) i i
            simp only [CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply]
            exact Finset.sum_nonneg (fun j _ => star_mul_self_nonneg _)
        | zero => simp
        | add x y _ _ hx hy =>
            exact add_nonneg hx hy
      exact (vectorState ψ hψ).toPositiveLinearMap.map_nonneg hentry)

@[simp]
lemma diagonal_apply
    {n : Type*} [Fintype n] [DecidableEq n]
    (ψ : H) (hψ : ‖ψ‖ = 1) (i : n) (M : CStarMatrix n n (B(H))) :
    diagonal ψ hψ i M = inner ℂ ψ (M i i ψ) := by
  rfl

end MatrixVectorState

namespace StinespringWitness

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {J : B(H) →CP B(H)}

set_option maxHeartbeats 800000

/-! The CCP-to-kernel step uses the existing bounded-operator representation and
rank-one operators.  It does not introduce any new domain or spectral machinery. -/

lemma ccp_implies_evansLewis_kernel_positive
    [Nontrivial H] (L : B(H) →L[ℂ] B(H))
    (hL1 : L 1 = 0)
    (hccp : IsConditionallyCompletelyPositiveBounded L) :
    IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b) := by
  let e₀ : H := Classical.choose (exists_ne (0 : H))
  have he₀ : e₀ ≠ 0 := Classical.choose_spec (exists_ne (0 : H))
  let e : H := ‖e₀‖⁻¹ • e₀
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, norm_inv]
    simp [norm_ne_zero_iff.mpr he₀]
  intro n a x
  let aa : Fin (n + 1) → B(H) := Fin.cons 1 a
  let cc : Fin (n + 1) → B(H) :=
    Fin.cons (-∑ i, a i * InnerProductSpace.rankOne ℂ (x i) e)
      (fun i => InnerProductSpace.rankOne ℂ (x i) e)
  have hzero : ∑ i, aa i * cc i = 0 := by
    simp [aa, cc, Fin.sum_univ_succ, Finset.mul_sum, ← Finset.sum_mul]
  have hp := CCPMatrix.ccp_column_compression L hccp aa cc hzero
    (MatrixVectorState.diagonal e he 0)
  change 0 ≤ Complex.re (inner ℂ e
    (((CStarMatrix.conjTranspose (CCPMatrix.column cc) *
      ((CStarMatrix.conjTranspose (CCPMatrix.row aa) * CCPMatrix.row aa).map L) *
      CCPMatrix.column cc) 0 0) e)) at hp
  rw [CCPMatrix.column_gram_compression_apply_zero] at hp
  change 0 ≤ Complex.re (inner ℂ e
    ((∑ i, ∑ j, star (cc i) * L (star (aa i) * aa j) * cc j) e)) at hp
  have hEval (i : Fin n) (y : H) :
      inner ℂ e
          ((ContinuousLinearMap.adjoint
            (a i * InnerProductSpace.rankOne ℂ (x i) e)) y) =
        inner ℂ (x i) ((ContinuousLinearMap.adjoint (a i)) y) := by
    rw [← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint]
    simp [star_mul, ContinuousLinearMap.star_eq_adjoint,
      InnerProductSpace.adjoint_rankOne, InnerProductSpace.rankOne_apply,
      inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, he]
  have heq : inner ℂ e
      ((∑ i, ∑ j, star (cc i) * L (star (aa i) * aa j) * cc j) e) =
      ∑ i, ∑ j, inner ℂ (x i) (evansLewisKernel L (a i) (a j) (x j)) := by
    simp [aa, cc, evansLewisKernel, Fin.sum_univ_succ, Finset.sum_mul,
      Finset.mul_sum, star_sum, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_one, he, InnerProductSpace.adjoint_rankOne,
      InnerProductSpace.rankOne_apply,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      hL1, hEval, mul_assoc]
    have hQ :
        (∑ i, ∑ j, inner ℂ (x j)
          ((ContinuousLinearMap.adjoint (a j)) ((L (a i)) (x i)))) =
        ∑ i, ∑ j, inner ℂ (x i)
          ((ContinuousLinearMap.adjoint (a i)) ((L (a j)) (x j))) := by
      rw [Finset.sum_comm]
    rw [hQ]
    rw [Finset.sum_add_distrib]
    norm_num
    abel
  rw [heq] at hp
  exact hp

/-- A defect Gram kernel is positive. -/
lemma defect_gram_isPositiveOperatorKernel
    (W : StinespringWitness (B(H)) H K J) :
    IsPositiveOperatorKernel (fun a b =>
      ContinuousLinearMap.adjoint (W.defect a) ∘L W.defect b) := by
  intro n a x
  have hsum :
      (∑ i, ∑ j, inner ℂ (x i)
        ((ContinuousLinearMap.adjoint (W.defect (a i)) ∘L W.defect (a j)) (x j))) =
        inner ℂ (∑ i, W.defect (a i) (x i))
          (∑ j, W.defect (a j) (x j)) := by
    simp only [ContinuousLinearMap.comp_apply]
    simp_rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [inner_sum, sum_inner]
    rw [Finset.sum_comm]
  rw [hsum]
  let z : K := ∑ i, W.defect (a i) (x i)
  change 0 ≤ Complex.re (inner ℂ z z)
  exact inner_self_nonneg (𝕜 := ℂ) (E := K) (x := z)

/-- The Evans--Lewis kernel of a Christensen--Evans generator is positive. -/
lemma evansLewisKernel_generator_isPositiveOperatorKernel
    (W : StinespringWitness (B(H)) H K J) (h : Observable B(H)) :
    IsPositiveOperatorKernel (fun a b =>
      evansLewisKernel (W.toChristensenEvansData h).generator a b) := by
  intro n a x
  simpa only [W.evansLewisKernel_generator_eq_defect_gram] using
    W.defect_gram_isPositiveOperatorKernel n a x

set_option maxHeartbeats 800000

/-- A bounded derivation on `B(H)` is implemented by a bounded operator.

The proof uses one rank-one operator `|x⟩⟨e|` for a fixed unit vector `e`.  It is deliberately
kept independent of any spectral or unbounded-operator infrastructure. -/
lemma exists_inner_implementer
    [Nontrivial H] (L : B(H) →L[ℂ] B(H))
    (hL : ∀ a b : B(H), L (a * b) = L a * b + a * L b) :
    ∃ T : B(H), ∀ (a : B(H)) (x : H), L a x = T (a x) - a (T x) := by
  let e₀ : H := Classical.choose (exists_ne (0 : H))
  have he₀ : e₀ ≠ 0 := Classical.choose_spec (exists_ne (0 : H))
  let e : H := ‖e₀‖⁻¹ • e₀
  have he : ‖e‖ = 1 := by
    dsimp [e]
    rw [norm_smul, norm_inv]
    simp [norm_ne_zero_iff.mpr he₀]
  let Tlin : H →ₗ[ℂ] H :=
    { toFun := fun x => L (InnerProductSpace.rankOne ℂ x e) e
      map_add' := by
        intro x y
        have hxy :
            InnerProductSpace.rankOne ℂ (x + y) e =
              InnerProductSpace.rankOne ℂ x e + InnerProductSpace.rankOne ℂ y e := by
          ext z
          simp [InnerProductSpace.rankOne_apply, add_smul]
        rw [hxy, map_add]
        rfl
      map_smul' := by
        intro c x
        have hcx :
            InnerProductSpace.rankOne ℂ (c • x) e =
              c • InnerProductSpace.rankOne ℂ x e := by
          ext z
          simp [InnerProductSpace.rankOne_apply, smul_smul]
        change L (InnerProductSpace.rankOne ℂ (c • x) e) e =
          c • L (InnerProductSpace.rankOne ℂ x e) e
        rw [hcx]
        simpa using congrArg (fun z : B(H) => z e)
          (L.map_smul c (InnerProductSpace.rankOne ℂ x e)) }
  have hTbound : ∀ x : H, ‖Tlin x‖ ≤ ‖L‖ * ‖x‖ := by
    intro x
    calc
      ‖Tlin x‖ = ‖L (InnerProductSpace.rankOne ℂ x e) e‖ := rfl
      _ ≤ ‖L (InnerProductSpace.rankOne ℂ x e)‖ * ‖e‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖L‖ * ‖InnerProductSpace.rankOne ℂ x e‖) * ‖e‖ := by
        exact mul_le_mul_of_nonneg_right
          (ContinuousLinearMap.le_opNorm L _) (norm_nonneg _)
      _ = ‖L‖ * ‖x‖ := by
        rw [InnerProductSpace.norm_rankOne, he]
        ring
  let T : B(H) := LinearMap.mkContinuousOfExistsBound Tlin
    (Exists.intro ‖L‖ (by intro x; exact hTbound x))
  have hT_apply (x : H) : T x = L (InnerProductSpace.rankOne ℂ x e) e := by
    rfl
  have hRank (a : B(H)) (x : H) :
      InnerProductSpace.rankOne ℂ (a x) e = a * InnerProductSpace.rankOne ℂ x e := by
    ext z
    simp [mul_apply_eq_comp, InnerProductSpace.rankOne_apply]
  have hRank_e (x : H) :
      InnerProductSpace.rankOne ℂ x e e = x := by
    simp [InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, he]
  refine ⟨T, ?_⟩
  intro a x
  have hOp := hL a (InnerProductSpace.rankOne ℂ x e)
  rw [← hRank a x] at hOp
  have h := congrArg (fun z : B(H) => z e) hOp
  simp only [add_apply, mul_apply_eq_comp, ContinuousLinearMap.comp_apply] at h
  rw [hRank_e x] at h
  rw [← hT_apply (a x), ← hT_apply x] at h
  exact (eq_sub_iff_add_eq).2 h.symm

set_option maxHeartbeats 800000

/-- A star-preserving bounded derivation on `B(H)` is a Hamiltonian commutator. -/
lemma exists_selfAdjoint_inner_implementer
    [Nontrivial H] (L : B(H) →L[ℂ] B(H))
    (hL : ∀ a b : B(H), L (a * b) = L a * b + a * L b)
    (hstar : ∀ a : B(H), star (L a) = L (star a)) :
    ∃ h : Observable (B(H)), ∀ a : B(H), L a = hamiltonianPartOf h a := by
  obtain ⟨T, hT⟩ := exists_inner_implementer L hL
  have hD (a : B(H)) : L a = T * a - a * T := by
    ext x
    simpa [mul_apply_eq_comp, sub_apply] using hT a x
  have hcomm_star (a : B(H)) :
      (T + star T) * star a = star a * (T + star T) := by
    have hs := hstar a
    rw [hD a, hD (star a)] at hs
    simp only [star_sub, star_mul, star_star] at hs
    have hs' := sub_eq_sub_iff_add_eq_add.mp hs
    calc
      (T + star T) * star a = T * star a + star T * star a := by rw [add_mul]
      _ = star a * T + star a * star T := by
        simpa [add_comm, add_left_comm, add_assoc] using hs'.symm
      _ = star a * (T + star T) := by rw [mul_add]
  have hcomm (a : B(H)) :
      (T + star T) * a = a * (T + star T) := by
    simpa using hcomm_star (star a)
  let S : B(H) := (2 : ℂ)⁻¹ • (T - star T)
  have hDS (a : B(H)) : L a = S * a - a * S := by
    rw [hD]
    have hinner :
        ((T - star T) * a - a * (T - star T)) +
            ((T + star T) * a - a * (T + star T)) =
          (T * a - a * T) + (T * a - a * T) := by
      noncomm_ring
    have hfactor :
        ((2 : ℂ)⁻¹ • (T - star T)) * a -
            a * ((2 : ℂ)⁻¹ • (T - star T)) +
            (2 : ℂ)⁻¹ • ((T + star T) * a - a * (T + star T)) =
          (2 : ℂ)⁻¹ •
            (((T - star T) * a - a * (T - star T)) +
              ((T + star T) * a - a * (T + star T))) := by
      simp only [smul_mul_assoc, mul_smul_comm]
      rw [← smul_sub, ← smul_add]
    calc
      T * a - a * T =
          (2 : ℂ)⁻¹ •
            (((T - star T) * a - a * (T - star T)) +
              ((T + star T) * a - a * (T + star T))) := by
            rw [hinner, ← two_smul ℂ (T * a - a * T)]
            simp [smul_smul]
      _ = ((2 : ℂ)⁻¹ • (T - star T)) * a -
            a * ((2 : ℂ)⁻¹ • (T - star T)) +
            (2 : ℂ)⁻¹ • ((T + star T) * a - a * (T + star T)) := hfactor.symm
      _ = S * a - a * S := by
        dsimp [S]
        rw [hcomm]
        simp
  have hSstar : star S = -S := by
    simp only [S, star_sub, star_smul]
    norm_num
    module
  let h : B(H) := -Complex.I • S
  have hh : star h = h := by
    simp [h, star_smul, hSstar]
  refine ⟨⟨h, hh⟩, ?_⟩
  intro a
  rw [hamiltonianPartOf_apply]
  rw [hDS]
  simp [h, smul_mul_assoc, mul_smul_comm, smul_smul]
  module

set_option maxHeartbeats 800000

/-- Kernel factorisation reduces the bounded Christensen--Evans converse to the derivation case.

The hypothesis is intentionally stated at the Evans--Lewis-kernel level: it is the exact
representation-free interface supplied by the preceding CCP-to-kernel theorem once its
factorisation datum is available. -/
lemma isChristensenEvansGenerator_of_evansLewisKernel_factorization
    [Nontrivial H] (L : B(H) →L[ℂ] B(H)) (hL1 : L 1 = 0)
    (hstar : ∀ a : B(H), star (L a) = L (star a))
    (J : B(H) →CP B(H))
    (W : StinespringWitness (B(H)) H K J)
    (hkernel : ∀ a b : B(H),
      evansLewisKernel L a b =
        evansLewisKernel (W.toChristensenEvansData ⟨0, by simp⟩).generator a b) :
    IsChristensenEvansGenerator L := by
  let G : B(H) →L[ℂ] B(H) :=
    (W.toChristensenEvansData ⟨0, by simp⟩).generator
  let R : B(H) →L[ℂ] B(H) := L - G
  have hR1 : R 1 = 0 := by
    dsimp [R, G]
    change L 1 - (W.toChristensenEvansData ⟨0, by simp⟩).generator 1 = 0
    rw [hL1, ChristensenEvansData.generator_apply_one, sub_zero]
  have hRstar : ∀ a : B(H), star (R a) = R (star a) := by
    intro a
    dsimp [R, G]
    change star (L a - (W.toChristensenEvansData ⟨0, by simp⟩).generator a) =
      L (star a) - (W.toChristensenEvansData ⟨0, by simp⟩).generator (star a)
    rw [star_sub, hstar, ChristensenEvansData.generator_star]
  have hRkernel : ∀ a b : B(H), evansLewisKernel R a b = 0 := by
    intro a b
    calc
      evansLewisKernel R a b = evansLewisKernel L a b - evansLewisKernel G a b := by
        dsimp [R]
        simp [evansLewisKernel, map_sub, sub_mul, mul_sub, add_sub_assoc,
          sub_eq_add_neg, add_mul, mul_add]
        noncomm_ring
      _ = 0 := sub_eq_zero.mpr (hkernel a b)
  have hRderiv : ∀ a b : B(H), R (a * b) = R a * b + a * R b :=
    leibniz_of_evansLewisKernel_eq_zero R hR1 hRkernel
  obtain ⟨h, hh⟩ := exists_selfAdjoint_inner_implementer R hRderiv hRstar
  refine ⟨{hamiltonian := h, jump := J}, ?_⟩
  apply ContinuousLinearMap.ext
  intro a
  have hsplit : L a = R a + G a := by
    dsimp [R]
    simp
  rw [hsplit, hh]
  rw [ChristensenEvansData.generator_apply,
    ChristensenEvansData.generator_apply]
  dsimp [G]
  have hham0 :
      (W.toChristensenEvansData ⟨0, by simp⟩).hamiltonian =
        (⟨0, by simp⟩ : Observable (B(H))) := rfl
  have hJ (x : B(H)) :
      (W.toChristensenEvansData ⟨0, by simp⟩).jump x = J x := rfl
  rw [hham0]
  simp only [hJ, zero_mul, mul_zero, sub_zero, zero_smul, add_zero]
  simp [hamiltonianPartOf_apply]
  noncomm_ring

/-! ### Packaged factorisation data -/

/-- A Stinespring witness for the positive Evans--Lewis kernel of a bounded map.

This is the exact infinite-dimensional datum still needed after the CCP-to-kernel theorem.  The
auxiliary Hilbert space is left as a parameter so that the object can be instantiated by a future
Arveson/Christensen--Evans factorisation without changing the generator API. -/
structure EvansLewisKernelFactorization
    (L : B(H) →L[ℂ] B(H)) where
  /-- The completely positive jump map. -/
  jump : B(H) →CP B(H)
  /-- A Stinespring witness for the jump map. -/
  witness : StinespringWitness (B(H)) H K jump
  /-- Equality of the given Evans--Lewis kernel with the witness kernel. -/
  kernel_eq : ∀ a b : B(H),
    evansLewisKernel L a b =
      evansLewisKernel
        (witness.toChristensenEvansData ⟨0, by simp⟩).generator a b

namespace ChristensenEvansData

/-- The canonical Stinespring witness turns any Christensen--Evans datum into a packaged
Evans--Lewis factorisation. -/
noncomputable def toEvansLewisKernelFactorization
    (D : ChristensenEvansData (B(H))) :
    EvansLewisKernelFactorization
      (K := TensorStinespring.Canonical.K D.jump) D.generator where
  jump := D.jump
  witness := TensorStinespring.Canonical.canonicalWitness D.jump
  kernel_eq := by
    intro a b
    change evansLewisKernel
        ((TensorStinespring.Canonical.canonicalWitness D.jump).toChristensenEvansData
          D.hamiltonian).generator a b = _
    rw [StinespringWitness.evansLewisKernel_generator_eq_cpKernel
      (TensorStinespring.Canonical.canonicalWitness D.jump) D.hamiltonian]
    rw [StinespringWitness.evansLewisKernel_generator_eq_cpKernel
      (TensorStinespring.Canonical.canonicalWitness D.jump) (Subtype.mk 0 (by simp))]

end ChristensenEvansData

set_option maxHeartbeats 800000

/-- A packaged Evans--Lewis factorisation produces Christensen--Evans data. -/
lemma EvansLewisKernelFactorization.isChristensenEvansGenerator
    [Nontrivial H] (F : EvansLewisKernelFactorization (K := K) L)
    (hL1 : L 1 = 0)
    (hstar : ∀ a : B(H), star (L a) = L (star a)) :
    IsChristensenEvansGenerator L := by
  exact isChristensenEvansGenerator_of_evansLewisKernel_factorization
    L hL1 hstar F.jump F.witness F.kernel_eq

set_option maxHeartbeats 800000 in
/-- The canonical Evans--Lewis implementer supplies the kernel equality required by the
Christensen--Evans converse when its CP compression is presented by a Stinespring witness.

The auxiliary Hilbert space is fixed to the canonical kernel completion.  Thus this is the exact
bridge from the reusable positive-kernel construction to the existing Christensen--Evans API. -/
lemma isChristensenEvansGenerator_of_kernel_implementer
    [Nontrivial H]
    (L : B(H) →L[ℂ] B(H)) (hL1 : L 1 = 0)
    (hstar : ∀ a : B(H), star (L a) = L (star a))
    (hpositive : IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b))
    {J : B(H) →CP B(H)}
    (W : StinespringWitness (B(H)) H
      (EvansLewisKernelHilbert L hstar hpositive) J)
    (himplementer : ∀ (a : B(H)) (x : H),
      evansLewisKernelEmbedding L hstar hpositive a x = W.defect a x) :
    IsChristensenEvansGenerator L := by
  apply isChristensenEvansGenerator_of_evansLewisKernel_factorization
    L hL1 hstar J W
  intro a b
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  calc
    inner ℂ y (evansLewisKernel L a b x) =
        inner ℂ (evansLewisKernelEmbedding L hstar hpositive a y)
          (evansLewisKernelEmbedding L hstar hpositive b x) := by
      symm
      exact evansLewisKernelEmbedding_inner L hstar hpositive a b y x
    _ = inner ℂ (W.defect a y) (W.defect b x) := by
      rw [himplementer, himplementer]
    _ = inner ℂ y
        ((ContinuousLinearMap.adjoint (W.defect a) ∘L W.defect b) x) := by
      rw [ContinuousLinearMap.comp_apply]
      exact (ContinuousLinearMap.adjoint_inner_right (W.defect a) y
        (W.defect b x)).symm
    _ = inner ℂ y
        (evansLewisKernel (W.toChristensenEvansData ⟨0, by simp⟩).generator a b x) := by
      rw [W.evansLewisKernel_generator_eq_defect_gram]

/-- A factorisation witness certifies positivity of the Evans--Lewis kernel. -/
lemma EvansLewisKernelFactorization.isPositiveOperatorKernel
    (L : B(H) →L[ℂ] B(H))
    (F : EvansLewisKernelFactorization (K := K) L) :
    IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b) := by
  have hEq : (fun a b => evansLewisKernel L a b) =
      (fun a b => evansLewisKernel
        (F.witness.toChristensenEvansData ⟨0, by simp⟩).generator a b) := by
    funext a b
    exact F.kernel_eq a b
  rw [hEq]
  exact F.witness.evansLewisKernel_generator_isPositiveOperatorKernel
    ⟨0, by simp⟩

/-! ### Positivity reflection for finite operator matrices

The order on `CStarMatrix (Fin n) (Fin n) (B(H))` is the C⋆-algebra order, while the concrete
block representation acts on a finite Hilbert sum.  The following inverse identifies the two
presentations.  This is the small analytic lemma needed when proving that a Stinespring compression
is completely positive. -/

noncomputable def piLpSingleCLM (n : ℕ) (j : Fin n) :
    H →L[ℂ] PiLp 2 (fun _ : Fin n => H) := by
  let s : H →ₗ[ℂ] PiLp 2 (fun _ : Fin n => H) :=
    { toFun := fun x => PiLp.single 2 j x
      map_add' := by
        intro x y
        exact PiLp.single_add 2 j
      map_smul' := by
        intro c x
        apply PiLp.ext
        intro i
        by_cases h : i = j
        · subst i
          simp
        · rw [PiLp.single_eq_of_ne 2 h]
          rw [PiLp.smul_apply, PiLp.single_eq_of_ne 2 h]
          simp }
  exact s.mkContinuous 1 (by
    intro x
    change ‖(PiLp.single 2 j x : PiLp 2 (fun _ : Fin n => H))‖ ≤ 1 * ‖x‖
    rw [PiLp.norm_single]
    simp)

@[simp]
lemma piLpSingleCLM_apply (n : ℕ) (j : Fin n) (x : H) :
    piLpSingleCLM n j x = PiLp.single 2 j x := by
  change (piLpSingleCLM n j) x = PiLp.single 2 j x
  simp [piLpSingleCLM]

noncomputable def blockMatrixInverse
    {n : ℕ} (T : B(PiLp 2 (fun _ : Fin n => H))) :
    CStarMatrix (Fin n) (Fin n) B(H) := fun i j =>
      (PiLp.proj 2 (fun _ : Fin n => H) i).comp
        (T.comp (piLpSingleCLM n j))

@[simp]
lemma blockMatrixInverse_apply
    {n : ℕ} (T : B(PiLp 2 (fun _ : Fin n => H)))
    (i j : Fin n) (x : H) :
    blockMatrixInverse T i j x = (T (PiLp.single 2 j x)) i := by
  simp [blockMatrixInverse, piLpSingleCLM_apply]

lemma blockMatrixMap_inverse
    {n : ℕ} (T : B(PiLp 2 (fun _ : Fin n => H))) :
    blockMatrixMap (blockMatrixInverse T) = T := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  have hx : x = ∑ j : Fin n, PiLp.single 2 j (x j) := by
    apply PiLp.ext
    intro k
    simp [Finset.sum_apply]
  rw [blockMatrixMap_apply]
  have hTx : T x = ∑ j : Fin n, T (PiLp.single 2 j (x j)) := by
    calc
      T x = T (∑ j : Fin n, PiLp.single 2 j (x j)) := congrArg T hx
      _ = ∑ j : Fin n, T (PiLp.single 2 j (x j)) := by
        rw [map_sum]
  rw [hTx]
  simp_rw [blockMatrixInverse_apply]
  simpa only [Finset.sum_apply] using congrArg (fun f : ∀ _ : Fin n, H => f i)
    (WithLp.ofLp_sum 2 (∀ _ : Fin n, H) Finset.univ
      (fun j : Fin n => T (PiLp.single 2 j (x.ofLp j)))).symm

lemma blockMatrixMap_injective
    {n : ℕ} : Function.Injective
      (blockMatrixMap (H := H) (n := n)) := by
  intro M N h
  apply CStarMatrix.ext
  intro i j
  apply ContinuousLinearMap.ext
  intro x
  have h' := congrArg (fun T : B(PiLp 2 (fun _ : Fin n => H)) =>
      (T (PiLp.single 2 j x : PiLp 2 (fun _ : Fin n => H))) i) h
  have hM : ∑ k : Fin n, M i k
      ((PiLp.single 2 j x : PiLp 2 (fun _ : Fin n => H)) k) = M i j x := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [Ne.symm hkj]
    · simp
  have hN : ∑ k : Fin n, N i k
      ((PiLp.single 2 j x : PiLp 2 (fun _ : Fin n => H)) k) = N i j x := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [Ne.symm hkj]
    · simp
  rw [blockMatrixMap_apply, blockMatrixMap_apply] at h'
  rw [Finset.sum_eq_single j] at h'
  · rw [Finset.sum_eq_single j] at h'
    · simpa using h'
    · intro k hk hkj
      simp [Ne.symm hkj]
    · simp
  · intro k hk hkj
    simp [Ne.symm hkj]
  · simp

lemma blockMatrixMap_nonneg_iff
    {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) B(H)) :
    0 ≤ M ↔ 0 ≤ blockMatrixMap M := by
  constructor
  · intro hM
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (blockMatrixMap_isPositive hM)
  · intro hT
    have hs : IsSelfAdjoint (blockMatrixMap M) := IsSelfAdjoint.of_nonneg hT
    have hq : QuasispectrumRestricts (blockMatrixMap M)
        ContinuousMap.realToNNReal := QuasispectrumRestricts.nnreal_of_nonneg hT
    obtain ⟨S, hSstar, hSsq⟩ :=
      CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hs hq
    let N := blockMatrixInverse S
    have hN : blockMatrixMap N = S := blockMatrixMap_inverse S
    have hfactor : M = star N * N := by
      apply blockMatrixMap_injective
      rw [blockMatrixMap_mul, blockMatrixMap_star, hN]
      calc
        blockMatrixMap M = S * S := hSsq.2.symm
        _ = (ContinuousLinearMap.adjoint S) ∘L S := by
          change S * S = (star S) ∘L S
          rw [hSstar.star_eq]
          apply ContinuousLinearMap.ext
          intro x
          rfl
    rw [hfactor]
    exact star_mul_self_nonneg N

/-! ### CP compression by a rectangular implementing operator

The usual Stinespring compression does not require the implementing operator to be an element of
the source algebra.  This is the form needed for the converse: the canonical representation acts
on the Evans--Lewis Hilbert space, while its defect maps the physical Hilbert space into it. -/

noncomputable def piLpMap
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {n : ℕ} (V : H →L[ℂ] K) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => K) := by
  let eH : PiLp 2 (fun _ : Fin n => H) ≃L[ℂ] (∀ _ : Fin n, H) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)
  let eK : PiLp 2 (fun _ : Fin n => K) ≃L[ℂ] (∀ _ : Fin n, K) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => K)
  let p : (∀ _ : Fin n, H) →L[ℂ] (∀ _ : Fin n, K) :=
    ContinuousLinearMap.piMap (fun _ : Fin n => V)
  exact eK.symm.toContinuousLinearMap.comp (p.comp eH.toContinuousLinearMap)

@[simp]
lemma piLpMap_apply
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {n : ℕ} (V : H →L[ℂ] K)
    (x : PiLp 2 (fun _ : Fin n => H)) (i : Fin n) :
    (piLpMap V x).ofLp i = V (x.ofLp i) := by
  simp [piLpMap]

noncomputable def compressionLinearMap
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : Representation (B(H)) K) (V : H →L[ℂ] K) :
    B(H) →ₗ[ℂ] B(H) where
  toFun a := ContinuousLinearMap.adjoint V ∘L (π a) ∘L V
  map_add' a b := by
    ext x
    simp [ContinuousLinearMap.comp_apply, map_add]
  map_smul' c a := by
    ext x
    simp [ContinuousLinearMap.comp_apply, map_smul]

lemma compressionLinearMap_apply
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : Representation (B(H)) K) (V : H →L[ℂ] K) (a : B(H)) :
    compressionLinearMap π V a =
      ContinuousLinearMap.adjoint V ∘L (π a) ∘L V :=
  rfl

lemma compressionLinearMap_star
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : Representation (B(H)) K) (V : H →L[ℂ] K) (a : B(H)) :
    compressionLinearMap π V (star a) =
      star (compressionLinearMap π V a) := by
  change ContinuousLinearMap.adjoint V ∘L (π (star a)) ∘L V = _
  change _ = ContinuousLinearMap.adjoint
    (ContinuousLinearMap.adjoint V ∘L (π a) ∘L V)
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
  rw [map_star]
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  rfl

noncomputable def compressionContinuousLinearMap
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : Representation (B(H)) K) (V : H →L[ℂ] K) :
    B(H) →L[ℂ] B(H) := by
  refine (compressionLinearMap π V).mkContinuous (‖V‖ * ‖V‖) ?_
  intro a
  calc
    ‖compressionLinearMap π V a‖ ≤
        ‖ContinuousLinearMap.adjoint V‖ * ‖π a‖ * ‖V‖ := by
      rw [compressionLinearMap_apply]
      change ‖(ContinuousLinearMap.adjoint V ∘L π a) ∘L V‖ ≤ _
      calc
        ‖(ContinuousLinearMap.adjoint V ∘L π a) ∘L V‖ ≤
            ‖ContinuousLinearMap.adjoint V ∘L π a‖ * ‖V‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖ContinuousLinearMap.adjoint V‖ * ‖π a‖) * ‖V‖ := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖V‖ * ‖V‖ * ‖a‖ := by
      calc
        ‖ContinuousLinearMap.adjoint V‖ * ‖π a‖ * ‖V‖ =
            ‖V‖ * ‖π a‖ * ‖V‖ := by
          rw [ContinuousLinearMap.adjoint.norm_map]
        _ ≤ ‖V‖ * ‖a‖ * ‖V‖ := by
          gcongr
          exact NonUnitalStarAlgHom.norm_apply_le π a
        _ = ‖V‖ * ‖V‖ * ‖a‖ := by ring

@[simp]
lemma compressionContinuousLinearMap_apply
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : Representation (B(H)) K) (V : H →L[ℂ] K) (a : B(H)) :
    compressionContinuousLinearMap π V a =
      ContinuousLinearMap.adjoint V ∘L (π a) ∘L V := by
  rfl

lemma compressionContinuousLinearMap_star
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : Representation (B(H)) K) (V : H →L[ℂ] K) (a : B(H)) :
    compressionContinuousLinearMap π V (star a) =
      star (compressionContinuousLinearMap π V a) := by
  change compressionLinearMap π V (star a) = star (compressionLinearMap π V a)
  exact compressionLinearMap_star π V a

noncomputable def compressionCPMap
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (π : Representation (B(H)) K) (V : H →L[ℂ] K) :
    B(H) →CP B(H) := by
  refine { toLinearMap := compressionContinuousLinearMap π V, map_cstarMatrix_nonneg' := ?_ }
  intro n M hM
  apply (blockMatrixMap_nonneg_iff (M.map (compressionContinuousLinearMap π V))).mpr
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  refine (ContinuousLinearMap.isPositive_iff' _).mpr ⟨?_, ?_⟩
  · rw [isSelfAdjoint_iff]
    change (blockMatrixMap (M.map (compressionContinuousLinearMap π V))).adjoint = _
    rw [← blockMatrixMap_star]
    have hmat : star (M.map (compressionContinuousLinearMap π V)) =
        M.map (compressionContinuousLinearMap π V) := by
      apply CStarMatrix.ext
      intro i j
      simp only [CStarMatrix.star_apply, CStarMatrix.map_apply]
      rw [← compressionContinuousLinearMap_star]
      have hMstar : star M = M := (IsSelfAdjoint.of_nonneg hM).star_eq
      simpa only [CStarMatrix.star_apply] using
        congrArg (fun q => compressionContinuousLinearMap π V q)
          (congrArg (fun q => q i j) hMstar)
    rw [hmat]
  · intro x
    have hN : 0 ≤ M.map (π : B(H) → B(K)) :=
      CompletelyPositiveMapClass.map_cstarMatrix_nonneg' π n M hM
    have hblock := (blockMatrixMap_isPositive hN).inner_nonneg_left (piLpMap V x)
    have hblock' : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
        inner ℂ ((M.map (π : B(H) → B(K)) i j) (V (x.ofLp j))) (V (x.ofLp i)) := by
      simpa only [PiLp.inner_apply, blockMatrixMap_apply, piLpMap_apply,
        sum_inner, inner_sum] using hblock
    rw [PiLp.inner_apply]
    simp only [blockMatrixMap_apply, sum_inner]
    convert hblock' using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [CStarMatrix.map_apply]
    rw [compressionContinuousLinearMap_apply]
    simp only [ContinuousLinearMap.comp_apply]
    exact ContinuousLinearMap.adjoint_inner_left V (x.ofLp i)
      ((M.map (π : B(H) → B(K)) i j) (V (x.ofLp j)))

set_option maxHeartbeats 800000 in
/-- The positive Evans--Lewis kernel has a canonical completely positive compression.

The representation is the multiplicative action on the kernel completion and the implementing
operator is the defect factorisation constructed above.  This is the general bounded
Christensen--Evans converse on `B(H)`; no finite-dimensionality or Kraus basis is used. -/
lemma isChristensenEvansGenerator_of_positive_evansLewis_kernel
    [Nontrivial H]
    (L : B(H) →L[ℂ] B(H)) (hL1 : L 1 = 0)
    (hstar : ∀ a : B(H), star (L a) = L (star a))
    (hpositive : IsPositiveOperatorKernel (fun a b => evansLewisKernel L a b)) :
    IsChristensenEvansGenerator L := by
  obtain ⟨V, hV⟩ := exists_evansLewis_kernel_implementer L hL1 hstar hpositive
  let K := evansLewisKernelData L hstar hpositive
  let hK := evansLewisKernelData_hasKernelCocycle L hstar hpositive
  let h1 := evansLewisKernelData_hasKernelZeroOne L hstar hpositive
  let A := PositiveOperatorKernelData.Canonical.completionAction K hK h1
  let π := PositiveOperatorKernelData.Canonical.CompletionAction.representation K hK h1 A
  let J := compressionCPMap π V
  let W : StinespringWitness (B(H)) H (EvansLewisKernelHilbert L hstar hpositive) J :=
    { representation := π
      implementing := V
      map_eq := by
        intro a
        change compressionContinuousLinearMap π V a =
          ContinuousLinearMap.adjoint V ∘L (π a) ∘L V
        rfl }
  apply isChristensenEvansGenerator_of_kernel_implementer
    L hL1 hstar hpositive W
  intro a x
  rw [hV]
  rfl

end StinespringWitness

namespace BoundedQuantumDynamicalSemigroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Semigroup realization on bounded operators

The following theorem is the semigroup-level packaging of the preceding operator formula.  It
uses the existing exponential uniqueness theorem: once a Christensen--Evans datum has the same
bounded generator, its canonical UCP semigroup is exactly the given semigroup.
-/

lemma exists_canonical_stinespring_realization
    [Nontrivial (B(H))]
    (Φ : BoundedQuantumDynamicalSemigroup (B(H)))
    (hΦ : IsChristensenEvansGenerator Φ.generator) :
    ∃ D : ChristensenEvansData (B(H)), D.generator = Φ.generator ∧
      ∀ (t : NNReal) (a : B(H)),
        Φ.toQuantumDynamicalSemigroup.map t a =
          D.boundedQuantumDynamicalSemigroup.toQuantumDynamicalSemigroup.map t a := by
  obtain ⟨D, hD⟩ := hΦ
  refine ⟨D, hD, ?_⟩
  intro t a
  rw [Φ.map_eq_exp, D.boundedQuantumDynamicalSemigroup.map_eq_exp]
  change (NormedSpace.exp ((t : ℂ) • Φ.generator)) a =
    (NormedSpace.exp ((t : ℂ) • D.generator)) a
  rw [hD]

set_option maxHeartbeats 800000

/-- The bounded-semigroup form of the positive-shift converse.

This is the direct API for applications that already carry a bounded generator: a
Hamiltonian-adjusted completely-positive shift produces both the Christensen--Evans datum and
the matching channel-valued semigroup. -/
lemma exists_canonical_stinespring_of_hasHamiltonianCompletelyPositiveShift
    [Nontrivial (B(H))]
    (Φ : BoundedQuantumDynamicalSemigroup (B(H)))
    (hshift : HasHamiltonianCompletelyPositiveShift Φ.generator) :
    ∃ D : ChristensenEvansData (B(H)),
      D.generator = Φ.generator ∧
      ∀ (t : NNReal) (a : B(H)),
        Φ.toQuantumDynamicalSemigroup.map t a =
          D.boundedQuantumDynamicalSemigroup.toQuantumDynamicalSemigroup.map t a := by
  have hCE : IsChristensenEvansGenerator Φ.generator :=
    OperatorAlgebra.isChristensenEvansGenerator_of_hasHamiltonianCompletelyPositiveShift
      Φ.generator Φ.generator_isUnital hshift
  obtain ⟨D, hD, hmap⟩ := Φ.exists_canonical_stinespring_realization hCE
  exact ⟨D, hD, hmap⟩

end BoundedQuantumDynamicalSemigroup

namespace QuantumDynamicalSemigroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

set_option maxHeartbeats 800000

/-- The bounded generator of a norm-continuous UCP semigroup on `B(H)` has a positive
Evans--Lewis kernel.  This is the reusable infinitesimal input to the canonical factorisation
proved immediately below. -/
lemma generator_evansLewis_kernel_isPositive
    [Nontrivial H]
    (Φ : QuantumDynamicalSemigroup (B(H)))
    (hΦ : QuantumDynamicalSemigroup.IsNormContinuous Φ) :
    IsPositiveOperatorKernel (fun a b =>
      evansLewisKernel (Φ.toHasBoundedGenerator hΦ).generator a b) := by
  let G := Φ.toHasBoundedGenerator hΦ
  exact StinespringWitness.ccp_implies_evansLewis_kernel_positive
    G.generator G.generator_apply_one G.generator_isConditionallyCompletelyPositive

set_option maxHeartbeats 800000 in
/-- The bounded generator of every norm-continuous UCP semigroup on `B(H)` has
Christensen--Evans form.

The proof uses the canonical positive-kernel completion, its multiplicative completion action, and
the completely positive rectangular compression proved in `StinespringWitness`. -/
lemma generator_isChristensenEvans
    [Nontrivial H]
    (Φ : QuantumDynamicalSemigroup (B(H)))
    (hΦ : QuantumDynamicalSemigroup.IsNormContinuous Φ) :
    IsChristensenEvansGenerator (Φ.toHasBoundedGenerator hΦ).generator := by
  let G := Φ.toHasBoundedGenerator hΦ
  let hstar : ∀ a : B(H), star (G.generator a) = G.generator (star a) :=
    fun a => G.generator_map_star a
  let hpositive : IsPositiveOperatorKernel (fun a b =>
      evansLewisKernel G.generator a b) :=
    generator_evansLewis_kernel_isPositive Φ hΦ
  exact StinespringWitness.isChristensenEvansGenerator_of_positive_evansLewis_kernel
    G.generator G.generator_apply_one hstar hpositive

/-! ### The same realization for a raw norm-continuous QDS

`QuantumDynamicalSemigroup` is the natural input supplied by applications.  Norm continuity
provides the bounded exponential realization; the preceding theorem then supplies the canonical
Christensen--Evans/Stinespring semigroup whenever the genuine converse hypothesis is available.
-/

lemma exists_canonical_stinespring_realization
    [Nontrivial (B(H))]
    (Φ : QuantumDynamicalSemigroup (B(H)))
    (hΦ : QuantumDynamicalSemigroup.IsNormContinuous Φ)
    (hCE : IsChristensenEvansGenerator
      (Φ.toHasBoundedGenerator hΦ).generator) :
    ∃ D : ChristensenEvansData (B(H)),
      D.generator = (Φ.toHasBoundedGenerator hΦ).generator ∧
      ∀ (t : NNReal) (a : B(H)),
        Φ.map t a =
          D.boundedQuantumDynamicalSemigroup.toQuantumDynamicalSemigroup.map t a := by
  let Ψ : BoundedQuantumDynamicalSemigroup (B(H)) :=
    Φ.toBoundedQuantumDynamicalSemigroup hΦ
  have hCE' : IsChristensenEvansGenerator Ψ.generator := by
    simpa [Ψ, QuantumDynamicalSemigroup.toHasBoundedGenerator_generator] using hCE
  obtain ⟨D, hD, hmap⟩ := Ψ.exists_canonical_stinespring_realization hCE'
  refine ⟨D, ?_, ?_⟩
  · simpa [Ψ] using hD
  · intro t a
    change Φ.map t a =
      D.boundedQuantumDynamicalSemigroup.toQuantumDynamicalSemigroup.map t a
    exact hmap t a

set_option maxHeartbeats 800000 in
/-- Full bounded Lindblad/Christensen--Evans realization for a norm-continuous UCP semigroup.

Thus the semigroup is recovered from its completely positive jump map and bounded self-adjoint
Hamiltonian by the existing exponential construction. -/
lemma exists_canonical_stinespring_of_normContinuous
    [Nontrivial H]
    (Φ : QuantumDynamicalSemigroup (B(H)))
    (hΦ : QuantumDynamicalSemigroup.IsNormContinuous Φ) :
    ∃ D : ChristensenEvansData (B(H)),
      D.generator = (Φ.toHasBoundedGenerator hΦ).generator ∧
      ∀ (t : NNReal) (a : B(H)),
        Φ.map t a =
          D.boundedQuantumDynamicalSemigroup.toQuantumDynamicalSemigroup.map t a := by
  exact Φ.exists_canonical_stinespring_realization hΦ (Φ.generator_isChristensenEvans hΦ)

set_option maxHeartbeats 800000

/-- Semigroup-level form of the kernel-factorisation reduction.

For a norm-continuous QDS, this is the explicit factorisation interface for clients that already
have a witness.  The canonical `B(H)` factorisation is supplied by
`generator_isChristensenEvans` below. -/
lemma exists_canonical_stinespring_of_evansLewisKernel_factorization
    [Nontrivial H]
    (Φ : QuantumDynamicalSemigroup (B(H)))
    (hΦ : QuantumDynamicalSemigroup.IsNormContinuous Φ)
    (J : B(H) →CP B(H))
    (W : StinespringWitness (B(H)) H K J)
    (hkernel : ∀ a b : B(H),
      evansLewisKernel (Φ.toHasBoundedGenerator hΦ).generator a b =
        evansLewisKernel
          (W.toChristensenEvansData ⟨0, by simp⟩).generator a b) :
    ∃ D : ChristensenEvansData (B(H)),
      D.generator = (Φ.toHasBoundedGenerator hΦ).generator ∧
      ∀ (t : NNReal) (a : B(H)),
        Φ.map t a =
          D.boundedQuantumDynamicalSemigroup.toQuantumDynamicalSemigroup.map t a := by
  let G := Φ.toHasBoundedGenerator hΦ
  have hCE : IsChristensenEvansGenerator G.generator := by
    exact StinespringWitness.isChristensenEvansGenerator_of_evansLewisKernel_factorization
      G.generator G.generator_apply_one (fun a => G.generator_map_star a) J W hkernel
  exact Φ.exists_canonical_stinespring_realization hΦ hCE

set_option maxHeartbeats 800000

/-- Semigroup-level form using the canonical kernel implementer.

The positive Evans--Lewis kernel is constructed from the generator itself.  If a CP map and its
Stinespring witness realize the corresponding canonical defect implementer, the semigroup is the
Christensen--Evans/Lindblad semigroup generated by that witness. -/
lemma exists_canonical_stinespring_of_kernel_implementer
    [Nontrivial H]
    (Φ : QuantumDynamicalSemigroup (B(H)))
    (hΦ : QuantumDynamicalSemigroup.IsNormContinuous Φ)
    {J : B(H) →CP B(H)}
    (W : StinespringWitness (B(H)) H
      (StinespringWitness.EvansLewisKernelHilbert
        (Φ.toHasBoundedGenerator hΦ).generator
        (fun a => (Φ.toHasBoundedGenerator hΦ).generator_map_star a)
        (generator_evansLewis_kernel_isPositive Φ hΦ)) J)
    (himplementer : ∀ (a : B(H)) (x : H),
      StinespringWitness.evansLewisKernelEmbedding
          (Φ.toHasBoundedGenerator hΦ).generator
          (fun a => (Φ.toHasBoundedGenerator hΦ).generator_map_star a)
        (generator_evansLewis_kernel_isPositive Φ hΦ) a x =
        W.defect a x) :
    ∃ D : ChristensenEvansData (B(H)),
      D.generator = (Φ.toHasBoundedGenerator hΦ).generator ∧
      ∀ (t : NNReal) (a : B(H)),
        Φ.map t a =
          D.boundedQuantumDynamicalSemigroup.toQuantumDynamicalSemigroup.map t a := by
  let G := Φ.toHasBoundedGenerator hΦ
  let hstar : ∀ a : B(H), star (G.generator a) = G.generator (star a) :=
    fun a => G.generator_map_star a
  let hpositive : IsPositiveOperatorKernel (fun a b =>
      evansLewisKernel G.generator a b) :=
    generator_evansLewis_kernel_isPositive Φ hΦ
  have hCE : IsChristensenEvansGenerator G.generator := by
    exact StinespringWitness.isChristensenEvansGenerator_of_kernel_implementer
      G.generator G.generator_apply_one hstar hpositive W himplementer
  exact Φ.exists_canonical_stinespring_realization hΦ hCE

set_option maxHeartbeats 800000

/-- The packaged Evans--Lewis factorisation gives the canonical Lindblad/Christensen--Evans
realisation of a norm-continuous UCP semigroup. -/
lemma exists_canonical_stinespring_of_factorization
    [Nontrivial H]
    (Φ : QuantumDynamicalSemigroup (B(H)))
    (hΦ : QuantumDynamicalSemigroup.IsNormContinuous Φ)
    (F : StinespringWitness.EvansLewisKernelFactorization
      (K := K) (Φ.toHasBoundedGenerator hΦ).generator) :
    ∃ D : ChristensenEvansData (B(H)),
      D.generator = (Φ.toHasBoundedGenerator hΦ).generator ∧
      ∀ (t : NNReal) (a : B(H)),
        Φ.map t a =
          D.boundedQuantumDynamicalSemigroup.toQuantumDynamicalSemigroup.map t a := by
  let G := Φ.toHasBoundedGenerator hΦ
  have hCE : IsChristensenEvansGenerator G.generator :=
    F.isChristensenEvansGenerator G.generator_apply_one
      (fun a => G.generator_map_star a)
  exact Φ.exists_canonical_stinespring_realization hΦ hCE

set_option maxHeartbeats 800000

/-- A proved positive-shift certificate also yields the canonical Christensen--Evans realization
of a norm-continuous UCP semigroup.  This is the algebraic converse route that does not require a
separate choice of a Stinespring witness: the witness is supplied canonically after the shift
lemma produces Christensen--Evans data. -/
lemma exists_canonical_stinespring_of_hasHamiltonianCompletelyPositiveShift
    [Nontrivial H]
    (Φ : QuantumDynamicalSemigroup (B(H)))
    (hΦ : QuantumDynamicalSemigroup.IsNormContinuous Φ)
    (hshift : HasHamiltonianCompletelyPositiveShift
      (Φ.toHasBoundedGenerator hΦ).generator) :
    ∃ D : ChristensenEvansData (B(H)),
      D.generator = (Φ.toHasBoundedGenerator hΦ).generator ∧
      ∀ (t : NNReal) (a : B(H)),
        Φ.map t a =
          D.boundedQuantumDynamicalSemigroup.toQuantumDynamicalSemigroup.map t a := by
  let G := Φ.toHasBoundedGenerator hΦ
  have hCE : IsChristensenEvansGenerator G.generator :=
    OperatorAlgebra.isChristensenEvansGenerator_of_hasHamiltonianCompletelyPositiveShift
      G.generator G.generator_apply_one hshift
  exact Φ.exists_canonical_stinespring_realization hΦ hCE

end QuantumDynamicalSemigroup
