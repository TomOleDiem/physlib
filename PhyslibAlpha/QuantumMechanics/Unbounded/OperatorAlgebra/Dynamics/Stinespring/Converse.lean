/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Dynamics.Stinespring.Canonical

/-!
# Stinespring's construction (part 3 of 3: the Christensen-Evans converse)

Continuation of `Stinespring/Canonical.lean`; see `Stinespring.lean` for the full module overview.
This part proves the complete bounded Christensen-Evans converse for `B(H)`: the positive
Evans-Lewis kernel is represented on its completion and compressed back to a CP jump map, and the
quantum-dynamical-semigroup generator data is assembled from it.
-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra TensorProduct
open OperatorAlgebra
noncomputable section

namespace OperatorAlgebra


namespace MatrixVectorState

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The vector-state functional obtained by evaluating a matrix at one diagonal entry.

This is the concrete positive functional used to turn matrix-compression CCP into Hilbert-space
quadratic inequalities.  Positivity of the selected diagonal entry is proved directly from the
`StarOrderedRing` description of the positive cone. -/
@[nolint unusedArguments]
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

/-- The continuous linear embedding of `H` into coordinate `j` of `PiLp 2 (Fin n → H)`. -/
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

@[nolint unusedArguments, simp]
lemma piLpSingleCLM_apply (n : ℕ) (j : Fin n) (x : H) :
    piLpSingleCLM n j x = PiLp.single 2 j x := by
  change (piLpSingleCLM n j) x = PiLp.single 2 j x
  simp [piLpSingleCLM]

/-- Recovers the `CStarMatrix` block entries of a bounded operator on `PiLp 2 (Fin n → H)`:
the inverse of `blockMatrixMap`. -/
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

/-- The entrywise (diagonal) action of `V : H →L[ℂ] K` on
`PiLp 2 (Fin n → H) → PiLp 2 (Fin n → K)`. -/
@[nolint unusedArguments]
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

/-- Compression of a representation `π` by a (not necessarily source-algebra) implementing
operator `V`: `a ↦ V⋆ π(a) V`. -/
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

/-- `compressionLinearMap`, bundled as a continuous linear map. -/
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

/-- `compressionContinuousLinearMap`, packaged as a completely positive map. -/
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
    OperatorAlgebra.isChristensenEvansGenerator_of_hamiltonianShift
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
    OperatorAlgebra.isChristensenEvansGenerator_of_hamiltonianShift
      G.generator G.generator_apply_one hshift
  exact Φ.exists_canonical_stinespring_realization hΦ hCE

end QuantumDynamicalSemigroup

end OperatorAlgebra
