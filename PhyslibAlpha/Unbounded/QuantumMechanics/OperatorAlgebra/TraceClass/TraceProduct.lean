/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.HilbertSchmidt
public import Mathlib.Analysis.MeanInequalities

/-!
# Products of Hilbert--Schmidt operators

This file records the first general (not necessarily self-adjoint) trace-ideal
estimate.  The diagonal of a product of two Hilbert--Schmidt operators is
absolutely summable in every Hilbert basis.  It is the Cauchy--Schwarz step
needed after polar decomposition.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace HilbertSchmidt

private lemma holder_two_two : (2 : ℝ).HolderConjugate 2 := by
  rw [Real.holderConjugate_iff]
  constructor <;> norm_num

/-- The real `ℓ²` Cauchy--Schwarz estimate in the form needed for operator
diagonal bounds. -/
theorem tsum_mul_le_sqrt_mul_sqrt {w : Set H} {f g : w → ℝ}
    (hf : Summable (fun i => f i ^ 2)) (hg : Summable (fun i => g i ^ 2))
    (hf_nonneg : ∀ i, 0 ≤ f i) (hg_nonneg : ∀ i, 0 ≤ g i) :
    ∑' i : w, f i * g i ≤
      Real.sqrt (∑' i : w, f i ^ 2) * Real.sqrt (∑' i : w, g i ^ 2) := by
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    (f := f) (g := g) holder_two_two hf_nonneg hg_nonneg
    (by convert hf using 1 <;> ext i <;> norm_num [Real.rpow_natCast])
    (by convert hg using 1 <;> ext i <;> norm_num [Real.rpow_natCast])
  have hf_eq : (∑' i : w, f i ^ (2 : ℝ)) = ∑' i : w, f i ^ 2 := by
    apply tsum_congr
    intro i
    exact Real.rpow_natCast (f i) 2
  have hg_eq : (∑' i : w, g i ^ (2 : ℝ)) = ∑' i : w, g i ^ 2 := by
    apply tsum_congr
    intro i
    exact Real.rpow_natCast (g i) 2
  rw [hf_eq, hg_eq] at h
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  simpa only [Real.rpow_natCast] using h

lemma summable_norm_mul_of_square_sums {w : Set H}
    (f g : w → ℝ) (hf : Summable (fun i => f i ^ 2))
    (hg : Summable (fun i => g i ^ 2))
    (hf_nonneg : ∀ i, 0 ≤ f i) (hg_nonneg : ∀ i, 0 ≤ g i) :
    Summable (fun i => f i * g i) := by
  apply Real.summable_mul_of_Lp_Lq_of_nonneg holder_two_two hf_nonneg hg_nonneg
  · convert hf using 1 <;> ext i <;> norm_num [Real.rpow_natCast]
  · convert hg using 1 <;> ext i <;> norm_num [Real.rpow_natCast]

theorem tsum_norm_inner_mul_inner_le {w : Set H}
    (b : HilbertBasis w ℂ H) (x y : H) :
    ∑' i : w, ‖⟪x, b i⟫_ℂ‖ * ‖⟪b i, y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := by
  have hx : HasSum (fun i : w => ‖⟪x, b i⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
      convert hasSum_norm_sq_inner b x using 1
      funext i
      rw [← inner_conj_symm x (b i), RCLike.norm_conj]
  have hy : HasSum (fun i : w => ‖⟪b i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) :=
    hasSum_norm_sq_inner b y
  have h := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    (f := fun i : w => ‖⟪x, b i⟫_ℂ‖) (g := fun i : w => ‖⟪b i, y⟫_ℂ‖)
    holder_two_two
    (fun i => norm_nonneg _) (fun i => norm_nonneg _)
    (by convert hx.summable using 1 <;> ext i <;> norm_num [Real.rpow_natCast])
    (by convert hy.summable using 1 <;> ext i <;> norm_num [Real.rpow_natCast])
  have hxs : (∑' i : w, ‖⟪x, b i⟫_ℂ‖ ^ (2 : ℝ)) = ‖x‖ ^ 2 := by
    convert hx.tsum_eq using 1
    apply tsum_congr
    intro i
    exact (Real.rpow_natCast ‖⟪x, b i⟫_ℂ‖ 2)
  have hys : (∑' i : w, ‖⟪b i, y⟫_ℂ‖ ^ (2 : ℝ)) = ‖y‖ ^ 2 := by
    convert hy.tsum_eq using 1
    apply tsum_congr
    intro i
    exact (Real.rpow_natCast ‖⟪b i, y⟫_ℂ‖ 2)
  calc
    ∑' i : w, ‖⟪x, b i⟫_ℂ‖ * ‖⟪b i, y⟫_ℂ‖ ≤
        (∑' i : w, ‖⟪x, b i⟫_ℂ‖ ^ (2 : ℝ)) ^ (1 / 2) *
          (∑' i : w, ‖⟪b i, y⟫_ℂ‖ ^ (2 : ℝ)) ^ (1 / 2) := h
    _ = ‖x‖ * ‖y‖ := by
      rw [hxs, hys, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
        Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

private lemma summable_norm_inner_mul_inner {w : Set H}
    (b : HilbertBasis w ℂ H) (x y : H) :
    Summable (fun i : w => ‖⟪x, b i⟫_ℂ‖ * ‖⟪b i, y⟫_ℂ‖) := by
  apply Real.summable_mul_of_Lp_Lq_of_nonneg holder_two_two
    (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  · have hx := (hasSum_norm_sq_inner b x).summable
    convert hx using 1
    funext i
    rw [← inner_conj_symm x (b i), RCLike.norm_conj]
    exact Real.rpow_natCast ‖⟪b i, x⟫_ℂ‖ 2
  · have hy := (hasSum_norm_sq_inner b y).summable
    convert hy using 1 <;> ext i <;> norm_num [Real.rpow_natCast]

/-- The diagonal coefficients of a product of two Hilbert--Schmidt operators
are absolutely summable. -/
theorem summable_diagonal_of_hilbertSchmidt {R S : B(H)}
    {w : Set H} (b : HilbertBasis w ℂ H)
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    Summable (fun i : w => ⟪b i, (R * S) (b i)⟫_ℂ) := by
  have hRstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint R) := by
    rcases hR with ⟨w₀, b₀, hb₀⟩
    refine ⟨w₀, b₀, ?_⟩
    exact (summable_norm_sq_adjoint_of_summable_norm_sq b₀ hb₀)
  have hRb : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint R) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hRstar
  have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hS
  have hprod : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint R) (b i)‖ * ‖S (b i)‖) :=
    summable_norm_mul_of_square_sums _ _ hRb hSb (fun i => norm_nonneg _)
      (fun i => norm_nonneg _)
  apply Summable.of_norm_bounded hprod
  intro i
  have hi : ⟪b i, (R * S) (b i)⟫_ℂ =
      ⟪(ContinuousLinearMap.adjoint R) (b i), S (b i)⟫_ℂ := by
    exact (ContinuousLinearMap.adjoint_inner_left R (S (b i)) (b i)).symm
  rw [hi]
  simpa only [ContinuousLinearMap.mul_apply] using
    (norm_inner_le_norm ((ContinuousLinearMap.adjoint R) (b i)) (S (b i)))

/-- Absolute summability of the matrix used in the Hilbert--Schmidt trace
product argument. -/
private lemma summable_matrix_of_hilbertSchmidt {R S : B(H)}
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    Summable (Function.uncurry (fun (i : w) (j : w') =>
      ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ *
        ⟪c j, S (b i)⟫_ℂ)) := by
  have hRstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint R) := by
    rcases hR with ⟨w₀, b₀, hb₀⟩
    exact ⟨w₀, b₀, summable_norm_sq_adjoint_of_summable_norm_sq b₀ hb₀⟩
  have hRb : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint R) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hRstar
  have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hS
  have hprod : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint R) (b i)‖ * ‖S (b i)‖) :=
    summable_norm_mul_of_square_sums _ _ hRb hSb (fun i => norm_nonneg _)
      (fun i => norm_nonneg _)
  let F : w → w' → ℂ := fun i j =>
    ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ *
      ⟪c j, S (b i)⟫_ℂ
  let M : w → w' → ℝ := fun i j => ‖F i j‖
  have hMrow : ∀ i : w, Summable (M i) := by
    intro i
    have h := summable_norm_inner_mul_inner c
      ((ContinuousLinearMap.adjoint R) (b i)) (S (b i))
    simpa [M, F, norm_mul] using h
  have hMrow_bound : ∀ i : w, ∑' j : w', M i j ≤
      ‖(ContinuousLinearMap.adjoint R) (b i)‖ * ‖S (b i)‖ := by
    intro i
    simpa [M, F, norm_mul] using tsum_norm_inner_mul_inner_le c
      ((ContinuousLinearMap.adjoint R) (b i)) (S (b i))
  have hMrows : Summable (fun i : w => ∑' j : w', M i j) := by
    apply Summable.of_nonneg_of_le (fun i => tsum_nonneg fun j => norm_nonneg _)
      hMrow_bound hprod
  have hMnonneg : 0 ≤ Function.uncurry M := fun _ => norm_nonneg _
  have hM : Summable (Function.uncurry M) := by
    rw [summable_prod_of_nonneg hMnonneg]
    exact ⟨hMrow, hMrows⟩
  apply Summable.of_norm_bounded hM
  rintro ⟨i, j⟩
  exact le_rfl

private lemma hasSum_matrix_row_of_hilbertSchmidt {R S : B(H)}
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (i : w) :
    HasSum (fun j : w' =>
      ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ *
        ⟪c j, S (b i)⟫_ℂ)
      ⟪b i, (R * S) (b i)⟫_ℂ := by
  have h := c.hasSum_inner_mul_inner
    ((ContinuousLinearMap.adjoint R) (b i)) (S (b i))
  have hi : ⟪(ContinuousLinearMap.adjoint R) (b i), S (b i)⟫_ℂ =
      ⟪b i, (R * S) (b i)⟫_ℂ := by
    exact ContinuousLinearMap.adjoint_inner_left R (S (b i)) (b i)
  rw [← hi]
  exact h

private lemma hasSum_matrix_col_of_hilbertSchmidt {R S : B(H)}
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (j : w') :
    HasSum (fun i : w =>
      ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ *
        ⟪c j, S (b i)⟫_ℂ)
      ⟪c j, (S * R) (c j)⟫_ℂ := by
  have h := b.hasSum_inner_mul_inner
    ((ContinuousLinearMap.adjoint S) (c j)) (R (c j))
  have hR : ∀ i : w, ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ =
      ⟪b i, R (c j)⟫_ℂ := fun i =>
    ContinuousLinearMap.adjoint_inner_left R (c j) (b i)
  have hS : ∀ i : w, ⟪c j, S (b i)⟫_ℂ =
      ⟪(ContinuousLinearMap.adjoint S) (c j), b i⟫_ℂ := fun i =>
    (ContinuousLinearMap.adjoint_inner_left S (b i) (c j)).symm
  have hpoint : (fun i : w =>
      ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ *
        ⟪c j, S (b i)⟫_ℂ) =
      (fun i : w =>
        ⟪(ContinuousLinearMap.adjoint S) (c j), b i⟫_ℂ *
          ⟪b i, R (c j)⟫_ℂ) := by
    funext i
    rw [hR i, hS i, mul_comm]
  have hSR : ⟪(ContinuousLinearMap.adjoint S) (c j), R (c j)⟫_ℂ =
      ⟪c j, (S * R) (c j)⟫_ℂ := by
    exact ContinuousLinearMap.adjoint_inner_left S (R (c j)) (c j)
  rw [hpoint, ← hSR]
  exact h

theorem tsum_diagonal_mul_eq_tsum_diagonal_swap {R S : B(H)}
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    (∑' i : w, ⟪b i, (R * S) (b i)⟫_ℂ) =
      ∑' j : w', ⟪c j, (S * R) (c j)⟫_ℂ := by
  let F : w → w' → ℂ := fun i j =>
    ⟪(ContinuousLinearMap.adjoint R) (b i), c j⟫_ℂ *
      ⟪c j, S (b i)⟫_ℂ
  have hF : Summable (Function.uncurry F) := by
    exact summable_matrix_of_hilbertSchmidt b c hR hS
  have hrow : ∀ i : w, HasSum (F i)
      ⟪b i, (R * S) (b i)⟫_ℂ := fun i =>
    hasSum_matrix_row_of_hilbertSchmidt b c i
  have hcol : ∀ j : w', HasSum (fun i : w => F i j)
      ⟪c j, (S * R) (c j)⟫_ℂ := fun j =>
    hasSum_matrix_col_of_hilbertSchmidt b c j
  have hswap := hF.tsum_comm' (fun i => (hrow i).summable)
    (fun j => (hcol j).summable)
  calc
    ∑' i : w, ⟪b i, (R * S) (b i)⟫_ℂ =
        ∑' i : w, ∑' j : w', F i j := by
          apply tsum_congr
          intro i
          exact (hrow i).tsum_eq.symm
    _ = ∑' j : w', ∑' i : w, F i j := hswap.symm
    _ = ∑' j : w', ⟪c j, (S * R) (c j)⟫_ℂ := by
          apply tsum_congr
          intro j
          exact (hcol j).tsum_eq

end HilbertSchmidt

end OperatorAlgebra
