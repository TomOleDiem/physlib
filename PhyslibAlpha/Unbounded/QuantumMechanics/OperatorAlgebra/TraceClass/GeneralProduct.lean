/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.TraceProduct
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.HSAlgebra
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.HSEstimate
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.Polar
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.GeneralIdeal

/-!
# The product of two Hilbert--Schmidt operators is trace class

This is the master lemma that finally crosses the non-self-adjoint boundary honestly: given the
general partial-isometry identity `Polar.star_polarFactor_mul_self` (`star (polarFactor T) * T =
|T|`, for *every* bounded `T`), the diagonal of `|R * S|` for Hilbert--Schmidt `R`, `S` is exactly
`i ↦ ⟪(adjoint R * polarFactor (R*S)) (eᵢ), S eᵢ⟫`, which is absolutely summable by the same
Hilbert--Schmidt Cauchy--Schwarz estimate used for the diagonal of a Hilbert--Schmidt product.

From this single theorem, the general (not necessarily positive or self-adjoint) trace-class ideal
structure follows: every trace-class operator is already `(polarFactor T * sqrt |T|) * sqrt |T|`
(both Hilbert--Schmidt), so this master lemma gives the full two-sided ideal estimate and additive
closure of `IsTraceClass` for arbitrary operators, not merely positive ones.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TraceClass

open HilbertSchmidt

/-- The diagonal of `star W * (R * S)` (for any contraction `W`) unwinds to a Hilbert--Schmidt
Cauchy--Schwarz pairing. This is the pointwise identity feeding both the master product theorem
and the general additive/ideal closure results below. -/
private lemma diagonal_star_mul_eq_inner {R S W : B(H)} {w : Set H} (b : HilbertBasis w ℂ H)
    (i : w) :
    ⟪b i, (star W * (R * S)) (b i)⟫_ℂ =
      ⟪(ContinuousLinearMap.adjoint R * W) (b i), S (b i)⟫_ℂ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right W (b i) (R (S (b i)))]
  rw [← ContinuousLinearMap.adjoint_inner_left R (S (b i)) (W (b i))]
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]

/-! ### Quantitative trace-pairing estimate -/

/-- A contraction inserted on the left of a trace-class operator produces an
absolutely summable diagonal whose absolute sum is bounded by the trace norm.
This is the dual estimate behind the trace-norm triangle inequality. -/
theorem tsum_norm_diagonal_star_mul_le_traceNorm {A T : B(H)}
    (hA : ‖A‖ ≤ 1) (hT : IsTraceClass T) {w : Set H}
    (b : HilbertBasis w ℂ H) :
    Summable (fun i : w => ‖⟪b i, (star A * T) (b i)⟫_ℂ‖) ∧
      (∑' i : w, ‖⟪b i, (star A * T) (b i)⟫_ℂ‖) ≤ traceNorm T hT := by
  let U : B(H) := Polar.polarFactor T
  let S : B(H) := CFC.sqrt (CFC.abs T)
  have hS : IsHilbertSchmidt S :=
    isHilbertSchmidt_sqrt_abs_of_isTraceClass hT
  have hUS : IsHilbertSchmidt (U * S) :=
    isHilbertSchmidt_mul_left_of_opNorm_le_one
      (Polar.polarFactor_opNorm_le T) hS
  have hRstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint (U * S)) :=
    isHilbertSchmidt_star hUS
  have hRA : IsHilbertSchmidt (ContinuousLinearMap.adjoint (U * S) * A) :=
    isHilbertSchmidt_mul_right_of_opNorm_le_one hA hRstar
  have hRA_sum : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint (U * S) * A) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hRA
  have hS_sum : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hS
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg (CFC.abs T))
  have hU' : ‖ContinuousLinearMap.adjoint U * A‖ ≤ 1 := by
    have hUadj : ‖ContinuousLinearMap.adjoint U‖ ≤ 1 := by
      simpa using (Polar.polarFactor_opNorm_le T)
    calc
      ‖ContinuousLinearMap.adjoint U * A‖ ≤
          ‖ContinuousLinearMap.adjoint U‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ 1 := mul_le_one₀ hUadj (norm_nonneg _) hA
  have hRAeq : ContinuousLinearMap.adjoint (U * S) * A =
      S * (ContinuousLinearMap.adjoint U * A) := by
    rw [show U * S = U ∘SL S by rfl, ContinuousLinearMap.adjoint_comp]
    rw [← ContinuousLinearMap.mul_def, ← ContinuousLinearMap.star_eq_adjoint]
    have hSstar : star S = S :=
      (ContinuousLinearMap.star_eq_adjoint S).trans
        ((ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself)
    rw [hSstar]
    simp only [mul_assoc]
  have hRA_le : (∑' i : w,
      ‖(ContinuousLinearMap.adjoint (U * S) * A) (b i)‖ ^ 2) ≤
      ∑' i : w, ‖S (b i)‖ ^ 2 := by
    rw [hRAeq]
    calc
      (∑' i : w, ‖(S * (ContinuousLinearMap.adjoint U * A)) (b i)‖ ^ 2) ≤
          ‖ContinuousLinearMap.adjoint U * A‖ ^ 2 *
            (∑' i : w, ‖S (b i)‖ ^ 2) :=
        tsum_norm_sq_mul_right_le_of_selfAdjoint hSself hS b b
      _ ≤ 1 * (∑' i : w, ‖S (b i)‖ ^ 2) := by
        have hsq : ‖ContinuousLinearMap.adjoint U * A‖ ^ 2 ≤ (1 : ℝ) := by
          calc
            ‖ContinuousLinearMap.adjoint U * A‖ ^ 2 ≤ (1 : ℝ) ^ 2 :=
              (sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hU'
            _ = 1 := by norm_num
        exact mul_le_mul_of_nonneg_right hsq
          (tsum_nonneg fun i => sq_nonneg (‖S (b i)‖))
      _ = ∑' i : w, ‖S (b i)‖ ^ 2 := one_mul _
  have htraceS : (∑' i : w, ‖S (b i)‖ ^ 2) = traceNorm T hT := by
    have htrace := traceNorm_eq_of_hilbertBasis hT b
    have hpt : ∀ i : w,
        (⟪b i, CFC.abs T (b i)⟫_ℂ).re = ‖S (b i)‖ ^ 2 := by
      intro i
      have hSS : S * S = CFC.abs T := by
        dsimp [S]
        exact CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)
      have hinner : ⟪b i, CFC.abs T (b i)⟫_ℂ =
          ⟪S (b i), S (b i)⟫_ℂ := by
        have hSstar : ContinuousLinearMap.adjoint S = S :=
          (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
        rw [← hSS]
        rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
          ← ContinuousLinearMap.adjoint_inner_left S (S (b i)) (b i), hSstar]
      rw [hinner, inner_self_eq_norm_sq_to_K]
      norm_cast
    calc
      (∑' i : w, ‖S (b i)‖ ^ 2) =
          ∑' i : w, (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
            apply tsum_congr
            intro i
            exact (hpt i).symm
      _ = traceNorm T hT := htrace.symm
  have hprod : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint (U * S) * A) (b i)‖ * ‖S (b i)‖) :=
    summable_norm_mul_of_square_sums _ _ hRA_sum hS_sum
      (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  have hprod_le : (∑' i : w,
      ‖(ContinuousLinearMap.adjoint (U * S) * A) (b i)‖ * ‖S (b i)‖) ≤
      traceNorm T hT := by
    have hcs := tsum_mul_le_sqrt_mul_sqrt hRA_sum hS_sum
      (fun i => norm_nonneg _) (fun i => norm_nonneg _)
    have hroot : Real.sqrt (∑' i : w,
        ‖(ContinuousLinearMap.adjoint (U * S) * A) (b i)‖ ^ 2) ≤
        Real.sqrt (traceNorm T hT) := by
      apply Real.sqrt_le_sqrt
      rw [← htraceS]
      exact hRA_le
    calc
      (∑' i : w, ‖(ContinuousLinearMap.adjoint (U * S) * A) (b i)‖ *
          ‖S (b i)‖) ≤
          Real.sqrt (∑' i : w,
            ‖(ContinuousLinearMap.adjoint (U * S) * A) (b i)‖ ^ 2) *
            Real.sqrt (∑' i : w, ‖S (b i)‖ ^ 2) := hcs
      _ ≤ Real.sqrt (traceNorm T hT) * Real.sqrt (traceNorm T hT) := by
        gcongr
        rw [htraceS]
      _ = traceNorm T hT := Real.mul_self_sqrt (traceNorm_nonneg T hT)
  have hdiag : Summable (fun i : w =>
      ‖⟪b i, (star A * T) (b i)⟫_ℂ‖) := by
    have hfactorT : (U * S) * S = T := by
      dsimp [U, S]
      rw [mul_assoc, CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)]
      exact Polar.polarFactor_mul_absOperator T
    have hpoint : ∀ i : w, ‖⟪b i, (star A * T) (b i)⟫_ℂ‖ ≤
        ‖(ContinuousLinearMap.adjoint (U * S) * A) (b i)‖ * ‖S (b i)‖ := by
      intro i
      rw [← hfactorT, diagonal_star_mul_eq_inner b i]
      simpa using (norm_inner_le_norm
        ((ContinuousLinearMap.adjoint (U * S) * A) (b i)) (S (b i)))
    apply Summable.of_nonneg_of_le (fun i => norm_nonneg _)
      hpoint hprod
  refine ⟨hdiag, ?_⟩
  have hle : (∑' i : w, ‖⟪b i, (star A * T) (b i)⟫_ℂ‖) ≤
      ∑' i : w, ‖(ContinuousLinearMap.adjoint (U * S) * A) (b i)‖ *
        ‖S (b i)‖ := by
    apply hdiag.tsum_le_tsum
    · intro i
      have hfactorT : (U * S) * S = T := by
        dsimp [U, S]
        rw [mul_assoc, CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)]
        exact Polar.polarFactor_mul_absOperator T
      rw [← hfactorT, diagonal_star_mul_eq_inner b i]
      exact norm_inner_le_norm _ _
    · exact hprod
  exact hle.trans hprod_le

/-- **Master lemma**: the product of two Hilbert--Schmidt operators is trace class.  The proof
factors `|RS| = star (polarFactor (RS)) * (RS)` (the general partial-isometry identity, valid for
every bounded operator, not just this product) and bounds its diagonal by the Hilbert--Schmidt
Cauchy--Schwarz estimate `summable_norm_mul_of_square_sums`. -/
theorem isTraceClass_mul_of_isHilbertSchmidt {R S : B(H)}
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    IsTraceClass (R * S) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  refine ⟨w, b, ?_⟩
  set W : B(H) := Polar.polarFactor (R * S) with hWdef
  have hWnorm : ‖W‖ ≤ 1 := Polar.polarFactor_opNorm_le (R * S)
  have hRstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint R) := by
    rcases hR with ⟨w₀, b₀, hb₀⟩
    exact ⟨w₀, b₀, summable_norm_sq_adjoint_of_summable_norm_sq b₀ hb₀⟩
  have hRW : IsHilbertSchmidt (ContinuousLinearMap.adjoint R * W) :=
    isHilbertSchmidt_mul_right_of_opNorm_le_one hWnorm hRstar
  have hRWb : Summable (fun i : w => ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hRW
  have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hS
  have hprod : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖) :=
    summable_norm_mul_of_square_sums _ _ hRWb hSb (fun i => norm_nonneg _) (fun i => norm_nonneg _)
  have habs : Polar.absOperator (R * S) = star W * (R * S) :=
    (Polar.star_polarFactor_mul_self (R * S)).symm
  have hpoint : ∀ i : w,
      ⟪b i, CFC.abs (R * S) (b i)⟫_ℂ =
        ⟪(ContinuousLinearMap.adjoint R * W) (b i), S (b i)⟫_ℂ := by
    intro i
    show ⟪b i, Polar.absOperator (R * S) (b i)⟫_ℂ = _
    rw [habs]
    exact diagonal_star_mul_eq_inner b i
  apply Summable.of_norm_bounded hprod
  intro i
  calc
    ‖(⟪b i, CFC.abs (R * S) (b i)⟫_ℂ).re‖ ≤ ‖⟪b i, CFC.abs (R * S) (b i)⟫_ℂ‖ :=
      Complex.abs_re_le_norm _
    _ = ‖⟪(ContinuousLinearMap.adjoint R * W) (b i), S (b i)⟫_ℂ‖ := by rw [hpoint i]
    _ ≤ ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖ :=
      norm_inner_le_norm _ _

/-- Every trace-class operator factors as a product of two Hilbert--Schmidt operators: the polar
factor composed with the Hilbert--Schmidt square root of `|T|`, and that same square root again.
This is the converse companion of the master lemma above, already implicit in
`summable_trace_diagonal_of_isTraceClass`; it is recorded here as a named factorization since the
general ideal/additivity results below both consume it directly. -/
theorem isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs {T : B(H)} (hT : IsTraceClass T) :
    IsHilbertSchmidt (Polar.polarFactor T * CFC.sqrt (CFC.abs T)) ∧
      IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) ∧
      Polar.polarFactor T * CFC.sqrt (CFC.abs T) * CFC.sqrt (CFC.abs T) = T := by
  have hS : IsHilbertSchmidt (CFC.sqrt (CFC.abs T)) :=
    isHilbertSchmidt_sqrt_abs_of_isTraceClass hT
  have hUS : IsHilbertSchmidt (Polar.polarFactor T * CFC.sqrt (CFC.abs T)) :=
    isHilbertSchmidt_mul_left_of_opNorm_le_one (Polar.polarFactor_opNorm_le T) hS
  refine ⟨hUS, hS, ?_⟩
  rw [mul_assoc, CFC.sqrt_mul_sqrt_self (CFC.abs T) (CFC.abs_nonneg T)]
  exact Polar.polarFactor_mul_absOperator T

/-- **General additive closure of `IsTraceClass`**, for arbitrary (not necessarily positive or
self-adjoint) trace-class operators.  The proof conjugates the sum by the *sum's own* polar factor
`W`: `star W * (T + T') = star W * T + star W * T'` splits additively as bounded operators, and
each summand's diagonal is absolutely summable by the same Hilbert--Schmidt Cauchy--Schwarz
estimate used in the master lemma, applied to `T`'s and `T'`'s own Hilbert--Schmidt
factorizations. -/
theorem isTraceClass_add {T T' : B(H)} (hT : IsTraceClass T) (hT' : IsTraceClass T') :
    IsTraceClass (T + T') := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  refine ⟨w, b, ?_⟩
  set W : B(H) := Polar.polarFactor (T + T') with hWdef
  have hWnorm : ‖W‖ ≤ 1 := Polar.polarFactor_opNorm_le (T + T')
  have hsummable_conj : ∀ {X : B(H)}, IsTraceClass X →
      Summable (fun i : w => ⟪(b i : H), (star W * X) (b i)⟫_ℂ) := by
    intro X hX
    obtain ⟨hUS, hS, hfactor⟩ := isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs hX
    set R : B(H) := Polar.polarFactor X * CFC.sqrt (CFC.abs X) with hRdef
    set S : B(H) := CFC.sqrt (CFC.abs X) with hSdef
    have hRstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint R) := by
      rcases hUS with ⟨w₀, b₀, hb₀⟩
      exact ⟨w₀, b₀, summable_norm_sq_adjoint_of_summable_norm_sq b₀ hb₀⟩
    have hRW : IsHilbertSchmidt (ContinuousLinearMap.adjoint R * W) :=
      isHilbertSchmidt_mul_right_of_opNorm_le_one hWnorm hRstar
    have hRWb : Summable (fun i : w => ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ ^ 2) :=
      summable_norm_sq_apply_of_hilbertBasis w b hRW
    have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
      summable_norm_sq_apply_of_hilbertBasis w b hS
    have hprod : Summable (fun i : w =>
        ‖(ContinuousLinearMap.adjoint R * W) (b i)‖ * ‖S (b i)‖) :=
      summable_norm_mul_of_square_sums _ _ hRWb hSb
        (fun i => norm_nonneg _) (fun i => norm_nonneg _)
    have hpoint : ∀ i : w, ⟪b i, (star W * X) (b i)⟫_ℂ =
        ⟪(ContinuousLinearMap.adjoint R * W) (b i), S (b i)⟫_ℂ := by
      intro i
      rw [show X = R * S from hfactor.symm]
      exact diagonal_star_mul_eq_inner b i
    apply Summable.of_norm_bounded hprod
    intro i
    rw [hpoint i]
    exact norm_inner_le_norm _ _
  have hTsum := hsummable_conj hT
  have hT'sum := hsummable_conj hT'
  have habs : CFC.abs (T + T') = star W * (T + T') := (Polar.star_polarFactor_mul_self (T +
      T')).symm
  have hsplit : (fun i : w => ⟪b i, CFC.abs (T + T') (b i)⟫_ℂ) =
      (fun i : w => ⟪b i, (star W * T) (b i)⟫_ℂ + ⟪b i, (star W * T') (b i)⟫_ℂ) := by
    funext i
    rw [habs]
    show ⟪b i, (star W * (T + T')) (b i)⟫_ℂ = _
    have hstep : (star W * (T + T')) (b i) = (star W * T) (b i) + (star W * T') (b i) := by
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.add_apply, map_add, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply]
    rw [hstep, inner_add_right]
  have hsum : Summable (fun i : w =>
      ⟪b i, (star W * T) (b i)⟫_ℂ + ⟪b i, (star W * T') (b i)⟫_ℂ) := hTsum.add hT'sum
  have hsum' : Summable (fun i : w =>
      (⟪b i, (star W * T) (b i)⟫_ℂ + ⟪b i, (star W * T') (b i)⟫_ℂ).re) := by
    convert (hsum.map Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous) using 1
    ext i
    rfl
  have hsplit' := congrArg (fun f : w → ℂ => fun i => (f i).re) hsplit
  rw [hsplit']
  exact hsum'

/-- **The general two-sided trace ideal estimate**: conjugating a trace-class operator by
arbitrary bounded operators on either side stays trace class.  Unlike
`isTraceClass_star_mul_mul_of_nonneg`, this needs no positivity hypothesis on `T`: the two
Hilbert--Schmidt factors of `T` absorb `A` and `B` on either side (bounded left/right
multiplication preserves the Hilbert--Schmidt predicate), and the master lemma finishes the
argument. -/
theorem isTraceClass_mul_mul {A B T : B(H)} (hT : IsTraceClass T) :
    IsTraceClass (A * T * B) := by
  obtain ⟨_, hS, hfactor⟩ := isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs hT
  set R : B(H) := Polar.polarFactor T * CFC.sqrt (CFC.abs T) with hRdef
  set S : B(H) := CFC.sqrt (CFC.abs T) with hSdef
  have hUS : IsHilbertSchmidt R :=
    isHilbertSchmidt_mul_left_of_opNorm_le_one (Polar.polarFactor_opNorm_le T) hS
  have hAR : IsHilbertSchmidt (A * R) := isHilbertSchmidt_mul_left hUS
  have hSB : IsHilbertSchmidt (S * B) := isHilbertSchmidt_mul_right hS
  have heq : A * T * B = (A * R) * (S * B) := by
    rw [show T = R * S from hfactor.symm]
    simp only [mul_assoc]
  rw [heq]
  exact isTraceClass_mul_of_isHilbertSchmidt hAR hSB

/-- Taking the adjoint preserves trace class. -/
theorem isTraceClass_star {T : B(H)} (hT : IsTraceClass T) :
    IsTraceClass (star T) := by
  obtain ⟨hR, hS, hfactor⟩ :=
    isHilbertSchmidt_polarFactor_mul_sqrt_abs_and_sqrt_abs hT
  have hstar : IsTraceClass (star (CFC.sqrt (CFC.abs T)) *
      star (Polar.polarFactor T * CFC.sqrt (CFC.abs T))) :=
    isTraceClass_mul_of_isHilbertSchmidt (isHilbertSchmidt_star hS)
      (isHilbertSchmidt_star hR)
  rw [← hfactor]
  simpa only [star_mul] using hstar

end TraceClass

end OperatorAlgebra
