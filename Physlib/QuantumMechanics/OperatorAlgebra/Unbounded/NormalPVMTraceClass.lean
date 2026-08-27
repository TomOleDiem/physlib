/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalRepresentationBoundedOperators
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.DensityOperatorTraceState
public import Physlib.QuantumMechanics.OperatorAlgebra.TraceClass.PositiveDomination

/-!
# Trace-class normality of concrete projection-valued measures

This module upgrades the identity-representation bridge from finite-rank functionals to the full
completed trace-class predual.  The proof is deliberately concrete: normalize a positive
trace-class operator to a density operator, apply the normal-state σ-additivity field of a
`NormalPVM`, then pass through positive/negative and real/imaginary decompositions.  The resulting
constructor turns every concrete `NormalPVM` on `B(H)` into a `PredualPVM` and hence into the
standard real/complex normal affiliation bridges.
It also provides the reverse promotion from a concrete WOT spectral measure
and proves the required normal-state σ-additivity internally from the trace-class
density-operator decomposition of `B(H)`.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra InnerProductSpace
open OperatorAlgebra
open MeasureTheory Set

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace BoundedOperatorsNormalRepresentation

private def realPart (T : B(H)) : B(H) := (1 / 2 : ℂ) • (T + star T)

private def imagPart (T : B(H)) : B(H) := (-Complex.I / 2 : ℂ) • (T - star T)

private lemma realPart_isSelfAdjoint (T : B(H)) : IsSelfAdjoint (realPart T) := by
  change star ((1 / 2 : ℂ) • (T + star T)) = (1 / 2 : ℂ) • (T + star T)
  rw [star_smul, star_add, star_star]
  simp only [Complex.star_def]
  have hc : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by
    simp only [starRingEnd_apply, star_div₀, star_one, star_ofNat]
  rw [hc]
  module

private lemma imagPart_isSelfAdjoint (T : B(H)) : IsSelfAdjoint (imagPart T) := by
  change star ((-Complex.I / 2 : ℂ) • (T - star T)) =
    (-Complex.I / 2 : ℂ) • (T - star T)
  rw [star_smul, star_sub, star_star]
  simp [Complex.star_def]
  module

private lemma positive_traceClass_eq_zero {P : B(H)} (hPclass : IsTraceClass P)
    (ht : traceNorm P hPclass = 0) : P = 0 := by
  have hop : ‖P‖ ≤ traceNorm P hPclass := TraceClass.opNorm_le_traceNorm hPclass
  have hnorm : ‖P‖ = 0 := le_antisymm (ht ▸ hop) (norm_nonneg _)
  exact norm_eq_zero.mp hnorm

/-- A normal PVM on `B(H)` is countably additive against a positive trace-class functional. -/
theorem normalPVM_predual_m_iUnion_of_nonneg
    {X : Type*} [MeasurableSpace X] (E : NormalPVM X (B(H)))
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j)))
    {P : B(H)} (hP : 0 ≤ P) (hPclass : IsTraceClass P) :
    HasSum
      (fun n => WStarAlgebra.predualPairing
        (TraceClass.ofOperator P hPclass) (E (s n)))
      (WStarAlgebra.predualPairing
        (TraceClass.ofOperator P hPclass) (E (⋃ n, s n))) := by
  let t : ℝ := traceNorm P hPclass
  by_cases ht : t = 0
  · have hPzero : P = 0 := positive_traceClass_eq_zero hPclass ht
    subst P
    have hzero : TraceClass.ofOperator (0 : B(H)) hPclass = 0 := by
      apply Subtype.ext
      rfl
    rw [hzero]
    simp
  · have htpos : 0 < t := lt_of_le_of_ne (traceNorm_nonneg P hPclass) (Ne.symm ht)
    let c : ℂ := ((t⁻¹ : ℝ) : ℂ)
    let ξ : TraceClass H := c • TraceClass.ofOperator P hPclass
    have hξ : ξ.1 = c • P := rfl
    have hξclass : IsTraceClass (c • P) := by
      change IsTraceClass ξ.1
      exact ξ.2
    let ρ : DensityOperator H :=
      { ρ := ξ.1
        nonneg := (operator_nonneg_iff_isPositive _).mpr <|
          ((operator_nonneg_iff_isPositive P).mp hP).smul_of_nonneg
            (RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr htpos.le))
        traceClass := hξclass
        trace_eq_one := by
          change trace (c • P) hξclass = 1
          have htrace : trace (c • P) hξclass = c * trace P hPclass := by
            rw [show hξclass = isTraceClass_smul c hPclass from Subsingleton.elim _ _]
            exact TraceClass.trace_smul c hPclass
          rw [htrace, TraceClass.trace_eq_ofReal_traceNorm_of_nonneg hP hPclass]
          dsimp [c, t]
          rw [← Complex.ofReal_mul]
          congr 1
          field_simp [ht]
          exact div_self ht }
    have hρ : TraceClass.ofOperator ρ.ρ ρ.traceClass = ξ := by
      apply Subtype.ext
      rfl
    have hξ' : ξ = c • TraceClass.ofOperator P hPclass := rfl
    have hpair (A : B(H)) :
        WStarAlgebra.predualPairing (TraceClass.ofOperator P hPclass) A =
          (t : ℂ) * ρ.canonicalNormalState A := by
      rw [ρ.canonicalNormalState_apply_predualPairing]
      have hscaledPair :
          WStarAlgebra.predualPairing (TraceClass.ofOperator ρ.ρ ρ.traceClass) A =
            c * WStarAlgebra.predualPairing (TraceClass.ofOperator P hPclass) A := by
        rw [hρ, hξ', WStarAlgebra.predualPairing_apply, map_smul]
        rfl
      rw [hscaledPair]
      have htc : (t : ℂ) * c = 1 := by
        dsimp [c]
        rw [← Complex.ofReal_mul]
        field_simp [ht]
        norm_num
      rw [← mul_assoc, htc, one_mul]
    have hsum := (E.m_iUnion s hs hdisj ρ.canonicalNormalState).const_smul (t : ℂ)
    convert hsum using 1
    · funext n
      rw [hpair]
      rfl
    · rw [hpair]
      rfl

/-! The self-adjoint case follows from the positive and negative parts. -/

/-- A normal PVM is countably additive against every self-adjoint trace-class functional. -/
theorem normalPVM_predual_m_iUnion_of_isSelfAdjoint
    {X : Type*} [MeasurableSpace X] (E : NormalPVM X (B(H)))
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j)))
    {T : B(H)} (hT : IsSelfAdjoint T) (hTclass : IsTraceClass T) :
    HasSum
      (fun n => WStarAlgebra.predualPairing
        (TraceClass.ofOperator T hTclass) (E (s n)))
      (WStarAlgebra.predualPairing
        (TraceClass.ofOperator T hTclass) (E (⋃ n, s n))) := by
  let P : B(H) := T⁺
  let N : B(H) := T⁻
  have hP : IsTraceClass P := by
    simpa [P] using isTraceClass_posPart_of_isSelfAdjoint hT hTclass
  have hN : IsTraceClass N := by
    simpa [N] using isTraceClass_negPart_of_isSelfAdjoint hT hTclass
  have hPnonneg : 0 ≤ P := by simpa [P] using CFC.posPart_nonneg T
  have hNnonneg : 0 ≤ N := by simpa [N] using CFC.negPart_nonneg T
  have hPsum := normalPVM_predual_m_iUnion_of_nonneg E s hs hdisj hPnonneg hP
  have hNsum := normalPVM_predual_m_iUnion_of_nonneg E s hs hdisj hNnonneg hN
  have hsub := hPsum.sub hNsum
  have hdecomp : P - N = T := by
    simpa [P, N] using CFC.posPart_sub_negPart T hT
  have hξ : TraceClass.ofOperator T hTclass =
      TraceClass.ofOperator P hP - TraceClass.ofOperator N hN := by
    apply Subtype.ext
    exact hdecomp.symm
  rw [hξ]
  simpa only [WStarAlgebra.predualPairing_apply, map_sub, sub_apply] using hsub

/-! The arbitrary complex case is obtained from the real and imaginary parts. -/

/-- A normal PVM is countably additive against every trace-class functional. -/
theorem normalPVM_predual_m_iUnion_of_traceClass
    {X : Type*} [MeasurableSpace X] (E : NormalPVM X (B(H)))
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j)))
    {T : B(H)} (hTclass : IsTraceClass T) :
    HasSum
      (fun n => WStarAlgebra.predualPairing
        (TraceClass.ofOperator T hTclass) (E (s n)))
      (WStarAlgebra.predualPairing
        (TraceClass.ofOperator T hTclass) (E (⋃ n, s n))) := by
  have hstar : IsTraceClass (star T) := TraceClass.isTraceClass_star hTclass
  let R : B(H) := realPart T
  let I : B(H) := imagPart T
  have hRclass : IsTraceClass R := by
    dsimp [R, realPart]
    exact isTraceClass_smul _ (TraceClass.isTraceClass_add hTclass hstar)
  have hIclass : IsTraceClass I := by
    dsimp [I, imagPart]
    exact isTraceClass_smul _ (by
      simpa [sub_eq_add_neg] using TraceClass.isTraceClass_add hTclass
        (TraceClass.isTraceClass_neg hstar))
  have hRsum := normalPVM_predual_m_iUnion_of_isSelfAdjoint E s hs hdisj
    (realPart_isSelfAdjoint T) hRclass
  have hIsum := normalPVM_predual_m_iUnion_of_isSelfAdjoint E s hs hdisj
    (imagPart_isSelfAdjoint T) hIclass
  have htotal := hRsum.add (hIsum.const_smul Complex.I)
  have hdecomp : R + Complex.I • I = T := by
    dsimp [R, I, realPart, imagPart]
    have hc : Complex.I * (-Complex.I / 2 : ℂ) = (1 / 2 : ℂ) := by
      rw [div_eq_mul_inv]
      ring_nf
      norm_num [Complex.I_mul_I]
    simp only [smul_add, smul_sub, smul_smul, hc]
    module
  have hξ : TraceClass.ofOperator T hTclass =
      TraceClass.ofOperator R hRclass + Complex.I • TraceClass.ofOperator I hIclass := by
    apply Subtype.ext
    exact hdecomp.symm
  rw [hξ]
  simpa only [WStarAlgebra.predualPairing_apply, map_add, map_smul, smul_eq_mul,
    add_apply] using htotal

/-! ### The concrete `B(H)` upgrade -/

/-! ### Going back from the representation level -/

/-- The normality datum needed to promote a concrete WOT spectral measure to an algebraic PVM.

This is a proposition rather than a typeclass: normality belongs to a particular spectral measure,
and making it an ambient instance would create accidental choices when several preduals or
representations are in scope. -/
structure WOTNormalityCertificate
    {X : Type*} [MeasurableSpace X]
    (μS : QuantumMechanics.WOTSpectralMeasure X H) : Prop where
  m_iUnion_normal' : ∀ (s : ℕ → Set X), (∀ n, MeasurableSet (s n)) →
    Pairwise (fun i j => Disjoint (s i) (s j)) →
    ∀ ω : NormalState (B(H)),
      HasSum (fun n => ω ((μS (s n)).toCLM))
        (ω ((μS (⋃ n, s n)).toCLM))

private lemma density_quadraticForm_diagonalMeasure_sum
    {X : Type*} [MeasurableSpace X]
    (μS : QuantumMechanics.WOTSpectralMeasure X H) (ρ : DensityOperator H)
    {S : Set X} (hS : MeasurableSet S) :
    ENNReal.ofReal
        (ρ.quadraticForm ((μS S).toCLM)).re =
      (Measure.sum (fun i : ρ.traceClass.choose =>
        μS.diagonalMeasure
          (ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i)))) S := by
  have hroot : HilbertSchmidt.IsHilbertSchmidt ρ.sqrtOperator := by
    have h := TraceClass.isHilbertSchmidt_sqrt_abs_of_isTraceClass ρ.traceClass
    rw [CFC.abs_of_nonneg ρ.ρ ρ.nonneg] at h
    exact h
  have hroot_sum : Summable (fun i : ρ.traceClass.choose =>
      ‖ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i)‖ ^ 2) :=
    HilbertSchmidt.isHilbertSchmidt_iff hroot _ _
  have hterm (A : B(H)) : Summable (fun i : ρ.traceClass.choose =>
      ⟪ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i),
        A (ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i))⟫_ℂ) := by
    apply Summable.of_norm_bounded (hroot_sum.mul_left ‖A‖)
    intro i
    calc
      ‖⟪ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i),
          A (ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i))⟫_ℂ‖ ≤
          ‖ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i)‖ *
            ‖A (ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i))‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i)‖ *
          (‖A‖ * ‖ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i)‖) := by
        gcongr
        exact A.le_opNorm _
      _ = ‖A‖ * ‖ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i)‖ ^ 2 := by
        ring
  rw [Measure.sum_apply _ hS, DensityOperator.quadraticForm]
  let A : B(H) := (μS S).toCLM
  have hre := (hterm A).hasSum.map Complex.reCLM.toAddMonoidHom
    Complex.reCLM.continuous
  have hnonneg : ∀ i : ρ.traceClass.choose, 0 ≤
      (⟪ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i),
        (μS S).toCLM (ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i))⟫_ℂ).re := by
    intro i
    exact μS.re_inner_nonneg S (ρ.sqrtOperator
      (ρ.traceClass.choose_spec.choose i))
  calc
    ENNReal.ofReal
        (∑' i : ρ.traceClass.choose,
          ⟪ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i),
            (μS S).toCLM (ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i))⟫_ℂ).re =
        ENNReal.ofReal (∑' i : ρ.traceClass.choose,
          (⟪ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i),
            (μS S).toCLM (ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i))⟫_ℂ).re) := by
      exact congrArg ENNReal.ofReal hre.tsum_eq.symm
    _ = ∑' i : ρ.traceClass.choose, ENNReal.ofReal
          (⟪ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i),
            (μS S).toCLM (ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i))⟫_ℂ).re :=
      ENNReal.ofReal_tsum_of_nonneg hnonneg hre.summable
    _ = ∑' i : ρ.traceClass.choose,
          μS.diagonalMeasure
            (ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i)) S := by
      apply tsum_congr
      intro i
      rw [μS.diagonalMeasure_apply _ _ hS]
      rfl

private lemma wot_canonicalNormalState_m_iUnion
    {X : Type*} [MeasurableSpace X]
    (μS : QuantumMechanics.WOTSpectralMeasure X H) (ρ : DensityOperator H)
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j))) :
    HasSum
      (fun n => ρ.canonicalNormalState ((μS (s n)).toCLM))
      (ρ.canonicalNormalState ((μS (⋃ n, s n)).toCLM)) := by
  let ν : Measure X := Measure.sum (fun i : ρ.traceClass.choose =>
    μS.diagonalMeasure
      (ρ.sqrtOperator (ρ.traceClass.choose_spec.choose i)))
  have hq (S : Set X) (hS : MeasurableSet S) :
      ENNReal.ofReal (ρ.quadraticForm ((μS S).toCLM)).re = ν S := by
    dsimp [ν]
    exact density_quadraticForm_diagonalMeasure_sum μS ρ hS
  have hνuniv : ν Set.univ = 1 := by
    calc
      ν Set.univ = ENNReal.ofReal
          (ρ.quadraticForm ((μS Set.univ).toCLM)).re :=
        (hq Set.univ MeasurableSet.univ).symm
      _ = 1 := by
        rw [μS.univ, ContinuousLinearMapWOT.toCLM_one, ρ.quadraticForm_one]
        norm_num
  letI : IsFiniteMeasure ν :=
    { measure_univ_lt_top := by
        rw [hνuniv]
        exact ENNReal.coe_lt_top }
  have hPstar (S : Set X) : IsStarProjection ((μS S).toCLM) := by
    refine ⟨?_, ?_⟩
    · change (μS S).toCLM * (μS S).toCLM = (μS S).toCLM
      simpa only [ContinuousLinearMapWOT.toCLM_mul] using
        congrArg ContinuousLinearMapWOT.toCLM (μS.comp_self S)
    · change (star (μS S)).toCLM = (μS S).toCLM
      rw [(μS.isStarProjection S).isSelfAdjoint]
  have hstate_q (S : Set X) (hS : MeasurableSet S) :
      ρ.canonicalNormalState ((μS S).toCLM) =
        ρ.quadraticForm ((μS S).toCLM) := by
    change ρ.canonicalState ((μS S).toCLM) = _
    exact ρ.canonicalState_eq_quadraticForm_of_nonneg
      (Projection.nonneg_of_isStarProjection (hPstar S))
  have hmass (S : Set X) (hS : MeasurableSet S) :
      (ρ.canonicalNormalState ((μS S).toCLM)).re = ν.real S := by
    have hnonneg : 0 ≤
        (ρ.quadraticForm ((μS S).toCLM)).re := by
      exact (Complex.le_def.mp (ρ.quadraticForm_nonneg
        (Projection.nonneg_of_isStarProjection (hPstar S)))).1
    have hνne : ν S ≠ ⊤ := measure_ne_top ν S
    have h := congrArg ENNReal.toReal (hq S hS)
    rw [ENNReal.toReal_ofReal hnonneg] at h
    rw [hstate_q S hS]
    exact h
  have hreal : HasSum (fun n => ν.real (s n)) (ν.real (⋃ n, s n)) := by
    have htop : (∑' n, ν (s n)) ≠ ⊤ := by
      rw [← measure_iUnion hdisj hs]
      exact measure_ne_top ν _
    have h := ENNReal.hasSum_toReal htop
    convert h using 1
    · rfl
    · rw [Measure.real, measure_iUnion hdisj hs,
        ENNReal.tsum_toReal_eq (fun n => measure_ne_top ν (s n))]
  have hreal' : HasSum
      (fun n => (ρ.canonicalNormalState ((μS (s n)).toCLM)).re)
      ((ρ.canonicalNormalState ((μS (⋃ n, s n)).toCLM)).re) := by
    convert hreal using 1
    · funext n
      exact hmass (s n) (hs n)
    · exact hmass (⋃ n, s n) (MeasurableSet.iUnion hs)
  have hcomplex := hreal'.map Complex.ofRealCLM Complex.ofRealCLM.continuous
  have hreal_state (S : Set X) (hS : MeasurableSet S) :
      ρ.canonicalNormalState ((μS S).toCLM) =
        Complex.ofReal (ρ.canonicalNormalState ((μS S).toCLM)).re := by
    have hstate_im := congrArg Complex.im (hstate_q S hS)
    have hquadratic_im : (ρ.quadraticForm ((μS S).toCLM)).im = 0 := by
      exact (Complex.le_def.mp (ρ.quadraticForm_nonneg
        (Projection.nonneg_of_isStarProjection (hPstar S)))).2.symm
    have him : (ρ.canonicalNormalState ((μS S).toCLM)).im = 0 := by
      exact hstate_im.trans (hquadratic_im)
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using him
  convert hcomplex using 1
  · funext n
    exact hreal_state (s n) (hs n)
  · exact hreal_state (⋃ n, s n) (MeasurableSet.iUnion hs)

/-- Every concrete WOT spectral measure on `B(H)` is normal for the trace-class predual.

The proof expands a density operator through the Hilbert--Schmidt square root and uses the
associated diagonal scalar measures.  Thus the reverse WOT-to-normal promotion does not require
an additional normality field in the concrete `B(H)` setting. -/
theorem wotSpectralMeasure_toWOTNormalityCertificate_of_traceClass
    {X : Type*} [MeasurableSpace X]
    (μS : QuantumMechanics.WOTSpectralMeasure X H) :
    WOTNormalityCertificate μS := by
  refine ⟨fun s hs hdisj ω => ?_⟩
  let ρ : DensityOperator H := NormalState.densityOperator ω
  have hρ : ρ.canonicalNormalState = ω := by
    exact NormalState.densityOperator_canonicalNormalState ω
  simpa only [hρ] using wot_canonicalNormalState_m_iUnion μS ρ s hs hdisj

/-- The predual σ-additivity field of a concrete `PredualPVM` supplies the WOT normality
certificate after passing through the identity representation. -/
theorem predualPVM_toWOTNormalityCertificate
    {X : Type*} [MeasurableSpace X]
    (E : PredualPVM X (B(H))) :
    WOTNormalityCertificate (predualPVM_toWOTSpectralMeasure E) := by
  refine ⟨fun s hs hdisj ω => ?_⟩
  let ρ : DensityOperator H := NormalState.densityOperator ω
  let ξ : TraceClass H := TraceClass.ofOperator ρ.ρ ρ.traceClass
  have hω (A : B(H)) : ω A = WStarAlgebra.predualPairing ξ A := by
    rw [← NormalState.densityOperator_canonicalNormalState ω]
    exact ρ.canonicalNormalState_apply_predualPairing A
  have hsum := E.m_iUnion s hs hdisj ξ
  convert hsum using 1
  · funext n
    rw [hω]
    simp only [predualPVM_toWOTSpectralMeasure_apply,
      ContinuousLinearMapWOT.toCLM_ofCLM]
  · rw [hω]
    simp only [predualPVM_toWOTSpectralMeasure_apply,
      ContinuousLinearMapWOT.toCLM_ofCLM]

/-- Turn a concrete WOT spectral measure into the corresponding normal PVM once its
normal-functional σ-additivity has been established.

The extra hypothesis is intentional.  WOT countable additivity alone controls matrix
coefficients, whereas `NormalPVM` is the von Neumann-algebraic object and must be additive
against every normal state.  This constructor is therefore the precise reusable interface at
which a concrete trace-class normality proof enters the abstract affiliation API. -/
def wotSpectralMeasure_toNormalPVM
    {X : Type*} [MeasurableSpace X]
    (μS : QuantumMechanics.WOTSpectralMeasure X H)
    (hnormal : WOTNormalityCertificate μS) :
    NormalPVM X (B(H)) where
  toFun := fun S => (μS S).toCLM
  isStarProjection' := fun S => by
    refine ⟨?_, ?_⟩
    · change (μS S).toCLM * (μS S).toCLM = (μS S).toCLM
      simpa only [ContinuousLinearMapWOT.toCLM_mul] using
        congrArg ContinuousLinearMapWOT.toCLM (μS.comp_self S)
    · change (star (μS S)).toCLM = (μS S).toCLM
      rw [(μS.isStarProjection S).isSelfAdjoint]
  empty' := by
    rw [μS.toVectorMeasure.empty]
    exact ContinuousLinearMapWOT.toCLM_zero
  univ' := by
    rw [μS.univ]
    exact ContinuousLinearMapWOT.toCLM_one
  not_measurable' := fun S hS => by
    rw [μS.apply_eq_zero_of_not_measurableSet hS]
    exact ContinuousLinearMapWOT.toCLM_zero
  of_union' := fun hST hS hT => by
    rw [μS.of_union hST hS hT, ContinuousLinearMapWOT.toCLM_add]
  m_iUnion' := fun s hs hdisj ω => hnormal.m_iUnion_normal' s hs hdisj ω

/-- The certificate-free concrete promotion of a WOT spectral measure on `B(H)`.

The trace-class density-operator argument proves the normality certificate internally, so users
working with the concrete Hilbert-space algebra do not have to carry that implementation detail. -/
noncomputable def wotSpectralMeasure_toNormalPVM_of_traceClass
    {X : Type*} [MeasurableSpace X]
    (μS : QuantumMechanics.WOTSpectralMeasure X H) :
    NormalPVM X (B(H)) :=
  wotSpectralMeasure_toNormalPVM μS
    (wotSpectralMeasure_toWOTNormalityCertificate_of_traceClass μS)

@[simp]
theorem wotSpectralMeasure_toNormalPVM_of_traceClass_apply
    {X : Type*} [MeasurableSpace X]
    (μS : QuantumMechanics.WOTSpectralMeasure X H) (S : Set X) :
    wotSpectralMeasure_toNormalPVM_of_traceClass μS S = (μS S).toCLM := rfl

/-- The certificate-free real affiliated-observable wrapper for a concrete WOT spectral measure. -/
noncomputable def wotSpectralMeasure_toNormalAffiliatedObservable_of_traceClass
    (μS : QuantumMechanics.WOTSpectralMeasure ℝ H) :
    NormalAffiliatedObservable (B(H)) :=
  ⟨wotSpectralMeasure_toNormalPVM_of_traceClass μS⟩

@[simp] theorem wotSpectralMeasure_toNormalAffiliatedObservable_of_traceClass_spectralMeasure
    (μS : QuantumMechanics.WOTSpectralMeasure ℝ H) :
    (wotSpectralMeasure_toNormalAffiliatedObservable_of_traceClass μS).spectralMeasure =
      wotSpectralMeasure_toNormalPVM_of_traceClass μS := rfl

/-- The certificate-free complex affiliated-operator wrapper for a concrete WOT spectral measure. -/
noncomputable def wotSpectralMeasure_toNormalAffiliatedOperator_of_traceClass
    (μS : QuantumMechanics.WOTSpectralMeasure ℂ H) :
    NormalAffiliatedOperator (B(H)) :=
  ⟨wotSpectralMeasure_toNormalPVM_of_traceClass μS⟩

@[simp] theorem wotSpectralMeasure_toNormalAffiliatedOperator_of_traceClass_spectralMeasure
    (μS : QuantumMechanics.WOTSpectralMeasure ℂ H) :
    (wotSpectralMeasure_toNormalAffiliatedOperator_of_traceClass μS).spectralMeasure =
      wotSpectralMeasure_toNormalPVM_of_traceClass μS := rfl

/-- Every concrete `B(H)` `NormalPVM` has the trace-class predual σ-additivity required by the
weak spectral-integral layer. -/
def normalPVM_toPredualPVM {X : Type*} [MeasurableSpace X]
    (E : NormalPVM X (B(H))) : PredualPVM X (B(H)) where
  toNormalPVM := E
  m_iUnion_predual' := fun s hs hdisj ξ =>
    normalPVM_predual_m_iUnion_of_traceClass E s hs hdisj (TraceClass.isTraceClass_coe ξ)

@[simp]
theorem normalPVM_toPredualPVM_apply {X : Type*} [MeasurableSpace X]
    (E : NormalPVM X (B(H))) (S : Set X) : normalPVM_toPredualPVM E S = E S := rfl

/-- The concrete trace-class route to the weak-operator spectral measure. -/
noncomputable def normalPVM_toWOTSpectralMeasure_of_traceClass
    {X : Type*} [MeasurableSpace X] (E : NormalPVM X (B(H))) :
    QuantumMechanics.WOTSpectralMeasure X H :=
  predualPVM_toWOTSpectralMeasure (normalPVM_toPredualPVM E)

@[simp]
theorem normalPVM_toWOTSpectralMeasure_of_traceClass_apply
    {X : Type*} [MeasurableSpace X] (E : NormalPVM X (B(H))) (S : Set X) :
    normalPVM_toWOTSpectralMeasure_of_traceClass E S =
      ContinuousLinearMapWOT.ofCLM (E S) := by
  rw [normalPVM_toWOTSpectralMeasure_of_traceClass,
    predualPVM_toWOTSpectralMeasure_apply]
  rfl

@[simp]
theorem normalPVM_toWOTSpectralMeasure_of_traceClass_toNormalPVM
    {X : Type*} [MeasurableSpace X]
    (μS : QuantumMechanics.WOTSpectralMeasure X H)
    (hnormal : WOTNormalityCertificate μS) (S : Set X) :
    normalPVM_toWOTSpectralMeasure_of_traceClass
        (wotSpectralMeasure_toNormalPVM μS hnormal) S = μS S := by
  rw [normalPVM_toWOTSpectralMeasure_of_traceClass_apply]
  exact ContinuousLinearMapWOT.ofCLM_toCLM _

@[simp]
theorem wotSpectralMeasure_toNormalPVM_predualPVM
    {X : Type*} [MeasurableSpace X]
    (E : PredualPVM X (B(H))) :
    wotSpectralMeasure_toNormalPVM
        (predualPVM_toWOTSpectralMeasure E)
        (predualPVM_toWOTNormalityCertificate E) = E.toNormalPVM := by
  apply NormalPVM.ext
  intro S hS
  change (predualPVM_toWOTSpectralMeasure E S).toCLM = E.toNormalPVM S
  rw [predualPVM_toWOTSpectralMeasure_apply]

/-- Package the concrete WOT-to-normal-PVM promotion directly as an affiliated observable. -/
def wotSpectralMeasure_toNormalAffiliatedObservable
    (μS : QuantumMechanics.WOTSpectralMeasure ℝ H)
    (hnormal : WOTNormalityCertificate μS) :
    NormalAffiliatedObservable (B(H)) :=
  ⟨wotSpectralMeasure_toNormalPVM μS hnormal⟩

@[simp] lemma wotSpectralMeasure_toNormalAffiliatedObservable_spectralMeasure
    (μS : QuantumMechanics.WOTSpectralMeasure ℝ H)
    (hnormal : WOTNormalityCertificate μS) :
    (wotSpectralMeasure_toNormalAffiliatedObservable μS hnormal).spectralMeasure =
      wotSpectralMeasure_toNormalPVM μS hnormal := rfl

/-- Package the complex-spectrum version directly as a normal affiliated operator. -/
def wotSpectralMeasure_toNormalAffiliatedOperator
    (μS : QuantumMechanics.WOTSpectralMeasure ℂ H)
    (hnormal : WOTNormalityCertificate μS) :
    NormalAffiliatedOperator (B(H)) :=
  ⟨wotSpectralMeasure_toNormalPVM μS hnormal⟩

@[simp] lemma wotSpectralMeasure_toNormalAffiliatedOperator_spectralMeasure
    (μS : QuantumMechanics.WOTSpectralMeasure ℂ H)
    (hnormal : WOTNormalityCertificate μS) :
    (wotSpectralMeasure_toNormalAffiliatedOperator μS hnormal).spectralMeasure =
      wotSpectralMeasure_toNormalPVM μS hnormal := rfl

/-- The identity representation of `B(H)` as a faithful normal affiliation bridge, using the
completed trace-class predual directly. -/
noncomputable def traceClassAffiliationBridge :
    FaithfulNormalAffiliationBridge (A := B(H)) (H := H) :=
  NormalAffiliationBridge.ofFaithfulPredualRepresentation
    (representation (H := H)) (fun E => normalPVM_toPredualPVM E)
    (fun _ => rfl) (predualMatrixCoefficientCertificate (H := H)) (by
      intro E f hf
      apply PredualPVM.ext
      intro S hS
      rw [normalPVM_toPredualPVM_apply,
        PredualPVM.map_apply (normalPVM_toPredualPVM E) hf hS,
        NormalPVM.map_apply E hf hS]
      rfl) (by
      intro a b h
      change a = b at h
      exact h)

/-- The corresponding faithful bridge for complex normal PVMs, again using the completed
trace-class predual rather than a separately supplied normality certificate. -/
noncomputable def traceClassOperatorAffiliationBridge :
    FaithfulNormalOperatorAffiliationBridge (A := B(H)) (H := H) :=
  NormalAffiliationBridge.FaithfulNormalOperatorAffiliationBridge.ofPredualRepresentation
    (traceClassAffiliationBridge (H := H)) (fun E => normalPVM_toPredualPVM E)
    (fun _ => rfl) (predualMatrixCoefficientCertificate (H := H)) (by
      intro E f hf
      apply PredualPVM.ext
      intro S hS
      rw [normalPVM_toPredualPVM_apply,
        PredualPVM.map_apply (normalPVM_toPredualPVM E) hf hS,
        NormalPVM.map_apply E hf hS]
      rfl) (by
      intro a b h
      change a = b at h
      exact h)

end BoundedOperatorsNormalRepresentation

end OperatorAlgebra

end
