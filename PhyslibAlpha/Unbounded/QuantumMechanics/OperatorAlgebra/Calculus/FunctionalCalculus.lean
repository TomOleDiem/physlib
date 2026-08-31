/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Affil.Affiliated
public import Mathlib.MeasureTheory.Integral.FinMeasAdditive
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.SimpleFuncDense
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!

# Measurable functional calculus

For `A : AffiliatedObservable M` and a measurable `f : ℝ → ℂ`, the measurable functional calculus
computes `f(A) = ∫ f \, dE_A`. Two cases matter:

* if `f` is merely measurable (possibly unbounded), `f(A)` is again an affiliated *operator*
  (`AffiliatedOperator M`, not necessarily self-adjoint unless `f` is real-valued);
* if `f` is bounded (measurable), `f(A)` is an honest *bounded* element of `M`.

Bounded spectral truncation, indicator functions, the unitary group `e^{itA}`, and the resolvent
`(A - z)⁻¹` are all corollaries of the bounded case, not separate foundational constructions.

## Key results

- `AffiliatedObservable.measurableFC` : `f(A)` for measurable (possibly unbounded) `f`.
- `AffiliatedObservable.boundedFC` : `f(A) ∈ M` for bounded measurable `f`.
- `AffiliatedObservable.indicator` : `1_S(A)`, recovering `A.spectralProjection S`.
- `AffiliatedObservable.expUnitary` : `e^{itA}`, a unitary in `M`.
- `AffiliatedObservable.resolvent` : `(A - z)⁻¹` for `z` off the real line.
- `AffiliatedObservable.truncate` : `A · 1_{[-R,R]}(A)`, the bounded spectral truncation of `A`.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra
open MeasureTheory Set

namespace OperatorAlgebra

/-! ## Auxiliary lemmas: finite orthogonal sums of projections

These are the general, PVM-independent algebraic facts driving `boundedFC`'s construction: a
finite `ℂ`-linear combination of pairwise-orthogonal star projections is norm-controlled by its
largest coefficient (the "key norm bound" from the module docstring), and a PVM is finitely
additive over any finite pairwise-disjoint measurable family (not just two sets, as
`PVM.of_union` already gives). -/

section Aux

variable {A : Type*} [OperatorAlgebra A]

/-- A finite sum of pairwise-orthogonal star projections is again a star projection. -/
private lemma isStarProjection_finsetSum {ι : Type*} [DecidableEq ι] (s : Finset ι) (P : ι → A)
    (hP : ∀ i ∈ s, IsStarProjection (P i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i * P j = 0) :
    IsStarProjection (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsStarProjection.zero A
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hPa : IsStarProjection (P a) := hP a (Finset.mem_insert_self a s)
    have hPs : IsStarProjection (∑ i ∈ s, P i) :=
      ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij =>
          horth i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    have h1 : P a * ∑ i ∈ s, P i = 0 := by
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero (fun i hi =>
        horth a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi)))
    have h2 : (∑ i ∈ s, P i) * P a = 0 := by
      rw [Finset.sum_mul]
      exact Finset.sum_eq_zero (fun i hi =>
        horth i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s)
          (fun h => ha (h ▸ hi)))
    refine ⟨?_, hPa.isSelfAdjoint.add hPs.isSelfAdjoint⟩
    show (P a + ∑ i ∈ s, P i) * (P a + ∑ i ∈ s, P i) = P a + ∑ i ∈ s, P i
    rw [add_mul, mul_add, mul_add, hPa.isIdempotentElem, h1, h2, hPs.isIdempotentElem]
    abel

/-- **Finite additivity of a PVM over a finite pairwise-disjoint measurable family.**
Generalizes `PVM.of_union` (the two-set case) to an arbitrary finite index by induction. -/
private lemma PVM.finsetSum_apply {X : Type*} [MeasurableSpace X] {ι : Type*}
    [DecidableEq ι] (E : PVM X A) (s : Finset ι) (S : ι → Set X)
    (hS : ∀ i ∈ s, MeasurableSet (S i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) :
    ∑ i ∈ s, (E (S i) : A) = E (⋃ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.set_biUnion_insert]
    have hSa : MeasurableSet (S a) := hS a (Finset.mem_insert_self a s)
    have hSs : MeasurableSet (⋃ i ∈ s, S i) :=
      Finset.measurableSet_biUnion s (fun i hi => hS i (Finset.mem_insert_of_mem hi))
    have hdisj : Disjoint (S a) (⋃ i ∈ s, S i) := by
      rw [Set.disjoint_iUnion₂_right]
      exact fun i hi => hd a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    rw [ih (fun i hi => hS i (Finset.mem_insert_of_mem hi))
      (fun i hi j hj hij =>
        hd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)]
    exact (E.of_union hdisj hSa hSs).symm

/-- **The key norm bound**, the C⋆-identity computation from the module docstring: for
pairwise-orthogonal star projections `P i` and complex coefficients `c i` bounded by `M` on every
nonzero `P i`, `‖∑ᵢ cᵢ • Pᵢ‖ ≤ M`. Proved by first showing `(∑cᵢPᵢ)⋆(∑cᵢPᵢ) = ∑‖cᵢ‖²Pᵢ` (again by
induction, cross terms vanishing by orthogonality), bounding this by `M² • 1` using that
`∑Pᵢ ≤ 1` (`isStarProjection_finsetSum` + `Projection.mem_effect`), and taking norms via the
C⋆-identity `‖x⋆x‖ = ‖x‖²`. -/
private lemma norm_sum_smul_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (P : ι → A) (c : ι → ℂ)
    (M : ℝ) (hM0 : 0 ≤ M) (hP : ∀ i ∈ s, IsStarProjection (P i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → P i * P j = 0)
    (hMc : ∀ i ∈ s, P i ≠ 0 → ‖c i‖ ≤ M) :
    ‖∑ i ∈ s, c i • P i‖ ≤ M := by
  classical
  have hCstarId : star (∑ i ∈ s, c i • P i) * (∑ i ∈ s, c i • P i)
      = ∑ i ∈ s, ((‖c i‖ ^ 2 : ℝ) : ℂ) • P i := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have hPa := hP a (Finset.mem_insert_self a s)
      have h1 : (star (c a) • P a) * (∑ i ∈ s, c i • P i) = 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_eq_zero (fun i hi => ?_)
        rw [smul_mul_smul_comm,
          horth a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
            (fun h => ha (h ▸ hi)),
          smul_zero]
      have h2 : (∑ i ∈ s, star (c i) • P i) * (c a • P a) = 0 := by
        rw [Finset.sum_mul]
        refine Finset.sum_eq_zero (fun i hi => ?_)
        rw [smul_mul_smul_comm,
          horth i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s)
            (fun h => ha (h ▸ hi)),
          smul_zero]
      have hdiag : (star (c a) • P a) * (c a • P a)
          = ((‖c a‖ ^ 2 : ℝ) : ℂ) • P a := by
        rw [smul_mul_smul_comm, hPa.isIdempotentElem.eq]
        congr 1
        show (starRingEnd ℂ) (c a) * c a = _
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      have hstar_s : star (∑ i ∈ s, c i • P i) = ∑ i ∈ s, star (c i) • P i :=
        (star_sum s _).trans (Finset.sum_congr rfl (fun i hi => by
          rw [star_smul, (hP i (Finset.mem_insert_of_mem hi)).isSelfAdjoint.star_eq]))
      rw [Finset.sum_insert ha, star_add, star_smul, hPa.isSelfAdjoint.star_eq,
        Finset.sum_insert ha, add_mul, mul_add, mul_add, hdiag, h1, hstar_s, h2,
        ← hstar_s,
        ih (fun i hi => hP i (Finset.mem_insert_of_mem hi))
          (fun i hi j hj hij =>
            horth i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
          (fun i hi hi0 => hMc i (Finset.mem_insert_of_mem hi) hi0)]
      abel
  have hsum_proj : IsStarProjection (∑ i ∈ s, P i) := isStarProjection_finsetSum s P hP horth
  have hsum_le : ∑ i ∈ s, P i ≤ 1 :=
    (Projection.mem_effect ⟨∑ i ∈ s, P i, hsum_proj⟩).2
  have hMsq_nonneg : (0 : ℂ) ≤ ((M ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.real_le_real.mpr (by positivity : (0:ℝ) ≤ M ^ 2)
  have hle : star (∑ i ∈ s, c i • P i) * (∑ i ∈ s, c i • P i) ≤ ((M ^ 2 : ℝ) : ℂ) • (1 : A) := by
    rw [hCstarId]
    calc ∑ i ∈ s, ((‖c i‖ ^ 2 : ℝ) : ℂ) • P i
        ≤ ∑ i ∈ s, ((M ^ 2 : ℝ) : ℂ) • P i := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          by_cases hPi0 : P i = 0
          · simp [hPi0]
          · exact smul_le_smul_of_nonneg_right
              (Complex.real_le_real.mpr (by nlinarith [hMc i hi hPi0, norm_nonneg (c i)]))
              (Projection.nonneg_of_isStarProjection (hP i hi))
      _ = ((M ^ 2 : ℝ) : ℂ) • ∑ i ∈ s, P i := (Finset.smul_sum).symm
      _ ≤ ((M ^ 2 : ℝ) : ℂ) • (1 : A) := smul_le_smul_of_nonneg_left hsum_le hMsq_nonneg
  have hpos : (0 : A) ≤ star (∑ i ∈ s, c i • P i) * (∑ i ∈ s, c i • P i) :=
    star_mul_self_nonneg _
  have hnormle := CStarAlgebra.norm_le_norm_of_nonneg_of_le hpos hle
  have hsq : ‖∑ i ∈ s, c i • P i‖ * ‖∑ i ∈ s, c i • P i‖ ≤ M ^ 2 := by
    calc ‖∑ i ∈ s, c i • P i‖ * ‖∑ i ∈ s, c i • P i‖
        = ‖star (∑ i ∈ s, c i • P i) * (∑ i ∈ s, c i • P i)‖ := (CStarRing.norm_star_mul_self).symm
      _ ≤ ‖((M ^ 2 : ℝ) : ℂ) • (1 : A)‖ := hnormle
      _ ≤ M ^ 2 := by
        rcases subsingleton_or_nontrivial A with hA | hA
        · letI : Subsingleton A := hA
          have h1 : (1 : A) = 0 := Subsingleton.elim _ _
          simp [h1]
          positivity
        · letI : Nontrivial A := hA
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
            CStarRing.norm_one, mul_one]
  nlinarith [norm_nonneg (∑ i ∈ s, c i • P i)]

end Aux

namespace AffiliatedObservable

variable {A : Type*} [OperatorAlgebra A] (T : AffiliatedObservable A)

/-! ## Finite spectral integrals -/

/-- The finite spectral integral of a complex-valued measurable simple function.

The fibres are used rather than an arbitrary presentation of a simple function;
this makes the definition canonical and exposes the orthogonality needed for
the norm estimate below. -/
def simpleIntegral (f : SimpleFunc ℝ ℂ) : A :=
  ∑ z ∈ f.range, z • (T.spectralMeasure (f ⁻¹' {z}) : A)

/-! The finite integral is an instance of Mathlib's canonical `setToSimpleFunc` construction.
This is the important structural observation: finite additivity of the PVM gives the
`FinMeasAdditive` hypothesis, so all the common-refinement algebra (`add`, `neg`, `sub`, and
eventual approximation independence) is inherited from the measure-theoretic API rather than
proved by repeatedly expanding two unrelated ranges. -/

/-- The continuous-linear-map-valued set function associated with a PVM.  Its value at `z` is
`z • E(S)`; exposing this small bridge lets the standard finite-simple-function integration API
operate directly on a projection-valued measure. -/
def spectralCLM (T : AffiliatedObservable A) (S : Set ℝ) : ℂ →L[ℝ] A :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (T.spectralMeasure S : A)).restrictScalars ℝ

lemma spectralCLM_apply (S : Set ℝ) (z : ℂ) :
    spectralCLM T S z = z • (T.spectralMeasure S : A) := by
  rfl

private lemma spectralCLM_finMeasAdditive (μ : Measure ℝ) :
    FinMeasAdditive μ (spectralCLM T) := by
  intro S U hS hU hμS hμU hdisj
  ext z
  rw [ContinuousLinearMap.add_apply]
  simp only [spectralCLM_apply]
  rw [T.spectralMeasure.of_union hdisj hS hU, smul_add]

@[nolint unusedArguments]
lemma simpleIntegral_eq_setToSimpleFunc (f : SimpleFunc ℝ ℂ) (μ : Measure ℝ) :
    T.simpleIntegral f = f.setToSimpleFunc (spectralCLM T) := by
  simp only [SimpleFunc.setToSimpleFunc, spectralCLM_apply, simpleIntegral]

private lemma simpleFunc_integrable_dirac (f : SimpleFunc ℝ ℂ) :
    Integrable f (Measure.dirac 0) := by
  obtain ⟨C, hC⟩ := (f.map norm).exists_forall_le
  apply Integrable.of_bound f.measurable.aestronglyMeasurable C
  filter_upwards [] with x
  exact hC x

private lemma simpleIntegral_add_aux (f g : SimpleFunc ℝ ℂ) :
    T.simpleIntegral (f + g) = T.simpleIntegral f + T.simpleIntegral g := by
  let μ : Measure ℝ := Measure.dirac 0
  rw [T.simpleIntegral_eq_setToSimpleFunc (f + g) μ, T.simpleIntegral_eq_setToSimpleFunc f μ,
    T.simpleIntegral_eq_setToSimpleFunc g μ]
  exact SimpleFunc.setToSimpleFunc_add (spectralCLM T) (spectralCLM_finMeasAdditive T μ)
    (simpleFunc_integrable_dirac f) (simpleFunc_integrable_dirac g)

lemma simpleIntegral_add (f g : SimpleFunc ℝ ℂ) :
    T.simpleIntegral (f + g) = T.simpleIntegral f + T.simpleIntegral g :=
  simpleIntegral_add_aux T f g

private lemma simpleIntegral_neg_aux (f : SimpleFunc ℝ ℂ) :
    T.simpleIntegral (-f) = -T.simpleIntegral f := by
  let μ : Measure ℝ := Measure.dirac 0
  rw [T.simpleIntegral_eq_setToSimpleFunc (-f) μ, T.simpleIntegral_eq_setToSimpleFunc f μ]
  exact SimpleFunc.setToSimpleFunc_neg (spectralCLM T) (spectralCLM_finMeasAdditive T μ)
    (simpleFunc_integrable_dirac f)

lemma simpleIntegral_neg (f : SimpleFunc ℝ ℂ) :
    T.simpleIntegral (-f) = -T.simpleIntegral f :=
  simpleIntegral_neg_aux T f

lemma simpleIntegral_sub (f g : SimpleFunc ℝ ℂ) :
    T.simpleIntegral (f - g) = T.simpleIntegral f - T.simpleIntegral g := by
  calc
    T.simpleIntegral (f - g) = T.simpleIntegral (f + -g) := by rw [sub_eq_add_neg]
    _ = T.simpleIntegral f + T.simpleIntegral (-g) := T.simpleIntegral_add f (-g)
    _ = T.simpleIntegral f + -T.simpleIntegral g := by rw [T.simpleIntegral_neg]
    _ = T.simpleIntegral f - T.simpleIntegral g := by rw [sub_eq_add_neg]

lemma simpleIntegral_norm_le (f : SimpleFunc ℝ ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hCf : ∀ z ∈ f.range, ‖z‖ ≤ C) :
    ‖T.simpleIntegral f‖ ≤ C := by
  apply norm_sum_smul_le f.range
    (fun z ↦ (T.spectralMeasure (f ⁻¹' {z}) : A))
    (fun z ↦ z) C hC
  · intro z hz
    exact T.spectralMeasure.isStarProjection _
  · intro z hz w hw hzw
    apply T.spectralMeasure.comp_of_disjoint
    · refine Set.disjoint_left.2 ?_
      intro a ha hb
      have haz : f a = z := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using ha
      have haw : f a = w := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hb
      exact hzw (haz.symm.trans haw)
    · exact f.measurableSet_fiber _
    · exact f.measurableSet_fiber _
  · intro z hz hz0
    exact hCf z hz

lemma simpleIntegral_diff_norm_le (f g : SimpleFunc ℝ ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hfg : ∀ x, ‖f x - g x‖ ≤ C) :
    ‖T.simpleIntegral f - T.simpleIntegral g‖ ≤ C := by
  rw [← T.simpleIntegral_sub]
  apply T.simpleIntegral_norm_le (f - g) hC
  exact fun z hz => by
    rcases SimpleFunc.mem_range.1 hz with ⟨x, rfl⟩
    simpa only [SimpleFunc.sub_apply] using hfg x

lemma simpleIntegral_star (f : SimpleFunc ℝ ℂ) :
    T.simpleIntegral (star f) = star (T.simpleIntegral f) := by
  classical
  simp only [simpleIntegral, star_sum]
  refine Finset.sum_bij (fun z hz => star z) ?_ ?_ ?_ ?_
  · intro z hz
    rcases SimpleFunc.mem_range.1 hz with ⟨x, hx⟩
    apply SimpleFunc.mem_range.2
    refine ⟨x, ?_⟩
    change f x = star z
    have hx' := congrArg star hx
    change star (star (f x)) = star z at hx'
    simpa using hx'
  · intro z₁ hz₁ z₂ hz₂ h
    exact star_injective h
  · intro z hz
    rcases SimpleFunc.mem_range.1 hz with ⟨x, hx⟩
    refine ⟨star z, ?_, ?_⟩
    · apply SimpleFunc.mem_range.2
      refine ⟨x, ?_⟩
      change star (f x) = star z
      exact congrArg star hx
    · simp
  · intro z hz
    have hfiber : (⇑(star f) : ℝ → ℂ) ⁻¹' {z} = (⇑f : ℝ → ℂ) ⁻¹' {star z} := by
      ext x
      change star (f x) = z ↔ f x = star z
      constructor
      · intro h
        simpa using congrArg star h
      · intro h
        exact congrArg star h |>.trans (star_star z)
    rw [hfiber, star_smul, star_star]
    simp only [(T.spectralMeasure.isStarProjection _).isSelfAdjoint.star_eq]

lemma simpleIntegral_mul (f g : SimpleFunc ℝ ℂ) :
    T.simpleIntegral (f * g) = T.simpleIntegral f * T.simpleIntegral g := by
  let μ : Measure ℝ := Measure.dirac 0
  let p : SimpleFunc ℝ (ℂ × ℂ) := f.pair g
  have hf : Integrable f μ := simpleFunc_integrable_dirac f
  have hg : Integrable g μ := simpleFunc_integrable_dirac g
  have hp : Integrable p μ := SimpleFunc.integrable_pair hf hg
  have hadd := spectralCLM_finMeasAdditive T μ
  have hfst : T.simpleIntegral f =
      ∑ q ∈ p.range, q.1 • (T.spectralMeasure (p ⁻¹' {q}) : A) := by
    rw [T.simpleIntegral_eq_setToSimpleFunc f μ, ← SimpleFunc.map_fst_pair f g]
    rw [SimpleFunc.map_setToSimpleFunc (spectralCLM T) hadd hp Prod.fst_zero]
    simp only [spectralCLM_apply]
  have hsnd : T.simpleIntegral g =
      ∑ q ∈ p.range, q.2 • (T.spectralMeasure (p ⁻¹' {q}) : A) := by
    rw [T.simpleIntegral_eq_setToSimpleFunc g μ, ← SimpleFunc.map_snd_pair f g]
    rw [SimpleFunc.map_setToSimpleFunc (spectralCLM T) hadd hp Prod.snd_zero]
    simp only [spectralCLM_apply]
  have hmul : T.simpleIntegral (f * g) =
      ∑ q ∈ p.range, (q.1 * q.2) • (T.spectralMeasure (p ⁻¹' {q}) : A) := by
    rw [T.simpleIntegral_eq_setToSimpleFunc (f * g) μ, SimpleFunc.mul_eq_map₂]
    rw [SimpleFunc.map_setToSimpleFunc (spectralCLM T) hadd hp (by simp)]
    simp only [spectralCLM_apply]
  rw [hfst, hsnd, hmul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.sum_eq_single q]
  · rw [smul_mul_smul_comm, T.spectralMeasure.comp_self]
  · intro r hr hneq
    rw [smul_mul_smul_comm]
    have hdisj : Disjoint (p ⁻¹' {q}) (p ⁻¹' {r}) := by
      refine Set.disjoint_left.2 ?_
      intro x hxq hxr
      have hxq' : p x = q := by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hxq
      have hxr' : p x = r := by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hxr
      exact hneq (hxr'.symm.trans hxq')
    rw [T.spectralMeasure.comp_of_disjoint hdisj (p.measurableSet_fiber q)
      (p.measurableSet_fiber r), smul_zero]
  · intro hq'
    exact (hq' hq).elim

/-! ## Uniform simple approximation on bounded complex range

Pointwise simple approximation is not enough for a norm completion.  The following lemma records
the stronger fact needed here.  Its proof uses that a bounded subset of `ℂ` has compact closure:
the dense sequence used by `SimpleFunc.approxOn` gives an open cover by approximation balls, and
compactness reduces that cover to finitely many indices.  The maximum of those indices then works
simultaneously for every point of the range. -/

lemma exists_uniform_simple_approx {f : ℝ → ℂ} (hf : Measurable f)
    (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ s : ℕ → SimpleFunc ℝ ℂ,
      (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) ∧
      ∃ C, ∀ n x, ‖s n x‖ ≤ C := by
  rcases hbdd with ⟨C, hC⟩
  have hC0 : 0 ≤ C := by
    exact (norm_nonneg (f 0)).trans (hC 0)
  let K : Set ℂ := Metric.closedBall 0 C
  have hKcompact : IsCompact K := isCompact_closedBall 0 C
  letI : TopologicalSpace.SeparableSpace K := hKcompact.isSeparable.separableSpace
  have hK0 : (0 : ℂ) ∈ K := by simp [K, hC0]
  letI : Nonempty K := ⟨⟨0, hK0⟩⟩
  let e : ℕ → ℂ := fun k => Nat.casesOn k 0 ((↑) ∘ TopologicalSpace.denseSeq K)
  let s : ℕ → SimpleFunc ℝ ℂ := fun n =>
    SimpleFunc.approxOn f hf K 0 hK0 n
  refine ⟨s, ?_, ⟨C, ?_⟩⟩
  · intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    have hcover : K ⊆ ⋃ k : ℕ, Metric.ball (e k) (ε / 2) := by
      intro y hy
      have hycl : (⟨y, hy⟩ : K) ∈ closure (Set.range (TopologicalSpace.denseSeq K)) := by
        rw [(denseRange_iff_closure_range.mp (TopologicalSpace.denseRange_denseSeq K))]
        exact mem_univ _
      have hy_mem : (⟨y, hy⟩ : K) ∈ Metric.ball (⟨y, hy⟩ : K) (ε / 2) :=
        Metric.mem_ball_self hε2
      rcases (mem_closure_iff.1 hycl) _ Metric.isOpen_ball hy_mem with ⟨z, hz, hzr⟩
      rcases hzr with ⟨k, rfl⟩
      refine mem_iUnion.2 ⟨k + 1, ?_⟩
      have hz' := (Metric.mem_ball.mp hz)
      rw [Subtype.dist_eq] at hz'
      simpa [e, Function.comp_def, dist_comm] using hz'
    rcases hKcompact.elim_finite_subcover (fun k : ℕ => Metric.ball (e k) (ε / 2))
        (fun _ => Metric.isOpen_ball) hcover with ⟨t, ht⟩
    have ht_ne : t.Nonempty := by
      by_contra ht'
      have : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht'
      subst this
      simpa using (ht (show (0 : ℂ) ∈ K from hK0))
    let N : ℕ := t.sup id
    refine ⟨N, ?_⟩
    intro n hn x
    have hfxK : f x ∈ K := by
      rw [Metric.mem_closedBall]
      simpa [dist_eq_norm] using hC x
    rcases Set.mem_iUnion₂.1 (ht hfxK) with ⟨k, hkt, hkx⟩
    have hkn : k ≤ n := (Finset.le_sup hkt).trans hn
    have hnearest : edist (SimpleFunc.nearestPt e n (f x)) (f x) ≤ edist (e k) (f x) := by
      exact SimpleFunc.edist_nearestPt_le e (f x) hkn
    have hkx' : dist (e k) (f x) < ε / 2 := by
      simpa [dist_comm] using (Metric.mem_ball.mp hkx)
    have hdist : dist (s n x) (f x) < ε := by
      have hnearest' : edist (s n x) (f x) ≤ edist (e k) (f x) := by
        simpa [s, SimpleFunc.approxOn, e] using hnearest
      have hkxed : edist (e k) (f x) < ENNReal.ofReal ε := by
        rw [edist_dist]
        exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith [hkx'])
      have : edist (s n x) (f x) < ENNReal.ofReal ε := hnearest'.trans_lt hkxed
      rw [edist_dist] at this
      exact ENNReal.ofReal_lt_ofReal_iff hε |>.mp this
    simpa only [dist_eq_norm] using hdist
  · intro n x
    have hx := SimpleFunc.approxOn_mem hf hK0 n x
    rw [Metric.mem_closedBall] at hx
    simpa [dist_eq_norm] using hx

/-! ## The general (possibly unbounded) measurable functional calculus -/

/-- `f(T) = ∫ f \, dE_T`, for any Borel-measurable `f : ℝ → ℂ`, as an affiliated operator — the
pushforward of `T`'s spectral measure along `f`, via `PVM.map` (`Measurement/PVM.lean`). This is the
general interface everything else in this file specializes: bounded truncation, indicator
functions and the unitary group are all corollaries, not separate constructions. Genuinely built,
not merely a signature: `PVM.map` needs only measurability of `f`, and `f` need not be injective —
a genuine pushforward, not merely a reindexing as in `AffiliatedObservable.toAffiliatedOperator`. -/
def measurableFC (T : AffiliatedObservable A) (f : ℝ → ℂ) (hf : Measurable f) :
    AffiliatedOperator A where
  spectralMeasure := T.spectralMeasure.map f hf

/-- The defining identity of the measurable functional calculus at the level of spectral
projections: `E_{f(T)}(S) = E_T(f⁻¹ S)`, for Borel `S ⊆ ℂ`. -/
@[simp]
lemma measurableFC_spectralMeasure_apply {f : ℝ → ℂ} (hf : Measurable f) {S : Set ℂ}
    (hS : MeasurableSet S) :
    (T.measurableFC f hf).spectralMeasure S = T.spectralMeasure (f ⁻¹' S) :=
  T.spectralMeasure.map_apply hf hS

/-! ### Real measurable functional calculus

The complex-valued calculus above is the normal-operator view.  For a real-valued multiplier the
result is still self-adjoint spectral data, so expose that case directly as an
`AffiliatedObservable`.  This is useful for truncations and real Borel functions and avoids an
unnecessary round trip through `AffiliatedOperator`. -/

/-- Pull back a real-valued Borel functional calculus along a measurable `f : ℝ → ℝ`. -/
def measurableRealFC (T : AffiliatedObservable A) (f : ℝ → ℝ) (hf : Measurable f) :
    AffiliatedObservable A where
  spectralMeasure := T.spectralMeasure.map f hf

@[simp]
lemma measurableRealFC_spectralMeasure_apply {f : ℝ → ℝ} (hf : Measurable f)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (T.measurableRealFC f hf).spectralMeasure S = T.spectralMeasure (f ⁻¹' S) :=
  T.spectralMeasure.map_apply hf hS

theorem measurableRealFC_comp (T : AffiliatedObservable A)
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    (T.measurableRealFC f hf).measurableRealFC g hg =
      T.measurableRealFC (g ∘ f) (hg.comp hf) := by
  apply AffiliatedObservable.ext
  intro S hS
  rw [(T.measurableRealFC f hf).measurableRealFC_spectralMeasure_apply hg hS,
    T.measurableRealFC_spectralMeasure_apply (hg.comp hf) hS]
  change (T.spectralMeasure.map f hf) (g ⁻¹' S) = _
  rw [T.spectralMeasure.map_apply hf (hg hS)]
  congr 1

theorem measurableRealFC_id (T : AffiliatedObservable A) :
    T.measurableRealFC id measurable_id = T := by
  apply AffiliatedObservable.ext
  intro S hS
  rw [T.measurableRealFC_spectralMeasure_apply measurable_id hS]
  rfl

/-- The indicator of `[-R, R]`, used to define `realTruncate`. -/
def realTruncateFunction (R : ℝ) : ℝ → ℝ :=
  Set.Icc (-R) R |>.indicator id

lemma realTruncateFunction_measurable (R : ℝ) :
    Measurable (realTruncateFunction R) := by
  exact measurable_id.indicator measurableSet_Icc

lemma realTruncateFunction_mem_Icc {R x : ℝ} (hR : 0 ≤ R) :
    realTruncateFunction R x ∈ Set.Icc (-R) R := by
  by_cases hx : x ∈ Set.Icc (-R) R
  · simpa [realTruncateFunction, Set.indicator_of_mem hx] using hx
  · have hzero : (0 : ℝ) ∈ Set.Icc (-R) R := by constructor <;> linarith
    simpa [realTruncateFunction, Set.indicator_of_notMem hx] using hzero

/-- `T`, truncated to the spectral window `[-R, R]`. -/
def realTruncate (T : AffiliatedObservable A) (R : ℝ) : AffiliatedObservable A :=
  T.measurableRealFC (realTruncateFunction R) (realTruncateFunction_measurable R)

@[simp]
lemma realTruncate_spectralMeasure_apply (T : AffiliatedObservable A) (R : ℝ)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (T.realTruncate R).spectralMeasure S =
      T.spectralMeasure (realTruncateFunction R ⁻¹' S) :=
  T.measurableRealFC_spectralMeasure_apply (realTruncateFunction_measurable R) hS

lemma realTruncate_spectralMeasure_eq_zero_of_disjoint
    (T : AffiliatedObservable A) {R : ℝ} (hR : 0 ≤ R)
    {S : Set ℝ} (hS : MeasurableSet S)
    (hdisj : Disjoint S (Set.Icc (-R) R)) :
    (T.realTruncate R).spectralMeasure S = 0 := by
  rw [T.realTruncate_spectralMeasure_apply R hS]
  have hpre : realTruncateFunction R ⁻¹' S = ∅ := by
    ext x
    constructor
    · intro hx
      exact (Set.disjoint_left.1 hdisj hx (realTruncateFunction_mem_Icc hR))
    · simp
  rw [hpre]
  simp

end AffiliatedObservable

namespace AffiliatedOperator

variable {A : Type*} [OperatorAlgebra A]

/-- Apply a measurable complex-valued function to an arbitrary affiliated operator.  At the
representation-free level an affiliated operator is its spectral PVM, so the functional calculus
is exactly spectral pushforward. -/
def measurableFC (T : AffiliatedOperator A) (f : ℂ → ℂ) (hf : Measurable f) :
    AffiliatedOperator A where
  spectralMeasure := T.spectralMeasure.map f hf

@[simp]
lemma measurableFC_spectralMeasure_apply (T : AffiliatedOperator A)
    {f : ℂ → ℂ} (hf : Measurable f) {S : Set ℂ} (hS : MeasurableSet S) :
    (T.measurableFC f hf).spectralMeasure S = T.spectralMeasure (f ⁻¹' S) :=
  T.spectralMeasure.map_apply hf hS

lemma measurableFC_comp_spectralMeasure_apply (T : AffiliatedObservable A)
    {f : ℝ → ℂ} {g : ℂ → ℂ} (hf : Measurable f) (hg : Measurable g)
    {S : Set ℂ} (hS : MeasurableSet S) :
    ((T.measurableFC f hf).measurableFC g hg).spectralMeasure S =
      T.spectralMeasure ((g ∘ f) ⁻¹' S) := by
  rw [AffiliatedOperator.measurableFC_spectralMeasure_apply
      (T.measurableFC f hf) hg hS,
    T.measurableFC_spectralMeasure_apply hf (hg hS)]
  rfl

lemma measurableFC_id_spectralMeasure (T : AffiliatedOperator A) {S : Set ℂ}
    (hS : MeasurableSet S) :
    (T.measurableFC id measurable_id).spectralMeasure S = T.spectralMeasure S := by
  rw [T.measurableFC_spectralMeasure_apply measurable_id hS]
  rfl

@[ext]
theorem ext {S U : AffiliatedOperator A}
    (h : ∀ X : Set ℂ, MeasurableSet X → S.spectralMeasure X = U.spectralMeasure X) :
    S = U := by
  cases S with
  | mk S =>
    cases U with
    | mk U =>
      congr
      exact OperatorAlgebra.PVM.ext h

theorem measurableFC_id (T : AffiliatedOperator A) :
    T.measurableFC id measurable_id = T := by
  apply ext
  intro S hS
  exact T.measurableFC_id_spectralMeasure hS

/- The full composition law for the complex measurable calculus.  The real-to-complex version
above is the self-adjoint specialization; this theorem is the reusable operator-level statement. -/
theorem measurableFC_comp_operator (T : AffiliatedOperator A)
    {f g : ℂ → ℂ} (hf : Measurable f) (hg : Measurable g) :
    (T.measurableFC f hf).measurableFC g hg =
      T.measurableFC (g ∘ f) (hg.comp hf) := by
  apply ext
  intro S hS
  calc
    ((T.measurableFC f hf).measurableFC g hg).spectralMeasure S =
        (T.measurableFC f hf).spectralMeasure (g ⁻¹' S) :=
      AffiliatedOperator.measurableFC_spectralMeasure_apply
        (T.measurableFC f hf) hg hS
    _ = T.spectralMeasure (f ⁻¹' (g ⁻¹' S)) :=
      AffiliatedOperator.measurableFC_spectralMeasure_apply T hf (hg hS)
    _ = T.spectralMeasure ((g ∘ f) ⁻¹' S) := by
      congr 1
    _ = (T.measurableFC (g ∘ f) (hg.comp hf)).spectralMeasure S :=
      (AffiliatedOperator.measurableFC_spectralMeasure_apply T (hg.comp hf) hS).symm

theorem measurableFC_comp (T : AffiliatedObservable A)
    {f : ℝ → ℂ} {g : ℂ → ℂ} (hf : Measurable f) (hg : Measurable g) :
    (T.measurableFC f hf).measurableFC g hg =
      T.measurableFC (g ∘ f) (hg.comp hf) := by
  apply ext
  intro S hS
  rw [T.measurableFC_spectralMeasure_apply (hg.comp hf) hS]
  exact measurableFC_comp_spectralMeasure_apply T hf hg hS

end AffiliatedOperator

namespace AffiliatedObservable

variable {A : Type*} [OperatorAlgebra A] (T : AffiliatedObservable A)

theorem measurableRealFC_toAffiliatedOperator
    (T : AffiliatedObservable A) {f : ℝ → ℝ} (hf : Measurable f) :
    (T.measurableRealFC f hf).toAffiliatedOperator =
      T.measurableFC
        (Complex.ofReal ∘ f) (Complex.measurable_ofReal.comp hf) := by
  apply AffiliatedOperator.ext
  intro S hS
  rw [AffiliatedObservable.toAffiliatedOperator_spectralMeasure_apply _ hS,
    T.measurableFC_spectralMeasure_apply
      (Complex.measurable_ofReal.comp hf) hS]
  change (T.spectralMeasure.map f hf) (Complex.ofReal ⁻¹' S) = _
  rw [T.spectralMeasure.map_apply hf (Complex.measurable_ofReal hS)]
  congr 1

/-! ## The bounded measurable functional calculus -/

/-- `f(T) ∈ A`, for a *bounded* Borel-measurable `f : ℝ → ℂ`: unlike the general
`measurableFC`, this genuinely lands in the algebra `A` itself rather than merely being another
affiliated operator, since a bounded operator with spectrum inside `f`'s bounded range is
automatically norm-bounded.

**Honesty note.** Unlike `Observable.toAffiliatedObservable` (`Affiliated.lean`), this
construction does *not* need `A` upgraded to a von Neumann algebra: we are not building a PVM from
scratch (which for a non-weakly-closed C⋆-algebra genuinely can fail to land back in `A`), we are
*integrating a bounded measurable function against a PVM `T.spectralMeasure` that already exists*,
and `A` is norm-complete, so norm-limits of finite `A`-linear combinations of the projections
`E_T(S_k) ∈ A` themselves stay in `A`. The uniform simple approximation, the orthogonal-fibre
norm estimate, the norm completion, and the additive/multiplicative/star laws are all proved below.
This is the bounded spectral-data calculus; the separate concrete domain-aware realization of an
unbounded multiplier remains in `Operators/SpectralTheory`. -/
lemma simpleIntegral_cauchySeq {f : ℝ → ℂ} {s : ℕ → SimpleFunc ℝ ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) :
    CauchySeq (fun n => T.simpleIntegral (s n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  rcases hs (ε / 4) (by linarith) with ⟨N, hN⟩
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmn : ∀ x, ‖s m x - s n x‖ ≤ ε / 2 := by
    intro x
    apply le_of_lt
    calc
      ‖s m x - s n x‖ ≤ ‖s m x - f x‖ + ‖s n x - f x‖ := by
        calc
          ‖s m x - s n x‖ = ‖(s m x - f x) - (s n x - f x)‖ := by ring_nf
          _ ≤ ‖s m x - f x‖ + ‖s n x - f x‖ := norm_sub_le _ _
      _ < ε / 4 + ε / 4 := add_lt_add (hN m hm x) (hN n hn x)
      _ = ε / 2 := by ring
  have hbound : ‖T.simpleIntegral (s m) - T.simpleIntegral (s n)‖ ≤ ε / 2 :=
    T.simpleIntegral_diff_norm_le (s m) (s n) (by linarith) hmn
  have hbound' : dist (T.simpleIntegral (s m)) (T.simpleIntegral (s n)) ≤ ε / 2 := by
    simpa only [dist_eq_norm] using hbound
  exact lt_of_le_of_lt hbound' (by linarith)

/-- The bounded Borel functional calculus, constructed as a norm limit of finite spectral sums.

The chosen approximating sequence is uniformly convergent by `exists_uniform_simple_approx`; the
orthogonal-fibre estimate makes its integrated sequence Cauchy, and completeness of the operator
algebra supplies the value.  Thus this definition uses only the PVM already carried by `T`, not a
von Neumann closure axiom. -/
def boundedFC (T : AffiliatedObservable A) (f : ℝ → ℂ) (hf : Measurable f)
    (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) : A := by
  classical
  let s : ℕ → SimpleFunc ℝ ℂ :=
    Classical.choose (exists_uniform_simple_approx hf hbdd)
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hbdd)).1
  have _hCauchy : CauchySeq (fun n => T.simpleIntegral (s n)) :=
    simpleIntegral_cauchySeq T hs
  exact Filter.atTop.limUnder (fun n => T.simpleIntegral (s n))

lemma boundedFC_eq_limUnder {f : ℝ → ℂ} (hf : Measurable f)
    (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) {s : ℕ → SimpleFunc ℝ ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) :
    T.boundedFC f hf hbdd = Filter.atTop.limUnder (fun n => T.simpleIntegral (s n)) := by
  classical
  let s₀ : ℕ → SimpleFunc ℝ ℂ :=
    Classical.choose (exists_uniform_simple_approx hf hbdd)
  have hs₀ : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s₀ n x - f x‖ < ε :=
    (Classical.choose_spec (exists_uniform_simple_approx hf hbdd)).1
  have hc₀ : CauchySeq (fun n => T.simpleIntegral (s₀ n)) :=
    simpleIntegral_cauchySeq T hs₀
  have hlim₀ : Filter.Tendsto (fun n => T.simpleIntegral (s₀ n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => T.simpleIntegral (s₀ n)))) :=
    hc₀.tendsto_limUnder
  have hdist : Filter.Tendsto (fun n => dist (T.simpleIntegral (s₀ n)) (T.simpleIntegral (s n)))
      Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases hs₀ (ε / 3) (by linarith) with ⟨N₀, hN₀⟩
    rcases hs (ε / 3) (by linarith) with ⟨N, hN⟩
    refine ⟨max N₀ N, fun n hn => ?_⟩
    have hpoint : ∀ x, ‖s₀ n x - s n x‖ ≤ 2 * ε / 3 := by
      intro x
      apply le_of_lt
      calc
        ‖s₀ n x - s n x‖ ≤ ‖s₀ n x - f x‖ + ‖s n x - f x‖ := by
          calc
            ‖s₀ n x - s n x‖ = ‖(s₀ n x - f x) - (s n x - f x)‖ := by ring_nf
            _ ≤ ‖s₀ n x - f x‖ + ‖s n x - f x‖ := norm_sub_le _ _
        _ < ε / 3 + ε / 3 := add_lt_add
          (hN₀ n (le_trans (le_max_left _ _) hn) x)
          (hN n (le_trans (le_max_right _ _) hn) x)
        _ = 2 * ε / 3 := by ring
    have hbound := T.simpleIntegral_diff_norm_le (s₀ n) (s n) (by linarith) hpoint
    have hlt : ‖T.simpleIntegral (s₀ n) - T.simpleIntegral (s n)‖ < ε :=
      lt_of_le_of_lt hbound (by linarith)
    change dist (dist (T.simpleIntegral (s₀ n)) (T.simpleIntegral (s n))) 0 < ε
    rw [dist_zero_right]
    simpa [dist_eq_norm, Real.norm_of_nonneg (norm_nonneg
      (T.simpleIntegral (s₀ n) - T.simpleIntegral (s n)))] using hlt
  have hlim : Filter.Tendsto (fun n => T.simpleIntegral (s n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => T.simpleIntegral (s₀ n)))) :=
    hlim₀.congr_dist hdist
  have heq := hlim.limUnder_eq
  unfold boundedFC
  dsimp [s₀] at heq ⊢
  exact heq.symm

lemma boundedFC_congr {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∀ x, f x = g x) :
    T.boundedFC f hf hbf = T.boundedFC g hg hbg := by
  classical
  rcases exists_uniform_simple_approx hf hbf with ⟨s, hs, hsB⟩
  have hs' : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - g x‖ < ε := by
    intro ε hε
    rcases hs ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn x => ?_⟩
    rw [← hfg x]
    exact hN n hn x
  calc
    T.boundedFC f hf hbf = Filter.atTop.limUnder (fun n => T.simpleIntegral (s n)) :=
      T.boundedFC_eq_limUnder hf hbf hs
    _ = T.boundedFC g hg hbg :=
      (T.boundedFC_eq_limUnder hg hbg hs').symm

lemma boundedFC_of_simpleFunc (f : SimpleFunc ℝ ℂ) (hf : Measurable (fun x => f x))
    (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    T.boundedFC (fun x => f x) hf hbdd = T.simpleIntegral f := by
  have hlim : Filter.Tendsto (fun _ : ℕ => T.simpleIntegral f) Filter.atTop
      (nhds (T.simpleIntegral f)) := tendsto_const_nhds
  have happrox : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x, ‖f x - f x‖ < ε := by
    intro ε hε
    exact ⟨0, fun n hn x => by simpa using hε⟩
  rw [T.boundedFC_eq_limUnder hf hbdd happrox]
  exact hlim.limUnder_eq

lemma simpleIntegral_const (c : ℂ) :
    T.simpleIntegral (SimpleFunc.const ℝ c) = c • (1 : A) := by
  classical
  simp only [simpleIntegral, SimpleFunc.range_const, Finset.sum_singleton]
  rw [show (⇑(SimpleFunc.const ℝ c) : ℝ → ℂ) ⁻¹' ({c} : Set ℂ) = Set.univ by ext x; simp,
    T.spectralMeasure.univ]

lemma boundedFC_const (c : ℂ) :
    T.boundedFC (fun _ : ℝ => c) (by fun_prop)
        (show ∃ C : ℝ, ∀ x : ℝ, ‖c‖ ≤ C from ⟨‖c‖, fun _ => le_rfl⟩) = c • (1 : A) := by
  let hbdd : ∃ C : ℝ, ∀ x : ℝ, ‖c‖ ≤ C := ⟨‖c‖, fun _ => le_rfl⟩
  have h := T.boundedFC_of_simpleFunc (SimpleFunc.const ℝ c) (by fun_prop) hbdd
  rw [T.simpleIntegral_const] at h
  convert h using 1 <;> simp [SimpleFunc.const]

lemma boundedFC_add {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    T.boundedFC (f + g) (hf.add hg)
        (by
          rcases hbf with ⟨Cf, hCf⟩
          rcases hbg with ⟨Cg, hCg⟩
          refine ⟨Cf + Cg, ?_⟩
          intro x
          exact (norm_add_le _ _).trans (add_le_add (hCf x) (hCg x))) =
      T.boundedFC f hf hbf + T.boundedFC g hg hbg := by
  classical
  rcases exists_uniform_simple_approx hf hbf with ⟨sf, hsf, hsfB⟩
  rcases exists_uniform_simple_approx hg hbg with ⟨sg, hsg, hsgB⟩
  have hsum : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(sf n + sg n) x - (f + g) x‖ < ε := by
    intro ε hε
    rcases hsf (ε / 2) (by linarith) with ⟨Nf, hNf⟩
    rcases hsg (ε / 2) (by linarith) with ⟨Ng, hNg⟩
    refine ⟨max Nf Ng, fun n hn x => ?_⟩
    simp only [SimpleFunc.add_apply, Pi.add_apply]
    calc
      ‖(sf n x + sg n x) - (f x + g x)‖ =
          ‖(sf n x - f x) + (sg n x - g x)‖ := by ring_nf
      _ ≤ ‖sf n x - f x‖ + ‖sg n x - g x‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add
        (hNf n (le_trans (le_max_left _ _) hn) x)
        (hNg n (le_trans (le_max_right _ _) hn) x)
      _ = ε := by ring
  have hcf : CauchySeq (fun n => T.simpleIntegral (sf n)) :=
    simpleIntegral_cauchySeq T hsf
  have hcg : CauchySeq (fun n => T.simpleIntegral (sg n)) :=
    simpleIntegral_cauchySeq T hsg
  have hlf : Filter.Tendsto (fun n => T.simpleIntegral (sf n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => T.simpleIntegral (sf n)))) :=
    hcf.tendsto_limUnder
  have hlg : Filter.Tendsto (fun n => T.simpleIntegral (sg n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => T.simpleIntegral (sg n)))) :=
    hcg.tendsto_limUnder
  have hlsum := hlf.add hlg
  calc
    T.boundedFC (f + g) (hf.add hg) _ =
        Filter.atTop.limUnder (fun n => T.simpleIntegral (sf n + sg n)) :=
      T.boundedFC_eq_limUnder (hf.add hg) _ hsum
    _ = Filter.atTop.limUnder
        (fun n => T.simpleIntegral (sf n) + T.simpleIntegral (sg n)) := by
      congr 1
      funext n
      exact T.simpleIntegral_add (sf n) (sg n)
    _ = Filter.atTop.limUnder (fun n => T.simpleIntegral (sf n)) +
        Filter.atTop.limUnder (fun n => T.simpleIntegral (sg n)) := hlsum.limUnder_eq
    _ = T.boundedFC f hf hbf + T.boundedFC g hg hbg := by
      rw [← T.boundedFC_eq_limUnder hf hbf hsf, ← T.boundedFC_eq_limUnder hg hbg hsg]

lemma boundedFC_mul {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    T.boundedFC (f * g) (hf.mul hg)
        (by
          rcases hbf with ⟨Cf, hCf⟩
          rcases hbg with ⟨Cg, hCg⟩
          have hCf0 : 0 ≤ Cf := (norm_nonneg (f 0)).trans (hCf 0)
          have hCg0 : 0 ≤ Cg := (norm_nonneg (g 0)).trans (hCg 0)
          refine ⟨Cf * Cg, ?_⟩
          intro x
          rw [Pi.mul_apply, norm_mul]
          exact mul_le_mul (hCf x) (hCg x) (norm_nonneg _) hCf0) =
      T.boundedFC f hf hbf * T.boundedFC g hg hbg := by
  classical
  rcases hbf with ⟨Cf, hCf⟩
  rcases hbg with ⟨Cg, hCg⟩
  let hbf' : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := ⟨Cf, hCf⟩
  let hbg' : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := ⟨Cg, hCg⟩
  rcases exists_uniform_simple_approx hf hbf' with ⟨sf, hsf, hsfB⟩
  rcases exists_uniform_simple_approx hg hbg' with ⟨sg, hsg, hsgB⟩
  have hCf0 : 0 ≤ Cf := (norm_nonneg (f 0)).trans (hCf 0)
  have hCg0 : 0 ≤ Cg := (norm_nonneg (g 0)).trans (hCg 0)
  rcases hsfB with ⟨Cs, hCs⟩
  have hCs0 : 0 ≤ Cs := (norm_nonneg (sf 0 0)).trans (hCs 0 0)
  have hD0 : 0 < Cs + Cg + 1 := by linarith
  have hprod : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(sf n * sg n) x - (f * g) x‖ < ε := by
    intro ε hε
    let δ : ℝ := ε / (2 * (Cs + Cg + 1))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    rcases hsf (δ) hδ with ⟨Nf, hNf⟩
    rcases hsg (δ) hδ with ⟨Ng, hNg⟩
    refine ⟨max Nf Ng, fun n hn x => ?_⟩
    simp only [SimpleFunc.mul_apply, Pi.mul_apply]
    have hsferr : ‖sf n x - f x‖ < δ := hNf n (le_trans (le_max_left _ _) hn) x
    have hsgerr : ‖sg n x - g x‖ < δ := hNg n (le_trans (le_max_right _ _) hn) x
    have hdecomp : sf n x * sg n x - f x * g x =
        sf n x * (sg n x - g x) + (sf n x - f x) * g x := by ring
    calc
      ‖sf n x * sg n x - f x * g x‖ =
          ‖sf n x * (sg n x - g x) + (sf n x - f x) * g x‖ := by rw [hdecomp]
      _ ≤ ‖sf n x‖ * ‖sg n x - g x‖ +
          ‖sf n x - f x‖ * ‖g x‖ := by
            calc
              _ ≤ ‖sf n x * (sg n x - g x)‖ +
                  ‖(sf n x - f x) * g x‖ := norm_add_le _ _
              _ = _ := by rw [norm_mul, norm_mul]
      _ ≤ Cs * δ + δ * Cg := by
        exact add_le_add
          (mul_le_mul (hCs n x) (le_of_lt hsgerr) (norm_nonneg _) hCs0)
          (mul_le_mul (le_of_lt hsferr) (hCg x) (norm_nonneg _) hδ.le)
      _ < ε := by
        calc
          Cs * δ + δ * Cg = (Cs + Cg) * δ := by ring
          _ ≤ (Cs + Cg + 1) * δ := by
            exact mul_le_mul_of_nonneg_right (by linarith) hδ.le
          _ = ε / 2 := by
            dsimp [δ]
            field_simp
          _ < ε := by linarith
  have hcf : CauchySeq (fun n => T.simpleIntegral (sf n)) :=
    simpleIntegral_cauchySeq T hsf
  have hcg : CauchySeq (fun n => T.simpleIntegral (sg n)) :=
    simpleIntegral_cauchySeq T hsg
  have hlf : Filter.Tendsto (fun n => T.simpleIntegral (sf n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => T.simpleIntegral (sf n)))) :=
    hcf.tendsto_limUnder
  have hlg : Filter.Tendsto (fun n => T.simpleIntegral (sg n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => T.simpleIntegral (sg n)))) :=
    hcg.tendsto_limUnder
  have hmul := hlf.mul hlg
  calc
    T.boundedFC (f * g) (hf.mul hg) _ =
        Filter.atTop.limUnder (fun n => T.simpleIntegral (sf n * sg n)) :=
      T.boundedFC_eq_limUnder (hf.mul hg) _ hprod
    _ = Filter.atTop.limUnder
        (fun n => T.simpleIntegral (sf n) * T.simpleIntegral (sg n)) := by
      congr 1
      funext n
      exact T.simpleIntegral_mul (sf n) (sg n)
    _ = Filter.atTop.limUnder (fun n => T.simpleIntegral (sf n)) *
        Filter.atTop.limUnder (fun n => T.simpleIntegral (sg n)) := hmul.limUnder_eq
    _ = T.boundedFC f hf hbf' * T.boundedFC g hg hbg' := by
      rw [← T.boundedFC_eq_limUnder hf hbf' hsf,
        ← T.boundedFC_eq_limUnder hg hbg' hsg]

lemma boundedFC_smul {f : ℝ → ℂ} (c : ℂ) (hf : Measurable f)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    T.boundedFC (fun x => c * f x) (measurable_const.mul hf)
        (by
          rcases hbf with ⟨C, hC⟩
          refine ⟨‖c‖ * C, fun x => ?_⟩
          rw [norm_mul]
          exact mul_le_mul (le_rfl) (hC x) (norm_nonneg _) (by
            exact norm_nonneg c)) =
      c • T.boundedFC f hf hbf := by
  rcases hbf with ⟨C, hC⟩
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  let hcf : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := ⟨C, hC⟩
  have hmul := T.boundedFC_mul
    (f := fun _ : ℝ => c) (g := f) (by fun_prop) hf
    (⟨‖c‖, fun _ => le_rfl⟩) hcf
  calc
    T.boundedFC (fun x => c * f x) (measurable_const.mul hf) _ =
        T.boundedFC ((fun _ : ℝ => c) * f) (by fun_prop) _ := by
          rfl
    _ = T.boundedFC (fun _ : ℝ => c) (by fun_prop) (⟨‖c‖, fun _ => le_rfl⟩) *
        T.boundedFC f hf hcf := hmul
    _ = c • T.boundedFC f hf hcf := by
      rw [T.boundedFC_const]
      simp [smul_mul_assoc]

lemma boundedFC_neg {f : ℝ → ℂ} (hf : Measurable f)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    T.boundedFC (fun x => -f x) (by fun_prop)
        (by
          rcases hbf with ⟨C, hC⟩
          exact ⟨C, fun x => by simpa using hC x⟩) =
      -T.boundedFC f hf hbf := by
  have h := T.boundedFC_smul (-1) hf hbf
  convert h using 1 <;> simp

lemma boundedFC_sub {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    T.boundedFC (f - g) (hf.sub hg)
        (by
          rcases hbf with ⟨Cf, hCf⟩
          rcases hbg with ⟨Cg, hCg⟩
          refine ⟨Cf + Cg, fun x => ?_⟩
          exact (norm_sub_le _ _).trans (add_le_add (hCf x) (hCg x))) =
      T.boundedFC f hf hbf - T.boundedFC g hg hbg := by
  have hneg := T.boundedFC_neg hg hbg
  have hadd := T.boundedFC_add hf (continuous_neg.measurable.comp hg)
    hbf (by
      rcases hbg with ⟨C, hC⟩
      exact ⟨C, fun x => by simpa using hC x⟩)
  calc
    T.boundedFC (f - g) (hf.sub hg) _ =
        T.boundedFC (f + (fun x => -g x)) (hf.add (continuous_neg.measurable.comp hg)) _ := by
          apply T.boundedFC_congr (hf.sub hg)
            (hf.add (continuous_neg.measurable.comp hg))
            (by
              rcases hbf with ⟨Cf, hCf⟩
              rcases hbg with ⟨Cg, hCg⟩
              refine ⟨Cf + Cg, fun x => ?_⟩
              exact (norm_sub_le _ _).trans (add_le_add (hCf x) (hCg x)))
            (by
              rcases hbf with ⟨Cf, hCf⟩
              rcases hbg with ⟨Cg, hCg⟩
              refine ⟨Cf + Cg, fun x => ?_⟩
              exact (norm_add_le _ _).trans
                (add_le_add (hCf x) (by simpa using hCg x)))
          · intro x
            simp [Pi.sub_apply, Pi.add_apply, Function.comp_apply, sub_eq_add_neg]
    _ = T.boundedFC f hf hbf + T.boundedFC (fun x => -g x)
        (continuous_neg.measurable.comp hg) _ :=
      T.boundedFC_add hf (continuous_neg.measurable.comp hg) hbf (by
        rcases hbg with ⟨C, hC⟩
        exact ⟨C, fun x => by simpa using hC x⟩)
    _ = T.boundedFC f hf hbf - T.boundedFC g hg hbg := by
      rw [hneg]
      simp only [sub_eq_add_neg]

lemma boundedFC_star {f : ℝ → ℂ} (hf : Measurable f)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    T.boundedFC (fun x => star (f x)) (continuous_star.measurable.comp hf)
        (by simpa only [norm_star] using hbf) =
      star (T.boundedFC f hf hbf) := by
  classical
  have hbstar : ∃ C, ∀ x, ‖star (f x)‖ ≤ C := by
    simpa only [norm_star] using hbf
  rcases exists_uniform_simple_approx hf hbf with ⟨sf, hsf, hsfB⟩
  have hstar : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      ‖(star (sf n)) x - star (f x)‖ < ε := by
    intro ε hε
    rcases hsf ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn x => ?_⟩
    change ‖star ((sf n) x) - star (f x)‖ < ε
    simpa only [← star_sub, norm_star] using hN n hn x
  have hcf : CauchySeq (fun n => T.simpleIntegral (sf n)) :=
    simpleIntegral_cauchySeq T hsf
  have hlf : Filter.Tendsto (fun n => T.simpleIntegral (sf n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => T.simpleIntegral (sf n)))) :=
    hcf.tendsto_limUnder
  have hls : Filter.Tendsto (fun n => T.simpleIntegral (star (sf n))) Filter.atTop
      (nhds (star (Filter.atTop.limUnder (fun n => T.simpleIntegral (sf n))))) := by
    simpa only [T.simpleIntegral_star] using hlf.star
  calc
    T.boundedFC (fun x => star (f x)) (continuous_star.measurable.comp hf) hbstar =
        Filter.atTop.limUnder (fun n => T.simpleIntegral (star (sf n))) :=
      T.boundedFC_eq_limUnder (continuous_star.measurable.comp hf) hbstar hstar
    _ = star (Filter.atTop.limUnder (fun n => T.simpleIntegral (sf n))) := hls.limUnder_eq
    _ = star (T.boundedFC f hf hbf) := by
      rw [show T.boundedFC f hf hbf =
          Filter.atTop.limUnder (fun n => T.simpleIntegral (sf n)) by
            exact T.boundedFC_eq_limUnder hf hbf hsf]

lemma boundedFC_mem_unitary {f : ℝ → ℂ} (hf : Measurable f)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hmod : ∀ x, star (f x) * f x = 1) :
    T.boundedFC f hf hbf ∈ unitary A := by
  classical
  have hbstar : ∃ C, ∀ x, ‖star (f x)‖ ≤ C := by
    simpa only [norm_star] using hbf
  have hmod' : ∀ x, f x * star (f x) = 1 := by
    intro x
    simpa [mul_comm] using hmod x
  have hm₁ := T.boundedFC_mul (f := fun x => star (f x)) (g := f)
    (continuous_star.measurable.comp hf) hf hbstar hbf
  have hm₂ := T.boundedFC_mul (f := f) (g := fun x => star (f x))
    hf (continuous_star.measurable.comp hf) hbf hbstar
  have hstarFC := T.boundedFC_star hf hbf
  have hone : T.boundedFC (fun _ : ℝ => (1 : ℂ)) (by fun_prop)
      (show ∃ C : ℝ, ∀ _ : ℝ, ‖(1 : ℂ)‖ ≤ C from ⟨1, by simp⟩) = (1 : A) := by
    simpa using T.boundedFC_const 1
  have h₁ : star (T.boundedFC f hf hbf) * T.boundedFC f hf hbf = 1 := by
    calc
      star (T.boundedFC f hf hbf) * T.boundedFC f hf hbf =
          T.boundedFC (fun x => star (f x)) (continuous_star.measurable.comp hf) hbstar *
            T.boundedFC f hf hbf := by rw [hstarFC]
      _ = T.boundedFC ((fun x => star (f x)) * f) _ _ := hm₁.symm
      _ = T.boundedFC (fun _ : ℝ => (1 : ℂ)) (by fun_prop) _ := by
        have heq : (fun x => star (f x)) * f = (fun _ : ℝ => (1 : ℂ)) := by
          funext x
          simpa only [Pi.mul_apply] using hmod x
        exact T.boundedFC_congr _ _ _ _ (fun x => congrFun heq x)
      _ = 1 := hone
  have h₂ : T.boundedFC f hf hbf * star (T.boundedFC f hf hbf) = 1 := by
    calc
      T.boundedFC f hf hbf * star (T.boundedFC f hf hbf) =
          T.boundedFC f hf hbf *
            T.boundedFC (fun x => star (f x)) (continuous_star.measurable.comp hf) hbstar := by
              rw [hstarFC]
      _ = T.boundedFC (f * (fun x => star (f x))) _ _ := hm₂.symm
      _ = T.boundedFC (fun _ : ℝ => (1 : ℂ)) (by fun_prop) _ := by
        have heq : f * (fun x => star (f x)) = (fun _ : ℝ => (1 : ℂ)) := by
          funext x
          simpa only [Pi.mul_apply] using hmod' x
        exact T.boundedFC_congr _ _ _ _ (fun x => congrFun heq x)
      _ = 1 := hone
  exact ⟨h₁, h₂⟩

/- The norm completion is independent of the approximating sequence and satisfies the expected
additive, multiplicative, involutive, constant, and unitary laws. -/

/- The compatibility between the bounded and general functional calculus: for bounded `f`,
`measurableFC` (an `AffiliatedOperator`) agrees with `boundedFC` included via
`Observable.toAffiliatedObservable`/its `AffiliatedOperator` counterpart. Bounded spectral
truncation is meant to be recoverable as a corollary of this compatibility, per the file's
overview. -/
/- The representation-level compatibility of `boundedFC` with the concrete Hilbert-space
spectral integral is proved in `Unbounded/Representation.lean`.  The remaining distinction is
intentional: `measurableFC` is an unbounded spectral-data object, whereas `boundedFC` is its
bounded realization inside the abstract algebra, so an equality between the two
representation-free types would require a concrete operator/domain representation. -/

/-! ## Convenient bounded operations, as corollaries -/

/-- The bounded measurable function representing a spectral indicator. -/
def indicatorFunction (S : Set ℝ) : ℝ → ℂ :=
  S.indicator (fun _ : ℝ => (1 : ℂ))

lemma indicatorFunction_measurable {S : Set ℝ} (hS : MeasurableSet S) :
    Measurable (indicatorFunction S) := by
  exact measurable_const.indicator hS

lemma indicatorFunction_bounded (S : Set ℝ) :
    ∃ C, ∀ x, ‖indicatorFunction S x‖ ≤ C := by
  refine ⟨1, ?_⟩
  intro x
  by_cases hx : x ∈ S <;> simp [indicatorFunction, hx]

/-- The bounded spectral integral sends an indicator function to the corresponding PVM
projection.  This is the bridge between the norm-completed simple integral and the primitive
spectral projections, and is the basic identity behind all cutoff constructions. -/
lemma boundedFC_indicator {S : Set ℝ} (hS : MeasurableSet S) :
    T.boundedFC (indicatorFunction S) (indicatorFunction_measurable hS)
      (indicatorFunction_bounded S) = (T.spectralMeasure S : A) := by
  classical
  let f : SimpleFunc ℝ ℂ :=
    SimpleFunc.piecewise S hS (SimpleFunc.const ℝ 1) (SimpleFunc.const ℝ 0)
  have hf : (fun x : ℝ => f x) = indicatorFunction S := by
    funext x
    change S.indicator (fun _ : ℝ => (1 : ℂ)) x = indicatorFunction S x
    rfl
  have hfb : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    refine ⟨1, ?_⟩
    intro x
    by_cases hx : x ∈ S <;> simp [f, hx]
  have hcalc := T.boundedFC_of_simpleFunc f (by fun_prop) hfb
  have hsimple : T.simpleIntegral f = (T.spectralMeasure S : A) := by
    rw [T.simpleIntegral_eq_setToSimpleFunc f (Measure.dirac 0)]
    exact (SimpleFunc.setToSimpleFunc_indicator (spectralCLM T)
      (by simp [spectralCLM]) hS 1).trans (by simp [spectralCLM_apply])
  calc
    T.boundedFC (indicatorFunction S) (indicatorFunction_measurable hS)
        (indicatorFunction_bounded S) = T.boundedFC (fun x : ℝ => f x) (by fun_prop) hfb := by
      apply T.boundedFC_congr (indicatorFunction_measurable hS) (by fun_prop)
        (indicatorFunction_bounded S) hfb
      exact fun x => (hf.symm ▸ rfl)
    _ = T.simpleIntegral f := hcalc
    _ = (T.spectralMeasure S : A) := hsimple

/-- The indicator function `1_S(T)`, recovering the spectral projection directly — this is the
special case `f = S.indicator 1` of `boundedFC`, and should coincide definitionally-up-to-proof
with `T.spectralProjection S` rather than requiring separate foundational treatment. -/
def indicator (T : AffiliatedObservable A) (S : Set ℝ) : Projection A := T.spectralProjection S

@[simp]
lemma indicator_eq_spectralProjection (S : Set ℝ) : T.indicator S = T.spectralProjection S := rfl

/-- The unitary group `e^{itT}` generated by `T`, for `t : ℝ` — Stone's theorem's forward
direction, as a corollary of the bounded functional calculus applied to the bounded function
`x ↦ exp (i t x)`. -/
def expFunction (t : ℝ) : ℝ → ℂ :=
  fun x => Complex.exp ((t * x : ℝ) * Complex.I)

lemma expFunction_measurable (t : ℝ) : Measurable (expFunction t) := by
  change Measurable (fun x : ℝ => Complex.exp ((t * x : ℝ) * Complex.I))
  fun_prop

lemma expFunction_bounded (t : ℝ) : ∃ C, ∀ x, ‖expFunction t x‖ ≤ C := by
  refine ⟨1, fun x => ?_⟩
  exact (Complex.norm_exp_ofReal_mul_I (t * x)).le

lemma expFunction_modulus (t : ℝ) : ∀ x, star (expFunction t x) * expFunction t x = 1 := by
  intro x
  change (starRingEnd ℂ) (Complex.exp ((t * x : ℝ) * Complex.I)) *
      Complex.exp ((t * x : ℝ) * Complex.I) = 1
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp

/-- The unitary `exp(itT)`, from the affiliated observable's bounded functional calculus. -/
def expUnitary (T : AffiliatedObservable A) (t : ℝ) : unitary A := by
  exact ⟨T.boundedFC (expFunction t) (expFunction_measurable t)
      (expFunction_bounded t),
    T.boundedFC_mem_unitary (expFunction_measurable t) (expFunction_bounded t)
      (expFunction_modulus t)⟩

lemma expUnitary_add (t s : ℝ) :
    T.expUnitary (t + s) = T.expUnitary t * T.expUnitary s := by
  apply Subtype.ext
  change T.boundedFC (expFunction (t + s)) (expFunction_measurable (t + s))
      (expFunction_bounded (t + s)) =
    T.boundedFC (expFunction t) (expFunction_measurable t) (expFunction_bounded t) *
      T.boundedFC (expFunction s) (expFunction_measurable s) (expFunction_bounded s)
  have hmul := T.boundedFC_mul
    (f := expFunction t) (g := expFunction s) (expFunction_measurable t)
    (expFunction_measurable s) (expFunction_bounded t) (expFunction_bounded s)
  rw [← hmul]
  apply T.boundedFC_congr (expFunction_measurable (t + s))
    ((expFunction_measurable t).mul (expFunction_measurable s))
    (expFunction_bounded (t + s)) (by
      rcases expFunction_bounded t with ⟨Ct, hCt⟩
      rcases expFunction_bounded s with ⟨Cs, hCs⟩
      refine ⟨Ct * Cs, fun x => ?_⟩
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul (hCt x) (hCs x) (norm_nonneg _) (by
        exact (norm_nonneg (expFunction t 0)).trans (hCt 0)))
  · intro x
    have harg : (((t + s) * x : ℝ) : ℂ) * Complex.I =
        ((t * x : ℝ) : ℂ) * Complex.I + ((s * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    change Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)
    rw [harg, Complex.exp_add]

lemma expUnitary_zero : T.expUnitary 0 = 1 := by
  apply Subtype.ext
  change T.boundedFC (expFunction 0) (expFunction_measurable 0)
      (expFunction_bounded 0) = (1 : A)
  calc
    T.boundedFC (expFunction 0) (expFunction_measurable 0) (expFunction_bounded 0) =
        T.boundedFC (fun _ : ℝ => (1 : ℂ)) (by fun_prop)
          (show ∃ C : ℝ, ∀ _ : ℝ, ‖(1 : ℂ)‖ ≤ C from ⟨1, by simp⟩) := by
      apply T.boundedFC_congr (expFunction_measurable 0) (by fun_prop)
        (expFunction_bounded 0)
        (show ∃ C : ℝ, ∀ _ : ℝ, ‖(1 : ℂ)‖ ≤ C from ⟨1, by simp⟩)
      intro x
      simp [expFunction]
    _ = 1 := by simpa using (T.boundedFC_const 1)

lemma expUnitary_neg_mul (t : ℝ) :
    T.expUnitary (-t) * T.expUnitary t = 1 := by
  calc
    T.expUnitary (-t) * T.expUnitary t = T.expUnitary (-t + t) :=
      (T.expUnitary_add (-t) t).symm
    _ = T.expUnitary 0 := by rw [neg_add_cancel]
    _ = 1 := T.expUnitary_zero

lemma expUnitary_mul_neg (t : ℝ) :
    T.expUnitary t * T.expUnitary (-t) = 1 := by
  calc
    T.expUnitary t * T.expUnitary (-t) = T.expUnitary (t + -t) :=
      (T.expUnitary_add t (-t)).symm
    _ = T.expUnitary 0 := by rw [add_neg_cancel]
    _ = 1 := T.expUnitary_zero

/-- The resolvent `(T - z)⁻¹ ∈ A`, for `z` off the real line (hence off `T`'s spectrum) — a
corollary of the bounded functional calculus applied to `x ↦ (x - z)⁻¹`, which is bounded exactly
because `z ∉ ℝ`. -/
def resolventFunction (z : ℂ) : ℝ → ℂ :=
  fun x => ((x : ℂ) - z)⁻¹

lemma resolventFunction_measurable (z : ℂ) : Measurable (resolventFunction z) := by
  change Measurable (fun x : ℝ => ((x : ℂ) - z)⁻¹)
  fun_prop

lemma resolventFunction_bounded (z : ℂ) (hz : z.im ≠ 0) :
    ∃ C, ∀ x, ‖resolventFunction z x‖ ≤ C := by
  refine ⟨|z.im|⁻¹, ?_⟩
  intro x
  have hne : (x : ℂ) - z ≠ 0 := by
    intro h
    apply hz
    have him := congrArg Complex.im h
    simpa using him
  have hden : |z.im| ≤ ‖(x : ℂ) - z‖ := by
    simpa using Complex.abs_im_le_norm ((x : ℂ) - z)
  rw [resolventFunction, norm_inv]
  exact (inv_le_inv₀ (norm_pos_iff.mpr hne) (abs_pos.mpr hz)).2 hden

/-- The resolvent `(T - z)⁻¹` of `T`, at a non-real `z`. -/
def resolvent (T : AffiliatedObservable A) (z : ℂ) (hz : z.im ≠ 0) : A := by
  exact T.boundedFC (resolventFunction z) (resolventFunction_measurable z)
    (resolventFunction_bounded z hz)

lemma resolvent_identity (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    T.resolvent z hz - T.resolvent w hw =
      (z - w) • (T.resolvent z hz * T.resolvent w hw) := by
  change T.boundedFC (resolventFunction z) (resolventFunction_measurable z)
      (resolventFunction_bounded z hz) -
      T.boundedFC (resolventFunction w) (resolventFunction_measurable w)
        (resolventFunction_bounded w hw) =
    (z - w) • (T.boundedFC (resolventFunction z) (resolventFunction_measurable z)
      (resolventFunction_bounded z hz) *
      T.boundedFC (resolventFunction w) (resolventFunction_measurable w)
        (resolventFunction_bounded w hw))
  have hsub := T.boundedFC_sub (resolventFunction_measurable z)
    (resolventFunction_measurable w) (resolventFunction_bounded z hz)
    (resolventFunction_bounded w hw)
  rcases resolventFunction_bounded z hz with ⟨Cz, hCz⟩
  rcases resolventFunction_bounded w hw with ⟨Cw, hCw⟩
  have hprod : ∃ C, ∀ x, ‖resolventFunction z x * resolventFunction w x‖ ≤ C := by
    refine ⟨Cz * Cw, fun x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hCz x) (hCw x) (norm_nonneg _) (by
      exact (norm_nonneg (resolventFunction z 0)).trans (hCz 0))
  have hmul := T.boundedFC_mul (resolventFunction_measurable z)
    (resolventFunction_measurable w) (⟨Cz, hCz⟩) (⟨Cw, hCw⟩)
  have hscaled : ∃ C, ∀ x,
      ‖(z - w) * (resolventFunction z x * resolventFunction w x)‖ ≤ C := by
    refine ⟨‖z - w‖ * (Cz * Cw), fun x => ?_⟩
    rw [norm_mul, norm_mul]
    exact mul_le_mul (le_rfl) (mul_le_mul (hCz x) (hCw x) (norm_nonneg _) (by
      exact (norm_nonneg (resolventFunction z 0)).trans (hCz 0)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hsmul := T.boundedFC_smul (z - w)
    ((resolventFunction_measurable z).mul (resolventFunction_measurable w)) hprod
  have hdiff' : ∃ C : ℝ, ∀ x,
      ‖(resolventFunction z - resolventFunction w) x‖ ≤ C := by
    refine ⟨Cz + Cw, fun x => ?_⟩
    simpa only [Pi.sub_apply] using
      (show ‖resolventFunction z x - resolventFunction w x‖ ≤ Cz + Cw from
        (norm_sub_le _ _).trans (add_le_add (hCz x) (hCw x)))
  calc
    T.boundedFC (resolventFunction z) (resolventFunction_measurable z)
        (resolventFunction_bounded z hz) -
        T.boundedFC (resolventFunction w) (resolventFunction_measurable w)
          (resolventFunction_bounded w hw) =
        T.boundedFC (resolventFunction z - resolventFunction w)
          ((resolventFunction_measurable z).sub (resolventFunction_measurable w)) hdiff' :=
      hsub.symm
    _ = T.boundedFC
        (fun x => (z - w) * (resolventFunction z x * resolventFunction w x))
        ((measurable_const.mul
          ((resolventFunction_measurable z).mul (resolventFunction_measurable w)))) hscaled := by
      apply T.boundedFC_congr
        ((resolventFunction_measurable z).sub (resolventFunction_measurable w))
        (measurable_const.mul
          ((resolventFunction_measurable z).mul (resolventFunction_measurable w)))
        hdiff' hscaled
      intro x
      have hne_z : (x : ℂ) - z ≠ 0 := by
        intro h
        apply hz
        have him := congrArg Complex.im h
        simpa using him
      have hne_w : (x : ℂ) - w ≠ 0 := by
        intro h
        apply hw
        have him := congrArg Complex.im h
        simpa using him
      dsimp [resolventFunction]
      field_simp
      ring
    _ = (z - w) • T.boundedFC
        (resolventFunction z * resolventFunction w)
        ((resolventFunction_measurable z).mul (resolventFunction_measurable w)) hprod :=
      hsmul
    _ = (z - w) • (T.boundedFC (resolventFunction z) (resolventFunction_measurable z)
        (resolventFunction_bounded z hz) *
        T.boundedFC (resolventFunction w) (resolventFunction_measurable w)
          (resolventFunction_bounded w hw)) := by rw [hmul]

/-- The bounded spectral truncation `T · 1_{[-R,R]}(T)`: an honest element of `A`, recovering
`T` restricted to the bounded part of its spectrum. As promised in the overview, this should be
derived from `boundedFC` applied to `x ↦ x · Set.indicator (Set.Icc (-R) R) 1 x` (bounded by `R`),
not treated as a separate foundational construction. -/
def truncateFunction (R : ℝ) : ℝ → ℂ :=
  fun x => (Set.Icc (-R) R).indicator (fun y : ℝ => (y : ℂ)) x

lemma truncateFunction_measurable (R : ℝ) : Measurable (truncateFunction R) := by
  change Measurable
    (fun x : ℝ => (Set.Icc (-R) R).indicator (fun y : ℝ => (y : ℂ)) x)
  exact Complex.measurable_ofReal.indicator measurableSet_Icc

lemma truncateFunction_bounded (R : ℝ) : ∃ C, ∀ x, ‖truncateFunction R x‖ ≤ C := by
  refine ⟨max R 0, ?_⟩
  intro x
  by_cases hx : x ∈ Set.Icc (-R) R
  · rw [truncateFunction, Set.indicator_of_mem hx]
    calc
      ‖(x : ℂ)‖ = ‖x‖ := Complex.norm_real x
      _ = |x| := Real.norm_eq_abs x
      _ ≤ R := abs_le.2 hx
      _ ≤ max R 0 := le_max_left _ _
  · simp [truncateFunction, hx]

/-- `T`, truncated to a bounded functional-calculus element on `[-R, R]`. -/
def truncate (T : AffiliatedObservable A) (R : ℝ) : A := by
  exact T.boundedFC (truncateFunction R) (truncateFunction_measurable R)
    (truncateFunction_bounded R)

lemma truncate_isSelfAdjoint (T : AffiliatedObservable A) (R : ℝ) :
    IsSelfAdjoint (T.truncate R) := by
  rw [isSelfAdjoint_iff]
  have hfun : (fun x : ℝ => star (truncateFunction R x)) = truncateFunction R := by
    funext x
    by_cases hx : x ∈ Set.Icc (-R) R
    · simp [truncateFunction, Set.indicator_of_mem hx, Complex.star_def]
    · simp [truncateFunction, hx]
  have hstar := T.boundedFC_star (truncateFunction_measurable R)
    (truncateFunction_bounded R)
  have hfc : T.boundedFC (fun x : ℝ => star (truncateFunction R x))
      (continuous_star.measurable.comp (truncateFunction_measurable R))
      (by simpa only [norm_star] using truncateFunction_bounded R) =
      T.boundedFC (truncateFunction R) (truncateFunction_measurable R)
        (truncateFunction_bounded R) := by
    apply T.boundedFC_congr
      (continuous_star.measurable.comp (truncateFunction_measurable R))
      (truncateFunction_measurable R)
      (show ∃ C, ∀ x : ℝ, ‖star (truncateFunction R x)‖ ≤ C by
        simpa only [norm_star] using truncateFunction_bounded R)
      (truncateFunction_bounded R)
    exact fun x => congrFun hfun x
  exact hstar.symm.trans hfc

/- The abstract `realTruncate`/`truncate` constructions already expose the bounded spectral
support and self-adjointness facts available from the PVM alone.  The corresponding strong
operator convergence and maximal-domain statement is represented at the concrete boundary by
`AffiliationBridge.representation_truncate_apply_tendsto` in `Representation.lean`.  A direct
representation-free equality of unbounded operators would require a faithful normal realization
and its WOT-to-norm bridge, so it is intentionally not asserted in this spectral-data layer. -/

end AffiliatedObservable

end OperatorAlgebra
