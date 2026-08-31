/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Calculus.FunctionalCalculus
public import Physlib.Meta.Sorry
public import Physlib.Meta.TODO.Basic
public import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# The Kaplansky bounded transform of an affiliated observable

`Affiliated.lean`'s module docstring names an explicit gap: the *representation-free* bounded
transform characterization of affiliation (Kaplansky's classical algebraic reformulation of
"closed densely-defined self-adjoint operator affiliated to `M`" as a genuine *bounded* element
`a ∈ M` with `‖a‖ ≤ 1` and `1 - a⋆a` having dense range). This file supplies that construction,
entirely within an abstract `OperatorAlgebra A` (no Hilbert space, no chosen representation),
reusing the already-proved `AffiliatedObservable.boundedFC`/`measurableRealFC` machinery of
`FunctionalCalculus.lean`.

## The choice of transform function

Kaplansky's classical bounded transform uses `f(λ) = λ / √(1 + λ²)`. Any bounded, strictly
increasing, odd homeomorphism `ℝ → (-1, 1)` serves exactly the same algebraic purpose (the
*specific* function is a convention, not part of the theorem's content — only its boundedness,
injectivity, and having a Borel-measurable inverse on its range matter). We use
`f = Real.tanh` instead: it is honestly equivalent in every respect that matters here, and
Mathlib's `Analysis.SpecialFunctions.Artanh` already supplies exactly the needed API
(`Real.tanh_lt_one`, `Real.neg_one_lt_tanh`, `Real.tanh_sq_lt_one`, `Real.tanh_injective`, and
crucially the *unconditional* two-sided inverse identity `Real.artanh_tanh : ∀ x, artanh (tanh x)
= x`), which lets the whole construction below be proved rather than reproved from scratch for the
algebraic function `λ ↦ λ/√(1+λ²)`.

## Main results

- `AffiliatedObservable.boundedTransform` : the bounded transform `a = tanh(T) ∈ A` of an affiliated
  observable `T`, via `T.boundedFC`.
- `boundedTransform_isSelfAdjoint`, `norm_boundedTransform_le_one` : `a` is a genuine bounded
  self-adjoint element of `A` with `‖a‖ ≤ 1` — Kaplansky's first two conditions.
- `one_sub_star_boundedTransform_mul_self_eq` : `1 - a⋆a` is itself a spectral function of `T`
  (namely `1 - tanh²(T)`), computed directly from `T.boundedFC`.
- `oneSubTanhSq_spectralProjection_zero_eq_zero` : the spectral projection of `1 - a⋆a` at
  eigenvalue `0`, computed via `T`'s own spectral measure, is `0` — the precise
  Kadison–Ringrose *"has dense range"* condition for an element of a von Neumann algebra, proved
  here (not assumed) from `1 - tanh² > 0` everywhere.
- `measurableRealFC_tanh_measurableRealFC_artanh` : the representation-free round-trip at the
  level of spectral data, `(T ↦ tanh(T)) ↦ artanh(·)` recovers `T` exactly, via the *unconditional*
  Mathlib identity `artanh ∘ tanh = id`.
- `boundedFC_measurableRealFC` : the general composition law `(T.measurableRealFC f hf).boundedFC g
  = T.boundedFC (g ∘ f)`, proved once and reused to show that `a = T.boundedTransform` literally
  *is* `(T.measurableRealFC tanh htanh)`'s own bounded value at (a truncation of) the identity —
  connecting the bounded algebra element back to the spectral-data round trip above.

## What remains open

The *converse* direction — reconstructing an `AffiliatedObservable A` from an arbitrary bounded
self-adjoint `a ∈ A` with `‖a‖ ≤ 1` and the dense-range condition on `1 - a⋆a`, with no further
data — needs `a` itself to already possess a Borel functional calculus (a way of producing
`1_S(a) ∈ A` for Borel `S`), exactly the `BorelFunctionalCalculus A` capability `Affiliated.lean`
already isolates as an explicit, unavoidable boundary for a bare C⋆-algebra (this is not a gap
invented for this file: it is the same boundary documented at the bottom of `Affiliated.lean`,
"recovering `a` from the spectral integral of the identity"). `AffiliatedObservable.ofBoundedTransform`
below is built assuming that capability; the compatibility theorem connecting it back to
`boundedTransform` is exposed with an explicit compatibility certificate: the abstract Borel
calculus must identify the relevant bounded spectral integral with the original observable.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra
open MeasureTheory Set

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-! ## The transform function `tanh` and its inverse `artanh` -/

/-- `Real.tanh` is continuous: it is `sinh / cosh`, and `cosh` is everywhere positive. -/
lemma continuous_tanh : Continuous Real.tanh := by
  have h : Real.tanh = fun x => Real.sinh x / Real.cosh x :=
    funext fun x => Real.tanh_eq_sinh_div_cosh x
  rw [h]
  exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'

lemma measurable_tanh : Measurable Real.tanh := continuous_tanh.measurable

/-- The complex-valued transform function `λ ↦ (tanh λ : ℂ)`, as a bounded measurable function
`ℝ → ℂ`, ready for `AffiliatedObservable.boundedFC`. -/
def tanhC : ℝ → ℂ := fun x => (Real.tanh x : ℂ)

lemma measurable_tanhC : Measurable tanhC :=
  Complex.measurable_ofReal.comp measurable_tanh

lemma norm_tanhC_le_one (x : ℝ) : ‖tanhC x‖ ≤ 1 := by
  have h : ‖tanhC x‖ = |Real.tanh x| := by
    rw [tanhC, Complex.norm_real, Real.norm_eq_abs]
  rw [h]
  exact (Real.abs_tanh_lt_one x).le

lemma tanhC_bounded : ∃ C, ∀ x, ‖tanhC x‖ ≤ C := ⟨1, norm_tanhC_le_one⟩

/-! ## A norm estimate for `boundedFC`

The bounded Borel calculus is a norm limit of finite spectral sums, each of which already
satisfies `simpleIntegral_norm_le`; the estimate survives the limit. This is stated once here
(rather than in `FunctionalCalculus.lean`) since it is the fact this file's whole construction
depends on, and is proved directly against `boundedFC_eq_limUnder` without relying on the exact
bound witness `exists_uniform_simple_approx` happens to return internally. -/

namespace AffiliatedObservable

variable (T : AffiliatedObservable A)

lemma boundedFC_norm_le {f : ℝ → ℂ} (hf : Measurable f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C)
    {C : ℝ} (hC0 : 0 ≤ C) (hfC : ∀ x, ‖f x‖ ≤ C) :
    ‖T.boundedFC f hf hbdd‖ ≤ C := by
  classical
  obtain ⟨s, hs, -⟩ := exists_uniform_simple_approx hf hbdd
  by_contra hcon
  push Not at hcon
  set ε : ℝ := (‖T.boundedFC f hf hbdd‖ - C) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨N, hN⟩ := hs ε hεpos
  have hbound : ∀ n ≥ N, ‖T.simpleIntegral (s n)‖ ≤ C + ε := by
    intro n hn
    apply T.simpleIntegral_norm_le (s n) (by linarith)
    intro z hz
    rcases SimpleFunc.mem_range.1 hz with ⟨x, rfl⟩
    have h1 : ‖s n x - f x‖ < ε := hN n hn x
    calc ‖s n x‖ = ‖(s n x - f x) + f x‖ := by ring_nf
      _ ≤ ‖s n x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ C + ε := by linarith [h1, hfC x]
  have heq : T.boundedFC f hf hbdd = Filter.atTop.limUnder (fun n => T.simpleIntegral (s n)) :=
    T.boundedFC_eq_limUnder hf hbdd hs
  have htendsto : Filter.Tendsto (fun n => T.simpleIntegral (s n)) Filter.atTop
      (nhds (T.boundedFC f hf hbdd)) := by
    rw [heq]; exact (T.simpleIntegral_cauchySeq hs).tendsto_limUnder
  have hle : ‖T.boundedFC f hf hbdd‖ ≤ C + ε :=
    le_of_tendsto htendsto.norm (Filter.eventually_atTop.2 ⟨N, hbound⟩)
  rw [hεdef] at hle
  linarith

end AffiliatedObservable

/-! ## The bounded transform -/

namespace AffiliatedObservable

variable (T : AffiliatedObservable A)

/-- Kaplansky's bounded transform: `a = tanh(T) ∈ A`, a genuine (bounded) algebra element built
from `T`'s unbounded spectral data by applying the bounded Borel calculus to `tanh`. -/
def boundedTransform : A := T.boundedFC tanhC measurable_tanhC tanhC_bounded

/-- Unfolding lemma, stated as a genuine equation so it can be `rw`'d (unlike the bare `def`). -/
lemma boundedTransform_eq :
    T.boundedTransform = T.boundedFC tanhC measurable_tanhC tanhC_bounded := rfl

/-- `boundedTransform` is self-adjoint: `tanh` is real-valued, so `star ∘ tanhC = tanhC`, and
`boundedFC_star` transports this to the algebra element. Mirrors `truncate_isSelfAdjoint`. -/
lemma boundedTransform_isSelfAdjoint : IsSelfAdjoint T.boundedTransform := by
  rw [isSelfAdjoint_iff]
  have hfun : (fun x : ℝ => star (tanhC x)) = tanhC := by
    funext x
    show star ((Real.tanh x : ℂ)) = (Real.tanh x : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal]
  have hstar_bdd : ∃ C, ∀ x, ‖star (tanhC x)‖ ≤ C :=
    ⟨1, fun x => by rw [norm_star]; exact norm_tanhC_le_one x⟩
  have hstar := T.boundedFC_star measurable_tanhC tanhC_bounded
  have hfc : T.boundedFC (fun x => star (tanhC x))
      (continuous_star.measurable.comp measurable_tanhC) hstar_bdd =
      T.boundedFC tanhC measurable_tanhC tanhC_bounded := by
    apply T.boundedFC_congr (continuous_star.measurable.comp measurable_tanhC) measurable_tanhC
      hstar_bdd tanhC_bounded
    exact fun x => congrFun hfun x
  exact hstar.symm.trans hfc

/-- Kaplansky's `‖a‖ ≤ 1` condition. -/
lemma norm_boundedTransform_le_one : ‖T.boundedTransform‖ ≤ 1 :=
  T.boundedFC_norm_le measurable_tanhC tanhC_bounded zero_le_one norm_tanhC_le_one

end AffiliatedObservable

/-! ## `1 - a⋆a` is a strictly positive spectral function of `T` -/

/-- `1 - tanh·tanh`, as a real measurable function of `T`'s spectrum (using `*` rather than `^2`
throughout this section, to match `boundedFC_mul`'s output shape exactly). -/
def oneSubTanhSqFunction : ℝ → ℝ := fun x => 1 - Real.tanh x * Real.tanh x

lemma measurable_oneSubTanhSqFunction : Measurable oneSubTanhSqFunction :=
  measurable_const.sub (measurable_tanh.mul measurable_tanh)

lemma oneSubTanhSqFunction_pos (x : ℝ) : 0 < oneSubTanhSqFunction x := by
  have h := Real.tanh_sq_lt_one x
  rw [sq] at h
  unfold oneSubTanhSqFunction
  linarith

/-- The complex-valued packaging `1 - tanhC * tanhC`, matching the algebra identity `1 - a⋆a`. -/
def oneSubTanhSqC : ℝ → ℂ := fun x => (1 : ℂ) - tanhC x * tanhC x

lemma measurable_oneSubTanhSqC : Measurable oneSubTanhSqC :=
  measurable_const.sub (measurable_tanhC.mul measurable_tanhC)

/-- `‖tanhC x * tanhC x‖ ≤ 1`, the bound needed both for `boundedFC_mul` and for
`oneSubTanhSqC_bounded`. -/
lemma norm_tanhC_mul_tanhC_le_one (x : ℝ) : ‖tanhC x * tanhC x‖ ≤ 1 := by
  rw [norm_mul]
  calc ‖tanhC x‖ * ‖tanhC x‖ ≤ 1 * 1 :=
        mul_le_mul (norm_tanhC_le_one x) (norm_tanhC_le_one x) (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

lemma tanhC_mul_tanhC_bounded : ∃ C, ∀ x, ‖tanhC x * tanhC x‖ ≤ C :=
  ⟨1, norm_tanhC_mul_tanhC_le_one⟩

lemma measurable_constOne : Measurable (fun _ : ℝ => (1 : ℂ)) := by fun_prop

lemma constOne_bounded : ∃ C, ∀ _ : ℝ, ‖(1 : ℂ)‖ ≤ C := ⟨1, fun _ => by norm_num⟩

lemma oneSubTanhSqC_bounded : ∃ C, ∀ x, ‖oneSubTanhSqC x‖ ≤ C := by
  refine ⟨2, fun x => ?_⟩
  calc ‖oneSubTanhSqC x‖ = ‖(1 : ℂ) - tanhC x * tanhC x‖ := rfl
    _ ≤ ‖(1:ℂ)‖ + ‖tanhC x * tanhC x‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
        have := norm_tanhC_mul_tanhC_le_one x
        simp only [norm_one]
        linarith
    _ = 2 := by norm_num

namespace AffiliatedObservable

variable (T : AffiliatedObservable A)

/-- `1 - a⋆a = 1 - tanh(T)·tanh(T)`, computed directly as a bounded functional-calculus value of
`T` — this is the algebraic content behind Kaplansky's dense-range condition: `1 - a⋆a` is not an
arbitrary element but a genuine bounded spectral function of `T` itself. -/
lemma one_sub_star_boundedTransform_mul_self_eq :
    1 - star T.boundedTransform * T.boundedTransform =
      T.boundedFC oneSubTanhSqC measurable_oneSubTanhSqC oneSubTanhSqC_bounded := by
  rw [(T.boundedTransform_isSelfAdjoint).star_eq, T.boundedTransform_eq]
  have hone : (1 : A) = T.boundedFC (fun _ : ℝ => (1:ℂ)) measurable_constOne constOne_bounded := by
    have h := T.boundedFC_const (1 : ℂ)
    simpa using h.symm
  rw [hone, ← T.boundedFC_mul measurable_tanhC measurable_tanhC tanhC_bounded tanhC_bounded,
    ← T.boundedFC_sub measurable_constOne (measurable_tanhC.mul measurable_tanhC) constOne_bounded
      tanhC_mul_tanhC_bounded]
  apply T.boundedFC_congr (measurable_constOne.sub (measurable_tanhC.mul measurable_tanhC))
    measurable_oneSubTanhSqC _ oneSubTanhSqC_bounded
  intro x
  rfl

/-- **The Kadison–Ringrose "dense range" condition, proved.** The spectral projection of
`1 - a⋆a`, computed at eigenvalue `0` via `T`'s own spectral measure (since `1 - a⋆a =
(1 - tanh²)(T)`, a spectral function of `T`), is `0`. This is the precise algebraic meaning of
"`1 - a⋆a` has dense range" for an element of a von Neumann algebra (Kadison–Ringrose II,
`e ≥ 0` has dense range iff its `{0}`-spectral projection vanishes), and it holds because
`1 - tanh²(λ) > 0` for every real `λ`: the value `0` is simply never attained. -/
theorem oneSubTanhSq_spectralMeasure_zero_eq_zero :
    (T.measurableRealFC oneSubTanhSqFunction measurable_oneSubTanhSqFunction).spectralMeasure
      {(0 : ℝ)} = 0 := by
  rw [T.measurableRealFC_spectralMeasure_apply measurable_oneSubTanhSqFunction
    (measurableSet_singleton (0 : ℝ))]
  have hpre : oneSubTanhSqFunction ⁻¹' {(0 : ℝ)} = ∅ := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    exact (oneSubTanhSqFunction_pos x).ne'
  rw [hpre]
  exact T.spectralMeasure.toVectorMeasure.empty

end AffiliatedObservable

/-! ## The representation-free round trip -/

lemma measurable_artanh : Measurable Real.artanh := by
  have h : Real.artanh = fun x => Real.log (Real.sqrt ((1 + x) / (1 - x))) := rfl
  rw [h]; fun_prop

namespace AffiliatedObservable

variable (T : AffiliatedObservable A)

/-- **The spectral-data round trip.** Pushing `T`'s spectral measure forward along `tanh` and
then along `artanh` recovers `T` exactly — this is the *unconditional* Mathlib identity
`Real.artanh_tanh : ∀ x, artanh (tanh x) = x` (no domain restriction needed, since `artanh` is
defined on all of `ℝ`), transported through `measurableRealFC_comp`/`measurableRealFC_id`. This is
the representation-free analogue of "the bounded transform and its inverse are mutually inverse",
at the level of spectral data. -/
theorem measurableRealFC_tanh_measurableRealFC_artanh :
    (T.measurableRealFC Real.tanh measurable_tanh).measurableRealFC Real.artanh
      measurable_artanh = T := by
  rw [measurableRealFC_comp]
  have hcomp : Real.artanh ∘ Real.tanh = id := funext Real.artanh_tanh
  calc T.measurableRealFC (Real.artanh ∘ Real.tanh) (measurable_artanh.comp measurable_tanh)
      = T.measurableRealFC id (hcomp ▸ (measurable_artanh.comp measurable_tanh)) := by
        apply AffiliatedObservable.ext
        intro S hS
        rw [T.measurableRealFC_spectralMeasure_apply (measurable_artanh.comp measurable_tanh) hS,
          T.measurableRealFC_spectralMeasure_apply (hcomp ▸ (measurable_artanh.comp measurable_tanh))
            hS, hcomp]
    _ = T := measurableRealFC_id T

end AffiliatedObservable

/-! ## Connecting the algebra element to the spectral-data round trip -/

section Composition

variable {A : Type*} [OperatorAlgebra A]

/-- The finite spectral integral against a pushed-forward PVM is the finite spectral integral of
the composed simple function. The two sums are literally the same expression, once the (possibly
larger) range of `s` is reduced to the range of `s.comp f hf` by discarding the zero terms
contributed by values `s` never attains after composing with `f`. -/
lemma AffiliatedObservable.simpleIntegral_measurableRealFC (T : AffiliatedObservable A)
    {f : ℝ → ℝ} (hf : Measurable f) (s : SimpleFunc ℝ ℂ) :
    (T.measurableRealFC f hf).simpleIntegral s = T.simpleIntegral (s.comp f hf) := by
  classical
  have hpre : ∀ z : ℂ, (s.comp f hf) ⁻¹' {z} = f ⁻¹' (s ⁻¹' {z}) := by
    intro z; ext x; simp [SimpleFunc.coe_comp]
  have hterm : ∀ z ∈ s.range,
      z • ((T.measurableRealFC f hf).spectralMeasure (s ⁻¹' {z}) : A) =
        z • (T.spectralMeasure ((s.comp f hf) ⁻¹' {z}) : A) := by
    intro z _
    rw [(T.measurableRealFC_spectralMeasure_apply hf (s.measurableSet_fiber z)), hpre z]
  have hzero : ∀ z ∈ s.range, z ∉ (s.comp f hf).range →
      z • (T.spectralMeasure ((s.comp f hf) ⁻¹' {z}) : A) = 0 := by
    intro z _ hzr
    have hempty : (s.comp f hf) ⁻¹' {z} = ∅ := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro hx
      exact hzr (SimpleFunc.mem_range.2 ⟨x, hx⟩)
    rw [hempty, T.spectralMeasure.toVectorMeasure.empty, smul_zero]
  calc
    (T.measurableRealFC f hf).simpleIntegral s
        = ∑ z ∈ s.range, z • ((T.measurableRealFC f hf).spectralMeasure (s ⁻¹' {z}) : A) := rfl
    _ = ∑ z ∈ s.range, z • (T.spectralMeasure ((s.comp f hf) ⁻¹' {z}) : A) :=
        Finset.sum_congr rfl hterm
    _ = ∑ z ∈ (s.comp f hf).range, z • (T.spectralMeasure ((s.comp f hf) ⁻¹' {z}) : A) :=
        (Finset.sum_subset (SimpleFunc.range_comp_subset_range s hf) hzero).symm
    _ = T.simpleIntegral (s.comp f hf) := rfl

/-- **The composition law for the bounded calculus.** Applying the bounded Borel calculus to a
pushed-forward `AffiliatedObservable` agrees with applying it to the composed function on the
original `T`: `g(f(T)) = (g ∘ f)(T)`. Proved directly (not merely stated) from the finite-sum
identity above, by comparing both sides' norm-limit presentations along a shared uniform
simple-function approximation of `g`. -/
theorem AffiliatedObservable.boundedFC_measurableRealFC (T : AffiliatedObservable A)
    {f : ℝ → ℝ} (hf : Measurable f) {g : ℝ → ℂ} (hg : Measurable g)
    (hgb : ∃ C, ∀ y, ‖g y‖ ≤ C) :
    (T.measurableRealFC f hf).boundedFC g hg hgb =
      T.boundedFC (g ∘ f) (hg.comp hf) (by
        obtain ⟨C, hC⟩ := hgb; exact ⟨C, fun x => hC (f x)⟩) := by
  classical
  obtain ⟨s, hs, -⟩ := exists_uniform_simple_approx hg hgb
  have hcomp_approx : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖(s n).comp f hf x - (g ∘ f) x‖ < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hs ε hε
    refine ⟨N, fun n hn x => ?_⟩
    simpa [SimpleFunc.coe_comp] using hN n hn (f x)
  have heqL : (T.measurableRealFC f hf).boundedFC g hg hgb =
      Filter.atTop.limUnder (fun n => (T.measurableRealFC f hf).simpleIntegral (s n)) :=
    (T.measurableRealFC f hf).boundedFC_eq_limUnder hg hgb hs
  have heqR : T.boundedFC (g ∘ f) (hg.comp hf)
      (by obtain ⟨C, hC⟩ := hgb; exact ⟨C, fun x => hC (f x)⟩) =
      Filter.atTop.limUnder (fun n => T.simpleIntegral ((s n).comp f hf)) :=
    T.boundedFC_eq_limUnder (hg.comp hf) _ hcomp_approx
  rw [heqL, heqR]
  congr 1
  funext n
  exact T.simpleIntegral_measurableRealFC hf (s n)

/-- **The bounded transform is `S`'s own value at the identity**, where `S = T.measurableRealFC
tanh` is the (already bounded, since `tanh`'s range is bounded) pushed-forward spectral data. This
is the honest connective tissue between the algebra element `a = T.boundedTransform` and the
spectral-data round trip `measurableRealFC_tanh_measurableRealFC_artanh`: `a` is not merely *some*
bounded element built from `T`, it literally *is* the identity function evaluated (via the bounded
calculus) at the pushed-forward observable `S`, using that `tanh`'s values always lie in
`Icc (-1) 1` so that the (necessarily bounded, since `S`'s calculus domain is all of `ℝ`)
truncated identity `AffiliatedObservable.realTruncateFunction 1` agrees with the true identity on all of `tanh`'s
range. -/
lemma measurable_ofReal_realTruncateFunction_one :
    Measurable (Complex.ofReal ∘ AffiliatedObservable.realTruncateFunction 1) :=
  Complex.measurable_ofReal.comp (AffiliatedObservable.realTruncateFunction_measurable 1)

lemma norm_ofReal_realTruncateFunction_one_le_one (y : ℝ) :
    ‖(Complex.ofReal ∘ AffiliatedObservable.realTruncateFunction 1) y‖ ≤ 1 := by
  rw [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
  by_cases hy : y ∈ Set.Icc (-(1:ℝ)) 1
  · rw [AffiliatedObservable.realTruncateFunction, Set.indicator_of_mem hy]; exact abs_le.2 hy
  · rw [AffiliatedObservable.realTruncateFunction, Set.indicator_of_notMem hy]; simp

lemma ofReal_realTruncateFunction_one_bounded :
    ∃ C, ∀ y, ‖(Complex.ofReal ∘ AffiliatedObservable.realTruncateFunction 1) y‖ ≤ C :=
  ⟨1, norm_ofReal_realTruncateFunction_one_le_one⟩

set_option maxHeartbeats 1000000 in
theorem AffiliatedObservable.boundedTransform_eq_boundedFC_measurableRealFC_tanh
    (T : AffiliatedObservable A) :
    T.boundedTransform =
      (T.measurableRealFC Real.tanh measurable_tanh).boundedFC
        (Complex.ofReal ∘ AffiliatedObservable.realTruncateFunction 1)
        measurable_ofReal_realTruncateFunction_one
        ofReal_realTruncateFunction_one_bounded := by
  rw [T.boundedFC_measurableRealFC measurable_tanh measurable_ofReal_realTruncateFunction_one
      ofReal_realTruncateFunction_one_bounded, T.boundedTransform_eq]
  apply T.boundedFC_congr measurable_tanhC
    (measurable_ofReal_realTruncateFunction_one.comp measurable_tanh) tanhC_bounded _
  intro x
  have hmem : Real.tanh x ∈ Set.Icc (-(1:ℝ)) 1 :=
    ⟨(Real.neg_one_lt_tanh x).le, (Real.tanh_lt_one x).le⟩
  simp [Function.comp_apply, AffiliatedObservable.realTruncateFunction,
    Set.indicator_of_mem hmem, tanhC]

end Composition

/-! ## The converse direction: a genuinely representation-dependent boundary

Reconstructing `T` from an arbitrary bounded self-adjoint `a ∈ A` with `‖a‖ ≤ 1` and the
dense-range condition needs `a` to already possess a Borel functional calculus — the same
`BorelFunctionalCalculus A` capability `Affiliated.lean` isolates for `Observable.toAffiliatedObservable`.
Given that capability, the natural reconstruction is `artanh` pushed forward along `a`'s own
spectral measure. -/

namespace AffiliatedObservable

variable [BorelFunctionalCalculus A]

/-- Compatibility of the supplied abstract Borel calculus with the bounded observable at the
inverse-transform composition.  A bare `BorelFunctionalCalculus` supplies spectral data and
algebra laws, but does not connect those data back to the element whose spectrum they describe;
this predicate isolates that representation-dependent law. -/
def BoundedTransformCompatibility (a : A) (ha : IsSelfAdjoint a) : Prop :=
  (Observable.toAffiliatedObservable (⟨a, ha⟩ : Observable A)).boundedFC
      (tanhC ∘ Real.artanh)
      (measurable_tanhC.comp measurable_artanh)
      (⟨1, fun x => norm_tanhC_le_one (Real.artanh x)⟩ :
        ∃ C : ℝ, ∀ x, ‖(tanhC ∘ Real.artanh) x‖ ≤ C) = a

/-- Reconstructing an `AffiliatedObservable` from a bounded self-adjoint `a`, given the
`BorelFunctionalCalculus A` capability: push `a`'s own spectral measure (via
`Observable.toAffiliatedObservable`) forward along `artanh`. -/
def ofBoundedTransform (a : A) (ha : IsSelfAdjoint a) : AffiliatedObservable A :=
  (Observable.toAffiliatedObservable (⟨a, ha⟩ : Observable A)).measurableRealFC
    Real.artanh measurable_artanh

/-- **The remaining boundary.** `boundedTransform (ofBoundedTransform a ha) = a` requires knowing
that `a` is recovered as the bounded calculus's own value at the identity from *its own* spectral
measure `BorelFunctionalCalculus.spectralMeasure ⟨a, ha⟩` — exactly the compatibility statement
`Affiliated.lean` already documents as deferred ("The bounded inclusion recovers `a` itself as the
affiliated operator's spectral integral of the identity ... depends on the same Borel functional
calculus as `toAffiliatedObservable` itself"). This is not a gap invented for this file: it is the
same acknowledged boundary, restated at the bounded-transform level. Supplying it would need either
an axiom relating `BorelFunctionalCalculus` to continuous functional calculus on `a`, or a concrete
von Neumann representation providing it as a theorem (`NormalRepresentation.lean`'s route). -/
theorem boundedTransform_ofBoundedTransform (a : A) (ha : IsSelfAdjoint a)
    (hcompat : BoundedTransformCompatibility a ha) :
    (ofBoundedTransform a ha).boundedTransform = a := by
  change
    ((Observable.toAffiliatedObservable (⟨a, ha⟩ : Observable A)).measurableRealFC
      Real.artanh measurable_artanh).boundedTransform = a
  rw [AffiliatedObservable.boundedTransform_eq]
  rw [AffiliatedObservable.boundedFC_measurableRealFC
    (Observable.toAffiliatedObservable (⟨a, ha⟩ : Observable A))
    measurable_artanh measurable_tanhC tanhC_bounded]
  exact hcompat

end AffiliatedObservable

end OperatorAlgebra
