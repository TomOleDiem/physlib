/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.NormalPVM
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Calculus.FunctionalCalculus

/-!
# Affiliated spectral data with normal-functional additivity

`AffiliatedObservable` is the norm-valued spectral-data façade. This file provides its
infinite-dimensional von Neumann counterpart: a `NormalAffiliatedObservable` stores a real
`NormalPVM`, whose countable additivity is tested against normal states. The measurable calculus
is again just pushforward of spectral data, so it has no domain hidden in the representation-free
object. Domains enter only when a concrete Hilbert-space realization is supplied.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra Function
open MeasureTheory Set

namespace OperatorAlgebra

variable {A : Type*} [WStarAlgebra A]

/-- A real affiliated observable represented by a normal-functional PVM. -/
structure NormalAffiliatedObservable (A : Type*) [WStarAlgebra A] where
  /-- The (real) normal-functional spectral measure `E_T : \Borel(ℝ) → Projection A`. -/
  spectralMeasure : NormalPVM ℝ A

/-- A complex affiliated operator represented by a normal-functional PVM. -/
structure NormalAffiliatedOperator (A : Type*) [WStarAlgebra A] where
  /-- The (complex) normal-functional spectral measure `E_T : \Borel(ℂ) → Projection A`. -/
  spectralMeasure : NormalPVM ℂ A

/-! A measurable indicator has the same bounded complex-valued representative on every spectral
space. Keeping this primitive independent of `AffiliatedObservable` is what lets the normal
Borel calculus work for complex normal operators as well as real self-adjoint ones. -/

/-- The bounded complex-valued indicator function of a set `S`, used as the common input to the
normal Borel calculus for both real and complex spectral spaces. -/
def normalIndicatorFunction {X : Type*} (S : Set X) : X → ℂ :=
  S.indicator (fun _ => (1 : ℂ))

lemma normalIndicatorFunction_measurable {X : Type*} [MeasurableSpace X]
    {S : Set X} (hS : MeasurableSet S) :
    Measurable (normalIndicatorFunction S) := by
  exact measurable_const.indicator hS

lemma normalIndicatorFunction_bounded {X : Type*} (S : Set X) :
    ∃ C : ℝ, ∀ x, ‖normalIndicatorFunction S x‖ ≤ C := by
  refine ⟨1, ?_⟩
  intro x
  by_cases hx : x ∈ S <;> simp [normalIndicatorFunction, hx]

/-! ## The bounded normal Borel calculus -/

/-- A bounded Borel functional calculus for a normal PVM.

The existence of this structure is the abstract von Neumann-algebra step: its values are elements
of `A`, while countable additivity of the underlying PVM is only normal-state additive. The laws
are included in the certificate so downstream affiliated constructions never need to reopen the
completion/ultraweak-continuity argument. -/
structure NormalBorelFunctionalCalculus
    {X : Type*} [MeasurableSpace X] {A : Type*} [WStarAlgebra A]
    (E : NormalPVM X A) where
  /-- The bounded measurable functional calculus itself: sends a bounded measurable
  `f : X → ℂ` (with its boundedness witness) to the corresponding element of `A`. -/
  boundedFC : ∀ (f : X → ℂ), Measurable f →
    (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) → A
  boundedFC_congr : ∀ {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C),
    (∀ x, f x = g x) →
      boundedFC f hf hfb = boundedFC g hg hgb
  boundedFC_const : ∀ (c : ℂ),
    boundedFC (fun _ : X => c) measurable_const (⟨‖c‖, fun _ => le_rfl⟩) = c • (1 : A)
  boundedFC_add : ∀ {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∃ C : ℝ, ∀ x, ‖f x + g x‖ ≤ C),
    boundedFC (f + g) (hf.add hg) hfg = boundedFC f hf hfb + boundedFC g hg hgb
  boundedFC_mul : ∀ {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∃ C : ℝ, ∀ x, ‖f x * g x‖ ≤ C),
    boundedFC (f * g) (hf.mul hg) hfg = boundedFC f hf hfb * boundedFC g hg hgb
  boundedFC_smul : ∀ (c : ℂ) {f : X → ℂ} (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hcf : ∃ C : ℝ, ∀ x, ‖c * f x‖ ≤ C),
    boundedFC (fun x => c * f x) (measurable_const.mul hf) hcf =
      c • boundedFC f hf hfb
  boundedFC_star : ∀ {f : X → ℂ} (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hstar : ∃ C : ℝ, ∀ x, ‖star (f x)‖ ≤ C),
    boundedFC (fun x => star (f x)) (continuous_star.measurable.comp hf) hstar =
      star (boundedFC f hf hfb)
  boundedFC_mem_unitary : ∀ {f : X → ℂ} (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hmod : ∀ x, star (f x) * f x = 1),
    boundedFC f hf hfb ∈ unitary A
  boundedFC_indicator : ∀ (S : Set X) (hS : MeasurableSet S),
    boundedFC (normalIndicatorFunction S)
      (normalIndicatorFunction_measurable hS)
      (normalIndicatorFunction_bounded S) = E S

namespace NormalBorelFunctionalCalculus

variable {X : Type*} [MeasurableSpace X]
variable {A : Type*} [WStarAlgebra A] {E : NormalPVM X A}

lemma boundedFC_const' (C : NormalBorelFunctionalCalculus E) (c : ℂ) :
    C.boundedFC (fun _ : X => c) measurable_const (⟨‖c‖, fun _ => le_rfl⟩) = c • (1 : A) :=
  C.boundedFC_const c

lemma boundedFC_neg (C : NormalBorelFunctionalCalculus E) {f : X → ℂ}
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hneg : ∃ C : ℝ, ∀ x, ‖-f x‖ ≤ C) :
    C.boundedFC (fun x => -f x) (continuous_neg.measurable.comp hf) hneg =
      -C.boundedFC f hf hfb := by
  rcases hneg with ⟨Cneg, hCneg⟩
  have hneg' : ∃ C : ℝ, ∀ x, ‖(-1 : ℂ) * f x‖ ≤ C := by
    refine ⟨Cneg, fun x => ?_⟩
    simpa only [neg_one_mul] using hCneg x
  calc
    C.boundedFC (fun x => -f x) (continuous_neg.measurable.comp hf) (⟨Cneg, hCneg⟩) =
        C.boundedFC (fun x => (-1 : ℂ) * f x) (measurable_const.mul hf) hneg' := by
      apply C.boundedFC_congr (continuous_neg.measurable.comp hf)
        (measurable_const.mul hf) (⟨Cneg, hCneg⟩) hneg'
      intro x
      exact (neg_one_mul (f x)).symm
    _ = (-1 : ℂ) • C.boundedFC f hf hfb := C.boundedFC_smul (-1 : ℂ) hf hfb hneg'
    _ = -C.boundedFC f hf hfb := by simp

lemma boundedFC_sub (C : NormalBorelFunctionalCalculus E) {f g : X → ℂ}
    (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∃ C : ℝ, ∀ x, ‖f x - g x‖ ≤ C) :
    C.boundedFC (f - g) (hf.sub hg) hfg =
      C.boundedFC f hf hfb - C.boundedFC g hg hgb := by
  rcases hgb with ⟨Cg, hCg⟩
  have hneg : ∃ C : ℝ, ∀ x, ‖-g x‖ ≤ C := by
    refine ⟨Cg, fun x => ?_⟩
    simpa using hCg x
  have haddBound : ∃ C : ℝ, ∀ x, ‖f x + -g x‖ ≤ C := by
    simpa only [sub_eq_add_neg] using hfg
  have hgm : Measurable (fun x => -g x) := continuous_neg.measurable.comp hg
  have hadd := C.boundedFC_add hf hgm hfb hneg haddBound
  have hnegFC := C.boundedFC_neg hg (⟨Cg, hCg⟩) hneg
  calc
    C.boundedFC (f - g) (hf.sub hg) hfg =
        C.boundedFC (f + (fun x => -g x)) (hf.add hgm) haddBound := by
      apply C.boundedFC_congr (hf.sub hg) (hf.add hgm) hfg haddBound
      intro x
      rfl
    _ = C.boundedFC f hf hfb + C.boundedFC (fun x => -g x)
        hgm hneg := hadd
    _ = C.boundedFC f hf hfb - C.boundedFC g hg (⟨Cg, hCg⟩) := by
      rw [hnegFC, sub_eq_add_neg]

end NormalBorelFunctionalCalculus

namespace NormalBorelFunctionalCalculus

variable {A : Type*} [WStarAlgebra A]

/-! ### The norm-additive special case

When a norm-valued `PVM` is available, its existing completed spectral integral gives all the
bounded-calculus laws required by `NormalBorelFunctionalCalculus`. This constructor is the
one-way compatibility bridge: it does not pretend that every normal-functional PVM is
norm-additive, but it lets the two APIs interoperate whenever the stronger object is present. -/

/-- Construct a normal Borel-calculus certificate from a norm-valued PVM. -/
noncomputable def ofPVM (E : PVM ℝ A) :
    NormalBorelFunctionalCalculus (NormalPVM.ofPVM E) where
  boundedFC := fun f hf hfb =>
    (⟨E⟩ : AffiliatedObservable A).boundedFC f hf hfb
  boundedFC_congr := by
    intro f g hf hg hfb hgb hfg
    exact AffiliatedObservable.boundedFC_congr (⟨E⟩ : AffiliatedObservable A)
      hf hg hfb hgb hfg
  boundedFC_const := by
    intro c
    exact AffiliatedObservable.boundedFC_const (⟨E⟩ : AffiliatedObservable A) c
  boundedFC_add := by
    intro f g hf hg hfb hgb hfg
    simpa only using AffiliatedObservable.boundedFC_add
      (⟨E⟩ : AffiliatedObservable A) hf hg hfb hgb
  boundedFC_mul := by
    intro f g hf hg hfb hgb hfg
    simpa only using AffiliatedObservable.boundedFC_mul
      (⟨E⟩ : AffiliatedObservable A) hf hg hfb hgb
  boundedFC_smul := by
    intro c f hf hfb hcf
    simpa only using AffiliatedObservable.boundedFC_smul
      (⟨E⟩ : AffiliatedObservable A) c hf hfb
  boundedFC_star := by
    intro f hf hfb hstar
    simpa only using AffiliatedObservable.boundedFC_star
      (⟨E⟩ : AffiliatedObservable A) hf hfb
  boundedFC_mem_unitary := by
    intro f hf hfb hmod
    exact AffiliatedObservable.boundedFC_mem_unitary (⟨E⟩ : AffiliatedObservable A)
      hf hfb hmod
  boundedFC_indicator := by
    intro S hS
    exact AffiliatedObservable.boundedFC_indicator (⟨E⟩ : AffiliatedObservable A) hS

end NormalBorelFunctionalCalculus

/-! ## Bounded observables on the normal-PVM façade -/

/-- An algebra-level bounded Borel calculus for bounded observables in the normal-PVM model.
The per-measure `NormalBorelFunctionalCalculus` carries the actual measurable integration laws;
this class chooses the spectral measure and such a calculus for each bounded observable. Keeping
this choice explicit is necessary because a bare C⋆-algebra does not contain arbitrary Borel
projections. -/
class NormalObservableBorelCalculus (A : Type*) [WStarAlgebra A] where
  /-- The normal-functional spectral measure `E_a` assigned to each bounded observable `a`. -/
  spectralMeasure : Observable A → NormalPVM ℝ A
  /-- The bounded normal Borel calculus certificate for `spectralMeasure a`. -/
  calculus : ∀ a : Observable A,
    NormalBorelFunctionalCalculus (spectralMeasure a)
  spectralSupport : ∀ a : Observable A, ∃ C : ℝ, 0 ≤ C ∧
    ∀ S : Set ℝ, MeasurableSet S → Disjoint S (Set.Icc (-C) C) →
      spectralMeasure a S = 0

namespace NormalObservableBorelCalculus

variable {A : Type*} [WStarAlgebra A]

/-- The norm-additive bounded Borel calculus canonically supplies the normal-PVM version. -/
noncomputable def ofBorelFunctionalCalculus [BorelFunctionalCalculus A] :
    NormalObservableBorelCalculus A where
  spectralMeasure := fun a => NormalPVM.ofPVM (BorelFunctionalCalculus.spectralMeasure a)
  calculus := fun a => NormalBorelFunctionalCalculus.ofPVM
    (BorelFunctionalCalculus.spectralMeasure a)
  spectralSupport := BorelFunctionalCalculus.spectralSupport

end NormalObservableBorelCalculus

namespace Observable

variable {A : Type*} [WStarAlgebra A] [NormalObservableBorelCalculus A]

/-- Include a bounded observable in the normal affiliated façade. -/
def toNormalAffiliatedObservable (a : Observable A) : NormalAffiliatedObservable A where
  spectralMeasure := NormalObservableBorelCalculus.spectralMeasure a

/-- The per-observable normal Borel-calculus certificate selected by the algebra-level class. -/
def normalBorelCalculus (a : Observable A) :
    NormalBorelFunctionalCalculus
      (NormalObservableBorelCalculus.spectralMeasure a) :=
  NormalObservableBorelCalculus.calculus a

/-- Apply a bounded measurable function to a bounded observable in the normal affiliated algebra. -/
def normalBoundedFC (a : Observable A) (f : ℝ → ℂ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : A :=
  (Observable.normalBorelCalculus a).boundedFC f hf hfb

lemma normalBoundedFC_indicator (a : Observable A) {S : Set ℝ} (hS : MeasurableSet S) :
    Observable.normalBoundedFC a (AffiliatedObservable.indicatorFunction S)
      (AffiliatedObservable.indicatorFunction_measurable hS)
      (AffiliatedObservable.indicatorFunction_bounded S) =
      (NormalObservableBorelCalculus.spectralMeasure a S : A) := by
  exact (Observable.normalBorelCalculus a).boundedFC_indicator S hS

end Observable

namespace NormalAffiliatedObservable

variable (T : NormalAffiliatedObservable A)

/-- View a real normal affiliated observable as a complex normal affiliated operator by pushing
its spectral measure along the canonical embedding `ℝ → ℂ`. -/
def toNormalAffiliatedOperator : NormalAffiliatedOperator A where
  spectralMeasure := T.spectralMeasure.map Complex.ofReal Complex.measurable_ofReal

@[simp]
lemma toNormalAffiliatedOperator_spectralMeasure_apply {S : Set ℂ}
    (hS : MeasurableSet S) :
    (T.toNormalAffiliatedOperator.spectralMeasure S) =
      T.spectralMeasure (Complex.ofReal ⁻¹' S) := by
  exact T.spectralMeasure.map_apply Complex.measurable_ofReal hS

@[ext]
theorem ext {T U : NormalAffiliatedObservable A}
    (h : ∀ S : Set ℝ, MeasurableSet S → T.spectralMeasure S = U.spectralMeasure S) :
    T = U := by
  cases T with
  | mk T =>
    cases U with
    | mk U =>
      congr
      exact NormalPVM.ext h

/-- The spectral projection `E_T(S) ∈ A` associated to a Borel set `S ⊆ ℝ`. -/
def spectralProjection (S : Set ℝ) : Projection A :=
  T.spectralMeasure.spectralProjection S

@[simp]
lemma spectralProjection_univ : T.spectralProjection univ = ⟨1, IsStarProjection.one A⟩ := by
  apply Subtype.ext
  exact T.spectralMeasure.univ

@[simp]
lemma spectralProjection_empty : T.spectralProjection ∅ = ⟨0, IsStarProjection.zero A⟩ := by
  apply Subtype.ext
  exact T.spectralMeasure.empty

/-- The real measurable functional calculus at the normal-PVM level. -/
def measurableRealFC (f : ℝ → ℝ) (hf : Measurable f) : NormalAffiliatedObservable A where
  spectralMeasure := T.spectralMeasure.map f hf

@[simp]
lemma measurableRealFC_spectralMeasure_apply {f : ℝ → ℝ} (hf : Measurable f)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (T.measurableRealFC f hf).spectralMeasure S = T.spectralMeasure (f ⁻¹' S) := by
  exact T.spectralMeasure.map_apply hf hS

theorem measurableRealFC_comp (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    (T.measurableRealFC f hf).measurableRealFC g hg =
      T.measurableRealFC (g ∘ f) (hg.comp hf) := by
  apply NormalAffiliatedObservable.ext
  intro S hS
  rw [(T.measurableRealFC f hf).measurableRealFC_spectralMeasure_apply hg hS,
    T.measurableRealFC_spectralMeasure_apply (hg.comp hf) hS]
  change (T.spectralMeasure.map f hf) (g ⁻¹' S) = _
  rw [T.spectralMeasure.map_apply hf (hg hS)]
  congr 1

@[simp]
theorem measurableRealFC_id :
    T.measurableRealFC id measurable_id = T := by
  apply NormalAffiliatedObservable.ext
  intro S hS
  rw [T.measurableRealFC_spectralMeasure_apply measurable_id hS]
  rfl

/-! ### The complex measurable calculus

The real-valued calculus above stays in `NormalAffiliatedObservable`. The genuinely complex
measurable calculus changes the spectral space from `ℝ` to `ℂ`, so its result is a
`NormalAffiliatedOperator`. Keeping this operation here (rather than only in the norm-valued
`AffiliatedObservable` API) is important: normal-state additivity is the correct abstract setting
for infinite-dimensional von Neumann algebras. -/

/-- Apply a measurable complex-valued function to a normal affiliated observable. -/
def measurableFC (f : ℝ → ℂ) (hf : Measurable f) : NormalAffiliatedOperator A where
  spectralMeasure := T.spectralMeasure.map f hf

@[simp]
lemma measurableFC_spectralMeasure_apply {f : ℝ → ℂ} (hf : Measurable f)
    {S : Set ℂ} (hS : MeasurableSet S) :
    (T.measurableFC f hf).spectralMeasure S = T.spectralMeasure (f ⁻¹' S) := by
  exact T.spectralMeasure.map_apply hf hS

@[simp]
lemma measurableFC_ofReal :
    T.measurableFC Complex.ofReal Complex.measurable_ofReal =
      T.toNormalAffiliatedOperator := rfl

/-! ### Bounded Borel functions and dynamics -/

/-- Apply a supplied bounded normal Borel calculus to a normal affiliated observable. -/
def boundedFC (C : NormalBorelFunctionalCalculus T.spectralMeasure)
    (f : ℝ → ℂ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : A :=
  C.boundedFC f hf hfb

lemma boundedFC_indicator (C : NormalBorelFunctionalCalculus T.spectralMeasure)
    {S : Set ℝ} (hS : MeasurableSet S) :
    T.boundedFC C (AffiliatedObservable.indicatorFunction S)
        (AffiliatedObservable.indicatorFunction_measurable hS)
        (AffiliatedObservable.indicatorFunction_bounded S) =
      (T.spectralMeasure S : A) := by
  exact C.boundedFC_indicator S hS

/-- The bounded functional calculus exponential, as an algebra unitary. -/
noncomputable def expUnitary (C : NormalBorelFunctionalCalculus T.spectralMeasure)
    (t : ℝ) : unitary A :=
  ⟨C.boundedFC (AffiliatedObservable.expFunction t)
      (AffiliatedObservable.expFunction_measurable t)
      (AffiliatedObservable.expFunction_bounded t),
    C.boundedFC_mem_unitary (AffiliatedObservable.expFunction_measurable t)
      (AffiliatedObservable.expFunction_bounded t)
      (AffiliatedObservable.expFunction_modulus t)⟩

lemma expUnitary_add (C : NormalBorelFunctionalCalculus T.spectralMeasure) (t s : ℝ) :
    T.expUnitary C (t + s) = T.expUnitary C t * T.expUnitary C s := by
  apply Subtype.ext
  change C.boundedFC (AffiliatedObservable.expFunction (t + s))
      (AffiliatedObservable.expFunction_measurable (t + s))
      (AffiliatedObservable.expFunction_bounded (t + s)) =
    C.boundedFC (AffiliatedObservable.expFunction t)
      (AffiliatedObservable.expFunction_measurable t)
      (AffiliatedObservable.expFunction_bounded t) *
      C.boundedFC (AffiliatedObservable.expFunction s)
        (AffiliatedObservable.expFunction_measurable s)
        (AffiliatedObservable.expFunction_bounded s)
  have hprod : ∃ C' : ℝ, ∀ x,
      ‖AffiliatedObservable.expFunction t x * AffiliatedObservable.expFunction s x‖ ≤ C' := by
    rcases AffiliatedObservable.expFunction_bounded t with ⟨Ct, hCt⟩
    rcases AffiliatedObservable.expFunction_bounded s with ⟨Cs, hCs⟩
    refine ⟨Ct * Cs, fun x => ?_⟩
    simp only [norm_mul]
    exact mul_le_mul (hCt x) (hCs x) (norm_nonneg _)
      ((norm_nonneg (AffiliatedObservable.expFunction t 0)).trans (hCt 0))
  have hmul := C.boundedFC_mul
    (AffiliatedObservable.expFunction_measurable t)
    (AffiliatedObservable.expFunction_measurable s)
    (AffiliatedObservable.expFunction_bounded t)
    (AffiliatedObservable.expFunction_bounded s) hprod
  rw [← hmul]
  apply C.boundedFC_congr
    (AffiliatedObservable.expFunction_measurable (t + s))
    ((AffiliatedObservable.expFunction_measurable t).mul
      (AffiliatedObservable.expFunction_measurable s))
    (AffiliatedObservable.expFunction_bounded (t + s)) hprod
  intro x
  change Complex.exp ((((t + s) * x : ℝ) : ℂ) * Complex.I) =
    Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((s * x : ℝ) : ℂ) * Complex.I)
  have harg : (((t + s) * x : ℝ) : ℂ) * Complex.I =
      ((t * x : ℝ) : ℂ) * Complex.I + ((s * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_add]

lemma expUnitary_zero (C : NormalBorelFunctionalCalculus T.spectralMeasure) :
    T.expUnitary C 0 = 1 := by
  apply Subtype.ext
  change C.boundedFC (AffiliatedObservable.expFunction 0)
      (AffiliatedObservable.expFunction_measurable 0)
      (AffiliatedObservable.expFunction_bounded 0) = (1 : A)
  calc
    C.boundedFC (AffiliatedObservable.expFunction 0)
        (AffiliatedObservable.expFunction_measurable 0)
        (AffiliatedObservable.expFunction_bounded 0) =
        C.boundedFC (fun _ : ℝ => (1 : ℂ)) measurable_const
          (⟨1, by simp⟩) := by
      apply C.boundedFC_congr
        (AffiliatedObservable.expFunction_measurable 0) measurable_const
        (AffiliatedObservable.expFunction_bounded 0) (⟨1, by simp⟩)
      intro x
      simp [AffiliatedObservable.expFunction]
    _ = 1 := by simpa using C.boundedFC_const 1

lemma expUnitary_neg_mul (C : NormalBorelFunctionalCalculus T.spectralMeasure) (t : ℝ) :
    T.expUnitary C (-t) * T.expUnitary C t = 1 := by
  calc
    T.expUnitary C (-t) * T.expUnitary C t = T.expUnitary C (-t + t) :=
      (T.expUnitary_add C (-t) t).symm
    _ = T.expUnitary C 0 := by rw [neg_add_cancel]
    _ = 1 := T.expUnitary_zero C

lemma expUnitary_mul_neg (C : NormalBorelFunctionalCalculus T.spectralMeasure) (t : ℝ) :
    T.expUnitary C t * T.expUnitary C (-t) = 1 := by
  calc
    T.expUnitary C t * T.expUnitary C (-t) = T.expUnitary C (t + -t) :=
      (T.expUnitary_add C t (-t)).symm
    _ = T.expUnitary C 0 := by rw [add_neg_cancel]
    _ = 1 := T.expUnitary_zero C

/-! ### The conventional quantum-dynamics sign -/

/-- The unitary `exp (-i t T)`, exposed as a time-reversed view of the canonical
`exp (i t T)` calculus. -/
noncomputable def negativeExpUnitary
    (C : NormalBorelFunctionalCalculus T.spectralMeasure) (t : ℝ) : unitary A :=
  T.expUnitary C (-t)

@[simp]
lemma negativeExpUnitary_zero
    (C : NormalBorelFunctionalCalculus T.spectralMeasure) :
    T.negativeExpUnitary C 0 = 1 := by
  simpa [negativeExpUnitary] using T.expUnitary_zero C

lemma negativeExpUnitary_add
    (C : NormalBorelFunctionalCalculus T.spectralMeasure) (t s : ℝ) :
    T.negativeExpUnitary C (t + s) =
      T.negativeExpUnitary C t * T.negativeExpUnitary C s := by
  change T.expUnitary C (-(t + s)) =
    T.expUnitary C (-t) * T.expUnitary C (-s)
  rw [show -(t + s) = -t + -s by ring]
  exact T.expUnitary_add C (-t) (-s)

lemma negativeExpUnitary_neg_mul
    (C : NormalBorelFunctionalCalculus T.spectralMeasure) (t : ℝ) :
    T.negativeExpUnitary C (-t) * T.negativeExpUnitary C t = 1 := by
  simpa [negativeExpUnitary] using T.expUnitary_mul_neg C t

lemma negativeExpUnitary_mul_neg
    (C : NormalBorelFunctionalCalculus T.spectralMeasure) (t : ℝ) :
    T.negativeExpUnitary C t * T.negativeExpUnitary C (-t) = 1 := by
  simpa [negativeExpUnitary] using T.expUnitary_neg_mul C t

/-- The bounded resolvent supplied by the normal Borel calculus. -/
def resolvent (C : NormalBorelFunctionalCalculus T.spectralMeasure)
    (z : ℂ) (hz : z.im ≠ 0) : A :=
  C.boundedFC (AffiliatedObservable.resolventFunction z)
    (AffiliatedObservable.resolventFunction_measurable z)
    (AffiliatedObservable.resolventFunction_bounded z hz)

lemma resolvent_identity (C : NormalBorelFunctionalCalculus T.spectralMeasure)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    T.resolvent C z hz - T.resolvent C w hw =
      (z - w) • (T.resolvent C z hz * T.resolvent C w hw) := by
  change C.boundedFC (AffiliatedObservable.resolventFunction z)
      (AffiliatedObservable.resolventFunction_measurable z)
      (AffiliatedObservable.resolventFunction_bounded z hz) -
      C.boundedFC (AffiliatedObservable.resolventFunction w)
        (AffiliatedObservable.resolventFunction_measurable w)
        (AffiliatedObservable.resolventFunction_bounded w hw) =
    (z - w) • (C.boundedFC (AffiliatedObservable.resolventFunction z)
      (AffiliatedObservable.resolventFunction_measurable z)
      (AffiliatedObservable.resolventFunction_bounded z hz) *
      C.boundedFC (AffiliatedObservable.resolventFunction w)
        (AffiliatedObservable.resolventFunction_measurable w)
        (AffiliatedObservable.resolventFunction_bounded w hw))
  rcases AffiliatedObservable.resolventFunction_bounded z hz with ⟨Cz, hCz⟩
  rcases AffiliatedObservable.resolventFunction_bounded w hw with ⟨Cw, hCw⟩
  have hprod : ∃ C' : ℝ, ∀ x,
      ‖AffiliatedObservable.resolventFunction z x *
          AffiliatedObservable.resolventFunction w x‖ ≤ C' := by
    refine ⟨Cz * Cw, fun x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hCz x) (hCw x) (norm_nonneg _)
      ((norm_nonneg (AffiliatedObservable.resolventFunction z 0)).trans (hCz 0))
  have hscaled : ∃ C' : ℝ, ∀ x,
      ‖(z - w) * (AffiliatedObservable.resolventFunction z x *
        AffiliatedObservable.resolventFunction w x)‖ ≤ C' := by
    refine ⟨‖z - w‖ * (Cz * Cw), fun x => ?_⟩
    rw [norm_mul, norm_mul]
    exact mul_le_mul (le_rfl)
      (mul_le_mul (hCz x) (hCw x) (norm_nonneg _)
        ((norm_nonneg (AffiliatedObservable.resolventFunction z 0)).trans (hCz 0)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hdiff : ∃ C' : ℝ, ∀ x,
      ‖(AffiliatedObservable.resolventFunction z -
        AffiliatedObservable.resolventFunction w) x‖ ≤ C' := by
    refine ⟨Cz + Cw, fun x => ?_⟩
    simpa only [Pi.sub_apply] using
      (show ‖AffiliatedObservable.resolventFunction z x -
          AffiliatedObservable.resolventFunction w x‖ ≤ Cz + Cw from
        (norm_sub_le _ _).trans (add_le_add (hCz x) (hCw x)))
  have hsub := NormalBorelFunctionalCalculus.boundedFC_sub C
    (AffiliatedObservable.resolventFunction_measurable z)
    (AffiliatedObservable.resolventFunction_measurable w)
    (⟨Cz, hCz⟩) (⟨Cw, hCw⟩) hdiff
  have hmul := C.boundedFC_mul
    (AffiliatedObservable.resolventFunction_measurable z)
    (AffiliatedObservable.resolventFunction_measurable w)
    (⟨Cz, hCz⟩) (⟨Cw, hCw⟩) hprod
  have hsmul := C.boundedFC_smul (z - w)
    ((AffiliatedObservable.resolventFunction_measurable z).mul
      (AffiliatedObservable.resolventFunction_measurable w)) hprod hscaled
  calc
    _ = C.boundedFC (AffiliatedObservable.resolventFunction z -
        AffiliatedObservable.resolventFunction w)
        ((AffiliatedObservable.resolventFunction_measurable z).sub
          (AffiliatedObservable.resolventFunction_measurable w)) hdiff := hsub.symm
    _ = C.boundedFC (fun x => (z - w) *
        (AffiliatedObservable.resolventFunction z x *
          AffiliatedObservable.resolventFunction w x))
        (measurable_const.mul
          ((AffiliatedObservable.resolventFunction_measurable z).mul
            (AffiliatedObservable.resolventFunction_measurable w))) hscaled := by
      apply C.boundedFC_congr
        ((AffiliatedObservable.resolventFunction_measurable z).sub
          (AffiliatedObservable.resolventFunction_measurable w))
        ((measurable_const.mul
          ((AffiliatedObservable.resolventFunction_measurable z).mul
            (AffiliatedObservable.resolventFunction_measurable w)))) hdiff hscaled
      intro x
      dsimp [AffiliatedObservable.resolventFunction]
      have hne_z : (x : ℂ) - z ≠ 0 := by
        intro h
        apply hz
        simpa using congrArg Complex.im h
      have hne_w : (x : ℂ) - w ≠ 0 := by
        intro h
        apply hw
        simpa using congrArg Complex.im h
      field_simp
      ring
    _ = (z - w) • C.boundedFC
        (AffiliatedObservable.resolventFunction z *
          AffiliatedObservable.resolventFunction w)
        ((AffiliatedObservable.resolventFunction_measurable z).mul
          (AffiliatedObservable.resolventFunction_measurable w)) hprod := hsmul
    _ = (z - w) • (C.boundedFC (AffiliatedObservable.resolventFunction z)
        (AffiliatedObservable.resolventFunction_measurable z) (⟨Cz, hCz⟩) *
      C.boundedFC (AffiliatedObservable.resolventFunction w)
        (AffiliatedObservable.resolventFunction_measurable w) (⟨Cw, hCw⟩)) := by
      rw [hmul]

/-! ## Normal-state measurement statistics -/

/-- The probability distribution of a normal affiliated observable in a normal state. -/
def distribution (ω : NormalState A) : ProbabilityMeasure ℝ :=
  T.spectralMeasure.distribution ω

@[simp]
lemma distribution_apply (ω : NormalState A) {S : Set ℝ} (hS : MeasurableSet S) :
    (T.distribution ω : Measure ℝ) S = ENNReal.ofReal (ω (T.spectralMeasure S)).re := by
  exact T.spectralMeasure.distribution_apply ω S hS

theorem distribution_measurableRealFC (ω : NormalState A)
    {f : ℝ → ℝ} (hf : Measurable f) :
    ((T.measurableRealFC f hf).distribution ω : Measure ℝ) =
      Measure.map f (T.distribution ω : Measure ℝ) := by
  exact T.spectralMeasure.distribution_map ω f hf

/-- Finiteness of the `n`-th moment in a normal state. -/
def HasFiniteMoment (ω : NormalState A) (n : ℕ) : Prop :=
  Integrable (fun x : ℝ => x ^ n) (T.distribution ω : Measure ℝ)

/-- The `n`-th moment, defined only when its integrability hypothesis is available. -/
def moment (ω : NormalState A) (n : ℕ) (_ : T.HasFiniteMoment ω n) : ℝ :=
  ∫ x, x ^ n ∂(T.distribution ω : Measure ℝ)

/-- The expectation of a normal affiliated observable, when its first moment is finite. -/
def expectation (ω : NormalState A) (h : T.HasFiniteMoment ω 1) : ℝ :=
  T.moment ω 1 h

/-- The variance of a normal affiliated observable, when its first and second moments are finite. -/
def variance (ω : NormalState A) (h₁ : T.HasFiniteMoment ω 1)
    (h₂ : T.HasFiniteMoment ω 2) : ℝ :=
  T.moment ω 2 h₂ - (T.expectation ω h₁) ^ 2

end NormalAffiliatedObservable

namespace Observable

variable {A : Type*} [WStarAlgebra A] [NormalObservableBorelCalculus A]

/-! ### Bounded observables have finite normal-state moments -/

/-- Every bounded observable, included in the normal affiliated façade, has finite moments of every
order in every normal state. The normal calculus carries an explicit bounded-support certificate,
so the proof is the same measure-theoretic fact as in the norm-additive façade: the state
distribution is concentrated on a compact interval. -/
lemma toNormalAffiliatedObservable_hasFiniteMoment
    (a : Observable A) (ω : NormalState A) (n : ℕ) :
    (Observable.toNormalAffiliatedObservable a).HasFiniteMoment ω n := by
  obtain ⟨C, hC, hsupport⟩ := NormalObservableBorelCalculus.spectralSupport a
  let T : NormalAffiliatedObservable A := Observable.toNormalAffiliatedObservable a
  let K : Set ℝ := Set.Icc (-C) C
  have hK : MeasurableSet K := measurableSet_Icc
  have hdisj : Disjoint Kᶜ K := by
    refine Set.disjoint_left.2 ?_
    intro x hx hxK
    exact hx hxK
  have hzero : T.spectralMeasure Kᶜ = 0 := by
    exact hsupport Kᶜ hK.compl hdisj
  have hμzero : (T.distribution ω : Measure ℝ) Kᶜ = 0 := by
    rw [NormalAffiliatedObservable.distribution,
      NormalPVM.distribution_apply T.spectralMeasure ω Kᶜ hK.compl]
    rw [hzero]
    simp
  have hmem : ∀ᵐ x ∂(T.distribution ω : Measure ℝ), x ∈ K := by
    apply ae_iff.mpr
    change (T.distribution ω : Measure ℝ) Kᶜ = 0
    exact hμzero
  have hbound : ∀ᵐ x ∂(T.distribution ω : Measure ℝ),
      ‖x ^ n‖ ≤ C ^ n := by
    filter_upwards [hmem] with x hx
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg x) (abs_le.2 hx) n
  exact Integrable.of_bound (measurable_id.pow_const n).aestronglyMeasurable (C ^ n) hbound

/-! ### Observable-level dynamics and resolvents -/

/-- The unitary obtained by applying the normal bounded Borel calculus to
`λ ↦ exp (i t λ)`. -/
noncomputable def normalExpUnitary (a : Observable A) (t : ℝ) : unitary A :=
  NormalAffiliatedObservable.expUnitary
    (Observable.toNormalAffiliatedObservable a) (Observable.normalBorelCalculus a) t

@[simp]
lemma normalExpUnitary_zero (a : Observable A) :
    Observable.normalExpUnitary a 0 = 1 := by
  simpa [Observable.normalExpUnitary] using
    (NormalAffiliatedObservable.expUnitary_zero
      (Observable.toNormalAffiliatedObservable a) (Observable.normalBorelCalculus a))

lemma normalExpUnitary_add (a : Observable A) (t s : ℝ) :
    Observable.normalExpUnitary a (t + s) =
      Observable.normalExpUnitary a t * Observable.normalExpUnitary a s := by
  simpa [Observable.normalExpUnitary] using
    (NormalAffiliatedObservable.expUnitary_add
      (Observable.toNormalAffiliatedObservable a) (Observable.normalBorelCalculus a) t s)

lemma normalExpUnitary_neg_mul (a : Observable A) (t : ℝ) :
    Observable.normalExpUnitary a (-t) * Observable.normalExpUnitary a t = 1 := by
  simpa [Observable.normalExpUnitary] using
    (NormalAffiliatedObservable.expUnitary_neg_mul
      (Observable.toNormalAffiliatedObservable a) (Observable.normalBorelCalculus a) t)

lemma normalExpUnitary_mul_neg (a : Observable A) (t : ℝ) :
    Observable.normalExpUnitary a t * Observable.normalExpUnitary a (-t) = 1 := by
  simpa [Observable.normalExpUnitary] using
    (NormalAffiliatedObservable.expUnitary_mul_neg
      (Observable.toNormalAffiliatedObservable a) (Observable.normalBorelCalculus a) t)

/-- The observable-level quantum-dynamics convention `exp (-i t a)`. -/
noncomputable def normalNegativeExpUnitary (a : Observable A) (t : ℝ) : unitary A :=
  NormalAffiliatedObservable.negativeExpUnitary
    (Observable.toNormalAffiliatedObservable a) (Observable.normalBorelCalculus a) t

@[simp]
lemma normalNegativeExpUnitary_zero (a : Observable A) :
    Observable.normalNegativeExpUnitary a 0 = 1 := by
  simpa [Observable.normalNegativeExpUnitary] using
    (NormalAffiliatedObservable.negativeExpUnitary_zero
      (Observable.toNormalAffiliatedObservable a) (Observable.normalBorelCalculus a))

lemma normalNegativeExpUnitary_add (a : Observable A) (t s : ℝ) :
    Observable.normalNegativeExpUnitary a (t + s) =
      Observable.normalNegativeExpUnitary a t * Observable.normalNegativeExpUnitary a s := by
  simpa [Observable.normalNegativeExpUnitary] using
    (NormalAffiliatedObservable.negativeExpUnitary_add
      (Observable.toNormalAffiliatedObservable a) (Observable.normalBorelCalculus a) t s)

lemma normalNegativeExpUnitary_neg_mul (a : Observable A) (t : ℝ) :
    Observable.normalNegativeExpUnitary a (-t) * Observable.normalNegativeExpUnitary a t = 1 := by
  simpa [Observable.normalNegativeExpUnitary] using
    (NormalAffiliatedObservable.negativeExpUnitary_neg_mul
      (Observable.toNormalAffiliatedObservable a) (Observable.normalBorelCalculus a) t)

lemma normalNegativeExpUnitary_mul_neg (a : Observable A) (t : ℝ) :
    Observable.normalNegativeExpUnitary a t * Observable.normalNegativeExpUnitary a (-t) = 1 := by
  simpa [Observable.normalNegativeExpUnitary] using
    (NormalAffiliatedObservable.negativeExpUnitary_mul_neg
      (Observable.toNormalAffiliatedObservable a) (Observable.normalBorelCalculus a) t)

/-- The bounded resolvent `(a - z)⁻¹` supplied by the normal Borel calculus, for `z ∉ ℝ`. -/
def normalResolvent (a : Observable A) (z : ℂ) (hz : z.im ≠ 0) : A :=
  NormalAffiliatedObservable.resolvent
    (Observable.toNormalAffiliatedObservable a) (Observable.normalBorelCalculus a) z hz

lemma normalResolvent_identity (a : Observable A) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    Observable.normalResolvent a z hz - Observable.normalResolvent a w hw =
      (z - w) • (Observable.normalResolvent a z hz * Observable.normalResolvent a w hw) := by
  simpa [Observable.normalResolvent] using
    (NormalAffiliatedObservable.resolvent_identity
      (Observable.toNormalAffiliatedObservable a) (Observable.normalBorelCalculus a) z w hz hw)

end Observable

namespace NormalAffiliatedOperator

variable (T : NormalAffiliatedOperator A)

@[ext]
theorem ext {T U : NormalAffiliatedOperator A}
    (h : ∀ S : Set ℂ, MeasurableSet S → T.spectralMeasure S = U.spectralMeasure S) :
    T = U := by
  cases T with
  | mk T =>
    cases U with
    | mk U =>
      congr
      exact NormalPVM.ext h

/-- The complex measurable functional calculus at the normal-PVM level. -/
def measurableFC (f : ℂ → ℂ) (hf : Measurable f) : NormalAffiliatedOperator A where
  spectralMeasure := T.spectralMeasure.map f hf

@[simp]
lemma measurableFC_spectralMeasure_apply {f : ℂ → ℂ} (hf : Measurable f)
    {S : Set ℂ} (hS : MeasurableSet S) :
    (T.measurableFC f hf).spectralMeasure S = T.spectralMeasure (f ⁻¹' S) := by
  exact T.spectralMeasure.map_apply hf hS

theorem measurableFC_comp (f g : ℂ → ℂ) (hf : Measurable f) (hg : Measurable g) :
    (T.measurableFC f hf).measurableFC g hg =
      T.measurableFC (g ∘ f) (hg.comp hf) := by
  apply NormalAffiliatedOperator.ext
  intro S hS
  rw [(T.measurableFC f hf).measurableFC_spectralMeasure_apply hg hS,
    T.measurableFC_spectralMeasure_apply (hg.comp hf) hS]
  change (T.spectralMeasure.map f hf) (g ⁻¹' S) = _
  rw [T.spectralMeasure.map_apply hf (hg hS)]
  congr 1

@[simp]
theorem measurableFC_id :
    T.measurableFC id measurable_id = T := by
  apply NormalAffiliatedOperator.ext
  intro S hS
  rw [T.measurableFC_spectralMeasure_apply measurable_id hS]
  rfl

/-! ### Bounded complex Borel calculus -/

/-- Apply a supplied bounded Borel calculus to a genuinely complex normal affiliated operator. -/
def boundedFC (C : NormalBorelFunctionalCalculus T.spectralMeasure)
    (f : ℂ → ℂ) (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : A :=
  C.boundedFC f hf hfb

lemma boundedFC_indicator (C : NormalBorelFunctionalCalculus T.spectralMeasure)
    {S : Set ℂ} (hS : MeasurableSet S) :
    T.boundedFC C (normalIndicatorFunction S)
        (normalIndicatorFunction_measurable hS)
        (normalIndicatorFunction_bounded S) = (T.spectralMeasure S : A) := by
  exact C.boundedFC_indicator S hS

end NormalAffiliatedOperator

namespace NormalAffiliatedObservable

variable {A : Type*} [WStarAlgebra A]
variable (T : NormalAffiliatedObservable A)

/-- Measurable functional calculus is functorial under composition, including the change from the
real spectral variable to the complex spectral variable. -/
theorem measurableFC_comp (f : ℝ → ℂ) (g : ℂ → ℂ)
    (hf : Measurable f) (hg : Measurable g) :
    (T.measurableFC f hf).measurableFC g hg =
      T.measurableFC (g ∘ f) (hg.comp hf) := by
  apply NormalAffiliatedOperator.ext
  intro S hS
  rw [(T.measurableFC f hf).measurableFC_spectralMeasure_apply hg hS,
    T.measurableFC_spectralMeasure_apply (hg.comp hf) hS]
  change (T.spectralMeasure.map f hf) (g ⁻¹' S) =
    T.spectralMeasure ((g ∘ f) ⁻¹' S)
  rw [T.spectralMeasure.map_apply hf (hg hS)]
  rfl

theorem measurableRealFC_toNormalAffiliatedOperator
    {f : ℝ → ℝ} (hf : Measurable f) :
    (T.measurableRealFC f hf).toNormalAffiliatedOperator =
      T.measurableFC (fun x : ℝ => (f x : ℂ))
        (Complex.measurable_ofReal.comp hf) := by
  apply NormalAffiliatedOperator.ext
  intro S hS
  rw [(T.measurableRealFC f hf).toNormalAffiliatedOperator_spectralMeasure_apply hS]
  rw [T.measurableRealFC_spectralMeasure_apply hf (Complex.measurable_ofReal hS)]
  have hfc : Measurable (fun x : ℝ => (f x : ℂ)) := by
    simpa [Function.comp_def] using (Complex.measurable_ofReal.comp hf)
  rw [T.measurableFC_spectralMeasure_apply hfc hS]
  rfl

end NormalAffiliatedObservable

/-- Forget the normal-additivity witness when an explicit norm-valued PVM is available. -/
def NormalAffiliatedObservable.ofPVM {A : Type*} [WStarAlgebra A]
    (T : AffiliatedObservable A) : NormalAffiliatedObservable A :=
  ⟨NormalPVM.ofPVM T.spectralMeasure⟩

end OperatorAlgebra

end
