/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.PVM

/-!
# Normal-functional projection-valued measures

The norm-valued `PVM` in `PVM.lean` is useful for an abstract vector-measure API, but its
countable additivity is too strong for the spectral measure of a general operator in `B(H)`.  An
infinite orthogonal decomposition is additive in the strong/weak operator sense, not in operator
norm.  `NormalPVM` records the corresponding von Neumann-algebra contract: finite projection
algebra is explicit, while countable additivity is required only after evaluation by every normal
state.

This is intentionally a separate type for now.  It lets the correct infinite-dimensional
semantics be developed without silently weakening the existing norm-valued `PVM` or changing the
already-proved bounded spectral-data API underneath it.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra Function
open MeasureTheory Set

namespace OperatorAlgebra

variable {A : Type*} [WStarAlgebra A]

/-- A projection-valued measure whose σ-additivity is expressed through all normal states.

The values on nonmeasurable sets are fixed to zero, matching Mathlib's measure convention.  The
`m_iUnion` field is the normal-functional version of countable additivity; unlike the field of
the norm-valued `PVM`, it does not demand a norm-convergent operator series. -/
structure NormalPVM (X : Type*) [MeasurableSpace X] (A : Type*) [WStarAlgebra A] where
  toFun : Set X → A
  isStarProjection' : ∀ S, IsStarProjection (toFun S)
  empty' : toFun ∅ = 0
  univ' : toFun univ = 1
  not_measurable' : ∀ S, ¬MeasurableSet S → toFun S = 0
  of_union' : ∀ {S T : Set X}, Disjoint S T → MeasurableSet S → MeasurableSet T →
    toFun (S ∪ T) = toFun S + toFun T
  m_iUnion' : ∀ (s : ℕ → Set X), (∀ n, MeasurableSet (s n)) → Pairwise (Disjoint on s) →
    ∀ ω : NormalState A,
      HasSum (fun n => ω (toFun (s n))) (ω (toFun (⋃ n, s n)))

namespace NormalPVM

variable {X : Type*} [MeasurableSpace X] (E : NormalPVM X A)

instance : CoeFun (NormalPVM X A) (fun _ => Set X → A) := ⟨NormalPVM.toFun⟩

/-! ### Conversion from the norm-additive layer -/

/-- Regard a norm-valued `PVM` as a normal PVM.  This direction is automatic: a norm-convergent
vector-measure sum remains convergent after applying any continuous normal state.  The converse is
not available in general, since weak/normal-state additivity does not imply norm additivity. -/
def ofPVM {X : Type*} [MeasurableSpace X] (E : PVM X A) : NormalPVM X A where
  toFun := E
  isStarProjection' := E.isStarProjection'
  empty' := E.empty
  univ' := E.univ
  not_measurable' := E.not_measurable'
  of_union' := E.of_union
  m_iUnion' := fun s hs hd ω =>
    (E.toVectorMeasure.m_iUnion hs hd).map ω.toState.toPositiveLinearMap ω.continuous

@[simp]
lemma ofPVM_apply {X : Type*} [MeasurableSpace X] (E : PVM X A) (S : Set X) :
    ofPVM E S = E S := rfl

@[ext]
theorem ext {E F : NormalPVM X A}
    (h : ∀ S : Set X, MeasurableSet S → E S = F S) : E = F := by
  cases E with
  | mk E hE eE uE hnm hu hs =>
    cases F with
    | mk F hF eF uF hnm' hu' hs' =>
      congr
      funext S
      by_cases hS : MeasurableSet S
      · exact h S hS
      · rw [hnm S hS, hnm' S hS]

@[simp]
lemma univ : E univ = 1 := E.univ'

@[simp]
lemma empty : E ∅ = 0 := E.empty'

@[simp]
lemma apply_eq_zero_of_not_measurableSet {S : Set X} (hS : ¬MeasurableSet S) : E S = 0 :=
  E.not_measurable' S hS

lemma isStarProjection (S : Set X) : IsStarProjection (E S) := E.isStarProjection' S

/-- The projection associated to a measurable set. -/
def spectralProjection (S : Set X) : Projection A := ⟨E S, E.isStarProjection S⟩

lemma of_union {S T : Set X} (hST : Disjoint S T) (hS : MeasurableSet S)
    (hT : MeasurableSet T) : E (S ∪ T) = E S + E T :=
  E.of_union' hST hS hT

lemma m_iUnion (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (Disjoint on s)) (ω : NormalState A) :
    HasSum (fun n => ω (E (s n))) (ω (E (⋃ n, s n))) :=
  E.m_iUnion' s hs hdisj ω

lemma comp_self (S : Set X) : E S * E S = E S :=
  (E.isStarProjection S).isIdempotentElem

lemma comp_of_disjoint {S T : Set X} (hST : Disjoint S T) (hS : MeasurableSet S)
    (hT : MeasurableSet T) : E S * E T = 0 := by
  have hunion : E (S ∪ T) = E S + E T := E.of_union hST hS hT
  have hp : E S * E (S ∪ T) = E S := by
    refine (IsStarProjection.sub_iff_mul_eq_left (E.isStarProjection S)
      (E.isStarProjection (S ∪ T))).mp ?_
    rw [hunion]
    simpa using E.isStarProjection T
  rw [hunion, mul_add, E.comp_self S] at hp
  have h0 : E S + E S * E T = E S + 0 := by rw [add_zero]; exact hp
  exact add_left_cancel h0

lemma comp_eq_of_inter {S T : Set X} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    E S * E T = E (S ∩ T) := by
  nth_rw 1 [← inter_union_sdiff T S, ← inter_union_sdiff S T]
  simp only [E.of_union, hS.inter hT, hT.inter hS, hS.diff hT, hT.diff hS,
    disjoint_sdiff_inter.symm, add_mul, mul_add]
  rw [inter_comm T S, E.comp_of_disjoint disjoint_sdiff_inter (hS.diff hT) (hS.inter hT),
    inter_comm S T, E.comp_of_disjoint disjoint_sdiff_inter.symm (hT.inter hS) (hT.diff hS)]
  rw [E.comp_of_disjoint disjoint_sdiff_sdiff (hS.diff hT) (hT.diff hS)]
  simp only [add_zero, zero_add]
  exact E.comp_self (T ∩ S)

lemma commute (S T : Set X) : Commute (E S) (E T) := by
  by_cases hST : MeasurableSet S ∧ MeasurableSet T
  · simp [commute_iff_eq, comp_eq_of_inter, hST, inter_comm]
  · rcases not_and_or.mp hST with hS | hT <;> simp [*]

/-! ### Pushforward -/

/-- Push a normal PVM forward along a measurable map. -/
noncomputable def map {Y : Type*} [MeasurableSpace Y] (f : X → Y) (hf : Measurable f) :
    NormalPVM Y A := by
  classical
  refine
    { toFun := fun S => if hS : MeasurableSet S then E (f ⁻¹' S) else 0
      isStarProjection' := ?_
      empty' := ?_
      univ' := ?_
      not_measurable' := ?_
      of_union' := ?_
      m_iUnion' := ?_ }
  · intro S
    by_cases hS : MeasurableSet S
    · simp only [hS, ↓reduceIte]
      exact E.isStarProjection _
    · simp only [hS, ↓reduceIte]
      exact IsStarProjection.zero A
  · rw [dif_pos MeasurableSet.empty, preimage_empty]
    exact E.empty
  · rw [dif_pos MeasurableSet.univ, preimage_univ]
    exact E.univ
  · intro S hS
    simp [hS]
  · intro S T hST hS hT
    simp only [hS, hT, hS.union hT, ↓reduceIte, preimage_union]
    exact E.of_union (hST.preimage f) (hf hS) (hf hT)
  · intro s hs hdisj ω
    have hpre : ∀ n, MeasurableSet (f ⁻¹' s n) := fun n => hf (hs n)
    have hpre_disj : Pairwise (Disjoint on fun n => f ⁻¹' s n) := by
      intro i j hij
      exact (hdisj hij).preimage f
    have hsum := E.m_iUnion (fun n => f ⁻¹' s n) hpre hpre_disj ω
    have hU : MeasurableSet (⋃ n, s n) := MeasurableSet.iUnion hs
    simpa only [dif_pos (hs _), dif_pos hU, preimage_iUnion] using hsum

@[simp]
lemma map_apply {Y : Type*} [MeasurableSpace Y] {f : X → Y} (hf : Measurable f)
    {S : Set Y} (hS : MeasurableSet S) : E.map f hf S = E (f ⁻¹' S) := by
  classical
  simp [NormalPVM.map, hS]

theorem map_map {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    {f : X → Y} {g : Y → Z} (hf : Measurable f) (hg : Measurable g) :
    (E.map f hf).map g hg = E.map (g ∘ f) (hg.comp hf) := by
  apply NormalPVM.ext
  intro S hS
  rw [(E.map f hf).map_apply hg hS, E.map_apply hf (hg hS),
    E.map_apply (hg.comp hf) hS]
  rfl

/-! ### Normal-state statistics -/

/-- The probability measure obtained by evaluating a normal PVM in a normal state.

The countable-additivity proof consumes `NormalPVM.m_iUnion` directly.  No norm convergence of the
operator-valued series is used; this is the measurement-theoretically correct construction for an
infinite-dimensional von Neumann algebra. -/
def distribution (E : NormalPVM X A) (ω : NormalState A) : ProbabilityMeasure X := by
  let m : ∀ S : Set X, MeasurableSet S → ENNReal :=
    fun S _ => ENNReal.ofReal (ω (E S)).re
  have hm_nonneg : ∀ S : Set X, MeasurableSet S → 0 ≤ (ω (E S)).re := by
    intro S hS
    have hp : 0 ≤ (E S : A) := (Projection.mem_effect (E.spectralProjection S)).1
    exact (Complex.le_def.mp (ω.toState.toPositiveLinearMap.map_nonneg hp)).1
  have hm_empty : m ∅ MeasurableSet.empty = 0 := by
    dsimp [m]
    rw [E.empty]
    simp
  have hm_iUnion : ∀ ⦃s : ℕ → Set X⦄ (hs : ∀ n, MeasurableSet (s n)),
      Pairwise (Disjoint on s) →
        m (⋃ n, s n) (MeasurableSet.iUnion hs) = ∑' n, m (s n) (hs n) := by
    intro s hs hdisj
    have hsum := E.m_iUnion s hs hdisj ω
    have hreal : HasSum (fun n => (ω (E (s n))).re) (ω (E (⋃ n, s n))).re := by
      exact hsum.map Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous
    dsimp [m]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => hm_nonneg (s n) (hs n)) hreal.summable]
    exact congrArg ENNReal.ofReal hreal.tsum_eq.symm
  let μ : Measure X := Measure.ofMeasurable m hm_empty hm_iUnion
  have hμ_univ : μ Set.univ = 1 := by
    dsimp [μ]
    rw [Measure.ofMeasurable_apply _ MeasurableSet.univ]
    dsimp [m]
    rw [E.univ]
    have hreal : (ω.toState.toPositiveLinearMap 1).re = 1 := by
      calc
        (ω.toPositiveLinearMap 1).re = ((1 : ℂ)).re :=
          congrArg Complex.re ω.toState.map_one
        _ = 1 := rfl
    rw [hreal]
    simp
  exact ⟨μ, ⟨hμ_univ⟩⟩

@[simp]
lemma distribution_apply (E : NormalPVM X A) (ω : NormalState A) (S : Set X)
    (hS : MeasurableSet S) :
    (E.distribution ω : Measure X) S = ENNReal.ofReal (ω (E S)).re := by
  simp only [distribution, ProbabilityMeasure.coe_mk, Measure.ofMeasurable_apply _ hS]

theorem distribution_map {Y : Type*} [MeasurableSpace Y]
    (E : NormalPVM X A) (ω : NormalState A) (f : X → Y) (hf : Measurable f) :
    ((E.map f hf).distribution ω : Measure Y) =
      Measure.map f (E.distribution ω : Measure X) := by
  apply Measure.ext
  intro S hS
  rw [distribution_apply (E.map f hf) ω S hS]
  rw [Measure.map_apply hf hS]
  rw [distribution_apply E ω (f ⁻¹' S) (hf hS)]
  rw [E.map_apply hf hS]

end NormalPVM

/-! ### The predual-functional refinement

Normal states are enough for probability distributions, but they are not the right separating
family for operator-valued integration: a general matrix coefficient is not positive.  The
following refinement records σ-additivity after every vector of the chosen predual.  It is the
interface consumed by weak-operator representations; `NormalPVM` remains available as the smaller
measurement-facing façade. -/

/-- A normal PVM with countable additivity against every canonical predual functional.

The extra field is deliberately not inferred from `NormalPVM`: positivity of a state does not by
itself provide the complex linear span of all normal functionals.  For a norm-valued `PVM` the
refinement is automatic, while for a genuinely weakly additive PVM it is the precise normality
certificate needed by the spectral-integral layer. -/
structure PredualPVM (X : Type*) [MeasurableSpace X] (A : Type*) [WStarAlgebra A]
    extends NormalPVM X A where
  m_iUnion_predual' : ∀ (s : ℕ → Set X), (∀ n, MeasurableSet (s n)) →
    Pairwise (Disjoint on s) → ∀ ξ : WStarAlgebra.Predual A,
      HasSum (fun n => WStarAlgebra.predualPairing ξ (toFun (s n)))
        (WStarAlgebra.predualPairing ξ (toFun (⋃ n, s n)))

namespace PredualPVM

variable {X : Type*} [MeasurableSpace X] {A : Type*} [WStarAlgebra A]

instance : CoeFun (PredualPVM X A) (fun _ => Set X → A) :=
  ⟨fun E => E.toNormalPVM.toFun⟩

@[simp]
lemma toNormalPVM_apply (E : PredualPVM X A) (S : Set X) :
    E.toNormalPVM S = E S := rfl

@[ext]
theorem ext {E F : PredualPVM X A}
    (h : ∀ S : Set X, MeasurableSet S → E S = F S) : E = F := by
  cases E with
  | mk E hE =>
    cases F with
    | mk F hF =>
      congr
      exact NormalPVM.ext h

lemma m_iUnion (E : PredualPVM X A) (s : ℕ → Set X)
    (hs : ∀ n, MeasurableSet (s n)) (hdisj : Pairwise (Disjoint on s))
    (ξ : WStarAlgebra.Predual A) :
    HasSum (fun n => WStarAlgebra.predualPairing ξ (E (s n)))
      (WStarAlgebra.predualPairing ξ (E (⋃ n, s n))) :=
  E.m_iUnion_predual' s hs hdisj ξ

lemma toNormalPVM_m_iUnion (E : PredualPVM X A) (s : ℕ → Set X)
    (hs : ∀ n, MeasurableSet (s n)) (hdisj : Pairwise (Disjoint on s))
    (ω : NormalState A) :
    HasSum (fun n => ω (E (s n))) (ω (E (⋃ n, s n))) :=
  E.toNormalPVM.m_iUnion s hs hdisj ω

/-! A norm-valued PVM automatically has the stronger predual additivity. -/

/-- Upgrade a norm-additive PVM to the predual-functional refinement. -/
def ofPVM {X : Type*} [MeasurableSpace X] {A : Type*} [WStarAlgebra A]
    (E : PVM X A) : PredualPVM X A where
  toNormalPVM := NormalPVM.ofPVM E
  m_iUnion_predual' := fun s hs hd ξ =>
    (E.toVectorMeasure.m_iUnion hs hd).map
      (WStarAlgebra.predualPairing ξ) (WStarAlgebra.predualPairing ξ).continuous

@[simp]
lemma ofPVM_apply {X : Type*} [MeasurableSpace X] {A : Type*} [WStarAlgebra A]
    (E : PVM X A) (S : Set X) : ofPVM E S = E S := rfl

/-! Pushforward preserves both the state and predual-functional additivity witnesses. -/

noncomputable def map {Y : Type*} [MeasurableSpace Y]
    (E : PredualPVM X A) (f : X → Y) (hf : Measurable f) : PredualPVM Y A := by
  classical
  refine
    { toNormalPVM := E.toNormalPVM.map f hf
      m_iUnion_predual' := ?_ }
  intro s hs hdisj ξ
  have hpre : ∀ n, MeasurableSet (f ⁻¹' s n) := fun n => hf (hs n)
  have hpre_disj : Pairwise (Disjoint on fun n => f ⁻¹' s n) := by
    intro i j hij
    exact (hdisj hij).preimage f
  have hsum := E.m_iUnion (fun n => f ⁻¹' s n) hpre hpre_disj ξ
  have hU : MeasurableSet (⋃ n, s n) := MeasurableSet.iUnion hs
  simpa only [NormalPVM.map_apply E.toNormalPVM hf (hs _),
    NormalPVM.map_apply E.toNormalPVM hf hU,
    preimage_iUnion] using hsum

@[simp]
lemma map_apply {Y : Type*} [MeasurableSpace Y] (E : PredualPVM X A)
    {f : X → Y} (hf : Measurable f) {S : Set Y} (hS : MeasurableSet S) :
    E.map f hf S = E (f ⁻¹' S) := by
  exact NormalPVM.map_apply E.toNormalPVM hf hS

theorem map_map {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    (E : PredualPVM X A) {f : X → Y} {g : Y → Z}
    (hf : Measurable f) (hg : Measurable g) :
    (E.map f hf).map g hg = E.map (g ∘ f) (hg.comp hf) := by
  apply PredualPVM.ext
  intro S hS
  rw [PredualPVM.map_apply (E.map f hf) hg hS,
    PredualPVM.map_apply E (hg.comp hf) hS,
    PredualPVM.map_apply E hf (hg hS)]
  rfl

end PredualPVM

end OperatorAlgebra

end
