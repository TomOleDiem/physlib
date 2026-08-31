/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.POVM
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.NormalState

/-!
# Normal positive-operator-valued measures

`NormalPOVM` is the infinite-dimensional version of `POVM`. Its countable additivity is tested after
evaluation by every normal state, so it does not demand norm convergence of an operator series.
This is the POVM analogue of `NormalPVM`; the ordinary `POVM` remains useful as the stronger
norm-valued/vector-measure interface and embeds into this one.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra Function
open MeasureTheory Set

namespace OperatorAlgebra

variable {A : Type*} [WStarAlgebra A]

/-- A POVM whose σ-additivity is expressed through all normal states. -/
structure NormalPOVM (X : Type*) [MeasurableSpace X] (A : Type*) [WStarAlgebra A] where
  /-- The underlying set function. -/
  toFun : Set X → A
  nonneg' : ∀ S, 0 ≤ toFun S
  empty' : toFun ∅ = 0
  univ' : toFun univ = 1
  not_measurable' : ∀ S, ¬MeasurableSet S → toFun S = 0
  of_union' : ∀ {S T : Set X}, Disjoint S T → MeasurableSet S → MeasurableSet T →
    toFun (S ∪ T) = toFun S + toFun T
  m_iUnion' : ∀ (s : ℕ → Set X), (∀ n, MeasurableSet (s n)) → Pairwise (Disjoint on s) →
    ∀ ω : NormalState A,
      HasSum (fun n => ω (toFun (s n))) (ω (toFun (⋃ n, s n)))

namespace NormalPOVM

variable {X : Type*} [MeasurableSpace X] (M : NormalPOVM X A)

instance : CoeFun (NormalPOVM X A) (fun _ => Set X → A) := ⟨NormalPOVM.toFun⟩

lemma nonneg (S : Set X) : 0 ≤ (M S : A) := M.nonneg' S

@[simp]
lemma empty : M ∅ = 0 := M.empty'

@[simp]
lemma univ : M univ = 1 := M.univ'

@[simp]
lemma apply_eq_zero_of_not_measurableSet {S : Set X} (hS : ¬MeasurableSet S) : M S = 0 :=
  M.not_measurable' S hS

lemma of_union {S T : Set X} (hST : Disjoint S T) (hS : MeasurableSet S)
    (hT : MeasurableSet T) : M (S ∪ T) = M S + M T :=
  M.of_union' hST hS hT

lemma m_iUnion (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (Disjoint on s)) (ω : NormalState A) :
    HasSum (fun n => ω (M (s n))) (ω (M (⋃ n, s n))) :=
  M.m_iUnion' s hs hdisj ω

/-- Every measurable value of a normal POVM is an effect. -/
theorem mem_effect {S : Set X} (hS : MeasurableSet S) : 0 ≤ (M S : A) ∧ (M S : A) ≤ 1 := by
  have hunion : (M (S ∪ Sᶜ) : A) = M S + M Sᶜ :=
    M.of_union disjoint_compl_right hS hS.compl
  rw [Set.union_compl_self, M.univ] at hunion
  exact ⟨M.nonneg S, by
    have hle : (M S : A) ≤ M S + M Sᶜ := le_add_of_nonneg_right (M.nonneg Sᶜ)
    rwa [← hunion] at hle⟩

/-- A norm-additive `POVM` is automatically a normal POVM. -/
def ofPOVM {X : Type*} [MeasurableSpace X] (M : POVM X A) : NormalPOVM X A where
  toFun := M
  nonneg' := M.nonneg
  empty' := by simp
  univ' := M.univ
  not_measurable' S hS := M.toVectorMeasure.not_measurable hS
  of_union' := fun hST hS hT => M.toVectorMeasure.of_union hST hS hT
  m_iUnion' := fun s hs hdisj ω =>
    (M.toVectorMeasure.m_iUnion hs hdisj).map ω.toState.toPositiveLinearMap ω.continuous

@[simp]
lemma ofPOVM_apply {X : Type*} [MeasurableSpace X] (M : POVM X A) (S : Set X) :
    ofPOVM M S = M S := rfl

@[ext]
theorem ext {M N : NormalPOVM X A}
    (h : ∀ S : Set X, MeasurableSet S → M S = N S) : M = N := by
  cases M with
  | mk M hm he hu hnm hU hi =>
    cases N with
    | mk N hn ne nu hnm' hU' hi' =>
      congr
      funext S
      by_cases hS : MeasurableSet S
      · exact h S hS
      · rw [hnm S hS, hnm' S hS]

/-- The scalar probability measure induced by a normal POVM and a normal state. -/
def distribution (M : NormalPOVM X A) (ω : NormalState A) : ProbabilityMeasure X := by
  let m : ∀ S : Set X, MeasurableSet S → ENNReal :=
    fun S _ => ENNReal.ofReal (ω (M S)).re
  have hm_nonneg : ∀ S : Set X, MeasurableSet S → 0 ≤ (ω (M S)).re := by
    intro S _
    exact (Complex.le_def.mp (ω.toState.toPositiveLinearMap.map_nonneg (M.nonneg S))).1
  have hm_empty : m ∅ MeasurableSet.empty = 0 := by simp [m, M.empty]
  have hm_iUnion : ∀ ⦃f : ℕ → Set X⦄ (h : ∀ i, MeasurableSet (f i)),
      Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion h) =
        ∑' i, m (f i) (h i) := by
    intro f hf hdisj
    have hs := M.m_iUnion f hf hdisj ω
    have hre : HasSum (fun i => (ω (M (f i))).re) (ω (M (⋃ i, f i))).re := by
      exact hs.map Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous
    dsimp [m]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hm_nonneg _ (hf i)) hre.summable]
    exact congrArg ENNReal.ofReal hre.tsum_eq.symm
  let μ : Measure X := Measure.ofMeasurable m hm_empty hm_iUnion
  have hμ_univ : μ Set.univ = 1 := by
    dsimp [μ]
    rw [Measure.ofMeasurable_apply _ MeasurableSet.univ]
    dsimp [m]
    rw [M.univ]
    rw [show (ω.toState.toPositiveLinearMap (1 : A)).re = 1 by rw [ω.toState.map_one]; rfl]
    simp
  exact ⟨μ, ⟨hμ_univ⟩⟩

lemma distribution_apply (M : NormalPOVM X A) (ω : NormalState A) (S : Set X)
    (hS : MeasurableSet S) :
    (M.distribution ω : Measure X) S = ENNReal.ofReal (ω (M S)).re := by
  simp only [distribution, ProbabilityMeasure.coe_mk, Measure.ofMeasurable_apply _ hS]

end NormalPOVM

end OperatorAlgebra
