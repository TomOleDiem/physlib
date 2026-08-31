/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.PVM
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.FinitePOVM

/-!

# General POVMs

The abstract W⋆-algebra route implements the sharp/projective case in `Measurement/PVM.lean`.
This file lifts that same construction from projections to general effects, which is the textbook
notion of a POVM (`M(S) ≥ 0`, `M(X) = 1`, valued in an additive operator space, *not* restricted to
`Effect A`'s own `Set.Icc` order structure since effects are not closed under addition — matching
`todo.md`'s explicit warning).

Every `PVM` is in particular a `POVM` (a projection is in particular a positive effect):
`PVM.toPOVM`. The measurement-statistics bridge `μ_{ω,M}(S) = ω(M(S))` is `POVM.distribution`,
built exactly as `PVM.distribution` is, generalized from `Projection.mem_effect` to the bare
positivity/normalization hypotheses `POVM` carries directly.

## Key results

- `POVM X A` : a σ-additive, normalized, pointwise-nonnegative `A`-valued measure on `X` — the
  general (non-projective) measurement notion.
- `POVM.mem_effect` : every value `M S` (`S` measurable) is a genuine effect, `0 ≤ M S ≤ 1`.
- `PVM.toPOVM` : the inclusion of projection-valued measures into general POVMs.
- `POVM.distribution` : `μ_{ω,M}(S) = ω(M(S))`, the induced scalar probability measure.
- `FinitePOVM.toPOVM` : the finite-discrete case (`FinitePOVM.lean`'s `FinitePOVM`, viewed on the
  discrete measurable space on `X`) recovers a `POVM`, as a finite sum of Dirac vector measures.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra Function
open MeasureTheory Set

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-! ## General POVMs -/

/-- A *positive operator-valued measure* (POVM) on a measurable space `X`, valued in `A`: a
σ-additive function `Set X → A` (a `VectorMeasure`, hence automatically `0` on the empty set and
on non-measurable sets), pointwise nonnegative, and normalized to `1` on `univ`.

Generalizes `PVM X A` (`PVM.lean`) by dropping the requirement that every value be a star
projection, keeping only positivity — the textbook general POVM, as opposed to the special
"sharp"/projective case. Every `PVM` is a `POVM` (`PVM.toPOVM`), but not conversely: a genuine
POVM's values need only be effects, not projections. -/
structure POVM (X : Type*) [MeasurableSpace X] (A : Type*) [OperatorAlgebra A]
    extends VectorMeasure X A where
  nonneg' : ∀ S, 0 ≤ measureOf' S
  univ' : measureOf' univ = 1

namespace POVM

variable {X : Type*} [MeasurableSpace X] (M : POVM X A)

attribute [coe] toVectorMeasure

instance instCoeVectorMeasure : Coe (POVM X A) (VectorMeasure X A) := ⟨toVectorMeasure⟩

instance instCoeFun : CoeFun (POVM X A) fun _ => Set X → A := ⟨fun M => ⇑M.toVectorMeasure⟩

lemma nonneg (S : Set X) : 0 ≤ (M S : A) := M.nonneg' S

@[simp]
lemma univ : M univ = 1 := M.univ'

/-- **A measurable value never exceeds `1`.** `M S ≤ 1` for `S` measurable: `S` and `Sᶜ` are
disjoint with union `univ`, so `M S + M Sᶜ = M univ = 1` (`VectorMeasure.of_union`), and
`M Sᶜ ≥ 0` (`POVM.nonneg`) gives `M S ≤ 1` directly. -/
theorem le_one_of_measurableSet {S : Set X} (hS : MeasurableSet S) : (M S : A) ≤ 1 := by
  have hunion : (M (S ∪ Sᶜ) : A) = M S + M Sᶜ :=
    M.toVectorMeasure.of_union disjoint_compl_right hS hS.compl
  rw [Set.union_compl_self, M.univ] at hunion
  have hle : (M S : A) ≤ M S + M Sᶜ := le_add_of_nonneg_right (M.nonneg Sᶜ)
  rwa [← hunion] at hle

/-- **Every measurable value of a POVM is a genuine effect**: `0 ≤ M S ≤ 1`, matching
`Projection.mem_effect`'s statement for `PVM`. -/
theorem mem_effect {S : Set X} (hS : MeasurableSet S) : 0 ≤ (M S : A) ∧ (M S : A) ≤ 1 :=
  ⟨M.nonneg S, M.le_one_of_measurableSet hS⟩

end POVM

/-! ## Every PVM is a POVM -/

/-- **The canonical inclusion of projection-valued measures into general POVMs**: a `PVM`'s
values are already star projections, hence in particular nonnegative
(`Projection.nonneg_of_isStarProjection`), so it satisfies `POVM`'s (weaker) positivity
requirement for free. -/
def PVM.toPOVM {X : Type*} [MeasurableSpace X] (E : PVM X A) : POVM X A where
  toVectorMeasure := E.toVectorMeasure
  nonneg' S := by
    by_cases hS : MeasurableSet S
    · exact Projection.nonneg_of_isStarProjection (E.isStarProjection S)
    · exact le_of_eq (E.toVectorMeasure.not_measurable hS).symm
  univ' := E.univ'

@[simp]
lemma PVM.toPOVM_apply {X : Type*} [MeasurableSpace X] (E : PVM X A) (S : Set X) :
    (E.toPOVM : POVM X A) S = E S := rfl

/-! ## Measurement statistics: `μ_{ω,M}(S) = ω(M(S))` -/

/-- The scalar probability measure `μ_{ω,M}(S) = ω (M S)` induced on `X` by evaluating the POVM
`M` against a normal state `ω`. Exactly `PVM.distribution`'s construction, generalized from
`Projection.mem_effect` to `POVM.mem_effect`. -/
def POVM.distribution {A : Type*} [WStarAlgebra A] {X : Type*} [MeasurableSpace X] (M : POVM X A)
    (ω : NormalState A) : ProbabilityMeasure X := by
  let m : ∀ S : Set X, MeasurableSet S → ENNReal :=
    fun S _ => ENNReal.ofReal (ω (M S)).re
  have hm_nonneg : ∀ S : Set X, MeasurableSet S → 0 ≤ (ω (M S)).re := by
    intro S _
    exact (Complex.le_def.mp (ω.toState.toPositiveLinearMap.map_nonneg (M.nonneg S))).1
  have hm_empty : m ∅ MeasurableSet.empty = 0 := by
    simp [m]
  have hm_iUnion : ∀ ⦃f : ℕ → Set X⦄ (h : ∀ i, MeasurableSet (f i)),
      Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion h) =
        ∑' i, m (f i) (h i) := by
    intro f hf hdisj
    have hs : HasSum (fun i => M (f i)) (M (⋃ i, f i)) := M.toVectorMeasure.m_iUnion hf hdisj
    have hω : HasSum (fun i => ω (M (f i))) (ω (M (⋃ i, f i))) :=
      hs.map ω.toState.toPositiveLinearMap ω.continuous
    have hre : HasSum (fun i => (ω (M (f i))).re) (ω (M (⋃ i, f i))).re := by
      exact hω.map Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous
    dsimp [m]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hm_nonneg _ (hf i)) hre.summable]
    exact congrArg ENNReal.ofReal hre.tsum_eq.symm
  let μ : Measure X := Measure.ofMeasurable m hm_empty hm_iUnion
  have hμ_univ : μ Set.univ = 1 := by
    dsimp [μ]
    rw [Measure.ofMeasurable_apply _ MeasurableSet.univ]
    dsimp [m]
    rw [M.univ]
    have hreal : (ω.toState.toPositiveLinearMap 1).re = 1 := by
      calc
        (ω.toPositiveLinearMap 1).re = ((1 : ℂ)).re :=
          congrArg Complex.re ω.toState.map_one
        _ = 1 := rfl
    rw [hreal]
    simp
  exact ⟨μ, ⟨hμ_univ⟩⟩

/-- The defining property of `POVM.distribution`: `μ_{ω,M}(S) = ω(M(S))` for measurable `S`. -/
lemma POVM.distribution_apply {A : Type*} [WStarAlgebra A] {X : Type*} [MeasurableSpace X]
    (M : POVM X A) (ω : NormalState A) (S : Set X) (hS : MeasurableSet S) :
    (M.distribution ω : Measure X) S = ENNReal.ofReal (ω (M S)).re := by
  simp only [distribution, ProbabilityMeasure.coe_mk, Measure.ofMeasurable_apply _ hS]

/-- **`PVM.distribution` and `POVM.distribution` agree** along the canonical inclusion
`PVM.toPOVM`: the two constructions compute the same scalar measure, as they must, since
`POVM.distribution` was built to literally be `PVM.distribution`'s construction generalized. -/
theorem PVM.distribution_toPOVM {A : Type*} [WStarAlgebra A] {X : Type*} [MeasurableSpace X]
    (E : PVM X A) (ω : NormalState A) :
    (E.toPOVM : POVM X A).distribution ω = E.distribution ω := by
  apply ProbabilityMeasure.toMeasure_injective
  ext S hS
  rw [POVM.distribution_apply _ ω S hS, PVM.distribution_apply E ω S hS, PVM.toPOVM_apply]

/-! ## The finite-discrete case -/

/-- A `VectorMeasure`'s values distribute over a `Finset` sum of underlying vector measures —
elementary, via `Finset.sum_insert`/`add_apply`, but not already a Mathlib lemma in this exact
shape. -/
private lemma vectorMeasure_finsetSum_apply {X : Type*} [MeasurableSpace X] {ι : Type*}
    (s : Finset ι) (v : ι → VectorMeasure X A) (S : Set X) :
    (∑ i ∈ s, v i) S = ∑ i ∈ s, v i S := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, add_apply, ih]

/-- **The finite-discrete case recovers a `POVM`**: `FinitePOVM.lean`'s `FinitePOVM A X` (a family of
effects resolving the identity), viewed on the discrete measurable space on `X` (every set
measurable, so the "resolves the identity" condition transports directly to `POVM.univ'`), is a
finite sum of Dirac vector measures `∑ x, dirac x (M.effect x)` — the textbook correspondence
between "one effect per outcome" and "a POVM on the discrete σ-algebra". -/
def FinitePOVM.toPOVM {X : Type*} [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    (M : FinitePOVM A X) : POVM X A where
  toVectorMeasure := ∑ x : X, VectorMeasure.dirac x (M.effect x : A)
  nonneg' S := by
    show (0 : A) ≤ (∑ x : X, VectorMeasure.dirac x (M.effect x : A)) S
    rw [vectorMeasure_finsetSum_apply]
    refine Finset.sum_nonneg fun x _ => ?_
    by_cases hx : x ∈ S
    · rw [VectorMeasure.dirac_apply_of_mem MeasurableSet.of_discrete hx]
      exact (M.effect x).2.1
    · rw [VectorMeasure.dirac_apply_of_notMem hx]
  univ' := by
    show (∑ x : X, VectorMeasure.dirac x (M.effect x : A)) univ = 1
    rw [vectorMeasure_finsetSum_apply]
    simp_rw [VectorMeasure.dirac_apply_of_mem MeasurableSet.of_discrete (Set.mem_univ _)]
    exact M.sum_effect

end OperatorAlgebra
