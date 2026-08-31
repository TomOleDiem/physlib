/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.NormalState
public import Mathlib.Analysis.CStarAlgebra.Projection
public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!

# General projection-valued measures

This file sets up a *projection-valued measure* (`PVM`) valued in an abstract `OperatorAlgebra M`,
generalizing the concrete `SpectralMeasure` on `H →L[ℂ] H`
(`PhyslibAlpha.Unbounded.QuantumMechanics.Operators.SpectralTheory.SpectralMeasure`) away from any fixed
Hilbert-space representation. `PVM` itself needs only `OperatorAlgebra M` (a PVM is a purely
algebraic/measure-theoretic gadget, no predual required); measurement *statistics* against a state
(`PVM.distribution`, below) additionally need `M` to be a genuine `WStarAlgebra`, since only
*normal* states (`WStarAlgebra.lean`'s `NormalState`, defined via the weak-⋆ topology) give
countably-additive — as opposed to merely finitely-additive — measurement statistics.

## History

Normal states are owned by `States/NormalState.lean`; this module owns the PVM structure and its
state-evaluation statistics.

## Key results

- `Projection M` : a star projection in `M`.
- `PVM X M` : a normalized, `Projection M`-valued vector measure on a measurable space `X`.
- `PVM.distribution` : the pushforward of a PVM along a normal state, `S ↦ ω (E S)`, as the scalar
  probability measure `μ_{ω,E}`.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra Function
open MeasureTheory Set

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-! ## Projections -/

/-- A star projection in `A`: a self-adjoint idempotent, the algebraic model of a single
measurement outcome's effect being sharp (`0`/`1`-valued). -/
abbrev Projection (A : Type*) [OperatorAlgebra A] := {p : A // IsStarProjection p}

namespace Projection

instance : CoeTC (Projection A) A := ⟨Subtype.val⟩

/-- A star projection is always positive: its spectrum lies in `{0,1} ⊆ [0,∞)`. -/
lemma nonneg_of_isStarProjection {q : A} (hq : IsStarProjection q) : 0 ≤ q := by
  obtain ⟨hspec, hsa⟩ := isStarProjection_iff_spectrum_subset_and_isSelfAdjoint.mp hq
  rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) q hsa]
  intro x hx
  rcases hspec hx with h0 | h1 <;> simp_all

/-- Every projection is an effect: `0 ≤ p ≤ 1`. `p` is positive directly
(`nonneg_of_isStarProjection`); `p ≤ 1` follows the same way applied to the complementary
projection `1 - p` (`IsStarProjection.one_sub`), via `0 ≤ 1 - p ↔ p ≤ 1`. -/
lemma mem_effect (p : Projection A) : 0 ≤ (p : A) ∧ (p : A) ≤ 1 := by
  refine ⟨nonneg_of_isStarProjection p.2, ?_⟩
  rw [← sub_nonneg]
  exact nonneg_of_isStarProjection p.2.one_sub

end Projection

/-! ## Projection-valued measures -/

/-- Every `NormalState`/`OperatorAlgebra` normed additive group is torsion-free: `n • a = 0` with
`n ≠ 0` forces `a = 0`, since `A` is a `ℂ`-vector space. Needed for `VectorMeasure`'s `HasSum` API
to interact well with `IsStarProjection`, mirroring the analogous instance for `H →L[ℂ] H` in
`SpectralMeasure.lean`. -/
instance (priority := 100) : IsAddTorsionFree A where
  nsmul_right_injective n hn := by
    refine Function.HasLeftInverse.injective ⟨fun x ↦ (n : ℂ)⁻¹ • x, fun x ↦ ?_⟩
    simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_ne_zero (R := ℂ), hn]

/-- A *projection-valued measure* (PVM) on a measurable space `X`, valued in `A`: a σ-additive
function `Set X → A` sending every set to a star projection, the empty set (and non-measurable
sets) to `0`, and `univ` to `1`.

This generalizes `SpectralMeasure X (H →L[ℂ] H)` away from any fixed Hilbert-space
representation `H`: an `AffiliatedObservable`'s spectral measure lives here, valued directly in the
abstract algebra `A` it is affiliated with, rather than in some ambient `B(H)`. -/
structure PVM (X : Type*) [MeasurableSpace X] (A : Type*) [OperatorAlgebra A]
    extends VectorMeasure X A where
  isStarProjection' : ∀ S, IsStarProjection (measureOf' S)
  univ' : measureOf' univ = 1

namespace PVM

open scoped Classical

variable {X : Type*} [MeasurableSpace X] (E : PVM X A)

attribute [coe] toVectorMeasure

instance instCoeVectorMeasure : Coe (PVM X A) (VectorMeasure X A) := ⟨toVectorMeasure⟩

instance instCoeFun : CoeFun (PVM X A) fun _ => Set X → A := ⟨fun E => ⇑E.toVectorMeasure⟩

@[ext]
theorem ext {E F : PVM X A}
    (h : ∀ S : Set X, MeasurableSet S → E S = F S) : E = F := by
  cases E with
  | mk E hE uE =>
    cases F with
    | mk F hF uF =>
      congr
      exact VectorMeasure.ext h

/-- The point-mass PVM at `x`.  This is useful for degenerate spectral data and for testing
the abstract PVM API without invoking a functional-calculus theorem. -/
def point (x : X) : PVM X A where
  toVectorMeasure := VectorMeasure.dirac x (1 : A)
  isStarProjection' S := by
    classical
    change IsStarProjection ((VectorMeasure.dirac x (1 : A)) S)
    by_cases hS : MeasurableSet S
    · by_cases hx : x ∈ S
      · rw [VectorMeasure.dirac_apply_of_mem hS hx]
        exact IsStarProjection.one A
      · rw [VectorMeasure.dirac_apply_of_notMem hx]
        exact IsStarProjection.zero A
    · rw [VectorMeasure.not_measurable _ hS]
      exact IsStarProjection.zero A
  univ' := by
    change (VectorMeasure.dirac x (1 : A)) Set.univ = 1
    rw [VectorMeasure.dirac_apply_of_mem MeasurableSet.univ (mem_univ x)]

@[simp]
lemma point_apply {A : Type*} [OperatorAlgebra A] (x : X) (S : Set X) (hS : MeasurableSet S) :
    point x S = if x ∈ S then (1 : A) else 0 := by
  classical
  change (VectorMeasure.dirac x (1 : A)) S = _
  by_cases hx : x ∈ S
  · simp [VectorMeasure.dirac_apply_of_mem hS hx, hx]
  · simp [VectorMeasure.dirac_apply_of_notMem hx, hx]

/-- The projection associated to a measurable set. -/
def spectralProjection (S : Set X) : Projection A := ⟨E S, E.isStarProjection' S⟩

lemma isStarProjection (S : Set X) : IsStarProjection (E S) := E.isStarProjection' S

@[simp]
lemma univ : E univ = 1 := E.univ'

@[simp]
lemma apply_eq_zero_of_not_measurableSet {S : Set X} (hS : ¬MeasurableSet S) : E S = 0 :=
  E.not_measurable' hS

/-! ### Composition -/

@[simp]
lemma comp_self (S : Set X) : E S * E S = E S := (E.isStarProjection S).isIdempotentElem

lemma comp_of_disjoint {S T : Set X} (h : Disjoint S T) (hS : MeasurableSet S)
    (hT : MeasurableSet T) : E S * E T = 0 := by
  have hunion : (E (S ∪ T) : A) = E S + E T := E.of_union h hS hT
  have hp : (E S : A) * E (S ∪ T) = E S := by
    refine (IsStarProjection.sub_iff_mul_eq_left (E.isStarProjection S)
      (E.isStarProjection (S ∪ T))).mp ?_
    rw [hunion]
    simpa using E.isStarProjection T
  rw [hunion, mul_add, E.comp_self S] at hp
  have h0 : (E S : A) + E S * E T = E S + 0 := by rw [add_zero]; exact hp
  exact add_left_cancel h0

/-- `E S * E T = E (S ∩ T)`: a PVM's values compose by intersecting their sets. -/
lemma comp_eq_of_inter {S T : Set X} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    E S * E T = E (S ∩ T) := by
  nth_rw 1 [← inter_union_sdiff T S, ← inter_union_sdiff S T]
  simp only [E.of_union, hS.inter hT, hT.inter hS, hS.diff hT, hT.diff hS,
    disjoint_sdiff_inter.symm, add_mul, mul_add]
  rw [inter_comm T S, E.comp_of_disjoint disjoint_sdiff_inter (hS.diff hT) (hS.inter hT),
    inter_comm S T, E.comp_of_disjoint disjoint_sdiff_inter.symm (hT.inter hS) (hT.diff hS)]
  simp [E.comp_of_disjoint disjoint_sdiff_sdiff (hS.diff hT) (hT.diff hS)]

lemma commute (S T : Set X) : Commute (E S) (E T) := by
  by_cases hST : MeasurableSet S ∧ MeasurableSet T
  · simp [commute_iff_eq, comp_eq_of_inter, hST, inter_comm]
  · rcases not_and_or.mp hST with hS | hT <;> simp [*]

/-! ### Pushforward -/

/-- **The pushforward of a PVM along a measurable map.** `(E.map f) S = E (f⁻¹' S)`, for measurable
`S`. Built directly from Mathlib's `MeasureTheory.VectorMeasure.map` (needs only `Measurable f`,
no continuity/boundedness), this is the general engine behind the "measurable functional calculus"
promised in `FunctionalCalculus.lean`: pushing a `PVM ℝ A` forward along any measurable
`f : ℝ → ℂ` gives `f`'s spectral measure directly, with no analytic construction needed — the
whole content is Mathlib's vector-measure pushforward, plus checking `IsStarProjection`/`univ'`
transport (both immediate, since `f ⁻¹' univ = univ` and every value of the underlying PVM is
already a star projection or `0`). -/
def map {Y : Type*} [MeasurableSpace Y] (f : X → Y) (hf : Measurable f) : PVM Y A where
  toVectorMeasure := E.toVectorMeasure.map f
  isStarProjection' S := by
    by_cases hS : MeasurableSet S
    · show IsStarProjection ((E.toVectorMeasure.map f) S)
      rw [VectorMeasure.map_apply _ hf hS]
      exact E.isStarProjection _
    · show IsStarProjection ((E.toVectorMeasure.map f) S)
      rw [show ((E.toVectorMeasure.map f) S) = 0 from (E.toVectorMeasure.map f).not_measurable' hS]
      exact IsStarProjection.zero A
  univ' := by
    show (E.toVectorMeasure.map f) Set.univ = 1
    rw [VectorMeasure.map_apply _ hf MeasurableSet.univ, Set.preimage_univ]
    exact E.univ'

@[simp]
lemma map_apply {Y : Type*} [MeasurableSpace Y] {f : X → Y} (hf : Measurable f) {S : Set Y}
    (hS : MeasurableSet S) : (E.map f hf) S = E (f ⁻¹' S) :=
  VectorMeasure.map_apply _ hf hS

lemma map_map_apply {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    {f : X → Y} {g : Y → Z} (hf : Measurable f) (hg : Measurable g)
    {S : Set Z} (hS : MeasurableSet S) :
    ((E.map f hf).map g hg) S = E ((g ∘ f) ⁻¹' S) := by
  rw [(E.map f hf).map_apply hg hS, E.map_apply hf (hg hS)]
  rfl

theorem map_map {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z]
    {f : X → Y} {g : Y → Z} (hf : Measurable f) (hg : Measurable g) :
    (E.map f hf).map g hg = E.map (g ∘ f) (hg.comp hf) := by
  apply PVM.ext
  intro S hS
  rw [E.map_map_apply hf hg hS, E.map_apply (hg.comp hf) hS]

/-! ### Measurement statistics: `μ_{ω,E}(S) = ω(E(S))` -/

/-- The scalar probability measure `μ_{ω,E}(S) = ω (E S)` induced on `X` by evaluating the PVM
`E` against a normal state `ω`. The construction goes through `MeasureTheory.Measure.ofMeasurable`
(a countably-additive nonnegative real-valued set function on the measurable sets, extended by
zero elsewhere): `ω (E S) ∈ [0,1]` since `E S` is an effect (`Projection.mem_effect`), and
countable additivity follows from `ω`'s continuity (automatic for positive functionals on a
C⋆-algebra) applied to the `HasSum` witnessed by the `VectorMeasure` structure of `E`. -/
def distribution {A : Type*} [WStarAlgebra A] {X : Type*} [MeasurableSpace X] (E : PVM X A)
    (ω : NormalState A) : ProbabilityMeasure X := by
  let m : ∀ S : Set X, MeasurableSet S → ENNReal :=
    fun S _ => ENNReal.ofReal (ω (E S)).re
  have hm_nonneg : ∀ S : Set X, MeasurableSet S → 0 ≤ (ω (E S)).re := by
    intro S hS
    have hp : 0 ≤ (E S : A) := (Projection.mem_effect (E.spectralProjection S)).1
    exact (Complex.le_def.mp (ω.toState.toPositiveLinearMap.map_nonneg hp)).1
  have hm_empty : m ∅ MeasurableSet.empty = 0 := by
    simp [m]
  have hm_iUnion : ∀ ⦃f : ℕ → Set X⦄ (h : ∀ i, MeasurableSet (f i)),
      Pairwise (Disjoint on f) → m (⋃ i, f i) (MeasurableSet.iUnion h) =
        ∑' i, m (f i) (h i) := by
    intro f hf hdisj
    have hs : HasSum (fun i => E (f i)) (E (⋃ i, f i)) := E.toVectorMeasure.m_iUnion hf hdisj
    have hω : HasSum (fun i => ω (E (f i))) (ω (E (⋃ i, f i))) :=
      hs.map ω.toState.toPositiveLinearMap ω.continuous
    have hre : HasSum (fun i => (ω (E (f i))).re) (ω (E (⋃ i, f i))).re := by
      exact hω.map Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous
    dsimp [m]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => hm_nonneg _ (hf i)) hre.summable]
    exact congrArg ENNReal.ofReal hre.tsum_eq.symm
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

/-- The defining property of `distribution`: `μ_{ω,E}(S) = ω(E(S))` for measurable `S`. Stated
separately from the construction of `distribution` itself so downstream files can
depend on this equation as the actual interface, independent of how `distribution` is eventually
built. -/
lemma distribution_apply {A : Type*} [WStarAlgebra A] {X : Type*} [MeasurableSpace X]
    (E : PVM X A) (ω : NormalState A) (S : Set X) (hS : MeasurableSet S) :
    (E.distribution ω : Measure X) S = ENNReal.ofReal (ω (E S)).re := by
  simp only [distribution, ProbabilityMeasure.coe_mk, Measure.ofMeasurable_apply _ hS]

/- The distribution construction commutes with measurable changes of spectral variable.  This is
the scalar-statistics counterpart of `PVM.map_map`: the law of `f(T)` is the pushforward of the
law of `T`. -/
theorem distribution_map {A : Type*} [WStarAlgebra A] {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (E : PVM X A) (ω : NormalState A)
    (f : X → Y) (hf : Measurable f) :
    ((E.map f hf).distribution ω : Measure Y) =
      Measure.map f (E.distribution ω : Measure X) := by
  apply Measure.ext
  intro S hS
  rw [distribution_apply (E.map f hf) ω S hS]
  rw [Measure.map_apply hf hS]
  rw [distribution_apply E ω (f ⁻¹' S) (hf hS)]
  rw [E.map_apply hf hS]

end PVM

end OperatorAlgebra
