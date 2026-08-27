/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalAffiliated

/-!
# The weak-⋆ bounded Borel functional calculus

`NormalAffiliated.lean` states `NormalBorelFunctionalCalculus` as a *certificate*: a bundle of
algebra laws a bounded Borel calculus for a `NormalPVM` would have, assumed rather than built. This
file supplies the missing construction: `NormalBorelFunctionalCalculus.ofNormalPVM` proves that
every `NormalPVM` (in particular, by forgetting to `NormalPVM`, every `PredualPVM`) already carries
such a calculus, with no extra hypothesis.

## The construction

The key observation is that `FunctionalCalculus.lean`'s construction of the bounded Borel calculus
for a norm-valued `PVM` never actually uses countable additivity: it uses only

* `IsStarProjection` of each spectral value,
* *finite* additivity over disjoint measurable pairs (`PVM.of_union`), and
* completeness of the norm topology on `A` (`A` is a C⋆-algebra).

`NormalPVM` has exactly the first two ingredients as primitive fields (`isStarProjection'`,
`of_union'`) — its extra countable-additivity axiom (`m_iUnion'`) is only tested after every normal
state, but the construction below never invokes it. So the same three-step recipe — integrate
simple functions by finite orthogonal sums, bound `‖∑ᵢ cᵢPᵢ‖ ≤ sup ‖cᵢ‖` from the C⋆-identity and
orthogonality alone, and pass to the norm limit along a uniformly convergent simple-function
approximation — builds a genuine element of `A` for every bounded measurable `f`, directly from
`NormalPVM`, with no weak-⋆/predual apparatus needed for *existence*. `PredualPVM` enters only
through `NormalBorelFunctionalCalculus.ofPredualPVM`, the named contract this file exports, which is
literally `ofNormalPVM` applied after forgetting the extra predual-additivity witness.

## Main results

- `NormalPVM.simpleIntegral`, `NormalPVM.boundedFC` : the finite and norm-limit spectral integrals
  of a bounded measurable `f : X → ℂ` against a `NormalPVM X A`.
- `NormalBorelFunctionalCalculus.ofNormalPVM` : the constructed calculus certificate for an
  arbitrary `NormalPVM`.
- `NormalBorelFunctionalCalculus.ofPredualPVM` : the same, specialized to a `PredualPVM` — the named
  constructor `general-theory-roadmap.md`'s P3 package asks for.
- `NormalBorelFunctionalCalculus.ofNormalPVM_ofPVM_boundedFC_eq` : compatibility with the existing
  norm-valued calculus — `ofNormalPVM (NormalPVM.ofPVM E)` and `NormalBorelFunctionalCalculus.ofPVM
  E` (`NormalAffiliated.lean`) agree on every bounded measurable function, not merely on the same
  type of certificate.
- `NormalBorelFunctionalCalculus.eq_of_eq_on_simpleFunctions` : certificate-level uniqueness from
  agreement on bounded simple functions, by uniform approximation and the contractive estimate.
- `NormalBorelFunctionalCalculus.boundedFC_eq_of_same_normalPVM` : the preceding uniqueness is
  unconditional for any two certificates over the same `NormalPVM`.

## What remains open

The certificate now exposes `NormalBorelFunctionalCalculus.norm_boundedFC_le`: its algebra laws
alone imply the C⋆-norm estimate for every bounded multiplier. This is the continuity estimate
needed to compare two certificates through a common sequence of uniformly convergent simple
functions. `boundedFC_of_simpleFunc_eq_simpleIntegral` derives the required simple-function
agreement from the indicator field, and `boundedFC_eq_of_same_normalPVM` packages the resulting
unconditional uniqueness. The concrete compatibility theorem below remains the instance used by
the representation layer.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra Topology
open MeasureTheory Set

namespace OperatorAlgebra

/-! ## Auxiliary lemmas: finite orthogonal sums of projections

Reproduced from `FunctionalCalculus.lean`'s `Aux` section (that file's copies are `private`, hence
unavailable here): these facts are about finite sums of orthogonal star projections in a bare
`OperatorAlgebra A`, and do not mention any particular PVM, so they are exactly as usable for
`NormalPVM` as they were for the norm-valued `PVM`. -/

section Aux

variable {A : Type*} [OperatorAlgebra A]

private lemma isStarProjection_finsetSum' {ι : Type*} [DecidableEq ι] (s : Finset ι) (P : ι → A)
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

private lemma norm_sum_smul_le' {ι : Type*} [DecidableEq ι] (s : Finset ι) (P : ι → A) (c : ι → ℂ)
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
  have hsum_proj : IsStarProjection (∑ i ∈ s, P i) := isStarProjection_finsetSum' s P hP horth
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

/-! ## Uniform simple approximation on an arbitrary measurable space

Generalizes `AffiliatedObservable.exists_uniform_simple_approx` (`FunctionalCalculus.lean`) from
`X = ℝ` to an arbitrary measurable `X`: the compactness argument only ever uses that the *range* of
`f` is a bounded subset of `ℂ`, never any structure on the domain. -/

lemma exists_uniform_simpleFunc_approx {X : Type*} [MeasurableSpace X] {f : X → ℂ}
    (hf : Measurable f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    ∃ s : ℕ → SimpleFunc X ℂ,
      (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) ∧
      ∃ C, ∀ n x, ‖s n x‖ ≤ C := by
  classical
  rcases hbdd with ⟨C, hC⟩
  rcases isEmpty_or_nonempty X with hX | hX
  · -- Vacuous case: `X` has no points, so every claim about `∀ x` holds trivially.
    refine ⟨fun _ => SimpleFunc.const X 0, fun ε _ => ⟨0, fun n _ x => (hX.false x).elim⟩,
      0, fun n x => (hX.false x).elim⟩
  · have hC0 : 0 ≤ C := (norm_nonneg (f (Classical.arbitrary X))).trans (hC (Classical.arbitrary X))
    let K : Set ℂ := Metric.closedBall 0 C
    have hKcompact : IsCompact K := isCompact_closedBall 0 C
    letI : TopologicalSpace.SeparableSpace K := hKcompact.isSeparable.separableSpace
    have hK0 : (0 : ℂ) ∈ K := by simp [K, hC0]
    letI : Nonempty K := ⟨⟨0, hK0⟩⟩
    let e : ℕ → ℂ := fun k => Nat.casesOn k 0 ((↑) ∘ TopologicalSpace.denseSeq K)
    let s : ℕ → SimpleFunc X ℂ := fun n => SimpleFunc.approxOn f hf K 0 hK0 n
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
      have hnearest : edist (SimpleFunc.nearestPt e n (f x)) (f x) ≤ edist (e k) (f x) :=
        SimpleFunc.edist_nearestPt_le e (f x) hkn
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

/-! ## The finite spectral integral of a `NormalPVM`

Mirrors `AffiliatedObservable.simpleIntegral`, generalized from `X = ℝ` to an arbitrary measurable
space and from a norm-valued `PVM` to a `NormalPVM`. Every law below uses only `isStarProjection'`
and the *finite* additivity `of_union'` already carried by `NormalPVM` — never `m_iUnion'`. -/

namespace NormalPVM

variable {X : Type*} [MeasurableSpace X] {A : Type*} [WStarAlgebra A] (E : NormalPVM X A)

/-- The finite spectral integral of a complex-valued measurable simple function against a
`NormalPVM`. -/
def simpleIntegral (f : SimpleFunc X ℂ) : A :=
  ∑ z ∈ f.range, z • (E (f ⁻¹' {z}) : A)

/-- The continuous-linear-map-valued set function associated with a `NormalPVM`, letting the
standard finite-simple-function integration API (`SimpleFunc.setToSimpleFunc`) operate on it. -/
def spectralCLM (S : Set X) : ℂ →L[ℝ] A :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight (E S : A)).restrictScalars ℝ

lemma spectralCLM_apply (S : Set X) (z : ℂ) : E.spectralCLM S z = z • (E S : A) := rfl

private lemma spectralCLM_finMeasAdditive : FinMeasAdditive (0 : Measure X) E.spectralCLM := by
  intro S U hS hU _ _ hdisj
  ext z
  rw [ContinuousLinearMap.add_apply]
  simp only [spectralCLM_apply]
  rw [E.of_union hdisj hS hU, smul_add]

lemma simpleIntegral_eq_setToSimpleFunc (f : SimpleFunc X ℂ) :
    E.simpleIntegral f = f.setToSimpleFunc E.spectralCLM := by
  simp only [SimpleFunc.setToSimpleFunc, spectralCLM_apply, simpleIntegral]

private lemma simpleFunc_integrable_zero (_E : NormalPVM X A) (f : SimpleFunc X ℂ) :
    Integrable f (0 : Measure X) :=
  integrable_zero_measure

private lemma simpleIntegral_add_aux (f g : SimpleFunc X ℂ) :
    E.simpleIntegral (f + g) = E.simpleIntegral f + E.simpleIntegral g := by
  rw [E.simpleIntegral_eq_setToSimpleFunc (f + g), E.simpleIntegral_eq_setToSimpleFunc f,
    E.simpleIntegral_eq_setToSimpleFunc g]
  exact SimpleFunc.setToSimpleFunc_add E.spectralCLM E.spectralCLM_finMeasAdditive
    (E.simpleFunc_integrable_zero f) (E.simpleFunc_integrable_zero g)

lemma simpleIntegral_add (f g : SimpleFunc X ℂ) :
    E.simpleIntegral (f + g) = E.simpleIntegral f + E.simpleIntegral g :=
  simpleIntegral_add_aux E f g

private lemma simpleIntegral_neg_aux (f : SimpleFunc X ℂ) :
    E.simpleIntegral (-f) = -E.simpleIntegral f := by
  rw [E.simpleIntegral_eq_setToSimpleFunc (-f), E.simpleIntegral_eq_setToSimpleFunc f]
  exact SimpleFunc.setToSimpleFunc_neg E.spectralCLM E.spectralCLM_finMeasAdditive
    (E.simpleFunc_integrable_zero f)

lemma simpleIntegral_neg (f : SimpleFunc X ℂ) :
    E.simpleIntegral (-f) = -E.simpleIntegral f :=
  simpleIntegral_neg_aux E f

lemma simpleIntegral_sub (f g : SimpleFunc X ℂ) :
    E.simpleIntegral (f - g) = E.simpleIntegral f - E.simpleIntegral g := by
  calc
    E.simpleIntegral (f - g) = E.simpleIntegral (f + -g) := by rw [sub_eq_add_neg]
    _ = E.simpleIntegral f + E.simpleIntegral (-g) := E.simpleIntegral_add f (-g)
    _ = E.simpleIntegral f + -E.simpleIntegral g := by rw [E.simpleIntegral_neg]
    _ = E.simpleIntegral f - E.simpleIntegral g := by rw [sub_eq_add_neg]

lemma simpleIntegral_norm_le (f : SimpleFunc X ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hCf : ∀ z ∈ f.range, ‖z‖ ≤ C) :
    ‖E.simpleIntegral f‖ ≤ C := by
  apply norm_sum_smul_le' f.range
    (fun z ↦ (E (f ⁻¹' {z}) : A))
    (fun z ↦ z) C hC
  · intro z _
    exact E.isStarProjection _
  · intro z _ w _ hzw
    apply E.comp_of_disjoint
    · refine Set.disjoint_left.2 ?_
      intro a ha hb
      have haz : f a = z := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using ha
      have haw : f a = w := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hb
      exact hzw (haz.symm.trans haw)
    · exact f.measurableSet_fiber _
    · exact f.measurableSet_fiber _
  · intro z hz _
    exact hCf z hz

lemma simpleIntegral_diff_norm_le (f g : SimpleFunc X ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hfg : ∀ x, ‖f x - g x‖ ≤ C) :
    ‖E.simpleIntegral f - E.simpleIntegral g‖ ≤ C := by
  rw [← E.simpleIntegral_sub]
  apply E.simpleIntegral_norm_le (f - g) hC
  exact fun z hz => by
    rcases SimpleFunc.mem_range.1 hz with ⟨x, rfl⟩
    simpa only [SimpleFunc.sub_apply] using hfg x

lemma simpleIntegral_star (f : SimpleFunc X ℂ) :
    E.simpleIntegral (star f) = star (E.simpleIntegral f) := by
  classical
  simp only [simpleIntegral, star_sum]
  refine Finset.sum_bij (fun z _ => star z) ?_ ?_ ?_ ?_
  · intro z hz
    rcases SimpleFunc.mem_range.1 hz with ⟨x, hx⟩
    apply SimpleFunc.mem_range.2
    refine ⟨x, ?_⟩
    change f x = star z
    have hx' := congrArg star hx
    change star (star (f x)) = star z at hx'
    simpa using hx'
  · intro z₁ _ z₂ _ h
    exact star_injective h
  · intro z hz
    rcases SimpleFunc.mem_range.1 hz with ⟨x, hx⟩
    refine ⟨star z, ?_, ?_⟩
    · apply SimpleFunc.mem_range.2
      refine ⟨x, ?_⟩
      change star (f x) = star z
      exact congrArg star hx
    · simp
  · intro z _
    have hfiber : (⇑(star f) : X → ℂ) ⁻¹' {z} = (⇑f : X → ℂ) ⁻¹' {star z} := by
      ext x
      change star (f x) = z ↔ f x = star z
      constructor
      · intro h
        simpa using congrArg star h
      · intro h
        exact congrArg star h |>.trans (star_star z)
    rw [hfiber, star_smul, star_star]
    simp only [(E.isStarProjection _).isSelfAdjoint.star_eq]

lemma simpleIntegral_mul (f g : SimpleFunc X ℂ) :
    E.simpleIntegral (f * g) = E.simpleIntegral f * E.simpleIntegral g := by
  let p : SimpleFunc X (ℂ × ℂ) := f.pair g
  have hf : Integrable f (0 : Measure X) := E.simpleFunc_integrable_zero f
  have hg : Integrable g (0 : Measure X) := E.simpleFunc_integrable_zero g
  have hp : Integrable p (0 : Measure X) := SimpleFunc.integrable_pair hf hg
  have hadd := E.spectralCLM_finMeasAdditive
  have hfst : E.simpleIntegral f =
      ∑ q ∈ p.range, q.1 • (E (p ⁻¹' {q}) : A) := by
    rw [E.simpleIntegral_eq_setToSimpleFunc f, ← SimpleFunc.map_fst_pair f g]
    rw [SimpleFunc.map_setToSimpleFunc E.spectralCLM hadd hp Prod.fst_zero]
    simp only [spectralCLM_apply]
  have hsnd : E.simpleIntegral g =
      ∑ q ∈ p.range, q.2 • (E (p ⁻¹' {q}) : A) := by
    rw [E.simpleIntegral_eq_setToSimpleFunc g, ← SimpleFunc.map_snd_pair f g]
    rw [SimpleFunc.map_setToSimpleFunc E.spectralCLM hadd hp Prod.snd_zero]
    simp only [spectralCLM_apply]
  have hmul : E.simpleIntegral (f * g) =
      ∑ q ∈ p.range, (q.1 * q.2) • (E (p ⁻¹' {q}) : A) := by
    rw [E.simpleIntegral_eq_setToSimpleFunc (f * g), SimpleFunc.mul_eq_map₂]
    rw [SimpleFunc.map_setToSimpleFunc E.spectralCLM hadd hp (by simp)]
    simp only [spectralCLM_apply]
  rw [hfst, hsnd, hmul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.sum_eq_single q]
  · rw [smul_mul_smul_comm, E.comp_self]
  · intro r hr hneq
    rw [smul_mul_smul_comm]
    have hdisj : Disjoint (p ⁻¹' {q}) (p ⁻¹' {r}) := by
      refine Set.disjoint_left.2 ?_
      intro x hxq hxr
      have hxq' : p x = q := by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hxq
      have hxr' : p x = r := by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hxr
      exact hneq (hxr'.symm.trans hxq')
    rw [E.comp_of_disjoint hdisj (p.measurableSet_fiber q)
      (p.measurableSet_fiber r), smul_zero]
  · intro hq'
    exact (hq' hq).elim

lemma simpleIntegral_const (c : ℂ) :
    E.simpleIntegral (SimpleFunc.const X c) = c • (1 : A) := by
  classical
  simp only [simpleIntegral]
  rcases isEmpty_or_nonempty X with hX | hX
  · have huniv : (Set.univ : Set X) = ∅ := by ext x; exact (hX.false x).elim
    have hone : (1 : A) = 0 := by rw [← E.univ, huniv, E.empty]
    simp [SimpleFunc.range_eq_empty_of_isEmpty, hone]
  · simp only [SimpleFunc.range_const, Finset.sum_singleton]
    rw [show (⇑(SimpleFunc.const X c) : X → ℂ) ⁻¹' ({c} : Set ℂ) = Set.univ by ext x; simp,
      E.univ]

/-! ## The bounded Borel functional calculus of a `NormalPVM`

Exactly the `AffiliatedObservable.boundedFC` recipe of `FunctionalCalculus.lean`, transported to
an arbitrary measurable space `X` and to `NormalPVM` in place of the norm-valued `PVM`: a norm
limit of the finite spectral sums `simpleIntegral` along a uniformly convergent simple-function
approximation.  Every ingredient used below (`simpleIntegral_diff_norm_le`,
`exists_uniform_simpleFunc_approx`, completeness of `A`) is already available for `NormalPVM`, so
this construction needs no extra hypothesis on `E`. -/

lemma simpleIntegral_cauchySeq {f : X → ℂ} {s : ℕ → SimpleFunc X ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) :
    CauchySeq (fun n => E.simpleIntegral (s n)) := by
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
  have hbound : ‖E.simpleIntegral (s m) - E.simpleIntegral (s n)‖ ≤ ε / 2 :=
    E.simpleIntegral_diff_norm_le (s m) (s n) (by linarith) hmn
  have hbound' : dist (E.simpleIntegral (s m)) (E.simpleIntegral (s n)) ≤ ε / 2 := by
    simpa only [dist_eq_norm] using hbound
  exact lt_of_le_of_lt hbound' (by linarith)

/-- The bounded Borel functional calculus of a `NormalPVM`, constructed as a norm limit of finite
spectral sums.  This is the existence part of P3: `A`'s C⋆-norm completeness turns the Cauchy
sequence `simpleIntegral (s n)` into a genuine element of `A`. -/
def boundedFC (f : X → ℂ) (hf : Measurable f)
    (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) : A := by
  classical
  let s : ℕ → SimpleFunc X ℂ := Classical.choose (exists_uniform_simpleFunc_approx hf hbdd)
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε :=
    (Classical.choose_spec (exists_uniform_simpleFunc_approx hf hbdd)).1
  have _hCauchy : CauchySeq (fun n => E.simpleIntegral (s n)) :=
    E.simpleIntegral_cauchySeq hs
  exact Filter.atTop.limUnder (fun n => E.simpleIntegral (s n))

lemma boundedFC_eq_limUnder {f : X → ℂ} (hf : Measurable f)
    (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) {s : ℕ → SimpleFunc X ℂ}
    (hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε) :
    E.boundedFC f hf hbdd = Filter.atTop.limUnder (fun n => E.simpleIntegral (s n)) := by
  classical
  let s₀ : ℕ → SimpleFunc X ℂ := Classical.choose (exists_uniform_simpleFunc_approx hf hbdd)
  have hs₀ : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s₀ n x - f x‖ < ε :=
    (Classical.choose_spec (exists_uniform_simpleFunc_approx hf hbdd)).1
  have hc₀ : CauchySeq (fun n => E.simpleIntegral (s₀ n)) := E.simpleIntegral_cauchySeq hs₀
  have hlim₀ : Filter.Tendsto (fun n => E.simpleIntegral (s₀ n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => E.simpleIntegral (s₀ n)))) :=
    hc₀.tendsto_limUnder
  have hdist : Filter.Tendsto (fun n => dist (E.simpleIntegral (s₀ n)) (E.simpleIntegral (s n)))
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
    have hbound := E.simpleIntegral_diff_norm_le (s₀ n) (s n) (by linarith) hpoint
    have hlt : ‖E.simpleIntegral (s₀ n) - E.simpleIntegral (s n)‖ < ε :=
      lt_of_le_of_lt hbound (by linarith)
    change dist (dist (E.simpleIntegral (s₀ n)) (E.simpleIntegral (s n))) 0 < ε
    rw [dist_zero_right]
    simpa [dist_eq_norm, Real.norm_of_nonneg (norm_nonneg
      (E.simpleIntegral (s₀ n) - E.simpleIntegral (s n)))] using hlt
  have hlim : Filter.Tendsto (fun n => E.simpleIntegral (s n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => E.simpleIntegral (s₀ n)))) :=
    hlim₀.congr_dist hdist
  have heq := hlim.limUnder_eq
  unfold boundedFC
  dsimp [s₀] at heq ⊢
  exact heq.symm

lemma boundedFC_congr {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∀ x, f x = g x) :
    E.boundedFC f hf hbf = E.boundedFC g hg hbg := by
  classical
  rcases exists_uniform_simpleFunc_approx hf hbf with ⟨s, hs, hsB⟩
  have hs' : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - g x‖ < ε := by
    intro ε hε
    rcases hs ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn x => ?_⟩
    rw [← hfg x]
    exact hN n hn x
  calc
    E.boundedFC f hf hbf = Filter.atTop.limUnder (fun n => E.simpleIntegral (s n)) :=
      E.boundedFC_eq_limUnder hf hbf hs
    _ = E.boundedFC g hg hbg := (E.boundedFC_eq_limUnder hg hbg hs').symm

lemma boundedFC_of_simpleFunc (f : SimpleFunc X ℂ) (hf : Measurable (fun x => f x))
    (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    E.boundedFC (fun x => f x) hf hbdd = E.simpleIntegral f := by
  have hlim : Filter.Tendsto (fun _ : ℕ => E.simpleIntegral f) Filter.atTop
      (nhds (E.simpleIntegral f)) := tendsto_const_nhds
  have happrox : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x, ‖f x - f x‖ < ε := by
    intro ε hε
    exact ⟨0, fun n hn x => by simpa using hε⟩
  rw [E.boundedFC_eq_limUnder hf hbdd happrox]
  exact hlim.limUnder_eq

lemma boundedFC_const (c : ℂ) :
    E.boundedFC (fun _ : X => c) (by fun_prop)
        (show ∃ C : ℝ, ∀ _ : X, ‖c‖ ≤ C from ⟨‖c‖, fun _ => le_rfl⟩) = c • (1 : A) := by
  let hbdd : ∃ C : ℝ, ∀ _ : X, ‖c‖ ≤ C := ⟨‖c‖, fun _ => le_rfl⟩
  have h := E.boundedFC_of_simpleFunc (SimpleFunc.const X c) (by fun_prop) hbdd
  rw [E.simpleIntegral_const] at h
  convert h using 1 <;> simp [SimpleFunc.const]

lemma boundedFC_add {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∃ C, ∀ x, ‖f x + g x‖ ≤ C) :
    E.boundedFC (f + g) (hf.add hg) hfg = E.boundedFC f hf hbf + E.boundedFC g hg hbg := by
  classical
  rcases exists_uniform_simpleFunc_approx hf hbf with ⟨sf, hsf, hsfB⟩
  rcases exists_uniform_simpleFunc_approx hg hbg with ⟨sg, hsg, hsgB⟩
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
  have hcf : CauchySeq (fun n => E.simpleIntegral (sf n)) := E.simpleIntegral_cauchySeq hsf
  have hcg : CauchySeq (fun n => E.simpleIntegral (sg n)) := E.simpleIntegral_cauchySeq hsg
  have hlf : Filter.Tendsto (fun n => E.simpleIntegral (sf n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => E.simpleIntegral (sf n)))) := hcf.tendsto_limUnder
  have hlg : Filter.Tendsto (fun n => E.simpleIntegral (sg n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => E.simpleIntegral (sg n)))) := hcg.tendsto_limUnder
  have hlsum := hlf.add hlg
  calc
    E.boundedFC (f + g) (hf.add hg) hfg =
        Filter.atTop.limUnder (fun n => E.simpleIntegral (sf n + sg n)) :=
      E.boundedFC_eq_limUnder (hf.add hg) hfg hsum
    _ = Filter.atTop.limUnder
        (fun n => E.simpleIntegral (sf n) + E.simpleIntegral (sg n)) := by
      congr 1
      funext n
      exact E.simpleIntegral_add (sf n) (sg n)
    _ = Filter.atTop.limUnder (fun n => E.simpleIntegral (sf n)) +
        Filter.atTop.limUnder (fun n => E.simpleIntegral (sg n)) := hlsum.limUnder_eq
    _ = E.boundedFC f hf hbf + E.boundedFC g hg hbg := by
      rw [← E.boundedFC_eq_limUnder hf hbf hsf, ← E.boundedFC_eq_limUnder hg hbg hsg]

lemma boundedFC_mul {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∃ C, ∀ x, ‖f x * g x‖ ≤ C) :
    E.boundedFC (f * g) (hf.mul hg) hfg = E.boundedFC f hf hbf * E.boundedFC g hg hbg := by
  classical
  rcases hbf with ⟨Cf, hCf⟩
  rcases hbg with ⟨Cg₀, hCg₀⟩
  have hCg0 : (0 : ℝ) ≤ max Cg₀ 0 := le_max_right _ _
  have hCg : ∀ x, ‖g x‖ ≤ max Cg₀ 0 := fun x => (hCg₀ x).trans (le_max_left _ _)
  set Cg : ℝ := max Cg₀ 0 with hCgdef
  let hbf' : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := ⟨Cf, hCf⟩
  let hbg' : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := ⟨Cg, hCg⟩
  rcases exists_uniform_simpleFunc_approx hf hbf' with ⟨sf, hsf, hsfB⟩
  rcases exists_uniform_simpleFunc_approx hg hbg' with ⟨sg, hsg, hsgB⟩
  rcases hsfB with ⟨Cs₀, hCs₀⟩
  have hCs0 : (0 : ℝ) ≤ max Cs₀ 0 := le_max_right _ _
  have hCs : ∀ n x, ‖sf n x‖ ≤ max Cs₀ 0 := fun n x => (hCs₀ n x).trans (le_max_left _ _)
  set Cs : ℝ := max Cs₀ 0 with hCsdef
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
      _ ≤ ‖sf n x‖ * ‖sg n x - g x‖ + ‖sf n x - f x‖ * ‖g x‖ := by
            calc
              _ ≤ ‖sf n x * (sg n x - g x)‖ + ‖(sf n x - f x) * g x‖ := norm_add_le _ _
              _ = _ := by rw [norm_mul, norm_mul]
      _ ≤ Cs * δ + δ * Cg := by
        exact add_le_add
          (mul_le_mul (hCs n x) (le_of_lt hsgerr) (norm_nonneg _) hCs0)
          (mul_le_mul (le_of_lt hsferr) (hCg x) (norm_nonneg _) hδ.le)
      _ < ε := by
        calc
          Cs * δ + δ * Cg = (Cs + Cg) * δ := by ring
          _ ≤ (Cs + Cg + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
          _ = ε / 2 := by dsimp [δ]; field_simp
          _ < ε := by linarith
  have hcf : CauchySeq (fun n => E.simpleIntegral (sf n)) := E.simpleIntegral_cauchySeq hsf
  have hcg : CauchySeq (fun n => E.simpleIntegral (sg n)) := E.simpleIntegral_cauchySeq hsg
  have hlf : Filter.Tendsto (fun n => E.simpleIntegral (sf n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => E.simpleIntegral (sf n)))) := hcf.tendsto_limUnder
  have hlg : Filter.Tendsto (fun n => E.simpleIntegral (sg n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => E.simpleIntegral (sg n)))) := hcg.tendsto_limUnder
  have hmul := hlf.mul hlg
  calc
    E.boundedFC (f * g) (hf.mul hg) hfg =
        Filter.atTop.limUnder (fun n => E.simpleIntegral (sf n * sg n)) :=
      E.boundedFC_eq_limUnder (hf.mul hg) hfg hprod
    _ = Filter.atTop.limUnder
        (fun n => E.simpleIntegral (sf n) * E.simpleIntegral (sg n)) := by
      congr 1
      funext n
      exact E.simpleIntegral_mul (sf n) (sg n)
    _ = Filter.atTop.limUnder (fun n => E.simpleIntegral (sf n)) *
        Filter.atTop.limUnder (fun n => E.simpleIntegral (sg n)) := hmul.limUnder_eq
    _ = E.boundedFC f hf hbf' * E.boundedFC g hg hbg' := by
      rw [← E.boundedFC_eq_limUnder hf hbf' hsf, ← E.boundedFC_eq_limUnder hg hbg' hsg]

lemma boundedFC_smul (c : ℂ) {f : X → ℂ} (hf : Measurable f)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hcf : ∃ C, ∀ x, ‖c * f x‖ ≤ C) :
    E.boundedFC (fun x => c * f x) (measurable_const.mul hf) hcf = c • E.boundedFC f hf hbf := by
  rcases hbf with ⟨C, hC⟩
  let hcf' : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := ⟨C, hC⟩
  have hmul := E.boundedFC_mul (f := fun _ : X => c) (g := f) (by fun_prop) hf
    (⟨‖c‖, fun _ => le_rfl⟩) hcf' hcf
  calc
    E.boundedFC (fun x => c * f x) (measurable_const.mul hf) hcf =
        E.boundedFC ((fun _ : X => c) * f) (by fun_prop) hcf := rfl
    _ = E.boundedFC (fun _ : X => c) (by fun_prop) (⟨‖c‖, fun _ => le_rfl⟩) *
        E.boundedFC f hf hcf' := hmul
    _ = c • E.boundedFC f hf hcf' := by
      rw [E.boundedFC_const]
      simp [smul_mul_assoc]

lemma boundedFC_neg {f : X → ℂ} (hf : Measurable f)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hneg : ∃ C, ∀ x, ‖-f x‖ ≤ C) :
    E.boundedFC (fun x => -f x) (by fun_prop) hneg = -E.boundedFC f hf hbf := by
  have h := E.boundedFC_smul (-1) hf hbf (by simpa using hneg)
  convert h using 1 <;> simp

lemma boundedFC_sub {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hbg : ∃ C, ∀ x, ‖g x‖ ≤ C)
    (hfg : ∃ C, ∀ x, ‖f x - g x‖ ≤ C) :
    E.boundedFC (f - g) (hf.sub hg) hfg = E.boundedFC f hf hbf - E.boundedFC g hg hbg := by
  rcases hbg with ⟨Cg, hCg⟩
  have hneg : ∃ C : ℝ, ∀ x, ‖-g x‖ ≤ C := ⟨Cg, fun x => by simpa using hCg x⟩
  have haddBound : ∃ C : ℝ, ∀ x, ‖f x + -g x‖ ≤ C := by simpa only [sub_eq_add_neg] using hfg
  have hgm : Measurable (fun x => -g x) := by fun_prop
  have hadd := E.boundedFC_add hf hgm hbf hneg haddBound
  have hnegFC := E.boundedFC_neg hg (⟨Cg, hCg⟩) hneg
  calc
    E.boundedFC (f - g) (hf.sub hg) hfg =
        E.boundedFC (f + fun x => -g x) (hf.add hgm) haddBound := by
      apply E.boundedFC_congr (hf.sub hg) (hf.add hgm) hfg haddBound
      intro x; rfl
    _ = E.boundedFC f hf hbf + E.boundedFC (fun x => -g x) hgm hneg := hadd
    _ = E.boundedFC f hf hbf - E.boundedFC g hg (⟨Cg, hCg⟩) := by rw [hnegFC, sub_eq_add_neg]

lemma boundedFC_star {f : X → ℂ} (hf : Measurable f)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hstar : ∃ C, ∀ x, ‖star (f x)‖ ≤ C) :
    E.boundedFC (fun x => star (f x)) (continuous_star.measurable.comp hf) hstar =
      star (E.boundedFC f hf hbf) := by
  classical
  rcases exists_uniform_simpleFunc_approx hf hbf with ⟨sf, hsf, hsfB⟩
  have hstarapprox : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖(star (sf n)) x - star (f x)‖ < ε := by
    intro ε hε
    rcases hsf ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn x => ?_⟩
    change ‖star (sf n x) - star (f x)‖ < ε
    simpa only [← star_sub, norm_star] using hN n hn x
  have hcf : CauchySeq (fun n => E.simpleIntegral (sf n)) := E.simpleIntegral_cauchySeq hsf
  have hlf : Filter.Tendsto (fun n => E.simpleIntegral (sf n)) Filter.atTop
      (nhds (Filter.atTop.limUnder (fun n => E.simpleIntegral (sf n)))) := hcf.tendsto_limUnder
  have hls : Filter.Tendsto (fun n => E.simpleIntegral (star (sf n))) Filter.atTop
      (nhds (star (Filter.atTop.limUnder (fun n => E.simpleIntegral (sf n))))) := by
    simpa only [E.simpleIntegral_star] using hlf.star
  calc
    E.boundedFC (fun x => star (f x)) (continuous_star.measurable.comp hf) hstar =
        Filter.atTop.limUnder (fun n => E.simpleIntegral (star (sf n))) :=
      E.boundedFC_eq_limUnder (continuous_star.measurable.comp hf) hstar hstarapprox
    _ = star (Filter.atTop.limUnder (fun n => E.simpleIntegral (sf n))) := hls.limUnder_eq
    _ = star (E.boundedFC f hf hbf) := by
      rw [show E.boundedFC f hf hbf = Filter.atTop.limUnder (fun n => E.simpleIntegral (sf n)) from
        E.boundedFC_eq_limUnder hf hbf hsf]

lemma boundedFC_mem_unitary {f : X → ℂ} (hf : Measurable f)
    (hbf : ∃ C, ∀ x, ‖f x‖ ≤ C) (hmod : ∀ x, star (f x) * f x = 1) :
    E.boundedFC f hf hbf ∈ unitary A := by
  classical
  have hbstar : ∃ C, ∀ x, ‖star (f x)‖ ≤ C := by simpa only [norm_star] using hbf
  have hmod' : ∀ x, f x * star (f x) = 1 := fun x => by simpa [mul_comm] using hmod x
  have hm₁ := E.boundedFC_mul (f := fun x => star (f x)) (g := f)
    (continuous_star.measurable.comp hf) hf hbstar hbf
    (by simpa [Pi.mul_apply] using
      (⟨1, fun x => by rw [hmod x]; simp⟩ : ∃ C, ∀ x, ‖star (f x) * f x‖ ≤ C))
  have hm₂ := E.boundedFC_mul (f := f) (g := fun x => star (f x))
    hf (continuous_star.measurable.comp hf) hbf hbstar
    (by simpa [Pi.mul_apply] using
      (⟨1, fun x => by rw [hmod' x]; simp⟩ : ∃ C, ∀ x, ‖f x * star (f x)‖ ≤ C))
  have hstarFC := E.boundedFC_star hf hbf
  have hone : E.boundedFC (fun _ : X => (1 : ℂ)) (by fun_prop)
      (show ∃ C : ℝ, ∀ _ : X, ‖(1 : ℂ)‖ ≤ C from ⟨1, by simp⟩) = (1 : A) := by
    simpa using E.boundedFC_const 1
  have h₁ : star (E.boundedFC f hf hbf) * E.boundedFC f hf hbf = 1 := by
    calc
      star (E.boundedFC f hf hbf) * E.boundedFC f hf hbf =
          E.boundedFC (fun x => star (f x)) (continuous_star.measurable.comp hf) hbstar *
            E.boundedFC f hf hbf := by rw [hstarFC]
      _ = E.boundedFC ((fun x => star (f x)) * f) _ _ := hm₁.symm
      _ = E.boundedFC (fun _ : X => (1 : ℂ)) (by fun_prop) _ := by
        have heq : (fun x => star (f x)) * f = (fun _ : X => (1 : ℂ)) := by
          funext x; simpa only [Pi.mul_apply] using hmod x
        exact E.boundedFC_congr _ _ _ _ (fun x => congrFun heq x)
      _ = 1 := hone
  have h₂ : E.boundedFC f hf hbf * star (E.boundedFC f hf hbf) = 1 := by
    calc
      E.boundedFC f hf hbf * star (E.boundedFC f hf hbf) =
          E.boundedFC f hf hbf *
            E.boundedFC (fun x => star (f x)) (continuous_star.measurable.comp hf) hbstar := by
              rw [hstarFC]
      _ = E.boundedFC (f * fun x => star (f x)) _ _ := hm₂.symm
      _ = E.boundedFC (fun _ : X => (1 : ℂ)) (by fun_prop) _ := by
        have heq : f * (fun x => star (f x)) = (fun _ : X => (1 : ℂ)) := by
          funext x; simpa only [Pi.mul_apply] using hmod' x
        exact E.boundedFC_congr _ _ _ _ (fun x => congrFun heq x)
      _ = 1 := hone
  exact ⟨h₁, h₂⟩

lemma boundedFC_indicator {S : Set X} (hS : MeasurableSet S) :
    E.boundedFC (normalIndicatorFunction S) (normalIndicatorFunction_measurable hS)
      (normalIndicatorFunction_bounded S) = (E S : A) := by
  classical
  let f : SimpleFunc X ℂ := SimpleFunc.piecewise S hS (SimpleFunc.const X 1) (SimpleFunc.const X 0)
  have hf : (fun x : X => f x) = normalIndicatorFunction S := by
    funext x
    change S.indicator (fun _ : X => (1 : ℂ)) x = normalIndicatorFunction S x
    rfl
  have hfb : ∃ C, ∀ x, ‖f x‖ ≤ C := by
    refine ⟨1, ?_⟩
    intro x; by_cases hx : x ∈ S <;> simp [f, hx]
  have hcalc := E.boundedFC_of_simpleFunc f (by fun_prop) hfb
  have hsimple : E.simpleIntegral f = (E S : A) := by
    rw [E.simpleIntegral_eq_setToSimpleFunc f]
    exact (SimpleFunc.setToSimpleFunc_indicator E.spectralCLM
      (by simp [spectralCLM]) hS 1).trans (by simp [spectralCLM_apply])
  calc
    E.boundedFC (normalIndicatorFunction S) (normalIndicatorFunction_measurable hS)
        (normalIndicatorFunction_bounded S) = E.boundedFC (fun x : X => f x) (by fun_prop) hfb := by
      apply E.boundedFC_congr (normalIndicatorFunction_measurable hS) (by fun_prop)
        (normalIndicatorFunction_bounded S) hfb
      exact fun x => hf.symm ▸ rfl
    _ = E.simpleIntegral f := hcalc
    _ = (E S : A) := hsimple

end NormalPVM

/-! ## The certificate constructors

`NormalBorelFunctionalCalculus.ofNormalPVM` packages every law proved above into the certificate
type of `NormalAffiliated.lean`.  `ofPredualPVM` is the named contract `general-theory-roadmap.md`'s
P3 package asks for: it is literally `ofNormalPVM` applied after forgetting the extra
predual-additivity witness, since the construction above never needed it. -/

namespace NormalBorelFunctionalCalculus

variable {X : Type*} [MeasurableSpace X] {A : Type*} [WStarAlgebra A]

/-- Every `NormalPVM` already carries a bounded Borel functional calculus: no predual-additivity
or completeness hypothesis beyond `WStarAlgebra A` is required. -/
noncomputable def ofNormalPVM (E : NormalPVM X A) : NormalBorelFunctionalCalculus E where
  boundedFC := E.boundedFC
  boundedFC_congr := by intro f g hf hg hfb hgb hfg; exact E.boundedFC_congr hf hg hfb hgb hfg
  boundedFC_const := by intro c; exact E.boundedFC_const c
  boundedFC_add := by intro f g hf hg hfb hgb hfg; exact E.boundedFC_add hf hg hfb hgb hfg
  boundedFC_mul := by intro f g hf hg hfb hgb hfg; exact E.boundedFC_mul hf hg hfb hgb hfg
  boundedFC_smul := by intro c f hf hfb hcf; exact E.boundedFC_smul c hf hfb hcf
  boundedFC_star := by intro f hf hfb hstar; exact E.boundedFC_star hf hfb hstar
  boundedFC_mem_unitary := by intro f hf hfb hmod; exact E.boundedFC_mem_unitary hf hfb hmod
  boundedFC_indicator := by intro S hS; exact E.boundedFC_indicator hS

/-- The named contract exported to P5/P6: a `PredualPVM` — a `NormalPVM` with the stronger
predual-functional σ-additivity — has a proved bounded Borel functional calculus, with no
certificate needed as an extra hypothesis.  The predual-additivity witness itself is not consumed
by the construction (see the file docstring); it is only what makes the resulting `NormalPVM` the
correct weak-⋆ spectral measure of a normal operator in the first place. -/
noncomputable def ofPredualPVM (E : PredualPVM X A) :
    NormalBorelFunctionalCalculus E.toNormalPVM :=
  ofNormalPVM E.toNormalPVM

/-! ### Simple functions and uniqueness -/

/- The indicator axiom and the algebra laws determine a certificate on every bounded simple
   function.  This is the finite-sum part of the usual uniqueness proof; the uniform-limit part is
   packaged below in `eq_of_eq_on_simpleFunctions`. -/
lemma boundedFC_of_simpleFunc_eq_simpleIntegral
    {E : NormalPVM X A} (C : NormalBorelFunctionalCalculus E)
    (f : SimpleFunc X ℂ) (hf : Measurable (fun x => f x))
    (hfb : ∃ K : ℝ, ∀ x, ‖f x‖ ≤ K) :
    C.boundedFC (fun x => f x) hf hfb = E.simpleIntegral f := by
  induction f using SimpleFunc.induction with
  | @const c s hs =>
    have hsi : ∀ x : X, ‖normalIndicatorFunction s x‖ ≤ 1 := by
      intro x
      by_cases hx : x ∈ s <;> simp [normalIndicatorFunction, hx]
    have hci : ∃ K : ℝ, ∀ x : X, ‖c * normalIndicatorFunction s x‖ ≤ K := by
      refine ⟨‖c‖, fun x => ?_⟩
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg c) (hsi x)
    have hsmul := C.boundedFC_smul (f := normalIndicatorFunction s) c
      (normalIndicatorFunction_measurable hs) (normalIndicatorFunction_bounded s) hci
    have hind := C.boundedFC_indicator (S := s) hs
    have hsimple := SimpleFunc.setToSimpleFunc_indicator E.spectralCLM
      (by simp [NormalPVM.spectralCLM, NormalPVM.spectralCLM_apply]) hs c
    calc
      C.boundedFC (fun x => (SimpleFunc.piecewise s hs (SimpleFunc.const X c)
          (SimpleFunc.const X 0)) x) hf hfb =
          C.boundedFC (fun x => c * normalIndicatorFunction s x)
            (measurable_const.mul (normalIndicatorFunction_measurable hs)) hci := by
        apply C.boundedFC_congr hf
          (measurable_const.mul (normalIndicatorFunction_measurable hs)) hfb hci
        intro x
        by_cases hx : x ∈ s <;>
          simp [normalIndicatorFunction, SimpleFunc.coe_piecewise, hx]
      _ = c • C.boundedFC (normalIndicatorFunction s)
          (normalIndicatorFunction_measurable hs)
          (normalIndicatorFunction_bounded s) := hsmul
      _ = c • (E s : A) := by rw [hind]
      _ = E.simpleIntegral (SimpleFunc.piecewise s hs (SimpleFunc.const X c)
          (SimpleFunc.const X 0)) := by
        rw [E.simpleIntegral_eq_setToSimpleFunc]
        simpa [NormalPVM.spectralCLM_apply] using hsimple.symm
  | @add f g hdisj ihf ihg =>
    have hfbf : ∃ K : ℝ, ∀ x, ‖f x‖ ≤ K := by
      obtain ⟨K, hK⟩ := (f.finite_range.image norm).bddAbove
      refine ⟨K, fun x => ?_⟩
      apply hK
      exact ⟨f x, by simp, rfl⟩
    have hfbg : ∃ K : ℝ, ∀ x, ‖g x‖ ≤ K := by
      obtain ⟨K, hK⟩ := (g.finite_range.image norm).bddAbove
      refine ⟨K, fun x => ?_⟩
      apply hK
      exact ⟨g x, by simp, rfl⟩
    have hif := ihf (by fun_prop) hfbf
    have hig := ihg (by fun_prop) hfbg
    have hadd := C.boundedFC_add (by fun_prop) (by fun_prop) hfbf hfbg hfb
    calc
      C.boundedFC (fun x => (f + g) x) hf hfb =
          C.boundedFC (fun x => f x + g x) (by fun_prop) hfb := by
        apply C.boundedFC_congr hf (by fun_prop) hfb hfb
        intro x
        rfl
      _ = C.boundedFC (fun x => f x) (by fun_prop) hfbf +
          C.boundedFC (fun x => g x) (by fun_prop) hfbg := hadd
      _ = E.simpleIntegral f + E.simpleIntegral g := by rw [hif, hig]
      _ = E.simpleIntegral (f + g) := (E.simpleIntegral_add f g).symm

/-! ### Contractivity and uniqueness

The certificate laws imply the usual C⋆-norm estimate.  This is useful independently of the
canonical construction: it makes the calculus continuous for uniform convergence and therefore
allows uniqueness to be stated at the certificate level. -/

lemma norm_boundedFC_le {E : NormalPVM X A} (C : NormalBorelFunctionalCalculus E)
    {f : X → ℂ} (hf : Measurable f) {M : ℝ} (hM : 0 ≤ M)
    (hfm : ∀ x, ‖f x‖ ≤ M) :
    ‖C.boundedFC f hf (⟨M, hfm⟩)‖ ≤ M := by
  let g : X → ℂ := fun x => (Real.sqrt (M ^ 2 - ‖f x‖ ^ 2) : ℂ)
  have hnonneg (x : X) : 0 ≤ M ^ 2 - ‖f x‖ ^ 2 := by
    have hsq : ‖f x‖ ^ 2 ≤ M ^ 2 :=
      (sq_le_sq₀ (norm_nonneg (f x)) hM).2 (hfm x)
    linarith
  have hg : Measurable g := by
    dsimp [g]
    exact Complex.measurable_ofReal.comp
      ((measurable_const.sub ((measurable_norm.comp hf).pow_const 2)).sqrt)
  have hgm' : ∀ x, ‖g x‖ ≤ M := by
    intro x
    dsimp [g]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact hM
    · nlinarith [sq_nonneg (‖f x‖)]
  have hgm : ∃ C' : ℝ, ∀ x, ‖g x‖ ≤ C' := ⟨M, hgm'⟩
  have hgstar : ∃ C' : ℝ, ∀ x, ‖star (g x)‖ ≤ C' := by
    simpa only [norm_star] using hgm
  have hstarf : Measurable (fun x => star (f x)) :=
    continuous_star.measurable.comp hf
  have hstarfb : ∃ C' : ℝ, ∀ x, ‖star (f x)‖ ≤ C' := by
    simpa only [norm_star] using ⟨M, hfm⟩
  have hffb : ∃ C' : ℝ, ∀ x, ‖(fun x => star (f x) * f x) x‖ ≤ C' := by
    refine ⟨M ^ 2, fun x => ?_⟩
    rw [norm_mul]
    simpa only [norm_star, pow_two] using
      (mul_le_mul (hfm x) (hfm x) (norm_nonneg _) hM)
  have hggb : ∃ C' : ℝ, ∀ x, ‖g x * g x‖ ≤ C' := by
    refine ⟨M ^ 2, fun x => ?_⟩
    rw [norm_mul]
    simpa [pow_two] using (mul_le_mul (hgm' x) (hgm' x) (norm_nonneg _) hM)
  have haddb : ∃ C' : ℝ, ∀ x, ‖star (f x) * f x + g x * g x‖ ≤ C' := by
    refine ⟨M ^ 2, fun x => ?_⟩
    have hff : star (f x) * f x = (‖f x‖ ^ 2 : ℝ) := by
      calc
        star (f x) * f x = f x * star (f x) := mul_comm _ _
        _ = (Complex.normSq (f x) : ℂ) := by
          rw [Complex.star_def, Complex.mul_conj]
        _ = (‖f x‖ ^ 2 : ℝ) := by rw [Complex.normSq_eq_norm_sq]
    have hgg : star (g x) * g x = (M ^ 2 - ‖f x‖ ^ 2 : ℝ) := by
      calc
        star (g x) * g x = g x * star (g x) := mul_comm _ _
        _ = (Complex.normSq (g x) : ℂ) := by
          rw [Complex.star_def, Complex.mul_conj]
        _ = (M ^ 2 - ‖f x‖ ^ 2 : ℝ) := by
          dsimp [g]
          rw [Complex.normSq_eq_norm_sq, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hnonneg x)]
    have hsum : star (f x) * f x + g x * g x = (M ^ 2 : ℝ) := by
      rw [hff]
      have hgg' : g x * g x = (M ^ 2 - ‖f x‖ ^ 2 : ℝ) := by
        dsimp [g]
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hnonneg x)]
      rw [hgg']
      push_cast
      ring
    rw [hsum, Complex.norm_real]
    simp
  have hmul₁ := C.boundedFC_mul hstarf hf hstarfb (⟨M, hfm⟩) hffb
  have hmul₂ := C.boundedFC_mul hg hg hgm hgm hggb
  have hadd := C.boundedFC_add (hstarf.mul hf) (hg.mul hg) hffb hggb haddb
  have hstar := C.boundedFC_star hf (⟨M, hfm⟩) hstarfb
  have hgbstar := C.boundedFC_star hg hgm hgstar
  have hsum :
      star (C.boundedFC f hf (⟨M, hfm⟩)) * C.boundedFC f hf (⟨M, hfm⟩) +
        C.boundedFC g hg hgm * C.boundedFC g hg hgm =
      (M ^ 2 : ℂ) • (1 : A) := by
    calc
      _ = C.boundedFC ((fun x => star (f x)) * f)
          (hstarf.mul hf) hffb + C.boundedFC (g * g)
            (hg.mul hg) hggb := by rw [← hstar, ← hmul₁, ← hmul₂]
      _ = C.boundedFC ((fun x => star (f x)) * f + g * g)
          ((hstarf.mul hf).add (hg.mul hg)) haddb := hadd.symm
      _ = C.boundedFC (fun _ : X => (M ^ 2 : ℂ)) measurable_const
          (⟨M ^ 2, fun _ => by simp [hM]⟩) := by
        apply C.boundedFC_congr _ _ haddb (⟨M ^ 2, fun _ => by simp [hM]⟩)
        intro x
        have hff : star (f x) * f x = (‖f x‖ ^ 2 : ℝ) := by
          calc
            star (f x) * f x = f x * star (f x) := mul_comm _ _
            _ = (Complex.normSq (f x) : ℂ) := by
              rw [Complex.star_def, Complex.mul_conj]
            _ = (‖f x‖ ^ 2 : ℝ) := by rw [Complex.normSq_eq_norm_sq]
        have hgg : g x * g x = (M ^ 2 - ‖f x‖ ^ 2 : ℝ) := by
          dsimp [g]
          rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hnonneg x)]
        rw [hff, hgg]
        push_cast
        ring
      _ = _ := C.boundedFC_const (M ^ 2 : ℂ)
  have hgbself : star (C.boundedFC g hg hgm) = C.boundedFC g hg hgm := by
    have hfun : (fun x => star (g x)) = g := by
      funext x
      dsimp [g]
      simp [Complex.star_def]
    have hfc := C.boundedFC_congr
      (continuous_star.measurable.comp hg) hg hgstar hgm (fun x => congrFun hfun x)
    exact hgbstar.symm.trans hfc
  have hle :
      star (C.boundedFC f hf (⟨M, hfm⟩)) * C.boundedFC f hf (⟨M, hfm⟩) ≤
        (M ^ 2 : ℂ) • (1 : A) := by
    calc
      _ ≤ _ + C.boundedFC g hg hgm * C.boundedFC g hg hgm := by
        apply le_add_of_nonneg_right
        calc
          0 ≤ star (C.boundedFC g hg hgm) * C.boundedFC g hg hgm :=
            star_mul_self_nonneg _
          _ = C.boundedFC g hg hgm * C.boundedFC g hg hgm := by rw [hgbself]
      _ = _ := hsum
  have hn := CStarAlgebra.norm_le_norm_of_nonneg_of_le
    (star_mul_self_nonneg (C.boundedFC f hf (⟨M, hfm⟩))) hle
  have hn' : ‖C.boundedFC f hf (⟨M, hfm⟩)‖ ^ 2 ≤ M ^ 2 := by
    calc
      ‖C.boundedFC f hf (⟨M, hfm⟩)‖ ^ 2 =
          ‖star (C.boundedFC f hf (⟨M, hfm⟩)) *
            C.boundedFC f hf (⟨M, hfm⟩)‖ := by
        rw [CStarRing.norm_star_mul_self, pow_two]
      _ ≤ ‖(M ^ 2 : ℂ) • (1 : A)‖ := hn
      _ ≤ M ^ 2 := by
        rcases subsingleton_or_nontrivial A with hA | hA
        · letI : Subsingleton A := hA
          have h1 : (1 : A) = 0 := Subsingleton.elim _ _
          rw [h1, smul_zero, norm_zero]
          positivity
        · letI : Nontrivial A := hA
          rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hM]
          rw [CStarRing.norm_one]
          simp
  nlinarith [sq_nonneg (‖C.boundedFC f hf (⟨M, hfm⟩)‖ + M)]

/-- The certificate calculus is contractive for the uniform norm. -/
lemma norm_boundedFC_sub_le {E : NormalPVM X A} (C : NormalBorelFunctionalCalculus E)
    {f g : X → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hgb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    {M : ℝ} (hM : 0 ≤ M) (hfg : ∀ x, ‖f x - g x‖ ≤ M) :
    ‖C.boundedFC f hf hfb - C.boundedFC g hg hgb‖ ≤ M := by
  obtain ⟨Cg, hCg⟩ := hgb
  have hneg : ∃ C : ℝ, ∀ x, ‖-g x‖ ≤ C := ⟨Cg, fun x => by simpa using hCg x⟩
  have hsumBound : ∃ C : ℝ, ∀ x, ‖f x + -g x‖ ≤ C := by
    simpa only [sub_eq_add_neg] using ⟨M, hfg⟩
  have hgm : Measurable (fun x => -g x) := continuous_neg.measurable.comp hg
  have hadd := C.boundedFC_add hf hgm hfb hneg hsumBound
  have hsmul := C.boundedFC_smul (-1) hg (⟨Cg, hCg⟩)
    (⟨Cg, fun x => by simpa using hCg x⟩)
  have hsub : C.boundedFC (f - g) (hf.sub hg) (⟨M, hfg⟩) =
      C.boundedFC f hf hfb - C.boundedFC g hg (⟨Cg, hCg⟩) := by
    calc
      C.boundedFC (f - g) (hf.sub hg) (⟨M, hfg⟩) =
          C.boundedFC (f + fun x => -g x) (hf.add hgm) hsumBound := by
        apply C.boundedFC_congr (hf.sub hg) (hf.add hgm) (⟨M, hfg⟩) hsumBound
        intro x
        rfl
      _ = C.boundedFC f hf hfb + C.boundedFC (fun x => -g x) hgm hneg := hadd
      _ = C.boundedFC f hf hfb - C.boundedFC g hg (⟨Cg, hCg⟩) := by
        have hsmul' : C.boundedFC (fun x => -g x) hgm hneg =
            C.boundedFC (fun x => -1 * g x) (by fun_prop)
              (⟨Cg, fun x => by simpa using hCg x⟩) := by
          apply C.boundedFC_congr hgm (by fun_prop) hneg
            (⟨Cg, fun x => by simpa using hCg x⟩)
          intro x
          simp
        rw [hsmul', hsmul]
        simp [sub_eq_add_neg]
  rw [← hsub]
  exact C.norm_boundedFC_le (hf.sub hg) hM hfg

/- The following is the certificate-level uniqueness principle.  The hypothesis is deliberately
   phrased on simple functions: it is the exact data needed to identify an arbitrary certificate
   through the uniform simple-function approximation theorem, without making any representation
   choices part of the public API. -/
theorem eq_of_eq_on_simpleFunctions
    {E : NormalPVM X A} (C D : NormalBorelFunctionalCalculus E)
    (hCD : ∀ (s : SimpleFunc X ℂ) (hs : Measurable (fun x => s x))
      (hsb : ∃ K : ℝ, ∀ x, ‖s x‖ ≤ K),
      C.boundedFC (fun x => s x) hs hsb = D.boundedFC (fun x => s x) hs hsb) :
    ∀ {f : X → ℂ} (hf : Measurable f)
      (hfb : ∃ K : ℝ, ∀ x, ‖f x‖ ≤ K),
      C.boundedFC f hf hfb = D.boundedFC f hf hfb := by
  intro f hf hfb
  rcases exists_uniform_simpleFunc_approx hf hfb with ⟨s, hs, hsB⟩
  obtain ⟨K, hK⟩ := hsB
  have hC : Filter.Tendsto (fun n => C.boundedFC (fun x => s n x)
      (by fun_prop) (⟨K, hK n⟩)) Filter.atTop
      (𝓝 (C.boundedFC f hf hfb)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    rcases hs (ε / 2) hε2 with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    change dist (C.boundedFC (fun x => s n x) _ _) (C.boundedFC f hf hfb) < ε
    have hsub := C.norm_boundedFC_sub_le (by fun_prop) hf
      (⟨K, hK n⟩) hfb (le_of_lt hε2)
      (fun x => le_of_lt (hN n hn x))
    simpa [dist_eq_norm] using lt_of_le_of_lt hsub (by linarith)
  have hD : Filter.Tendsto (fun n => D.boundedFC (fun x => s n x)
      (by fun_prop) (⟨K, hK n⟩)) Filter.atTop
      (𝓝 (D.boundedFC f hf hfb)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε2 : 0 < ε / 2 := by linarith
    rcases hs (ε / 2) hε2 with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    change dist (D.boundedFC (fun x => s n x) _ _) (D.boundedFC f hf hfb) < ε
    have hsub := D.norm_boundedFC_sub_le (by fun_prop) hf
      (⟨K, hK n⟩) hfb (le_of_lt hε2)
      (fun x => le_of_lt (hN n hn x))
    simpa [dist_eq_norm] using lt_of_le_of_lt hsub (by linarith)
  apply tendsto_nhds_unique hC
  apply hD.congr'
  exact Filter.Eventually.of_forall (fun n => hCD (s n) (by fun_prop)
    (⟨K, hK n⟩) |>.symm)

/-- Any two bounded Borel-calculus certificates over the same `NormalPVM` have identical values.
The indicator axiom fixes the finite simple sums, and contractivity plus uniform approximation fixes
all bounded measurable functions. -/
theorem boundedFC_eq_of_same_normalPVM
    {E : NormalPVM X A} (C D : NormalBorelFunctionalCalculus E)
    {f : X → ℂ} (hf : Measurable f)
    (hfb : ∃ K : ℝ, ∀ x, ‖f x‖ ≤ K) :
    C.boundedFC f hf hfb = D.boundedFC f hf hfb := by
  apply C.eq_of_eq_on_simpleFunctions D
  intro s hs hsb
  rw [C.boundedFC_of_simpleFunc_eq_simpleIntegral s hs hsb,
    D.boundedFC_of_simpleFunc_eq_simpleIntegral s hs hsb]

end NormalBorelFunctionalCalculus

/-! ## Compatibility with the norm-valued calculus

The old norm-valued calculus remains a specialization of the new one: forgetting a norm-valued
`PVM` down to a `NormalPVM` and constructing `ofNormalPVM` agrees, on every bounded measurable
function, with the calculus `NormalBorelFunctionalCalculus.ofPVM` already built directly from the
norm-valued PVM in `NormalAffiliated.lean`.  Both sides are norm limits of the *same* finite
spectral sums along any common uniformly convergent simple-function approximation, so the proof
never has to unfold `boundedFC`'s internal choice of approximating sequence — it only needs the
`boundedFC_eq_limUnder` characterization on each side. -/

theorem NormalBorelFunctionalCalculus.ofNormalPVM_ofPVM_boundedFC_eq
    {A : Type*} [WStarAlgebra A] (E : PVM ℝ A) {f : ℝ → ℂ} (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    (NormalBorelFunctionalCalculus.ofNormalPVM (NormalPVM.ofPVM E)).boundedFC f hf hfb =
      (NormalBorelFunctionalCalculus.ofPVM E).boundedFC f hf hfb := by
  classical
  dsimp only [NormalBorelFunctionalCalculus.ofNormalPVM, NormalBorelFunctionalCalculus.ofPVM]
  rcases exists_uniform_simpleFunc_approx hf hfb with ⟨s, hs, _⟩
  have h1 : (NormalPVM.ofPVM E).boundedFC f hf hfb =
      Filter.atTop.limUnder (fun n => (NormalPVM.ofPVM E).simpleIntegral (s n)) :=
    (NormalPVM.ofPVM E).boundedFC_eq_limUnder hf hfb hs
  have h2 : (⟨E⟩ : AffiliatedObservable A).boundedFC f hf hfb =
      Filter.atTop.limUnder (fun n => (⟨E⟩ : AffiliatedObservable A).simpleIntegral (s n)) :=
    (⟨E⟩ : AffiliatedObservable A).boundedFC_eq_limUnder hf hfb hs
  have hpt : ∀ n, (NormalPVM.ofPVM E).simpleIntegral (s n) =
      (⟨E⟩ : AffiliatedObservable A).simpleIntegral (s n) := by
    intro n
    simp only [NormalPVM.simpleIntegral, AffiliatedObservable.simpleIntegral,
      NormalPVM.ofPVM_apply]
  rw [h1, h2]
  simp_rw [hpt]

end OperatorAlgebra
