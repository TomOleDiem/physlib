/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Calculus.FunctionalCalculus
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.SpectralTheory.UnboundedSpectralIntegral

/-!
# Concrete representations of the affiliated functional calculus

This is the first compatibility layer between the representation-free affiliated API and the
Hilbert-space spectral integral. The bridge hypothesis identifies spectral projections; the
finite/simple integral compatibility below is then a direct algebraic consequence. The bounded
measurable compatibility theorem is proved later by passing this identity through the common
uniform simple approximants.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ComplexOrder CStarAlgebra InnerProductSpace Topology
open ContinuousLinearMap ContinuousLinearMapWOT

namespace OperatorAlgebra

variable {A H : Type*} [OperatorAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The additive-monoid-homomorphism view of a representation `π : A →⋆ B(H)`, landing in the
weak-operator-topology bundle `H →WOT[ℂ] H` so that spectral-measure pushforward
(`VectorMeasure.mapRange`) applies to it directly. -/
noncomputable def representationToWOT (π : Representation A H) :
    A →+ (H →WOT[ℂ] H) where
  toFun a := ContinuousLinearMapWOT.ofCLM (π a)
  map_zero' := by simp
  map_add' a b := by simp

lemma continuous_representationToWOT (π : Representation A H) :
    Continuous (representationToWOT π) := by
  have hπ : Continuous (π : A → B(H)) := by
    apply AddMonoidHomClass.continuous_of_bound π 1
    intro a
    simpa using NonUnitalStarAlgHom.norm_apply_le π a
  change Continuous (fun a : A => ContinuousLinearMapWOT.ofCLM (π a))
  exact ContinuousLinearMapWOT.continuous_ofCLM.comp hπ

/-- The concrete weak-operator-topology spectral measure obtained by representing a real
`AffiliatedObservable`'s spectral projections through `π`. -/
noncomputable def representedSpectralMeasure
    (π : Representation A H) (T : AffiliatedObservable A) :
    QuantumMechanics.WOTSpectralMeasure ℝ H where
  toVectorMeasure :=
    T.spectralMeasure.toVectorMeasure.mapRange (representationToWOT π)
      (continuous_representationToWOT π)
  isStarProjection' S := by
    change IsStarProjection (ContinuousLinearMapWOT.ofCLM
      (π (T.spectralMeasure S : A)))
    refine ⟨?_, ?_⟩
    · change ContinuousLinearMapWOT.ofCLM (π (T.spectralMeasure S : A)) *
        ContinuousLinearMapWOT.ofCLM (π (T.spectralMeasure S : A)) = _
      rw [← ContinuousLinearMapWOT.ofCLM_mul, ← map_mul]
      exact congrArg (fun a : A => ContinuousLinearMapWOT.ofCLM (π a))
        (T.spectralMeasure.isStarProjection S).isIdempotentElem
    · apply ContinuousLinearMapWOT.toCLM_injective
      change star (π (T.spectralMeasure S : A)) = π (T.spectralMeasure S : A)
      rw [← map_star]
      exact congrArg π (T.spectralMeasure.isStarProjection S).isSelfAdjoint
  univ' := by
    change ContinuousLinearMapWOT.ofCLM (π (T.spectralMeasure univ : A)) = 1
    rw [T.spectralMeasure.univ, map_one]
    rfl

@[simp]
lemma representedSpectralMeasure_apply
    (π : Representation A H) (T : AffiliatedObservable A) (S : Set ℝ) :
    representedSpectralMeasure π T S =
      ContinuousLinearMapWOT.ofCLM (π (T.spectralMeasure S : A)) := by
  change (T.spectralMeasure.toVectorMeasure.mapRange (representationToWOT π)
      (continuous_representationToWOT π)) S = _
  rw [MeasureTheory.VectorMeasure.mapRange_apply]
  rfl

/-! ## Representation compatibility of the `StarAlgEquiv` transport

`Affiliated.lean`'s `β.affiliatedObservable` transports spectral data along a star-algebra
isomorphism `β : A ≃⋆ₐ[ℂ] B`. Representing the transported observable through `π : Representation
B H` gives exactly the same WOT spectral measure as representing the original observable through
the composed representation `π.comp β.toStarAlgHom : Representation A H`. This is the
representation half of P5's `StarAlgEquiv` functoriality requirement: transport-then-represent
agrees with represent-along-the-composed-map, so a faithful representation of `B` together with a
`StarAlgEquiv` gives back a (generally non-faithful, unless `π` is also faithful) representation of
`A` with compatible spectral data. -/

lemma representedSpectralMeasure_starAlgEquiv
    {A B : Type*} [OperatorAlgebra A] [OperatorAlgebra B]
    (β : A ≃⋆ₐ[ℂ] B) (π : Representation B H) (T : AffiliatedObservable A) :
    representedSpectralMeasure (π.comp β.toStarAlgHom) T =
      representedSpectralMeasure π (β.affiliatedObservable T) := by
  rw [QuantumMechanics.WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  apply ContinuousLinearMapWOT.toCLM_injective
  rw [representedSpectralMeasure_apply, representedSpectralMeasure_apply]
  change π (β (T.spectralMeasure S : A)) = π ((β.affiliatedObservable T).spectralMeasure S)
  rw [StarAlgEquiv.affiliatedObservable_spectralMeasure_apply]

/-! ## Representing the complex measurable calculus

`AffiliatedObservable.measurableFC` changes the spectral variable from `ℝ` to `ℂ`. Its concrete
realization is therefore the WOT pushforward of the represented real PVM. We keep the complex
version of the representation map explicit so that the theorem below also applies to arbitrary
`AffiliatedOperator`s, not only to self-adjoint data. -/

/-- The concrete weak-operator-topology spectral measure obtained by representing a complex
`AffiliatedOperator`'s spectral projections through `π`. -/
noncomputable def representedAffiliatedOperatorSpectralMeasure
    (π : Representation A H) (T : AffiliatedOperator A) :
    QuantumMechanics.WOTSpectralMeasure ℂ H where
  toVectorMeasure :=
    T.spectralMeasure.toVectorMeasure.mapRange (representationToWOT π)
      (continuous_representationToWOT π)
  isStarProjection' S := by
    change IsStarProjection (ContinuousLinearMapWOT.ofCLM
      (π (T.spectralMeasure S : A)))
    refine ⟨?_, ?_⟩
    · change ContinuousLinearMapWOT.ofCLM (π (T.spectralMeasure S : A)) *
        ContinuousLinearMapWOT.ofCLM (π (T.spectralMeasure S : A)) = _
      rw [← ContinuousLinearMapWOT.ofCLM_mul, ← map_mul]
      exact congrArg (fun a : A => ContinuousLinearMapWOT.ofCLM (π a))
        (T.spectralMeasure.isStarProjection S).isIdempotentElem
    · apply ContinuousLinearMapWOT.toCLM_injective
      change star (π (T.spectralMeasure S : A)) = π (T.spectralMeasure S : A)
      rw [← map_star]
      exact congrArg π (T.spectralMeasure.isStarProjection S).isSelfAdjoint
  univ' := by
    change ContinuousLinearMapWOT.ofCLM (π (T.spectralMeasure univ : A)) = 1
    rw [T.spectralMeasure.univ, map_one]
    rfl

@[simp]
lemma representedAffiliatedOperatorSpectralMeasure_apply
    (π : Representation A H) (T : AffiliatedOperator A) (S : Set ℂ) :
    representedAffiliatedOperatorSpectralMeasure π T S =
      ContinuousLinearMapWOT.ofCLM (π (T.spectralMeasure S : A)) := by
  change (T.spectralMeasure.toVectorMeasure.mapRange (representationToWOT π)
      (continuous_representationToWOT π)) S = _
  rw [MeasureTheory.VectorMeasure.mapRange_apply]
  rfl

lemma representedMeasurableFC_eq_map
    (π : Representation A H) (T : AffiliatedObservable A)
    {f : ℝ → ℂ} (hf : Measurable f) :
    representedAffiliatedOperatorSpectralMeasure π (T.measurableFC f hf) =
      (representedSpectralMeasure π T).map f hf := by
  apply QuantumMechanics.WOTSpectralMeasure.ext_of_scalarMeasure_eq
  intro x y
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  change ⟪y, representedAffiliatedOperatorSpectralMeasure π
      (T.measurableFC f hf) S x⟫_ℂ =
    ⟪y, ((representedSpectralMeasure π T).map f hf) S x⟫_ℂ
  rw [representedAffiliatedOperatorSpectralMeasure_apply,
    (representedSpectralMeasure π T).map_apply f hf hS,
    representedSpectralMeasure_apply]
  rw [T.measurableFC_spectralMeasure_apply hf hS]

lemma representedMeasurableRealFC_eq_map
    (π : Representation A H) (T : AffiliatedObservable A)
    {f : ℝ → ℝ} (hf : Measurable f) :
    representedSpectralMeasure π (T.measurableRealFC f hf) =
      (representedSpectralMeasure π T).map f hf := by
  apply QuantumMechanics.WOTSpectralMeasure.ext_of_scalarMeasure_eq
  intro x y
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  change ⟪y, representedSpectralMeasure π
      (T.measurableRealFC f hf) S x⟫_ℂ =
    ⟪y, ((representedSpectralMeasure π T).map f hf) S x⟫_ℂ
  rw [representedSpectralMeasure_apply,
    (representedSpectralMeasure π T).map_apply f hf hS,
    representedSpectralMeasure_apply]
  rw [T.measurableRealFC_spectralMeasure_apply hf hS]

lemma representedSpectralMeasure_eq
    (R : RepresentedAffiliatedObservable A H) :
    representedSpectralMeasure R.representation R.observable = R.spectralMeasure := by
  rw [QuantumMechanics.WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  apply ContinuousLinearMapWOT.toCLM_injective
  simpa [AffiliatedObservable.spectralMeasure_coe_spectralProjection] using
    R.spectralProjection_apply S

lemma affiliatedObservable_ext_of_representedSpectralMeasure_eq
    (π : Representation A H) (hπ : Function.Injective π)
    (T U : AffiliatedObservable A)
    (h : representedSpectralMeasure π T = representedSpectralMeasure π U) :
    T = U := by
  cases T with
  | mk μ =>
    cases U with
    | mk ν =>
      congr
      apply PVM.ext
      intro S hS
      apply hπ
      have hS' := congrArg (fun E : QuantumMechanics.WOTSpectralMeasure ℝ H => E S) h
      have hclm := congrArg ContinuousLinearMapWOT.toCLM hS'
      simpa [representedSpectralMeasure_apply] using hclm

/-! ## Representation of the bounded measurable calculus

The representation map sends the abstract finite spectral sums to the corresponding WOT sums.
Passing to the common uniform simple approximants then identifies the two completed bounded
calculi. This statement is deliberately formulated for an arbitrary representation and
`AffiliatedObservable`; it does not require a separately supplied `AffiliationBridge`, because
the represented WOT spectral measure is constructed directly from the abstract PVM. -/

namespace Representation

variable {A : Type*} [OperatorAlgebra A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma simpleIntegral_eq_boundedIntegral
    (π : Representation A H) (T : AffiliatedObservable A) (f : SimpleFunc ℝ ℂ) :
    π (T.simpleIntegral f) =
      (QuantumMechanics.WOTSpectralMeasure.simpleIntegral
        (representedSpectralMeasure π T) f).toCLM := by
  unfold AffiliatedObservable.simpleIntegral
    QuantumMechanics.WOTSpectralMeasure.simpleIntegral
  rw [map_sum]
  have hsum :
      (∑ z ∈ f.range, z • (representedSpectralMeasure π T) (f ⁻¹' {z})).toCLM =
        ∑ z ∈ f.range,
          (z • (representedSpectralMeasure π T) (f ⁻¹' {z})).toCLM := by
    induction f.range using Finset.induction_on with
    | empty => rfl
    | @insert z s hz ih =>
      simp only [Finset.sum_insert hz, ContinuousLinearMapWOT.toCLM_add, ih]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [map_smul]
  change z • π (T.spectralMeasure (f ⁻¹' {z}) : A) = _
  rw [representedSpectralMeasure_apply]
  rfl

lemma boundedFC_eq_boundedIntegral
    (π : Representation A H) (T : AffiliatedObservable A) {f : ℝ → ℂ}
    (hf : Measurable f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    π (T.boundedFC f hf hbdd) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (representedSpectralMeasure π T) f hf hbdd).toCLM := by
  let s : ℕ → SimpleFunc ℝ ℂ :=
    Classical.choose (AffiliatedObservable.exists_uniform_simple_approx hf hbdd)
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε :=
    (Classical.choose_spec (AffiliatedObservable.exists_uniform_simple_approx hf hbdd)).1
  have hsimple : ∀ n,
      π (T.simpleIntegral (s n)) =
        (QuantumMechanics.WOTSpectralMeasure.simpleIntegral
          (representedSpectralMeasure π T) (s n)).toCLM :=
    fun n => simpleIntegral_eq_boundedIntegral π T (s n)
  have hA : Filter.Tendsto
      (fun n => π (T.simpleIntegral (s n))) Filter.atTop
      (𝓝 (π (Filter.atTop.limUnder (fun n => T.simpleIntegral (s n))))) := by
    have hC : CauchySeq (fun n => T.simpleIntegral (s n)) :=
      AffiliatedObservable.simpleIntegral_cauchySeq T hs
    have hlim := hC.tendsto_limUnder
    have hcont : Continuous (π : A → B(H)) := by
      apply AddMonoidHomClass.continuous_of_bound π 1
      intro a
      simpa using NonUnitalStarAlgHom.norm_apply_le π a
    exact hcont.continuousAt.tendsto.comp hlim
  have hB : Filter.Tendsto
      (fun n =>
        (QuantumMechanics.WOTSpectralMeasure.simpleIntegral
          (representedSpectralMeasure π T) (s n)).toCLM) Filter.atTop
      (𝓝 (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (representedSpectralMeasure π T) f hf hbdd).toCLM) := by
    rw [QuantumMechanics.WOTSpectralMeasure.boundedIntegral_eq_of_uniform_approx
      (representedSpectralMeasure π T) hf hbdd hs]
    rw [QuantumMechanics.WOTSpectralMeasure.boundedIntegralOfUniformApprox_eq_limUnder]
    exact (QuantumMechanics.WOTSpectralMeasure.simpleIntegral_toCLM_cauchySeq
      (representedSpectralMeasure π T) hs).tendsto_limUnder
  have hA' : Filter.Tendsto
      (fun n => π (T.simpleIntegral (s n))) Filter.atTop
      (𝓝 (π (T.boundedFC f hf hbdd))) := by
    rw [AffiliatedObservable.boundedFC_eq_limUnder T hf hbdd hs]
    exact hA
  have hB' : Filter.Tendsto
      (fun n => π (T.simpleIntegral (s n))) Filter.atTop
      (𝓝 (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (representedSpectralMeasure π T) f hf hbdd).toCLM) := by
    apply hB.congr'
    exact Filter.Eventually.of_forall (fun n => (hsimple n).symm)
  have hlim :
      π (T.boundedFC f hf hbdd) =
        (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
          (representedSpectralMeasure π T) f hf hbdd).toCLM :=
    tendsto_nhds_unique hA' hB'
  exact hlim

lemma expUnitary_eq_expIntegral
    (π : Representation A H) (T : AffiliatedObservable A) (t : ℝ) :
    π (((T.expUnitary t : unitary A) : A)) =
      (QuantumMechanics.WOTSpectralMeasure.expIntegral
        (representedSpectralMeasure π T) t).toCLM := by
  change π (T.boundedFC
    (AffiliatedObservable.expFunction t)
    (AffiliatedObservable.expFunction_measurable t)
    (AffiliatedObservable.expFunction_bounded t)) = _
  exact boundedFC_eq_boundedIntegral π T
    (AffiliatedObservable.expFunction_measurable t)
    (AffiliatedObservable.expFunction_bounded t)

lemma resolvent_eq_boundedIntegral
    (π : Representation A H) (T : AffiliatedObservable A) (z : ℂ)
    (hz : z.im ≠ 0) :
    π (T.resolvent z hz) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (representedSpectralMeasure π T)
        (AffiliatedObservable.resolventFunction z)
        (AffiliatedObservable.resolventFunction_measurable z)
        (AffiliatedObservable.resolventFunction_bounded z hz)).toCLM := by
  change π (T.boundedFC
    (AffiliatedObservable.resolventFunction z)
    (AffiliatedObservable.resolventFunction_measurable z)
    (AffiliatedObservable.resolventFunction_bounded z hz)) = _
  exact boundedFC_eq_boundedIntegral π T
    (AffiliatedObservable.resolventFunction_measurable z)
    (AffiliatedObservable.resolventFunction_bounded z hz)

lemma truncate_eq_boundedIntegral
    (π : Representation A H) (T : AffiliatedObservable A) (R : ℝ) :
    π (T.truncate R) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (representedSpectralMeasure π T)
        (AffiliatedObservable.truncateFunction R)
        (AffiliatedObservable.truncateFunction_measurable R)
        (AffiliatedObservable.truncateFunction_bounded R)).toCLM := by
  change π (T.boundedFC
    (AffiliatedObservable.truncateFunction R)
    (AffiliatedObservable.truncateFunction_measurable R)
    (AffiliatedObservable.truncateFunction_bounded R)) = _
  exact boundedFC_eq_boundedIntegral π T
    (AffiliatedObservable.truncateFunction_measurable R)
    (AffiliatedObservable.truncateFunction_bounded R)

lemma boundedFC_indicator_eq_representedSpectralProjection
    (π : Representation A H) (T : AffiliatedObservable A)
    {S : Set ℝ} (hS : MeasurableSet S) :
    π (T.boundedFC (AffiliatedObservable.indicatorFunction S)
      (AffiliatedObservable.indicatorFunction_measurable hS)
      (AffiliatedObservable.indicatorFunction_bounded S)) =
      (representedSpectralMeasure π T S).toCLM := by
  rw [boundedFC_eq_boundedIntegral]
  have hI := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_indicator
    (μS := representedSpectralMeasure π T) hS
  have hI' := congrArg ContinuousLinearMapWOT.toCLM hI
  simpa [AffiliatedObservable.indicatorFunction] using hI'

end Representation

namespace AffiliationBridge

variable (bridge : AffiliationBridge A H)

lemma representedSpectralMeasure_toAffiliatedObservable_eq
    (T : ConcreteAffiliatedObservable ℝ H) :
    representedSpectralMeasure bridge.representation
        (bridge.toAffiliatedObservable T) = T.spectralMeasure := by
  exact representedSpectralMeasure_eq (bridge.toRepresentedAffiliatedObservable T)

end AffiliationBridge

namespace AffiliationBridge

variable (bridge : AffiliationBridge A H)

lemma representation_simpleIntegral_eq
    (T : ConcreteAffiliatedObservable ℝ H) (f : SimpleFunc ℝ ℂ) :
    bridge.representation
        ((bridge.toAffiliatedObservable T).simpleIntegral f : A) =
      (QuantumMechanics.WOTSpectralMeasure.simpleIntegral T.spectralMeasure f).toCLM := by
  unfold AffiliatedObservable.simpleIntegral
    QuantumMechanics.WOTSpectralMeasure.simpleIntegral
  rw [map_sum]
  have hsum : (∑ z ∈ f.range, z • T.spectralMeasure (f ⁻¹' {z})).toCLM =
      ∑ z ∈ f.range, (z • T.spectralMeasure (f ⁻¹' {z})).toCLM := by
    induction f.range using Finset.induction_on with
    | empty => rfl
    | @insert z s hz ih =>
      simp only [Finset.sum_insert hz, ContinuousLinearMapWOT.toCLM_add, ih]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [map_smul]
  change z • bridge.representation
      (bridge.toPVM T.spectralMeasure (f ⁻¹' {z}) : A) = _
  rw [bridge.toPVM_apply]
  rfl

lemma representation_boundedFC_eq_boundedIntegral
    (T : ConcreteAffiliatedObservable ℝ H) {f : ℝ → ℂ}
    (hf : Measurable f) (hbdd : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    bridge.representation
        ((bridge.toAffiliatedObservable T).boundedFC f hf hbdd) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral T.spectralMeasure f hf hbdd).toCLM := by
  let s : ℕ → SimpleFunc ℝ ℂ :=
    Classical.choose (AffiliatedObservable.exists_uniform_simple_approx hf hbdd)
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε :=
    (Classical.choose_spec (AffiliatedObservable.exists_uniform_simple_approx hf hbdd)).1
  have hsimple : ∀ n,
      bridge.representation
          ((bridge.toAffiliatedObservable T).simpleIntegral (s n)) =
        (QuantumMechanics.WOTSpectralMeasure.simpleIntegral T.spectralMeasure (s n)).toCLM :=
    fun n => bridge.representation_simpleIntegral_eq T (s n)
  have hA : Filter.Tendsto
      (fun n => bridge.representation
        ((bridge.toAffiliatedObservable T).simpleIntegral (s n))) Filter.atTop
      (𝓝 (bridge.representation
        (Filter.atTop.limUnder
          (fun n => (bridge.toAffiliatedObservable T).simpleIntegral (s n))))) := by
    have hC : CauchySeq
        (fun n => (bridge.toAffiliatedObservable T).simpleIntegral (s n)) :=
      AffiliatedObservable.simpleIntegral_cauchySeq _ hs
    have hlim := hC.tendsto_limUnder
    have hcont : Continuous (bridge.representation : A → B(H)) := by
      apply AddMonoidHomClass.continuous_of_bound bridge.representation 1
      intro a
      simpa using NonUnitalStarAlgHom.norm_apply_le bridge.representation a
    exact hcont.continuousAt.tendsto.comp hlim
  have hB : Filter.Tendsto
      (fun n => (QuantumMechanics.WOTSpectralMeasure.simpleIntegral T.spectralMeasure
        (s n)).toCLM) Filter.atTop
      (𝓝 (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        T.spectralMeasure f hf hbdd).toCLM) := by
    rw [QuantumMechanics.WOTSpectralMeasure.boundedIntegral_eq_of_uniform_approx
      T.spectralMeasure hf hbdd hs]
    rw [QuantumMechanics.WOTSpectralMeasure.boundedIntegralOfUniformApprox_eq_limUnder]
    exact (QuantumMechanics.WOTSpectralMeasure.simpleIntegral_toCLM_cauchySeq
      T.spectralMeasure hs).tendsto_limUnder
  have hA' : Filter.Tendsto
      (fun n => bridge.representation
        ((bridge.toAffiliatedObservable T).simpleIntegral (s n))) Filter.atTop
      (𝓝 (bridge.representation
        ((bridge.toAffiliatedObservable T).boundedFC f hf hbdd))) := by
    rw [AffiliatedObservable.boundedFC_eq_limUnder _ hf hbdd hs]
    exact hA
  have hB' : Filter.Tendsto
      (fun n => bridge.representation
        ((bridge.toAffiliatedObservable T).simpleIntegral (s n))) Filter.atTop
      (𝓝 (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        T.spectralMeasure f hf hbdd).toCLM) := by
    apply hB.congr'
    exact Filter.Eventually.of_forall (fun n => (hsimple n).symm)
  exact tendsto_nhds_unique hA' hB'

lemma representation_expUnitary_eq_expIntegral
    (T : ConcreteAffiliatedObservable ℝ H) (t : ℝ) :
    bridge.representation
        (((bridge.toAffiliatedObservable T).expUnitary t : unitary A) : A) =
      (QuantumMechanics.WOTSpectralMeasure.expIntegral T.spectralMeasure t).toCLM := by
  change bridge.representation
      ((bridge.toAffiliatedObservable T).boundedFC
        (AffiliatedObservable.expFunction t)
        (AffiliatedObservable.expFunction_measurable t)
        (AffiliatedObservable.expFunction_bounded t)) = _
  exact bridge.representation_boundedFC_eq_boundedIntegral T
    (AffiliatedObservable.expFunction_measurable t)
    (AffiliatedObservable.expFunction_bounded t)

lemma representation_resolvent_eq_boundedIntegral
    (T : ConcreteAffiliatedObservable ℝ H) (z : ℂ) (hz : z.im ≠ 0) :
    bridge.representation
        ((bridge.toAffiliatedObservable T).resolvent z hz) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral T.spectralMeasure
        (AffiliatedObservable.resolventFunction z)
        (AffiliatedObservable.resolventFunction_measurable z)
        (AffiliatedObservable.resolventFunction_bounded z hz)).toCLM := by
  change bridge.representation
      ((bridge.toAffiliatedObservable T).boundedFC
        (AffiliatedObservable.resolventFunction z)
        (AffiliatedObservable.resolventFunction_measurable z)
        (AffiliatedObservable.resolventFunction_bounded z hz)) = _
  exact bridge.representation_boundedFC_eq_boundedIntegral T
    (AffiliatedObservable.resolventFunction_measurable z)
    (AffiliatedObservable.resolventFunction_bounded z hz)

lemma representation_truncate_eq_boundedIntegral
    (T : ConcreteAffiliatedObservable ℝ H) (R : ℝ) :
    bridge.representation
        ((bridge.toAffiliatedObservable T).truncate R) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral T.spectralMeasure
        (AffiliatedObservable.truncateFunction R)
        (AffiliatedObservable.truncateFunction_measurable R)
        (AffiliatedObservable.truncateFunction_bounded R)).toCLM := by
  change bridge.representation
      ((bridge.toAffiliatedObservable T).boundedFC
        (AffiliatedObservable.truncateFunction R)
        (AffiliatedObservable.truncateFunction_measurable R)
        (AffiliatedObservable.truncateFunction_bounded R)) = _
  exact bridge.representation_boundedFC_eq_boundedIntegral T
    (AffiliatedObservable.truncateFunction_measurable R)
    (AffiliatedObservable.truncateFunction_bounded R)

/-! ### Strong convergence of represented spectral cutoffs

The abstract cutoff is an element of the represented algebra, while the unbounded operator is
only defined on its square-moment domain. The correct compatibility statement is therefore
strong convergence on each vector in that domain, not norm convergence of bounded operators. -/

lemma representation_truncate_apply_tendsto
    (T : ConcreteAffiliatedObservable ℝ H) (x : H)
    (hx : x ∈ OperatorAlgebra.spectralSquareMomentDomain T.spectralMeasure) :
    Filter.Tendsto
      (fun n : ℕ => bridge.representation
        ((bridge.toAffiliatedObservable T).truncate n) x)
      Filter.atTop
      (𝓝 (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
        T.spectralMeasure
          (⟨x, hx⟩ : QuantumMechanics.WOTSpectralMeasure.spectralSquareMomentSubmodule
            T.spectralMeasure))) := by
  have hlim := QuantumMechanics.WOTSpectralMeasure.truncationLimit_tendsto
    T.spectralMeasure
      (⟨x, hx⟩ : QuantumMechanics.WOTSpectralMeasure.spectralSquareMomentSubmodule
        T.spectralMeasure)
  have hlim' : Filter.Tendsto
      (fun n : ℕ => QuantumMechanics.WOTSpectralMeasure.truncationIntegral
        T.spectralMeasure n x)
      Filter.atTop
      (𝓝 (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
        T.spectralMeasure
          (⟨x, hx⟩ : QuantumMechanics.WOTSpectralMeasure.spectralSquareMomentSubmodule
            T.spectralMeasure))) := by
    simpa [QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral,
      QuantumMechanics.WOTSpectralMeasure.truncationLimit] using hlim
  apply hlim'.congr'
  filter_upwards [] with n
  have hrep := bridge.representation_boundedFC_eq_boundedIntegral T
    (AffiliatedObservable.truncateFunction_measurable n)
    (AffiliatedObservable.truncateFunction_bounded n)
  have happly := congrArg (fun L : B(H) => L x) hrep
  have hfun : AffiliatedObservable.truncateFunction (n : ℝ) =
      QuantumMechanics.WOTSpectralMeasure.truncationFunction n := by
    funext r
    simp [AffiliatedObservable.truncateFunction,
      QuantumMechanics.WOTSpectralMeasure.truncationFunction]
  have hB := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_congr
    (μS := T.spectralMeasure)
    (AffiliatedObservable.truncateFunction_measurable n)
    (QuantumMechanics.WOTSpectralMeasure.truncationFunction_measurable n)
    (AffiliatedObservable.truncateFunction_bounded n)
    (QuantumMechanics.WOTSpectralMeasure.truncationFunction_bounded n)
    (fun r => congrFun hfun r)
  calc
    (T.spectralMeasure.boundedIntegral
        (QuantumMechanics.WOTSpectralMeasure.truncationFunction n) _ _).toCLM x =
      (T.spectralMeasure.boundedIntegral
        (AffiliatedObservable.truncateFunction (n : ℝ)) _ _).toCLM x := by
        exact congrArg (fun L : H →WOT[ℂ] H => L.toCLM x) hB.symm
    _ = bridge.representation
        ((bridge.toAffiliatedObservable T).truncate (n : ℝ)) x := by
      simpa [AffiliatedObservable.truncate] using happly.symm

end AffiliationBridge

/-! ## The represented unbounded operator -/

/-- The canonical (maximal square-moment) closed self-adjoint operator represented by an
`AffiliatedObservable`, obtained as the unbounded spectral integral of its represented WOT
spectral measure. -/
noncomputable def representedSelfAdjointOperator
    (π : Representation A H) (T : AffiliatedObservable A) : H →ₗ.[ℂ] H :=
  QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
    (representedSpectralMeasure π T)

lemma representedSelfAdjointOperator_measurableRealFC
    (π : Representation A H) (T : AffiliatedObservable A)
    {f : ℝ → ℝ} (hf : Measurable f) :
    representedSelfAdjointOperator π (T.measurableRealFC f hf) =
      QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
        ((representedSpectralMeasure π T).map f hf) := by
  change QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
      (representedSpectralMeasure π (T.measurableRealFC f hf)) = _
  rw [representedMeasurableRealFC_eq_map]

/-- The represented real measurable functional calculus is the canonical unbounded spectral
integral of the pushed-forward represented PVM.

This is an operator-level compatibility theorem: it includes the exact square-moment domain
because `measurableSpectralIntegral` is the maximal `LinearPMap` attached to that domain, rather
than merely an equality of matrix coefficients. -/
theorem representedSelfAdjointOperator_measurableRealFC_eq_measurableSpectralIntegral
    (π : Representation A H) (T : AffiliatedObservable A)
    {f : ℝ → ℝ} (hf : Measurable f) :
    representedSelfAdjointOperator π (T.measurableRealFC f hf) =
      QuantumMechanics.WOTSpectralMeasure.measurableSpectralIntegral
        (representedSpectralMeasure π T) f hf := by
  exact representedSelfAdjointOperator_measurableRealFC π T hf

lemma representedSelfAdjointOperator_isSelfAdjoint
    (π : Representation A H) (T : AffiliatedObservable A) :
    IsSelfAdjoint (representedSelfAdjointOperator π T) := by
  exact QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_isSelfAdjoint _

lemma representedSelfAdjointOperator_domain
    (π : Representation A H) (T : AffiliatedObservable A) :
    (representedSelfAdjointOperator π T).domain =
      spectralSquareMomentDomain (representedSpectralMeasure π T) := by
  rfl

lemma representedSelfAdjointOperator_measurableRealFC_domain
    (π : Representation A H) (T : AffiliatedObservable A)
    {f : ℝ → ℝ} (hf : Measurable f) :
    (representedSelfAdjointOperator π (T.measurableRealFC f hf)).domain =
      spectralSquareMomentDomain ((representedSpectralMeasure π T).map f hf) := by
  rw [representedSelfAdjointOperator_domain,
    representedMeasurableRealFC_eq_map]

lemma representedSelfAdjointOperator_closure
    (π : Representation A H) (T : AffiliatedObservable A) :
    (representedSelfAdjointOperator π T).closure =
      representedSelfAdjointOperator π T := by
  exact (representedSelfAdjointOperator_isSelfAdjoint π T).isClosed.closure_eq

/-- The represented maximal self-adjoint operator is compatible with the `StarAlgEquiv` transport:
representing along the composed map `π.comp β.toStarAlgHom` gives the same unbounded operator as
transporting `T` along `β` first and then representing along `π`. -/
theorem representedSelfAdjointOperator_starAlgEquiv
    {B : Type*} [OperatorAlgebra B]
    (β : A ≃⋆ₐ[ℂ] B) (π : Representation B H) (T : AffiliatedObservable A) :
    representedSelfAdjointOperator (π.comp β.toStarAlgHom) T =
      representedSelfAdjointOperator π (β.affiliatedObservable T) := by
  unfold representedSelfAdjointOperator
  rw [representedSpectralMeasure_starAlgEquiv]

lemma representedSelfAdjointOperator_of_represented
    (R : RepresentedAffiliatedObservable A H) :
    representedSelfAdjointOperator R.representation R.observable =
      QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral R.spectralMeasure := by
  change QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
      (representedSpectralMeasure R.representation R.observable) = _
  rw [representedSpectralMeasure_eq R]

/-! ## Uniqueness of the represented realization

The maximal square-moment operator is canonical. This theorem exposes that fact directly at the
representation boundary: a self-adjoint operator with the represented weak spectral resolution and
the expected domain inclusion is necessarily the operator represented by the affiliated object.
Thus users do not have to mention the internal maximal-integral construction when proving equality
of two concrete realizations.
-/

theorem representedSelfAdjointOperator_eq_of_isWeakSpectralResolution
    (π : Representation A H) (T : AffiliatedObservable A)
    (S : H →ₗ.[ℂ] H) (hS : IsSelfAdjoint S)
    (hres : IsWeakSpectralResolution S (representedSpectralMeasure π T))
    (hdom : ∀ x : S.domain,
      (x : H) ∈ spectralSquareMomentDomain (representedSpectralMeasure π T)) :
    representedSelfAdjointOperator π T = S := by
  change QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
      (representedSpectralMeasure π T) = S
  exact QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution
    S hS hres hdom

theorem representedSelfAdjointOperator_eq_of_domainAware
    (R : RepresentedAffiliatedObservable A H)
    (S : H →ₗ.[ℂ] H)
    (D : DomainAwareSelfAdjointSpectralTheorem S R.spectralMeasure) :
    representedSelfAdjointOperator R.representation R.observable = S := by
  rw [representedSelfAdjointOperator_of_represented R]
  exact D.maximal_eq

namespace AffiliationBridge

variable (bridge : AffiliationBridge A H)

lemma representedSelfAdjointOperator_toAffiliatedObservable_eq
    (T : ConcreteAffiliatedObservable ℝ H) :
    representedSelfAdjointOperator bridge.representation
        (bridge.toAffiliatedObservable T) =
      QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral T.spectralMeasure := by
  change QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
      (representedSpectralMeasure bridge.representation (bridge.toAffiliatedObservable T)) = _
  rw [bridge.representedSpectralMeasure_toAffiliatedObservable_eq T]

end AffiliationBridge

namespace EssentialSelfAdjointSpectralData

variable {T : H →ₗ.[ℂ] H} (D : EssentialSelfAdjointSpectralData T)

lemma representation_expUnitary_eq_expIntegral
    {A : Type*} [OperatorAlgebra A] (bridge : AffiliationBridge A H) (t : ℝ) :
    bridge.representation
        (((D.toAffiliatedObservable bridge).expUnitary t : unitary A) : A) =
      (QuantumMechanics.WOTSpectralMeasure.expIntegral D.spectralMeasure t).toCLM := by
  exact bridge.representation_expUnitary_eq_expIntegral D.toConcreteAffiliatedObservable t

end EssentialSelfAdjointSpectralData

namespace DomainAwareSelfAdjointSpectralTheorem

variable {T : H →ₗ.[ℂ] H} {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

/-- Recover a given domain-aware self-adjoint realization from its affiliated spectral data.

This is the packaged concrete-to-abstract bridge: `bridge.toAffiliatedObservable ⟨μS⟩` stores the
same spectral projections in the abstract algebra, while the representation sends them back to
the original WOT spectral measure. The domain-aware uniqueness theorem then identifies the
represented maximal square-moment operator with the supplied operator `T`. -/
theorem representedSelfAdjointOperator_eq
    (D : DomainAwareSelfAdjointSpectralTheorem T μS)
    {A : Type*} [OperatorAlgebra A] (bridge : AffiliationBridge A H) :
    representedSelfAdjointOperator bridge.representation
        (bridge.toAffiliatedObservable ⟨μS⟩) = T := by
  rw [bridge.representedSelfAdjointOperator_toAffiliatedObservable_eq ⟨μS⟩]
  exact D.maximal_eq

lemma representation_expUnitary_eq_expUnitaryGroup
    (D : DomainAwareSelfAdjointSpectralTheorem T μS)
    {A : Type*} [OperatorAlgebra A] (bridge : AffiliationBridge A H) (t : ℝ) :
    bridge.representation
        (((bridge.toAffiliatedObservable ⟨μS⟩).expUnitary t : unitary A) : A) =
      (D.expUnitaryGroup t).toCLM := by
  exact bridge.representation_expUnitary_eq_expIntegral ⟨μS⟩ t

end DomainAwareSelfAdjointSpectralTheorem

end OperatorAlgebra

end
