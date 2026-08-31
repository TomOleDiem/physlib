/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Representation.NormalRepresentation
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.VectorState
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.WStarAlgebra.InfiniteDimensional
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Calculus.WeakStarFunctionalCalculus

/-!
# The concrete normal representation of `B(H)`

The identity action of the bounded operators on a complete Hilbert space is the basic faithful
normal representation.  The concrete predual pairing proved in
`WStarAlgebra.TracePairingSurjectivity` represents matrix coefficients by rank-one trace-class
operators; `NormalPVMTraceClass.lean` extends the resulting σ-additivity to every completed
trace-class functional and supplies the reusable normal-affiliation bridges for both real and
complex spectral data.

No finite-dimensional hypothesis is used here.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra InnerProductSpace Topology
open OperatorAlgebra
open MeasureTheory Set Filter

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace BoundedOperatorsNormalRepresentation

/-- The identity representation of `B(H)` on `H`. -/
def representation : Representation (B(H)) H :=
  StarAlgHom.id ℂ B(H)

@[simp]
lemma representation_apply (a : B(H)) : representation (H := H) a = a := rfl

/-- The vector state on `B(H)` is weak-star continuous for the trace-class predual. -/
noncomputable def normalVectorState (x : H) (hx : ‖x‖ = 1) : NormalState (B(H)) where
  toState := vectorState x hx
  weakStar_continuous := by
    change Continuous[WStarAlgebra.weakStarTopology (B(H)), inferInstance]
      (fun a : B(H) => ⟪x, a x⟫_ℂ)
    have h := WStarAlgebra.predualPairing_weakStar_continuous
      (A := B(H)) (TraceClass.rankOneTraceClass x x)
    have heq : (fun a : B(H) => ⟪x, a x⟫_ℂ) =
        WStarAlgebra.predualPairing (TraceClass.rankOneTraceClass x x) := by
      funext a
      symm
      change TraceClass.tracePairing a (TraceClass.rankOneTraceClass x x) = _
      exact TraceClass.tracePairing_rankOne a x x
    rw [heq]
    exact h

@[simp]
lemma normalVectorState_apply (x : H) (hx : ‖x‖ = 1) (a : B(H)) :
    normalVectorState x hx a = ⟪x, a x⟫_ℂ := rfl

/-- Normality of every unit-vector state for the concrete trace-class predual. -/
noncomputable def vectorStateCertificate :
    NormalPVM.NormalVectorStateCertificate (representation (H := H)) where
  state := fun x hx => normalVectorState x hx
  apply := by
    intro x hx a
    change normalVectorState x hx a = ⟪x, representation (H := H) a x⟫_ℂ
    simp [representation]

@[simp]
lemma vectorStateCertificate_apply (x : H) (hx : ‖x‖ = 1) (a : B(H)) :
    (vectorStateCertificate (H := H)).state x hx a = ⟪x, a x⟫_ℂ := by
  change normalVectorState x hx a = _
  rfl

/-- Matrix coefficients of the identity representation, represented by rank-one trace-class
operators. -/
noncomputable def predualMatrixCoefficientCertificate :
    NormalPVM.PredualMatrixCoefficientCertificate (representation (H := H)) where
  coefficient := fun x y => TraceClass.rankOneTraceClass x y
  apply := by
    intro x y a
    change WStarAlgebra.predualPairing (TraceClass.rankOneTraceClass x y) a = _
    change TraceClass.tracePairing a (TraceClass.rankOneTraceClass x y) = _
    exact TraceClass.tracePairing_rankOne a x y

@[simp]
lemma predualMatrixCoefficientCertificate_apply (x y : H) (a : B(H)) :
    WStarAlgebra.predualPairing
        ((predualMatrixCoefficientCertificate (H := H)).coefficient x y) a =
      ⟪y, a x⟫_ℂ := by
  exact (predualMatrixCoefficientCertificate (H := H)).apply x y a

/-- The identity representation equipped with its proved weak-star continuity of matrix
coefficients.  This is the canonical input to the representation-level normality API. -/
noncomputable def normalRepresentation : NormalRepresentation (A := B(H)) (H := H) :=
  NormalRepresentation.ofPredualMatrixCoefficientCertificate
    (representation (H := H)) (predualMatrixCoefficientCertificate (H := H))

@[simp]
lemma normalRepresentation_apply (a : B(H)) :
    (normalRepresentation (H := H)).representation a = a := rfl

/-- The generic normal-representation constructor recovers a faithful affiliation bridge for
`B(H)`.  The trace-class-specific bridge remains available when a predual-PVM lift is useful. -/
noncomputable def normalRepresentationAffiliationBridge :
    FaithfulNormalAffiliationBridge (A := B(H)) (H := H) :=
  (normalRepresentation (H := H)).toFaithfulNormalAffiliationBridge (by
    intro a b h
    change a = b at h
    exact h)

/-! ### Automatic concrete PVM conversion -/

/-- Convert any normal-functional PVM in `B(H)` to its weak-operator spectral measure under the
identity representation.  The countable-additivity proof is supplied by the trace-class
representation of matrix coefficients above. -/
noncomputable def normalPVMToWOTSpectralMeasure
    {X : Type*} [MeasurableSpace X] (E : NormalPVM X (B(H))) :
    QuantumMechanics.WOTSpectralMeasure X H :=
  NormalPVM.toWOTSpectralMeasure E (representation (H := H))
    (NormalPVM.isWOTCountablyAdditive_of_normalVectorStateCertificate E
      (representation (H := H)) (vectorStateCertificate (H := H)))

@[simp]
lemma normalPVM_toWOTSpectralMeasure_apply
    {X : Type*} [MeasurableSpace X] (E : NormalPVM X (B(H))) (S : Set X) :
    normalPVMToWOTSpectralMeasure E S =
      ContinuousLinearMapWOT.ofCLM (E S) := by
  rw [normalPVMToWOTSpectralMeasure, NormalPVM.toWOTSpectralMeasure_apply]
  rfl

/-! ### Trace-class additivity on finite-rank functionals

The WOT construction already contains the full matrix-coefficient series.  The following lemma
exposes that fact through the concrete trace-class predual: it is the rank-one calculation needed
before extending the result by trace-norm density to arbitrary predual vectors. -/

/-- A normal PVM on `B(H)` is countably additive against every rank-one trace-class functional. -/
lemma normalPVM_predual_m_iUnion_rankOne
    {X : Type*} [MeasurableSpace X] (E : NormalPVM X (B(H)))
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j))) (x y : H) :
    HasSum
      (fun n => WStarAlgebra.predualPairing
        (TraceClass.rankOneTraceClass x y) (E (s n)))
      (WStarAlgebra.predualPairing
        (TraceClass.rankOneTraceClass x y) (E (⋃ n, s n))) := by
  let g : (H →WOT[ℂ] H) →+ ℂ :=
    { toFun := fun T => ⟪y, T x⟫_ℂ
      map_zero' := by simp
      map_add' := by
        intro T U
        change ⟪y, T x + U x⟫_ℂ = _
        rw [inner_add_right] }
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hsum := (normalPVMToWOTSpectralMeasure E).toVectorMeasure.m_iUnion hs hdisj
  have hsum' := hsum.map g hg
  change HasSum
      (fun n => g (normalPVMToWOTSpectralMeasure E (s n)))
      (g (normalPVMToWOTSpectralMeasure E (⋃ n, s n))) at hsum'
  have hterm (S : Set X) :
      g (normalPVMToWOTSpectralMeasure E S) =
        WStarAlgebra.predualPairing (TraceClass.rankOneTraceClass x y) (E S) := by
    rw [normalPVM_toWOTSpectralMeasure_apply]
    change ⟪y, (E S) x⟫_ℂ = _
    rw [WStarAlgebra.predualPairing_apply]
    change ⟪y, (E S) x⟫_ℂ =
      TraceClass.tracePairing (E S) (TraceClass.rankOneTraceClass x y)
    rw [TraceClass.tracePairing_rankOne]
  convert hsum' using 1
  · funext n
    exact (hterm (s n)).symm
  · exact (hterm (⋃ n, s n)).symm

/-! The finite-rank span follows by the linearity of `HasSum`.  This is deliberately stated for
the concrete rank-one span rather than pretending that WOT additivity alone has already supplied
the completion step for arbitrary trace-class operators. -/

set_option maxHeartbeats 1000000 in
/-- A normal PVM on `B(H)` is countably additive against every finite linear combination of
rank-one trace-class functionals. -/
lemma normalPVM_predual_m_iUnion_of_rankOneSpan
    {X : Type*} [MeasurableSpace X] (E : NormalPVM X (B(H)))
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j)))
    {ξ : TraceClass H} (hξ : ξ ∈ TraceClass.rankOneSpan (H := H)) :
    HasSum
      (fun n => WStarAlgebra.predualPairing ξ (E (s n)))
      (WStarAlgebra.predualPairing ξ (E (⋃ n, s n))) := by
  let p : TraceClass H → Prop := fun ζ ↦
    HasSum
      (fun n => WStarAlgebra.predualPairing ζ (E (s n)))
      (WStarAlgebra.predualPairing ζ (E (⋃ n, s n)))
  change ξ ∈ Submodule.span ℂ {T : TraceClass H |
    ∃ x y : H, T.1 = InnerProductSpace.rankOne ℂ x y} at hξ
  have hp : ∀ ζ, ζ ∈ Submodule.span ℂ
      {T : TraceClass H | ∃ x y : H, T.1 = InnerProductSpace.rankOne ℂ x y} → p ζ := by
    intro ζ hζ
    refine Submodule.span_induction (R := ℂ)
      (s := {T : TraceClass H | ∃ x y : H, T.1 = InnerProductSpace.rankOne ℂ x y})
      (p := fun η _ ↦ p η) ?_ ?_ ?_ ?_ hζ
    · rintro η ⟨x, y, hη⟩
      have hη' : η = TraceClass.rankOneTraceClass x y := by
        apply Subtype.ext
        exact hη
      rw [hη']
      exact normalPVM_predual_m_iUnion_rankOne E s hs hdisj x y
    · simpa [p] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) (0 : ℂ))
    · intro η θ _ _ hη hθ
      simpa only [p, WStarAlgebra.predualPairing_apply, map_add, add_apply] using hη.add hθ
    · intro c η _ hη
      simpa only [p, WStarAlgebra.predualPairing_apply, map_smul, smul_eq_mul] using
        hη.const_smul c
  exact hp ξ hξ

/-- The predual-functional route to the same concrete PVM conversion.  This form is useful when
the source PVM already carries its σ-additivity witness against the chosen trace-class predual. -/
noncomputable def predualPVMToWOTSpectralMeasure
    {X : Type*} [MeasurableSpace X] (E : PredualPVM X (B(H))) :
    QuantumMechanics.WOTSpectralMeasure X H :=
  NormalPVM.toWOTSpectralMeasureOfPredual E (representation (H := H))
    (predualMatrixCoefficientCertificate (H := H))

@[simp]
lemma predualPVM_toWOTSpectralMeasure_apply
    {X : Type*} [MeasurableSpace X] (E : PredualPVM X (B(H))) (S : Set X) :
    predualPVMToWOTSpectralMeasure E S =
      ContinuousLinearMapWOT.ofCLM (E S) := by
  rw [predualPVMToWOTSpectralMeasure,
    NormalPVM.toWOTSpectralMeasure_of_predual_apply]
  rfl

/-! ### Representation of the completed bounded calculus -/

/-- A representation bridge carries finite normal-PVM integrals to the corresponding WOT finite
integrals. -/
lemma simpleIntegral_eq_boundedIntegral
    {A : Type*} [WStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (bridge : NormalAffiliationBridge (A := A) (H := H))
    (E : NormalPVM ℝ A) (f : SimpleFunc ℝ ℂ) :
    bridge.representation (NormalPVM.simpleIntegral E f) =
      (QuantumMechanics.WOTSpectralMeasure.simpleIntegral
        (bridge.toWOTSpectralMeasure E) f).toCLM := by
  unfold NormalPVM.simpleIntegral QuantumMechanics.WOTSpectralMeasure.simpleIntegral
  rw [map_sum]
  have hsum :
      (∑ z ∈ f.range, z • (bridge.toWOTSpectralMeasure E) (f ⁻¹' {z})).toCLM =
        ∑ z ∈ f.range,
          (z • (bridge.toWOTSpectralMeasure E) (f ⁻¹' {z})).toCLM := by
    induction f.range using Finset.induction_on with
    | empty => rfl
    | @insert z s hz ih =>
        simp only [Finset.sum_insert hz, ContinuousLinearMapWOT.toCLM_add, ih]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [map_smul]
  change z • bridge.representation (E (f ⁻¹' {z})) = _
  rw [bridge.toWOTSpectralMeasure_apply]
  rfl

/-- The canonical normal Borel calculus is represented by the completed WOT spectral integral.
This is the general bridge theorem needed by the affiliation layer; it uses only continuity of the
star-representation and the common uniform simple-function approximation, not norm countable
additivity of the source `NormalPVM`. -/
theorem represented_boundedFC_eq_boundedIntegral
    {A : Type*} [WStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (bridge : NormalAffiliationBridge (A := A) (H := H))
    (E : NormalPVM ℝ A) {f : ℝ → ℂ} (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    bridge.representation
        ((NormalBorelFunctionalCalculus.ofNormalPVM E).boundedFC f hf hfb) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasure E) f hf hfb).toCLM := by
  classical
  let s : ℕ → SimpleFunc ℝ ℂ :=
    Classical.choose (exists_uniform_simpleFunc_approx hf hfb)
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε :=
    (Classical.choose_spec (exists_uniform_simpleFunc_approx hf hfb)).1
  have hsimple : ∀ n,
      bridge.representation (NormalPVM.simpleIntegral E (s n)) =
        (QuantumMechanics.WOTSpectralMeasure.simpleIntegral
          (bridge.toWOTSpectralMeasure E) (s n)).toCLM :=
    fun n => simpleIntegral_eq_boundedIntegral bridge E (s n)
  have hA : Filter.Tendsto
      (fun n => bridge.representation (NormalPVM.simpleIntegral E (s n))) Filter.atTop
      (𝓝 (bridge.representation
        (Filter.atTop.limUnder (fun n => NormalPVM.simpleIntegral E (s n))))) := by
    have hC : CauchySeq (fun n => NormalPVM.simpleIntegral E (s n)) :=
      NormalPVM.simpleIntegral_cauchySeq E hs
    have hlim := hC.tendsto_limUnder
    have hcont : Continuous (bridge.representation : A → B(H)) := by
      apply AddMonoidHomClass.continuous_of_bound bridge.representation 1
      intro a
      simpa using NonUnitalStarAlgHom.norm_apply_le bridge.representation a
    exact hcont.continuousAt.tendsto.comp hlim
  have hB : Filter.Tendsto
      (fun n =>
        (QuantumMechanics.WOTSpectralMeasure.simpleIntegral
          (bridge.toWOTSpectralMeasure E) (s n)).toCLM) Filter.atTop
      (𝓝 (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasure E) f hf hfb).toCLM) := by
    rw [QuantumMechanics.WOTSpectralMeasure.boundedIntegral_eq_of_uniform_approx
      (bridge.toWOTSpectralMeasure E) hf hfb hs]
    rw [QuantumMechanics.WOTSpectralMeasure.boundedIntegralOfUniformApprox_eq_limUnder]
    exact (QuantumMechanics.WOTSpectralMeasure.simpleIntegral_toCLM_cauchySeq
      (bridge.toWOTSpectralMeasure E) hs).tendsto_limUnder
  have hA' : Filter.Tendsto
      (fun n => bridge.representation (NormalPVM.simpleIntegral E (s n))) Filter.atTop
      (𝓝 (bridge.representation
        ((NormalBorelFunctionalCalculus.ofNormalPVM E).boundedFC f hf hfb))) := by
    change Filter.Tendsto
      (fun n => bridge.representation (NormalPVM.simpleIntegral E (s n))) Filter.atTop
      (𝓝 (bridge.representation (E.boundedFC f hf hfb)))
    rw [NormalPVM.boundedFC_eq_limUnder E hf hfb hs]
    exact hA
  have hB' : Filter.Tendsto
      (fun n => bridge.representation (NormalPVM.simpleIntegral E (s n))) Filter.atTop
      (𝓝 (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasure E) f hf hfb).toCLM) := by
    apply hB.congr'
    exact Filter.Eventually.of_forall (fun n => (hsimple n).symm)
  exact tendsto_nhds_unique hA' hB'

/-! ### The complex normal-PVM analogue -/

/-- Finite complex normal-PVM integrals are carried to the corresponding complex WOT integrals.
This is the same finite-sum argument as `simpleIntegral_eq_boundedIntegral`, with the spectral
space made explicit so it can be used by `NormalOperatorAffiliationBridge`. -/
lemma simpleIntegral_eq_boundedIntegralComplex
    {A : Type*} [WStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (bridge : NormalOperatorAffiliationBridge (A := A) (H := H))
    (E : NormalPVM ℂ A) (f : SimpleFunc ℂ ℂ) :
    bridge.representation (NormalPVM.simpleIntegral E f) =
      (QuantumMechanics.WOTSpectralMeasure.simpleIntegral
        (bridge.toWOTSpectralMeasureComplex E) f).toCLM := by
  unfold NormalPVM.simpleIntegral QuantumMechanics.WOTSpectralMeasure.simpleIntegral
  rw [map_sum]
  have hsum :
      (∑ z ∈ f.range, z • (bridge.toWOTSpectralMeasureComplex E) (f ⁻¹' {z})).toCLM =
        ∑ z ∈ f.range,
          (z • (bridge.toWOTSpectralMeasureComplex E) (f ⁻¹' {z})).toCLM := by
    induction f.range using Finset.induction_on with
    | empty => rfl
    | @insert z s hz ih =>
        simp only [Finset.sum_insert hz, ContinuousLinearMapWOT.toCLM_add, ih]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro z hz
  rw [map_smul]
  change z • bridge.representation (E (f ⁻¹' {z})) = _
  rw [bridge.toWOTSpectralMeasureComplex_apply]
  rfl

/-- The canonical normal Borel calculus for a complex normal PVM is represented by the completed
WOT spectral integral.  Thus arbitrary bounded measurable complex functional calculus is
available from a `NormalOperatorAffiliationBridge` without a separately supplied calculus
certificate. -/
theorem represented_boundedFCComplex_eq_boundedIntegral
    {A : Type*} [WStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (bridge : NormalOperatorAffiliationBridge (A := A) (H := H))
    (E : NormalPVM ℂ A) {f : ℂ → ℂ} (hf : Measurable f)
    (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    bridge.representation
        ((NormalBorelFunctionalCalculus.ofNormalPVM E).boundedFC f hf hfb) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasureComplex E) f hf hfb).toCLM := by
  classical
  let s : ℕ → SimpleFunc ℂ ℂ :=
    Classical.choose (exists_uniform_simpleFunc_approx hf hfb)
  have hs : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, ‖s n x - f x‖ < ε :=
    (Classical.choose_spec (exists_uniform_simpleFunc_approx hf hfb)).1
  have hsimple : ∀ n,
      bridge.representation (NormalPVM.simpleIntegral E (s n)) =
        (QuantumMechanics.WOTSpectralMeasure.simpleIntegral
          (bridge.toWOTSpectralMeasureComplex E) (s n)).toCLM :=
    fun n => simpleIntegral_eq_boundedIntegralComplex bridge E (s n)
  have hA : Filter.Tendsto
      (fun n => bridge.representation (NormalPVM.simpleIntegral E (s n))) Filter.atTop
      (𝓝 (bridge.representation
        (Filter.atTop.limUnder (fun n => NormalPVM.simpleIntegral E (s n))))) := by
    have hC : CauchySeq (fun n => NormalPVM.simpleIntegral E (s n)) :=
      NormalPVM.simpleIntegral_cauchySeq E hs
    have hlim := hC.tendsto_limUnder
    have hcont : Continuous (bridge.representation : A → B(H)) := by
      apply AddMonoidHomClass.continuous_of_bound bridge.representation 1
      intro a
      simpa using NonUnitalStarAlgHom.norm_apply_le bridge.representation a
    exact hcont.continuousAt.tendsto.comp hlim
  have hB : Filter.Tendsto
      (fun n =>
        (QuantumMechanics.WOTSpectralMeasure.simpleIntegral
          (bridge.toWOTSpectralMeasureComplex E) (s n)).toCLM) Filter.atTop
      (𝓝 (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasureComplex E) f hf hfb).toCLM) := by
    rw [QuantumMechanics.WOTSpectralMeasure.boundedIntegral_eq_of_uniform_approx
      (bridge.toWOTSpectralMeasureComplex E) hf hfb hs]
    rw [QuantumMechanics.WOTSpectralMeasure.boundedIntegralOfUniformApprox_eq_limUnder]
    exact (QuantumMechanics.WOTSpectralMeasure.simpleIntegral_toCLM_cauchySeq
      (bridge.toWOTSpectralMeasureComplex E) hs).tendsto_limUnder
  have hA' : Filter.Tendsto
      (fun n => bridge.representation (NormalPVM.simpleIntegral E (s n))) Filter.atTop
      (𝓝 (bridge.representation
        ((NormalBorelFunctionalCalculus.ofNormalPVM E).boundedFC f hf hfb))) := by
    change Filter.Tendsto
      (fun n => bridge.representation (NormalPVM.simpleIntegral E (s n))) Filter.atTop
      (𝓝 (bridge.representation (E.boundedFC f hf hfb)))
    rw [NormalPVM.boundedFC_eq_limUnder E hf hfb hs]
    exact hA
  have hB' : Filter.Tendsto
      (fun n => bridge.representation (NormalPVM.simpleIntegral E (s n))) Filter.atTop
      (𝓝 (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasureComplex E) f hf hfb).toCLM) := by
    apply hB.congr'
    exact Filter.Eventually.of_forall (fun n => (hsimple n).symm)
  exact tendsto_nhds_unique hA' hB'

/-! ### The generic certificate constructor -/

/-- Every `NormalAffiliationBridge` automatically carries the compatibility certificate for the
canonical normal Borel calculus.  The bridge still records the genuinely external normality fact
that its PVM values form a WOT spectral measure; no additional calculus witness is needed. -/
noncomputable def NormalBorelRepresentationWitness.ofBridge
    {A H : Type*} [WStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (bridge : NormalAffiliationBridge (A := A) (H := H)) :
    NormalBorelRepresentationWitness bridge where
  represented_boundedFC := by
    intro E f hf hfb
    exact represented_boundedFC_eq_boundedIntegral bridge E hf hfb

/-- The full canonical-calculus representation certificate associated with a normal bridge. -/
noncomputable def NormalBorelRepresentationCertificate.ofBridge
    {A H : Type*} [WStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (bridge : NormalAffiliationBridge (A := A) (H := H)) :
    NormalBorelRepresentationCertificate bridge :=
  (NormalBorelRepresentationWitness.ofBridge bridge).certificate

/-- Every real-and-complex normal bridge automatically supplies the compatibility witness for
both canonical bounded Borel calculi. -/
noncomputable def NormalOperatorBorelRepresentationWitness.ofBridge
    {A H : Type*} [WStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (bridge : NormalOperatorAffiliationBridge (A := A) (H := H)) :
    NormalOperatorBorelRepresentationWitness bridge where
  real := NormalBorelRepresentationWitness.ofBridge bridge.toNormalAffiliationBridge
  represented_boundedFCComplex := by
    intro E f hf hfb
    exact represented_boundedFCComplex_eq_boundedIntegral bridge E hf hfb

/-- The full canonical real-and-complex representation certificate associated with a normal
operator bridge.  Both calculus components are constructed by `ofNormalPVM`; the only input used
by the construction is the bridge's proved finite/simple-integral compatibility. -/
noncomputable def NormalOperatorBorelRepresentationCertificate.ofBridge
    {A H : Type*} [WStarAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (bridge : NormalOperatorAffiliationBridge (A := A) (H := H)) :
    NormalOperatorBorelRepresentationCertificate bridge :=
  (NormalOperatorBorelRepresentationWitness.ofBridge bridge).certificate

/-- A faithful normal bridge for real normal PVMs on `B(H)`. -/
noncomputable def affiliationBridge :
    FaithfulNormalAffiliationBridge (A := B(H)) (H := H) :=
  NormalAffiliationBridge.ofFaithfulNormalVectorStateCertificate
    (representation (H := H)) (vectorStateCertificate (H := H)) (by
      intro a b h
      change a = b at h
      exact h)

/-- A faithful normal bridge for both real and complex normal PVMs on `B(H)`. -/
noncomputable def operatorAffiliationBridge :
    FaithfulNormalOperatorAffiliationBridge (A := B(H)) (H := H) :=
  NormalOperatorAffiliationBridge.ofFaithfulNormalVectorStateCertificate
    (representation (H := H)) (vectorStateCertificate (H := H)) (by
      intro a b h
      change a = b at h
      exact h)

/-! ### The ready-made real-and-complex Borel representation package -/

/-- The identity representation of `B(H)` satisfies the canonical real-and-complex Borel
representation compatibility theorem for every normal PVM. -/
noncomputable def operatorBorelRepresentationWitness :
    NormalOperatorBorelRepresentationWitness
      (operatorAffiliationBridge (H := H)).toNormalOperatorAffiliationBridge :=
  NormalOperatorBorelRepresentationWitness.ofBridge
    (operatorAffiliationBridge (H := H)).toNormalOperatorAffiliationBridge

/-- The corresponding full real-and-complex certificate, with both canonical calculi selected
automatically. -/
noncomputable def operatorBorelRepresentationCertificate :
    NormalOperatorBorelRepresentationCertificate
      (operatorAffiliationBridge (H := H)).toNormalOperatorAffiliationBridge :=
  (operatorBorelRepresentationWitness (H := H)).certificate

/-! ### The ready-made real Borel representation package -/

/-- The identity representation of `B(H)` satisfies the normal Borel representation compatibility
theorem for every real normal PVM. -/
noncomputable def borelRepresentationWitness :
    NormalBorelRepresentationWitness
      (affiliationBridge (H := H)).toNormalAffiliationBridge where
  represented_boundedFC := by
    intro E f hf hfb
    exact represented_boundedFC_eq_boundedIntegral
      (affiliationBridge (H := H)).toNormalAffiliationBridge E hf hfb

/-- The corresponding full certificate, with the canonical calculus selected automatically. -/
noncomputable def borelRepresentationCertificate :
    NormalBorelRepresentationCertificate
      (affiliationBridge (H := H)).toNormalAffiliationBridge :=
  (borelRepresentationWitness (H := H)).certificate

end BoundedOperatorsNormalRepresentation

end OperatorAlgebra
