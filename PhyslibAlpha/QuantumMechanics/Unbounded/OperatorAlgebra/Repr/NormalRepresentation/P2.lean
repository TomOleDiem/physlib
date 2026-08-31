/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Repr.NormalRepresentation.P1

/-!
# Normal affiliated observables in a Hilbert-space representation (part 2 of 2)

Continuation of `NormalRepresentation/P1.lean`; see `NormalRepresentation.lean` for the full
module overview. This part covers the reduced complex/operator witnesses, the faithful normal
affiliation bridges, and the domain-aware self-adjoint spectral theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ComplexOrder CStarAlgebra InnerProductSpace Topology Function BigOperators
open ContinuousLinearMapWOT

namespace OperatorAlgebra

variable {A H : Type*} [WStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


/-! ### The reduced complex witness (P5 boundary)

The complex analogue of `NormalBorelRepresentationWitness`: `calculusComplex` is likewise never
genuine data (`NormalBorelFunctionalCalculus.ofNormalPVM` supplies it for every `NormalPVM ℂ A`
with no hypothesis), so only the two `represented_boundedFC*` compatibility statements for the
canonical calculi remain as the genuine external representation theorem. -/

/-- The reduced real-and-complex representation witness. -/
structure NormalOperatorBorelRepresentationWitness
    (bridge : NormalOperatorAffiliationBridge (A := A) (H := H)) where
  real : NormalBorelRepresentationWitness bridge.toNormalAffiliationBridge
  represented_boundedFCComplex :
    ∀ (E : NormalPVM ℂ A) (f : ℂ → ℂ)
      (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C),
      bridge.representation
          ((NormalBorelFunctionalCalculus.ofNormalPVM E).boundedFC f hf hfb) =
        (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
          (bridge.toWOTSpectralMeasureComplex E) f hf hfb).toCLM

namespace NormalOperatorBorelRepresentationWitness

variable {bridge : NormalOperatorAffiliationBridge (A := A) (H := H)}

/-- Every complex witness upgrades to a full `NormalOperatorBorelRepresentationCertificate`, using
the canonical `ofNormalPVM` calculus on both the real and complex spectral spaces. -/
def certificate (W : NormalOperatorBorelRepresentationWitness bridge) :
    NormalOperatorBorelRepresentationCertificate bridge where
  toNormalBorelRepresentationCertificate := W.real.certificate
  calculusComplex := fun E => NormalBorelFunctionalCalculus.ofNormalPVM E
  represented_boundedFCComplex := W.represented_boundedFCComplex

end NormalOperatorBorelRepresentationWitness

/-! ## Faithful normal bridges -/

/-- A faithful normal-affiliation bridge.  Faithfulness is kept separate from the representation
bridge itself because constructing a faithful normal representation is a von Neumann-algebra
question, while the uniqueness arguments below need only injectivity. -/
structure FaithfulNormalAffiliationBridge
    extends NormalAffiliationBridge (A := A) (H := H) where
  faithful : Function.Injective representation

namespace FaithfulNormalAffiliationBridge

variable (bridge : FaithfulNormalAffiliationBridge (A := A) (H := H))

lemma representation_injective : Function.Injective bridge.representation :=
  bridge.faithful

/-- A faithful normal representation reflects equality of the values of two normal PVMs when
their represented WOT spectral measures agree. -/
lemma normalPVM_ext
    {E F : NormalPVM ℝ A}
    (h : ∀ S : Set ℝ,
      MeasurableSet S →
      bridge.toWOTSpectralMeasure E S = bridge.toWOTSpectralMeasure F S) :
    E = F := by
  apply NormalPVM.ext
  intro S hS
  apply bridge.faithful
  calc
    bridge.representation (E S) = (bridge.toWOTSpectralMeasure E S).toCLM :=
      bridge.toWOTSpectralMeasure_apply E S
    _ = (bridge.toWOTSpectralMeasure F S).toCLM := congrArg (fun U => U.toCLM) (h S hS)
    _ = bridge.representation (F S) := (bridge.toWOTSpectralMeasure_apply F S).symm

/-- In a faithful normal representation, a normal affiliated observable is determined by its
represented WOT spectral measure. -/
lemma normalAffiliatedObservable_ext
    (T U : NormalAffiliatedObservable A)
    (h : ∀ S : Set ℝ,
      MeasurableSet S →
      bridge.toNormalAffiliationBridge.toWOTSpectralMeasure T.spectralMeasure S =
        bridge.toNormalAffiliationBridge.toWOTSpectralMeasure U.spectralMeasure S) :
    T = U := by
  apply NormalAffiliatedObservable.ext
  intro S hS
  have hEF : T.spectralMeasure = U.spectralMeasure :=
    FaithfulNormalAffiliationBridge.normalPVM_ext bridge (fun S hS => h S hS)
  exact congrArg (fun E : NormalPVM ℝ A => E S) hEF

end FaithfulNormalAffiliationBridge

/-- The faithful version of the real-and-complex normal bridge. -/
structure FaithfulNormalOperatorAffiliationBridge
    extends NormalOperatorAffiliationBridge (A := A) (H := H) where
  faithful : Function.Injective representation

namespace FaithfulNormalOperatorAffiliationBridge

variable (bridge : FaithfulNormalOperatorAffiliationBridge (A := A) (H := H))

lemma representation_injective : Function.Injective bridge.representation :=
  bridge.faithful

/-- A faithful normal representation reflects equality of complex normal PVMs from equality of
their represented WOT spectral measures. -/
lemma normalPVM_ext
    {E F : NormalPVM ℂ A}
    (h : ∀ S : Set ℂ,
      MeasurableSet S →
      bridge.toWOTSpectralMeasureComplex E S =
        bridge.toWOTSpectralMeasureComplex F S) :
    E = F := by
  apply NormalPVM.ext
  intro S hS
  apply bridge.faithful
  calc
    bridge.representation (E S) =
        (bridge.toWOTSpectralMeasureComplex E S).toCLM :=
      bridge.toWOTSpectralMeasureComplex_apply E S
    _ = (bridge.toWOTSpectralMeasureComplex F S).toCLM :=
      congrArg (fun U => U.toCLM) (h S hS)
    _ = bridge.representation (F S) :=
      (bridge.toWOTSpectralMeasureComplex_apply F S).symm

/-- In a faithful normal representation, a complex normal affiliated operator is determined by its
represented WOT spectral measure. -/
lemma normalAffiliatedOperator_ext
    (T U : NormalAffiliatedOperator A)
    (h : ∀ S : Set ℂ,
      MeasurableSet S →
      bridge.toWOTSpectralMeasureComplex T.spectralMeasure S =
        bridge.toWOTSpectralMeasureComplex U.spectralMeasure S) :
    T = U := by
  apply NormalAffiliatedOperator.ext
  intro S hS
  have hEF : T.spectralMeasure = U.spectralMeasure :=
    FaithfulNormalOperatorAffiliationBridge.normalPVM_ext bridge (fun S hS => h S hS)
  exact congrArg (fun E : NormalPVM ℂ A => E S) hEF

end FaithfulNormalOperatorAffiliationBridge

namespace NormalAffiliationBridge

variable (bridge : NormalAffiliationBridge (A := A) (H := H))

/-- Build the real normal-affiliation bridge from a representation that supplies matrix-coefficient
σ-additivity for every normal PVM.  This is the reusable constructor; the analytic theorem that a
particular faithful normal representation supplies the certificate remains a separate input. -/
noncomputable def ofRepresentation (π : Representation A H)
    (hnormal : ∀ E : NormalPVM ℝ A,
      NormalPVM.IsWOTCountablyAdditive E π) : NormalAffiliationBridge (A := A) (H := H) where
  representation := π
  toWOTSpectralMeasure := fun E => NormalPVM.toWOTSpectralMeasure E π (hnormal E)
  toWOTSpectralMeasure_apply := by
    intro E S
    rw [NormalPVM.toWOTSpectralMeasure_apply]
  toWOTSpectralMeasure_map := by
    intro E f hf
    exact NormalPVM.toWOTSpectralMeasure_map E π (hnormal E) hf

/-- Build a real affiliation bridge from an explicit predual lift of every normal PVM.

The lift is required to be compatible with measurable pushforward.  This constructor is useful
when the concrete von Neumann theorem naturally produces predual-functional additivity rather
than a matrix-coefficient statement; `PredualMatrixCoefficientCertificate` supplies the latter
without a positivity or polarization detour.  The lift and its compatibility remain explicit
because they are precisely the nontrivial infinite-dimensional normality theorem. -/
noncomputable def ofPredualRepresentation (π : Representation A H)
    (predual : ∀ E : NormalPVM ℝ A, PredualPVM ℝ A)
    (hpredual : ∀ E : NormalPVM ℝ A, (predual E).toNormalPVM = E)
    (C : NormalPVM.PredualMatrixCoefficientCertificate π)
    (hmap : ∀ (E : NormalPVM ℝ A) {f : ℝ → ℝ} (hf : Measurable f),
      predual (E.map f hf) = (predual E).map f hf) :
    NormalAffiliationBridge (A := A) (H := H) where
  representation := π
  toWOTSpectralMeasure := fun E =>
    NormalPVM.toWOTSpectralMeasureOfPredual (predual E) π C
  toWOTSpectralMeasure_apply := by
    intro E S
    change π (E S) =
      (NormalPVM.toWOTSpectralMeasureOfPredual (predual E) π C S).toCLM
    calc
      π (E S) = π ((predual E).toNormalPVM S) := by rw [hpredual E]
      _ = π ((predual E) S) := rfl
      _ = (NormalPVM.toWOTSpectralMeasureOfPredual
          (predual E) π C S).toCLM := by
        rw [NormalPVM.toWOTSpectralMeasure_of_predual_apply]
  toWOTSpectralMeasure_map := by
    intro E f hf
    change NormalPVM.toWOTSpectralMeasureOfPredual
        (predual (E.map f hf)) π C =
      (NormalPVM.toWOTSpectralMeasureOfPredual (predual E) π C).map f hf
    rw [hmap E hf]
    exact NormalPVM.toWOTSpectralMeasure_of_predual_map (predual E) π C hf

/-- The faithful version of `ofPredualRepresentation`. -/
noncomputable def ofFaithfulPredualRepresentation (π : Representation A H)
    (predual : ∀ E : NormalPVM ℝ A, PredualPVM ℝ A)
    (hpredual : ∀ E : NormalPVM ℝ A, (predual E).toNormalPVM = E)
    (C : NormalPVM.PredualMatrixCoefficientCertificate π)
    (hmap : ∀ (E : NormalPVM ℝ A) {f : ℝ → ℝ} (hf : Measurable f),
      predual (E.map f hf) = (predual E).map f hf)
    (hfaithful : Function.Injective π) :
    FaithfulNormalAffiliationBridge (A := A) (H := H) :=
  { ofPredualRepresentation π predual hpredual C hmap with faithful := hfaithful }

/-! The diagonal variant is the preferred entry point when normality is proved from vector
quadratic forms. -/

/-- Build a real representation bridge from diagonal matrix-coefficient σ-additivity. -/
noncomputable def ofDiagonalRepresentation (π : Representation A H)
    (hdiagonal : ∀ E : NormalPVM ℝ A,
      NormalPVM.IsDiagonalCountablyAdditive E π) :
    NormalAffiliationBridge (A := A) (H := H) :=
  ofRepresentation π (fun E =>
    NormalPVM.isWOTCountablyAdditive_of_diagonal E π (hdiagonal E))

/-- Build the real representation bridge from the normality of all unit-vector states. -/
noncomputable def ofNormalVectorStateCertificate (π : Representation A H)
    (C : NormalPVM.NormalVectorStateCertificate π) :
    NormalAffiliationBridge (A := A) (H := H) :=
  ofDiagonalRepresentation π (fun E =>
    NormalPVM.isDiagonalCountablyAdditive_of_normalVectorStateCertificate E π C)

/-- Build a faithful real normal bridge from the normality of unit-vector states and an injective
representation. -/
noncomputable def ofFaithfulNormalVectorStateCertificate (π : Representation A H)
    (C : NormalPVM.NormalVectorStateCertificate π) (hfaithful : Function.Injective π) :
    FaithfulNormalAffiliationBridge (A := A) (H := H) :=
  { ofNormalVectorStateCertificate π C with faithful := hfaithful }

/-! ### Complex predual bridges -/

/-- Extend a real normal bridge to complex normal affiliated operators using an explicit predual
representation of matrix coefficients for complex-valued PVMs. -/
noncomputable def NormalOperatorAffiliationBridge.ofPredualRepresentation
    (realBridge : NormalAffiliationBridge (A := A) (H := H))
    (predual : ∀ E : NormalPVM ℂ A, PredualPVM ℂ A)
    (hpredual : ∀ E : NormalPVM ℂ A, (predual E).toNormalPVM = E)
    (C : NormalPVM.PredualMatrixCoefficientCertificate realBridge.representation)
    (hmap : ∀ (E : NormalPVM ℂ A) {f : ℂ → ℂ} (hf : Measurable f),
      predual (E.map f hf) = (predual E).map f hf) :
    NormalOperatorAffiliationBridge (A := A) (H := H) where
  toNormalAffiliationBridge := realBridge
  toWOTSpectralMeasureComplex := fun E =>
    NormalPVM.toWOTSpectralMeasureOfPredual (predual E) realBridge.representation C
  toWOTSpectralMeasureComplex_apply := by
    intro E S
    change realBridge.representation (E S) =
      (NormalPVM.toWOTSpectralMeasureOfPredual
        (predual E) realBridge.representation C S).toCLM
    calc
      realBridge.representation (E S) =
          realBridge.representation ((predual E).toNormalPVM S) := by rw [hpredual E]
      _ = realBridge.representation ((predual E) S) := rfl
      _ = (NormalPVM.toWOTSpectralMeasureOfPredual
          (predual E) realBridge.representation C S).toCLM := by
        rw [NormalPVM.toWOTSpectralMeasure_of_predual_apply]
  toWOTSpectralMeasureComplex_map := by
    intro E f hf
    change NormalPVM.toWOTSpectralMeasureOfPredual
        (predual (E.map f hf)) realBridge.representation C =
      (NormalPVM.toWOTSpectralMeasureOfPredual
        (predual E) realBridge.representation C).map f hf
    rw [hmap E hf]
    exact NormalPVM.toWOTSpectralMeasure_of_predual_map (predual E)
      realBridge.representation C hf

/-- The faithful version of the complex predual extension. -/
noncomputable def FaithfulNormalOperatorAffiliationBridge.ofPredualRepresentation
    (realBridge : FaithfulNormalAffiliationBridge (A := A) (H := H))
    (predual : ∀ E : NormalPVM ℂ A, PredualPVM ℂ A)
    (hpredual : ∀ E : NormalPVM ℂ A, (predual E).toNormalPVM = E)
    (C : NormalPVM.PredualMatrixCoefficientCertificate realBridge.representation)
    (hmap : ∀ (E : NormalPVM ℂ A) {f : ℂ → ℂ} (hf : Measurable f),
      predual (E.map f hf) = (predual E).map f hf)
    (hfaithful : Function.Injective realBridge.representation) :
    FaithfulNormalOperatorAffiliationBridge (A := A) (H := H) :=
  { NormalOperatorAffiliationBridge.ofPredualRepresentation
      realBridge.toNormalAffiliationBridge predual hpredual C hmap with
    faithful := hfaithful }

/-! ## Canonical represented operator -/

/-- The weak-operator spectral measure obtained from a normal affiliated observable. -/
def representedSpectralMeasure (T : NormalAffiliatedObservable A) :
    QuantumMechanics.WOTSpectralMeasure ℝ H :=
  bridge.toWOTSpectralMeasure T.spectralMeasure

@[simp]
lemma representedSpectralMeasure_apply (T : NormalAffiliatedObservable A) (S : Set ℝ) :
    bridge.representedSpectralMeasure T S =
      ContinuousLinearMapWOT.ofCLM (bridge.representation (T.spectralMeasure S)) := by
  rw [bridge.toWOTSpectralMeasure_apply]
  rfl

lemma representedSpectralMeasure_projection_apply (T : NormalAffiliatedObservable A)
    (S : Set ℝ) :
    bridge.representation (T.spectralMeasure S) =
      (bridge.representedSpectralMeasure T S).toCLM := by
  exact bridge.toWOTSpectralMeasure_apply T.spectralMeasure S

lemma representedSpectralMeasure_measurableRealFC
    (T : NormalAffiliatedObservable A) {f : ℝ → ℝ} (hf : Measurable f) :
    bridge.representedSpectralMeasure (T.measurableRealFC f hf) =
      (bridge.representedSpectralMeasure T).map f hf := by
  exact bridge.toWOTSpectralMeasure_map T.spectralMeasure hf

/-- The canonical (maximal-domain) self-adjoint operator represented by `T`. -/
noncomputable def representedSelfAdjointOperator
    (T : NormalAffiliatedObservable A) : H →ₗ.[ℂ] H :=
  QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
    (bridge.representedSpectralMeasure T)

lemma representedSelfAdjointOperator_isSelfAdjoint
    (T : NormalAffiliatedObservable A) :
    IsSelfAdjoint (bridge.representedSelfAdjointOperator T) := by
  exact QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_isSelfAdjoint _

lemma representedSelfAdjointOperator_domain
    (T : NormalAffiliatedObservable A) :
    (bridge.representedSelfAdjointOperator T).domain =
      spectralSquareMomentDomain (bridge.representedSpectralMeasure T) := by
  rfl

lemma representedSelfAdjointOperator_measurableRealFC
    (T : NormalAffiliatedObservable A) {f : ℝ → ℝ} (hf : Measurable f) :
    bridge.representedSelfAdjointOperator (T.measurableRealFC f hf) =
      QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
        ((bridge.representedSpectralMeasure T).map f hf) := by
  change QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
    (bridge.representedSpectralMeasure (T.measurableRealFC f hf)) = _
  rw [bridge.representedSpectralMeasure_measurableRealFC T hf]

/-! ## The represented unitary dynamics -/

/-- The strongly continuous unitary group generated by the represented normal affiliated
observable.  Its value at `t` is the bounded spectral integral of
`λ ↦ exp (i t λ)`. -/
noncomputable def expUnitaryGroup
    (T : NormalAffiliatedObservable A) :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup H :=
  QuantumMechanics.WOTSpectralMeasure.expUnitaryGroup
    (bridge.representedSpectralMeasure T)

lemma expUnitaryGroup_zero (T : NormalAffiliatedObservable A) :
    bridge.expUnitaryGroup T 0 = 1 := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.zero _

lemma expUnitaryGroup_add (T : NormalAffiliatedObservable A) (t s : ℝ) :
    bridge.expUnitaryGroup T (t + s) =
      bridge.expUnitaryGroup T t * bridge.expUnitaryGroup T s := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.add _ t s

lemma expUnitaryGroup_continuous_apply (T : NormalAffiliatedObservable A) (x : H) :
    Continuous (fun t => bridge.expUnitaryGroup T t x) := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.continuous_apply _ x

lemma expUnitaryGroup_eq_expIntegral (T : NormalAffiliatedObservable A) (t : ℝ) :
    bridge.expUnitaryGroup T t =
      QuantumMechanics.WOTSpectralMeasure.expIntegral
        (bridge.representedSpectralMeasure T) t := by
  rfl

/-! ### Compatibility with the canonical abstract calculus -/

/-- The canonical algebra-level `exp (i t T)` is represented by the concrete spectral integral. -/
lemma represented_canonicalExpUnitary
    (W : NormalBorelRepresentationWitness bridge)
    (T : NormalAffiliatedObservable A) (t : ℝ) :
    bridge.representation ((T.canonicalExpUnitary t : unitary A) : A) =
      (bridge.expUnitaryGroup T t).toCLM := by
  change bridge.representation
      ((NormalBorelFunctionalCalculus.ofNormalPVM T.spectralMeasure).boundedFC
        (AffiliatedObservable.expFunction t)
        (AffiliatedObservable.expFunction_measurable t)
        (AffiliatedObservable.expFunction_bounded t)) = _
  exact W.represented_boundedFC T.spectralMeasure _ _ _

/-- The canonical algebra-level `exp (-i t T)` is represented by the time-reversed concrete
spectral integral. -/
lemma represented_canonicalNegativeExpUnitary
    (W : NormalBorelRepresentationWitness bridge)
    (T : NormalAffiliatedObservable A) (t : ℝ) :
    bridge.representation ((T.canonicalNegativeExpUnitary t : unitary A) : A) =
      (bridge.expUnitaryGroup T (-t)).toCLM := by
  change bridge.representation
      ((NormalBorelFunctionalCalculus.ofNormalPVM T.spectralMeasure).boundedFC
        (AffiliatedObservable.expFunction (-t))
        (AffiliatedObservable.expFunction_measurable (-t))
        (AffiliatedObservable.expFunction_bounded (-t))) = _
  exact W.represented_boundedFC T.spectralMeasure _ _ _

/-! ### The conventional quantum-dynamics sign -/

/-- The represented quantum-dynamics group `exp (-i t T)`, obtained by time reversal of
the canonical `exp (i t T)` group. -/
noncomputable def negativeExpUnitaryGroup
    (T : NormalAffiliatedObservable A) :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup H :=
  { toFun := fun t => bridge.expUnitaryGroup T (-t)
    mem_unitary := fun t =>
      (bridge.expUnitaryGroup T).mem_unitary (-t)
    map_zero := by
      simpa using bridge.expUnitaryGroup_zero T
    map_add := by
      intro t s
      change bridge.expUnitaryGroup T (-(t + s)) =
        bridge.expUnitaryGroup T (-t) * bridge.expUnitaryGroup T (-s)
      rw [show -(t + s) = -t + -s by ring]
      exact bridge.expUnitaryGroup_add T (-t) (-s)
    strong_continuous := by
      intro x
      simpa [Function.comp_def] using
        (bridge.expUnitaryGroup_continuous_apply T x).comp continuous_neg }

lemma negativeExpUnitaryGroup_zero (T : NormalAffiliatedObservable A) :
    bridge.negativeExpUnitaryGroup T 0 = 1 := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.zero _

lemma negativeExpUnitaryGroup_add (T : NormalAffiliatedObservable A) (t s : ℝ) :
    bridge.negativeExpUnitaryGroup T (t + s) =
      bridge.negativeExpUnitaryGroup T t * bridge.negativeExpUnitaryGroup T s := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.add _ t s

lemma negativeExpUnitaryGroup_continuous_apply
    (T : NormalAffiliatedObservable A) (x : H) :
    Continuous (fun t => bridge.negativeExpUnitaryGroup T t x) := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.continuous_apply _ x

/-! ### The star/inverse law -/

/-- The represented canonical group satisfies the star/inverse law: adjoint at time `t` equals
the group value at `-t`.  This is the `WOT`-level identity `expIntegral_star`, transported through
the represented spectral measure. -/
theorem expUnitaryGroup_star (T : NormalAffiliatedObservable A) (t : ℝ) :
    star (bridge.expUnitaryGroup T t) = bridge.expUnitaryGroup T (-t) :=
  QuantumMechanics.WOTSpectralMeasure.expIntegral_star (bridge.representedSpectralMeasure T) t

/-- The represented quantum-dynamics group satisfies the same star/inverse law, with the sign
inherited from the time reversal. -/
theorem negativeExpUnitaryGroup_star (T : NormalAffiliatedObservable A) (t : ℝ) :
    star (bridge.negativeExpUnitaryGroup T t) = bridge.negativeExpUnitaryGroup T (-t) := by
  have h := bridge.expUnitaryGroup_star T (-t)
  simpa [negativeExpUnitaryGroup, neg_neg] using h

/-! ## The represented resolvent -/

/-- The concrete bounded resolvent of the represented maximal realization.

This is deliberately a `WOT` operator rather than an element of `A`: the latter requires a
normal Borel-functional-calculus certificate on the abstract side.  The Hilbert-space spectral
integral already gives the bounded operator for every `z ∉ ℝ`, and the identity below makes its
resolvent law available without any additional affiliation assumptions. -/
noncomputable def representedResolvent
    (T : NormalAffiliatedObservable A) (z : ℂ) (hz : z.im ≠ 0) : H →WOT[ℂ] H :=
  QuantumMechanics.WOTSpectralMeasure.boundedIntegral
    (bridge.representedSpectralMeasure T)
    (AffiliatedObservable.resolventFunction z)
    (AffiliatedObservable.resolventFunction_measurable z)
    (AffiliatedObservable.resolventFunction_bounded z hz)

@[simp]
lemma representedResolvent_eq_boundedIntegral
    (T : NormalAffiliatedObservable A) (z : ℂ) (hz : z.im ≠ 0) :
    bridge.representedResolvent T z hz =
      QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.representedSpectralMeasure T)
        (AffiliatedObservable.resolventFunction z)
        (AffiliatedObservable.resolventFunction_measurable z)
        (AffiliatedObservable.resolventFunction_bounded z hz) := by
  rfl

/-- The represented bounded resolvent is the ordinary partial-map resolvent of the represented
maximal self-adjoint operator.  This is the general-parameter version of the two Cayley-shift
lemmas below; it is the theorem downstream applications should use when they need the resolvent
of the unbounded operator itself. -/
lemma representedResolvent_apply
    (T : NormalAffiliatedObservable A) (z : ℂ) (hz : z.im ≠ 0) (x : H) :
    bridge.representedResolvent T z hz x =
      (LinearPMap.resolvent (bridge.representedSelfAdjointOperator T) z)
        (⟨x, by
          rw [LinearPMap.inverse_domain]
          change x ∈
            (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
              (bridge.representedSpectralMeasure T) - z • (1 : H →ₗ.[ℂ] H)).toFun.range
          rw [QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_resolvent_range hz]
          exact Submodule.mem_top⟩) := by
  dsimp only [representedResolvent, representedSelfAdjointOperator]
  have hfun : AffiliatedObservable.resolventFunction z =
      QuantumMechanics.WOTSpectralMeasure.resolventMultiplier z := by
    funext r
    rfl
  have hconv := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_congr
    (μS := bridge.representedSpectralMeasure T)
    (AffiliatedObservable.resolventFunction_measurable z)
    (QuantumMechanics.WOTSpectralMeasure.resolventMultiplier_measurable z)
    (AffiliatedObservable.resolventFunction_bounded z hz)
    (QuantumMechanics.WOTSpectralMeasure.resolventMultiplier_bounded hz)
    (congrFun hfun)
  rw [hconv]
  exact (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_resolvent_apply
    (μS := bridge.representedSpectralMeasure T) hz x).symm

lemma representedResolvent_identity
    (T : NormalAffiliatedObservable A) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    bridge.representedResolvent T z hz - bridge.representedResolvent T w hw =
      (z - w) • (bridge.representedResolvent T z hz *
        bridge.representedResolvent T w hw) := by
  let μS := bridge.representedSpectralMeasure T
  let fz := AffiliatedObservable.resolventFunction z
  let fw := AffiliatedObservable.resolventFunction w
  have hfz : Measurable fz := AffiliatedObservable.resolventFunction_measurable z
  have hfw : Measurable fw := AffiliatedObservable.resolventFunction_measurable w
  have hbfz : ∃ C : ℝ, ∀ x, ‖fz x‖ ≤ C :=
    AffiliatedObservable.resolventFunction_bounded z hz
  have hbfw : ∃ C : ℝ, ∀ x, ‖fw x‖ ≤ C :=
    AffiliatedObservable.resolventFunction_bounded w hw
  have hprod : ∃ C : ℝ, ∀ x, ‖fz x * fw x‖ ≤ C := by
    rcases hbfz with ⟨Cz, hCz⟩
    rcases hbfw with ⟨Cw, hCw⟩
    refine ⟨Cz * Cw, fun x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hCz x) (hCw x) (norm_nonneg _)
      ((norm_nonneg (fz 0)).trans (hCz 0))
  have hscaled : ∃ C : ℝ, ∀ x, ‖(z - w) * (fz x * fw x)‖ ≤ C := by
    rcases hbfz with ⟨Cz, hCz⟩
    rcases hbfw with ⟨Cw, hCw⟩
    refine ⟨‖z - w‖ * (Cz * Cw), fun x => ?_⟩
    rw [norm_mul, norm_mul]
    exact mul_le_mul (le_rfl)
      (mul_le_mul (hCz x) (hCw x) (norm_nonneg _)
        ((norm_nonneg (fz 0)).trans (hCz 0)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hdiff : ∃ C : ℝ, ∀ x, ‖(fz - fw) x‖ ≤ C := by
    rcases hbfz with ⟨Cz, hCz⟩
    rcases hbfw with ⟨Cw, hCw⟩
    refine ⟨Cz + Cw, fun x => ?_⟩
    simpa only [Pi.sub_apply] using
      (show ‖fz x - fw x‖ ≤ Cz + Cw from
        (norm_sub_le _ _).trans (add_le_add (hCz x) (hCw x)))
  have hsub := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_sub
    (μS := μS) hfz hfw hbfz hbfw
  have hmul := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_mul
    (μS := μS) hfz hfw hbfz hbfw
  have hsmul := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_smul
    (μS := μS) (z - w) (hfz.mul hfw) hprod
  calc
    bridge.representedResolvent T z hz - bridge.representedResolvent T w hw =
        QuantumMechanics.WOTSpectralMeasure.boundedIntegral μS (fz - fw)
          (hfz.sub hfw) hdiff := by
      exact hsub.symm
    _ = QuantumMechanics.WOTSpectralMeasure.boundedIntegral μS
        (fun x => (z - w) * (fz x * fw x))
        (measurable_const.mul (hfz.mul hfw)) hscaled := by
      apply QuantumMechanics.WOTSpectralMeasure.boundedIntegral_congr
        (μS := μS) (hfz.sub hfw) (measurable_const.mul (hfz.mul hfw)) hdiff hscaled
      intro x
      dsimp [fz, fw, AffiliatedObservable.resolventFunction]
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
    _ = (z - w) • QuantumMechanics.WOTSpectralMeasure.boundedIntegral μS
        (fz * fw) (hfz.mul hfw) hprod := hsmul
    _ = (z - w) • (bridge.representedResolvent T z hz *
        bridge.representedResolvent T w hw) := by
      rw [hmul]
      rfl

lemma representedSelfAdjointOperator_plus_resolvent_inverse_apply
    (T : NormalAffiliatedObservable A) (x : H) :
    (bridge.representedSelfAdjointOperator T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse
        ⟨x, by
          rw [LinearPMap.inverse_domain]
          change x ∈
            (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
              (bridge.representedSpectralMeasure T) + Complex.I •
                (1 : H →ₗ.[ℂ] H)).toFun.range
          rw [QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_plus_resolvent_range]
          exact Submodule.mem_top⟩ =
      bridge.representedResolvent T (-Complex.I) (by norm_num) x := by
  dsimp only [representedSelfAdjointOperator]
  have h :=
    QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_plus_resolvent_inverse_apply
      (μS := bridge.representedSpectralMeasure T) x
  have hfun : AffiliatedObservable.resolventFunction (-Complex.I) =
      QuantumMechanics.WOTSpectralMeasure.plusResolventMultiplier := by
    funext r
    simp [AffiliatedObservable.resolventFunction,
      QuantumMechanics.WOTSpectralMeasure.plusResolventMultiplier]
  have hconv := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_congr
    (μS := bridge.representedSpectralMeasure T)
    (AffiliatedObservable.resolventFunction_measurable (-Complex.I))
    QuantumMechanics.WOTSpectralMeasure.plusResolventMultiplier_measurable
    (AffiliatedObservable.resolventFunction_bounded (-Complex.I) (by norm_num))
    QuantumMechanics.WOTSpectralMeasure.plusResolventMultiplier_bounded (congrFun hfun)
  dsimp only [representedResolvent]
  rw [hconv]
  exact h

lemma representedSelfAdjointOperator_minus_resolvent_inverse_apply
    (T : NormalAffiliatedObservable A) (x : H) :
    (bridge.representedSelfAdjointOperator T - Complex.I • (1 : H →ₗ.[ℂ] H)).inverse
        ⟨x, by
          rw [LinearPMap.inverse_domain]
          change x ∈
            (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
              (bridge.representedSpectralMeasure T) - Complex.I •
                (1 : H →ₗ.[ℂ] H)).toFun.range
          rw [QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_minus_resolvent_range]
          exact Submodule.mem_top⟩ =
      bridge.representedResolvent T Complex.I (by norm_num) x := by
  dsimp only [representedSelfAdjointOperator]
  have h :=
    QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_minus_resolvent_inverse_apply
      (μS := bridge.representedSpectralMeasure T) x
  have hfun : AffiliatedObservable.resolventFunction Complex.I =
      QuantumMechanics.WOTSpectralMeasure.minusResolventMultiplier := by
    funext r
    simp [AffiliatedObservable.resolventFunction,
      QuantumMechanics.WOTSpectralMeasure.minusResolventMultiplier]
  have hconv := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_congr
    (μS := bridge.representedSpectralMeasure T)
    (AffiliatedObservable.resolventFunction_measurable Complex.I)
    QuantumMechanics.WOTSpectralMeasure.minusResolventMultiplier_measurable
    (AffiliatedObservable.resolventFunction_bounded Complex.I (by norm_num))
    QuantumMechanics.WOTSpectralMeasure.minusResolventMultiplier_bounded (congrFun hfun)
  dsimp only [representedResolvent]
  rw [hconv]
  exact h

/-! ## The represented Stone generator -/

lemma expUnitaryGroup_strong_slope_tendsto
    (T : NormalAffiliatedObservable A)
    (x : (bridge.representedSelfAdjointOperator T).domain) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ •
        (bridge.expUnitaryGroup T t (x : H) - (x : H)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (Complex.I • bridge.representedSelfAdjointOperator T x)) := by
  cases x with
  | mk x hx =>
      change Filter.Tendsto
        (fun t : ℝ => t⁻¹ •
          (QuantumMechanics.WOTSpectralMeasure.expIntegral
            (bridge.representedSpectralMeasure T) t x - x))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (Complex.I •
          QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
            (bridge.representedSpectralMeasure T) (⟨x, hx⟩)))
      exact QuantumMechanics.WOTSpectralMeasure.expIntegral_strong_slope_tendsto
        (bridge.representedSpectralMeasure T) x hx

lemma expUnitaryGroup_hasDerivAt_zero
    (T : NormalAffiliatedObservable A)
    (x : (bridge.representedSelfAdjointOperator T).domain) :
    HasDerivAt (fun t : ℝ => bridge.expUnitaryGroup T t (x : H))
      (Complex.I • bridge.representedSelfAdjointOperator T x) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  convert bridge.expUnitaryGroup_strong_slope_tendsto T x using 1
  funext t
  simp [slope, bridge.expUnitaryGroup_zero T]

theorem representedSelfAdjointOperator_measurableRealFC_eq_measurableSpectralIntegral
    (T : NormalAffiliatedObservable A) {f : ℝ → ℝ} (hf : Measurable f) :
    bridge.representedSelfAdjointOperator (T.measurableRealFC f hf) =
      QuantumMechanics.WOTSpectralMeasure.measurableSpectralIntegral
        (bridge.representedSpectralMeasure T) f hf := by
  exact bridge.representedSelfAdjointOperator_measurableRealFC T hf

end NormalAffiliationBridge

namespace NormalOperatorAffiliationBridge

variable (bridge : NormalOperatorAffiliationBridge (A := A) (H := H))

/-! ### Constructing the complex bridge -/

/-- Build the real-and-complex representation bridge from matrix-coefficient σ-additivity.

The two certificates are kept separate because the real and complex affiliated façades have
different spectral spaces.  In a concrete von Neumann algebra representation they normally come
from the same normality theorem, but requiring both here prevents an accidental use of a real
certificate for a genuinely complex normal operator. -/
noncomputable def ofRepresentation (π : Representation A H)
    (hreal : ∀ E : NormalPVM ℝ A,
      NormalPVM.IsWOTCountablyAdditive E π)
    (hcomplex : ∀ E : NormalPVM ℂ A,
      NormalPVM.IsWOTCountablyAdditive E π) :
    NormalOperatorAffiliationBridge (A := A) (H := H) where
  representation := π
  toWOTSpectralMeasure := fun E => NormalPVM.toWOTSpectralMeasure E π (hreal E)
  toWOTSpectralMeasure_apply := by
    intro E S
    rw [NormalPVM.toWOTSpectralMeasure_apply]
  toWOTSpectralMeasure_map := by
    intro E f hf
    exact NormalPVM.toWOTSpectralMeasure_map E π (hreal E) hf
  toWOTSpectralMeasureComplex :=
    fun E => NormalPVM.toWOTSpectralMeasure E π (hcomplex E)
  toWOTSpectralMeasureComplex_apply := by
    intro E S
    rw [NormalPVM.toWOTSpectralMeasure_apply]
  toWOTSpectralMeasureComplex_map := by
    intro E f hf
    exact NormalPVM.toWOTSpectralMeasure_map E π (hcomplex E) hf

/-- Build the real-and-complex representation bridge from diagonal matrix-coefficient
σ-additivity. -/
noncomputable def ofDiagonalRepresentation (π : Representation A H)
    (hreal : ∀ E : NormalPVM ℝ A,
      NormalPVM.IsDiagonalCountablyAdditive E π)
    (hcomplex : ∀ E : NormalPVM ℂ A,
      NormalPVM.IsDiagonalCountablyAdditive E π) :
    NormalOperatorAffiliationBridge (A := A) (H := H) :=
  NormalOperatorAffiliationBridge.ofRepresentation π
    (fun E => NormalPVM.isWOTCountablyAdditive_of_diagonal E π (hreal E))
    (fun E => NormalPVM.isWOTCountablyAdditive_of_diagonal E π (hcomplex E))

/-- Build the real-and-complex representation bridge from the normality of all unit-vector
states.  The same vector-state certificate applies to both measurable spectral spaces. -/
noncomputable def ofNormalVectorStateCertificate (π : Representation A H)
    (C : NormalPVM.NormalVectorStateCertificate π) :
    NormalOperatorAffiliationBridge (A := A) (H := H) :=
  NormalOperatorAffiliationBridge.ofDiagonalRepresentation π
    (fun E => NormalPVM.isDiagonalCountablyAdditive_of_normalVectorStateCertificate E π C)
    (fun E => NormalPVM.isDiagonalCountablyAdditive_of_normalVectorStateCertificate E π C)

/-- Build a faithful real-and-complex normal bridge from the normality of unit-vector states and an
injective representation. -/
noncomputable def ofFaithfulNormalVectorStateCertificate (π : Representation A H)
    (C : NormalPVM.NormalVectorStateCertificate π) (hfaithful : Function.Injective π) :
    FaithfulNormalOperatorAffiliationBridge (A := A) (H := H) :=
  { ofNormalVectorStateCertificate π C with faithful := hfaithful }

/-- The weak-operator spectral measure represented by a complex normal affiliated operator. -/
def representedSpectralMeasure (T : NormalAffiliatedOperator A) :
    QuantumMechanics.WOTSpectralMeasure ℂ H :=
  bridge.toWOTSpectralMeasureComplex T.spectralMeasure

@[simp]
lemma representedSpectralMeasure_apply (T : NormalAffiliatedOperator A) (S : Set ℂ) :
    bridge.representedSpectralMeasure T S =
      ContinuousLinearMapWOT.ofCLM (bridge.representation (T.spectralMeasure S)) := by
  rw [bridge.toWOTSpectralMeasureComplex_apply]
  rfl

lemma representedSpectralMeasure_measurableFC
    (T : NormalAffiliatedOperator A) {f : ℂ → ℂ} (hf : Measurable f) :
    bridge.representedSpectralMeasure (T.measurableFC f hf) =
      (bridge.representedSpectralMeasure T).map f hf := by
  exact bridge.toWOTSpectralMeasureComplex_map T.spectralMeasure hf

end NormalOperatorAffiliationBridge

/-- The predual vector-state certificate produced by weak-star continuity of all matrix
coefficients. -/
noncomputable def NormalRepresentation.toNormalVectorStateCertificate
    (π : NormalRepresentation (A := A) (H := H)) :
    NormalPVM.NormalVectorStateCertificate π.representation where
  state := fun x hx => normalVectorState π x hx
  apply := by intro x hx a; rfl

/-- Construct the real normal-affiliation bridge directly from a normal representation. -/
noncomputable def NormalRepresentation.toNormalAffiliationBridge
    (π : NormalRepresentation (A := A) (H := H)) :
    NormalAffiliationBridge (A := A) (H := H) :=
  NormalAffiliationBridge.ofNormalVectorStateCertificate
    π.representation π.toNormalVectorStateCertificate

/-- Construct a faithful real normal-affiliation bridge directly from a faithful normal
representation. -/
noncomputable def NormalRepresentation.toFaithfulNormalAffiliationBridge
    (π : NormalRepresentation (A := A) (H := H))
    (hfaithful : Function.Injective π.representation) :
    FaithfulNormalAffiliationBridge (A := A) (H := H) :=
  NormalAffiliationBridge.ofFaithfulNormalVectorStateCertificate
    π.representation π.toNormalVectorStateCertificate hfaithful

/-- Construct the real-and-complex normal-affiliation bridge directly from a normal
representation. -/
noncomputable def NormalRepresentation.toNormalOperatorAffiliationBridge
    (π : NormalRepresentation (A := A) (H := H)) :
    NormalOperatorAffiliationBridge (A := A) (H := H) :=
  NormalOperatorAffiliationBridge.ofNormalVectorStateCertificate
    π.representation π.toNormalVectorStateCertificate

/-- Construct a faithful real-and-complex normal-affiliation bridge directly from a faithful
normal representation. -/
noncomputable def NormalRepresentation.toFaithfulNormalOperatorAffiliationBridge
    (π : NormalRepresentation (A := A) (H := H))
    (hfaithful : Function.Injective π.representation) :
    FaithfulNormalOperatorAffiliationBridge (A := A) (H := H) :=
  NormalOperatorAffiliationBridge.ofFaithfulNormalVectorStateCertificate
    π.representation π.toNormalVectorStateCertificate hfaithful

namespace DomainAwareSelfAdjointSpectralTheorem

variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

/-! ## Consuming a domain-aware theorem -/

/-- A domain-aware spectral theorem identifies the bridge's canonical maximal realization with the
given self-adjoint operator, once its represented spectral measure is identified with the theorem's
measure. -/
theorem representedNormalSelfAdjointOperator_eq
    (D : DomainAwareSelfAdjointSpectralTheorem T μS)
    (bridge : NormalAffiliationBridge (A := A) (H := H))
    (S : NormalAffiliatedObservable A)
    (hS : bridge.representedSpectralMeasure S = μS) :
    bridge.representedSelfAdjointOperator S = T := by
  change QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
    (bridge.representedSpectralMeasure S) = T
  rw [hS]
  exact D.maximal_eq

end DomainAwareSelfAdjointSpectralTheorem

end OperatorAlgebra

end
