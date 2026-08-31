/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Spec.UnitaryInfrastructure
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.SpectralTheory.SpectralIntegral
public import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
public import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec

/-!
# Bounded spectral data for a Cayley transform

This module is the adapter between the spectrum-valued bounded-unitary construction and the
ambient `ℂ`-valued certificate consumed by the Cayley transform.  The proof is intentionally kept
separate from `Cayley.lean`, which supplies the transport definitions and must not import the
bounded spectral construction back.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped ComplexOrder CStarAlgebra InnerProductSpace
open QuantumMechanics.WOTSpectralMeasure

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real part of a spectral point of `U`, as a compactly supported continuous function on
`spectrum ℂ U`. -/
def spectrumRealPart (U : H →L[ℂ] H) :
    CompactlySupportedContinuousMap (spectrum ℂ U) ℝ :=
  ⟨⟨fun z => z.1.re, by fun_prop⟩,
    hasCompactSupport_def.mpr
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (subset_univ _))⟩

/-- The imaginary part of a spectral point of `U`, as a compactly supported continuous function
on `spectrum ℂ U`. -/
def spectrumImagPart (U : H →L[ℂ] H) :
    CompactlySupportedContinuousMap (spectrum ℂ U) ℝ :=
  ⟨⟨fun z => z.1.im, by fun_prop⟩,
    hasCompactSupport_def.mpr
      (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (subset_univ _))⟩

lemma cfcScalarMeasure_integral_spectrum_coe
    (U : H →L[ℂ] H) (hU : IsStarNormal U) (v : H) :
    ∫ z, (z.1 : ℂ) ∂cfcScalarMeasure U hU v =
      ((∫ z, spectrumRealPart U z ∂cfcScalarMeasure U hU v : ℝ) : ℂ) +
        Complex.I * ∫ z, spectrumImagPart U z ∂cfcScalarMeasure U hU v := by
  have hf : Integrable (fun z : spectrum ℂ U => (z.1 : ℂ))
      (cfcScalarMeasure U hU v) := by
    rw [← integrableOn_univ]
    exact continuous_subtype_val.continuousOn.integrableOn_compact isCompact_univ
  have hre : ∫ z, (z.1).re ∂cfcScalarMeasure U hU v =
      RCLike.re ⟪v, cfcRealOperator U hU (spectrumRealPart U) v⟫_ℂ := by
    simpa [spectrumRealPart] using
      cfcScalarMeasure_integral U hU v (spectrumRealPart U)
  have him : ∫ z, (z.1).im ∂cfcScalarMeasure U hU v =
      RCLike.re ⟪v, cfcRealOperator U hU (spectrumImagPart U) v⟫_ℂ := by
    simpa [spectrumImagPart] using
      cfcScalarMeasure_integral U hU v (spectrumImagPart U)
  rw [← integral_re_add_im hf]
  change ((∫ z, (z.1).re ∂cfcScalarMeasure U hU v : ℝ) : ℂ) +
      (∫ z, (z.1).im ∂cfcScalarMeasure U hU v : ℝ) * Complex.I =
    ((∫ z, (z.1).re ∂cfcScalarMeasure U hU v : ℝ) : ℂ) +
      Complex.I * ∫ z, (z.1).im ∂cfcScalarMeasure U hU v
  rw [hre, him]
  ring

lemma polarizedCfcScalarMeasure_integral_spectrum_coe
    (U : H →L[ℂ] H) (hU : IsStarNormal U) (x y : H) :
    ∫ᵛ z, (z.1 : ℂ) ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      polarizedCfcScalarMeasure (hU := hU) U x y] =
      ⟪y, U x⟫_ℂ := by
  let fC : spectrum ℂ U → ℂ := fun z => (z.1 : ℂ)
  have hfC : Continuous fC := by fun_prop
  have hplus : Integrable fC (cfcScalarMeasure U hU (x + y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  have hminus : Integrable fC (cfcScalarMeasure U hU (x - y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  have hip : Integrable fC
      (cfcScalarMeasure U hU (x + Complex.I • y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  have him : Integrable fC
      (cfcScalarMeasure U hU (x - Complex.I • y)) := by
    rw [← integrableOn_univ]
    exact hfC.continuousOn.integrableOn_compact isCompact_univ
  let μplus := cfcScalarMeasure U hU (x + y)
  let μminus := cfcScalarMeasure U hU (x - y)
  let νplus := cfcScalarMeasure U hU (x + Complex.I • y)
  let νminus := cfcScalarMeasure U hU (x - Complex.I • y)
  change ∫ᵛ z, fC z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      ((1 / 4 : ℝ) • (μplus.toSignedMeasure - μminus.toSignedMeasure)).toComplexMeasure
        ((1 / 4 : ℝ) • (νplus.toSignedMeasure - νminus.toSignedMeasure))] = _
  have hreal :
      (((1 / 4 : ℝ) • (μplus.toSignedMeasure - μminus.toSignedMeasure)).mapRange
        Complex.ofRealCLM.toAddMonoidHom Complex.ofRealCLM.continuous).Integrable fC := by
    rw [VectorMeasure.mapRange_smul, mapRange_sub_toSignedMeasure μplus μminus]
    exact (integrable_mapRange_ofReal_signedMeasure μplus fC hplus).sub_vectorMeasure
      (integrable_mapRange_ofReal_signedMeasure μminus fC hminus) |>.smul_vectorMeasure _
  have himag :
      (((1 / 4 : ℝ) • (νplus.toSignedMeasure - νminus.toSignedMeasure)).mapRange
        imaginaryOfRealCLM.toAddMonoidHom imaginaryOfRealCLM.continuous).Integrable fC := by
    rw [VectorMeasure.mapRange_smul, mapRange_sub_toSignedMeasure νplus νminus]
    exact (integrable_mapRange_imaginaryOfReal_signedMeasure νplus fC hip).sub_vectorMeasure
      (integrable_mapRange_imaginaryOfReal_signedMeasure νminus fC him) |>.smul_vectorMeasure _
  rw [integral_toComplexMeasure_eq_add_mapRange _ _ fC hreal himag]
  rw [integral_mapRange_ofReal_signedDifference μplus μminus (1 / 4 : ℝ) fC hplus hminus,
    integral_mapRange_imaginaryOfReal_signedDifference νplus νminus (1 / 4 : ℝ) fC hip him]
  have hJ (v : H) :
      ∫ z, (z.1 : ℂ) ∂cfcScalarMeasure U hU v =
        ((∫ z, spectrumRealPart U z ∂cfcScalarMeasure U hU v : ℝ) : ℂ) +
          Complex.I * ∫ z, spectrumImagPart U z ∂cfcScalarMeasure U hU v :=
    cfcScalarMeasure_integral_spectrum_coe U hU v
  rw [hJ, hJ, hJ, hJ]
  have hre := polarizedCfcRealIntegral_eq_inner U hU (spectrumRealPart U) x y
  have him' := polarizedCfcRealIntegral_eq_inner U hU (spectrumImagPart U) x y
  have hsplit :
      cfcRealOperator U hU (spectrumRealPart U) +
          (Complex.I : ℂ) • (cfcRealOperator U hU (spectrumImagPart U)) = U := by
    unfold cfcRealOperator
    rw [← map_smul, ← map_add]
    have hid :
        realToComplexContinuousMap U (spectrumRealPart U) +
            (Complex.I : ℂ) • realToComplexContinuousMap U (spectrumImagPart U) =
          (ContinuousMap.id ℂ).restrict (spectrum ℂ U) := by
      ext z
      change (z.1.re : ℂ) + Complex.I * z.1.im = z.1
      rw [mul_comm]
      exact Complex.re_add_im z.1
    calc
      cfcHom hU (realToComplexContinuousMap U (spectrumRealPart U) +
          Complex.I • realToComplexContinuousMap U (spectrumImagPart U)) =
          cfcHom hU ((ContinuousMap.id ℂ).restrict (spectrum ℂ U)) :=
        congrArg (fun f => cfcHom hU f) hid
      _ = U := cfcHom_id hU
  have hfinal :
      polarizedCfcRealIntegral U hU (spectrumRealPart U) x y +
          Complex.I * polarizedCfcRealIntegral U hU (spectrumImagPart U) x y =
        ⟪y, (cfcRealOperator U hU (spectrumRealPart U) +
          (Complex.I : ℂ) • (cfcRealOperator U hU (spectrumImagPart U))) x⟫_ℂ := by
    rw [hre, him']
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      inner_add_right, inner_smul_right]
  calc
    _ = polarizedCfcRealIntegral U hU (spectrumRealPart U) x y +
        Complex.I * polarizedCfcRealIntegral U hU (spectrumImagPart U) x y := by
      dsimp [polarizedCfcRealIntegral]
      ring
    _ = ⟪y, (cfcRealOperator U hU (spectrumRealPart U) +
        (Complex.I : ℂ) • cfcRealOperator U hU (spectrumImagPart U)) x⟫_ℂ := hfinal
    _ = ⟪y, U x⟫_ℂ := by rw [hsplit]

/-- The Cayley unitary of `T`, as a bounded continuous linear map. -/
def cayleyBoundedOperator (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) : H →L[ℂ] H :=
  (cayleyUnitary T hT).toLinearIsometry.toContinuousLinearMap

lemma cayleyBoundedOperator_apply (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    cayleyBoundedOperator T hT x = cayleyContinuousLinearMap T hT x := by
  rfl

lemma cayleyBoundedOperator_isStarNormal (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    IsStarNormal (cayleyBoundedOperator T hT) := by
  let u := cayleyUnitary T hT
  change IsStarNormal (u.toLinearIsometry.toContinuousLinearMap)
  rw [isStarNormal_iff]
  change Commute (star u.toLinearIsometry.toContinuousLinearMap)
    u.toLinearIsometry.toContinuousLinearMap
  rw [show star u.toLinearIsometry.toContinuousLinearMap =
      u.symm.toLinearIsometry.toContinuousLinearMap by
        change star (u : H →L[ℂ] H) = (u.symm : H →L[ℂ] H)
        exact u.star_eq_symm]
  change u.symm.toLinearIsometry.toContinuousLinearMap *
      u.toLinearIsometry.toContinuousLinearMap =
    u.toLinearIsometry.toContinuousLinearMap *
      u.symm.toLinearIsometry.toContinuousLinearMap
  ext x
  simp [ContinuousLinearMap.mul_def]

lemma cayleyBoundedOperator_mem_unitary (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    cayleyBoundedOperator T hT ∈ unitary (H →L[ℂ] H) := by
  let u := cayleyUnitary T hT
  have hstar : star u.toLinearIsometry.toContinuousLinearMap =
      u.symm.toLinearIsometry.toContinuousLinearMap := by
    change star (u : H →L[ℂ] H) = (u.symm : H →L[ℂ] H)
    exact u.star_eq_symm
  rw [Unitary.mem_iff]
  constructor
  · change star u.toLinearIsometry.toContinuousLinearMap *
      u.toLinearIsometry.toContinuousLinearMap = 1
    rw [hstar]
    change u.symm.toLinearIsometry.toContinuousLinearMap *
        u.toLinearIsometry.toContinuousLinearMap = 1
    ext x
    simp [ContinuousLinearMap.mul_def]
  · change u.toLinearIsometry.toContinuousLinearMap *
      star u.toLinearIsometry.toContinuousLinearMap = 1
    rw [hstar]
    change u.toLinearIsometry.toContinuousLinearMap *
        u.symm.toLinearIsometry.toContinuousLinearMap = 1
    ext x
    simp [ContinuousLinearMap.mul_def]

/-- The pushforward of the Cayley unitary's continuous functional calculus spectral measure
along `spectrum ℂ U ↪ ℂ`. -/
noncomputable def cayleyBoundedSpectralMeasure (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    QuantumMechanics.WOTSpectralMeasure ℂ H :=
  let U := cayleyBoundedOperator T hT
  (cfcSpectralMeasure U (cayleyBoundedOperator_isStarNormal T hT)).map
    (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe

lemma cfcSpectralMeasure_reconstruction_coe
    (U : H →L[ℂ] H) (hU : IsStarNormal U) (x y : H) :
    (cfcSpectralMeasure U hU).complexWeakIntegral
        (fun z : spectrum ℂ U => (z.1 : ℂ)) x y = ⟪y, U x⟫_ℂ := by
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [cfcSpectralMeasure_scalarMeasure]
  exact polarizedCfcScalarMeasure_integral_spectrum_coe U hU x y

/-! ## The generic bounded-normal wrapper

The Riesz--Markov construction is carried out on the compact spectrum.  The public spectral
certificate should expose a measure on the ambient scalar field, since that is what the later
functional-calculus and Cayley APIs consume.  This wrapper performs exactly that harmless subtype
pushforward and does not impose any unitary or Cayley support hypothesis.
-/

lemma cfcSpectralMeasure_ambient_reconstruction
    (U : H →L[ℂ] H) (hU : IsStarNormal U) (x y : H) :
    ((cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe).complexWeakIntegral
        id x y = ⟪y, U x⟫_ℂ := by
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_map]
  rw [(MeasurableEmbedding.subtype_coe (spectrum.isClosed
      U).measurableSet).integral_map_vectorMeasure]
  change (cfcSpectralMeasure U hU).complexWeakIntegral
      (fun z : spectrum ℂ U => (z.1 : ℂ)) x y = ⟪y, U x⟫_ℂ
  exact cfcSpectralMeasure_reconstruction_coe U hU x y

/-- The generic bounded normal spectral certificate for `U`, from its continuous functional
calculus. -/
noncomputable def cfcBoundedNormalSpectralData
    (U : H →L[ℂ] H) (hU : IsStarNormal U) :
    QuantumMechanics.WOTSpectralMeasure.BoundedNormalSpectralData U where
  spectralMeasure := (cfcSpectralMeasure U hU).map
    (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe
  reconstruction := cfcSpectralMeasure_ambient_reconstruction U hU

/-! A unitary with no spectral mass at `1` is now the exact input expected by the Cayley inverse.
The only extra work is the support calculation: the normal PVM is pushed forward from the compact
spectrum, and the spectrum of a unitary lies on the unit circle. -/

/-- The bounded unitary spectral certificate for a unitary with no spectral mass at `1`. -/
noncomputable def cfcBoundedUnitarySpectralData
    (u : H ≃ₗᵢ[ℂ] H)
    (h1 : (1 : ℂ) ∉ spectrum ℂ (u : H →L[ℂ] H)) :
    QuantumMechanics.WOTSpectralMeasure.BoundedUnitarySpectralData u := by
  let hu : unitary (H →L[ℂ] H) :=
    (Unitary.linearIsometryEquiv (𝕜 := ℂ) (H := H)).symm u
  let U : H →L[ℂ] H := u
  have hU : IsStarNormal U := by
    exact isStarNormal_of_mem_unitary (by simpa [U, hu] using hu.property)
  let D := cfcBoundedNormalSpectralData U hU
  have hsub : spectrum ℂ U ⊆ Metric.sphere 0 1 := by
    simpa [U, hu] using (Unitary.spectrum_subset_circle hu)
  have hsupport : ∀ S : Set ℂ, MeasurableSet S →
      D.spectralMeasure S = D.spectralMeasure (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1}) := by
    intro S hS
    have hpre : (fun z : spectrum ℂ U => (z : ℂ)) ⁻¹' S =
        (fun z : spectrum ℂ U => (z : ℂ)) ⁻¹'
          (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1}) := by
      ext z
      constructor
      · intro hz
        have hzunit : (z : ℂ) ∈ Metric.sphere 0 1 := hsub z.property
        have hznorm : ‖(z : ℂ)‖ = 1 := by
          have := Metric.mem_sphere.mp hzunit
          simpa [dist_zero_right] using this
        have hznot : (z : ℂ) ≠ 1 := by
          intro hz1
          apply h1
          simpa [U, hz1] using z.property
        exact ⟨hz, hznorm, hznot⟩
      · intro hz
        exact hz.1
    change (cfcSpectralMeasure U hU).map
        (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe S =
      (cfcSpectralMeasure U hU).map
        (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe
          (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1})
    calc
      _ = (cfcSpectralMeasure U hU)
          ((fun z : spectrum ℂ U => (z : ℂ)) ⁻¹' S) :=
        (cfcSpectralMeasure U hU).map_apply
          (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe hS
      _ = (cfcSpectralMeasure U hU)
          ((fun z : spectrum ℂ U => (z : ℂ)) ⁻¹'
            (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1})) := congrArg _ hpre
      _ = _ := ((cfcSpectralMeasure U hU).map_apply
          (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe (hS.inter
            ((measurableSet_eq_fun measurable_norm measurable_const).inter
              (measurableSet_singleton (1 : ℂ)).compl))).symm
  exact {
    spectralMeasure := D.spectralMeasure
    support_away_one := hsupport
    reconstruction := D.reconstruction
  }

lemma cayleyBoundedSpectralMeasure_reconstruction
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x y : H) :
    (cayleyBoundedSpectralMeasure T hT).complexWeakIntegral id x y =
      ⟪y, cayleyBoundedOperator T hT x⟫_ℂ := by
  let U := cayleyBoundedOperator T hT
  let hU : IsStarNormal U := cayleyBoundedOperator_isStarNormal T hT
  change ((cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe).complexWeakIntegral
        id x y = _
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_map]
  rw [(MeasurableEmbedding.subtype_coe (spectrum.isClosed
      U).measurableSet).integral_map_vectorMeasure]
  change (cfcSpectralMeasure U hU).complexWeakIntegral
      (fun z : spectrum ℂ U => (z.1 : ℂ)) x y = ⟪y, U x⟫_ℂ
  exact cfcSpectralMeasure_reconstruction_coe U hU x y

set_option maxHeartbeats 1000000 in
lemma cayleyBoundedSpectralMeasure_scalarMeasure_isFinite
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x y : H) :
    IsFiniteMeasure
      ((cayleyBoundedSpectralMeasure T hT).scalarMeasure x y).variation := by
  let U := cayleyBoundedOperator T hT
  let hU : IsStarNormal U := cayleyBoundedOperator_isStarNormal T hT
  have hp : IsFiniteMeasure
      (polarizedCfcScalarMeasure (hU := hU) U x y).variation :=
    polarizedCfcScalarMeasure_isFiniteMeasure U hU x y
  letI : IsFiniteMeasure
      (polarizedCfcScalarMeasure (hU := hU) U x y).variation := hp
  change IsFiniteMeasure
    (((cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe).scalarMeasure x y).variation
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_map]
  rw [cfcSpectralMeasure_scalarMeasure]
  infer_instance

lemma atom_eigenvector_of_reconstruction
    (E : QuantumMechanics.WOTSpectralMeasure ℂ H) (V : H →L[ℂ] H)
    (hrec : ∀ x y : H, E.complexWeakIntegral id x y = ⟪y, V x⟫_ℂ)
    {a : ℂ} (ha : MeasurableSet {a}) (x : H)
    (hfinite : ∀ y : H, IsFiniteMeasure (E.scalarMeasure x y).variation) :
    V (E {a} x) = a • E {a} x := by
  apply ext_inner_left ℂ
  intro y
  letI : IsFiniteMeasure (E.scalarMeasure x y).variation := hfinite y
  letI : IsFiniteMeasure ((E.scalarMeasure x y).restrict {a}).variation := by
    rw [MeasureTheory.VectorMeasure.variation_restrict ha]
    infer_instance
  have hμ : E.scalarMeasure (E {a} x) y = (E.scalarMeasure x y).restrict {a} := by
    apply MeasureTheory.VectorMeasure.ext
    intro S hS
    rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply,
      MeasureTheory.VectorMeasure.restrict_apply _ ha hS,
      QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
    change ⟪y, (E S * E {a}) x⟫_ℂ = _
    rw [E.comp_eq_of_inter hS ha]
  rw [← hrec (E {a} x) y]
  change (∫ᵛ z, id z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      E.scalarMeasure (E {a} x) y]) = _
  rw [hμ]
  change (∫ᵛ z in {a}, id z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      E.scalarMeasure x y]) = _
  have hid :
      (∫ᵛ z in {a}, id z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        E.scalarMeasure x y]) =
        ∫ᵛ _ in {a}, a ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
          E.scalarMeasure x y] := by
    apply VectorMeasure.integral_congr_ae
    rw [MeasureTheory.VectorMeasure.variation_restrict ha]
    filter_upwards [ae_restrict_mem ha] with z hz
    simpa [Set.mem_singleton_iff] using hz
  rw [hid]
  change (∫ᵛ _ : ℂ, a ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
      (E.scalarMeasure x y).restrict {a}]) = _
  rw [VectorMeasure.integral_const]
  rw [MeasureTheory.VectorMeasure.restrict_apply_univ]
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
  simp [inner_smul_right]

lemma cayleyBoundedSpectralMeasure_support_unit_circle
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (S : Set ℂ) (hS : MeasurableSet S) :
    cayleyBoundedSpectralMeasure T hT S =
      cayleyBoundedSpectralMeasure T hT (S ∩ {z | ‖z‖ = 1}) := by
  let U := cayleyBoundedOperator T hT
  let hU : IsStarNormal U := cayleyBoundedOperator_isStarNormal T hT
  have hu : U ∈ unitary (H →L[ℂ] H) := cayleyBoundedOperator_mem_unitary T hT
  change (cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe S =
    (cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe (S ∩ {z | ‖z‖ = 1})
  change (cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe S =
    (cfcSpectralMeasure U hU).map
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe
        (S ∩ (fun z : ℂ => ‖z‖) ⁻¹' ({1} : Set ℝ))
  rw [(cfcSpectralMeasure U hU).map_apply
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe hS,
    (cfcSpectralMeasure U hU).map_apply
      (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe
      (hS.inter (((isClosed_singleton : IsClosed ({1} : Set ℝ)).preimage
        continuous_norm).measurableSet))]
  congr 1
  ext z
  constructor
  · intro hz
    refine ⟨hz, ?_⟩
    exact spectrum.norm_eq_one_of_unitary hu z.property
  · exact fun hz => hz.1

lemma cayleyBoundedOperator_one_eigenspace_eq_bot
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) {x : H}
    (hx : cayleyBoundedOperator T hT x = x) : x = 0 := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have heq : T - (-Complex.I) • 1 = T + Complex.I • 1 := by
    exact LinearPMap.ext rfl fun z hz hz' => by
      simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, neg_smul]
  have hker : (T + Complex.I • 1).toFun.ker = ⊥ := by
    rw [← heq]
    exact hres.1
  have hrange : (T + Complex.I • 1).toFun.range = ⊤ := by
    rw [← heq]
    exact hres.2.1
  have hinvdom : (T + Complex.I • 1).inverse.domain = ⊤ := by
    rw [LinearPMap.inverse_domain, hrange]
  let xi : (T + Complex.I • 1).inverse.domain :=
    ⟨x, by rw [hinvdom]; exact Submodule.mem_top⟩
  have hxi : (T + Complex.I • 1).inverse xi ∈ (T + Complex.I • 1).domain := by
    rw [← LinearPMap.inverse_range hker]
    exact LinearMap.mem_range_self _ xi
  let y : (T + Complex.I • 1).domain :=
    ⟨(T + Complex.I • 1).inverse xi, hxi⟩
  have hxrange : x ∈ (T + Complex.I • 1).toFun.range := by
    rw [hrange]
    exact Submodule.mem_top
  obtain ⟨x₀, hx₀⟩ := hxrange
  have hxy : (T + Complex.I • 1) x₀ = xi := by
    change (T + Complex.I • 1) x₀ = x
    exact hx₀
  have hinv₀ : (T + Complex.I • 1).inverse xi = x₀ :=
    LinearPMap.inverse_apply_eq hker hxy
  have hy : (T + Complex.I • 1) y = x := by
    have heq : y = x₀ := Subtype.ext hinv₀
    rw [heq]
    exact hx₀
  have hminus : (T - Complex.I • 1) y = x := by
    calc
      (T - Complex.I • 1) y = cayleyContinuousLinearMap T hT x := by
        symm
        exact cayleyContinuousLinearMap_apply_of_mem_range hT y x hy
      _ = cayleyBoundedOperator T hT x := by
        rw [cayleyBoundedOperator_apply]
      _ = x := hx
  have hdiff : (T + Complex.I • 1) y - (T - Complex.I • 1) y = 0 := by
    rw [hy, hminus]
    simp
  have hplusdom : (T + Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.add_domain]
  let yt : T.domain := ⟨(y : H), by rw [← hplusdom]; exact y.property⟩
  have hdiff' : (T yt + Complex.I • (y : H)) -
      (T yt - Complex.I • (y : H)) = 0 := by
    simpa [LinearPMap.add_apply, LinearPMap.sub_apply, LinearPMap.smul_apply] using hdiff
  have hy0 : (y : H) = 0 := by
    have hscalar : (2 * Complex.I) • (y : H) = 0 := by
      have heq : Complex.I • (y : H) = -(Complex.I • (y : H)) := by
        apply add_left_cancel (a := T yt)
        simpa [sub_eq_add_neg] using (sub_eq_zero.mp hdiff')
      calc
        (2 * Complex.I) • (y : H) = (Complex.I + Complex.I) • (y : H) := by ring
        _ = Complex.I • (y : H) + Complex.I • (y : H) := by rw [add_smul]
        _ = Complex.I • (y : H) + -(Complex.I • (y : H)) :=
          congrArg (fun q => Complex.I • (y : H) + q) heq
        _ = 0 := add_neg_cancel _
    exact (smul_eq_zero.mp hscalar).resolve_left (by norm_num)
  calc
    x = (T + Complex.I • 1) y := hy.symm
    _ = 0 := by
      have hy' : y = 0 := Subtype.ext hy0
      rw [hy']
      simp

set_option maxHeartbeats 1000000

lemma cayleyBoundedSpectralMeasure_id_integrable
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x y : H) :
    ((cayleyBoundedSpectralMeasure T hT).scalarMeasure x y).Integrable id := by
  let E := cayleyBoundedSpectralMeasure T hT
  let C : Set ℂ := {z | ‖z‖ = 1}
  have hC : MeasurableSet C := by
    dsimp [C]
    exact measurableSet_eq_fun measurable_norm measurable_const
  have hfinite : IsFiniteMeasure (E.scalarMeasure x y).variation := by
    exact cayleyBoundedSpectralMeasure_scalarMeasure_isFinite T hT x y
  letI := hfinite
  have hrestrict : E.scalarMeasure x y = (E.scalarMeasure x y).restrict C := by
    apply MeasureTheory.VectorMeasure.ext
    intro S hS
    rw [MeasureTheory.VectorMeasure.restrict_apply (E.scalarMeasure x y) hC hS]
    rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply,
      QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
    rw [cayleyBoundedSpectralMeasure_support_unit_circle T hT S hS]
  rw [hrestrict]
  change MeasureTheory.Integrable id ((E.scalarMeasure x y).restrict C).variation
  rw [MeasureTheory.VectorMeasure.variation_restrict hC]
  apply MeasureTheory.Integrable.of_bound measurable_id.aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem hC] with z hz
  calc
    ‖z‖ = 1 := hz
    _ ≤ 1 := le_rfl

lemma cayleyBoundedSpectralMeasure_singleton_one
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    cayleyBoundedSpectralMeasure T hT {1} = 0 := by
  let U := cayleyBoundedOperator T hT
  let hU : IsStarNormal U := cayleyBoundedOperator_isStarNormal T hT
  let E := cayleyBoundedSpectralMeasure T hT
  have hrec : ∀ x y : H, E.complexWeakIntegral id x y = ⟪y, U x⟫_ℂ := by
    intro x y
    exact cayleyBoundedSpectralMeasure_reconstruction T hT x y
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  have hfinite : ∀ y : H, IsFiniteMeasure (E.scalarMeasure x y).variation := by
    intro y
    have hp : IsFiniteMeasure
        (polarizedCfcScalarMeasure (hU := hU) U x y).variation := by
      unfold polarizedCfcScalarMeasure
      have hsub (a b : H) : IsFiniteMeasure
          (((1 / 4 : ℝ) • ((cfcScalarMeasure U hU a).toSignedMeasure -
            (cfcScalarMeasure U hU b).toSignedMeasure)).variation) := by
        letI : IsFiniteMeasure (cfcScalarMeasure U hU a).toSignedMeasure.variation := by
          rw [Measure.variation_toSignedMeasure]
          infer_instance
        letI : IsFiniteMeasure (cfcScalarMeasure U hU b).toSignedMeasure.variation := by
          rw [Measure.variation_toSignedMeasure]
          infer_instance
        apply isFiniteMeasure_of_le
          (cfcScalarMeasure U hU a + cfcScalarMeasure U hU b)
        rw [MeasureTheory.VectorMeasure.variation_smul]
        have hv : ((cfcScalarMeasure U hU a).toSignedMeasure -
            (cfcScalarMeasure U hU b).toSignedMeasure).variation ≤
            cfcScalarMeasure U hU a + cfcScalarMeasure U hU b := by
          simpa only [Measure.variation_toSignedMeasure] using
            (MeasureTheory.VectorMeasure.variation_sub_le
              (μ := (cfcScalarMeasure U hU a).toSignedMeasure)
              (ν := (cfcScalarMeasure U hU b).toSignedMeasure))
        calc
          ‖(1 / 4 : ℝ)‖₊ •
              ((cfcScalarMeasure U hU a).toSignedMeasure -
                (cfcScalarMeasure U hU b).toSignedMeasure).variation ≤
              (1 : ENNReal) • ((cfcScalarMeasure U hU a).toSignedMeasure -
                (cfcScalarMeasure U hU b).toSignedMeasure).variation := by
            change ((‖(1 / 4 : ℝ)‖₊ : NNReal) : ENNReal) •
                ((cfcScalarMeasure U hU a).toSignedMeasure -
                  (cfcScalarMeasure U hU b).toSignedMeasure).variation ≤
              (1 : ENNReal) • ((cfcScalarMeasure U hU a).toSignedMeasure -
                (cfcScalarMeasure U hU b).toSignedMeasure).variation
            gcongr
            norm_num
          _ ≤ (1 : ENNReal) • (cfcScalarMeasure U hU a + cfcScalarMeasure U hU b) := by
            simpa only [one_smul] using hv
          _ = cfcScalarMeasure U hU a + cfcScalarMeasure U hU b := by simp
      apply isFiniteMeasure_toComplexMeasure
    letI : IsFiniteMeasure
        (polarizedCfcScalarMeasure (hU := hU) U x y).variation := hp
    change IsFiniteMeasure
      (((cfcSpectralMeasure U hU).map
        (fun z : spectrum ℂ U => (z : ℂ)) measurable_subtype_coe).scalarMeasure x y).variation
    rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_map]
    rw [cfcSpectralMeasure_scalarMeasure]
    infer_instance
  have hAtom := atom_eigenvector_of_reconstruction (a := (1 : ℂ)) E U hrec
    (measurableSet_singleton (1 : ℂ)) x hfinite
  have hzero : E {1} x = 0 := by
    apply cayleyBoundedOperator_one_eigenspace_eq_bot T hT
    simpa using hAtom
  simpa [E] using congrArg (fun v : H => ⟪y, v⟫_ℂ) hzero

lemma cayleyBoundedSpectralMeasure_support_away_one
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (S : Set ℂ) (hS : MeasurableSet S) :
    cayleyBoundedSpectralMeasure T hT S =
      cayleyBoundedSpectralMeasure T hT (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1}) := by
  let E := cayleyBoundedSpectralMeasure T hT
  have hC : MeasurableSet ({z : ℂ | ‖z‖ = 1}) :=
    ((isClosed_singleton : IsClosed ({1} : Set ℝ)).preimage continuous_norm).measurableSet
  have h1 : MeasurableSet ({(1 : ℂ)} : Set ℂ) := measurableSet_singleton 1
  have hne : MeasurableSet ({z : ℂ | z ≠ 1}) := h1.compl
  have hA : MeasurableSet (S ∩ {z : ℂ | ‖z‖ = 1}) := hS.inter hC
  have hB : MeasurableSet (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ)) :=
    (hS.inter hC).inter h1
  have hB' : MeasurableSet (S ∩ {z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | z ≠ 1}) :=
    (hS.inter hC).inter hne
  have hunion :
      (S ∩ {z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | z ≠ 1}) ∪
          (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ)) =
        S ∩ {z : ℂ | ‖z‖ = 1} := by
    ext z
    by_cases hz : z = 1 <;> simp [hz]
  have hdisj : Disjoint
      (S ∩ {z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | z ≠ 1})
      (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ)) := by
    refine Set.disjoint_left.2 ?_
    intro z hz hz'
    exact hz.2 hz'.2
  have hzeroB : E (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ)) = 0 := by
    have hcomp := E.comp_eq_of_inter hB h1
    have hinter :
        (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ)) ∩ ({(1 : ℂ)} : Set ℂ) =
          S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ) := by
      ext z
      simp
    rw [hinter, cayleyBoundedSpectralMeasure_singleton_one T hT] at hcomp
    simpa using hcomp.symm
  calc
    E S = E (S ∩ {z : ℂ | ‖z‖ = 1}) :=
      cayleyBoundedSpectralMeasure_support_unit_circle T hT S hS
    _ = E ((S ∩ {z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | z ≠ 1}) ∪
        (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ))) := by rw [hunion]
    _ = E (S ∩ {z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | z ≠ 1}) +
        E (S ∩ {z : ℂ | ‖z‖ = 1} ∩ ({(1 : ℂ)} : Set ℂ)) :=
      E.of_union hdisj hB' hB
    _ = E (S ∩ {z : ℂ | ‖z‖ = 1} ∩ {z : ℂ | z ≠ 1}) := by
      rw [hzeroB]
      simp
    _ = E (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1}) := by
      congr 1
      ext z
      simp [and_assoc, and_left_comm, and_comm]

lemma cayleyInverse_mul_one_sub_of_unit_circle
    {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    (cayleyInverse z : ℂ) * (1 - z) = Complex.I * (1 + z) := by
  let x : ℝ := cayleyInverse z
  have hx : cayley x = z := by
    exact cayley_cayleyInverse hz hz1
  change (x : ℂ) * (1 - z) = Complex.I * (1 + z)
  rw [← hx]
  unfold cayley
  have hden : (x : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  field_simp [hden]
  ring

lemma cayley_domain_factorization
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x : T.domain) :
    ∃ v : H,
      (x : H) = v - cayleyBoundedOperator T hT v ∧
        T x = Complex.I • (v + cayleyBoundedOperator T hT v) := by
  let hplusdom : (T + Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.add_domain]
  let xp : (T + Complex.I • 1).domain :=
    ⟨(x : H), by rw [hplusdom]; exact x.property⟩
  let a : H := (T + Complex.I • 1) xp
  let v : H := (2 * Complex.I)⁻¹ • a
  have ha : cayleyBoundedOperator T hT a = (T - Complex.I • 1) xp := by
    rw [cayleyBoundedOperator_apply]
    exact cayleyContinuousLinearMap_apply_of_mem_range hT xp a rfl
  have h2i : (2 * Complex.I : ℂ) ≠ 0 := by norm_num
  have hxpinf : (xp : H) ∈ T.domain ⊓
      (Complex.I • (1 : H →ₗ.[ℂ] H)).domain := by
    rw [← LinearPMap.add_domain]
    exact xp.property
  have hxmem : (xp : H) ∈ T.domain ∧
      (xp : H) ∈ (Complex.I • (1 : H →ₗ.[ℂ] H)).domain := by
    exact ⟨hxpinf.1, hxpinf.2⟩
  have hxpT : (⟨(xp : H), hxmem.1⟩ : T.domain) = x := by
    apply Subtype.ext
    rfl
  have hxp_coe : (xp : H) = (x : H) := by
    rfl
  refine ⟨v, ?_, ?_⟩
  · dsimp [v, a]
    rw [map_smul, ha]
    field_simp [h2i]
    simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, hxmem, hxpT,
      smul_add, smul_sub, smul_smul, div_eq_mul_inv, Complex.inv_I, Complex.I_mul_I,
      pow_two] <;>
      field_simp [h2i] <;> (try module) <;>
      norm_num [Complex.I_sq, Complex.I_mul_I, pow_two] <;>
      simp [hxp_coe] <;> module

  · dsimp [v, a]
    rw [map_smul, ha]
    field_simp [h2i]
    simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, hxmem, hxpT,
      smul_add, smul_sub, smul_smul, div_eq_mul_inv, Complex.inv_I, Complex.I_mul_I,
      pow_two] <;>
      field_simp [h2i] <;> (try module) <;>
      norm_num [Complex.I_sq, Complex.I_mul_I, pow_two] <;>
      simp [hxp_coe] <;> module

/-! ### A bounded extension of the Cayley difference multiplier

The algebraic factor `1 - z` is bounded on the unit circle, which is the support of the
bounded Cayley spectral measure, but it is not bounded on all of `ℂ`.  The bounded integral
API quite correctly asks for a global bound.  We therefore use the zero extension outside the
closed unit disk; support reduction makes it equal to `1 - z` wherever the spectral measure
sees it.
-/

/-- `z ↦ 1 - z` on the unit circle, extended by zero elsewhere so it is globally bounded. -/
def cayleyDifferenceMultiplier (z : ℂ) : ℂ :=
  if ‖z‖ = 1 then 1 - z else 0

lemma cayleyDifferenceMultiplier_measurable :
    Measurable cayleyDifferenceMultiplier := by
  unfold cayleyDifferenceMultiplier
  exact Measurable.ite (measurableSet_eq_fun measurable_norm measurable_const)
    (measurable_const.sub measurable_id) measurable_const

lemma cayleyDifferenceMultiplier_bounded :
    ∃ C : ℝ, ∀ z : ℂ, ‖cayleyDifferenceMultiplier z‖ ≤ C := by
  refine ⟨2, fun z => ?_⟩
  by_cases hz : ‖z‖ = 1
  · simp [cayleyDifferenceMultiplier, hz]
    exact (norm_sub_le _ _).trans (by norm_num; linarith)
  · simp [cayleyDifferenceMultiplier, hz]

lemma cayleyDifferenceMultiplier_eq_one_sub_of_unit_circle {z : ℂ} (hz : ‖z‖ = 1) :
    cayleyDifferenceMultiplier z = 1 - z := by
  simp [cayleyDifferenceMultiplier, hz]

lemma boundedIntegral_cayleyDifferenceMultiplier_eq_sub
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    QuantumMechanics.WOTSpectralMeasure.boundedIntegral (cayleyBoundedSpectralMeasure T hT)
        cayleyDifferenceMultiplier cayleyDifferenceMultiplier_measurable
        cayleyDifferenceMultiplier_bounded =
      (1 : H →WOT[ℂ] H) -
        ContinuousLinearMapWOT.ofCLM (cayleyBoundedOperator T hT) := by
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  have hfinite := cayleyBoundedSpectralMeasure_scalarMeasure_isFinite T hT x y
  let ν := (cayleyBoundedSpectralMeasure T hT).scalarMeasure x y
  let A : Set ℂ := {z : ℂ | ‖z‖ = 1 ∧ z ≠ 1}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact (measurableSet_eq_fun measurable_norm measurable_const).inter
      (measurableSet_singleton (1 : ℂ)).compl
  have hνA : ν = ν.restrict {z : ℂ | ‖z‖ = 1 ∧ z ≠ 1} := by
    apply MeasureTheory.VectorMeasure.ext
    intro S hS
    rw [MeasureTheory.VectorMeasure.restrict_apply ν
      hA hS]
    change ⟪y, (cayleyBoundedSpectralMeasure T hT) S x⟫_ℂ =
      ⟪y, (cayleyBoundedSpectralMeasure T hT)
        (S ∩ {z : ℂ | ‖z‖ = 1 ∧ z ≠ 1}) x⟫_ℂ
    rw [cayleyBoundedSpectralMeasure_support_away_one T hT S hS]
  have hνA' : ν = ν.restrict A := by simpa [A] using hνA
  letI := hfinite
  have hA_ae : ∀ᵐ z ∂ν.variation, ‖z‖ = 1 ∧ z ≠ 1 := by
    have hvar : ν.variation = (ν.restrict A).variation := congrArg
      MeasureTheory.VectorMeasure.variation hνA'
    rw [hvar, MeasureTheory.VectorMeasure.variation_restrict hA]
    exact ae_restrict_mem hA
  have hq_ae : cayleyDifferenceMultiplier =ᵐ[ν.variation]
      (fun z : ℂ => (1 : ℂ) - z) := by
    filter_upwards [hA_ae] with z hz
    exact cayleyDifferenceMultiplier_eq_one_sub_of_unit_circle hz.1
  have hconst : ν.Integrable (fun _ : ℂ => (1 : ℂ)) := by
    exact MeasureTheory.integrable_const (μ := ν.variation) (c := (1 : ℂ))
  have hfi : ν.Integrable id :=
    cayleyBoundedSpectralMeasure_id_integrable T hT x y
  have hq : ν.Integrable (fun z : ℂ => (1 : ℂ) - z) := hconst.sub hfi
  have hqbd : ν.Integrable cayleyDifferenceMultiplier := by
    exact hq.congr hq_ae.symm
  have hqint : ∫ᵛ z, cayleyDifferenceMultiplier z ∂[
      ContinuousLinearMap.lsmul ℝ ℂ; ν] =
      ∫ᵛ z, ((1 : ℂ) - z) ∂[
        ContinuousLinearMap.lsmul ℝ ℂ; ν] :=
    VectorMeasure.integral_congr_ae hq_ae
  have hsub : ∫ᵛ z, ((1 : ℂ) - z) ∂[
      ContinuousLinearMap.lsmul ℝ ℂ; ν] =
      ⟪y, x⟫_ℂ - ⟪y, cayleyBoundedOperator T hT x⟫_ℂ := by
    have hdiff : ν.Integrable (fun z : ℂ => (1 : ℂ) - z) := hq
    change ∫ᵛ z, ((fun _ : ℂ => (1 : ℂ)) z - id z) ∂[
      ContinuousLinearMap.lsmul ℝ ℂ; ν] = _
    rw [VectorMeasure.integral_fun_sub hconst hfi]
    rw [VectorMeasure.integral_const]
    rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
    rw [QuantumMechanics.WOTSpectralMeasure.univ]
    simp only [ContinuousLinearMap.lsmul_apply, one_smul]
    change ⟪y, x⟫_ℂ - (∫ᵛ z, id z ∂[
      ContinuousLinearMap.lsmul ℝ ℂ; ν]) = _
    rw [show (∫ᵛ z, id z ∂[
        ContinuousLinearMap.lsmul ℝ ℂ; ν]) =
        ⟪y, cayleyBoundedOperator T hT x⟫_ℂ by
      change (cayleyBoundedSpectralMeasure T hT).complexWeakIntegral id x y = _
      exact cayleyBoundedSpectralMeasure_reconstruction T hT x y]
  change ⟪y, QuantumMechanics.WOTSpectralMeasure.boundedIntegral
      (cayleyBoundedSpectralMeasure T hT)
      cayleyDifferenceMultiplier cayleyDifferenceMultiplier_measurable
      cayleyDifferenceMultiplier_bounded x⟫_ℂ = _
  rw [QuantumMechanics.WOTSpectralMeasure.boundedIntegral_inner
    (cayleyBoundedSpectralMeasure T hT) cayleyDifferenceMultiplier_measurable
    cayleyDifferenceMultiplier_bounded x y hfinite]
  rw [hqint, hsub]
  simp [inner_sub_right]

/-- The bounded unitary spectral certificate for `T`'s Cayley unitary. -/
noncomputable def cayleyBoundedUnitarySpectralData
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    QuantumMechanics.WOTSpectralMeasure.BoundedUnitarySpectralData
      (cayleyUnitary T hT) where
  spectralMeasure := cayleyBoundedSpectralMeasure T hT
  support_away_one := fun S hS => cayleyBoundedSpectralMeasure_support_away_one T hT S hS
  reconstruction := by
    intro x y
    simpa [cayleyUnitary_apply, cayleyBoundedOperator_apply] using
      cayleyBoundedSpectralMeasure_reconstruction T hT x y

/-- The real spectral measure of `T`, transported from its Cayley unitary's bounded unitary
spectral data. -/
noncomputable def cayleyRealSpectralMeasure
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    QuantumMechanics.WOTSpectralMeasure ℝ H :=
  (cayleyBoundedUnitarySpectralData T hT).realSpectralMeasure

lemma cayleyMap_cayleyRealSpectralMeasure
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    QuantumMechanics.WOTSpectralMeasure.cayleyMap (cayleyRealSpectralMeasure T hT) =
      cayleyBoundedSpectralMeasure T hT := by
  exact (cayleyBoundedUnitarySpectralData T hT).cayleyMap_realSpectralMeasure

lemma cayleyRealSpectralMeasure_mem_domain
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x : T.domain) :
    (x : H) ∈ OperatorAlgebra.spectralSquareMomentDomain
      (cayleyRealSpectralMeasure T hT) := by
  let E := cayleyBoundedSpectralMeasure T hT
  let q := cayleyDifferenceMultiplier
  obtain ⟨v, hx, _⟩ := cayley_domain_factorization T hT x
  have hqv : QuantumMechanics.WOTSpectralMeasure.boundedIntegral E q
      cayleyDifferenceMultiplier_measurable cayleyDifferenceMultiplier_bounded v =
      v - cayleyBoundedOperator T hT v := by
    have h := congrArg (fun A : H →WOT[ℂ] H => A v)
      (boundedIntegral_cayleyDifferenceMultiplier_eq_sub T hT)
    simpa [E, q] using h
  have hxeq : (x : H) = QuantumMechanics.WOTSpectralMeasure.boundedIntegral E q
      cayleyDifferenceMultiplier_measurable cayleyDifferenceMultiplier_bounded v :=
    hx.trans hqv.symm
  have hdiag : E.diagonalMeasure ((x : H)) =
      Measure.withDensity (E.diagonalMeasure v)
        (fun z => ENNReal.ofReal (‖q z‖ ^ 2)) := by
    rw [hxeq]
    exact QuantumMechanics.WOTSpectralMeasure.diagonalMeasure_boundedIntegral_eq_withDensity E
      cayleyDifferenceMultiplier_measurable cayleyDifferenceMultiplier_bounded v
  let A : Set ℂ := {z : ℂ | ‖z‖ = 1 ∧ z ≠ 1}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact (measurableSet_eq_fun measurable_norm measurable_const).inter
      (measurableSet_singleton (1 : ℂ)).compl
  have hdiagA : E.diagonalMeasure v = (E.diagonalMeasure v).restrict A := by
    apply Measure.ext
    intro S hS
    rw [MeasureTheory.Measure.restrict_apply hS]
    rw [E.diagonalMeasure_apply_eq_norm_sq v S hS,
      E.diagonalMeasure_apply_eq_norm_sq v (S ∩ A) (hS.inter hA)]
    have hs := cayleyBoundedSpectralMeasure_support_away_one T hT S hS
    have hvec : (E S) v = (E (S ∩ A)) v := by
      simpa [A] using congrArg (fun P : H →WOT[ℂ] H => P v) hs
    rw [hvec]
  have hA_ae : ∀ᵐ z ∂E.diagonalMeasure v, z ∈ A := by
    rw [hdiagA]
    exact ae_restrict_mem hA
  have hbase : Integrable (fun z : ℂ => (cayleyInverse z) ^ 2)
      (E.diagonalMeasure ((x : H))) := by
    rw [hdiag]
    let d : ℂ → ENNReal := fun z => ENNReal.ofReal (‖q z‖ ^ 2)
    have hd : Measurable d := ENNReal.continuous_ofReal.measurable.comp
      (cayleyDifferenceMultiplier_measurable.norm.pow_const 2)
    have hd_top : ∀ᵐ z ∂E.diagonalMeasure v, d z < (⊤ : ENNReal) := by
      filter_upwards [] with z
      exact (lt_top_iff_ne_top).2 (ENNReal.ofReal_ne_top)
    apply (integrable_withDensity_iff_integrable_smul₀' hd.aemeasurable hd_top).2
    have hmeas : AEStronglyMeasurable (fun z : ℂ =>
        (d z).toReal • (cayleyInverse z) ^ 2) (E.diagonalMeasure v) := by
      change AEStronglyMeasurable
        ((fun z : ℂ => (d z).toReal) * (fun z : ℂ => (cayleyInverse z) ^ 2))
        (E.diagonalMeasure v)
      exact hd.ennreal_toReal.aestronglyMeasurable.mul
        (measurable_cayleyInverse.pow_const 2).aestronglyMeasurable
    apply Integrable.of_bound hmeas 4
    filter_upwards [hA_ae] with z hz
    have hzid := cayleyInverse_mul_one_sub_of_unit_circle hz.1 hz.2
    have hqz : q z = 1 - z := cayleyDifferenceMultiplier_eq_one_sub_of_unit_circle hz.1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (cayleyInverse z))]
    rw [show d z = ENNReal.ofReal (‖1 - z‖ ^ 2) by
      dsimp [d]
      rw [hqz],
      ENNReal.toReal_ofReal (sq_nonneg ‖1 - z‖)]
    have hprod : ‖(cayleyInverse z : ℂ) * (1 - z)‖ ≤ 2 := by
      rw [hzid]
      calc
        ‖Complex.I * (1 + z)‖ = ‖1 + z‖ := by rw [norm_mul]; simp
        _ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
        _ = 2 := by rw [hz.1]; norm_num
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hprod
    have hprod_nonneg : 0 ≤ |cayleyInverse z| * ‖1 - z‖ :=
      mul_nonneg (abs_nonneg _) (norm_nonneg _)
    have hsq := (sq_le_sq₀ hprod_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr hprod
    calc
      ‖1 - z‖ ^ 2 * cayleyInverse z ^ 2 =
          (|cayleyInverse z| * ‖1 - z‖) ^ 2 := by
            rw [mul_pow, sq_abs]
            ring
      _ ≤ 2 ^ 2 := hsq
      _ = 4 := by norm_num
  rw [OperatorAlgebra.mem_spectralSquareMomentDomain_iff]
  rw [show (cayleyRealSpectralMeasure T hT).diagonalMeasure (x : H) =
      Measure.map cayleyInverse (E.diagonalMeasure (x : H)) by
    change (E.map cayleyInverse measurable_cayleyInverse).diagonalMeasure (x : H) = _
    exact E.diagonalMeasure_map cayleyInverse measurable_cayleyInverse (x : H)]
  apply (integrable_map_measure
    ((measurable_id.pow_const 2).aestronglyMeasurable)
    measurable_cayleyInverse.aemeasurable).2
  simpa [Function.comp_def] using hbase

/-! ### Restriction identities for PVM scalar measures

These identities are independent of the Cayley transform.  They express the elementary fact
that testing a projection-valued measure after applying one of its projections restricts the
corresponding scalar measure.  They are the bookkeeping lemmas needed when a bounded spectral
moment is localized to a measurable spectral set.
-/

lemma WOTSpectralMeasure.scalarMeasure_proj_left_restrict
    {α : Type*} [MeasurableSpace α]
    (μ : QuantumMechanics.WOTSpectralMeasure α H) {S : Set α} (hS : MeasurableSet S)
    (x y : H) :
    μ.scalarMeasure (μ S x) y = (μ.scalarMeasure x y).restrict S := by
  apply MeasureTheory.VectorMeasure.ext
  intro A hA
  change μ.scalarMeasure (μ S x) y A = (μ.scalarMeasure x y).restrict S A
  rw [MeasureTheory.VectorMeasure.restrict_apply (μ.scalarMeasure x y) hS hA]
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply,
    QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
  change ⟪y, μ A (μ S x)⟫_ℂ = _
  change ⟪y, (μ A * μ S) x⟫_ℂ = _
  rw [μ.comp_eq_of_inter hA hS]

lemma WOTSpectralMeasure.scalarMeasure_proj_right_restrict
    {α : Type*} [MeasurableSpace α]
    (μ : QuantumMechanics.WOTSpectralMeasure α H) {S : Set α} (hS : MeasurableSet S)
    (x y : H) :
    μ.scalarMeasure x (μ S y) = (μ.scalarMeasure x y).restrict S := by
  apply MeasureTheory.VectorMeasure.ext
  intro A hA
  change μ.scalarMeasure x (μ S y) A = (μ.scalarMeasure x y).restrict S A
  rw [MeasureTheory.VectorMeasure.restrict_apply (μ.scalarMeasure x y) hS hA]
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply,
    QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
  change ⟪μ S y, μ A x⟫_ℂ = _
  calc
    ⟪μ S y, μ A x⟫_ℂ = ⟪y, μ S (μ A x)⟫_ℂ := by
      change ⟪ContinuousLinearMapWOT.toCLM (μ S) y, μ A x⟫_ℂ =
        ⟪y, ContinuousLinearMapWOT.toCLM (μ S) (μ A x)⟫_ℂ
      have hstar : star (ContinuousLinearMapWOT.toCLM (μ S)) =
          ContinuousLinearMapWOT.toCLM (μ S) :=
        congrArg ContinuousLinearMapWOT.toCLM (μ.isStarProjection S).isSelfAdjoint
      have hstar' : ContinuousLinearMap.adjoint (ContinuousLinearMapWOT.toCLM (μ S)) =
          ContinuousLinearMapWOT.toCLM (μ S) := by
        rw [← ContinuousLinearMap.star_eq_adjoint]
        exact hstar
      calc
        ⟪ContinuousLinearMapWOT.toCLM (μ S) y, μ A x⟫_ℂ =
            ⟪ContinuousLinearMap.adjoint (ContinuousLinearMapWOT.toCLM (μ S)) y,
              μ A x⟫_ℂ := by rw [hstar']
        _ = ⟪y, ContinuousLinearMapWOT.toCLM (μ S) (μ A x)⟫_ℂ :=
          ContinuousLinearMap.adjoint_inner_left (ContinuousLinearMapWOT.toCLM (μ S))
            (μ A x) y
    _ = ⟪y, (μ S * μ A) x⟫_ℂ := rfl
    _ = ⟪y, μ (S ∩ A) x⟫_ℂ := by
      rw [μ.comp_eq_of_inter hS hA]
    _ = ⟪y, μ (A ∩ S) x⟫_ℂ := by rw [inter_comm]
    _ = _ := rfl

@[nolint unusedArguments]
lemma WOTSpectralMeasure.complexWeakIntegral_proj_left
    {α : Type*} [MeasurableSpace α]
    (μ : QuantumMechanics.WOTSpectralMeasure α H) {S : Set α} (hS : MeasurableSet S)
    (g : α → ℂ) (x y : H)
    (hgi : (μ.scalarMeasure x y).Integrable g) :
    μ.complexWeakIntegral g (μ S x) y =
      ∫ᵛ z, Set.indicator S g z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μ.scalarMeasure x y] := by
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [WOTSpectralMeasure.scalarMeasure_proj_left_restrict μ hS]
  exact (MeasureTheory.VectorMeasure.integral_indicator
    (μ := μ.scalarMeasure x y) (f := g) hS).symm

@[nolint unusedArguments]
lemma WOTSpectralMeasure.complexWeakIntegral_proj_right
    {α : Type*} [MeasurableSpace α]
    (μ : QuantumMechanics.WOTSpectralMeasure α H) {S : Set α} (hS : MeasurableSet S)
    (g : α → ℂ) (x y : H)
    (hgi : (μ.scalarMeasure x y).Integrable g) :
    μ.complexWeakIntegral g x (μ S y) =
      ∫ᵛ z, Set.indicator S g z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μ.scalarMeasure x y] := by
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [WOTSpectralMeasure.scalarMeasure_proj_right_restrict μ hS]
  exact (MeasureTheory.VectorMeasure.integral_indicator
    (μ := μ.scalarMeasure x y) (f := g) hS).symm

lemma WOTSpectralMeasure.reconstruction_commutes_projection
    {α : Type*} [MeasurableSpace α]
    (μ : QuantumMechanics.WOTSpectralMeasure α H) (U : H →L[ℂ] H)
    (f : α → ℂ)
    (hrec : ∀ x y, μ.complexWeakIntegral f x y = ⟪y, U x⟫_ℂ)
    (hfi : ∀ x y, (μ.scalarMeasure x y).Integrable f)
    {S : Set α} (hS : MeasurableSet S) :
    μ S * ContinuousLinearMapWOT.ofCLM U =
      ContinuousLinearMapWOT.ofCLM U * μ S := by
  apply ContinuousLinearMapWOT.ext_inner
  intro x y
  have hstar : star (ContinuousLinearMapWOT.toCLM (μ S)) =
      ContinuousLinearMapWOT.toCLM (μ S) :=
    congrArg ContinuousLinearMapWOT.toCLM (μ.isStarProjection S).isSelfAdjoint
  have hstar' : ContinuousLinearMap.adjoint (ContinuousLinearMapWOT.toCLM (μ S)) =
      ContinuousLinearMapWOT.toCLM (μ S) := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hstar
  have hproj : ⟪y, μ S (U x)⟫_ℂ = ⟪μ S y, U x⟫_ℂ := by
    change ⟪y, ContinuousLinearMapWOT.toCLM (μ S) (U x)⟫_ℂ =
      ⟪ContinuousLinearMapWOT.toCLM (μ S) y, U x⟫_ℂ
    calc
      ⟪y, ContinuousLinearMapWOT.toCLM (μ S) (U x)⟫_ℂ =
          ⟪y, ContinuousLinearMap.adjoint (ContinuousLinearMapWOT.toCLM (μ S))
            (U x)⟫_ℂ := by rw [hstar']
      _ = ⟪ContinuousLinearMapWOT.toCLM (μ S) y, U x⟫_ℂ :=
        ContinuousLinearMap.adjoint_inner_right
          (ContinuousLinearMapWOT.toCLM (μ S)) y (U x)
  calc
    ⟪y, (μ S * ContinuousLinearMapWOT.ofCLM U) x⟫_ℂ =
        ⟪y, μ S (U x)⟫_ℂ := rfl
    _ = ⟪μ S y, U x⟫_ℂ := hproj
    _ = μ.complexWeakIntegral f x (μ S y) := (hrec x (μ S y)).symm
    _ = ∫ᵛ z, Set.indicator S f z ∂[ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ);
        μ.scalarMeasure x y] := by
      exact WOTSpectralMeasure.complexWeakIntegral_proj_right μ hS f x y (hfi x y)
    _ = μ.complexWeakIntegral f (μ S x) y := by
      symm
      exact WOTSpectralMeasure.complexWeakIntegral_proj_left μ hS f x y (hfi x y)
    _ = ⟪y, U (μ S x)⟫_ℂ := hrec (μ S x) y
    _ = ⟪y, (ContinuousLinearMapWOT.ofCLM U * μ S) x⟫_ℂ := rfl

lemma WOTSpectralMeasure.complexWeakIntegral_one_sub
    (μ : QuantumMechanics.WOTSpectralMeasure ℂ H) (U : H →L[ℂ] H)
    (hrec : ∀ x y, μ.complexWeakIntegral id x y = ⟪y, U x⟫_ℂ)
    (hfi : ∀ x y, (μ.scalarMeasure x y).Integrable id)
    (hfinite : ∀ x y, IsFiniteMeasure (μ.scalarMeasure x y).variation) (x y : H) :
    μ.complexWeakIntegral (fun z => (1 : ℂ) - z) x y =
      ⟪y, x - U x⟫_ℂ := by
  letI := hfinite x y
  have hconst : (μ.scalarMeasure x y).Integrable (fun _ : ℂ => (1 : ℂ)) := by
    change Integrable (fun _ : ℂ => (1 : ℂ)) (μ.scalarMeasure x y).variation
    exact MeasureTheory.integrable_const (μ := (μ.scalarMeasure x y).variation) (c := (1 : ℂ))
  have hsub : (μ.scalarMeasure x y).Integrable (fun z => (1 : ℂ) - z) := by
    exact hconst.sub (hfi x y)
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  have hfun : (fun z : ℂ => (1 : ℂ) - z) = (fun _ : ℂ => (1 : ℂ)) - id := by
    funext z
    simp
  rw [hfun]
  rw [VectorMeasure.integral_sub (μ := μ.scalarMeasure x y)
    (B := ContinuousLinearMap.lsmul ℝ ℂ) hconst (hfi x y)]
  rw [VectorMeasure.integral_const]
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
  simp only [μ.univ, ContinuousLinearMap.lsmul_apply, one_smul]
  have hid : (∫ᵛ z, id z ∂[ContinuousLinearMap.lsmul ℝ ℂ;
      μ.scalarMeasure x y]) = ⟪y, U x⟫_ℂ := by
    change μ.complexWeakIntegral id x y = _
    exact hrec x y
  rw [hid]
  change ⟪y, x⟫_ℂ - ⟪y, U x⟫_ℂ = _
  rw [inner_sub_right]

lemma WOTSpectralMeasure.scalarMeasure_domain_factorization
    (μ : QuantumMechanics.WOTSpectralMeasure ℂ H) (U : H →L[ℂ] H)
    (hrec : ∀ x y, μ.complexWeakIntegral id x y = ⟪y, U x⟫_ℂ)
    (hfi : ∀ x y, (μ.scalarMeasure x y).Integrable id)
    (hfinite : ∀ x y, IsFiniteMeasure (μ.scalarMeasure x y).variation)
    (hcomm : ∀ {S : Set ℂ}, MeasurableSet S →
      μ S * ContinuousLinearMapWOT.ofCLM U =
        ContinuousLinearMapWOT.ofCLM U * μ S)
    (x v y : H) (hx : x = v - U v) {S : Set ℂ} (hS : MeasurableSet S) :
    μ.scalarMeasure x y S =
      μ.complexWeakIntegral (fun z => (1 : ℂ) - z) (μ S v) y := by
  rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply, hx, map_sub]
  have hcommv := congrArg (fun A : H →WOT[ℂ] H => A v) (hcomm hS)
  change μ S (U v) = U (μ S v) at hcommv
  rw [hcommv]
  exact (WOTSpectralMeasure.complexWeakIntegral_one_sub μ U hrec hfi hfinite
    (μ S v) y).symm

/-! ### Complex vector-measure density transport

The scalar measures of a complex PVM are complex vector measures, rather than positive
measures.  This is the reusable density-integral theorem needed by the inverse Cayley step.
-/

set_option maxHeartbeats 3000000 in
lemma VectorMeasure.integral_real_withDensity_mul
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.VectorMeasure α ℂ)
    {q : α → ℂ} (hq : μ.Integrable q) {g : α → ℝ}
    (hg : (μ.withDensity q (ContinuousLinearMap.mul ℝ ℂ)).Integrable g)
    (hvar0 : (μ.withDensity q (ContinuousLinearMap.mul ℝ ℂ)).variation =
      μ.variation.withDensity (fun x => ‖q x‖ₑ)) :
    ∫ᵛ x, g x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ);
        μ.withDensity q (ContinuousLinearMap.mul ℝ ℂ)] =
      ∫ᵛ x, (g x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := by
  let B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ
  have hmul : B = ContinuousLinearMap.lsmul ℝ ℂ := by
    ext z w
    simp [B, ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hvar :
      (μ.withDensity q B).variation = μ.variation.withDensity (fun x => ‖q x‖ₑ) := by
    simpa [B] using hvar0
  have hq_lt : ∀ᵐ x ∂μ.variation, ‖q x‖ₑ < ⊤ := by
    filter_upwards with x
    exact (lt_top_iff_ne_top).2 enorm_ne_top
  have bridge : ∀ {f : α → ℝ},
      (μ.withDensity q B).Integrable f →
        Integrable (fun x => (f x : ℂ) * q x) μ.variation := by
    intro f hf
    have hfd : Integrable f (μ.variation.withDensity (fun x => ‖q x‖ₑ)) := by
      change Integrable f (μ.withDensity q B).variation at hf
      rw [hvar] at hf
      exact hf
    have hweighted : Integrable
        (fun x => (‖q x‖ₑ).toReal • f x) μ.variation :=
      (integrable_withDensity_iff_integrable_smul₀'
        hq.aestronglyMeasurable.enorm hq_lt).1 hfd
    have hmeas : AEStronglyMeasurable (fun x => (f x : ℂ) * q x) μ.variation := by
      have hqmeas : AEStronglyMeasurable q μ.variation := hq.aestronglyMeasurable
      have hnormmeas : AEStronglyMeasurable (fun x => ‖q x‖) μ.variation :=
        hqmeas.norm
      let u : α → ℂ := fun x => (‖q x‖ : ℝ)⁻¹ • q x
      have hu : AEStronglyMeasurable u μ.variation :=
        hnormmeas.inv₀.smul hqmeas
      have haux' : AEStronglyMeasurable
          (fun x => ((‖q x‖ₑ).toReal • f x : ℂ) * u x) μ.variation := by
        convert (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
          hweighted.aestronglyMeasurable).mul hu using 1 <;>
          funext x <;> simp [Complex.ofRealCLM_apply, smul_eq_mul]
      have haux := haux'
      apply haux.congr
      filter_upwards with x
      by_cases hqx : q x = 0
      · simp [u, hqx]
      · dsimp [u]
        rw [show (‖q x‖ₑ).toReal = ‖q x‖ by simp [enorm_eq_nnnorm]]
        have hn : (‖q x‖ : ℂ) ≠ 0 := by
          exact_mod_cast (norm_ne_zero_iff.mpr hqx)
        calc
          (‖q x‖ : ℂ) * (f x : ℂ) * (((‖q x‖⁻¹ : ℝ) : ℂ) * q x) =
              (‖q x‖ : ℂ) * (f x : ℂ) * ((‖q x‖ : ℂ)⁻¹ * q x) := by
                rw [Complex.ofReal_inv]
          _ =
              (f x : ℂ) * ((‖q x‖ : ℂ) * (‖q x‖ : ℂ)⁻¹) * q x := by ring
          _ = (f x : ℂ) * q x := by
            rw [mul_inv_cancel₀ hn, mul_one]
    apply hweighted.norm.mono' hmeas
    filter_upwards with x
    rw [norm_mul, Complex.norm_real]
    simp [enorm_eq_nnnorm, norm_smul, abs_mul, mul_comm]
  apply hg.induction (P := fun f =>
    ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); μ.withDensity q B] =
      ∫ᵛ x, (f x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ])
  · intro c s hs hfinite
    change (μ.withDensity q B).variation s < ⊤ at hfinite
    have hfinite' : IsFiniteMeasure ((μ.withDensity q B).variation.restrict s) := by
      exact MeasureTheory.isFiniteMeasure_restrict.mpr hfinite.ne
    letI := hfinite'
    rw [VectorMeasure.integral_indicator_const c hs]
    have hfun : (fun x => ((s.indicator (fun _ => c) x : ℝ) : ℂ) * q x) =
        s.indicator (fun x => (c : ℂ) * q x) := by
      funext x
      by_cases hx : x ∈ s <;> simp [hx]
    rw [hfun, MeasureTheory.VectorMeasure.withDensity_apply hq, hmul]
    rw [VectorMeasure.integral_indicator (μ := μ)
      (B := ContinuousLinearMap.lsmul ℝ ℂ) (f := fun x => (c : ℂ) * q x) hs]
    change (c : ℂ) • (∫ᵛ x, q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ.restrict s]) =
      ∫ᵛ x, (c : ℝ) • q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ.restrict s]
    rw [VectorMeasure.integral_fun_smul]
    simp [smul_eq_mul]
  · intro f k _ hf hk hfP hkP
    have hfk := bridge hf
    have hkk := bridge hk
    change (∫ᵛ x, f x + k x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ);
      μ.withDensity q B]) = _
    rw [VectorMeasure.integral_fun_add (μ := μ.withDensity q B) hf hk]
    have hfunadd : (fun x => ((f + k) x : ℂ) * q x) =
        (fun x => ((f x : ℂ) + (k x : ℂ)) * q x) := by
      funext x
      simp [Pi.add_apply]
    rw [hfunadd]
    have hfunadd' :
        (fun x => ((f x : ℂ) + (k x : ℂ)) * q x) =
          (fun x => (f x : ℂ) * q x + (k x : ℂ) * q x) := by
      funext x
      rw [add_mul]
    rw [hfunadd']
    rw [VectorMeasure.integral_fun_add (μ := μ) hfk hkk, hfP, hkP]
  · apply isClosed_eq
    · exact MeasureTheory.VectorMeasure.continuous_integral
    · have hLip : LipschitzWith 1
          (fun y : (Lp ℝ 1 ((μ.withDensity q B).variation)) =>
            ∫ᵛ x, (y x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ]) := by
        rw [lipschitzWith_iff_dist_le_mul]
        intro f k
        have hf := bridge (by
          simpa [B] using (L1.integrable_coeFn f))
        have hk := bridge (by
          simpa [B] using (L1.integrable_coeFn k))
        have hdist := MeasureTheory.VectorMeasure.dist_integral_le_lintegral_edist
          (μ := μ) (B := ContinuousLinearMap.lsmul ℝ ℂ) hf hk
        calc
          dist (∫ᵛ x, (f x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ])
              (∫ᵛ x, (k x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ]) ≤
              ‖ContinuousLinearMap.lsmul ℝ ℂ‖ *
                (∫⁻ x, edist ((f x : ℂ) * q x) ((k x : ℂ) * q x) ∂μ.variation).toReal := hdist
          _ = (1 : ℝ) * dist f k := by
            have hlin :
                (∫⁻ x, edist ((f x : ℂ) * q x) ((k x : ℂ) * q x) ∂μ.variation) =
                  ∫⁻ x, ‖f x - k x‖ₑ ∂(μ.variation.withDensity
                    (fun x => ‖q x‖ₑ)) := by
              rw [lintegral_withDensity_eq_lintegral_mul₀'
                hq.aestronglyMeasurable.enorm]
              · apply lintegral_congr_ae
                filter_upwards with x
                rw [edist_dist, dist_eq_norm, ← sub_mul]
                rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _),
                  ofReal_norm, ofReal_norm]
                have hnorm : ‖(f x : ℂ) - (k x : ℂ)‖ₑ = ‖f x - k x‖ₑ := by
                  rw [← Complex.ofReal_sub]
                  simp only [enorm_eq_nnnorm]
                  apply congrArg ENNReal.ofNNReal
                  apply NNReal.eq
                  simp only [coe_nnnorm, Complex.norm_real]
                rw [hnorm]
                simp [enorm_eq_nnnorm, mul_comm]
              · rw [← hvar]
                exact (Lp.aestronglyMeasurable f).sub
                  (Lp.aestronglyMeasurable k) |>.enorm
            rw [hlin, ← hvar]
            rw [← eLpNorm_one_eq_lintegral_enorm]
            have he : eLpNorm (fun x => f x - k x) 1 (μ.withDensity q B).variation =
                eLpNorm (⇑(f - k)) 1 (μ.withDensity q B).variation :=
              eLpNorm_congr_ae (Lp.coeFn_sub f k).symm
            rw [he, Lp.dist_def]
            rw [eLpNorm_congr_ae (Lp.coeFn_sub f k)]
            simp
      exact hLip.continuous
  · intro f k hfk hf hfP
    have hfk' : f =ᵐ[μ.variation.withDensity (fun x => ‖q x‖ₑ)] k := by
      change f =ᵐ[(μ.withDensity q B).variation] k at hfk
      rw [hvar] at hfk
      exact hfk
    have hfkq : (fun x => (f x : ℂ) * q x) =ᵐ[μ.variation]
        (fun x => (k x : ℂ) * q x) := by
      have hqae := (ae_withDensity_iff' hq.aestronglyMeasurable.enorm).1 hfk'
      filter_upwards [hqae] with x hx
      by_cases hqx : q x = 0
      · simp [hqx]
      · rw [hx (by simp [hqx])]
    calc
      ∫ᵛ x, k x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ);
          μ.withDensity q B] =
          ∫ᵛ x, f x ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ);
            μ.withDensity q B] :=
        (VectorMeasure.integral_congr_ae (μ := μ.withDensity q B) hfk).symm
      _ = ∫ᵛ x, (f x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] := hfP
      _ = ∫ᵛ x, (k x : ℂ) * q x ∂[ContinuousLinearMap.lsmul ℝ ℂ; μ] :=
        VectorMeasure.integral_congr_ae (μ := μ) hfkq

lemma WOTSpectralMeasure.scalarMeasure_eq_withDensity_one_sub
    (μ : QuantumMechanics.WOTSpectralMeasure ℂ H) (U : H →L[ℂ] H)
    (hrec : ∀ x y, μ.complexWeakIntegral id x y = ⟪y, U x⟫_ℂ)
    (hfi : ∀ x y, (μ.scalarMeasure x y).Integrable id)
    (hfinite : ∀ x y, IsFiniteMeasure (μ.scalarMeasure x y).variation)
    (hcomm : ∀ {S : Set ℂ}, MeasurableSet S →
      μ S * ContinuousLinearMapWOT.ofCLM U =
        ContinuousLinearMapWOT.ofCLM U * μ S)
    (x v y : H) (hx : x = v - U v) :
    μ.scalarMeasure x y =
      (μ.scalarMeasure v y).withDensity (fun z => (1 : ℂ) - z)
        (ContinuousLinearMap.mul ℝ ℂ) := by
  let ν := μ.scalarMeasure v y
  letI := hfinite v y
  have hconst : ν.Integrable (fun _ : ℂ => (1 : ℂ)) := by
    change Integrable (fun _ : ℂ => (1 : ℂ)) ν.variation
    exact MeasureTheory.integrable_const (μ := ν.variation) (c := (1 : ℂ))
  have hq : ν.Integrable (fun z => (1 : ℂ) - z) := by
    exact hconst.sub (hfi v y)
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  rw [WOTSpectralMeasure.scalarMeasure_domain_factorization μ U hrec hfi hfinite hcomm
    x v y hx hS]
  rw [MeasureTheory.VectorMeasure.withDensity_apply hq]
  rw [← MeasureTheory.VectorMeasure.integral_indicator hS]
  have hB : ContinuousLinearMap.mul ℝ ℂ = ContinuousLinearMap.lsmul ℝ ℂ := by
    ext z w
    simp [ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [hB]
  exact WOTSpectralMeasure.complexWeakIntegral_proj_left μ hS
    (fun z => (1 : ℂ) - z) v y hq

lemma cayleyBoundedSpectralMeasure_commutes_operator
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T)
    {S : Set ℂ} (hS : MeasurableSet S) :
    cayleyBoundedSpectralMeasure T hT S *
        ContinuousLinearMapWOT.ofCLM (cayleyBoundedOperator T hT) =
      ContinuousLinearMapWOT.ofCLM (cayleyBoundedOperator T hT) *
        cayleyBoundedSpectralMeasure T hT S := by
  apply WOTSpectralMeasure.reconstruction_commutes_projection
    (cayleyBoundedSpectralMeasure T hT)
    (cayleyBoundedOperator T hT) id
  · intro x y
    exact cayleyBoundedSpectralMeasure_reconstruction T hT x y
  · intro x y
    exact cayleyBoundedSpectralMeasure_id_integrable T hT x y
  · exact hS

lemma cayleyBoundedSpectralMeasure_inverse_moment
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    ∀ x : T.domain, ∀ y : H,
      ((cayleyBoundedSpectralMeasure T hT).scalarMeasure (x : H) y).Integrable
          cayleyInverse ∧
        ⟪y, T x⟫_ℂ =
          (cayleyBoundedSpectralMeasure T hT).weakIntegral
            cayleyInverse (x : H) y := by
  intro x y
  let E := cayleyBoundedSpectralMeasure T hT
  let U := cayleyBoundedOperator T hT
  obtain ⟨v, hx, hTx⟩ := cayley_domain_factorization T hT x
  let ν := E.scalarMeasure v y
  let q : ℂ → ℂ := fun z => (1 : ℂ) - z
  have hfinite : IsFiniteMeasure ν.variation := by
    exact cayleyBoundedSpectralMeasure_scalarMeasure_isFinite T hT v y
  letI := hfinite
  have hfi : ν.Integrable id := by
    exact cayleyBoundedSpectralMeasure_id_integrable T hT v y
  have hconst : ν.Integrable (fun _ : ℂ => (1 : ℂ)) := by
    change Integrable (fun _ : ℂ => (1 : ℂ)) ν.variation
    exact MeasureTheory.integrable_const (μ := ν.variation) (c := (1 : ℂ))
  have hq : ν.Integrable q := by
    exact hconst.sub hfi
  have hq_ae : AEMeasurable (fun z => ‖q z‖ₑ) ν.variation :=
    hq.aestronglyMeasurable.enorm
  have hq_lt : ∀ᵐ z ∂ν.variation, ‖q z‖ₑ < ⊤ := by
    filter_upwards with z
    exact (lt_top_iff_ne_top).2 (show ‖q z‖ₑ ≠ ⊤ from enorm_ne_top)
  have hvar : (ν.withDensity q (ContinuousLinearMap.mul ℝ ℂ)).variation =
      ν.variation.withDensity (fun z => ‖q z‖ₑ) := by
    rw [MeasureTheory.VectorMeasure.variation_withDensity hq]
    rw [MeasureTheory.VectorMeasure.variation_transpose_eq _ _]
    · simp [ContinuousLinearMap.mul_apply', nnnorm_mul]
    · intro a b
      simp [ContinuousLinearMap.mul_apply', nnnorm_mul]
  let A : Set ℂ := {z | ‖z‖ = 1 ∧ z ≠ 1}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact (measurableSet_eq_fun measurable_norm measurable_const).inter
      (measurableSet_singleton (1 : ℂ)).compl
  have hνA : ν = ν.restrict A := by
    apply MeasureTheory.VectorMeasure.ext
    intro S hS
    rw [MeasureTheory.VectorMeasure.restrict_apply ν hA hS]
    change ⟪y, E S v⟫_ℂ = ⟪y, E (S ∩ A) v⟫_ℂ
    rw [cayleyBoundedSpectralMeasure_support_away_one T hT S hS]
  have hA_ae : ∀ᵐ z ∂ν.variation, z ∈ A := by
    rw [hνA, MeasureTheory.VectorMeasure.variation_restrict hA]
    exact ae_restrict_mem hA
  have hprod : Integrable (fun z => (cayleyInverse z : ℂ) * q z) ν.variation := by
    have hmeas : AEStronglyMeasurable
        (fun z => (cayleyInverse z : ℂ) * q z) ν.variation := by
      have hqmeas : AEStronglyMeasurable q ν.variation := hq.aestronglyMeasurable
      exact (Complex.ofRealCLM.continuous.comp_aestronglyMeasurable
        measurable_cayleyInverse.aestronglyMeasurable).mul hqmeas
    apply Integrable.of_bound hmeas 2
    filter_upwards [hA_ae] with z hz
    have hzid := cayleyInverse_mul_one_sub_of_unit_circle hz.1 hz.2
    calc
      ‖(cayleyInverse z : ℂ) * q z‖ = ‖Complex.I * (1 + z)‖ := by
        rw [show q z = 1 - z by rfl, hzid]
      _ = ‖1 + z‖ := by rw [norm_mul]; simp
      _ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
      _ = 2 := by rw [hz.1]; norm_num
  have hweighted : (ν.withDensity q (ContinuousLinearMap.mul ℝ ℂ)).Integrable
      cayleyInverse := by
    change Integrable cayleyInverse
      (ν.withDensity q (ContinuousLinearMap.mul ℝ ℂ)).variation
    rw [hvar]
    apply (integrable_withDensity_iff_integrable_smul₀' hq_ae hq_lt).2
    have habs : Integrable
        (fun z => ‖(cayleyInverse z : ℂ) * q z‖) ν.variation := hprod.norm
    have habs' : Integrable
        (fun z => ‖q z‖ * |cayleyInverse z|) ν.variation := by
      apply habs.congr
      filter_upwards with z
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
    have hsign : Integrable
        (fun z => ‖q z‖ * cayleyInverse z) ν.variation := by
      apply habs'.congr'
        ((hq.aestronglyMeasurable.norm.mul
          measurable_cayleyInverse.aestronglyMeasurable))
      filter_upwards with z
      simp [abs_mul]
    apply hsign.congr
    filter_upwards with z
    simp [toReal_enorm, smul_eq_mul]
  have hmeasure : E.scalarMeasure (x : H) y =
      ν.withDensity q (ContinuousLinearMap.mul ℝ ℂ) := by
    exact WOTSpectralMeasure.scalarMeasure_eq_withDensity_one_sub E U
      (fun a b => cayleyBoundedSpectralMeasure_reconstruction T hT a b)
      (fun a b => cayleyBoundedSpectralMeasure_id_integrable T hT a b)
      (fun a b => cayleyBoundedSpectralMeasure_scalarMeasure_isFinite T hT a b)
      (fun {S} hS => cayleyBoundedSpectralMeasure_commutes_operator T hT hS)
      (x : H) v y hx
  constructor
  · rw [hmeasure]
    exact hweighted
  · have hden := VectorMeasure.integral_real_withDensity_mul ν hq hweighted hvar
    have hbase : ∫ᵛ z, (cayleyInverse z : ℂ) * q z ∂[
        ContinuousLinearMap.lsmul ℝ ℂ; ν] =
        Complex.I * (∫ᵛ z, (1 + z) ∂[
          ContinuousLinearMap.lsmul ℝ ℂ; ν]) := by
      have hplus : ν.Integrable (fun z => (1 : ℂ) + z) := hconst.add hfi
      have hpoint : (fun z => (cayleyInverse z : ℂ) * q z) =ᵐ[ν.variation]
          (fun z => Complex.I * ((1 : ℂ) + z)) := by
        rw [hνA, MeasureTheory.VectorMeasure.variation_restrict hA]
        filter_upwards [ae_restrict_mem hA] with z hz
        exact cayleyInverse_mul_one_sub_of_unit_circle hz.1 hz.2
      rw [VectorMeasure.integral_congr_ae hpoint]
      have hcomp :
          ContinuousLinearMap.lsmul ℝ ℂ ∘L ContinuousLinearMap.lsmul ℝ ℂ Complex.I =
            (ContinuousLinearMap.compL ℝ ℂ ℂ ℂ
              (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) ∘L
              ContinuousLinearMap.lsmul ℝ ℂ := by
        ext c w
        simp [ContinuousLinearMap.compL_apply, ContinuousLinearMap.lsmul_apply,
          smul_eq_mul]
        ring
      calc
        ∫ᵛ x, Complex.I * (1 + x) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ; ν] =
            ∫ᵛ x, (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) (1 + x) ∂[
              ContinuousLinearMap.lsmul ℝ ℂ; ν] := by rfl
        _ = ∫ᵛ x, (1 + x) ∂[
            (ContinuousLinearMap.lsmul ℝ ℂ) ∘L
              (ContinuousLinearMap.lsmul ℝ ℂ Complex.I); ν] :=
          VectorMeasure.integral_continuousLinearMap_comp hplus
        _ = ∫ᵛ x, (1 + x) ∂[
            (ContinuousLinearMap.compL ℝ ℂ ℂ ℂ
              (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) ∘L
              ContinuousLinearMap.lsmul ℝ ℂ; ν] := by rw [hcomp]
        _ = Complex.I * (∫ᵛ x, (1 + x) ∂[
            ContinuousLinearMap.lsmul ℝ ℂ; ν]) :=
          (VectorMeasure.continuousLinearMap_apply_integral
            (C := ContinuousLinearMap.lsmul ℝ ℂ Complex.I) hplus).symm
    unfold QuantumMechanics.WOTSpectralMeasure.weakIntegral
    rw [hmeasure, hden, hbase]
    have hplus : ∫ᵛ z, (1 + z) ∂[
        ContinuousLinearMap.lsmul ℝ ℂ; ν] = ⟪y, v + U v⟫_ℂ := by
      have hplus' : ν.Integrable (fun z => (1 : ℂ) + z) := hconst.add hfi
      have hfun : (fun z : ℂ => (1 : ℂ) + z) =
          (fun _ : ℂ => (1 : ℂ)) + id := by
        funext z
        simp
      rw [hfun]
      change (∫ᵛ z, (1 : ℂ) + id z ∂[
        ContinuousLinearMap.lsmul ℝ ℂ; ν]) = _
      rw [VectorMeasure.integral_fun_add hconst hfi]
      rw [VectorMeasure.integral_const]
      rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_apply]
      rw [QuantumMechanics.WOTSpectralMeasure.univ]
      simp only [ContinuousLinearMap.lsmul_apply, one_smul]
      have hid : (∫ᵛ z, id z ∂[ContinuousLinearMap.lsmul ℝ ℂ; ν]) =
          ⟪y, U v⟫_ℂ := by
        change E.complexWeakIntegral id v y = _
        exact cayleyBoundedSpectralMeasure_reconstruction T hT v y
      rw [hid]
      change ⟪y, v⟫_ℂ + ⟪y, U v⟫_ℂ = _
      rw [inner_add_right]
    rw [hplus, hTx, inner_smul_right]

/-! ### The inverse-moment transport lemma

The bounded spectral reconstruction supplies the Cayley moment `z`.  The genuinely unbounded
step is the inverse-Cayley moment on the operator domain.  The following theorem isolates the
measure-transport part of that step: once the inverse moment is established on the bounded
Cayley measure, it is transported automatically to the real spectral measure.  This keeps the
analytic domain argument separate from the bookkeeping for mapped vector measures.
-/

lemma cayleyRealSpectralMeasure_isWeakSpectralResolution_of_inverse_moment
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T)
    (hinv : ∀ x : T.domain, ∀ y : H,
      ((cayleyBoundedSpectralMeasure T hT).scalarMeasure (x : H) y).Integrable cayleyInverse ∧
        ⟪y, T x⟫_ℂ =
          (cayleyBoundedSpectralMeasure T hT).weakIntegral cayleyInverse (x : H) y) :
    IsWeakSpectralResolution T (cayleyRealSpectralMeasure T hT) := by
  intro x
  refine ⟨?_, ?_⟩
  · intro y
    have hmap := hinv x y |>.1
    change ((cayleyBoundedSpectralMeasure T hT).map cayleyInverse
      measurable_cayleyInverse).scalarMeasure (x : H) y |>.Integrable id
    rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_map]
    exact VectorMeasure.Integrable.map measurable_id.aestronglyMeasurable hmap
  · intro y
    have hmap := hinv x y |>.1
    have htransport :
        (cayleyRealSpectralMeasure T hT).weakIntegral id (x : H) y =
          (cayleyBoundedSpectralMeasure T hT).weakIntegral
            (id ∘ cayleyInverse) (x : H) y := by
      change ((cayleyBoundedSpectralMeasure T hT).map cayleyInverse
        measurable_cayleyInverse).weakIntegral id (x : H) y = _
      exact QuantumMechanics.WOTSpectralMeasure.weakIntegral_map
        (μS := cayleyBoundedSpectralMeasure T hT) cayleyInverse
        measurable_cayleyInverse id (x : H) y
        measurable_id.aestronglyMeasurable hmap
    rw [htransport]
    simpa [Function.comp_def] using (hinv x y).2

lemma cayleyRealSpectralMeasure_isWeakSpectralResolution
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    IsWeakSpectralResolution T (cayleyRealSpectralMeasure T hT) := by
  apply cayleyRealSpectralMeasure_isWeakSpectralResolution_of_inverse_moment T hT
  exact cayleyBoundedSpectralMeasure_inverse_moment T hT

theorem cayleySelfAdjointSpectralTheorem
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    SelfAdjointSpectralTheorem T (cayleyRealSpectralMeasure T hT) where
  isSelfAdjoint := hT
  reconstruction := cayleyRealSpectralMeasure_isWeakSpectralResolution T hT

lemma cayleyRealSpectralMeasure_le_maximal
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    T ≤ QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
      (cayleyRealSpectralMeasure T hT) := by
  let E := cayleyRealSpectralMeasure T hT
  let M := QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral E
  have hres := cayleyRealSpectralMeasure_isWeakSpectralResolution T hT
  refine ⟨?_, ?_⟩
  · intro x hx
    change x ∈ spectralSquareMomentDomain E
    exact cayleyRealSpectralMeasure_mem_domain T hT (⟨x, hx⟩ : T.domain)
  · intro x z hxz
    have hxM : (x : H) ∈ M.domain := by
      change (x : H) ∈ spectralSquareMomentDomain E
      exact cayleyRealSpectralMeasure_mem_domain T hT x
    let z₀ : M.domain := ⟨(x : H), hxM⟩
    have hz : z = z₀ := by
      apply Subtype.ext
      exact hxz.symm
    apply ext_inner_left ℂ
    intro y
    have hfi : (E.scalarMeasure (x : H) y).Integrable id := (hres x).1 y
    have hweak :=
      QuantumMechanics.WOTSpectralMeasure.truncationIntegral_inner_tendsto_weakIntegral
        E (x : H) y hfi
    have hcomplex : Filter.Tendsto
        (fun n : ℕ => ∫ᵛ r, QuantumMechanics.WOTSpectralMeasure.truncationFunction n r ∂[
          ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); E.scalarMeasure (x : H) y])
        Filter.atTop (𝓝 (E.weakIntegral id (x : H) y)) := by
      apply hweak.congr'
      filter_upwards [] with n
      have htrunc : (E.scalarMeasure (x : H) y).Integrable
          (QuantumMechanics.WOTSpectralMeasure.realTruncationFunction n) := by
        rcases QuantumMechanics.WOTSpectralMeasure.realTruncationFunction_bounded n with ⟨C, hC⟩
        letI := QuantumMechanics.WOTSpectralMeasure.scalarMeasure_isFiniteVariation E (x : H) y
        apply Integrable.of_bound
          (QuantumMechanics.WOTSpectralMeasure.realTruncationFunction_measurable
              n).aestronglyMeasurable C
        filter_upwards [] with r
        simpa [Real.norm_eq_abs] using hC r
      have hreal := QuantumMechanics.WOTSpectralMeasure.integral_real_eq_complex
        (E.scalarMeasure (x : H) y) htrunc
      have hfun : (fun r => QuantumMechanics.WOTSpectralMeasure.truncationFunction n r) =
          (fun r => Complex.ofRealCLM
            (QuantumMechanics.WOTSpectralMeasure.realTruncationFunction n r)) := by
        funext r
        simpa [Complex.ofRealCLM_apply] using congrFun
          (QuantumMechanics.WOTSpectralMeasure.realTruncationFunction_complex_eq n).symm r
      calc
        ∫ᵛ r, QuantumMechanics.WOTSpectralMeasure.realTruncationFunction n r ∂[
            ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ); E.scalarMeasure (x : H) y] =
            ∫ᵛ r, Complex.ofRealCLM
              (QuantumMechanics.WOTSpectralMeasure.realTruncationFunction n r) ∂[
                ContinuousLinearMap.lsmul ℝ ℂ; E.scalarMeasure (x : H) y] :=
          hreal
        _ = ∫ᵛ r, QuantumMechanics.WOTSpectralMeasure.truncationFunction n r ∂[
            ContinuousLinearMap.lsmul ℝ ℂ (E := ℂ); E.scalarMeasure (x : H) y] :=
          congrArg (fun f : ℝ → ℂ => ∫ᵛ r, f r ∂[
            ContinuousLinearMap.lsmul ℝ ℂ; E.scalarMeasure (x : H) y]) hfun.symm
    have hmax :=
      QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_weak_truncation_reconstruction
        E (x : H) hxM y
    have hinner : ⟪y, M z₀⟫_ℂ = E.weakIntegral id (x : H) y :=
      tendsto_nhds_unique hmax hcomplex
    calc
      ⟪y, T x⟫_ℂ = E.weakIntegral id (x : H) y := (hres x).2 y
      _ = ⟪y, M z₀⟫_ℂ := hinner.symm
      _ = ⟪y, M z⟫_ℂ := by rw [hz]

theorem cayleyRealSpectralMeasure_eq_maximal
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    maximalSpectralIntegral
        (cayleyRealSpectralMeasure T hT) = T := by
  exact maximalSpectralIntegral_eq_of_isSelfAdjoint_of_isWeakSpectralResolution
      T hT
      (cayleyRealSpectralMeasure_isWeakSpectralResolution T hT)
      (fun x => cayleyRealSpectralMeasure_mem_domain T hT x)

theorem cayleyDomainAwareSelfAdjointSpectralTheorem
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    DomainAwareSelfAdjointSpectralTheorem T (cayleyRealSpectralMeasure T hT) := by
  exact domainAwareSelfAdjointSpectralTheorem_of_isWeakSpectralResolution
      T hT
      (cayleyRealSpectralMeasure_isWeakSpectralResolution T hT)
      (fun x => cayleyRealSpectralMeasure_mem_domain T hT x)

/-- The public unbounded spectral theorem for a self-adjoint `LinearPMap`.

The Cayley transform is an implementation detail of the construction: the result exposes the
real spectral measure and the exact square-moment domain through the standard
`DomainAwareSelfAdjointSpectralTheorem` interface.  Clients that already have a self-adjoint
operator should use this facade rather than depending on the Cayley-side names. -/
theorem unboundedSpectralTheorem
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    DomainAwareSelfAdjointSpectralTheorem T (cayleyRealSpectralMeasure T hT) := by
  exact cayleyDomainAwareSelfAdjointSpectralTheorem T hT

/-- The public Cayley-based theorem starting from an essentially self-adjoint core.

The operator supplied to the spectral API is the canonical graph closure.  Thus the implication
`essential self-adjointness → self-adjoint closure → exact unbounded spectral theorem` is visible
in one declaration, while the returned certificate still exposes the closure domain and the
square-moment domain equality separately. -/
theorem unboundedSpectralTheorem_of_essentiallySelfAdjoint
    (T : H →ₗ.[ℂ] H) (hT : LinearPMap.IsEssentiallySelfAdjoint T) :
    DomainAwareSelfAdjointSpectralTheorem T.closure
      (cayleyRealSpectralMeasure T.closure hT) := by
  exact cayleyDomainAwareSelfAdjointSpectralTheorem T.closure hT

/-- The essential-self-adjointness spectral data built from the Cayley construction, given only
an essential-self-adjointness witness for `T`. -/
noncomputable def cayleyEssentiallySelfAdjointSpectralData
    (T : H →ₗ.[ℂ] H) (hT : LinearPMap.IsEssentiallySelfAdjoint T) :
    EssentialSelfAdjointSpectralData T where
  essentiallySelfAdjoint := hT
  spectralMeasure := cayleyRealSpectralMeasure T.closure hT
  spectralTheorem := cayleyDomainAwareSelfAdjointSpectralTheorem T.closure hT

end OperatorAlgebra

end
