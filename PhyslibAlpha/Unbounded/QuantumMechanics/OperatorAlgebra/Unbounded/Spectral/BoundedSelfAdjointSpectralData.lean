/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Spectral.CayleySpectralData

/-!
# The bounded self-adjoint spectral measure

The bounded normal construction naturally produces a measure on the complex spectrum.  For a
self-adjoint operator that spectrum is real, so pushing the measure forward along `Complex.re`
gives the real spectral measure consumed by the unbounded integral API.  This file records that
adapter independently of the Cayley transform.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real spectral measure of a bounded self-adjoint operator, obtained from the genuine
bounded-normal spectral measure by the real-part map on the complex spectrum. -/
noncomputable def boundedSelfAdjointSpectralMeasure
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    QuantumMechanics.WOTSpectralMeasure ℝ H :=
  (cfcSpectralMeasure A hA.isStarNormal).map
    (fun z : spectrum ℂ A => z.1.re) (by fun_prop)

set_option maxHeartbeats 2000000 in
lemma boundedSelfAdjointSpectralMeasure_reconstruction
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (x y : H) :
    (boundedSelfAdjointSpectralMeasure A hA).complexWeakIntegral
        (fun r : ℝ => (r : ℂ)) x y = ⟪y, A x⟫_ℂ := by
  let E := cfcSpectralMeasure A hA.isStarNormal
  let f : spectrum ℂ A → ℝ := fun z => z.1.re
  have hf : Measurable f := by fun_prop
  have hfinite : IsFiniteMeasure (E.scalarMeasure x y).variation := by
    rw [cfcSpectralMeasure_scalarMeasure]
    exact polarizedCfcScalarMeasure_isFiniteMeasure A hA.isStarNormal x y
  letI := hfinite
  have hgi : (E.scalarMeasure x y).Integrable (fun z => ((f z : ℝ) : ℂ)) := by
    have hcont : Continuous (fun z : spectrum ℂ A => ((f z : ℝ) : ℂ)) := by
      fun_prop
    have hbdd : BddAbove ((fun z : ℂ => ‖z‖) '' (spectrum ℂ A)) :=
      (spectrum.isCompact A).bddAbove_image continuous_norm.continuousOn
    rcases hbdd with ⟨C, hC⟩
    apply MeasureTheory.Integrable.of_bound hcont.aestronglyMeasurable C
    filter_upwards [] with z
    calc
      ‖((f z : ℝ) : ℂ)‖ = |f z| := by simp
      _ = |z.1.re| := rfl
      _ ≤ ‖z.1‖ := Complex.abs_re_le_norm _
      _ ≤ C := hC ⟨z.1, z.property, rfl⟩
  have hmap := QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral_map
    (μS := E) f hf (fun r : ℝ => (r : ℂ)) x y
    Complex.continuous_ofReal.aestronglyMeasurable hgi
  change (E.map f hf).complexWeakIntegral (fun r : ℝ => (r : ℂ)) x y = _
  rw [hmap]
  have hreal : ((fun r : ℝ => (r : ℂ)) ∘ f) = (fun z : spectrum ℂ A => z.1) := by
    funext z
    exact (hA.mem_spectrum_eq_re z.property).symm
  rw [hreal]
  unfold QuantumMechanics.WOTSpectralMeasure.complexWeakIntegral
  rw [cfcSpectralMeasure_scalarMeasure]
  exact polarizedCfcScalarMeasure_integral_spectrum_coe A hA.isStarNormal x y

lemma exists_boundedSelfAdjointSpectralSupport
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    ∃ C : ℝ, HasBoundedSpectralSupport
      (boundedSelfAdjointSpectralMeasure A hA) C := by
  let E := cfcSpectralMeasure A hA.isStarNormal
  let f : spectrum ℂ A → ℝ := fun z => z.1.re
  have hbdd : BddAbove ((fun z : ℂ => ‖z‖) '' (spectrum ℂ A)) :=
    (spectrum.isCompact A).bddAbove_image continuous_norm.continuousOn
  rcases hbdd with ⟨B, hB⟩
  let C : ℝ := max 0 B
  refine ⟨C, le_max_left _ _, ?_⟩
  intro S hS hdisj
  have hpre : f ⁻¹' S = ∅ := by
    ext z
    constructor
    · intro hz
      have habs : |f z| ≤ C := by
        calc
          |f z| ≤ ‖z.1‖ := Complex.abs_re_le_norm _
          _ ≤ B := hB ⟨z.1, z.property, rfl⟩
          _ ≤ C := le_max_right _ _
      have hzIcc : f z ∈ Set.Icc (-C) C :=
        (abs_le.mp habs)
      exact (Set.disjoint_left.1 hdisj hz) hzIcc
    · simp
  change (E.map f (by fun_prop)) S = 0
  rw [E.map_apply f (by fun_prop) hS, hpre]
  simp

lemma continuousLinearMapToPMap_isSelfAdjoint
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (continuousLinearMapToPMap A) := by
  rw [LinearPMap.isSelfAdjoint_def]
  have h := A.toPMap_adjoint_eq_adjoint_toPMap_of_dense
    (p := (⊤ : Submodule ℂ H)) (by simpa using (dense_univ : Dense (Set.univ : Set H)))
  have hadj : A.adjoint = A := by
    rw [← A.star_eq_adjoint]
    exact hA.star_eq
  change (A.toPMap (⊤ : Submodule ℂ H)).adjoint = _
  rw [h, hadj]
  rfl

noncomputable def boundedSelfAdjointSpectralData
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    SelfAdjointSpectralData (continuousLinearMapToPMap A) where
  isSelfAdjoint := continuousLinearMapToPMap_isSelfAdjoint A hA
  spectralMeasure := boundedSelfAdjointSpectralMeasure A hA
  spectralTheorem := {
    isSelfAdjoint := continuousLinearMapToPMap_isSelfAdjoint A hA
    reconstruction := by
      intro x
      constructor
      · intro y
        let E := cfcSpectralMeasure A hA.isStarNormal
        let f : spectrum ℂ A → ℝ := fun z => z.1.re
        have hfinite : IsFiniteMeasure (E.scalarMeasure (x : H) y).variation := by
          rw [cfcSpectralMeasure_scalarMeasure]
          exact polarizedCfcScalarMeasure_isFiniteMeasure A hA.isStarNormal (x : H) y
        letI := hfinite
        have hgi : (E.scalarMeasure (x : H) y).Integrable f := by
          have hbdd : BddAbove ((fun z : ℂ => ‖z‖) '' (spectrum ℂ A)) :=
            (spectrum.isCompact A).bddAbove_image continuous_norm.continuousOn
          rcases hbdd with ⟨C, hC⟩
          apply MeasureTheory.Integrable.of_bound (by fun_prop) C
          filter_upwards [] with z
          calc
            ‖f z‖ = |z.1.re| := rfl
            _ ≤ ‖z.1‖ := Complex.abs_re_le_norm _
            _ ≤ C := hC ⟨z.1, z.property, rfl⟩
        change (E.map f (by fun_prop)).scalarMeasure (x : H) y |>.Integrable id
        rw [QuantumMechanics.WOTSpectralMeasure.scalarMeasure_map]
        exact MeasureTheory.VectorMeasure.Integrable.map
          measurable_id.aestronglyMeasurable hgi
      · intro y
        let E := cfcSpectralMeasure A hA.isStarNormal
        let f : spectrum ℂ A → ℝ := fun z => z.1.re
        have hfinite : IsFiniteMeasure (E.scalarMeasure (x : H) y).variation := by
          rw [cfcSpectralMeasure_scalarMeasure]
          exact polarizedCfcScalarMeasure_isFiniteMeasure A hA.isStarNormal (x : H) y
        letI := hfinite
        have hgi : (E.scalarMeasure (x : H) y).Integrable f := by
          have hbdd : BddAbove ((fun z : ℂ => ‖z‖) '' (spectrum ℂ A)) :=
            (spectrum.isCompact A).bddAbove_image continuous_norm.continuousOn
          rcases hbdd with ⟨C, hC⟩
          apply MeasureTheory.Integrable.of_bound (by fun_prop) C
          filter_upwards [] with z
          calc
            ‖f z‖ = |z.1.re| := rfl
            _ ≤ ‖z.1‖ := Complex.abs_re_le_norm _
            _ ≤ C := hC ⟨z.1, z.property, rfl⟩
        have hmap := QuantumMechanics.WOTSpectralMeasure.weakIntegral_map
          (μS := E) f (by fun_prop) (fun r : ℝ => r) (x : H) y
          measurable_id.aestronglyMeasurable hgi
        change ⟪y, A (x : H)⟫_ℂ =
          (E.map f (by fun_prop)).weakIntegral (fun r : ℝ => r) (x : H) y
        rw [hmap]
        have hreal := QuantumMechanics.WOTSpectralMeasure.integral_real_eq_complex
          (E.scalarMeasure (x : H) y) hgi
        change ⟪y, A (x : H)⟫_ℂ =
          ∫ᵛ z, f z ∂[ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ);
            E.scalarMeasure (x : H) y]
        rw [hreal]
        have hfunc : (fun z : spectrum ℂ A => ((f z : ℝ) : ℂ)) =
            (fun z : spectrum ℂ A => z.1) := by
          funext z
          exact (hA.mem_spectrum_eq_re z.property).symm
        have hsource : E.complexWeakIntegral
            (fun z : spectrum ℂ A => ((f z : ℝ) : ℂ)) (x : H) y =
            ⟪y, A (x : H)⟫_ℂ := by
          rw [hfunc]
          exact cfcSpectralMeasure_reconstruction_coe A hA.isStarNormal (x : H) y
        exact hsource.symm }

noncomputable def boundedSelfAdjointDomainAwareSpectralTheorem
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    DomainAwareSelfAdjointSpectralTheorem (continuousLinearMapToPMap A)
      (boundedSelfAdjointSpectralMeasure A hA) := by
  let D := boundedSelfAdjointSpectralData A hA
  rcases exists_boundedSelfAdjointSpectralSupport A hA with ⟨C, hC⟩
  exact DomainAwareSelfAdjointSpectralTheorem.ofBoundedSupport
    D.spectralTheorem rfl hC

end OperatorAlgebra
