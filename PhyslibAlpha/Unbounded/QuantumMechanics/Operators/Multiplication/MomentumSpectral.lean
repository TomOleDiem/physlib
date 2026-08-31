/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Operators.Momentum
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.Multiplication.Spectral
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Fourier representation of Schwartz momentum

The maximal Fourier-side multiplication operator and its spectral theorem live in
`MultiplicationSpectral`.  This file supplies the reusable analytic identity relating that
realization to the differential momentum expression on Schwartz space, the exact identification
of the transported Schwartz restriction, and the resulting closure and essential
self-adjointness theorems.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory
open scoped ComplexOrder FourierTransform

namespace QuantumMechanics

open Constants Complex Space SchwartzMap SpaceDHilbertSpace
open SchwartzSubmodule

variable {d : ℕ}

/-- The complex-valued multiplier corresponding to the real physical momentum coordinate. -/
def momentumCoordinateComplex (i : Fin d) : Space d → ℂ :=
  fun p => (momentumCoordinate i p : ℂ)

lemma momentumCoordinateComplex_hasTemperateGrowth (i : Fin d) :
    HasTemperateGrowth (momentumCoordinateComplex i) := by
  apply Function.Complex.hasTemperateGrowth_ofReal.comp
  unfold momentumCoordinate
  apply (Function.HasTemperateGrowth.const _).mul
  have heq : Space.coord i = ⇑(Space.coordCLM i) := by
    funext x
    exact (Space.coordCLM_apply i x).symm
  rw [heq]
  exact (Space.coordCLM i).hasTemperateGrowth

/-!
### The Fourier multiplier identity
-/

/-- Fourier transformation turns the Schwartz differential momentum `-iℏ ∂ᵢ` into multiplication
by the physical momentum coordinate `2πℏ xᵢ`. -/
lemma fourier_momentumCLM_eq (i : Fin d) (f : 𝓢(Space d, ℂ)) :
    𝓕 (𝐩 i f) =
      (2 * Real.pi * (ℏ : ℂ)) •
        SchwartzMap.smulLeftCLM ℂ (fun x : Space d => (x i : ℂ)) (𝓕 f) := by
  rw [show 𝐩 i f = (-Complex.I * ℏ) •
      LineDeriv.lineDerivOpCLM ℂ (𝓢(Space d, ℂ)) (Space.basis i) f by
    rfl]
  rw [FourierSMul.fourier_smul]
  change (-Complex.I * ℏ) •
    (FourierTransform.fourier (LineDeriv.lineDerivOp (Space.basis i) f)) = _
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_smul]
  have hcoord :
      (fun x : Space d => inner ℝ x (Space.basis i)) =
        (fun x : Space d => x i) := by
    funext x
    exact Space.coord_apply i x
  rw [hcoord]
  have htemp : (fun x : Space d => x i).HasTemperateGrowth := by
    have heq : (fun x : Space d => x i) = ⇑(Space.coordCLM i) := by
      funext x
      calc
        x i = Space.coord i x := (Space.coord_apply i x).symm
        _ = Space.coordCLM i x := rfl
    rw [heq]
    exact (Space.coordCLM i).hasTemperateGrowth
  rw [← SchwartzMap.smulLeftCLM_ofReal ℂ htemp (𝓕 f)]
  congr 1
  ring_nf
  simp [Complex.I_sq]

lemma fourier_momentumCLM_eq_smulLeft (i : Fin d) (f : 𝓢(Space d, ℂ)) :
    SchwartzMap.smulLeftCLM ℂ (momentumCoordinateComplex i) (𝓕 f) = 𝓕 (𝐩 i f) := by
  rw [fourier_momentumCLM_eq i f]
  apply SchwartzMap.ext
  intro x
  have hcoord : (fun x : Space d => (x i : ℂ)).HasTemperateGrowth := by
    apply Function.Complex.hasTemperateGrowth_ofReal.comp
    have heq : (fun x : Space d => x.val i) = Space.coord i := by
      funext y
      exact (Space.coord_apply i y).symm
    rw [heq]
    have heq' : Space.coord i = ⇑(Space.coordCLM i) := by
      funext y
      exact (Space.coordCLM_apply i y).symm
    rw [heq']
    exact (Space.coordCLM i).hasTemperateGrowth
  have hleft := congr_fun
    (SchwartzMap.smulLeftCLM_apply (momentumCoordinateComplex_hasTemperateGrowth i) (𝓕 f)) x
  have hright := congr_fun
    (SchwartzMap.smulLeftCLM_apply hcoord (𝓕 f)) x
  rw [hleft]
  change _ = (2 * Real.pi * (ℏ : ℂ)) * _
  rw [hright]
  simp only [momentumCoordinateComplex, momentumCoordinate, Complex.ofReal_mul,
    Complex.ofReal_ofNat, smul_eq_mul]
  rw [Space.coord_apply]
  ring

/-!
### The Schwartz operator as a restriction
-/

/-- The Schwartz momentum operator transported to the Fourier representation. -/
def fourierSchwartzMomentumOperator (i : Fin d) :
    SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d :=
  LinearPMap.unitaryConj (SpaceDHilbertSpace.fourierUnitary d).symm
    (schwartzMulOperator
      (f := momentumCoordinateComplex i)
      (momentumCoordinateComplex_hasTemperateGrowth i))

lemma fourierSchwartzMomentumOperator_apply (i : Fin d)
    (f : 𝓢(Space d, ℂ))
    (hM : SpaceDHilbertSpace.fourierUnitary d (schwartzEquiv volume f) ∈
      (realMultiplicationOperator (μ := volume) (momentumCoordinate i)).domain) :
    fourierSchwartzMomentumOperator i
        ⟨schwartzEquiv volume f, by
          change (SpaceDHilbertSpace.fourierUnitary d).symm.symm
              (schwartzEquiv volume f) ∈
            (schwartzMulOperator
              (f := momentumCoordinateComplex i)
              (momentumCoordinateComplex_hasTemperateGrowth i)).domain
          change SpaceDHilbertSpace.fourierUnitary d (schwartzIncl volume f) ∈
            SchwartzSubmodule d
          have hU : SpaceDHilbertSpace.fourierUnitary d (schwartzIncl volume f) =
              schwartzIncl volume (𝓕 f) := by
            simpa using schwartzIncl_fourier_eq f
          rw [hU]
          exact ⟨𝓕 f, rfl⟩⟩ =
      momentumOperator i (schwartzEquiv volume f) := by
  let U := SpaceDHilbertSpace.fourierUnitary d
  let qv : SchwartzSubmodule d :=
    ⟨U (schwartzEquiv volume f), by
      rw [show U (schwartzEquiv volume f) = schwartzIncl volume (𝓕 f) by
        rw [schwartzEquiv_apply_coe]
        exact schwartzIncl_fourier_eq f]
      exact ⟨𝓕 f, rfl⟩⟩
  have hqv : qv = ⟨schwartzIncl volume (𝓕 f), ⟨𝓕 f, rfl⟩⟩ := by
    apply Subtype.ext
    change U (schwartzEquiv volume f) = schwartzIncl volume (𝓕 f)
    rw [schwartzEquiv_apply_coe]
    exact schwartzIncl_fourier_eq f
  have htemp := momentumCoordinateComplex_hasTemperateGrowth i
  have hmul :
      schwartzMulOperator (f := momentumCoordinateComplex i) htemp qv =
        schwartzIncl volume
          (SchwartzMap.smulLeftCLM ℂ (momentumCoordinateComplex i) (𝓕 f)) := by
    rw [hqv]
    exact schwartzMulOperator_apply_schwartz htemp (𝓕 f)
  have hmax :
      (realMultiplicationOperator (μ := volume) (momentumCoordinate i))
          ⟨U (schwartzEquiv volume f), hM⟩ =
        schwartzMulOperator (f := momentumCoordinateComplex i) htemp qv := by
    change (𝓜 volume (fun x : Space d => (momentumCoordinate i x : ℂ)))
          ⟨U (schwartzIncl volume f), hM⟩ =
        (𝓜 volume (fun x : Space d => (momentumCoordinate i x : ℂ)))
          (Submodule.inclusion
            (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth htemp volume)
            qv)
    have heq :
        (Submodule.inclusion
          (SpaceDHilbertSpace.mulOperator_domain_ge_of_hasTemperateGrowth htemp volume)
      qv : (𝓜 volume (fun x : Space d => (momentumCoordinate i x : ℂ))).domain) =
          ⟨U (schwartzEquiv volume f), hM⟩ := by
      apply Subtype.ext
      rfl
    rw [heq]
    rfl
  change U.symm
      ((schwartzMulOperator
        (f := momentumCoordinateComplex i)
        (momentumCoordinateComplex_hasTemperateGrowth i))
        ⟨U (schwartzEquiv volume f), _⟩) = _
  change U.symm
      ((realMultiplicationOperator (μ := volume) (momentumCoordinate i))
        ⟨U (schwartzEquiv volume f), hM⟩) = _
  rw [hmax, hmul]
  rw [fourier_momentumCLM_eq_smulLeft]
  rw [← schwartzIncl_fourier_eq]
  have hP : momentumOperator i (schwartzEquiv volume f) =
      schwartzIncl volume (𝐩 i f) := by
    rw [momentumOperator_apply]
    simp only [LinearEquiv.symm_apply_apply]
    exact schwartzEquiv_apply_coe _
  rw [hP]
  change 𝓕⁻ (𝓕 (schwartzIncl volume (𝐩 i f))) =
    schwartzIncl volume (𝐩 i f)
  rw [FourierPair.fourierInv_fourier_eq]

lemma momentumOperator_eq_fourierSchwartzMomentumOperator (i : Fin d) :
    momentumOperator i = fourierSchwartzMomentumOperator i := by
  let U := SpaceDHilbertSpace.fourierUnitary d
  have hdomain : (fourierSchwartzMomentumOperator i).domain =
      SchwartzSubmodule d := by
    ext x
    constructor
    · intro hx
      change U x ∈ SchwartzSubmodule d at hx
      rw [← SpaceDHilbertSpace.fourierUnitary_map_schwartzSubmodule] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      have hyeq : y = x := U.injective (by simpa [U] using hxy)
      exact hyeq ▸ hy
    · intro hx
      change U x ∈ SchwartzSubmodule d
      have hmap : U x ∈ (SchwartzSubmodule d).map U.toLinearMap :=
        ⟨x, hx, rfl⟩
      rw [SpaceDHilbertSpace.fourierUnitary_map_schwartzSubmodule] at hmap
      exact hmap
  have hdomain' : (momentumOperator i).domain =
      (fourierSchwartzMomentumOperator i).domain := by
    simpa [momentumOperator] using hdomain.symm
  apply LinearPMap.eq_of_le_of_domain_eq ?_ hdomain'
  apply LinearPMap.le_of_le_graph
  rintro ⟨x, y⟩ hxy
  rw [LinearPMap.mem_graph_iff] at hxy ⊢
  obtain ⟨ψ, hψx, hψy⟩ := hxy
  obtain ⟨f, rfl⟩ := (schwartzEquiv volume).surjective ψ
  have hU : U (schwartzEquiv volume f) ∈ SchwartzSubmodule d := by
    change 𝓕 (schwartzIncl volume f) ∈ SchwartzSubmodule d
    rw [schwartzIncl_fourier_eq]
    exact ⟨𝓕 f, rfl⟩
  have hM : U (schwartzEquiv volume f) ∈
      (realMultiplicationOperator (μ := volume) (momentumCoordinate i)).domain := by
    exact mulOperator_domain_ge_of_hasTemperateGrowth
      (momentumCoordinateComplex_hasTemperateGrowth i) volume hU
  have htarget : (schwartzEquiv volume f : SpaceDHilbertSpace d) ∈
      (fourierSchwartzMomentumOperator i).domain := by
    change U (schwartzEquiv volume f) ∈ SchwartzSubmodule d
    exact hU
  refine ⟨⟨schwartzEquiv volume f, htarget⟩, ?_, ?_⟩
  · simpa using hψx
  · have happly := fourierSchwartzMomentumOperator_apply i f hM
    rw [happly]
    exact hψy

lemma schwartzMulOperator_closure_eq_realMultiplicationOperator
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    (schwartzMulOperator
      (f := momentumCoordinateComplex i)
      (momentumCoordinateComplex_hasTemperateGrowth i)).closure =
      realMultiplicationOperator (μ := volume) (momentumCoordinate i) := by
  have hfun : momentumCoordinateComplex i =
      (fun p : Space d => (momentumCoordinate i p : ℂ)) := by
    funext p
    simp [momentumCoordinateComplex, momentumCoordinate]
  have hcore := schwartzMulOperator_closure_eq_mulOperator
    (f := momentumCoordinateComplex i)
    (momentumCoordinateComplex_hasTemperateGrowth i)
  have hmul : 𝓜 volume (momentumCoordinateComplex i) =
      realMultiplicationOperator (μ := volume) (momentumCoordinate i) := by
    rw [realMultiplicationOperator]
    congr 1
  exact hcore.trans hmul

lemma momentumOperator_closure_eq_fourierMomentumOperator
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    (momentumOperator i).closure = fourierMomentumOperator i := by
  have hmul := schwartzMulOperator_closure_eq_realMultiplicationOperator i
  have hself := realMultiplicationOperator_isSelfAdjoint
    (μ := volume) (momentumCoordinate i)
    (momentumCoordinate_measurable i).aestronglyMeasurable
  have hSclosable :
      (schwartzMulOperator
        (f := momentumCoordinateComplex i)
        (momentumCoordinateComplex_hasTemperateGrowth i)).IsClosable := by
    apply LinearPMap.isClosable_iff_exists_closed_extension.mpr
    exact ⟨realMultiplicationOperator (μ := volume) (momentumCoordinate i),
      hself.isClosed,
      schwartzMulOperator_le_mulOperator
        (momentumCoordinateComplex_hasTemperateGrowth i)⟩
  have htransport := LinearPMap.IsClosable.unitaryConj_closure
    (SpaceDHilbertSpace.fourierUnitary d).symm
    (schwartzMulOperator
      (f := momentumCoordinateComplex i)
      (momentumCoordinateComplex_hasTemperateGrowth i)) hSclosable
  calc
    (momentumOperator i).closure =
        (fourierSchwartzMomentumOperator i).closure := by
      exact congrArg LinearPMap.closure
        (momentumOperator_eq_fourierSchwartzMomentumOperator i)
    _ = (LinearPMap.unitaryConj (SpaceDHilbertSpace.fourierUnitary d).symm
        (schwartzMulOperator
          (f := momentumCoordinateComplex i)
          (momentumCoordinateComplex_hasTemperateGrowth i))).closure := rfl
    _ = LinearPMap.unitaryConj (SpaceDHilbertSpace.fourierUnitary d).symm
        (schwartzMulOperator
          (f := momentumCoordinateComplex i)
          (momentumCoordinateComplex_hasTemperateGrowth i)).closure := htransport
    _ = fourierMomentumOperator i := by
      rw [hmul]
      rfl

lemma momentumOperator_isEssentiallySelfAdjoint
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    (momentumOperator i).IsEssentiallySelfAdjoint := by
  change IsSelfAdjoint (momentumOperator i).closure
  rw [momentumOperator_closure_eq_fourierMomentumOperator i]
  exact fourierMomentumOperator_isSelfAdjoint i

/-- Spectral data for the actual Schwartz momentum operator, obtained by closing it and using
the Fourier multiplication model. -/
def momentumOperatorSpectralData
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    OperatorAlgebra.EssentialSelfAdjointSpectralData (momentumOperator i) where
  essentiallySelfAdjoint := momentumOperator_isEssentiallySelfAdjoint i
  spectralMeasure := fourierMomentumSpectralMeasure i
  spectralTheorem := by
    rw [momentumOperator_closure_eq_fourierMomentumOperator i]
    exact fourierMomentumOperator_domainAwareSelfAdjointSpectralTheorem i

/-- The Schwartz differential momentum is a restriction of the maximal Fourier multiplier.

This is the graph inclusion retained as a compatibility lemma for clients that only need the
one-sided statement.  The equality of closures is supplied by
`momentumOperator_closure_eq_fourierMomentumOperator`. -/
lemma momentumOperator_le_fourierMomentumOperator (i : Fin d) :
    momentumOperator i ≤ fourierMomentumOperator i := by
  have momentumCoordinate_complex_hasTemperateGrowth (i : Fin d) :
      Function.HasTemperateGrowth
        (fun x : Space d => (momentumCoordinate i x : ℂ)) := by
    apply Function.Complex.hasTemperateGrowth_ofReal.comp
    unfold momentumCoordinate
    apply (Function.HasTemperateGrowth.const _).mul
    have heq : Space.coord i = ⇑(Space.coordCLM i) := by
      funext x
      exact (Space.coordCLM_apply i x).symm
    rw [heq]
    exact (Space.coordCLM i).hasTemperateGrowth
  apply LinearPMap.le_of_le_graph
  rintro ⟨x, y⟩ hx
  rw [LinearPMap.mem_graph_iff] at hx ⊢
  obtain ⟨ψ, hψx, hψy⟩ := hx
  let U := SpaceDHilbertSpace.fourierUnitary d
  have hUψ : U (ψ : SpaceDHilbertSpace d) ∈ SchwartzSubmodule d := by
    rw [← SpaceDHilbertSpace.fourierUnitary_map_schwartzSubmodule]
    exact ⟨ψ, ψ.property, rfl⟩
  have htemp := momentumCoordinate_complex_hasTemperateGrowth i
  have hM : U (ψ : SpaceDHilbertSpace d) ∈
      (realMultiplicationOperator (μ := volume) (momentumCoordinate i)).domain := by
    exact mulOperator_domain_ge_of_hasTemperateGrowth htemp volume hUψ
  have htarget : x ∈ (fourierMomentumOperator i).domain := by
    change x ∈ (LinearPMap.unitaryConj U.symm
      (realMultiplicationOperator (μ := volume) (momentumCoordinate i))).domain
    rw [LinearPMap.mem_unitaryConj_domain_iff]
    simpa [U, hψx] using hM
  refine ⟨⟨x, htarget⟩, ?_, ?_⟩
  · simpa using hψx
  have hconj := LinearPMap.unitaryConj_apply_map
    (SpaceDHilbertSpace.fourierUnitary d).symm
    (realMultiplicationOperator (μ := volume) (momentumCoordinate i))
    ⟨U (ψ : SpaceDHilbertSpace d), hM⟩
  have hconj' : fourierMomentumOperator i
      ⟨x, htarget⟩ =
        (SpaceDHilbertSpace.fourierUnitary d).symm
          ((realMultiplicationOperator (μ := volume) (momentumCoordinate i))
            ⟨U (ψ : SpaceDHilbertSpace d), hM⟩) := by
    simpa [fourierMomentumOperator, U, hψx] using hconj
  rw [hconj']
  rw [← hψy]
  apply U.injective
  rw [U.apply_symm_apply]
  obtain ⟨f, rfl⟩ := (schwartzEquiv volume).surjective ψ
  have hUf : U (↑(schwartzEquiv volume f) : SpaceDHilbertSpace d) =
      schwartzIncl volume (𝓕 f) := by
    change fourierUnitary d (↑(schwartzEquiv volume f) : SpaceDHilbertSpace d) = _
    rw [← schwartzEquiv_apply_coe]
    exact schwartzIncl_fourier_eq f
  have hP : (momentumOperator i) (schwartzEquiv volume f) =
      schwartzIncl volume (𝐩 i f) := by
    rw [momentumOperator_apply]
    simp only [LinearEquiv.symm_apply_apply]
    exact schwartzEquiv_apply_coe _
  have hUf_ae :
      U (↑(schwartzEquiv volume f) : SpaceDHilbertSpace d) =ᵐ[volume]
        ((𝓕 f : 𝓢(Space d, ℂ)) : Space d → ℂ) := by
    filter_upwards [SpaceDHilbertSpace.ext_iff.mp hUf,
      SchwartzMap.coeFn_toLp (𝓕 f) 2 volume] with z hz hz'
    exact hz.trans (by simpa [schwartzIncl] using hz')
  have hright_eq :
      U ((momentumOperator i) (schwartzEquiv volume f)) =
        schwartzIncl volume (𝓕 (𝐩 i f)) := by
    rw [hP]
    exact schwartzIncl_fourier_eq _
  have hright_ae :
      U ((momentumOperator i) (schwartzEquiv volume f)) =ᵐ[volume]
        ((𝓕 (𝐩 i f) : 𝓢(Space d, ℂ)) : Space d → ℂ) := by
    filter_upwards [SpaceDHilbertSpace.ext_iff.mp hright_eq,
      SchwartzMap.coeFn_toLp (𝓕 (𝐩 i f)) 2 volume] with z hz hz'
    exact hz.trans (by simpa [schwartzIncl] using hz')
  have hFourierMap := fourier_momentumCLM_eq i f
  have hM_ae :
      (realMultiplicationOperator (μ := volume) (momentumCoordinate i))
          ⟨U (↑(schwartzEquiv volume f) : SpaceDHilbertSpace d), hM⟩ =ᵐ[volume]
        (fun z : Space d => (momentumCoordinate i z : ℂ)) *
          (U (↑(schwartzEquiv volume f) : SpaceDHilbertSpace d)) := by
    simpa [realMultiplicationOperator] using
      (mulOperator_apply_ae
        ⟨U (↑(schwartzEquiv volume f) : SpaceDHilbertSpace d), hM⟩)
  apply SpaceDHilbertSpace.ext_iff.mpr
  filter_upwards [hM_ae, hUf_ae, hright_ae] with z hM' hUf' hright'
  rw [hM', hright']
  simp only [Pi.mul_apply]
  rw [hUf']
  have hcoordC :
      (fun x : Space d => (x i : ℂ)).HasTemperateGrowth := by
    apply Function.Complex.hasTemperateGrowth_ofReal.comp
    have hcoord : HasTemperateGrowth (Space.coord i) := by
      have heq : Space.coord i = ⇑(Space.coordCLM i) := by
        funext x
        exact (Space.coordCLM_apply i x).symm
      rw [heq]
      exact (Space.coordCLM i).hasTemperateGrowth
    have heq : (fun x : Space d => x.val i) = Space.coord i := by
      funext x
      exact (Space.coord_apply i x).symm
    rw [heq]
    exact hcoord
  have hsmul :
      ((SchwartzMap.smulLeftCLM ℂ (fun x : Space d => (x i : ℂ))
        (𝓕 f) : 𝓢(Space d, ℂ)) : Space d → ℂ) z =
        (z i : ℂ) * (𝓕 f) z := by
    rw [SchwartzMap.smulLeftCLM_apply hcoordC]
    simp only [smul_eq_mul]
  have hFourierPoint := congr_fun
    (congrArg (fun g : 𝓢(Space d, ℂ) => (g : Space d → ℂ)) hFourierMap) z
  change (𝓕 (𝐩 i f)) z =
    (2 * Real.pi * (ℏ : ℂ)) •
      ((SchwartzMap.smulLeftCLM ℂ (fun x : Space d => (x i : ℂ))
        (𝓕 f)) z) at hFourierPoint
  rw [hsmul] at hFourierPoint
  rw [show (z.val i : ℂ) = (Space.coord i z : ℂ) by
    rw [Space.coord_apply]] at hFourierPoint
  rw [momentumCoordinate]
  convert hFourierPoint.symm using 1 <;> push_cast <;> ring

/-- The closure of the Schwartz momentum is contained in the maximal Fourier realization. -/
lemma momentumOperator_closure_le_fourierMomentumOperator
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    (momentumOperator i).closure ≤ fourierMomentumOperator i := by
  have hself := fourierMomentumOperator_isSelfAdjoint i
  have hclosed := LinearPMap.IsSelfAdjoint.isClosable hself
  have hmono := hclosed.closure_mono (momentumOperator_le_fourierMomentumOperator i)
  have hfourier_closed : (fourierMomentumOperator i).IsClosed :=
    LinearPMap.IsSelfAdjoint.isClosed hself
  rw [hfourier_closed.closure_eq] at hmono
  exact hmono

end QuantumMechanics
