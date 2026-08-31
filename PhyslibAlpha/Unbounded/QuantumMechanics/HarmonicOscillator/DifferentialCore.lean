/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.HarmonicOscillator.EssentialSelfAdjointness
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Examples.HarmonicOscillator
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Examples.Spectrum
public import Physlib.Mathematics.InnerProductSpace.Gaussian

/-! # The differential oscillator core

This file is the bridge between the older one-dimensional `ℝ` model and the current
`SpaceDHilbertSpace 1` operator API.  The bridge is built through `Space.oneEquiv`; no
identification of the two function types is taken for granted.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap
open QuantumMechanics
open QuantumMechanics.SpaceDHilbertSpace
open QuantumMechanics.HarmonicOscillator
open _root_.QuantumMechanics.OneDimension
open OperatorAlgebra.Unbounded.Example
open Polynomial

namespace QuantumMechanics.HarmonicOscillator

def oneDimension (q : _root_.QuantumMechanics.OneDimension.HarmonicOscillator) :
    QuantumMechanics.HarmonicOscillator 1 :=
  { m := q.m
    hm := q.hm
    ω := fun _ => q.ω
    hω := fun _ => q.hω }

namespace DifferentialCore

abbrev OldHilbertSpace := _root_.QuantumMechanics.OneDimension.HilbertSpace
abbrev NewHilbertSpace := SpaceDHilbertSpace 1
abbrev OldOscillator := _root_.QuantumMechanics.OneDimension.HarmonicOscillator

noncomputable def oneEquivLp : OldHilbertSpace ≃ₗᵢ[ℂ] NewHilbertSpace :=
  LinearIsometryEquiv.ofLinearIsometry
    (Lp.compMeasurePreservingₗᵢ ℂ Space.oneEquiv Space.oneEquiv_measurePreserving)
    (Lp.compMeasurePreservingₗ ℂ Space.oneEquiv.symm Space.oneEquiv_symm_measurePreserving)
    (by
      ext f
      change (Lp.compMeasurePreserving Space.oneEquiv Space.oneEquiv_measurePreserving
        (Lp.compMeasurePreserving Space.oneEquiv.symm Space.oneEquiv_symm_measurePreserving f) :
          NewHilbertSpace) =ᵐ[volume] f
      rw [← Lp.compMeasurePreserving_comp_apply f Space.oneEquiv_symm_measurePreserving
        Space.oneEquiv_measurePreserving]
      simp)
    (by
      ext f
      change (Lp.compMeasurePreserving Space.oneEquiv.symm Space.oneEquiv_symm_measurePreserving
        (Lp.compMeasurePreserving Space.oneEquiv Space.oneEquiv_measurePreserving f) :
          OldHilbertSpace) =ᵐ[volume] f
      rw [← Lp.compMeasurePreserving_comp_apply f Space.oneEquiv_measurePreserving
        Space.oneEquiv_symm_measurePreserving]
      simp)

@[simp]
lemma oneEquivLp_apply (f : OldHilbertSpace) :
    oneEquivLp f = Lp.compMeasurePreserving Space.oneEquiv
      Space.oneEquiv_measurePreserving f := by
  rfl

open _root_.QuantumMechanics.OneDimension.HarmonicOscillator
open Physlib

noncomputable def gaussianSpace (q : OldOscillator) : 𝓢(Space 1, ℂ) :=
  (gaussianVacuum q.m q.ω q.hm q.hω).compCLMOfContinuousLinearEquiv ℂ Space.oneEquivCLE

lemma gaussianSpace_apply (q : OldOscillator) (x : Space 1) :
    gaussianSpace q x = gaussianVacuum q.m q.ω q.hm q.hω (x 0) := by
  rfl

noncomputable def hermitePolynomialSpace (q : OldOscillator) (n : ℕ) : Space 1 → ℂ :=
  fun x => (physHermite n (x 0 / q.ξ) : ℂ)

lemma hermitePolynomialSpace_hasTemperateGrowth (q : OldOscillator) (n : ℕ) :
    Function.HasTemperateGrowth (hermitePolynomialSpace q n) := by
  have harg : (fun x : Space 1 => x 0 / q.ξ) =
      (fun x : Space 1 => q.ξ⁻¹ * x 0) := by
    funext x
    field_simp
  have hcoord : Function.HasTemperateGrowth (fun x : Space 1 => x 0) := by
    have hcoord' := (Space.coordCLM (0 : Fin 1)).hasTemperateGrowth
    have hfun : (Space.coordCLM (0 : Fin 1) : Space 1 → ℝ) =
        (fun x : Space 1 => x 0) := by
      funext x
      rw [Space.coordCLM_apply, Space.coord_apply]
    rw [hfun] at hcoord'
    exact hcoord'
  have hscale : Function.HasTemperateGrowth (fun x : Space 1 => q.ξ⁻¹ * x 0) := by
    exact (Function.HasTemperateGrowth.const _).mul hcoord
  have hpoly : Function.HasTemperateGrowth
      (fun x : Space 1 => (physHermite n (q.ξ⁻¹ * x 0) : ℂ)) :=
    Function.Complex.hasTemperateGrowth_ofReal.comp
    ((physHermite_hasTemperateGrowth n).comp hscale)
  have hcomp : (fun x : Space 1 => (physHermite n (x 0 / q.ξ) : ℂ)) =
      (fun x : Space 1 => (physHermite n (q.ξ⁻¹ * x 0) : ℂ)) := by
    funext x
    exact congrArg (fun y : ℝ => (physHermite n y : ℂ)) (congrFun harg x)
  change Function.HasTemperateGrowth
    (fun x : Space 1 => (physHermite n (x 0 / q.ξ) : ℂ))
  rw [hcomp]
  exact hpoly

noncomputable def eigenfunctionSpaceSchwartz (q : OldOscillator) (n : ℕ) :
    𝓢(Space 1, ℂ) :=
  Complex.ofReal ((Real.sqrt ((2 ^ n * Nat.factorial n : ℕ) : ℝ))⁻¹ *
      (Real.sqrt (Real.sqrt Real.pi * q.ξ))⁻¹) •
    SchwartzMap.smulLeftCLM ℂ (hermitePolynomialSpace q n) (gaussianSpace q)

/-- The Hilbert-space eigenfunction, evaluated pointwise, is exactly the textbook
Hermite-times-Gaussian formula `q.eigenfunction n`. Cited directly by `Summary.lean`. -/
lemma eigenfunctionSpaceSchwartz_apply (q : OldOscillator) (n : ℕ) (x : Space 1) :
    eigenfunctionSpaceSchwartz q n x =
      q.eigenfunction n (x 0) := by
  rw [eigenfunctionSpaceSchwartz, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply (hermitePolynomialSpace_hasTemperateGrowth q n),
    gaussianSpace_apply, gaussianVacuum_apply]
  simp only [OneDimension.HarmonicOscillator.eigenfunction, hermitePolynomialSpace,
    Pi.smul_apply, smul_eq_mul, Complex.ofReal_exp]
  rw [q.ξ_sq]
  push_cast
  have hexp :
      (-(q.m * q.ω / (2 * Constants.ℏ)) * (x 0) ^ 2 : ℂ) =
        (-((x 0) ^ 2) / (2 * (Constants.ℏ / (q.m * q.ω))) : ℂ) := by
    norm_cast
    field_simp [Constants.ℏ_ne_zero, q.m_ne_zero, q.ω_ne_zero] <;> ring
  rw [hexp]
  ring

noncomputable def eigenfunctionSpace (q : OldOscillator) (n : ℕ) : NewHilbertSpace :=
  SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n)

noncomputable def transportedEigenbasis (q : OldOscillator) :
    HilbertBasis ℕ ℂ NewHilbertSpace :=
  HilbertBasis.ofRepr (oneEquivLp.symm.trans
    (_root_.QuantumMechanics.OneDimension.HarmonicOscillator.eigenbasis q).repr)

lemma transportedEigenbasis_apply (q : OldOscillator) (n : ℕ) :
    transportedEigenbasis q n = oneEquivLp
      (_root_.QuantumMechanics.OneDimension.HarmonicOscillator.eigenbasis q n) := by
  apply (transportedEigenbasis q).repr.injective
  rw [HilbertBasis.repr_self]
  change _ = (_root_.QuantumMechanics.OneDimension.HarmonicOscillator.eigenbasis q).repr
    (oneEquivLp.symm (oneEquivLp
      (_root_.QuantumMechanics.OneDimension.HarmonicOscillator.eigenbasis q n)))
  rw [oneEquivLp.symm_apply_apply, HilbertBasis.repr_self]

lemma eigenfunctionSpace_eq_transportedEigenbasis (q : OldOscillator) (n : ℕ) :
    eigenfunctionSpace q n = transportedEigenbasis q n := by
  rw [transportedEigenbasis_apply,
    _root_.QuantumMechanics.OneDimension.HarmonicOscillator.eigenbasis_apply]
  change SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n) = _
  rw [← SpaceDHilbertSpace.SchwartzSubmodule.schwartzEquiv_apply_coe]
  apply Lp.ext
  have hold :
      (fun x : Space 1 =>
        (_root_.QuantumMechanics.OneDimension.HilbertSpace.mk
          (q.eigenfunction_memHS n)) (x 0)) =ᵐ[volume]
        (fun x : Space 1 => q.eigenfunction n (x 0)) :=
    Space.oneEquiv_measurePreserving.quasiMeasurePreserving.ae
      (_root_.QuantumMechanics.OneDimension.HilbertSpace.coe_mk_ae
        (q.eigenfunction_memHS n))
  filter_upwards [SpaceDHilbertSpace.SchwartzSubmodule.schwartzEquiv_coe_ae
      (eigenfunctionSpaceSchwartz q n),
    Lp.coeFn_compMeasurePreserving
      (_root_.QuantumMechanics.OneDimension.HilbertSpace.mk
        (q.eigenfunction_memHS n)) Space.oneEquiv_measurePreserving, hold] with x hx hcomp hold
  rw [hx, eigenfunctionSpaceSchwartz_apply, oneEquivLp_apply, hcomp]
  exact hold.symm

lemma schwartzEquiv_symm_apply_schwartzIncl (s : 𝓢(Space 1, ℂ))
    (hs : SpaceDHilbertSpace.schwartzIncl volume s ∈ SchwartzSubmodule 1) :
    (SpaceDHilbertSpace.schwartzEquiv volume).symm
        (⟨SpaceDHilbertSpace.schwartzIncl volume s, hs⟩ : SchwartzSubmodule 1) = s := by
  apply (SpaceDHilbertSpace.schwartzEquiv volume).injective
  calc
    (SpaceDHilbertSpace.schwartzEquiv volume)
        ((SpaceDHilbertSpace.schwartzEquiv volume).symm
          (⟨SpaceDHilbertSpace.schwartzIncl volume s, hs⟩ : SchwartzSubmodule 1)) =
        (⟨SpaceDHilbertSpace.schwartzIncl volume s, hs⟩ : SchwartzSubmodule 1) :=
      (SpaceDHilbertSpace.schwartzEquiv volume).apply_symm_apply _
    _ = SpaceDHilbertSpace.schwartzEquiv volume s := by
      apply Subtype.ext
      exact (SpaceDHilbertSpace.SchwartzSubmodule.schwartzEquiv_apply_coe s).symm

lemma momentumOperator_apply_schwartz (s : 𝓢(Space 1, ℂ))
    (hs : SpaceDHilbertSpace.schwartzIncl volume s ∈ SchwartzSubmodule 1) :
    momentumOperator (0 : Fin 1) ⟨SpaceDHilbertSpace.schwartzIncl volume s, hs⟩ =
      SpaceDHilbertSpace.schwartzIncl volume (𝐩 (0 : Fin 1) s) := by
  change SpaceDHilbertSpace.schwartzIncl volume
      (𝐩 (0 : Fin 1) ((SpaceDHilbertSpace.schwartzEquiv volume).symm
        ⟨SpaceDHilbertSpace.schwartzIncl volume s, hs⟩)) = _
  have hsymm := schwartzEquiv_symm_apply_schwartzIncl s hs
  rw [hsymm, ← SpaceDHilbertSpace.SchwartzSubmodule.schwartzEquiv_apply_coe]

lemma momentumSqOperator_apply_schwartz (s : 𝓢(Space 1, ℂ))
    (hdom : SpaceDHilbertSpace.schwartzIncl volume s ∈
      (momentumSqOperator (d := 1)).domain) :
    momentumSqOperator (d := 1) ⟨SpaceDHilbertSpace.schwartzIncl volume s, hdom⟩ =
      SpaceDHilbertSpace.schwartzIncl volume (𝐩 (0 : Fin 1) (𝐩 (0 : Fin 1) s)) := by
  unfold momentumSqOperator
  rw [LinearPMap.sum_apply]
  simp only [Fin.sum_univ_one]
  have h0 : SpaceDHilbertSpace.schwartzIncl volume s ∈
      (momentumOperator (d := 1) 0).domain := ⟨s, rfl⟩
  have hp : momentumOperator (d := 1) 0
      ⟨SpaceDHilbertSpace.schwartzIncl volume s, h0⟩ =
      SpaceDHilbertSpace.schwartzIncl volume (𝐩 (0 : Fin 1) s) :=
    momentumOperator_apply_schwartz s h0
  have h1 : momentumOperator (d := 1) 0
      ⟨SpaceDHilbertSpace.schwartzIncl volume s, h0⟩ ∈
      (momentumOperator (d := 1) 0).domain := by
    rw [hp]
    exact ⟨𝐩 (0 : Fin 1) s, rfl⟩
  change momentumOperator (d := 1) 0
      ⟨momentumOperator (d := 1) 0
        ⟨SpaceDHilbertSpace.schwartzIncl volume s, h0⟩, h1⟩ = _
  have hsub :
      (⟨momentumOperator (d := 1) 0
          ⟨SpaceDHilbertSpace.schwartzIncl volume s, h0⟩, h1⟩ :
        (momentumOperator (d := 1) 0).domain) =
      ⟨SpaceDHilbertSpace.schwartzIncl volume (𝐩 (0 : Fin 1) s),
        ⟨𝐩 (0 : Fin 1) s, rfl⟩⟩ := by
    apply Subtype.ext
    exact hp
  rw [hsub]
  exact momentumOperator_apply_schwartz (𝐩 (0 : Fin 1) s) ⟨𝐩 (0 : Fin 1) s, rfl⟩

lemma eigenfunction_differentiable (q : OldOscillator) (n : ℕ) :
    Differentiable ℝ (q.eigenfunction n) := by
  intro x
  exact q.eigenfunction_differentiableAt x n

lemma eigenfunction_deriv_differentiable (q : OldOscillator) (n : ℕ) :
    Differentiable ℝ (deriv (q.eigenfunction n)) := by
  have hcont : ContDiff ℝ (↑(⊤ : ℕ∞)) (q.eigenfunction n) := by
    rw [q.eigenfunction_eq]
    have hreal : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun x : ℝ => physHermite n (x / q.ξ) * Real.exp (-x ^ 2 / (2 * q.ξ ^ 2))) := by
      fun_prop
    have hof : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun x : ℝ => Complex.ofReal
          (physHermite n (x / q.ξ) * Real.exp (-x ^ 2 / (2 * q.ξ ^ 2)))) := by
      convert (Complex.ofRealCLM.contDiff.comp hreal) using 1 <;> rfl
    change ContDiff ℝ (↑(⊤ : ℕ∞))
      ((fun _ : ℝ => (1 / Complex.ofReal (Real.sqrt (2 ^ n * Nat.factorial n))) *
        (1 / Complex.ofReal (Real.sqrt (Real.sqrt Real.pi * q.ξ)))) *
        (fun x : ℝ => Complex.ofReal
          (physHermite n (x / q.ξ) * Real.exp (-x ^ 2 / (2 * q.ξ ^ 2)))))
    exact contDiff_const.mul hof
  have hderiv : ContDiff ℝ (↑(⊤ : ℕ∞)) (deriv (q.eigenfunction n)) :=
    (contDiff_infty_iff_deriv (𝕜 := ℝ)).mp hcont |>.2
  exact hderiv.differentiable (by simp)

lemma deriv_space_one_comp (f : ℝ → ℂ) (hf : Differentiable ℝ f) (x : Space 1) :
    ∂[(0 : Fin 1)] (f ∘ fun y : Space 1 => y 0) x = deriv f (x 0) := by
  rw [Space.deriv_eq, fderiv_comp x hf.differentiableAt (by fun_prop)]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  have hcoord : fderiv ℝ (fun y : Space 1 => y 0) x (Space.basis 0) = 1 := by
    simp [Space.coord_apply, Space.basis_apply]
  rw [hcoord, fderiv_apply_one_eq_deriv]

lemma eigenfunctionSpaceSchwartz_momentumSq_apply (q : OldOscillator) (n : ℕ) (x : Space 1) :
    (𝐩 (0 : Fin 1) (𝐩 (0 : Fin 1) (eigenfunctionSpaceSchwartz q n))) x =
      (-Constants.ℏ ^ 2) * deriv (deriv (q.eigenfunction n)) (x 0) := by
  have hfun : (eigenfunctionSpaceSchwartz q n : Space 1 → ℂ) =
      q.eigenfunction n ∘ fun y : Space 1 => y 0 := by
    funext y
    exact eigenfunctionSpaceSchwartz_apply q n y
  have hf := eigenfunction_differentiable q n
  have hdf := eigenfunction_deriv_differentiable q n
  have hcoordDiff : DifferentiableAt ℝ (fun y : Space 1 => y 0) x := by
    have hcoordfun : (fun y : Space 1 => y 0) = Space.coordCLM (0 : Fin 1) := by
      funext y
      simp [Space.coordCLM_apply, Space.coord_apply]
    rw [hcoordfun]
    exact (Space.coordCLM (0 : Fin 1)).differentiableAt
  have hcompDiff : DifferentiableAt ℝ
      (fun y : Space 1 => deriv (q.eigenfunction n) (y 0)) x :=
    hdf.differentiableAt.comp x hcoordDiff
  rw [momentumCLM_apply]
  have hpfun : (𝐩 (0 : Fin 1) (eigenfunctionSpaceSchwartz q n) : Space 1 → ℂ) =
      fun y : Space 1 => (-Complex.I * Constants.ℏ) *
        deriv (q.eigenfunction n) (y 0) := by
    funext y
    rw [momentumCLM_apply, hfun]
    exact congrArg (fun z => (-Complex.I * Constants.ℏ) * z)
      (deriv_space_one_comp (q.eigenfunction n) hf y)
  rw [hpfun]
  rw [Space.deriv_eq, fderiv_const_mul]
  · have hcomp : fderiv ℝ (fun y : Space 1 => deriv (q.eigenfunction n) (y 0)) x
        (Space.basis 0) = deriv (deriv (q.eigenfunction n)) (x 0) := by
      rw [show (fun y : Space 1 => deriv (q.eigenfunction n) (y 0)) =
        deriv (q.eigenfunction n) ∘ fun y : Space 1 => y 0 by rfl,
        fderiv_comp x hdf.differentiableAt hcoordDiff]
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
      have hcoord : fderiv ℝ (fun y : Space 1 => y 0) x (Space.basis 0) = 1 := by
        simp [Space.coord_apply, Space.basis_apply]
      rw [hcoord, fderiv_apply_one_eq_deriv]
    simp only [ContinuousLinearMap.smul_apply]
    rw [hcomp]
    simp only [smul_eq_mul]
    ring_nf
    simp [Complex.I_sq]
  · exact hcompDiff

lemma hamiltonian_apply_eigenfunction (q : OldOscillator) (n : ℕ)
    (hdom : SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n) ∈
      (oneDimension q).hamiltonian.domain) :
    (oneDimension q).hamiltonian ⟨SpaceDHilbertSpace.schwartzIncl volume
        (eigenfunctionSpaceSchwartz q n), hdom⟩ =
      (q.eigenValue n : ℂ) •
        SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n) := by
  let Q : QuantumMechanics.HarmonicOscillator 1 := oneDimension q
  have hsq : SpaceDHilbertSpace.schwartzIncl volume
      (eigenfunctionSpaceSchwartz q n) ∈ (momentumSqOperator (d := 1)).domain := by
    rw [momentumSqOperator_domain_eq]
    exact ⟨eigenfunctionSpaceSchwartz q n, rfl⟩
  have hkin : SpaceDHilbertSpace.schwartzIncl volume
      (eigenfunctionSpaceSchwartz q n) ∈ Q.kineticOperator.domain := by
    rw [kineticOperator, LinearPMap.smul_domain]
    exact hsq
  have hpot : SpaceDHilbertSpace.schwartzIncl volume
      (eigenfunctionSpaceSchwartz q n) ∈ Q.potentialOperator.domain := by
    exact Q.schwartzSubmodule_le_potentialOperator_domain
      ⟨eigenfunctionSpaceSchwartz q n, rfl⟩
  change SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n) ∈
      (𝓜 volume (Complex.ofReal ∘ Q.potentialFunction)).domain at hpot
  change (Q.kineticOperator + Q.potentialOperator)
    ⟨SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n),
      ⟨hkin, hpot⟩⟩ = _
  rw [LinearPMap.add_apply]
  change ((2 * Q.m)⁻¹ • momentumSqOperator)
      ⟨SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n), hsq⟩ +
      Q.potentialOperator
        ⟨SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n), hpot⟩ = _
  rw [LinearPMap.smul_apply]
  rw [momentumSqOperator_apply_schwartz (eigenfunctionSpaceSchwartz q n) hsq]
  have hsIncl : (SpaceDHilbertSpace.schwartzIncl volume
      (eigenfunctionSpaceSchwartz q n) : Space 1 → ℂ) =ᵐ[volume]
      eigenfunctionSpaceSchwartz q n := by
    simpa only [← SpaceDHilbertSpace.SchwartzSubmodule.schwartzEquiv_apply_coe] using
      (SpaceDHilbertSpace.SchwartzSubmodule.schwartzEquiv_coe_ae
        (eigenfunctionSpaceSchwartz q n))
  have hppIncl : (SpaceDHilbertSpace.schwartzIncl volume
      (𝐩 (0 : Fin 1) (𝐩 (0 : Fin 1) (eigenfunctionSpaceSchwartz q n))) : Space 1 → ℂ) =ᵐ[volume]
      (𝐩 (0 : Fin 1) (𝐩 (0 : Fin 1) (eigenfunctionSpaceSchwartz q n))) := by
    simpa only [← SpaceDHilbertSpace.SchwartzSubmodule.schwartzEquiv_apply_coe] using
      (SpaceDHilbertSpace.SchwartzSubmodule.schwartzEquiv_coe_ae
        (𝐩 (0 : Fin 1) (𝐩 (0 : Fin 1) (eigenfunctionSpaceSchwartz q n))))
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      ((2 * Q.m)⁻¹ • SpaceDHilbertSpace.schwartzIncl volume
        (𝐩 (0 : Fin 1) (𝐩 (0 : Fin 1) (eigenfunctionSpaceSchwartz q n))))
      (Q.potentialOperator
        ⟨SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n), hpot⟩),
    Lp.coeFn_smul ((2 * Q.m)⁻¹ : ℝ)
      (SpaceDHilbertSpace.schwartzIncl volume
        (𝐩 (0 : Fin 1) (𝐩 (0 : Fin 1) (eigenfunctionSpaceSchwartz q n)))),
    mulOperator_apply_ae
      ⟨SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n), hpot⟩,
    Lp.coeFn_smul (q.eigenValue n : ℂ)
      (SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n)),
    hsIncl, hppIncl] with x hadd hkin' hx hright hs hpp
  rw [hadd]
  simp only [Pi.add_apply]
  change ((2 * Q.m)⁻¹ • SpaceDHilbertSpace.schwartzIncl volume
      (𝐩 (0 : Fin 1) (𝐩 (0 : Fin 1) (eigenfunctionSpaceSchwartz q n)))) x +
      (𝓜 volume (Complex.ofReal ∘ Q.potentialFunction))
        ⟨SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n), hpot⟩ x = _
  rw [hkin', hx, hright]
  simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul, Function.comp_apply]
  rw [hs, hpp]
  rw [eigenfunctionSpaceSchwartz_apply]
  rw [show (𝐩 (0 : Fin 1) (𝐩 (0 : Fin 1) (eigenfunctionSpaceSchwartz q n))) x =
      (-Constants.ℏ ^ 2) * deriv (deriv (q.eigenfunction n)) (x 0) by
        exact eigenfunctionSpaceSchwartz_momentumSq_apply q n x]
  rw [← _root_.QuantumMechanics.OneDimension.HarmonicOscillator.schrodingerOperator_eigenfunction
      q n (x 0)]
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [hs, eigenfunctionSpaceSchwartz_apply]
  simp [potentialFunction_one_eq,
    _root_.QuantumMechanics.OneDimension.HarmonicOscillator.schrodingerOperator]
  dsimp [Q, oneDimension]
  ring

/-! ## Essential self-adjointness of the actual differential operator

The preceding calculation is the model-specific analytic step.  The transported Hermite
functions are a dense family in the current `L²(Space 1)` model, they belong to the Schwartz
domain, and the differential Hamiltonian acts on them by the real oscillator eigenvalues.  The
general dense-real-eigenvector criterion therefore applies to the differential operator itself;
no separate deficiency-space certificate is needed here.
-/

noncomputable def differentialHamiltonianCore (q : OldOscillator) :
    OperatorAlgebra.EssentialSelfAdjointCore (H := NewHilbertSpace) :=
  OperatorAlgebra.EssentialSelfAdjointCore.ofDenseRealEigenvectors
    (oneDimension q).hamiltonian_isSymmetric
    (oneDimension q).hamiltonian_hasDenseDomain
    (eigenfunctionSpace q) q.eigenValue
    (fun n => by
      rw [(oneDimension q).hamiltonian_domain_eq]
      exact ⟨eigenfunctionSpaceSchwartz q n, rfl⟩)
    (fun n => by
      simpa [eigenfunctionSpace] using
        (hamiltonian_apply_eigenfunction q n (by
          rw [(oneDimension q).hamiltonian_domain_eq]
          exact ⟨eigenfunctionSpaceSchwartz q n, rfl⟩)))
    (by
      have hv : (eigenfunctionSpace q) = transportedEigenbasis q :=
        funext (eigenfunctionSpace_eq_transportedEigenbasis q)
      rw [hv]
      exact (transportedEigenbasis q).dense_span)

/-- The actual Schwartz differential oscillator Hamiltonian is essentially self-adjoint. -/
lemma differentialHamiltonian_isEssentiallySelfAdjoint (q : OldOscillator) :
    (oneDimension q).hamiltonian.IsEssentiallySelfAdjoint :=
  (differentialHamiltonianCore q).essentiallySelfAdjoint

/-- The canonical self-adjoint closure of the actual differential oscillator Hamiltonian. -/
noncomputable abbrev differentialHamiltonianClosure (q : OldOscillator) :
    NewHilbertSpace →ₗ.[ℂ] NewHilbertSpace :=
  (differentialHamiltonianCore q).closure

lemma differentialHamiltonian_mem_closure_domain (q : OldOscillator) (n : ℕ) :
    eigenfunctionSpace q n ∈ (differentialHamiltonianClosure q).domain := by
  apply (differentialHamiltonianCore q).le_closure.1
  change eigenfunctionSpace q n ∈ (oneDimension q).hamiltonian.domain
  rw [(oneDimension q).hamiltonian_domain_eq]
  exact ⟨eigenfunctionSpaceSchwartz q n, rfl⟩

/-- Every transported Hermite vector remains an eigenvector of the self-adjoint closure. -/
lemma differentialHamiltonianClosure_apply_eigenfunction (q : OldOscillator) (n : ℕ) :
    differentialHamiltonianClosure q
        ⟨eigenfunctionSpace q n, differentialHamiltonian_mem_closure_domain q n⟩ =
      (q.eigenValue n : ℂ) • eigenfunctionSpace q n := by
  have hdom : SpaceDHilbertSpace.schwartzIncl volume
      (eigenfunctionSpaceSchwartz q n) ∈ (oneDimension q).hamiltonian.domain := by
    rw [(oneDimension q).hamiltonian_domain_eq]
    exact ⟨eigenfunctionSpaceSchwartz q n, rfl⟩
  have hcore : (oneDimension q).hamiltonian
      ⟨SpaceDHilbertSpace.schwartzIncl volume (eigenfunctionSpaceSchwartz q n), hdom⟩ =
      differentialHamiltonianClosure q
        ⟨eigenfunctionSpace q n, differentialHamiltonian_mem_closure_domain q n⟩ := by
    exact (differentialHamiltonianCore q).le_closure.2 rfl
  rw [← hcore]
  exact hamiltonian_apply_eigenfunction q n hdom

/-- The Cayley-constructed real spectral measure of the differential oscillator closure. -/
noncomputable abbrev differentialHamiltonianSpectralMeasure (q : OldOscillator) :
    QuantumMechanics.WOTSpectralMeasure ℝ NewHilbertSpace :=
  (differentialHamiltonianCore q).spectralMeasure

/-- The domain-aware unbounded spectral theorem for the differential oscillator closure. -/
noncomputable abbrev differentialHamiltonianSpectralTheorem (q : OldOscillator) :
    OperatorAlgebra.DomainAwareSelfAdjointSpectralTheorem
      (differentialHamiltonianClosure q) (differentialHamiltonianSpectralMeasure q) :=
  (differentialHamiltonianCore q).spectralTheorem

/-- The closure domain is the finite second-moment domain of the Cayley spectral measure. -/
lemma differentialHamiltonian_domain_eq_squareMoment (q : OldOscillator) :
    (differentialHamiltonianClosure q).domain =
      OperatorAlgebra.spectralSquareMomentDomain
        (differentialHamiltonianSpectralMeasure q) :=
  (differentialHamiltonianCore q).domain_eq_squareMoment

/-- The differential oscillator closure is self-adjoint. -/
lemma differentialHamiltonianClosure_isSelfAdjoint (q : OldOscillator) :
    IsSelfAdjoint (differentialHamiltonianClosure q) :=
  (differentialHamiltonianCore q).closure_isSelfAdjoint

/-- The closure is exactly the maximal square-moment spectral integral. -/
lemma differentialHamiltonian_maximalSpectralIntegral_eq (q : OldOscillator) :
    QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
        (differentialHamiltonianSpectralMeasure q) = differentialHamiltonianClosure q :=
  (differentialHamiltonianCore q).maximalSpectralIntegral_eq

/-- The unitary group generated by the self-adjoint closure of the differential Hamiltonian. -/
noncomputable abbrev differentialHamiltonianUnitaryGroup (q : OldOscillator) :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup NewHilbertSpace :=
  (differentialHamiltonianCore q).expUnitaryGroup

/-- The conventional quantum evolution `exp (-I t closure(H))`. -/
noncomputable abbrev differentialHamiltonianEvolution (q : OldOscillator) :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup NewHilbertSpace :=
  (differentialHamiltonianCore q).negativeExpUnitaryGroup

/-- The physical oscillator packaged as a quantum system using the actual differential core. -/
noncomputable def differentialHamiltonianQuantumSystem (q : OldOscillator) : QuantumSystem :=
  QuantumSystem.mkESA (differentialHamiltonian_isEssentiallySelfAdjoint q)

end DifferentialCore
end QuantumMechanics.HarmonicOscillator
end
