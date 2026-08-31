/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.Completeness

/-!
# Plancherel's theorem for the classical Fourier transform

`Completeness.lean` proves Hermite completeness in `L²(ℝ)` conditional on Plancherel's theorem
for the *classical* (pointwise-integral) Fourier transform `𝓕` on functions that are
simultaneously `Integrable` and `MemLp · 2`. Mathlib has Plancherel's theorem only in the
abstract `Lp`-isometry form (`MeasureTheory.Lp.fourierTransformₗᵢ`,
`MeasureTheory.Lp.norm_fourier_eq`, in `Mathlib.Analysis.Fourier.LpSpace`). This file bridges the
two, and discharges `Completeness.lean`'s hypothesis, giving an unconditional statement of Hermite
completeness.

## Main statements

* `plancherel_theorem_classical`: for `f : ℝ → ℂ` with `Integrable f volume` and `MemLp f 2
  volume`, `eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume`.
* `QuantumMechanics.OneDimension.HarmonicOscillator.eigenfunction_completeness'`: the
  unconditional (hypothesis-free) statement that the harmonic-oscillator eigenfunctions span a
  topologically dense subspace of `L²(ℝ)`.

## Proof idea

Write `F := hf2.toLp f` for the `L²`-class of `f`, and `G := 𝓕 F` for its abstract `L²`-Fourier
transform (an a.e.-equivalence class). We show `𝓕 f =ᵐ G` (as functions), from which the
`eLpNorm` equality follows from the abstract isometry `‖𝓕 F‖ = ‖F‖`.

To show `𝓕 f =ᵐ G`, we show that `𝓕 f - (G : ℝ → ℂ)` is locally integrable and integrates to
zero against every real-valued, smooth, compactly-supported test function `φ`; this forces a.e.
vanishing by `ae_eq_zero_of_integral_contDiff_smul_eq_zero`. The vanishing itself follows by
computing the same pairing two ways:

* On the classical side, the self-adjointness/multiplication formula for the classical Fourier
  transform (`VectorFourier.integral_bilin_fourierIntegral_eq_flip`) gives
  `∫ ξ, (𝓕 f) ξ * φ ξ = ∫ x, f x * (𝓕 φ) x`.
* On the abstract side, unitarity of `Lp.fourierTransformₗᵢ` gives the adjoint identity
  `⟪a, 𝓕 b⟫ = ⟪𝓕⁻ a, b⟫`, which (using `SchwartzMap.toLp_fourierInv_eq` to move the Fourier
  transform of the Schwartz lift of `φ` back to the classical picture) reduces to the same
  integral, using that `φ` is real-valued so `conj (𝓕 φ) = 𝓕⁻ φ` pointwise.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Complex FourierTransform
open scoped ComplexConjugate InnerProductSpace ContDiff SchwartzMap

/-- Pulling `conj` through the classical Fourier transform of a real-valued function turns it
into the inverse Fourier transform, pointwise. -/
private lemma fourier_conj_ofReal (φ : ℝ → ℝ) (ξ : ℝ) :
    conj (𝓕 (fun x => (φ x : ℂ)) ξ) = 𝓕⁻ (fun x => (φ x : ℂ)) ξ := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq, Real.fourier_real_eq,
    ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  dsimp only
  rw [Circle.smul_def, Circle.smul_def, smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal,
    ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]
  congr 1
  ring

/-- The abstract `L²` Fourier transform is self-adjoint: `⟪a, 𝓕 b⟫ = ⟪𝓕⁻ a, b⟫`. -/
private lemma Lp_inner_fourier_eq_inner_fourierInv (a b : Lp (α := ℝ) ℂ 2 volume) :
    ⟪a, (𝓕 b)⟫_ℂ = ⟪(𝓕⁻ a), b⟫_ℂ := by
  have ha : a = 𝓕 (𝓕⁻ a) := (fourier_fourierInv_eq a).symm
  nth_rewrite 1 [ha]
  exact Lp.inner_fourier_eq (𝓕⁻ a) b

/-- **Plancherel's theorem for the classical Fourier transform.**
For `f : ℝ → ℂ` that is both `Integrable` and `MemLp f 2`, the classical (pointwise-integral)
Fourier transform `𝓕 f` preserves the `L²` norm. -/
theorem plancherel_theorem_classical {f : ℝ → ℂ} (hf1 : Integrable f volume)
    (hf2 : MemLp f 2 volume) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  set F : Lp (α := ℝ) ℂ 2 volume := hf2.toLp f with hF
  set G : Lp (α := ℝ) ℂ 2 volume := 𝓕 F with hG
  have hFf : (F : ℝ → ℂ) =ᵐ[volume] f := hf2.coeFn_toLp
  -- Continuity/local integrability of the classical Fourier transform of `f`.
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf1
  have hloc1 : LocallyIntegrable (𝓕 f) volume := hcont.locallyIntegrable
  have hloc2 : LocallyIntegrable (G : ℝ → ℂ) volume :=
    (Lp.memLp G).locallyIntegrable (by norm_num)
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    show ⟪w, v⟫_ℝ = ⟪v, w⟫_ℝ
    exact real_inner_comm v w
  -- Key vanishing pairing against real compactly-supported smooth test functions.
  have key : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, φ x • (𝓕 f - (G : ℝ → ℂ)) x = 0 := by
    intro φ hφsmooth hφsupp
    have hφsupp' : HasCompactSupport (fun x => (φ x : ℂ)) :=
      hφsupp.comp_left (g := fun (t : ℝ) => (t : ℂ)) Complex.ofReal_zero
    have hφsmooth' : ContDiff ℝ (⊤ : ℕ∞) (fun x => (φ x : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hφsmooth
    set φS : 𝓢(ℝ, ℂ) := hφsupp'.toSchwartzMap hφsmooth' with hφS
    have hφSfun : (φS : ℝ → ℂ) = fun x => (φ x : ℂ) := rfl
    have hφInt : Integrable (fun x => (φ x : ℂ)) volume := hφSfun ▸ φS.integrable
    -- Classical multiplication formula.
    have hterm1 : ∫ ξ, (𝓕 f ξ) * (φ ξ : ℂ) ∂volume
        = ∫ x, f x * (𝓕 (fun x => (φ x : ℂ))) x ∂volume := by
      have hraw := VectorFourier.integral_bilin_fourierIntegral_eq_flip (V := ℝ) (W := ℝ)
        (E := ℂ) (F := ℂ) (G := ℂ) (μ := volume) (ν := volume) (L := innerₗ ℝ)
        (e := 𝐞) (ContinuousLinearMap.mul ℂ ℂ) Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hf1 hφInt
      rw [hflip] at hraw
      exact hraw
    -- Abstract-side identity via self-adjointness of the `L²` Fourier transform.
    have hterm2 : ∫ x, (φ x : ℂ) * (G : ℝ → ℂ) x ∂volume
        = ∫ x, f x * (𝓕 (fun x => (φ x : ℂ))) x ∂volume := by
      have hinner : ⟪φS.toLp 2 volume, G⟫_ℂ = ⟪𝓕⁻ (φS.toLp 2 volume), F⟫_ℂ :=
        Lp_inner_fourier_eq_inner_fourierInv (φS.toLp 2 volume) F
      have hlhs : ⟪φS.toLp 2 volume, G⟫_ℂ = ∫ x, (φ x : ℂ) * (G : ℝ → ℂ) x ∂volume := by
        rw [L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [φS.coeFn_toLp 2 volume] with x hx
        rw [RCLike.inner_apply', hx, hφSfun, Complex.conj_ofReal]
      have hFourierInv_eq : 𝓕⁻ (φS.toLp 2 volume) = (𝓕⁻ φS).toLp 2 volume :=
        SchwartzMap.toLp_fourierInv_eq φS
      have hrhs : ⟪𝓕⁻ (φS.toLp 2 volume), F⟫_ℂ
          = ∫ x, f x * (𝓕 (fun x => (φ x : ℂ))) x ∂volume := by
        rw [hFourierInv_eq, L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [(𝓕⁻ φS).coeFn_toLp 2 volume, hFf] with x hx hFfx
        rw [RCLike.inner_apply', hx]
        have hconjeq : conj ((𝓕⁻ φS) x) = 𝓕 (fun x => (φ x : ℂ)) x := by
          rw [SchwartzMap.fourierInv_coe, hφSfun, ← fourier_conj_ofReal φ x, Complex.conj_conj]
        rw [hconjeq, hFfx]
        ring
      rw [hlhs] at hinner
      rw [hinner, hrhs]
    have hI1 : Integrable (fun x => φ x • 𝓕 f x) volume :=
      hloc1.integrable_smul_left_of_hasCompactSupport hφsmooth.continuous hφsupp
    have hI2 : Integrable (fun x => φ x • (G : ℝ → ℂ) x) volume :=
      hloc2.integrable_smul_left_of_hasCompactSupport hφsmooth.continuous hφsupp
    have hstep : (fun x => φ x • (𝓕 f - (G : ℝ → ℂ)) x)
        = (fun x => φ x • 𝓕 f x) - (fun x => φ x • (G : ℝ → ℂ) x) := by
      funext x
      exact smul_sub (φ x) (𝓕 f x) ((G : ℝ → ℂ) x)
    calc ∫ x, φ x • (𝓕 f - (G : ℝ → ℂ)) x
        = (∫ x, φ x • 𝓕 f x) - ∫ x, φ x • (G : ℝ → ℂ) x := by
          rw [← integral_sub hI1 hI2]
          exact congrArg (∫ x, · x ∂volume) hstep
      _ = 0 := by
          simp only [Complex.real_smul]
          have hterm1' : ∫ x, (φ x : ℂ) * 𝓕 f x ∂volume
              = ∫ x, f x * (𝓕 (fun x => (φ x : ℂ))) x ∂volume := by
            rw [← hterm1]
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            ring
          rw [hterm1', ← hterm2]
          ring
  have hae0 : ∀ᵐ x ∂volume, (𝓕 f - (G : ℝ → ℂ)) x = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc1.sub hloc2) key
  have hae : 𝓕 f =ᵐ[volume] (G : ℝ → ℂ) := by
    filter_upwards [hae0] with x hx
    simpa [sub_eq_zero] using hx
  rw [eLpNorm_congr_ae hae]
  have hnorm : ‖G‖ = ‖F‖ := Lp.norm_fourier_eq F
  rw [Lp.norm_def, Lp.norm_def] at hnorm
  have h1 : eLpNorm (G : ℝ → ℂ) 2 volume ≠ ⊤ := (Lp.memLp G).2.ne
  have h2 : eLpNorm (F : ℝ → ℂ) 2 volume ≠ ⊤ := (Lp.memLp F).2.ne
  have h3 : eLpNorm (G : ℝ → ℂ) 2 volume = eLpNorm (F : ℝ → ℂ) 2 volume :=
    (ENNReal.toReal_eq_toReal_iff' h1 h2).mp hnorm
  rw [h3, eLpNorm_congr_ae hFf]

namespace QuantumMechanics

namespace OneDimension
namespace HarmonicOscillator
variable (Q : HarmonicOscillator)

/--
The topological closure of the span of the eigenfunctions of the harmonic oscillator is the
whole Hilbert space. This is the unconditional (hypothesis-free) form of
`eigenfunction_completeness`, obtained by discharging its Plancherel-theorem hypothesis with
`plancherel_theorem_classical`.
-/
theorem eigenfunction_completeness' :
    (Submodule.span ℂ
    (Set.range (fun n => HilbertSpace.mk (Q.eigenfunction_memHS n)))).topologicalClosure = ⊤ :=
  Q.eigenfunction_completeness (fun hf1 hf2 => plancherel_theorem_classical hf1 hf2)

end HarmonicOscillator
end OneDimension
end QuantumMechanics
