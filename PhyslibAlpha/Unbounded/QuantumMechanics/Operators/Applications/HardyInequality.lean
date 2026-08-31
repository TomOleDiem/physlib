/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!

# Hardy's inequality in `ℝ³`

## i. Overview

This file proves Hardy's inequality in three spatial dimensions: for a compactly-supported
`C¹` function `ψ : ℝ³ → ℂ`,
```
∫ ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 ≤ 4 * ∫ ‖fderiv ℝ ψ x‖ ^ 2.
```
This is Phase 2 of a Kato–Rellich-for-hydrogen project: combined with the (already proved)
Kato–Rellich theorem in `KatoRellich.lean`, Hardy's inequality is the analytic estimate that shows
the Coulomb potential `x ↦ -1/‖x‖` is relatively bounded (with relative bound `0`) with respect to
the free Hamiltonian `-Δ`, hence that the hydrogen Hamiltonian `-Δ - 1/‖x‖` is essentially
self-adjoint on (e.g.) `C_c^∞(ℝ³)`.

## ii. Overview of the proof

The classical proof proceeds via the divergence theorem applied to the vector field
`F(x) = ‖ψ x‖ ^ 2 • (x / ‖x‖ ^ 2)`. Writing `u := ‖ψ ·‖ ^ 2` and `V := invSqSmulId`
(`V(x) = (‖x‖ ^ 2)⁻¹ • x`), so that `F = u • V`:

1. `div V x = 1 / ‖x‖ ^ 2` for `x ≠ 0` — pure multivariable calculus, proved for real (via the
   trace of the Fréchet derivative and `LinearMap.trace_smulRight`) in `divergence_invSqSmulId`.
2. `(fderiv ℝ u x) (V x) = ⟪∇u(x), V(x)⟫`, bounded by Cauchy–Schwarz plus the chain rule for
   `‖·‖ ^ 2` on the inner-product space `ℂ`:
   `|(fderiv ℝ u x) (V x)| ≤ 2 * ‖ψ x‖ * ‖fderiv ℝ ψ x‖ / ‖x‖`,
   proved for real in `abs_fderiv_normSq_ψ_apply_invSqSmulId_le`.
3. Combining (1)–(2) via the product rule for divergence
   (`div (u • V) = u * div V + (fderiv u) (V ·)`) gives the pointwise inequality
   `u x / ‖x‖ ^ 2 ≤ div F x + 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖` for `x ≠ 0`, proved for real in
   `normSq_ψ_div_sq_le_divergence_add_two_mul`.
4. The genuinely hard analytic step, `integral_divergence_eq_zero_of_support_subset_ball`, is that
   `∫_{closedBall 0 R} div F = 0` once `R` is chosen so that `ψ` (and hence `F`) vanishes near the
   sphere `‖x‖ = R`. The obstruction is genuine: `F` itself is *unbounded* near the origin
   (`‖F x‖ = ‖ψ x‖ ^ 2 / ‖x‖ → ∞` unless `ψ 0 = 0`), so
   `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`'s "one exceptional point"
   dispensation — which only waives *differentiability*, not *continuity*, at the excluded point —
   does not apply directly to `F` on the closed ball. Rather than excising a literal ball around the
   origin and using the divergence theorem on an annulus (which would need spherical/annulus
   divergence machinery), this file instead multiplies `F` by a smooth radial cutoff `cutoffRadial ε`
   that is identically `0` near the origin (built from `Real.smoothTransition`): the field
   `cutoffRadial ε • F` is then genuinely `C¹` *everywhere* (no exceptional point at all), so the
   *plain* divergence theorem applies. That base fact —
   `integral_trace_fderiv_eq_zero_of_compactSupport`, "a globally `C¹`, compactly-supported vector
   field on `ℝ³` has zero total divergence" — is proved by transporting Mathlib's box-shaped
   divergence theorem (stated on `Fin 3 → ℝ`) across the linear identification `toFin3` with `ℝ³`.
   A product-rule decomposition and an elementary `O(ε)` bound (via `EuclideanSpace.volume_ball`-
   style volume formulas) on the resulting boundary-layer term, combined with dominated convergence,
   then gives the `ε → 0⁺` limit.
5. Downstream of (4), combining with (3) and integrating gives
   `I_R := ∫_{closedBall 0 R} u/‖x‖^2 ≤ 2 * ∫_{closedBall 0 R} (‖ψ‖/‖x‖) * ‖fderiv ℝ ψ‖`.
6. The right-hand side is controlled by the *pointwise* AM–GM inequality
   `2 a b ≤ (1/2) a ^ 2 + 2 b ^ 2` (rather than an `L²` Cauchy–Schwarz-for-integrals lemma, whose
   exact Mathlib name was the other flagged risk in this project — AM–GM sidesteps needing it
   entirely), giving `I_R ≤ (1/2) I_R + 2 J_R`, i.e. `I_R ≤ 4 J_R` where `J_R` is the gradient
   integral over the same ball.
7. Finally, `hcompact` lets us choose `R` large enough that `I_R = I` and `J_R = J` are the
   corresponding integrals over all of `ℝ³`, giving the theorem.

Local integrability of the singular integrand `‖ψ x‖ ^ 2 / ‖x‖ ^ 2` near the origin (needed to make
sense of / manipulate the integrals in (5)–(6)) is handled rigorously via
`MeasureTheory.integrableOn_ball_of_norm_le_rpow`, since `2 < finrank ℝ ℝ³ = 3`.

## iii. Key results

- `divergence_invSqSmulId` : `div (x / ‖x‖ ^ 2) = 1 / ‖x‖ ^ 2` for `x ≠ 0` (proved).
- `normSq_ψ_div_sq_le_divergence_add_two_mul` : the pointwise divergence inequality (proved).
- `integral_trace_fderiv_eq_zero_of_compactSupport` : a globally `C¹`, compactly-supported vector
  field on `ℝ³` has zero total divergence (proved, via Mathlib's box divergence theorem).
- `integral_divergence_eq_zero_of_support_subset_ball` : the integration-by-parts step,
  `∫_{closedBall 0 R} div (hardyField ψ) = 0` (proved, via a smooth radial cutoff and `ε → 0⁺`).
- `hardy_inequality_R3` : Hardy's inequality in `ℝ³`,
  `∫ ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 ≤ 4 * ∫ ‖fderiv ℝ ψ x‖ ^ 2`, for `ψ` compactly-supported `C¹` (proved).

## iv. Table of contents

- A. The radial vector field `x / ‖x‖ ^ 2` and its divergence
- B. The gradient of `‖ψ ·‖ ^ 2` and its bound
- C. The pointwise divergence inequality
- D. The integration-by-parts step, via a smooth radial cutoff and the box divergence theorem
- E. Assembling Hardy's inequality

## v. References

- Standard textbook derivation, e.g. E. H. Lieb and M. Loss, *Analysis*, Theorem 5.11 (Hardy's
  inequality in `ℝⁿ`, `n ≥ 3`).

-/

@[expose] public section

/-- The ambient space for Hardy's inequality: physical three-dimensional Euclidean space. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable section

open MeasureTheory Metric Set

/-!
## A. The radial vector field `x / ‖x‖ ^ 2` and its divergence
-/

/-- The radial vector field `V(x) = x / ‖x‖ ^ 2`, as an unbundled function `ℝ³ → ℝ³`. -/
def invSqSmulId (x : ℝ³) : ℝ³ := (‖x‖ ^ 2)⁻¹ • x

/-- The Fréchet derivative of `t ↦ (‖t‖ ^ 2)⁻¹` at a nonzero point `x`. -/
lemma hasFDerivAt_invSq (x : ℝ³) (hx : x ≠ 0) :
    HasFDerivAt (fun y : ℝ³ => (‖y‖ ^ 2)⁻¹)
      ((-((‖x‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ x)) x := by
  have hne : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hnormSq : HasFDerivAt (fun y : ℝ³ => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hinv : HasDerivAt (fun t : ℝ => t⁻¹) (-((‖x‖ ^ 2) ^ 2)⁻¹) (‖x‖ ^ 2) :=
    hasDerivAt_inv hne
  have heq : (fun y : ℝ³ => (‖y‖ ^ 2)⁻¹) = (fun t : ℝ => t⁻¹) ∘ fun y : ℝ³ => ‖y‖ ^ 2 := rfl
  rw [heq]
  exact hinv.comp_hasFDerivAt x hnormSq

/-- The Fréchet derivative of the radial vector field `V(x) = x / ‖x‖ ^ 2` at a nonzero point. -/
lemma hasFDerivAt_invSqSmulId (x : ℝ³) (hx : x ≠ 0) :
    HasFDerivAt invSqSmulId
      ((‖x‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ³ +
        ((-((‖x‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ x)).smulRight x) x :=
  (hasFDerivAt_invSq x hx).smul (hasFDerivAt_id x)

/-- The divergence of the radial vector field `V(x) = x / ‖x‖ ^ 2` at a nonzero point equals
`1 / ‖x‖ ^ 2`: the key elementary multivariable-calculus computation
`div (x / ‖x‖ ^ 2) = 3 / ‖x‖ ^ 2 - 2 ‖x‖ ^ 2 / ‖x‖ ^ 4 = 1 / ‖x‖ ^ 2` in `ℝ³`. -/
theorem divergence_invSqSmulId (x : ℝ³) (hx : x ≠ 0) :
    LinearMap.trace ℝ ℝ³ ((fderiv ℝ invSqSmulId x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) =
      (‖x‖ ^ 2)⁻¹ := by
  have hderiv := hasFDerivAt_invSqSmulId x hx
  rw [hderiv.fderiv]
  have hne : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have htrace : LinearMap.trace ℝ ℝ³
      (((‖x‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ³ +
        ((-((‖x‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ x)).smulRight x :
          ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) =
      (‖x‖ ^ 2)⁻¹ * LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.id ℝ ℝ³ : ℝ³ →ₗ[ℝ] ℝ³) +
        (((-((‖x‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ x) : ℝ³ →L[ℝ] ℝ)) x := by
    rw [ContinuousLinearMap.toLinearMap_add, map_add, ContinuousLinearMap.toLinearMap_smul, map_smul,
      smul_eq_mul]
    congr 1
    exact LinearMap.trace_smulRight
      (((-((‖x‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ x) : ℝ³ →L[ℝ] ℝ) : ℝ³ →ₗ[ℝ] ℝ) x
  rw [htrace]
  have hid : LinearMap.trace ℝ ℝ³ (ContinuousLinearMap.id ℝ ℝ³ : ℝ³ →ₗ[ℝ] ℝ³) =
      (Module.finrank ℝ ℝ³ : ℝ) := LinearMap.trace_id ..
  rw [hid, finrank_euclideanSpace_fin]
  have happly : (((-((‖x‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ x) : ℝ³ →L[ℝ] ℝ)) x =
      (-((‖x‖ ^ 2) ^ 2)⁻¹) * (2 * ‖x‖ ^ 2) := by
    simp [innerSL_apply_apply, two_mul, mul_add]
  rw [happly]
  field_simp
  ring

/-!
## B. The gradient of `‖ψ ·‖ ^ 2` and its bound
-/

variable {ψ : ℝ³ → ℂ}

/-- The Fréchet derivative of `u := ‖ψ ·‖ ^ 2 : ℝ³ → ℝ` at `x`, in terms of the (real) inner
product on `ℂ` and the Fréchet derivative of `ψ`. -/
lemma hasFDerivAt_normSq_ψ {x : ℝ³} (hψx : HasFDerivAt ψ (fderiv ℝ ψ x) x) :
    HasFDerivAt (‖ψ ·‖ ^ 2) (2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) x :=
  hψx.norm_sq

/-- Cauchy–Schwarz bound on the directional derivative of `u := ‖ψ ·‖ ^ 2` along the radial
vector field `V(x) = x / ‖x‖ ^ 2`:
`|(fderiv ℝ u x) (V x)| ≤ 2 * ‖ψ x‖ * ‖fderiv ℝ ψ x‖ / ‖x‖`. -/
theorem abs_fderiv_normSq_ψ_apply_invSqSmulId_le
    {x : ℝ³} (hx : x ≠ 0) :
    |(2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x)|
      ≤ 2 * ‖ψ x‖ * ‖fderiv ℝ ψ x‖ / ‖x‖ := by
  have hVx : ‖invSqSmulId x‖ = (‖x‖)⁻¹ := by
    have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    rw [invSqSmulId, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (‖x‖ ^ 2)⁻¹),
      pow_two, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hnx, mul_one]
  calc |(2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x)|
      = ‖(2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x)‖ := by
        rw [Real.norm_eq_abs]
    _ ≤ 2 * (‖(innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)‖ * ‖invSqSmulId x‖) := by
        rw [smul_apply, two_nsmul]
        calc
          ‖((innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x) +
              ((innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x)‖
              ≤ ‖((innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x)‖ +
                ‖((innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x)‖ := norm_add_le _ _
          _ = 2 * ‖((innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x)‖ := by ring
          _ ≤ 2 * (‖(innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)‖ * ‖invSqSmulId x‖) := by
            gcongr
            exact ContinuousLinearMap.le_opNorm ((innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x))
              (invSqSmulId x)
    _ ≤ 2 * ((‖ψ x‖ * ‖fderiv ℝ ψ x‖) * ‖invSqSmulId x‖) := by
        gcongr
        refine ((innerSL ℝ (ψ x)).opNorm_comp_le (fderiv ℝ ψ x)).trans ?_
        gcongr
        exact (innerSL_apply_norm ℝ (ψ x)).le
    _ = 2 * ‖ψ x‖ * ‖fderiv ℝ ψ x‖ / ‖x‖ := by rw [hVx]; ring

/-!
## C. The pointwise divergence inequality
-/

/-- The vector field `F(x) = ‖ψ x‖ ^ 2 • (x / ‖x‖ ^ 2)` whose divergence, integrated over a ball
containing the support of `ψ`, gives Hardy's inequality via the divergence theorem. -/
def hardyField (ψ : ℝ³ → ℂ) (x : ℝ³) : ℝ³ := ‖ψ x‖ ^ 2 • invSqSmulId x

/-- The Fréchet derivative of `F = u • V` at a nonzero point, via the product rule. -/
lemma hasFDerivAt_hardyField {x : ℝ³} (hx : x ≠ 0) (hψx : HasFDerivAt ψ (fderiv ℝ ψ x) x) :
    HasFDerivAt (hardyField ψ)
      (‖ψ x‖ ^ 2 • ((‖x‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ³ +
          ((-((‖x‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ x)).smulRight x) +
        (2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)).smulRight (invSqSmulId x)) x :=
  (hasFDerivAt_normSq_ψ hψx).smul (hasFDerivAt_invSqSmulId x hx)

/-- The trace (divergence) of `F = u • V` at a nonzero point decomposes as
`div F x = u x * div V x + (fderiv ℝ u x) (V x)`, the product rule for divergence. -/
theorem divergence_hardyField {x : ℝ³} (hx : x ≠ 0) (hψx : HasFDerivAt ψ (fderiv ℝ ψ x) x) :
    LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) =
      ‖ψ x‖ ^ 2 * (‖x‖ ^ 2)⁻¹ +
        (2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x) := by
  rw [(hasFDerivAt_hardyField hx hψx).fderiv]
  have hV : LinearMap.trace ℝ ℝ³
      (((‖x‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ³ +
        ((-((‖x‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ x)).smulRight x :
          ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) = (‖x‖ ^ 2)⁻¹ := by
    rw [← (hasFDerivAt_invSqSmulId x hx).fderiv]; exact divergence_invSqSmulId x hx
  rw [ContinuousLinearMap.toLinearMap_add, map_add, ContinuousLinearMap.toLinearMap_smul, map_smul,
    smul_eq_mul, hV]
  congr 1
  exact LinearMap.trace_smulRight
    (((2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) : ℝ³ →L[ℝ] ℝ) : ℝ³ →ₗ[ℝ] ℝ) (invSqSmulId x)

/-- The key pointwise inequality: `‖ψ x‖ ^ 2 / ‖x‖ ^ 2 ≤ div F x + 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖`
for `x ≠ 0`. Integrating this over a ball and using
`integral_divergence_eq_zero_of_support_subset_ball` gives Hardy's inequality. -/
theorem normSq_ψ_div_sq_le_divergence_add_two_mul
    {x : ℝ³} (hx : x ≠ 0) (hψx : HasFDerivAt ψ (fderiv ℝ ψ x) x) :
    ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 ≤
      LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) +
        2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖ := by
  rw [divergence_hardyField hx hψx, div_eq_mul_inv]
  have hbound := neg_abs_le ((2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x))
  have hb : -(2 * ‖ψ x‖ * ‖fderiv ℝ ψ x‖ / ‖x‖) ≤
      (2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x) :=
    le_trans (neg_le_neg (abs_fderiv_normSq_ψ_apply_invSqSmulId_le hx)) hbound
  have heq : 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖ = 2 * ‖ψ x‖ * ‖fderiv ℝ ψ x‖ / ‖x‖ := by ring
  linarith [hb, heq]

/-!
## D. The integration-by-parts step

The strategy is a smooth radial cutoff: rather than excising a literal ball around the origin
and applying the divergence theorem on an annulus (which would need spherical/annulus divergence
machinery this project does not have), we multiply `hardyField ψ` by a smooth cutoff `χ_ε` that is
identically `0` near the origin. The resulting field `χ_ε • hardyField ψ` is genuinely `C¹`
*everywhere* (no exceptional point at all), so the *plain* divergence theorem applies with no
continuity issue. Letting `ε → 0⁺` recovers the original integral.
-/

/-- The one-variable smooth cutoff profile: `0` for `t ≤ 1`, `1` for `t ≥ 2`, built from
`Real.smoothTransition`. -/
private noncomputable def chiCutoff (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

private lemma chiCutoff_contDiff {n : ℕ∞} : ContDiff ℝ n chiCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

private lemma chiCutoff_eq_zero {t : ℝ} (ht : t ≤ 1) : chiCutoff t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private lemma chiCutoff_eq_one {t : ℝ} (ht : 2 ≤ t) : chiCutoff t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private lemma chiCutoff_nonneg (t : ℝ) : 0 ≤ chiCutoff t := Real.smoothTransition.nonneg _

private lemma chiCutoff_le_one (t : ℝ) : chiCutoff t ≤ 1 := Real.smoothTransition.le_one _

/-- `chiCutoff` has derivative `0` at any `t < 1` (it is locally constant `0` there). -/
private lemma chiCutoff_hasDerivAt_zero_of_lt_one {t : ℝ} (ht : t < 1) :
    HasDerivAt chiCutoff 0 t := by
  refine (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_Iio (a := (1:ℝ))).mem_nhds ht] with y hy
  exact chiCutoff_eq_zero hy.le

/-- `chiCutoff` has derivative `0` at any `t > 2` (it is locally constant `1` there). -/
private lemma chiCutoff_hasDerivAt_zero_of_gt_two {t : ℝ} (ht : 2 < t) :
    HasDerivAt chiCutoff 0 t := by
  refine (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_Ioi (a := (2:ℝ))).mem_nhds ht] with y hy
  exact chiCutoff_eq_one hy.le

/-- A uniform bound on `|deriv chiCutoff|`, coming from continuity of `deriv chiCutoff` (since
`chiCutoff` is `C¹`) together with `deriv chiCutoff` vanishing outside the compact set `[1, 2]`. -/
private lemma chiCutoff_deriv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |deriv chiCutoff t| ≤ M := by
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn (isCompact_Icc (a := (1:ℝ)) (b := 2))
    (chiCutoff_contDiff (n := 1)).continuous_deriv_one.continuousOn
  have hM0 : (0:ℝ) ≤ M := le_trans (norm_nonneg _) (hM 1 (by norm_num))
  refine ⟨M, hM0, fun t => ?_⟩
  rcases lt_trichotomy t 1 with ht | ht | ht
  · rw [(chiCutoff_hasDerivAt_zero_of_lt_one ht).deriv, abs_zero]; exact hM0
  · rw [ht, ← Real.norm_eq_abs]; exact hM 1 (by norm_num)
  · rcases le_or_gt t 2 with ht2 | ht2
    · rw [← Real.norm_eq_abs]; exact hM t ⟨ht.le, ht2⟩
    · rw [(chiCutoff_hasDerivAt_zero_of_gt_two ht2).deriv, abs_zero]; exact hM0

/-- The radial cutoff `χ_ε(x) = chiCutoff (‖x‖ / ε)`: identically `0` on `ball 0 ε`, identically
`1` outside `closedBall 0 (2 * ε)`, valued in `[0, 1]`, and `C¹` on all of `ℝ³` (including at the
origin, where it is locally constant `0`). -/
private noncomputable def cutoffRadial (ε : ℝ) (x : ℝ³) : ℝ := chiCutoff (‖x‖ / ε)

private lemma cutoffRadial_eq_zero_of_lt {ε : ℝ} (hε : 0 < ε) {x : ℝ³} (hx : ‖x‖ < ε) :
    cutoffRadial ε x = 0 :=
  chiCutoff_eq_zero (by rw [div_le_one hε]; linarith)

private lemma cutoffRadial_eq_one_of_le {ε : ℝ} (hε : 0 < ε) {x : ℝ³} (hx : 2 * ε ≤ ‖x‖) :
    cutoffRadial ε x = 1 :=
  chiCutoff_eq_one (by rw [le_div_iff₀ hε]; linarith)

private lemma cutoffRadial_nonneg (ε : ℝ) (x : ℝ³) : 0 ≤ cutoffRadial ε x := chiCutoff_nonneg _

private lemma cutoffRadial_le_one (ε : ℝ) (x : ℝ³) : cutoffRadial ε x ≤ 1 := chiCutoff_le_one _

/-- `cutoffRadial ε` is `C¹` at every `x ≠ 0`: away from the origin `‖·‖` is `C¹`, and `chiCutoff`
is `C¹` everywhere, so the composition is `C¹` by the chain rule. -/
private lemma contDiffAt_cutoffRadial_of_ne {ε : ℝ} (_hε : 0 < ε) {x : ℝ³} (hx : x ≠ 0) :
    ContDiffAt ℝ 1 (cutoffRadial ε) x :=
  (chiCutoff_contDiff (n := 1)).contDiffAt.comp x ((contDiffAt_norm (𝕜 := ℝ) hx).div_const ε)

/-- `cutoffRadial ε` is `C¹` at `x = 0`: it is locally constant `0` on the open ball `ball 0 ε`. -/
private lemma contDiffAt_cutoffRadial_zero {ε : ℝ} (hε : 0 < ε) :
    ContDiffAt ℝ 1 (cutoffRadial ε) (0 : ℝ³) := by
  have hev : cutoffRadial ε =ᶠ[nhds (0 : ℝ³)] (fun _ => (0 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ³) hε] with y hy
    exact cutoffRadial_eq_zero_of_lt hε (mem_ball_zero_iff.mp hy)
  exact (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq hev

/-- `cutoffRadial ε` is `C¹` on all of `ℝ³`. -/
private lemma contDiff_cutoffRadial {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (cutoffRadial ε) :=
  contDiff_iff_contDiffAt.mpr fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · exact contDiffAt_cutoffRadial_zero hε
    · exact contDiffAt_cutoffRadial_of_ne hε hx

/-- The Fréchet derivative of `cutoffRadial ε` at a nonzero point, via the chain rule (the
derivative of `‖·‖` at `x` is left as the unspecified continuous linear functional
`fderiv ℝ (‖·‖) x`; its magnitude is bounded below via `norm_fderiv_le_of_lipschitz`, without
needing an explicit formula). -/
private lemma hasFDerivAt_cutoffRadial_of_ne {ε : ℝ} (_hε : 0 < ε) {x : ℝ³} (hx : x ≠ 0) :
    HasFDerivAt (cutoffRadial ε)
      ((deriv chiCutoff (‖x‖ / ε)) • (ε⁻¹ • fderiv ℝ (fun y : ℝ³ => ‖y‖) x)) x := by
  have hnorm : HasFDerivAt (fun y : ℝ³ => ‖y‖) (fderiv ℝ (fun y : ℝ³ => ‖y‖) x) x :=
    ((contDiffAt_norm (𝕜 := ℝ) hx).differentiableAt one_ne_zero).hasFDerivAt
  have hg : HasFDerivAt (fun y : ℝ³ => ‖y‖ / ε)
      (ε⁻¹ • fderiv ℝ (fun y : ℝ³ => ‖y‖) x) x := by
    have h2 := hnorm.const_smul ε⁻¹
    have heq2 : (ε⁻¹ • fun y : ℝ³ => ‖y‖) = fun y : ℝ³ => ‖y‖ / ε := by
      funext y; simp [div_eq_mul_inv, mul_comm]
    rwa [heq2] at h2
  have hc : HasDerivAt chiCutoff (deriv chiCutoff (‖x‖ / ε)) (‖x‖ / ε) :=
    ((chiCutoff_contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
  have heq : cutoffRadial ε = chiCutoff ∘ fun y : ℝ³ => ‖y‖ / ε := rfl
  rw [heq]
  exact hc.comp_hasFDerivAt x hg

/-- Uniform bound `‖fderiv ℝ (cutoffRadial ε) x‖ ≤ M / ε` for all `x` (including `x = 0`, where the
derivative is `0`), where `M` is the bound on `|deriv chiCutoff|` from `chiCutoff_deriv_bound`. -/
private lemma norm_fderiv_cutoffRadial_le {ε : ℝ} (hε : 0 < ε) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ t : ℝ, |deriv chiCutoff t| ≤ M) (x : ℝ³) :
    ‖fderiv ℝ (cutoffRadial ε) x‖ ≤ M / ε := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hzero : fderiv ℝ (cutoffRadial ε) (0:ℝ³) = 0 := by
      have hev : cutoffRadial ε =ᶠ[nhds (0:ℝ³)] (fun _ => (0:ℝ)) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ³) hε] with y hy
        exact cutoffRadial_eq_zero_of_lt hε (mem_ball_zero_iff.mp hy)
      rw [hev.fderiv_eq]
      simp
    rw [hzero, norm_zero]
    positivity
  · rw [(hasFDerivAt_cutoffRadial_of_ne hε hx).fderiv]
    have hnormle : ‖fderiv ℝ (fun y : ℝ³ => ‖y‖) x‖ ≤ 1 := by
      simpa using norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_one_norm (E := ℝ³))
    calc ‖(deriv chiCutoff (‖x‖ / ε)) • (ε⁻¹ • fderiv ℝ (fun y : ℝ³ => ‖y‖) x)‖
        = |deriv chiCutoff (‖x‖ / ε)| * (ε⁻¹ * ‖fderiv ℝ (fun y : ℝ³ => ‖y‖) x‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hε)]
      _ ≤ M * (ε⁻¹ * 1) := by
          gcongr
          exact hM _
      _ = M / ε := by ring

/-- `cutoffRadial ε` has vanishing derivative on `ball 0 ε` (locally constant `0` there). -/
private lemma fderiv_cutoffRadial_eq_zero_of_lt {ε : ℝ} (hε : 0 < ε) {x : ℝ³} (hx : ‖x‖ < ε) :
    fderiv ℝ (cutoffRadial ε) x = 0 := by
  have hev : cutoffRadial ε =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [(isOpen_ball).mem_nhds (mem_ball_zero_iff.mpr hx)] with y hy
    exact cutoffRadial_eq_zero_of_lt hε (mem_ball_zero_iff.mp hy)
  rw [hev.fderiv_eq]; simp

/-- `cutoffRadial ε` has vanishing derivative outside `closedBall 0 (2 * ε)` (locally constant `1`
there). -/
private lemma fderiv_cutoffRadial_eq_zero_of_gt {ε : ℝ} (hε : 0 < ε) {x : ℝ³} (hx : 2 * ε < ‖x‖) :
    fderiv ℝ (cutoffRadial ε) x = 0 := by
  have hopen : IsOpen {y : ℝ³ | 2 * ε < ‖y‖} := isOpen_lt continuous_const continuous_norm
  have hev : cutoffRadial ε =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact cutoffRadial_eq_one_of_le hε hy.le
  rw [hev.fderiv_eq]; simp

/-- The pointwise product rule for the divergence of `cutoffRadial ε • hardyField ψ`, at a nonzero
point (where both factors are genuinely differentiable in the ordinary sense). -/
private lemma divergence_cutoffRadial_smul_hardyField {ε : ℝ} (hε : 0 < ε) {x : ℝ³} (hx : x ≠ 0)
    (hψx : HasFDerivAt ψ (fderiv ℝ ψ x) x) :
    LinearMap.trace ℝ ℝ³
      ((fderiv ℝ (fun y => cutoffRadial ε y • hardyField ψ y) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) =
      cutoffRadial ε x *
        LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) +
      (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x) := by
  have hcut := hasFDerivAt_cutoffRadial_of_ne hε hx
  have hF := hasFDerivAt_hardyField hx hψx
  have hG := hcut.smul hF
  have hGeq : (fun y => cutoffRadial ε y • hardyField ψ y) = cutoffRadial ε • hardyField ψ := rfl
  rw [hGeq, hG.fderiv]
  have hV : LinearMap.trace ℝ ℝ³
      ((cutoffRadial ε x •
        (‖ψ x‖ ^ 2 • ((‖x‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ ℝ³ +
            ((-((‖x‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ x)).smulRight x) +
          (2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)).smulRight (invSqSmulId x)) :
          ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) =
      cutoffRadial ε x * LinearMap.trace ℝ ℝ³
        ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) := by
    rw [ContinuousLinearMap.toLinearMap_smul, map_smul, smul_eq_mul]
    congr 1
    rw [hF.fderiv]
  rw [ContinuousLinearMap.toLinearMap_add, map_add, hV, hcut.fderiv]
  congr 1
  exact LinearMap.trace_smulRight
    (((deriv chiCutoff (‖x‖ / ε)) • (ε⁻¹ • fderiv ℝ (fun y : ℝ³ => ‖y‖) x) : ℝ³ →L[ℝ] ℝ)
      : ℝ³ →ₗ[ℝ] ℝ) (hardyField ψ x)

/-- `invSqSmulId` is `C¹` at every nonzero point. -/
private lemma contDiffAt_invSqSmulId_of_ne {x : ℝ³} (hx : x ≠ 0) : ContDiffAt ℝ 1 invSqSmulId x :=
  (((contDiffAt_id (n := 1)).norm_sq ℝ).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).smul
    contDiffAt_id

/-- `hardyField ψ` is `C¹` at every nonzero point, given `ψ` is `C¹`. -/
private lemma contDiffAt_hardyField_of_ne (hψ : ContDiff ℝ 1 ψ) {x : ℝ³} (hx : x ≠ 0) :
    ContDiffAt ℝ 1 (hardyField ψ) x :=
  (hψ.contDiffAt.norm_sq ℂ).smul (contDiffAt_invSqSmulId_of_ne hx)

/-- `cutoffRadial ε • hardyField ψ` is `C¹` on all of `ℝ³`: locally constant `0` on `ball 0 ε`
(including at the origin, where `hardyField ψ` need not even be continuous), and a product of `C¹`
factors away from the origin. -/
private lemma contDiff_hardyFieldCutoff (hψ : ContDiff ℝ 1 ψ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (fun x => cutoffRadial ε x • hardyField ψ x) :=
  contDiff_iff_contDiffAt.mpr fun x => by
    rcases eq_or_ne x 0 with rfl | hx
    · have hev : (fun y => cutoffRadial ε y • hardyField ψ y) =ᶠ[nhds (0 : ℝ³)]
          (fun _ => (0 : ℝ³)) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ³) hε] with y hy
        rw [cutoffRadial_eq_zero_of_lt hε (mem_ball_zero_iff.mp hy), zero_smul]
      exact (contDiffAt_const (c := (0 : ℝ³))).congr_of_eventuallyEq hev
    · exact (contDiffAt_cutoffRadial_of_ne hε hx).smul (contDiffAt_hardyField_of_ne hψ hx)

/-- The (transported) support of `cutoffRadial ε • hardyField ψ` is contained in that of `ψ`: the
cutoff cannot enlarge the support, and `hardyField ψ x = 0` whenever `ψ x = 0`. -/
private lemma tsupport_hardyFieldCutoff_subset {ε : ℝ} :
    tsupport (fun x => cutoffRadial ε x • hardyField ψ x) ⊆ tsupport ψ := by
  have hsub : Function.support (fun x => cutoffRadial ε x • hardyField ψ x) ⊆ Function.support ψ := by
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hψx
    exact hx (by simp [hardyField, hψx])
  exact closure_mono hsub

/-- The (measure-preserving, continuous, linear) identification of `ℝ³` with `Fin 3 → ℝ`, used to
transport `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable` (stated for
`Fin (n + 1) → ℝ`) to `ℝ³ = EuclideanSpace ℝ (Fin 3)`. -/
private noncomputable def toFin3 : ℝ³ ≃L[ℝ] (Fin 3 → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toContinuousLinearEquiv

private lemma measurePreserving_toFin3 :
    MeasurePreserving (toFin3 : ℝ³ → Fin 3 → ℝ) volume volume :=
  PiLp.volume_preserving_ofLp (Fin 3)

private lemma measurePreserving_toFin3_symm :
    MeasurePreserving (toFin3.symm : (Fin 3 → ℝ) → ℝ³) volume volume :=
  PiLp.volume_preserving_toLp (Fin 3)

/-- **Base fact for the divergence theorem.** A globally `C¹`, compactly-supported vector field on
`ℝ³` has zero total divergence. Unlike `hardyField ψ`, such a field has no singularity anywhere, so
the *plain* divergence theorem applies (no exceptional points needed). The proof transports
Mathlib's box-shaped divergence theorem `integral_divergence_of_hasFDerivAt_off_countable`
(stated on `Fin 3 → ℝ`) across the identification `toFin3`, using:
* the chain rule to relate `fderiv` of the transported field `H` to `fderiv G`;
* conjugation-invariance of trace (`LinearMap.trace_conj'`) to relate `div H` to `div G`;
* a box strictly containing the (compact) image of `tsupport G`, so `H` vanishes identically on
  every face of the box, killing all boundary terms;
* `measurePreserving_toFin3(_symm)` to transport the integral itself. -/
private lemma integral_trace_fderiv_eq_zero_of_compactSupport
    {G : ℝ³ → ℝ³} (hG : ContDiff ℝ 1 G) {R : ℝ} (hR : 0 < R)
    (hGsupp : tsupport G ⊆ ball (0 : ℝ³) R) :
    ∫ x, LinearMap.trace ℝ ℝ³ ((fderiv ℝ G x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)
      ∂(volume : Measure ℝ³) = 0 := by
  set H : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => toFin3 (G (toFin3.symm y)) with hHdef
  have hGdiff : Differentiable ℝ G := hG.differentiable one_ne_zero
  -- The Fréchet derivative of `H`, via the chain rule.
  have hHderiv : ∀ y, HasFDerivAt H (toFin3.toContinuousLinearMap.comp
      ((fderiv ℝ G (toFin3.symm y)).comp toFin3.symm.toContinuousLinearMap)) y := fun y =>
    toFin3.hasFDerivAt.comp y ((hGdiff (toFin3.symm y)).hasFDerivAt.comp y toFin3.symm.hasFDerivAt)
  -- `div H (y) = div G (toFin3.symm y)`, via conjugation-invariance of trace.
  have htrace : ∀ y, LinearMap.trace ℝ (Fin 3 → ℝ)
      ((fderiv ℝ H y : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) =
      LinearMap.trace ℝ ℝ³ ((fderiv ℝ G (toFin3.symm y) : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) := by
    intro y
    rw [(hHderiv y).fderiv]
    have heq : ((toFin3.toContinuousLinearMap.comp
        ((fderiv ℝ G (toFin3.symm y)).comp toFin3.symm.toContinuousLinearMap) :
          (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) =
        toFin3.toLinearEquiv.conj
          ((fderiv ℝ G (toFin3.symm y) : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) := by
      ext v; simp [LinearEquiv.conj_apply, ContinuousLinearEquiv.coe_toLinearEquiv]
    rw [heq, LinearMap.trace_conj']
  -- The trace of `fderiv H y` in the "sum of diagonal entries" form used by the box theorem.
  have hdiv_eq : ∀ y, ∑ i, (fderiv ℝ H y) (Pi.single i 1) i =
      LinearMap.trace ℝ ℝ³ ((fderiv ℝ G (toFin3.symm y) : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) := by
    intro y
    rw [← htrace y, LinearMap.trace_eq_matrix_trace ℝ (Pi.basisFun ℝ (Fin 3))]
    simp [Matrix.trace]
  -- `H` is `C¹`, hence globally differentiable with continuous derivative.
  have hHcontDiff : ContDiff ℝ 1 H := toFin3.contDiff.comp (hG.comp toFin3.symm.contDiff)
  have hHcont : Continuous H := hHcontDiff.continuous
  have hfderivCont : Continuous (fderiv ℝ H) := hHcontDiff.continuous_fderiv one_ne_zero
  have hHdiv_cont : Continuous (fun y => ∑ i, (fderiv ℝ H y) (Pi.single i 1) i) :=
    continuous_finsetSum Finset.univ fun i _ =>
      (continuous_apply i).comp (hfderivCont.clm_apply continuous_const)
  -- A box `Icc a b` strictly containing the (compact) image of `tsupport G`.
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ³) R).image toFin3.continuous).isBounded.subset_closedBall
    (0 : Fin 3 → ℝ)
  have hCbound : ∀ x ∈ closedBall (0 : ℝ³) R, ∀ i, |(toFin3 x) i| ≤ C := fun x hx i =>
    (norm_le_pi_norm (toFin3 x) i).trans (mem_closedBall_zero_iff.mp (hC ⟨x, hx, rfl⟩))
  set a : Fin 3 → ℝ := fun _ => -(C + 1) with hadef
  set b : Fin 3 → ℝ := fun _ => C + 1 with hbdef
  have hCnn : (0:ℝ) ≤ C := (abs_nonneg _).trans (hCbound 0 (mem_closedBall_self hR.le) 0)
  have hab : a ≤ b := fun i => by simp [hadef, hbdef]; linarith
  -- `H` vanishes at every point with some coordinate exceeding `C` in absolute value, since such a
  -- point cannot lie in the (transported) support of `G`.
  have hHzero_open : ∀ z : Fin 3 → ℝ, (∃ i, C < |z i|) → H z = 0 := by
    rintro z ⟨i, hi⟩
    have hznotsupp : z ∉ tsupport H := by
      intro hzmem
      have : z ∈ toFin3 '' (tsupport G) := by
        have hHsupp : tsupport H = toFin3 '' (tsupport G) := by
          have hHeq : Function.support H = toFin3 '' (Function.support G) := by
            ext y
            simp only [Function.mem_support, hHdef, ne_eq, map_eq_zero_iff _
              toFin3.injective, Set.mem_image]
            constructor
            · intro hy; exact ⟨toFin3.symm y, hy, by simp⟩
            · rintro ⟨x, hx, rfl⟩; simpa using hx
          rw [tsupport, hHeq, tsupport]
          exact (toFin3.toHomeomorph.image_closure (Function.support G)).symm
        rwa [hHsupp] at hzmem
      obtain ⟨x, hxsupp, hxz⟩ := this
      have hxR : x ∈ closedBall (0:ℝ³) R := ball_subset_closedBall (hGsupp hxsupp)
      have := hCbound x hxR i
      rw [hxz] at this
      linarith
    exact image_eq_zero_of_notMem_tsupport hznotsupp
  -- Consequently `fderiv H` vanishes wherever some coordinate exceeds `C`: `H` is locally constant
  -- `0` there (the set of such points is open).
  have hfderiv_zero_open : ∀ y : Fin 3 → ℝ, (∃ i, C < |y i|) → fderiv ℝ H y = 0 := by
    rintro y ⟨i, hi⟩
    have hopen : IsOpen {z : Fin 3 → ℝ | C < |z i|} :=
      isOpen_lt continuous_const ((continuous_apply i).abs)
    have hev : H =ᶠ[nhds y] (fun _ => (0 : Fin 3 → ℝ)) := by
      filter_upwards [hopen.mem_nhds hi] with w hw
      exact hHzero_open w ⟨i, hw⟩
    rw [hev.fderiv_eq]; simp
  -- The two boundary faces of the box vanish identically.
  have hface : ∀ (i : Fin 3) (v : ℝ) (hv : |v| = C + 1) (x : Fin 2 → ℝ),
      H (i.insertNth v x) i = 0 := fun i v hv x => by
    rw [hHzero_open (i.insertNth v x)
      ⟨i, by rw [Fin.insertNth_apply_same, hv]; linarith⟩, Pi.zero_apply]
  -- The divergence integral over the box vanishes: apply the box divergence theorem with an empty
  -- exceptional set (there is no singularity at all).
  have habs_b : ∀ i : Fin 3, |b i| = C + 1 := fun i => by
    simp only [hbdef]; exact abs_of_nonneg (by linarith)
  have habs_a : ∀ i : Fin 3, |a i| = C + 1 := fun i => by
    simp only [hadef]; rw [abs_neg]; exact abs_of_nonneg (by linarith)
  have hbox : ∫ y in Set.Icc a b, ∑ i, (fderiv ℝ H y) (Pi.single i 1) i = 0 := by
    have hthm := integral_divergence_of_hasFDerivAt_off_countable a b hab H (fun y => fderiv ℝ H y)
      ∅ Set.countable_empty hHcont.continuousOn
      (fun x _ => by rw [(hHderiv x).fderiv]; exact hHderiv x)
      (hHdiv_cont.continuousOn.integrableOn_compact isCompact_Icc)
    rw [hthm]
    apply Finset.sum_eq_zero
    intro i _
    have hfront : (∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), H (i.insertNth (b i) x) i) = 0 := by
      simp only [hface i (b i) (habs_b i)]
      simp
    have hback : (∫ x in Set.Icc (a ∘ i.succAbove) (b ∘ i.succAbove), H (i.insertNth (a i) x) i) = 0 := by
      simp only [hface i (a i) (habs_a i)]
      simp
    rw [hfront, hback, sub_zero]
  -- `H`'s divergence vanishes outside the box, so the box integral equals the whole-space integral.
  have hdiv_zero_outside_box : ∀ y ∈ (Set.Icc a b)ᶜ, ∑ i, (fderiv ℝ H y) (Pi.single i 1) i = 0 := by
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, hadef, hbdef, Pi.le_def, not_forall,
      not_le] at hy
    have hex : ∃ i, C < |y i| := by
      rcases hy with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact ⟨i, by rw [abs_of_neg (by linarith)]; linarith⟩
      · exact ⟨i, by rw [abs_of_pos (by linarith)]; linarith⟩
    obtain ⟨i, hi⟩ := hex
    rw [hfderiv_zero_open y ⟨i, hi⟩]; simp
  have hset : (∫ y in Set.Icc a b, ∑ i, (fderiv ℝ H y) (Pi.single i 1) i) =
      ∫ y, ∑ i, (fderiv ℝ H y) (Pi.single i 1) i :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hdiv_zero_outside_box
  have hwhole : (∫ y, ∑ i, (fderiv ℝ H y) (Pi.single i 1) i) = 0 := hset ▸ hbox
  -- Rewrite the (transported) divergence sum via `hdiv_eq`, then transport the whole-space integral
  -- back to `ℝ³` via the measure-preserving map `toFin3.symm`.
  have hwhole' : (∫ y, LinearMap.trace ℝ ℝ³
      ((fderiv ℝ G (toFin3.symm y) : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)) = 0 := by
    rw [← hwhole]; exact integral_congr_ae (Filter.Eventually.of_forall fun y => (hdiv_eq y).symm)
  have hembed : MeasurableEmbedding (toFin3.symm : (Fin 3 → ℝ) → ℝ³) :=
    toFin3.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  rw [← measurePreserving_toFin3_symm.integral_comp hembed
    (fun x => LinearMap.trace ℝ ℝ³ ((fderiv ℝ G x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³))]
  exact hwhole'

/-- Local integrability (indeed, integrability on any ball) of the singular integrand
`‖ψ x‖ ^ 2 / ‖x‖ ^ 2`, using that its `‖x‖⁻²` singularity at the origin is (barely) integrable in
`ℝ³` (`2 < finrank ℝ ℝ³ = 3`). -/
private lemma integrableOn_normSq_div_sq_ball (hψc : Continuous ψ) {C r : ℝ}
    (hC : ∀ x, ‖ψ x‖ ≤ C) :
    IntegrableOn (fun x : ℝ³ => ‖ψ x‖ ^ 2 / ‖x‖ ^ 2) (ball (0 : ℝ³) r) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ³ => ‖ψ x‖ ^ 2 / ‖x‖ ^ 2) volume := by
    refine (measurable_of_continuousOn_compl_singleton (0 : ℝ³) ?_).aestronglyMeasurable
    exact ((hψc.norm.pow 2).continuousOn).div (continuous_norm.pow 2).continuousOn
      (fun x hx => pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  refine integrableOn_ball_of_norm_le_rpow (by simp)
    (C := C ^ 2) (α := 2) (by rw [finrank_euclideanSpace_fin]; norm_num)
    (Filter.Eventually.of_forall fun x => ?_) hmeas
  rcases eq_or_ne x 0 with hx0 | hx0
  · simp [hx0]
  · have hnn : (0:ℝ) ≤ ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.rpow_neg (norm_nonneg x),
      ← Real.rpow_natCast ‖x‖ 2]
    push_cast
    rw [div_eq_mul_inv]
    gcongr
    exact hC x

/-- Local integrability of `x ↦ 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖`, via domination by
`(1/2) * (‖ψ x‖ ^ 2 / ‖x‖ ^ 2) + 2 * ‖fderiv ℝ ψ x‖ ^ 2` (AM–GM) and integrability of both
summands. -/
private lemma integrableOn_two_mul_div_mul_norm_fderiv (hψ : ContDiff ℝ 1 ψ)
    {s : Set ℝ³}
    (hIntI : IntegrableOn (fun x : ℝ³ => ‖ψ x‖ ^ 2 / ‖x‖ ^ 2) s)
    (hIntJ : IntegrableOn (fun x : ℝ³ => ‖fderiv ℝ ψ x‖ ^ 2) s) :
    IntegrableOn (fun x : ℝ³ => 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖) s := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ³ => 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖) volume := by
    refine (measurable_of_continuousOn_compl_singleton (0 : ℝ³) ?_).aestronglyMeasurable
    have h1 : ContinuousOn (fun x : ℝ³ => ‖ψ x‖ / ‖x‖) {(0 : ℝ³)}ᶜ :=
      hψ.continuous.norm.continuousOn.div continuous_norm.continuousOn
        (fun x hx => norm_ne_zero_iff.mpr (by simpa using hx))
    have h2 : ContinuousOn (fun x : ℝ³ => ‖fderiv ℝ ψ x‖) {(0 : ℝ³)}ᶜ :=
      ((hψ.continuous_fderiv (by norm_num)).norm).continuousOn
    exact (continuousOn_const.mul h1).mul h2
  have hdom : Integrable (fun x : ℝ³ => (1/2) * (‖ψ x‖ ^ 2 / ‖x‖ ^ 2) + 2 * ‖fderiv ℝ ψ x‖ ^ 2)
      (volume.restrict s) := (hIntI.const_mul (1/2)).add (hIntJ.const_mul 2)
  refine Integrable.mono' hdom hmeas.restrict (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (‖ψ x‖ / ‖x‖ - 2 * ‖fderiv ℝ ψ x‖), sq_nonneg (‖ψ x‖ / ‖x‖),
    sq_nonneg (‖fderiv ℝ ψ x‖), div_pow ‖ψ x‖ ‖x‖ 2]

/-- **The integration-by-parts step of Hardy's inequality.** For `ψ` a `C¹` function whose
(topological) support is strictly inside the ball of radius `R`, `∫_{closedBall 0 R} div F = 0`
where `F := hardyField ψ`. Proved via a smooth radial cutoff `cutoffRadial ε` that vanishes near the
origin (so `cutoffRadial ε • F` is genuinely `C¹` everywhere and the base divergence-theorem fact
`integral_trace_fderiv_eq_zero_of_compactSupport` applies with no exceptional point), followed by
`ε → 0⁺`. -/
theorem integral_divergence_eq_zero_of_support_subset_ball
    (hψ : ContDiff ℝ 1 ψ) {R : ℝ} (hR : 0 < R) (hsupp : tsupport ψ ⊆ ball (0 : ℝ³) R) :
    IntegrableOn
      (fun x => LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³))
      (closedBall (0 : ℝ³) R) volume ∧
    ∫ x in closedBall (0 : ℝ³) R,
      LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)
        ∂(volume : Measure ℝ³) = 0 := by
  have hFD : ∀ x, HasFDerivAt ψ (fderiv ℝ ψ x) x :=
    fun x => (hψ.differentiable one_ne_zero x).hasFDerivAt
  have hcompact : HasCompactSupport ψ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℝ³) R) (isClosed_tsupport ψ)
      (hsupp.trans ball_subset_closedBall)
  obtain ⟨C0, hC0⟩ := (hcompact.isCompact_range hψ.continuous).isBounded.subset_closedBall (0 : ℂ)
  set C : ℝ := max C0 0 with hCdef
  have hC : ∀ x, ‖ψ x‖ ≤ C := fun x =>
    (mem_closedBall_zero_iff.mp (hC0 (mem_range_self x))).trans (le_max_left _ _)
  have hCnn : (0 : ℝ) ≤ C := le_max_right _ _
  -- Integrability of `div F` over `closedBall 0 R`, via domination by the pieces `div F`
  -- decomposes into (already handled by the existing local-integrability infrastructure).
  have hIntI : IntegrableOn (fun x : ℝ³ => ‖ψ x‖ ^ 2 / ‖x‖ ^ 2) (closedBall (0 : ℝ³) R) :=
    (integrableOn_normSq_div_sq_ball hψ.continuous hC (r := R + 1)).mono_set
      (closedBall_subset_ball (lt_add_one R))
  have hIntJ : IntegrableOn (fun x : ℝ³ => ‖fderiv ℝ ψ x‖ ^ 2) (closedBall (0 : ℝ³) R) :=
    ((hψ.continuous_fderiv one_ne_zero).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 R)
  have hIntAB : IntegrableOn (fun x : ℝ³ => 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖)
      (closedBall (0 : ℝ³) R) := integrableOn_two_mul_div_mul_norm_fderiv hψ hIntI hIntJ
  have hbound : ∀ x : ℝ³, x ≠ 0 →
      |LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)|
        ≤ ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 + 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖ := by
    intro x hx
    rw [divergence_hardyField hx (hFD x)]
    have h1 := abs_fderiv_normSq_ψ_apply_invSqSmulId_le (ψ := ψ) hx
    have h3 : |‖ψ x‖ ^ 2 * (‖x‖ ^ 2)⁻¹| = ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 := by
      rw [abs_of_nonneg (by positivity), div_eq_mul_inv]
    calc |‖ψ x‖ ^ 2 * (‖x‖ ^ 2)⁻¹ + (2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x)|
        ≤ |‖ψ x‖ ^ 2 * (‖x‖ ^ 2)⁻¹| +
            |(2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x)| := abs_add_le _ _
      _ ≤ ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 + 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖ := by
          rw [h3]
          gcongr
          calc |(2 • (innerSL ℝ (ψ x)).comp (fderiv ℝ ψ x)) (invSqSmulId x)|
              ≤ 2 * ‖ψ x‖ * ‖fderiv ℝ ψ x‖ / ‖x‖ := h1
            _ = 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖ := by ring
  have hTraceCont : Continuous (fun T : ℝ³ →L[ℝ] ℝ³ => LinearMap.trace ℝ ℝ³ (T : ℝ³ →ₗ[ℝ] ℝ³)) :=
    ((LinearMap.trace ℝ ℝ³).comp (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
  have hcontAt : ∀ x : ℝ³, x ≠ 0 → ContinuousAt
      (fun x => LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)) x :=
    fun x hx => hTraceCont.continuousAt.comp
      ((contDiffAt_hardyField_of_ne hψ hx).continuousAt_fderiv one_ne_zero)
  have hmeasTrace : AEStronglyMeasurable
      (fun x => LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³))
      volume :=
    (measurable_of_continuousOn_compl_singleton (0 : ℝ³)
      (fun x hx => (hcontAt x hx).continuousWithinAt)).aestronglyMeasurable
  have hIntTrace : IntegrableOn
      (fun x => LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³))
      (closedBall (0 : ℝ³) R) volume := by
    have hae : ∀ᵐ x ∂(volume.restrict (closedBall (0 : ℝ³) R)),
        ‖LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)‖ ≤
          ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 + 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖ := by
      have hne : {(0 : ℝ³)}ᶜ ∈ ae volume := compl_mem_ae_iff.mpr (measure_singleton 0)
      filter_upwards [ae_restrict_of_ae hne] with x hx
      rw [Real.norm_eq_abs]; exact hbound x hx
    exact Integrable.mono' (hIntI.add hIntAB) hmeasTrace.restrict hae
  refine ⟨hIntTrace, ?_⟩
  obtain ⟨M, hM0, hM⟩ := chiCutoff_deriv_bound
  -- **The per-`ε` identity.** For every `ε > 0`,
  -- `∫ cutoffRadial ε * div F = - ∫ (∇cutoffRadial ε) · F` over `closedBall 0 R`.
  have hEq : ∀ ε : ℝ, 0 < ε →
      (∫ x in closedBall (0 : ℝ³) R, cutoffRadial ε x *
        LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) ∂volume) =
      - ∫ x in closedBall (0 : ℝ³) R, (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x) ∂volume := by
    intro ε hε
    have hGεsupp : tsupport (fun x => cutoffRadial ε x • hardyField ψ x) ⊆ ball (0 : ℝ³) R :=
      (tsupport_hardyFieldCutoff_subset (ψ := ψ) (ε := ε)).trans hsupp
    have hzero := integral_trace_fderiv_eq_zero_of_compactSupport
      (contDiff_hardyFieldCutoff hψ hε) hR hGεsupp
    have hGεzero_outside : ∀ x ∉ closedBall (0 : ℝ³) R,
        LinearMap.trace ℝ ℝ³ ((fderiv ℝ (fun y => cutoffRadial ε y • hardyField ψ y) x :
          ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) = 0 := by
      intro x hx
      have hxnot : x ∉ tsupport (fun y => cutoffRadial ε y • hardyField ψ y) :=
        fun h => hx (ball_subset_closedBall (hGεsupp h))
      have hev : (fun y => cutoffRadial ε y • hardyField ψ y) =ᶠ[nhds x] (fun _ => (0 : ℝ³)) := by
        filter_upwards [(isOpen_compl_iff.mpr isClosed_closure).mem_nhds hxnot] with y hy
        exact image_eq_zero_of_notMem_tsupport (f := fun y => cutoffRadial ε y • hardyField ψ y) hy
      rw [hev.fderiv_eq]; simp
    have hset : (∫ x, LinearMap.trace ℝ ℝ³ ((fderiv ℝ (fun y => cutoffRadial ε y • hardyField ψ y) x :
        ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) ∂volume) =
        ∫ x in closedBall (0 : ℝ³) R, LinearMap.trace ℝ ℝ³
          ((fderiv ℝ (fun y => cutoffRadial ε y • hardyField ψ y) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)
          ∂volume := (setIntegral_eq_integral_of_forall_compl_eq_zero hGεzero_outside).symm
    rw [hset] at hzero
    have hpt : ∀ᵐ x ∂(volume.restrict (closedBall (0 : ℝ³) R)),
        LinearMap.trace ℝ ℝ³ ((fderiv ℝ (fun y => cutoffRadial ε y • hardyField ψ y) x :
          ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) =
        cutoffRadial ε x *
          LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) +
        (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x) := by
      have hne : {(0 : ℝ³)}ᶜ ∈ ae volume := compl_mem_ae_iff.mpr (measure_singleton 0)
      filter_upwards [ae_restrict_of_ae hne] with x hx
      exact divergence_cutoffRadial_smul_hardyField hε hx (hFD x)
    have hIntCF : IntegrableOn (fun x => cutoffRadial ε x *
        LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³))
        (closedBall (0 : ℝ³) R) volume := by
      have hmeas : AEStronglyMeasurable (fun x => cutoffRadial ε x *
          LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)) volume :=
        (contDiff_cutoffRadial hε).continuous.aestronglyMeasurable.mul hmeasTrace
      refine Integrable.mono' hIntTrace.abs hmeas.restrict (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      calc |cutoffRadial ε x| *
            |LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)|
          ≤ 1 * |LinearMap.trace ℝ ℝ³
              ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)| := by
            gcongr
            rw [abs_of_nonneg (cutoffRadial_nonneg ε x)]; exact cutoffRadial_le_one ε x
        _ = _ := by rw [one_mul]
    have hIntGεTrace : IntegrableOn (fun x => LinearMap.trace ℝ ℝ³
        ((fderiv ℝ (fun y => cutoffRadial ε y • hardyField ψ y) x : ℝ³ →L[ℝ] ℝ³) :
          ℝ³ →ₗ[ℝ] ℝ³)) (closedBall (0 : ℝ³) R) volume :=
      (hTraceCont.comp
        ((contDiff_hardyFieldCutoff hψ hε).continuous_fderiv one_ne_zero)).continuousOn.integrableOn_compact
        (isCompact_closedBall 0 R)
    have hIntGrad : IntegrableOn (fun x => (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x))
        (closedBall (0 : ℝ³) R) volume :=
      (hIntGεTrace.sub hIntCF).congr (hpt.mono fun x hx => by simp only [Pi.sub_apply]; linarith [hx])
    have hsplit : (∫ x in closedBall (0 : ℝ³) R, LinearMap.trace ℝ ℝ³
        ((fderiv ℝ (fun y => cutoffRadial ε y • hardyField ψ y) x : ℝ³ →L[ℝ] ℝ³) :
          ℝ³ →ₗ[ℝ] ℝ³) ∂volume) =
        (∫ x in closedBall (0 : ℝ³) R, cutoffRadial ε x *
          LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) ∂volume) +
        ∫ x in closedBall (0 : ℝ³) R, (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x) ∂volume := by
      rw [← integral_add hIntCF hIntGrad]; exact integral_congr_ae hpt
    rw [hsplit] at hzero
    linarith [hzero]
  -- **The elementary `O(ε)` bound on the "gradient" term**, using that `∇(cutoffRadial ε)` is
  -- supported in the shell `ε ≤ ‖x‖ ≤ 2 * ε`, where `‖∇(cutoffRadial ε)‖ ≤ M / ε` and
  -- `‖hardyField ψ‖ ≤ C ^ 2 / ε`, over a region of volume `O(ε ^ 3)`.
  set K : ℝ := M * C ^ 2 * (32 * Real.pi / 3) with hKdef
  have hK0 : 0 ≤ K :=
    mul_nonneg (mul_nonneg hM0 (sq_nonneg C)) (by positivity)
  have hRHSbound : ∀ ε : ℝ, 0 < ε → 2 * ε ≤ R →
      |∫ x in closedBall (0 : ℝ³) R, (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x) ∂volume|
        ≤ K * ε := by
    intro ε hε hεR
    have hgzero : ∀ x : ℝ³, 2 * ε < ‖x‖ → (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x) = 0 :=
      fun x hx => by rw [fderiv_cutoffRadial_eq_zero_of_gt hε hx]; simp
    have hgzeroR : ∀ x ∉ closedBall (0 : ℝ³) R, (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x) = 0 := by
      intro x hx
      refine hgzero x ?_
      by_contra hle
      push Not at hle
      exact hx (mem_closedBall_zero_iff.mpr (hle.trans hεR))
    have hgzero2ε : ∀ x ∉ closedBall (0 : ℝ³) (2 * ε),
        (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x) = 0 :=
      fun x hx => hgzero x (by simpa [mem_closedBall_zero_iff, not_le] using hx)
    have heqset : (∫ x in closedBall (0 : ℝ³) R, (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x)
          ∂volume) =
        ∫ x in closedBall (0 : ℝ³) (2 * ε), (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x)
          ∂volume :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hgzeroR).trans
        (setIntegral_eq_integral_of_forall_compl_eq_zero hgzero2ε).symm
    rw [heqset, ← Real.norm_eq_abs]
    have hgbound : ∀ x ∈ closedBall (0 : ℝ³) (2 * ε),
        ‖(fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x)‖ ≤ M * C ^ 2 / ε ^ 2 := by
      intro x _
      rcases lt_or_ge ‖x‖ ε with hlt | hge
      · rw [fderiv_cutoffRadial_eq_zero_of_lt hε hlt]
        simp only [zero_apply, norm_zero]
        positivity
      · have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hε hge
        have hxne : x ≠ 0 := norm_pos_iff.mp hxpos
        have hFxeq : ‖hardyField ψ x‖ = ‖ψ x‖ ^ 2 / ‖x‖ := by
          rw [hardyField, invSqSmulId, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (sq_nonneg _), abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))]
          field_simp
        have hFxle : ‖hardyField ψ x‖ ≤ C ^ 2 / ε := by
          rw [hFxeq]
          calc ‖ψ x‖ ^ 2 / ‖x‖ ≤ C ^ 2 / ‖x‖ := by gcongr; exact hC x
            _ ≤ C ^ 2 / ε := by gcongr
        calc ‖(fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x)‖
            ≤ ‖fderiv ℝ (cutoffRadial ε) x‖ * ‖hardyField ψ x‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ M / ε * (C ^ 2 / ε) := by
              gcongr
              exact norm_fderiv_cutoffRadial_le hε hM0 hM x
          _ = M * C ^ 2 / ε ^ 2 := by ring
    have hvol : volume (closedBall (0 : ℝ³) (2 * ε)) < ⊤ := (isCompact_closedBall 0 _).measure_lt_top
    have hnormle := norm_setIntegral_le_of_norm_le_const hvol hgbound
    have hvoleq : volume.real (closedBall (0 : ℝ³) (2 * ε)) = (2 * ε) ^ 3 * (Real.pi * 4 / 3) := by
      unfold Measure.real
      rw [EuclideanSpace.volume_closedBall_fin_three]
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_ofReal (by positivity)]
    rw [hvoleq] at hnormle
    calc ‖∫ x in closedBall (0 : ℝ³) (2 * ε), (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x)
          ∂volume‖
        ≤ M * C ^ 2 / ε ^ 2 * ((2 * ε) ^ 3 * (Real.pi * 4 / 3)) := hnormle
      _ = K * ε := by rw [hKdef]; field_simp; ring
  -- **The `ε → 0⁺` limit.** `cutoffRadial ε x → 1` pointwise for `x ≠ 0`.
  have hcutofflim : ∀ x : ℝ³, x ≠ 0 →
      Filter.Tendsto (fun ε => cutoffRadial ε x) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
    intro x hx
    have hmem : {ε : ℝ | cutoffRadial ε x = 1} ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      (mem_nhdsGT_iff_exists_Ioo_subset' (show (0:ℝ) < ‖x‖/2 from half_pos (norm_pos_iff.mpr hx))).mpr
        ⟨‖x‖ / 2, half_pos (norm_pos_iff.mpr hx),
          fun ε hε => cutoffRadial_eq_one_of_le hε.1 (by linarith [hε.2])⟩
    have heqfun : (fun ε => cutoffRadial ε x) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun _ => (1 : ℝ)) :=
      Filter.eventuallyEq_of_mem hmem (fun ε hε => hε)
    exact (Filter.tendsto_congr' heqfun).mpr tendsto_const_nhds
  -- Dominated convergence for `LHS ε := ∫ cutoffRadial ε * div F`.
  have hDCT : Filter.Tendsto
      (fun ε => ∫ x in closedBall (0 : ℝ³) R, cutoffRadial ε x *
        LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) ∂volume)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (∫ x in closedBall (0 : ℝ³) R,
        LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) ∂volume)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => |LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)|)
      (Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε =>
        (contDiff_cutoffRadial hε).continuous.aestronglyMeasurable.mul hmeasTrace.restrict)
      (Filter.eventually_of_mem self_mem_nhdsWithin fun ε _ => Filter.Eventually.of_forall fun x => ?_)
      hIntTrace.abs ?_
    · rw [Real.norm_eq_abs, abs_mul]
      calc |cutoffRadial ε x| *
            |LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)|
          ≤ 1 * |LinearMap.trace ℝ ℝ³
              ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)| := by
            gcongr
            rw [abs_of_nonneg (cutoffRadial_nonneg ε x)]; exact cutoffRadial_le_one ε x
        _ = _ := by rw [one_mul]
    · have hne : {(0 : ℝ³)}ᶜ ∈ ae volume := compl_mem_ae_iff.mpr (measure_singleton 0)
      filter_upwards [ae_restrict_of_ae hne] with x hx
      simpa using (hcutofflim x hx).mul (tendsto_const_nhds
        (x := LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³)))
  -- The `∇(cutoffRadial ε) · F` term tends to `0`.
  have hRHStendsto0 : Filter.Tendsto
      (fun ε => ∫ x in closedBall (0 : ℝ³) R, (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x) ∂volume)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hKtendsto : Filter.Tendsto (fun ε : ℝ => K * ε) (nhds (0 : ℝ)) (nhds 0) := by
      simpa using (tendsto_const_nhds (x := K)).mul (Filter.tendsto_id (x := nhds (0:ℝ)))
    have hmem : Set.Ioc (0 : ℝ) (R / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
      (mem_nhdsGT_iff_exists_Ioo_subset' (half_pos hR)).mpr
        ⟨R / 2, half_pos hR, fun ε hε => ⟨hε.1, hε.2.le⟩⟩
    exact squeeze_zero_norm'
      (Filter.eventually_of_mem hmem fun ε hε => hRHSbound ε hε.1 (by linarith [hε.2]))
      (hKtendsto.mono_left nhdsWithin_le_nhds)
  -- `LHS ε` also tends to `0` (since `LHS ε = -RHS ε` exactly).
  have hLHStendsto0 : Filter.Tendsto
      (fun ε => ∫ x in closedBall (0 : ℝ³) R, cutoffRadial ε x *
        LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) ∂volume)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hcongr : (fun ε => ∫ x in closedBall (0 : ℝ³) R, cutoffRadial ε x *
          LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) ∂volume)
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun ε => - ∫ x in closedBall (0 : ℝ³) R, (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x)
          ∂volume) :=
      Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun ε hε => hEq ε hε
    have hneg : Filter.Tendsto
        (fun ε => - ∫ x in closedBall (0 : ℝ³) R, (fderiv ℝ (cutoffRadial ε) x) (hardyField ψ x)
          ∂volume)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by simpa using hRHStendsto0.neg
    exact (Filter.tendsto_congr' hcongr).mpr hneg
  exact tendsto_nhds_unique hDCT hLHStendsto0

/-!
## E. Assembling Hardy's inequality
-/

/-- If `ψ` vanishes outside `tsupport ψ ⊆ ball 0 R`, then `x ↦ ‖ψ x‖ ^ 2 / ‖x‖ ^ 2` vanishes outside
`closedBall 0 R`, so its integral over `closedBall 0 R` equals its integral over all of `ℝ³`. -/
private lemma setIntegral_normSq_div_sq_eq_integral {R : ℝ}
    (hsupp : tsupport ψ ⊆ ball (0 : ℝ³) R) :
    ∫ x in closedBall (0 : ℝ³) R, ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 ∂(volume : Measure ℝ³) =
      ∫ x, ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 ∂(volume : Measure ℝ³) := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have hxnot : x ∉ tsupport ψ := fun h => hx (ball_subset_closedBall (hsupp h))
  simp [image_eq_zero_of_notMem_tsupport hxnot]

/-- If `ψ` vanishes outside `tsupport ψ ⊆ ball 0 R`, then so does `fderiv ℝ ψ`, so
`x ↦ ‖fderiv ℝ ψ x‖ ^ 2` vanishes outside `closedBall 0 R` and its integral over `closedBall 0 R`
equals its integral over all of `ℝ³`. -/
private lemma setIntegral_normSq_fderiv_eq_integral {R : ℝ}
    (hsupp : tsupport ψ ⊆ ball (0 : ℝ³) R) :
    ∫ x in closedBall (0 : ℝ³) R, ‖fderiv ℝ ψ x‖ ^ 2 ∂(volume : Measure ℝ³) =
      ∫ x, ‖fderiv ℝ ψ x‖ ^ 2 ∂(volume : Measure ℝ³) := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have hxnot : x ∉ tsupport ψ := fun h => hx (ball_subset_closedBall (hsupp h))
  have : ψ =ᶠ[nhds x] 0 := by
    filter_upwards [(isOpen_compl_iff.mpr isClosed_closure).mem_nhds hxnot] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  simp [this.fderiv_eq]

/-- **Hardy's inequality in `ℝ³`.** For a compactly-supported `C¹` function `ψ : ℝ³ → ℂ`,
`∫ ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 ≤ 4 * ∫ ‖fderiv ℝ ψ x‖ ^ 2`. -/
theorem hardy_inequality_R3 (hψ : ContDiff ℝ 1 ψ) (hcompact : HasCompactSupport ψ) :
    ∫ x, ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 ∂(volume : Measure ℝ³) ≤
      4 * ∫ x, ‖fderiv ℝ ψ x‖ ^ 2 ∂(volume : Measure ℝ³) := by
  have hFD : ∀ x, HasFDerivAt ψ (fderiv ℝ ψ x) x :=
    fun x => (hψ.differentiable (by norm_num) x).hasFDerivAt
  -- Choose `R` with `tsupport ψ ⊆ ball 0 R`.
  obtain ⟨R0, hR0⟩ := hcompact.isBounded.subset_ball (0 : ℝ³)
  set R : ℝ := max R0 1 with hRdef
  have hR : (0:ℝ) < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsupp : tsupport ψ ⊆ ball (0 : ℝ³) R := hR0.trans (ball_subset_ball (le_max_left _ _))
  -- Bound `C` on `‖ψ‖` from compact support.
  obtain ⟨C0, hC0⟩ := (hcompact.isCompact_range hψ.continuous).isBounded.subset_closedBall (0 : ℂ)
  set C : ℝ := max C0 0 with hCdef
  have hC : ∀ x, ‖ψ x‖ ≤ C := fun x =>
    (mem_closedBall_zero_iff.mp (hC0 (mem_range_self x))).trans (le_max_left _ _)
  -- Local integrability on `closedBall 0 R`.
  have hIntI : IntegrableOn (fun x : ℝ³ => ‖ψ x‖ ^ 2 / ‖x‖ ^ 2) (closedBall (0:ℝ³) R) :=
    (integrableOn_normSq_div_sq_ball hψ.continuous hC (r := R + 1)).mono_set
      (closedBall_subset_ball (lt_add_one R))
  have hIntJ : IntegrableOn (fun x : ℝ³ => ‖fderiv ℝ ψ x‖ ^ 2) (closedBall (0:ℝ³) R) :=
    ((hψ.continuous_fderiv (by norm_num)).norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall 0 R)
  have hIntAB : IntegrableOn (fun x : ℝ³ => 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖)
      (closedBall (0:ℝ³) R) := integrableOn_two_mul_div_mul_norm_fderiv hψ hIntI hIntJ
  -- The integration-by-parts step.
  obtain ⟨hIntTrace, hZero⟩ := integral_divergence_eq_zero_of_support_subset_ball hψ hR hsupp
  -- The pointwise divergence inequality holds a.e. (off the null set `{0}`).
  have hpt : ∀ᵐ x ∂(volume.restrict (closedBall (0:ℝ³) R)), ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 ≤
      LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) +
        2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖ := by
    have hne : {(0:ℝ³)}ᶜ ∈ ae volume := compl_mem_ae_iff.mpr (measure_singleton 0)
    filter_upwards [ae_restrict_of_ae hne] with x hx
    exact normSq_ψ_div_sq_le_divergence_add_two_mul hx (hFD x)
  -- Integrate: `I_R ≤ ∫ (div F + 2 a b) = 0 + 2 ∫ a b`.
  have hstep1 : ∫ x in closedBall (0:ℝ³) R, ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 ∂volume ≤
      ∫ x in closedBall (0:ℝ³) R,
        (LinearMap.trace ℝ ℝ³ ((fderiv ℝ (hardyField ψ) x : ℝ³ →L[ℝ] ℝ³) : ℝ³ →ₗ[ℝ] ℝ³) +
          2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖) ∂volume :=
    setIntegral_mono_ae_restrict hIntI (hIntTrace.add hIntAB) hpt
  rw [integral_add hIntTrace hIntAB, hZero, zero_add] at hstep1
  -- AM–GM: `2 ∫ a b ≤ (1/2) I_R + 2 J_R`.
  have hAMGM : ∫ x in closedBall (0:ℝ³) R, 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖ ∂volume ≤
      (1/2) * ∫ x in closedBall (0:ℝ³) R, ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 ∂volume +
        2 * ∫ x in closedBall (0:ℝ³) R, ‖fderiv ℝ ψ x‖ ^ 2 ∂volume := by
    have hle : ∫ x in closedBall (0:ℝ³) R, 2 * (‖ψ x‖ / ‖x‖) * ‖fderiv ℝ ψ x‖ ∂volume ≤
        ∫ x in closedBall (0:ℝ³) R,
          ((1/2) * (‖ψ x‖ ^ 2 / ‖x‖ ^ 2) + 2 * ‖fderiv ℝ ψ x‖ ^ 2) ∂volume :=
      setIntegral_mono_ae_restrict hIntAB ((hIntI.const_mul (1/2)).add (hIntJ.const_mul 2))
        (ae_restrict_of_ae (Filter.Eventually.of_forall fun x => by
          nlinarith [sq_nonneg (‖ψ x‖ / ‖x‖ - 2 * ‖fderiv ℝ ψ x‖), sq_nonneg (‖ψ x‖ / ‖x‖),
            sq_nonneg (‖fderiv ℝ ψ x‖), div_pow ‖ψ x‖ ‖x‖ 2]))
    rwa [integral_add (hIntI.const_mul (1/2)) (hIntJ.const_mul 2), integral_const_mul,
      integral_const_mul] at hle
  -- Combine: `I_R ≤ (1/2) I_R + 2 J_R`, i.e. `I_R ≤ 4 J_R`.
  have hfinal : ∫ x in closedBall (0:ℝ³) R, ‖ψ x‖ ^ 2 / ‖x‖ ^ 2 ∂volume ≤
      4 * ∫ x in closedBall (0:ℝ³) R, ‖fderiv ℝ ψ x‖ ^ 2 ∂volume := by linarith
  -- Extend from `closedBall 0 R` to all of `ℝ³` via compact support.
  rwa [setIntegral_normSq_div_sq_eq_integral hsupp,
    setIntegral_normSq_fderiv_eq_integral hsupp] at hfinal
