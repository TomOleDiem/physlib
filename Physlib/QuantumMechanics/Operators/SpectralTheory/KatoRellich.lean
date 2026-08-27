/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Complex.Convex

/-!

# The Kato–Rellich theorem

## i. Overview

This file develops the general operator-theoretic content of the Kato–Rellich theorem: if `A` is
self-adjoint and `B` is symmetric and *relatively bounded* with respect to `A` with relative bound
strictly less than `1`, then `A + B` (with domain `A.domain`) is essentially self-adjoint.

The proof is potential-independent pure operator theory. It proceeds via von Neumann's defect-index
criterion (`IsSymmetric.isEssentiallySelfAdjoint_of_defectNumber_eq_zero`): we show that
`(A + B) - (i λ) • 1` is surjective for a single sufficiently large `λ > 0`, and transfer this fact
to `z = ± i` using the connectedness of the (upper/lower) open half-planes inside the regularity
domain of the symmetric operator `A + B`.

The key elementary facts used are:
- For `A` symmetric and `x ∈ A.domain`, `r : ℝ`, `‖A x - (i r) • x‖ ^ 2 = ‖A x‖ ^ 2 + r ^ 2 * ‖x‖ ^ 2`
  (`sq_norm_sub_I_smul`). This uses only symmetry (`⟪A x, x⟫` real), not self-adjointness.
- Surjectivity of `A - (i λ) • 1` at every real `λ ≠ 0`, from self-adjointness of `A`
  (`IsSelfAdjoint.sub_smul_surjective`, already in `SelfAdjoint.lean`).

Combining these lets us construct, for `λ` large, a bounded operator `K = B ∘ (A - iλ)⁻¹` on all of
`H` with `‖K‖ < 1`, invert `1 + K` via a Neumann series, and solve `(A + B - iλ) x = y` for
arbitrary `y : H` explicitly.

## ii. Key results

- `LinearPMap.IsRelativelyBounded` : `B` is relatively bounded w.r.t. `A` with bound `(a, b)`.
- `LinearPMap.IsSymmetric.sq_norm_sub_I_smul` : the elementary norm identity
  `‖A x - (i r) • x‖ ^ 2 = ‖A x‖ ^ 2 + r ^ 2 * ‖x‖ ^ 2` for symmetric `A`.
- `LinearPMap.katoRellich` : the Kato–Rellich theorem — `A` self-adjoint, `B` symmetric and
  relatively `A`-bounded with relative bound `< 1` implies `A + B` is essentially self-adjoint.

## iii. Table of contents

- A. Relative boundedness
- B. The elementary norm identity for symmetric operators
- C. The Kato–Rellich theorem
  - C.1. Surjectivity of the shifted sum at a single large `λ`
  - C.2. Transfer to `± i` and conclusion

## iv. References

- [Michael Reed and Barry Simon, *Methods of Modern Mathematical Physics II: Fourier Analysis,
  Self-Adjointness*][ReedSimon1975], Theorem X.12 (the Kato–Rellich theorem).

-/

@[expose] public section

namespace LinearPMap

open InnerProductSpace
open Complex
open ComplexConjugate
open Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable section

/-!
## A. Relative boundedness
-/

/-- `B` is relatively bounded with respect to `A` with bound `(a, b)`: `A.domain ≤ B.domain`, and
`‖B x‖ ≤ a * ‖A x‖ + b * ‖x‖` for every `x ∈ A.domain` (viewed as an element of `B.domain` via the
domain inclusion). -/
def IsRelativelyBounded (B A : H →ₗ.[ℂ] H) (a b : ℝ) : Prop :=
  ∃ hle : A.domain ≤ B.domain, ∀ x : A.domain, ‖B ⟨(x : H), hle x.2⟩‖ ≤ a * ‖A x‖ + b * ‖(x : H)‖

namespace IsRelativelyBounded

variable {A B : H →ₗ.[ℂ] H} {a b : ℝ}

lemma domain_le (h : IsRelativelyBounded B A a b) : A.domain ≤ B.domain := h.choose

lemma norm_le (h : IsRelativelyBounded B A a b) (x : A.domain) :
    ‖B ⟨(x : H), h.domain_le x.2⟩‖ ≤ a * ‖A x‖ + b * ‖(x : H)‖ := h.choose_spec x

end IsRelativelyBounded

/-!
## B. The elementary norm identity for symmetric operators
-/

namespace IsSymmetric

variable {A : H →ₗ.[ℂ] H} (hA : A.IsSymmetric)
include hA

/-- The elementary norm identity for a symmetric operator: for `x ∈ A.domain` and `r : ℝ`,
`‖A x - (i r) • x‖ ^ 2 = ‖A x‖ ^ 2 + r ^ 2 * ‖x‖ ^ 2`. The cross term vanishes because
`⟪A x, x⟫` is real (symmetry) and `i r` is purely imaginary. -/
lemma sq_norm_sub_I_smul (x : A.domain) (r : ℝ) :
    ‖(A x : H) - (Complex.I * r) • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + r ^ 2 * ‖(x : H)‖ ^ 2 := by
  set u : H := (A x : H) with hu
  set v : H := (x : H) with hv
  have hreal := isSymmetric_iff_inner_map_self_real.mp hA x
  have him : (⟪u, v⟫_ℂ).im = 0 := Complex.conj_eq_iff_im.mp hreal
  have hre : ∀ z : ℂ, RCLike.re z = z.re := fun z ↦ congrFun RCLike.re_eq_complex_re z
  rw [norm_sub_sq (𝕜 := ℂ), hre]
  have hcross : (⟪u, (Complex.I * (r : ℂ)) • v⟫_ℂ).re = 0 := by
    rw [inner_smul_right, show (⟪u, v⟫_ℂ) = ((⟪u, v⟫_ℂ).re : ℂ) from Complex.ext rfl (by simp [him])]
    simp [Complex.mul_re]
  rw [hcross]
  have hnorm : ‖(Complex.I * (r : ℂ)) • v‖ ^ 2 = r ^ 2 * ‖v‖ ^ 2 := by
    rw [norm_smul]; simp [mul_pow]
  rw [hnorm]
  ring

/-- Corollary: `‖A x‖ ≤ ‖A x - (i r) • x‖`. -/
lemma norm_le_norm_sub_I_smul (x : A.domain) (r : ℝ) :
    ‖A x‖ ≤ ‖(A x : H) - (Complex.I * r) • (x : H)‖ := by
  have h := hA.sq_norm_sub_I_smul x r
  have hle : ‖A x‖ ^ 2 ≤ ‖(A x : H) - (Complex.I * r) • (x : H)‖ ^ 2 := by
    rw [h]; nlinarith [sq_nonneg r, sq_nonneg ‖(x : H)‖, mul_nonneg (sq_nonneg r) (sq_nonneg ‖(x:H)‖)]
  have := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at this

/-- Corollary: `|r| * ‖x‖ ≤ ‖A x - (i r) • x‖`. -/
lemma abs_mul_norm_le_norm_sub_I_smul (x : A.domain) (r : ℝ) :
    |r| * ‖(x : H)‖ ≤ ‖(A x : H) - (Complex.I * r) • (x : H)‖ := by
  have h := hA.sq_norm_sub_I_smul x r
  have hle : (|r| * ‖(x : H)‖) ^ 2 ≤ ‖(A x : H) - (Complex.I * r) • (x : H)‖ ^ 2 := by
    rw [h, mul_pow, sq_abs]; nlinarith [sq_nonneg ‖A x‖]
  have := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at this

end IsSymmetric

/-!
## C. The Kato–Rellich theorem
-/

section

variable [CompleteSpace H]

/-!
### C.1. Surjectivity of the shifted sum at a single large `λ`
-/

/-- **Kato–Rellich, surjectivity step.** If `A` is self-adjoint, `B` is relatively `A`-bounded
with bound `(a, b)` (with `0 ≤ a < 1`, `0 ≤ b`), and `r : ℝ` satisfies `b / (1 - a) < |r|`, then
`(A + B) - (i r) • 1` is surjective, i.e. it has full range.

The proof constructs the bounded operator `K := B ∘ (A - i r)⁻¹ : H →L[ℂ] H`, shows `‖K‖ < 1`,
inverts `1 + K` via a Neumann series (`Units.oneSub`), and solves `(A + B - i r) x = y` explicitly
for arbitrary `y : H`. -/
lemma katoRellich_sub_I_smul_surjective
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {a b : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha1 : a < 1) (hbound : B.IsRelativelyBounded A a b)
    {r : ℝ} (hr : b / (1 - a) < |r|) :
    Function.Surjective ((A + B) - (Complex.I * (r : ℂ)) • 1).toFun := by
  have hsym : A.IsSymmetric := LinearPMap.IsSelfAdjoint.isSymmetric hA
  obtain ⟨hle, hBbound⟩ := hbound
  set c : ℂ := Complex.I * (r : ℂ) with hc
  have h1a : (0:ℝ) < 1 - a := by linarith
  have hr0 : |r| > 0 := lt_of_le_of_lt (by positivity) hr
  have hrne : r ≠ 0 := fun h ↦ by simp [h] at hr0
  -- `f x = A x - c • x`, a bijective linear map `A.domain →ₗ[ℂ] H`.
  set f : A.domain →ₗ[ℂ] H := A.toFun - c • A.domain.subtype with hf
  have hfx : ∀ x : A.domain, f x = (A x : H) - c • (x : H) := fun x ↦ rfl
  -- Injectivity of `f`, from the norm identity.
  have hf_inj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx0
    have hbnd := hsym.abs_mul_norm_le_norm_sub_I_smul x r
    rw [← hfx, hx0, norm_zero] at hbnd
    have hxle : ‖(x : H)‖ ≤ 0 := by
      by_contra h
      exact absurd hbnd (not_le.mpr (mul_pos hr0 (lt_of_not_ge h)))
    exact Subtype.ext (norm_le_zero_iff.mp hxle)
  -- Surjectivity of `f`, from self-adjointness of `A`.
  have hf_surj : Function.Surjective f := by
    have hsurjA : Function.Surjective (A - c • 1).toFun :=
      LinearPMap.IsSelfAdjoint.sub_smul_surjective hA (by simp [hc, hrne])
    intro y
    obtain ⟨z, hz⟩ := hsurjA y
    have hzA : (z : H) ∈ A.domain := by
      have := z.2
      simpa [sub_domain, smul_domain, one_domain] using this
    refine ⟨⟨(z : H), hzA⟩, ?_⟩
    rw [hfx]
    rw [← hz]
    simp [sub_apply, smul_apply]
  let e : A.domain ≃ₗ[ℂ] H := LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  -- Norm bounds transported through `e.symm`.
  have he_bound : ∀ y : H, ‖(e.symm y : H)‖ ≤ |r|⁻¹ * ‖y‖ := by
    intro y
    have hfe : f (e.symm y) = y := e.apply_symm_apply y
    have hbnd := hsym.abs_mul_norm_le_norm_sub_I_smul (e.symm y) r
    rw [← hfx, hfe] at hbnd
    have h2 : |r| * ‖(e.symm y : H)‖ ≤ |r| * (|r|⁻¹ * ‖y‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul]
      exact hbnd
    exact le_of_mul_le_mul_left h2 hr0
  have heA_bound : ∀ y : H, ‖A (e.symm y)‖ ≤ ‖y‖ := by
    intro y
    have hfe : f (e.symm y) = y := e.apply_symm_apply y
    have hbnd := hsym.norm_le_norm_sub_I_smul (e.symm y) r
    rwa [← hfx, hfe] at hbnd
  -- `Rinv : H →L[ℂ] H` is the (bounded) inverse of `A - c • 1`, valued in `A.domain`.
  set Rinv0 : H →ₗ[ℂ] H := A.domain.subtype ∘ₗ e.symm.toLinearMap with hRinv0
  have hRinv0_bound : ∀ y : H, ‖Rinv0 y‖ ≤ |r|⁻¹ * ‖y‖ := he_bound
  set Rinv : H →L[ℂ] H := Rinv0.mkContinuous |r|⁻¹ hRinv0_bound with hRinv
  have hRinv_apply : ∀ y : H, Rinv y = (e.symm y : H) := fun y ↦ rfl
  -- `K = B ∘ Rinv : H →L[ℂ] H`, with `‖K‖ ≤ c₀ < 1`.
  set K0 : H →ₗ[ℂ] H := B.toFun ∘ₗ (Submodule.inclusion hle) ∘ₗ e.symm.toLinearMap with hK0
  have hK0_apply : ∀ y : H, K0 y = B ⟨(e.symm y : H), hle (e.symm y).2⟩ := fun y ↦ rfl
  set c₀ : ℝ := a + b * |r|⁻¹ with hc₀
  have hc₀_lt1 : c₀ < 1 := by
    have key : b < |r| * (1 - a) := (div_lt_iff₀ h1a).mp hr
    have hc₀r : c₀ * |r| < 1 * |r| := by
      have hexpand : c₀ * |r| = a * |r| + b := by
        rw [hc₀, add_mul, mul_assoc, inv_mul_cancel₀ hr0.ne', mul_one]
      rw [hexpand, one_mul]
      nlinarith [key]
    exact lt_of_mul_lt_mul_right hc₀r hr0.le
  have hc₀_nonneg : 0 ≤ c₀ := by positivity
  have hK0_bound : ∀ y : H, ‖K0 y‖ ≤ c₀ * ‖y‖ := by
    intro y
    rw [hK0_apply]
    have hB := hBbound (e.symm y)
    have h1 := heA_bound y
    have h2 := he_bound y
    calc
      ‖B ⟨(e.symm y : H), hle (e.symm y).2⟩‖
          ≤ a * ‖A (e.symm y)‖ + b * ‖(e.symm y : H)‖ := hB
      _ ≤ a * ‖y‖ + b * (|r|⁻¹ * ‖y‖) := by
          gcongr
      _ = c₀ * ‖y‖ := by rw [hc₀]; ring
  set K : H →L[ℂ] H := K0.mkContinuous c₀ hK0_bound with hK
  have hK_apply : ∀ y : H, K y = K0 y := fun y ↦ rfl
  have hK_norm : ‖K‖ ≤ c₀ := LinearMap.mkContinuous_norm_le K0 hc₀_nonneg hK0_bound
  have hnegK_norm : ‖(-K : H →L[ℂ] H)‖ < 1 := by rw [norm_neg]; exact lt_of_le_of_lt hK_norm hc₀_lt1
  -- Invert `1 + K` via a Neumann series.
  let u : (H →L[ℂ] H)ˣ := Units.oneSub (-K) hnegK_norm
  have hu_val : (u : H →L[ℂ] H) = 1 + K := by simp [u, Units.val_oneSub, sub_neg_eq_add]
  intro y₀
  set w : H := (↑u⁻¹ : H →L[ℂ] H) y₀ with hw
  have hw_eq : w + K w = y₀ := by
    have h1 : ((u : H →L[ℂ] H) * (↑u⁻¹ : H →L[ℂ] H)) y₀ = y₀ := by
      rw [← Units.val_mul, mul_inv_cancel]
      rfl
    rw [hu_val] at h1
    simpa [w, add_mul, _root_.add_apply, mul_apply_eq_comp] using h1
  set x₀ : A.domain := e.symm w with hx₀
  have hfx₀ : f x₀ = w := e.apply_symm_apply w
  refine ⟨⟨(x₀ : H), by simp [add_domain, sub_domain, smul_domain, one_domain, x₀.2, hle x₀.2]⟩,
    ?_⟩
  have hgoal : A x₀ + B ⟨(x₀ : H), hle x₀.2⟩ - c • (x₀ : H) = y₀ := by
    have hK0x₀ : K0 w = B ⟨(x₀ : H), hle x₀.2⟩ := by rw [hK0_apply]
    rw [← hK0x₀, ← hK_apply]
    have heq : (A x₀ : H) - c • (x₀ : H) = w := by rw [hfx] at hfx₀; exact hfx₀
    calc (A x₀ : H) + K w - c • (x₀ : H) = ((A x₀ : H) - c • (x₀ : H)) + K w := by abel
      _ = w + K w := by rw [heq]
      _ = y₀ := hw_eq
  rw [← hgoal]
  simp [sub_apply, add_apply, smul_apply]

/-- The defect number of `A + B` vanishes at `i r` for `r` large: an immediate consequence of
`katoRellich_sub_I_smul_surjective`, since a full-range operator has trivial deficiency subspace. -/
lemma katoRellich_defectNumber_eq_zero
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {a b : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha1 : a < 1) (hbound : B.IsRelativelyBounded A a b)
    {r : ℝ} (hr : b / (1 - a) < |r|) :
    (A + B).defectNumber (Complex.I * (r : ℂ)) = 0 := by
  have hsurj := katoRellich_sub_I_smul_surjective hA ha0 hb0 ha1 hbound hr
  have hrange : ((A + B) - (Complex.I * (r : ℂ)) • 1).toFun.range = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  show Module.rank ℂ ↥(((A + B) - (Complex.I * (r : ℂ)) • 1).toFun.rangeᗮ) = 0
  rw [hrange]
  exact Submodule.rank_eq_zero.mpr Submodule.top_orthogonal_eq_bot

/-!
### C.2. Transfer to `± i` and conclusion
-/

/-- **The Kato–Rellich theorem.** If `A` is self-adjoint, `B` is symmetric, and `B` is relatively
`A`-bounded with relative bound `(a, b)` satisfying `0 ≤ a < 1` and `0 ≤ b`, then `A + B` (with
domain `A.domain`) is essentially self-adjoint.

The proof shows the defect numbers of `A + B` vanish at `i λ₀` for one large `λ₀ > 0` (and at
`- i λ₀` by the same argument applied to `-λ₀`), then transfers these to `z = ± i` using the
connectedness of the upper/lower open half-planes, which lie entirely inside the regularity domain
of the symmetric operator `A + B` (`IsSymmetric.mem_regularityDomain_of_im_ne_zero`), via
`IsClosable.defectNumber_const`. -/
theorem katoRellich
    {A B : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (hB : B.IsSymmetric) {a b : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha1 : a < 1) (hbound : B.IsRelativelyBounded A a b) :
    (A + B).IsEssentiallySelfAdjoint := by
  have hsym : (A + B).IsSymmetric := IsSymmetric.add (LinearPMap.IsSelfAdjoint.isSymmetric hA) hB
  have hdense : (A + B).HasDenseDomain := by
    have hdomeq : (A + B).domain = A.domain := by
      rw [add_domain, inf_eq_left.mpr hbound.domain_le]
    rw [hasDenseDomain_def, hdomeq]
    exact IsSelfAdjoint.dense_domain hA
  have hclosable : (A + B).IsClosable := hsym.isClosable hdense
  have h1a : (0 : ℝ) < 1 - a := by linarith
  set r₀ : ℝ := b / (1 - a) + 1 with hr₀
  have hr₀gt : b / (1 - a) < r₀ := by linarith
  have hr₀pos : 0 < r₀ := lt_of_le_of_lt (by positivity) hr₀gt
  have hr₀abs : b / (1 - a) < |r₀| := by rwa [abs_of_pos hr₀pos]
  have hr₀abs' : b / (1 - a) < |(-r₀ : ℝ)| := by rwa [abs_neg, abs_of_pos hr₀pos]
  have hplus0 : (A + B).defectNumber (Complex.I * (r₀ : ℂ)) = 0 :=
    katoRellich_defectNumber_eq_zero hA ha0 hb0 ha1 hbound hr₀abs
  have hminus0 : (A + B).defectNumber (Complex.I * ((-r₀ : ℝ) : ℂ)) = 0 :=
    katoRellich_defectNumber_eq_zero hA ha0 hb0 ha1 hbound (r := -r₀) hr₀abs'
  -- transfer `i r₀ ⇝ i` through the upper half-plane
  have hUHP : {z : ℂ | (0:ℝ) < z.im} ⊆ (A + B).regularityDomain :=
    fun z hz ↦ hsym.mem_regularityDomain_of_im_ne_zero (ne_of_gt hz)
  have hIinUHP : Complex.I ∈ {z : ℂ | (0:ℝ) < z.im} := by simp
  have hIr₀inUHP : Complex.I * (r₀ : ℂ) ∈ {z : ℂ | (0:ℝ) < z.im} := by simp [hr₀pos]
  have hmemcc : Complex.I * (r₀ : ℂ) ∈ connectedComponentIn (A + B).regularityDomain Complex.I :=
    (convex_halfSpace_im_gt 0).isPreconnected.subset_connectedComponentIn hIinUHP hUHP hIr₀inUHP
  have hplus : (A + B).defectNumber Complex.I = 0 := by
    rw [hclosable.defectNumber_const hmemcc]; exact hplus0
  -- transfer `- i r₀ ⇝ - i` through the lower half-plane
  have hLHP : {z : ℂ | z.im < (0:ℝ)} ⊆ (A + B).regularityDomain :=
    fun z hz ↦ hsym.mem_regularityDomain_of_im_ne_zero (ne_of_lt hz)
  have hnegIinLHP : (-Complex.I) ∈ {z : ℂ | z.im < (0:ℝ)} := by simp
  have hInegr₀inLHP : Complex.I * ((-r₀ : ℝ) : ℂ) ∈ {z : ℂ | z.im < (0:ℝ)} := by simp [hr₀pos]
  have hmemcc' :
      Complex.I * ((-r₀ : ℝ) : ℂ) ∈ connectedComponentIn (A + B).regularityDomain (-Complex.I) :=
    (convex_halfSpace_im_lt 0).isPreconnected.subset_connectedComponentIn
      hnegIinLHP hLHP hInegr₀inLHP
  have hminus : (A + B).defectNumber (-Complex.I) = 0 := by
    rw [hclosable.defectNumber_const hmemcc']; exact hminus0
  exact hsym.isEssentiallySelfAdjoint_of_defectNumber_eq_zero hdense hplus hminus

end

end

end LinearPMap
