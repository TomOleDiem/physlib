/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.Concrete

/-!
# The Cayley transform for real spectral data

The Cayley transform turns a real spectral variable into a bounded unitary spectral variable:

`c(x) = (x - i) / (x + i)`.

Its inverse is only needed away from `1`, the point corresponding to infinity.  The inverse is
defined arbitrarily at `1`; on the actual Cayley image it is a genuine inverse.  This file keeps
that elementary measure-transport layer separate from the bounded-unitary spectral theorem.  In
particular, no unbounded theorem is hidden in a definition: a bounded spectral measure supplied by
a concrete construction can be transported here, and the round-trip back to the real measure is
proved exactly.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ComplexOrder InnerProductSpace

namespace OperatorAlgebra

/-- The scalar Cayley transform from the real line to the unit circle. -/
def cayley (x : ℝ) : ℂ := (x - Complex.I) / (x + Complex.I)

/-- The inverse Cayley coordinate, with an arbitrary value at the point `1` (infinity). -/
def cayleyInverse (z : ℂ) : ℝ := if z = 1 then 0 else -z.im / (1 - z.re)

lemma cayley_ne_one (x : ℝ) : cayley x ≠ 1 := by
  intro h
  have hden : (x : ℂ) + Complex.I ≠ 0 := by
    intro hz
    have hi := congrArg Complex.im hz
    norm_num at hi
  have h' : (x : ℂ) - Complex.I = (x : ℂ) + Complex.I := by
    have h' := (div_eq_iff hden).mp (by simpa [cayley] using h)
    simpa using h'
  have hi := congrArg Complex.im h'
  norm_num at hi

lemma cayley_re (x : ℝ) : (cayley x).re = (x ^ 2 - 1) / (x ^ 2 + 1) := by
  rw [cayley, Complex.div_re]
  simp [Complex.normSq, pow_two]
  ring_nf

lemma cayley_im (x : ℝ) : (cayley x).im = (-2 * x) / (x ^ 2 + 1) := by
  rw [cayley, Complex.div_im]
  simp [Complex.normSq, pow_two]
  ring_nf

lemma cayleyInverse_cayley (x : ℝ) : cayleyInverse (cayley x) = x := by
  rw [cayleyInverse, if_neg (cayley_ne_one x), cayley_im, cayley_re]
  have h : x ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg x]
  field_simp
  ring

lemma cayley_norm (x : ℝ) : ‖cayley x‖ = 1 := by
  have hs : ‖cayley x‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, cayley_re, cayley_im]
    have h : x ^ 2 + 1 ≠ 0 := by nlinarith [sq_nonneg x]
    field_simp
    ring
  nlinarith [norm_nonneg (cayley x)]

lemma cayley_cayleyInverse {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    cayley (cayleyInverse z) = z := by
  have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
    calc
      z.re ^ 2 + z.im ^ 2 = Complex.normSq z := by
        simp [Complex.normSq_apply, pow_two]
      _ = ‖z‖ ^ 2 := (Complex.sq_norm z).symm
      _ = 1 := by rw [hz]; norm_num
  have hden : 1 - z.re ≠ 0 := by
    intro hd
    have hre : z.re = 1 := by linarith
    have him : z.im = 0 := by nlinarith [hnorm]
    apply hz1
    apply Complex.ext <;> assumption
  rw [Complex.ext_iff]
  simp only [cayleyInverse, if_neg hz1]
  rw [cayley_re, cayley_im]
  have hx : (-(z.im) / (1 - z.re)) ^ 2 + 1 ≠ 0 := by
    positivity
  have hrel : z.im ^ 2 + (1 - z.re) ^ 2 = 2 * (1 - z.re) := by
    nlinarith [hnorm]
  constructor
  · field_simp [hden]
    nlinarith [hrel]
  · field_simp [hden]
    have hm := congrArg (fun t : ℝ => z.im * t) hnorm
    nlinarith [hm]

lemma measurable_cayley : Measurable cayley := by
  unfold cayley
  fun_prop

lemma measurable_cayleyInverse : Measurable cayleyInverse := by
  unfold cayleyInverse
  apply Measurable.ite
  · exact measurableSet_eq
  · fun_prop
  · fun_prop

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Cayley transform before forgetting that it is bounded. -/
def cayleyPMap (T : H →ₗ.[ℂ] H) : H →ₗ.[ℂ] H :=
  (T - Complex.I • 1) * (T + Complex.I • 1).inverse

lemma cayleyPMap_domain_top {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) :
    (cayleyPMap T).domain = ⊤ := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have heq : T - (-Complex.I) • 1 = T + Complex.I • 1 := by
    exact LinearPMap.ext rfl fun x hf hg => by
      simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
  have hker' : (T - (-Complex.I) • 1).toFun.ker = ⊥ := hres.1
  have hrange' : (T - (-Complex.I) • 1).toFun.range = ⊤ := hres.2.1
  have hker : (T + Complex.I • 1).toFun.ker = ⊥ := by
    rw [heq] at hker'
    exact hker'
  have hrange : (T + Complex.I • 1).toFun.range = ⊤ := by
    rw [heq] at hrange'
    exact hrange'
  have hplusdom : (T + Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.add_domain]
  have hinvdom : (T + Complex.I • 1).inverse.domain = ⊤ := by
    rw [LinearPMap.inverse_domain, hrange]
  rw [cayleyPMap, LinearPMap.mul_def, LinearPMap.compRestricted_domain]
  apply le_antisymm le_top
  intro x hx
  let xi : (T + Complex.I • 1).inverse.domain :=
    ⟨x, by rw [hinvdom]; exact Submodule.mem_top⟩
  have hv' : (T + Complex.I • 1).inverse xi ∈
      (T + Complex.I • 1).domain := by
    rw [← LinearPMap.inverse_range hker]
    exact LinearMap.mem_range_self _ xi
  have hv : (T + Complex.I • 1).inverse xi ∈ T.domain := hplusdom ▸ hv'
  have hxi' : xi ∈
      Submodule.comap (T + Complex.I • 1).inverse.toFun
        (T - Complex.I • 1).domain := by
    change (T + Complex.I • 1).inverse xi ∈ (T - Complex.I • 1).domain
    simpa [LinearPMap.sub_domain] using hv
  refine ⟨xi, hxi', ?_⟩
  rfl

/-- Turn a continuous partial linear map with full domain into a bounded operator on `H`. -/
def topDomainToContinuousLinearMap (A : H →ₗ.[ℂ] H) (hdom : A.domain = ⊤)
    (hc : Continuous A.toFun) : H →L[ℂ] H := by
  let i : H →ₗ[ℂ] A.domain :=
    { toFun := fun x => ⟨x, hdom ▸ Submodule.mem_top⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let L : H →ₗ[ℂ] H := A.toFun.comp i
  have hL : Continuous L := by
    dsimp [L]
    apply hc.comp
    dsimp [i]
    fun_prop
  exact ⟨L, hL⟩

@[nolint unusedArguments]
lemma topDomainToContinuousLinearMap_apply (A : H →ₗ.[ℂ] H) (hdom : A.domain = ⊤)
    (hc : Continuous A.toFun) (x : H) :
    topDomainToContinuousLinearMap A hdom hc x = A ⟨x, hdom ▸ Submodule.mem_top⟩ := by
  rfl

lemma cayleyPMap_eq_one_sub {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) :
    cayleyPMap T = 1 - (2 * Complex.I) • (T + Complex.I • 1).inverse := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have heq : T - (-Complex.I) • 1 = T + Complex.I • 1 := by
    exact LinearPMap.ext rfl fun x hf hg => by
      simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
  have hker : (T + Complex.I • 1).toFun.ker = ⊥ := by
    rw [← heq]
    exact hres.1
  have hrange : (T + Complex.I • 1).toFun.range = ⊤ := by
    rw [← heq]
    exact hres.2.1
  have hinvdom : (T + Complex.I • 1).inverse.domain = ⊤ := by
    rw [LinearPMap.inverse_domain, hrange]
  have hdom := cayleyPMap_domain_top hT
  have hdom' : (1 - (2 * Complex.I) • (T + Complex.I • 1).inverse).domain = ⊤ := by
    simp [LinearPMap.sub_domain, hinvdom]
  apply LinearPMap.ext (hdom.trans hdom'.symm)
  intro x hx hx'
  let xi : (T + Complex.I • 1).inverse.domain :=
    ⟨x, by rw [hinvdom]; exact Submodule.mem_top⟩
  have hxi : (T + Complex.I • 1).inverse xi ∈ (T + Complex.I • 1).domain := by
    rw [← LinearPMap.inverse_range hker]
    exact LinearMap.mem_range_self _ xi
  have hxi_range : (x : H) ∈ LinearMap.range (T + Complex.I • 1).toFun := by
    rw [← LinearPMap.inverse_domain]
    exact xi.property
  obtain ⟨x₀, hx₀⟩ := hxi_range
  have hxy : (T + Complex.I • 1) x₀ = xi := by
    change (T + Complex.I • 1) x₀ = x
    exact hx₀
  have hinv₀ : (T + Complex.I • 1).inverse xi = x₀ :=
    LinearPMap.inverse_apply_eq hker hxy
  have hinv : (T + Complex.I • 1)
      ⟨(T + Complex.I • 1).inverse xi, hxi⟩ = x := by
    have heq : (⟨(T + Complex.I • 1).inverse xi, hxi⟩ :
        (T + Complex.I • 1).domain) = x₀ := Subtype.ext hinv₀
    rw [heq]
    exact hx₀
  let y : (T + Complex.I • 1).domain :=
    ⟨(T + Complex.I • 1).inverse xi, hxi⟩
  have hy : (T + Complex.I • 1) y = x := hinv
  change (T - Complex.I • 1) y = x - (2 * Complex.I) • (y : H)
  rw [← hy]
  simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply]
  module

lemma cayleyPMap_eq_one_sub_minus {T : H →ₗ.[ℂ] H} (hT : IsSelfAdjoint T) :
    cayleyPMap T = 1 - (2 * Complex.I) • (T - (-Complex.I) • 1).inverse := by
  have heq : T - (-Complex.I) • 1 = T + Complex.I • 1 := by
    exact LinearPMap.ext rfl fun x hf hg => by
      simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
  have heq' := congrArg LinearPMap.inverse heq
  rw [cayleyPMap_eq_one_sub hT, ← heq']

/-- The bounded operator represented by the Cayley transform of a self-adjoint `LinearPMap`. -/
noncomputable def cayleyContinuousLinearMap (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    H →L[ℂ] H := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have hinvdom : (T - (-Complex.I) • 1).inverse.domain = ⊤ := by
    rw [LinearPMap.inverse_domain, hres.2.1]
  exact 1 - (2 * Complex.I) •
    topDomainToContinuousLinearMap (T - (-Complex.I) • 1).inverse hinvdom hres.2.2

/-- A bounded operator, viewed as an everywhere-defined `LinearPMap`. -/
def continuousLinearMapToPMap (L : H →L[ℂ] H) : H →ₗ.[ℂ] H :=
  ⟨⊤, L.toLinearMap.comp Submodule.topEquiv.toLinearMap⟩

lemma cayleyPMap_eq_continuousLinearMapToPMap {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) :
    cayleyPMap T = continuousLinearMapToPMap (cayleyContinuousLinearMap T hT) := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have heq : T - (-Complex.I) • 1 = T + Complex.I • 1 := by
    exact LinearPMap.ext rfl fun x hf hg => by
      simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
  calc
    cayleyPMap T = 1 - (2 * Complex.I) • (T - (-Complex.I) • 1).inverse :=
      cayleyPMap_eq_one_sub_minus hT
    _ = continuousLinearMapToPMap (cayleyContinuousLinearMap T hT) := by
      have hinvdom : (T - (-Complex.I) • 1).inverse.domain = ⊤ := by
        rw [LinearPMap.inverse_domain]
        exact hres.2.1
      have hdom : (1 - (2 * Complex.I) •
          (T - (-Complex.I) • 1).inverse).domain = ⊤ := by
        simp [LinearPMap.sub_domain, hinvdom]
      have hdom' : (continuousLinearMapToPMap
          (cayleyContinuousLinearMap T hT)).domain = ⊤ := rfl
      apply LinearPMap.ext (hdom.trans hdom'.symm)
      intro x hx hx'
      simp only [LinearPMap.sub_apply, LinearPMap.smul_apply,
        continuousLinearMapToPMap, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.smul_apply]
      simp [cayleyContinuousLinearMap,
        topDomainToContinuousLinearMap_apply (T - (-Complex.I) • 1).inverse
          hinvdom hres.2.2 x]

lemma cayleyContinuousLinearMap_norm_shift {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) (y : T.domain) :
    ‖T y - Complex.I • (y : H)‖ = ‖T y + Complex.I • (y : H)‖ := by
  have hsym : T.IsSymmetric := LinearPMap.IsSelfAdjoint.isSymmetric hT
  have hreal : (⟪T y, (y : H)⟫_ℂ).im = 0 := by
    exact Complex.conj_eq_iff_im.mp
      ((LinearPMap.isSymmetric_iff_inner_map_self_real).mp hsym y)
  have hsub := norm_sub_sq (𝕜 := ℂ) (T y) (Complex.I • (y : H))
  have hadd := norm_add_sq (𝕜 := ℂ) (T y) (Complex.I • (y : H))
  have hinner : (⟪T y, Complex.I • (y : H)⟫_ℂ).re = 0 := by
    rw [inner_smul_right]
    simp [Complex.mul_re, hreal]
  have hnorm : ‖Complex.I • (y : H)‖ ^ 2 = ‖(y : H)‖ ^ 2 := by
    rw [norm_smul]
    simp
  have hsquares : ‖T y - Complex.I • (y : H)‖ ^ 2 =
      ‖T y + Complex.I • (y : H)‖ ^ 2 := by
    rw [hsub, hadd]
    rw [show RCLike.re ⟪T y, Complex.I • (y : H)⟫_ℂ = 0 from hinner, hnorm]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquares

lemma cayleyContinuousLinearMap_apply_of_mem_range {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) (y : (T + Complex.I • 1).domain) (x : H)
    (hy : (T + Complex.I • 1) y = x) :
    cayleyContinuousLinearMap T hT x = (T - Complex.I • 1) y := by
  have hres := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := -Complex.I) (by norm_num)
  have heq : T - (-Complex.I) • 1 = T + Complex.I • 1 := by
    exact LinearPMap.ext rfl fun x hf hg => by
      simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply,
        neg_smul]
  have hres' := LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hT
    (z := Complex.I) (by norm_num)
  have hker' : (T - Complex.I • 1).toFun.ker = ⊥ := hres'.1
  have hminusdom : (T - (-Complex.I) • 1).domain = T.domain := by
    simp [LinearPMap.sub_domain]
  have hplusdom : (T + Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.add_domain]
  have hyT : (y : H) ∈ T.domain := by
    rw [← hplusdom]
    exact y.property
  have hym : (y : H) ∈ (T - (-Complex.I) • 1).domain := by
    rw [hminusdom]
    exact hyT
  let hyminus : (T - (-Complex.I) • 1).domain :=
    ⟨(y : H), hym⟩
  have hyminus_eq : (T - (-Complex.I) • 1) hyminus = x := by
    have hyt : (⟨(hyminus : H), hminusdom ▸ hyminus.property⟩ : T.domain) =
        ⟨(y : H), hyT⟩ := by
      apply Subtype.ext
      change (y : H) = (y : H)
      rfl
    simp only [LinearPMap.sub_apply, LinearPMap.smul_apply]
    rw [hyt]
    simpa [LinearPMap.add_apply, LinearPMap.smul_apply] using hy
  have hxinv : x ∈ (T - (-Complex.I) • 1).inverse.domain := by
    rw [LinearPMap.inverse_domain]
    rw [hres.2.1]
    exact Submodule.mem_top
  have hminus_inv : (T - (-Complex.I) • 1).inverse
      ⟨x, hxinv⟩ = hyminus := by
    exact LinearPMap.inverse_apply_eq hres.1 hyminus_eq
  have hc : Continuous (T - (-Complex.I) • 1).inverse.toFun := hres.2.2
  simp only [cayleyContinuousLinearMap, sub_apply, smul_apply]
  rw [topDomainToContinuousLinearMap_apply _ _ hc]
  rw [hminus_inv]
  have hycoe : (hyminus : H) = (y : H) := by
    change (y : H) = (y : H)
    rfl
  rw [hycoe]
  change x - (2 * Complex.I) • (y : H) = (T - Complex.I • 1) y
  rw [← hy]
  simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply]
  module

lemma cayleyContinuousLinearMap_norm_map {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) (x : H) :
    ‖cayleyContinuousLinearMap T hT x‖ = ‖x‖ := by
  obtain ⟨y, hy⟩ := LinearPMap.IsSelfAdjoint.sub_smul_surjective hT
    (z := -Complex.I) (by norm_num) x
  have hplusdom : (T + Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.add_domain]
  let yp : (T + Complex.I • 1).domain :=
    ⟨(y : H), by rw [hplusdom]; exact (show (y : H) ∈ T.domain from by
      simpa [LinearPMap.sub_domain] using y.property)⟩
  have hyp : (T + Complex.I • 1) yp = x := by
    simpa [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply] using hy
  rw [cayleyContinuousLinearMap_apply_of_mem_range hT yp x hyp]
  rw [← hyp]
  have hypp : (yp : H) ∈ (T + Complex.I • 1).domain := yp.property
  let yT : T.domain := ⟨(yp : H), hplusdom ▸ hypp⟩
  have hcoey : (yp : H) = (yT : H) := by
    dsimp [yp, yT]
  have hyt : (⟨(yp : H), hplusdom ▸ hypp⟩ : T.domain) = yT := by
    exact Subtype.ext hcoey
  have hshift := cayleyContinuousLinearMap_norm_shift hT yT
  convert hshift using 1 <;>
    simp [LinearPMap.sub_apply, LinearPMap.add_apply, LinearPMap.smul_apply, hyt, hcoey]

lemma cayleyContinuousLinearMap_isometry {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) : Isometry (cayleyContinuousLinearMap T hT) := by
  intro x y
  have hdist : dist (cayleyContinuousLinearMap T hT x)
      (cayleyContinuousLinearMap T hT y) = dist x y := by
    simpa [dist_eq_norm, map_sub] using cayleyContinuousLinearMap_norm_map hT (x - y)
  rw [edist_dist, hdist, edist_dist]

lemma cayleyContinuousLinearMap_surjective {T : H →ₗ.[ℂ] H}
    (hT : IsSelfAdjoint T) : Function.Surjective (cayleyContinuousLinearMap T hT) := by
  intro x
  obtain ⟨y, hy⟩ := LinearPMap.IsSelfAdjoint.sub_smul_surjective hT
    (z := Complex.I) (by norm_num) x
  have hminusdom : (T - Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.sub_domain]
  have hym : (y : H) ∈ T.domain := by
    have h := y.property
    exact hminusdom ▸ h
  have hplusdom : (T + Complex.I • 1).domain = T.domain := by
    simp [LinearPMap.add_domain]
  have hypmem : (y : H) ∈ (T + Complex.I • 1).domain := by
    rw [hplusdom]
    exact hym
  let yp : (T + Complex.I • 1).domain := ⟨(y : H), hypmem⟩
  refine ⟨(T + Complex.I • 1) yp, ?_⟩
  rw [cayleyContinuousLinearMap_apply_of_mem_range hT yp _ rfl]
  simpa [LinearPMap.sub_apply, LinearPMap.smul_apply] using hy

/-- The unitary Cayley transform of a self-adjoint partial operator. -/
noncomputable def cayleyUnitary (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective
    ((cayleyContinuousLinearMap T hT).toLinearMap.toLinearIsometry
      (cayleyContinuousLinearMap_isometry hT))
    (cayleyContinuousLinearMap_surjective hT)

@[simp]
lemma cayleyUnitary_apply (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (x : H) :
    cayleyUnitary T hT x = cayleyContinuousLinearMap T hT x := by
  rfl

end OperatorAlgebra

namespace QuantumMechanics
namespace WOTSpectralMeasure

open OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded spectral measure obtained from a real spectral measure by the Cayley map. -/
def cayleyMap (μS : WOTSpectralMeasure ℝ H) : WOTSpectralMeasure ℂ H :=
  μS.map cayley measurable_cayley

/-- Pull a complex spectral measure back to a real variable using the inverse Cayley coordinate. -/
def cayleyInverseMap (ν : WOTSpectralMeasure ℂ H) : WOTSpectralMeasure ℝ H :=
  ν.map cayleyInverse measurable_cayleyInverse

lemma cayleyInverseMap_cayleyMap (μS : WOTSpectralMeasure ℝ H) :
    cayleyInverseMap (cayleyMap μS) = μS := by
  cases μS with
  | mk vm hp hu =>
    have hvm : ((vm.map cayley).map cayleyInverse) = vm := by
      apply MeasureTheory.VectorMeasure.ext
      intro S hS
      rw [MeasureTheory.VectorMeasure.map_apply _ measurable_cayleyInverse hS]
      rw [MeasureTheory.VectorMeasure.map_apply _ measurable_cayley
        (hS.preimage measurable_cayleyInverse)]
      congr 1
      ext x
      simp [Set.mem_preimage, cayleyInverse_cayley]
    unfold cayleyInverseMap cayleyMap
    rw [QuantumMechanics.WOTSpectralMeasure.mk.injEq]
    exact hvm

/-- The Cayley pushforward is injective on real spectral measures.  Thus a real spectral measure
is completely recoverable from its bounded Cayley-side measure; this is the basic uniqueness
half of the Cayley equivalence used by the unbounded spectral theorem. -/
lemma cayleyMap_injective {μS νS : WOTSpectralMeasure ℝ H}
    (h : cayleyMap μS = cayleyMap νS) : μS = νS := by
  calc
    μS = cayleyInverseMap (cayleyMap μS) :=
      (cayleyInverseMap_cayleyMap μS).symm
    _ = cayleyInverseMap (cayleyMap νS) := congrArg cayleyInverseMap h
    _ = νS := cayleyInverseMap_cayleyMap νS

/-! ## The Cayley equivalence of spectral-measure data -/

/-- The support condition which makes the inverse Cayley coordinate an actual inverse rather than
an arbitrary choice at the point representing infinity. -/
def CayleySupported (ν : WOTSpectralMeasure ℂ H) : Prop :=
  ∀ S : Set ℂ, MeasurableSet S →
    ν S = ν (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1})

lemma cayleyMap_cayleyInverseMap_of_supported
    {ν : WOTSpectralMeasure ℂ H} (hν : CayleySupported ν) :
    cayleyMap (cayleyInverseMap ν) = ν := by
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  change ((ν.map cayleyInverse measurable_cayleyInverse).map cayley measurable_cayley) S = ν S
  rw [(ν.map cayleyInverse measurable_cayleyInverse).map_apply cayley measurable_cayley hS]
  rw [ν.map_apply cayleyInverse measurable_cayleyInverse
    (hS.preimage measurable_cayley)]
  have hL : MeasurableSet (cayleyInverse ⁻¹' cayley ⁻¹' S) :=
    (hS.preimage measurable_cayley).preimage measurable_cayleyInverse
  rw [hν _ hL, hν _ hS]
  congr 1
  ext z
  constructor
  · rintro ⟨hz, hunit⟩
    refine ⟨?_, hunit⟩
    simpa [Set.mem_preimage, cayley_cayleyInverse hunit.1 hunit.2] using hz
  · rintro ⟨hz, hunit⟩
    have hz' : cayley (cayleyInverse z) = z := cayley_cayleyInverse hunit.1 hunit.2
    refine ⟨?_, hunit⟩
    simpa [Set.mem_preimage, hz'] using hz

lemma cayleyMap_cayleySupported (μS : WOTSpectralMeasure ℝ H) :
    CayleySupported (cayleyMap μS) := by
  have hne : MeasurableSet {z : ℂ | z ≠ 1} := by
    rw [show {z : ℂ | z ≠ 1} = ({1} : Set ℂ)ᶜ by ext; simp]
    exact (measurableSet_singleton (1 : ℂ)).compl
  have hunit : MeasurableSet {z : ℂ | ‖z‖ = 1 ∧ z ≠ 1} := by
    exact (measurableSet_eq_fun measurable_norm measurable_const).inter
      hne
  intro S hS
  change (μS.map cayley measurable_cayley) S =
    (μS.map cayley measurable_cayley) (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1})
  rw [μS.map_apply cayley measurable_cayley hS,
    μS.map_apply cayley measurable_cayley
      (MeasurableSet.inter hS hunit)]
  congr 1
  ext x
  constructor
  · intro hx
    exact ⟨hx, cayley_norm x, cayley_ne_one x⟩
  · exact fun hx => hx.1

/-- Cayley transport is an equivalence between real WOT spectral measures and complex WOT
spectral measures supported on the unit circle away from `1`.  This is the reusable measure-level
core of the self-adjoint/unitary correspondence. -/
def cayleyMeasureEquiv :
    WOTSpectralMeasure ℝ H ≃ {ν : WOTSpectralMeasure ℂ H // CayleySupported ν} where
  toFun μS := ⟨cayleyMap μS, cayleyMap_cayleySupported μS⟩
  invFun ν := cayleyInverseMap ν.1
  left_inv μS := cayleyInverseMap_cayleyMap μS
  right_inv ν := Subtype.ext (cayleyMap_cayleyInverseMap_of_supported ν.property)

lemma cayleyMap_weakIntegral {μS : WOTSpectralMeasure ℝ H}
    (g : ℂ → ℝ) (x y : H)
    (hg : AEStronglyMeasurable g ((μS.scalarMeasure x y).variation.map cayley))
    (hgi : (μS.scalarMeasure x y).Integrable (g ∘ cayley)) :
    (cayleyMap μS).weakIntegral g x y = μS.weakIntegral (g ∘ cayley) x y := by
  exact WOTSpectralMeasure.weakIntegral_map (μS := μS) cayley measurable_cayley g x y hg hgi

end WOTSpectralMeasure
end QuantumMechanics

namespace QuantumMechanics
namespace WOTSpectralMeasure

open OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The bounded-unitary spectral interface -/

/-!
The bounded spectral theorem itself does not need the Cayley support condition.  That condition is
only needed when a unitary is going to be pulled back to the real line.  Keep the general output
separate so arbitrary bounded normal operators can consume the same PVM construction.
-/

/-- A bounded normal spectral certificate for `U`: a genuine weak-operator spectral measure
reconstructing `U`. -/
structure BoundedNormalSpectralData (U : H →L[ℂ] H) where
  /-- The spectral measure. -/
  spectralMeasure : WOTSpectralMeasure ℂ H
  reconstruction : ∀ x y : H,
    spectralMeasure.complexWeakIntegral id x y = ⟪y, U x⟫_ℂ

namespace BoundedNormalSpectralData

variable {U : H →L[ℂ] H}

@[ext]
theorem ext {D E : BoundedNormalSpectralData U}
    (h : D.spectralMeasure = E.spectralMeasure) : D = E := by
  cases D with
  | mk μ hμ =>
    cases E with
    | mk ν hν =>
      cases h
      rfl

/- A bounded-integral equality is a convenient representation-independent uniqueness criterion.
The stronger hypothesis is intentional: reconstruction of only the identity multiplier does not
by itself expose the spectral projections, whereas equality for all bounded Borel multipliers does.
    -/
theorem ext_of_boundedIntegral_eq {D E : BoundedNormalSpectralData U}
    (h : ∀ (f : ℂ → ℂ) (hf : Measurable f)
      (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C),
      D.spectralMeasure.boundedIntegral f hf hfb =
        E.spectralMeasure.boundedIntegral f hf hfb) :
    D = E := by
  apply ext
  exact WOTSpectralMeasure.ext_of_boundedIntegral_eq h

end BoundedNormalSpectralData

/-- The exact output required from the bounded unitary spectral theorem.

The support equation records both facts needed to invert the Cayley map: the measure is on the
unit circle and has no mass at `1`, the point representing infinity.  The reconstruction equation
is weak-operator reconstruction for the bounded unitary itself.  This is deliberately a data
structure rather than an axiom-producing definition: constructing it for an arbitrary unitary is
the bounded spectral theorem proper. -/
structure BoundedUnitarySpectralData (u : H ≃ₗᵢ[ℂ] H) where
  /-- The spectral measure. -/
  spectralMeasure : WOTSpectralMeasure ℂ H
  support_away_one : ∀ S : Set ℂ, MeasurableSet S →
    spectralMeasure S = spectralMeasure (S ∩ {z | ‖z‖ = 1 ∧ z ≠ 1})
  reconstruction : ∀ x y : H,
    spectralMeasure.complexWeakIntegral id x y = ⟪y, u x⟫_ℂ

namespace BoundedUnitarySpectralData

variable {u : H ≃ₗᵢ[ℂ] H}

@[ext]
theorem ext {D E : BoundedUnitarySpectralData u}
    (h : D.spectralMeasure = E.spectralMeasure) : D = E := by
  cases D with
  | mk μ hμ hμ' =>
    cases E with
    | mk ν hν hν' =>
      cases h
      rfl

theorem ext_of_boundedIntegral_eq {D E : BoundedUnitarySpectralData u}
    (h : ∀ (f : ℂ → ℂ) (hf : Measurable f)
      (hfb : ∃ C : ℝ, ∀ z, ‖f z‖ ≤ C),
      D.spectralMeasure.boundedIntegral f hf hfb =
        E.spectralMeasure.boundedIntegral f hf hfb) :
    D = E := by
  apply ext
  exact WOTSpectralMeasure.ext_of_boundedIntegral_eq h

variable {u : H ≃ₗᵢ[ℂ] H} (D : BoundedUnitarySpectralData u)

/-- Pull the bounded unitary measure back to the real line. -/
def realSpectralMeasure : WOTSpectralMeasure ℝ H :=
  WOTSpectralMeasure.cayleyInverseMap D.spectralMeasure

lemma cayleyMap_realSpectralMeasure :
    WOTSpectralMeasure.cayleyMap D.realSpectralMeasure = D.spectralMeasure := by
  rw [WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  change ((D.realSpectralMeasure.map cayley measurable_cayley) S) = D.spectralMeasure S
  rw [D.realSpectralMeasure.map_apply cayley measurable_cayley hS]
  change ((D.spectralMeasure.map cayleyInverse measurable_cayleyInverse)
      (cayley ⁻¹' S)) = D.spectralMeasure S
  rw [D.spectralMeasure.map_apply cayleyInverse measurable_cayleyInverse
    (hS.preimage measurable_cayley)]
  have hL : MeasurableSet (cayleyInverse ⁻¹' cayley ⁻¹' S) :=
    (hS.preimage measurable_cayley).preimage measurable_cayleyInverse
  rw [D.support_away_one _ hL, D.support_away_one S hS]
  congr 1
  ext z
  constructor
  · rintro ⟨hz, hunit⟩
    refine ⟨?_, hunit⟩
    simpa [Set.mem_preimage, cayley_cayleyInverse hunit.1 hunit.2] using hz
  · rintro ⟨hz, hunit⟩
    have hz' : cayley (cayleyInverse z) = z := cayley_cayleyInverse hunit.1 hunit.2
    refine ⟨?_, hunit⟩
    simpa [Set.mem_preimage, hz'] using hz

/-- The real measure recovered from bounded Cayley data is unique among real measures with the
same Cayley pushforward. -/
lemma realSpectralMeasure_eq_of_cayleyMap_eq
    {μS : WOTSpectralMeasure ℝ H}
    (hμ : WOTSpectralMeasure.cayleyMap μS = D.spectralMeasure) :
    D.realSpectralMeasure = μS := by
  apply WOTSpectralMeasure.cayleyMap_injective
  calc
    WOTSpectralMeasure.cayleyMap D.realSpectralMeasure = D.spectralMeasure :=
      D.cayleyMap_realSpectralMeasure
    _ = WOTSpectralMeasure.cayleyMap μS := hμ.symm

end BoundedUnitarySpectralData
end WOTSpectralMeasure
end QuantumMechanics

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The Cayley-side unbounded certificate -/

/-- A complete Cayley proof certificate for an unbounded self-adjoint operator.

The bounded-unitary field is the output of the bounded spectral theorem; the second field is the
maximal-domain identity-integral argument.  Keeping both fields explicit makes the dependency
boundary precise while allowing the final unbounded theorem and all downstream affiliated APIs
to be consumed uniformly once those two analytic constructions are supplied. -/
structure CayleySpectralCertificate (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) where
  /-- The bounded unitary spectral certificate for `T`'s Cayley unitary. -/
  bounded : QuantumMechanics.WOTSpectralMeasure.BoundedUnitarySpectralData
    (cayleyUnitary T hT)
  reconstruction : IsWeakSpectralResolution T bounded.realSpectralMeasure

namespace CayleySpectralCertificate

variable {T : H →ₗ.[ℂ] H} {hT : IsSelfAdjoint T}

@[ext]
theorem ext {D E : CayleySpectralCertificate T hT}
    (h : D.bounded.spectralMeasure = E.bounded.spectralMeasure) : D = E := by
  cases D with
  | mk D hD =>
    cases E with
    | mk E hE =>
      cases QuantumMechanics.WOTSpectralMeasure.BoundedUnitarySpectralData.ext h
      rfl

theorem spectralTheorem (D : CayleySpectralCertificate T hT) :
    SelfAdjointSpectralTheorem T D.bounded.realSpectralMeasure where
  isSelfAdjoint := hT
  reconstruction := D.reconstruction

lemma cayley_measure_round_trip (D : CayleySpectralCertificate T hT) :
    QuantumMechanics.WOTSpectralMeasure.cayleyMap D.bounded.realSpectralMeasure =
      D.bounded.spectralMeasure :=
  D.bounded.cayleyMap_realSpectralMeasure

end CayleySpectralCertificate
end OperatorAlgebra

namespace OperatorAlgebra
namespace SelfAdjointSpectralTheorem

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

/-- The bounded Cayley-side spectral measure attached to an unbounded self-adjoint spectral
theorem.  This is the reusable forward half of the Cayley construction; a concrete bounded-unitary
spectral theorem can identify this measure with a Cayley transform constructed independently. -/
@[nolint unusedArguments]
def cayleySpectralMeasure (D : SelfAdjointSpectralTheorem T μS) :
    QuantumMechanics.WOTSpectralMeasure ℂ H :=
  QuantumMechanics.WOTSpectralMeasure.cayleyMap μS

theorem spectralMeasure_eq_of_cayleySpectralMeasure_eq
    {νS : QuantumMechanics.WOTSpectralMeasure ℝ H}
    (D : SelfAdjointSpectralTheorem T μS)
    (E : SelfAdjointSpectralTheorem T νS)
    (h : D.cayleySpectralMeasure = E.cayleySpectralMeasure) :
    μS = νS := by
  exact QuantumMechanics.WOTSpectralMeasure.cayleyMap_injective h

lemma cayleySpectralMeasure_inverse (D : SelfAdjointSpectralTheorem T μS) :
    QuantumMechanics.WOTSpectralMeasure.cayleyInverseMap D.cayleySpectralMeasure = μS := by
  exact QuantumMechanics.WOTSpectralMeasure.cayleyInverseMap_cayleyMap μS

lemma cayleySpectralMeasure_supported (D : SelfAdjointSpectralTheorem T μS) :
    QuantumMechanics.WOTSpectralMeasure.CayleySupported D.cayleySpectralMeasure := by
  exact QuantumMechanics.WOTSpectralMeasure.cayleyMap_cayleySupported μS

lemma cayleySpectralMeasure_round_trip (D : SelfAdjointSpectralTheorem T μS) :
    QuantumMechanics.WOTSpectralMeasure.cayleyMap
      (QuantumMechanics.WOTSpectralMeasure.cayleyInverseMap D.cayleySpectralMeasure) =
        D.cayleySpectralMeasure := by
  exact QuantumMechanics.WOTSpectralMeasure.cayleyMap_cayleyInverseMap_of_supported
    D.cayleySpectralMeasure_supported

end SelfAdjointSpectralTheorem
end OperatorAlgebra
