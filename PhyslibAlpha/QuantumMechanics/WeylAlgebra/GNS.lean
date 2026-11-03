/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.TauCeti.Analysis.PositiveDefinite.Kernel.Kolmogorov
public import PhyslibAlpha.QuantumMechanics.WeylAlgebra.QuasiFree
public import PhyslibAlpha.QuantumMechanics.WeylAlgebra.Weyl

/-!
# The GNS representation of the Weyl relations

A positive characteristic function determines a Hilbert space and unitary Weyl operators with a
cyclic vector reproducing it.

## i. Overview

Let `Φ` be positive for the symplectic form `σ`, that is, its kernel `charKernel σ Φ`
is positive semidefinite. Its Kolmogorov decomposition is a Hilbert space `GNS` with vectors
`δ_f`, one for each wave function `f`, such that `⟨δ_f, δ_g⟩ = exp(i σ(f, g) / 2) Φ(g - f)`, and
the `δ_f` span a dense subspace. The vectors `exp(-i σ(h, f) / 2) δ_{h + f}` have the same Gram
kernel, by the symplectic computation, so they define an isometry `W(h)` with
`W(h) δ_f = exp(-i σ(h, f) / 2) δ_{h + f}`, and these satisfy the Weyl relations. The vector
`Ω = δ_0` is cyclic, and `⟨Ω, W(f) Ω⟩ = Φ(f)`.

## ii. Key results

- `GNS`: the Hilbert space of a positive characteristic function.
- `GNS.rep`: the unitary Weyl operators, as a `WeylRep` in the bounded operators.
- `GNS.inner_vacuum`: the vector `Ω = δ_0` reproduces `Φ`.
- `GNS.cyclic`: the vectors `W(f) Ω` span a dense subspace.

## iii. Table of contents

- A. The translations
- B. The Hilbert space and the representation

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Section 5.2.

-/

@[expose] public section

noncomputable section

namespace WeylAlgebra

open Matrix Complex Matrix.PosSemidef
open scoped ComplexOrder

/-!

## A. The translations

-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (σ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (Φ : V → ℂ)

/-- The phase `exp(-i σ(h, f) / 2)` of the translation by `h` of the vector `δ_f`. -/
def phase (h f : V) : ℂ := Complex.exp (-(Complex.I * (σ h f : ℂ)) / 2)

/-- **The kernel is invariant under translation**, up to the phases. -/
lemma charKernel_shift (hσ : ∀ f, σ f f = 0) (h f g : V) :
    star (phase σ h f) * charKernel σ Φ (h + f) (h + g) * phase σ h g = charKernel σ Φ f g := by
  have s1 : σ g h = - σ h g := skew_of_alt hσ h g
  have s2 : σ f h = - σ h f := skew_of_alt hσ h f
  simp only [charKernel, phase, of_apply, Complex.star_def, ← Complex.exp_conj, map_div₀, map_neg,
    map_mul, Complex.conj_I, Complex.conj_ofReal, add_sub_add_left_eq_sub, map_add,
    LinearMap.add_apply, hσ, s2, show (starRingEnd ℂ) 2 = 2 from map_ofNat _ 2]
  have key : ∀ a b c p d : ℂ, a + b + c = d →
      Complex.exp a * (Complex.exp b * p) * Complex.exp c = Complex.exp d * p := by
    intro a b c p d h
    rw [← h, Complex.exp_add, Complex.exp_add]
    ring
  refine key _ _ _ _ _ ?_
  push_cast
  ring

lemma phase_zero (f : V) : phase σ 0 f = 1 := by simp [phase]

lemma phase_neg (hσ : ∀ f, σ f f = 0) (h : V) : phase σ h (-h) = 1 := by simp [phase, hσ]

lemma phase_mul_phase (h k f : V) :
    phase σ h k * phase σ (h + k) f = phase σ h (k + f) * phase σ k f := by
  simp only [phase, ← Complex.exp_add]
  congr 1
  simp only [map_add, LinearMap.add_apply]
  push_cast
  ring

/-!

## B. The Hilbert space and the representation

-/

variable {σ Φ} (hΦ : IsPositive σ Φ) (hσ : ∀ f, σ f f = 0)
include hΦ

/-- **The GNS Hilbert space** of a positive characteristic function: the Kolmogorov decomposition
of its kernel. -/
abbrev GNS : Type _ := Matrix.PosSemidef.KolmogorovSpace (K := charKernel σ Φ) hΦ

/-- The vector `δ_f` of the Hilbert space. -/
def GNS.delta (f : V) : GNS hΦ := kolmogorovFeature (K := charKernel σ Φ) hΦ f

lemma GNS.inner_delta (f g : V) : inner ℂ (GNS.delta hΦ f) (GNS.delta hΦ g) = charKernel σ Φ f g :=
  inner_kolmogorovFeature hΦ f g

/-- Two continuous linear maps of the Hilbert space agreeing on the vectors `δ_f` are equal. -/
lemma GNS.ext {T T' : GNS hΦ →L[ℂ] GNS hΦ} (h : ∀ f, T (GNS.delta hΦ f) = T' (GNS.delta hΦ f)) :
    T = T' :=
  ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2
    (kolmogorovFeature_dense hΦ)) (by rintro _ ⟨f, rfl⟩; exact h f)

include hσ

lemma GNS.inner_shift (h f g : V) :
    inner ℂ (phase σ h f • GNS.delta hΦ (h + f)) (phase σ h g • GNS.delta hΦ (h + g)) =
      charKernel σ Φ f g := by
  rw [inner_smul_left, inner_smul_right, GNS.inner_delta, ← charKernel_shift σ Φ hσ h f g]
  simp only [RCLike.star_def]
  ring

/-- The Weyl operator as a linear isometry of the Hilbert space: the extension of the
translation `δ_f ↦ exp(-i σ(h, f) / 2) δ_{h + f}`. -/
def GNS.isometry (h : V) : GNS hΦ →ₗᵢ[ℂ] GNS hΦ :=
  kolmogorovIsometry hΦ (fun f => phase σ h f • GNS.delta hΦ (h + f)) (GNS.inner_shift hΦ hσ h)

lemma GNS.isometry_delta (h f : V) :
    GNS.isometry hΦ hσ h (GNS.delta hΦ f) = phase σ h f • GNS.delta hΦ (h + f) :=
  kolmogorovIsometry_apply hΦ _ _ f

lemma GNS.isometry_zero : (GNS.isometry hΦ hσ 0).toContinuousLinearMap = 1 :=
  GNS.ext hΦ fun f => by simp [GNS.isometry_delta, phase_zero]

lemma GNS.isometry_isometry (h k : V) :
    (GNS.isometry hΦ hσ h).toContinuousLinearMap * (GNS.isometry hΦ hσ k).toContinuousLinearMap =
      phase σ h k • (GNS.isometry hΦ hσ (h + k)).toContinuousLinearMap :=
  GNS.ext hΦ fun f => by
    simp only [mul_apply_eq_comp, _root_.smul_apply,
      LinearIsometry.coe_toContinuousLinearMap, GNS.isometry_delta, map_smul, smul_smul,
      add_assoc, phase_mul_phase, mul_comm (phase σ k f)]

/-- The Weyl operators of the Hilbert space are unitary and satisfy the Weyl relations: the
**GNS representation** of the Weyl relations. -/
def GNS.rep : WeylRep σ (GNS hΦ →L[ℂ] GNS hΦ) where
  W h := (GNS.isometry hΦ hσ h).toContinuousLinearMap
  W_zero := GNS.isometry_zero hΦ hσ
  star_W h := by
    have h2 := GNS.isometry_isometry hΦ hσ h (-h)
    rw [add_neg_cancel, GNS.isometry_zero, phase_neg σ hσ, one_smul] at h2
    rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    have hx : GNS.isometry hΦ hσ h (GNS.isometry hΦ hσ (-h) x) = x := by
      simpa using congrArg (fun L => L x) h2
    simp only [LinearIsometry.coe_toContinuousLinearMap]
    rw [← LinearIsometry.inner_map_map (GNS.isometry hΦ hσ h), hx]
  W_mul f g := GNS.isometry_isometry hΦ hσ f g

/-- **The cyclic vector `Ω` reproduces the characteristic function**: `⟨Ω, W(f) Ω⟩ = Φ(f)`. -/
lemma GNS.inner_vacuum (f : V) :
    inner ℂ (GNS.delta hΦ 0) ((GNS.rep hΦ hσ).W f (GNS.delta hΦ 0)) = Φ f := by
  change inner ℂ (GNS.delta hΦ 0) (GNS.isometry hΦ hσ f (GNS.delta hΦ 0)) = Φ f
  rw [GNS.isometry_delta, inner_smul_right, GNS.inner_delta]
  simp [charKernel, phase]

/-- **The vacuum is cyclic**: the vectors `W(f) Ω` span a dense subspace. -/
lemma GNS.cyclic :
    (Submodule.span ℂ (Set.range fun f => (GNS.rep hΦ hσ).W f (GNS.delta hΦ 0))).topologicalClosure
      = ⊤ := by
  have : (fun f => (GNS.rep hΦ hσ).W f (GNS.delta hΦ 0)) = GNS.delta hΦ := funext fun f => by
    change GNS.isometry hΦ hσ f (GNS.delta hΦ 0) = _
    simp [GNS.isometry_delta, phase]
  rw [this]
  exact kolmogorovFeature_dense hΦ

end WeylAlgebra

end
