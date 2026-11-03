/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FockNet
/-!

# On-site dynamics of the local net

Arbitrary real on-site energies generate a one-parameter group of star automorphisms of every
local algebra. The automorphisms commute with the inclusions of the net.

## i. Overview

Let `θ x : Ω x → ℝ` be any real function on the configurations of a site. It need not be bounded.
It defines the diagonal self-adjoint operator `Σ_x θ x` on `ℓ²(Ω^X)` for every finite region `X`.
Conjugation by the unitary `exp(i t Σ_x θ x)` is a star automorphism of `B(ℓ²(Ω^X))`. The
unitary is a diagonal phase and needs no domain discussion. The energy of a region splits along
`X ≤ Y` into the energy of `X` and the energy of `Y \ X`. Hence the automorphisms commute with the
inclusions `T ↦ T ⊗ 1`. This is the algebraic dynamics of non-interacting sites. For
`θ x n = ω_x n` it is the harmonic evolution of an oscillator lattice. The group law holds on every
local algebra. Norm continuity in `t` is a separate statement and is not asserted here.

## ii. Key results

- `InfiniteBosons.phaseAut`: conjugation by a diagonal phase unitary.
- `InfiniteBosons.inclE_phaseAut`: phases compatible with a splitting commute with the inclusion.
- `InfiniteBosons.onSiteFlow`: the on-site dynamics of a region.
- `InfiniteBosons.onSiteFlow_add`: the group law.
- `InfiniteBosons.onSiteFlow_incl`: compatibility with the net inclusions.
- `InfiniteBosons.fockRep_harmonicFlow`: the Fock representation intertwines the harmonic on-site
  dynamics with conjugation by `exp(i t Σ ω_x N_x)`.

## iii. Table of contents

- A. Phase automorphisms
- B. On-site energies of regions
- C. The dynamics of the net

## iv. References

* O. Bratteli, D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, Section 6.2.
-/

@[expose] public section

open Finsupp

noncomputable section
namespace InfiniteBosons

lemma phaseEquiv_apply {B : Type*} (c : B → ℂ) (hc : ∀ b, ‖c b‖ = 1) (f : HilbertSp B) (b : B) :
    phaseEquiv c hc f b = c b * f b := rfl

lemma phaseEquiv_symm_apply {B : Type*} (c : B → ℂ) (hc : ∀ b, ‖c b‖ = 1) (f : HilbertSp B)
    (b : B) : (phaseEquiv c hc).symm f b = starRingEnd ℂ (c b) * f b := by
  have : (phaseEquiv c hc).symm f = ⟨fun b => starRingEnd ℂ (c b) * f b,
      memℓp_mul_two (C := 1) (fun b => by simpa using (hc b).le) f⟩ :=
    (LinearIsometryEquiv.symm_apply_eq _).mpr (Subtype.ext (funext fun b => by
      rw [phaseEquiv_apply]
      show f b = c b * (starRingEnd ℂ (c b) * f b)
      have h : c b * starRingEnd ℂ (c b) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc b]; simp
      rw [← mul_assoc, h, one_mul]))
  rw [this]

/-- Conjugation by a diagonal phase unitary. -/
def phaseAut {B : Type*} (c : B → ℂ) (hc : ∀ b, ‖c b‖ = 1) :
    (HilbertSp B →L[ℂ] HilbertSp B) ≃⋆ₐ[ℂ] (HilbertSp B →L[ℂ] HilbertSp B) :=
  (phaseEquiv c hc).conjStarAlgEquiv

lemma phaseAut_congr {B : Type*} {c d : B → ℂ} (hc : ∀ b, ‖c b‖ = 1) (hd : ∀ b, ‖d b‖ = 1)
    (h : c = d) : phaseAut c hc = phaseAut d hd := by
  subst h; rfl

lemma phaseAut_mul {B : Type*} (c d : B → ℂ) (hc : ∀ b, ‖c b‖ = 1) (hd : ∀ b, ‖d b‖ = 1)
    (hcd : ∀ b, ‖c b * d b‖ = 1) (T : HilbertSp B →L[ℂ] HilbertSp B) :
    phaseAut (fun b => c b * d b) hcd T = phaseAut c hc (phaseAut d hd T) := by
  refine ContinuousLinearMap.ext fun ψ => Subtype.ext (funext fun b => ?_)
  simp only [phaseAut, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  have h1 : (phaseEquiv (fun b => c b * d b) hcd).symm ψ =
      (phaseEquiv d hd).symm ((phaseEquiv c hc).symm ψ) :=
    Subtype.ext (funext fun b => by
      rw [phaseEquiv_symm_apply, phaseEquiv_symm_apply, phaseEquiv_symm_apply, map_mul]; ring)
  rw [h1, phaseEquiv_apply, phaseEquiv_apply, phaseEquiv_apply]
  ring

lemma inclE_phaseAut {A B C : Type*} (e : C ≃ A × B) (uA : A → ℂ) (uB : B → ℂ)
    (hA : ∀ a, ‖uA a‖ = 1) (hB : ∀ b, ‖uB b‖ = 1)
    (hC : ∀ c, ‖uA (e c).1 * uB (e c).2‖ = 1)
    (T : HilbertSp A →L[ℂ] HilbertSp A) :
    inclE e (phaseAut uA hA T) = phaseAut (fun c => uA (e c).1 * uB (e c).2) hC (inclE e T) := by
  refine ContinuousLinearMap.ext fun ψ => Subtype.ext (funext fun c => ?_)
  show inclE e (phaseAut uA hA T) ψ c = phaseAut _ hC (inclE e T) ψ c
  rw [inclE_apply]
  simp only [phaseAut, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rw [phaseEquiv_apply, phaseEquiv_apply]
  rw [inclE_apply]
  have hv : slice (e c).2 ((reindexEquiv e).symm
      ((phaseEquiv (fun b => uA (e b).1 * uB (e b).2) hC).symm ψ)) =
      starRingEnd ℂ (uB (e c).2) • (phaseEquiv uA hA).symm
        (slice (e c).2 ((reindexEquiv e).symm ψ)) :=
    Subtype.ext (funext fun a => by
      show slice (e c).2 _ a = starRingEnd ℂ (uB (e c).2) * _
      rw [slice_symm_apply, phaseEquiv_symm_apply, phaseEquiv_symm_apply, slice_symm_apply]
      simp only [Equiv.apply_symm_apply, map_mul]
      ring)
  rw [hv, map_smul]
  show _ = _ * (starRingEnd ℂ (uB (e c).2) * _)
  have h : uB (e c).2 * starRingEnd ℂ (uB (e c).2) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hB]; simp
  calc _ = uA (e c).1 * (uB (e c).2 * starRingEnd ℂ (uB (e c).2)) *
        ((T ((phaseEquiv uA hA).symm (slice (e c).2 ((reindexEquiv e).symm ψ)))) (e c).1) := by
        rw [h, mul_one]
    _ = _ := by ring

open CondensedMatter.QuasiLocal

section OnSite

variable {S : Type*} [DecidableEq S] {Ω : S → Type*}

/-- The on-site energy of a configuration of a finite region. -/
def regionEnergy (θ : ∀ x, Ω x → ℝ) (X : Finset S) (σ : Cfg Ω X) : ℝ := ∑ x : ↥X, θ x.1 (σ x)

lemma regionEnergy_eq (θ : ∀ x, Ω x → ℝ) (X : Finset S) (σ : Cfg Ω X) :
    regionEnergy θ X σ = ∑ l ∈ X, (if h : l ∈ X then θ l (σ ⟨l, h⟩) else 0) := by
  unfold regionEnergy
  rw [← Finset.sum_coe_sort X]
  exact Finset.sum_congr rfl fun x _ => by simp [x.2]

lemma regionEnergy_split {X Y : Finset S} (h : X ≤ Y) (c : Cfg Ω Y) (θ : ∀ x, Ω x → ℝ) :
    regionEnergy θ Y c = regionEnergy θ X (splitEquiv h c).1 +
      regionEnergy θ (Y \ X) (splitEquiv h c).2 := by
  rw [regionEnergy_eq, regionEnergy_eq, regionEnergy_eq]
  have h1 : ∑ l ∈ Y, (if h' : l ∈ Y then θ l (c ⟨l, h'⟩) else 0) =
      ∑ l ∈ Y \ X, (if h' : l ∈ Y then θ l (c ⟨l, h'⟩) else 0) +
      ∑ l ∈ X, (if h' : l ∈ Y then θ l (c ⟨l, h'⟩) else 0) :=
    (Finset.sum_sdiff h).symm
  rw [h1, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun l hl => ?_
    have := h hl
    simp [splitEquiv, hl, this, restr]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Finset.mem_sdiff.1 hl
    simp [splitEquiv, hl, hl'.1, hl'.2]

/-- The phase `exp(i t E)` of a configuration of a region. -/
def onSitePhase (θ : ∀ x, Ω x → ℝ) (t : ℝ) (X : Finset S) (σ : Cfg Ω X) : ℂ :=
  Complex.exp (Complex.I * (t * regionEnergy θ X σ))

lemma norm_onSitePhase (θ : ∀ x, Ω x → ℝ) (t : ℝ) (X : Finset S) (σ : Cfg Ω X) :
    ‖onSitePhase θ t X σ‖ = 1 := by
  unfold onSitePhase
  rw [mul_comm, ← Complex.ofReal_mul]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **On-site dynamics of the local net** for an arbitrary real on-site energy `θ x : Ω x → ℝ`
(possibly unbounded): conjugation of the observables of a region by `exp(i t Σ_x θ_x)`. -/
def onSiteFlow (θ : ∀ x, Ω x → ℝ) (t : ℝ) (X : Finset S) :
    (HilbertSp (Cfg Ω X) →L[ℂ] HilbertSp (Cfg Ω X)) ≃⋆ₐ[ℂ]
      (HilbertSp (Cfg Ω X) →L[ℂ] HilbertSp (Cfg Ω X)) :=
  phaseAut (onSitePhase θ t X) (norm_onSitePhase θ t X)

lemma onSiteFlow_add (θ : ∀ x, Ω x → ℝ) (s t : ℝ) (X : Finset S)
    (T : HilbertSp (Cfg Ω X) →L[ℂ] HilbertSp (Cfg Ω X)) :
    onSiteFlow θ (s + t) X T = onSiteFlow θ s X (onSiteFlow θ t X T) := by
  unfold onSiteFlow
  rw [← phaseAut_mul _ _ (norm_onSitePhase θ s X) (norm_onSitePhase θ t X) (fun σ => by
    rw [norm_mul, norm_onSitePhase, norm_onSitePhase, one_mul])]
  refine congrArg (fun F => F T) (phaseAut_congr _ _ ?_)
  funext σ
  simp only [onSitePhase, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- **The on-site dynamics commutes with the inclusions of the net.** -/
theorem onSiteFlow_incl (θ : ∀ x, Ω x → ℝ) (t : ℝ) {X Y : Finset S} (h : X ≤ Y)
    (T : HilbertSp (Cfg Ω X) →L[ℂ] HilbertSp (Cfg Ω X)) :
    (tensorNet Ω).incl h (onSiteFlow θ t X T) = onSiteFlow θ t Y ((tensorNet Ω).incl h T) := by
  have hC : ∀ c, ‖onSitePhase θ t X (splitEquiv h c).1 * onSitePhase θ t (Y \ X)
      (splitEquiv h c).2‖ = 1 := fun c => by
    rw [norm_mul, norm_onSitePhase, norm_onSitePhase, one_mul]
  have := inclE_phaseAut (splitEquiv h) (onSitePhase θ t X) (onSitePhase θ t (Y \ X))
    (norm_onSitePhase θ t X) (norm_onSitePhase θ t (Y \ X)) hC T
  refine this.trans ?_
  unfold onSiteFlow
  refine congrArg (fun F => F ((tensorNet Ω).incl h T)) (phaseAut_congr hC _ ?_)
  funext c
  simp only [onSitePhase, ← Complex.exp_add]
  congr 1
  rw [regionEnergy_split h c θ]
  push_cast; ring

end OnSite

section Harmonic

variable {L : Type*} [DecidableEq L]

/-- The harmonic energy `Σ_x ω_x α_x` of a finite occupation vector. -/
def harmonicEnergy (ω : L → ℝ) (α : L →₀ ℕ) : ℝ := α.sum fun l n => ω l * n

lemma harmonicEnergy_add (ω : L → ℝ) (a b : L →₀ ℕ) :
    harmonicEnergy ω (a + b) = harmonicEnergy ω a + harmonicEnergy ω b := by
  unfold harmonicEnergy
  refine Finsupp.sum_add_index' (fun l => by simp) (fun l n m => by push_cast; ring)

lemma harmonicEnergy_inOcc (ω : L → ℝ) (X : Finset L) (c : Cfg (fun _ : L => ℕ) X) :
    harmonicEnergy ω (inOcc X c) = regionEnergy (fun x (n : ℕ) => ω x * n) X c := by
  unfold harmonicEnergy regionEnergy
  rw [Finsupp.sum_of_support_subset (inOcc X c) (s := X) (fun l hl => by
    by_contra h; simp [Finsupp.mem_support_iff, inOcc_apply, h] at hl) _ (fun l _ => by simp)]
  rw [← Finset.sum_coe_sort X]
  exact Finset.sum_congr rfl fun x _ => by simp [inOcc_apply, x.2]

/-- The Fock phase `exp(i t Σ ω_x N_x)`. -/
def fockPhase (ω : L → ℝ) (t : ℝ) (α : L →₀ ℕ) : ℂ :=
  Complex.exp (Complex.I * (t * harmonicEnergy ω α))

lemma norm_fockPhase (ω : L → ℝ) (t : ℝ) (α : L →₀ ℕ) : ‖fockPhase ω t α‖ = 1 := by
  unfold fockPhase
  rw [mul_comm, ← Complex.ofReal_mul]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **The harmonic evolution of the Fock space implements the on-site dynamics of the net.** -/
theorem fockRep_harmonicFlow (ω : L → ℝ) (t : ℝ) (X : Finset L)
    (T : HilbertSp (Cfg (fun _ : L => ℕ) X) →L[ℂ] HilbertSp (Cfg (fun _ : L => ℕ) X)) :
    fockRep X (onSiteFlow (fun x (n : ℕ) => ω x * n) t X T) =
      phaseAut (fockPhase ω t) (norm_fockPhase ω t) (fockRep X T) := by
  have hB : ∀ o : OutOcc X, ‖Complex.exp (Complex.I * (t * harmonicEnergy ω o.1))‖ = 1 :=
    fun o => by
      rw [mul_comm, ← Complex.ofReal_mul]; exact Complex.norm_exp_ofReal_mul_I _
  have hC : ∀ α : L →₀ ℕ, ‖onSitePhase (fun x (n : ℕ) => ω x * n) t X ((fockSplit X) α).1 *
      Complex.exp (Complex.I * (t * harmonicEnergy ω ((fockSplit X) α).2.1))‖ = 1 := fun α => by
    rw [norm_mul, norm_onSitePhase, hB, one_mul]
  have := inclE_phaseAut (fockSplit X) (onSitePhase (fun x (n : ℕ) => ω x * n) t X)
    (fun o : OutOcc X => Complex.exp (Complex.I * (t * harmonicEnergy ω o.1)))
    (norm_onSitePhase _ t X) hB hC T
  refine this.trans ?_
  refine congrArg (fun F => F (fockRep X T)) (phaseAut_congr hC _ ?_)
  funext α
  simp only [onSitePhase, fockPhase, ← Complex.exp_add]
  congr 1
  have hα : α = inOcc X ((fockSplit X) α).1 + ((fockSplit X) α).2.1 := by
    have := (fockSplit X).symm_apply_apply α
    simpa [fockSplit] using this.symm
  have hE : harmonicEnergy ω α = regionEnergy (fun x (n : ℕ) => ω x * n) X ((fockSplit X) α).1 +
      harmonicEnergy ω ((fockSplit X) α).2.1 := by
    rw [← harmonicEnergy_inOcc, ← harmonicEnergy_add, ← hα]
  rw [hE]; push_cast; ring

end Harmonic


end InfiniteBosons
