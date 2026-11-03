/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.WeylSymplectic
/-!

# The infinite oscillator lattice

A harmonic oscillator at every site of an arbitrary set, quantised through the Weyl C*-algebra.

## i. Overview

The classical phase space of oscillators at the sites of `L` is the space of pairs `(q, p)` of
finitely supported real fields. Its symplectic form is `σ(f, g) = q_f · p_g - p_f · q_g`. The
fields supported in a set of sites are the region of that set. The Weyl C*-algebra of a region is
the algebra of the oscillators in that region. Algebras of disjoint sets of sites commute, for any
set of sites, so the net is local. The harmonic evolution rotates positions into momenta and is a
symplectic group. It acts on the Weyl C*-algebra by star automorphisms that send `W(f)` to `W` of
the rotated field. Nothing here depends on a Fock representation. The model has no finite volume
cutoff. Anharmonic perturbations are outside this algebra and need separate analysis.

## ii. Key results

- `InfiniteBosons.oscSymp`: the symplectic form of the oscillator lattice.
- `InfiniteBosons.oscillator_locality`: locality of the Weyl C*-net.
- `InfiniteBosons.oscSymp_rot`: the harmonic rotation is symplectic.
- `InfiniteBosons.oscillatorFlow`: the harmonic evolution as an automorphism.

## iii. Table of contents

- A. Phase space
- B. Locality
- C. Harmonic evolution

## iv. References

* B. Nachtergaele, H. Raz, B. Schlein and R. Sims, Lieb-Robinson bounds for harmonic and
  anharmonic lattice systems, Commun. Math. Phys. 286, 1073 (2009).
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- The pairing `Σ_x a_x b_x` of finitely supported real fields. -/
def dotF : (L →₀ ℝ) →ₗ[ℝ] (L →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.lsum ℝ fun x => LinearMap.toSpanSingleton ℝ _ (Finsupp.lapply x)

lemma dotF_single_left (x : L) (c : ℝ) (b : L →₀ ℝ) : dotF (single x c) b = c * b x := by
  simp [dotF, Finsupp.lsum_single]

lemma dotF_comm (a b : L →₀ ℝ) : dotF a b = dotF b a := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp [map_add, LinearMap.add_apply, ha, ha']
  | single x c =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, LinearMap.add_apply, hb, hb']
    | single y d =>
      rw [dotF_single_left, dotF_single_left]
      by_cases h : x = y
      · subst h; simp [mul_comm]
      · simp [Finsupp.single_apply, h, Ne.symm h]


lemma dotF_apply (a b : L →₀ ℝ) : dotF a b = a.sum fun x c => c * b x := by
  simp [dotF, Finsupp.lsum_apply, Finsupp.sum]

lemma dotF_eq_zero_of_disjoint {a b : L →₀ ℝ} {X Y : Set L} (hXY : Disjoint X Y)
    (ha : (a.support : Set L) ⊆ X) (hb : (b.support : Set L) ⊆ Y) : dotF a b = 0 := by
  rw [dotF_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hxX : x ∈ X := ha hx
  have hxY : x ∉ Y := Set.disjoint_left.mp hXY hxX
  have : b x = 0 := by
    by_contra h
    exact hxY (hb (Finsupp.mem_support_iff.mpr h))
  simp [this]

/-- The classical phase space of an oscillator lattice: finitely supported positions and momenta. -/
abbrev FieldSpace (L : Type*) := (L →₀ ℝ) × (L →₀ ℝ)

/-- **The symplectic form of the oscillator lattice**: `σ(f, g) = q_f · p_g - p_f · q_g`. -/
def oscSymp : FieldSpace L →ₗ[ℝ] FieldSpace L →ₗ[ℝ] ℝ :=
  dotF.compl₁₂ (LinearMap.fst ℝ _ _) (LinearMap.snd ℝ _ _) -
    dotF.compl₁₂ (LinearMap.snd ℝ _ _) (LinearMap.fst ℝ _ _)

lemma oscSymp_apply (f g : FieldSpace L) : oscSymp f g = dotF f.1 g.2 - dotF f.2 g.1 := rfl

lemma oscSymp_self (f : FieldSpace L) : oscSymp f f = 0 := by
  rw [oscSymp_apply, dotF_comm f.1 f.2]; ring

/-- The fields supported in the sites `X`. -/
def regionOn (X : Set L) : Set (FieldSpace L) :=
  {f | (f.1.support : Set L) ⊆ X ∧ (f.2.support : Set L) ⊆ X}

lemma neg_mem_regionOn {X : Set L} {f : FieldSpace L} (hf : f ∈ regionOn X) :
    -f ∈ regionOn X := by
  obtain ⟨h1, h2⟩ := hf
  exact ⟨by simpa using h1, by simpa using h2⟩

lemma oscSymp_eq_zero_of_disjoint {X Y : Set L} (hXY : Disjoint X Y) {f g : FieldSpace L}
    (hf : f ∈ regionOn X) (hg : g ∈ regionOn Y) : oscSymp f g = 0 := by
  rw [oscSymp_apply, dotF_eq_zero_of_disjoint hXY hf.1 hg.2, dotF_eq_zero_of_disjoint hXY hf.2 hg.1]
  ring

/-- **Locality of the oscillator lattice C*-net**: the Weyl C*-algebras of disjoint sets of sites
commute. No finiteness of the lattice and no Fock representation is used. -/
theorem oscillator_locality {X Y : Set L} (hXY : Disjoint X Y)
    {a b : HilbertSp (FieldSpace L) →L[ℂ] HilbertSp (FieldSpace L)}
    (ha : a ∈ weylCStarOn oscSymp (regionOn X)) (hb : b ∈ weylCStarOn oscSymp (regionOn Y)) :
    Commute a b :=
  weyl_locality oscSymp oscSymp_self (fun f hf => neg_mem_regionOn hf)
    (fun f hf => neg_mem_regionOn hf)
    (fun f hf g hg => oscSymp_eq_zero_of_disjoint hXY hf hg) ha hb


/-- **The harmonic rotation** of the phase space by the angle `θ`: positions and momenta rotate. -/
def rot (L : Type*) [DecidableEq L] (θ : ℝ) : FieldSpace L →ₗ[ℝ] FieldSpace L :=
  LinearMap.prod
    ((Real.cos θ) • LinearMap.fst ℝ (L →₀ ℝ) (L →₀ ℝ) +
      (Real.sin θ) • LinearMap.snd ℝ (L →₀ ℝ) (L →₀ ℝ))
    ((-Real.sin θ) • LinearMap.fst ℝ (L →₀ ℝ) (L →₀ ℝ) +
      (Real.cos θ) • LinearMap.snd ℝ (L →₀ ℝ) (L →₀ ℝ))

lemma rot_apply (θ : ℝ) (f : FieldSpace L) :
    rot L θ f = (Real.cos θ • f.1 + Real.sin θ • f.2, -Real.sin θ • f.1 + Real.cos θ • f.2) := rfl

lemma rot_zero : rot L (0 : ℝ) = LinearMap.id := by
  refine LinearMap.ext fun f => ?_
  simp [rot_apply]

lemma rot_add (θ φ : ℝ) : rot L (θ + φ) = rot L θ ∘ₗ rot L φ := by
  refine LinearMap.ext fun f => Prod.ext ?_ ?_
  · simp only [rot_apply, LinearMap.comp_apply, Real.cos_add, Real.sin_add, smul_add, smul_smul,
      neg_smul, add_smul, sub_smul]
    module
  · simp only [rot_apply, LinearMap.comp_apply, Real.cos_add, Real.sin_add, smul_add, smul_smul,
      neg_smul, add_smul, sub_smul]
    module

/-- The rotation as a linear equivalence. -/
def rotEquiv (θ : ℝ) : FieldSpace L ≃ₗ[ℝ] FieldSpace L :=
  LinearEquiv.ofLinear (rot L θ) (rot L (-θ))
    (by rw [← rot_add, add_neg_cancel, rot_zero])
    (by rw [← rot_add, neg_add_cancel, rot_zero])

lemma rotEquiv_apply (θ : ℝ) (f : FieldSpace L) : rotEquiv θ f = rot L θ f := rfl

/-- **The rotation is symplectic.** -/
lemma oscSymp_rot (θ : ℝ) (f g : FieldSpace L) : oscSymp (rot L θ f) (rot L θ g) = oscSymp f g := by
  simp only [oscSymp_apply, rot_apply, map_add, map_smul, map_neg, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, LinearMap.neg_apply]
  have h1 := Real.sin_sq_add_cos_sq θ
  linear_combination ((dotF f.1) g.2 - (dotF f.2) g.1) * h1

lemma rotEquiv_add (θ φ : ℝ) : rotEquiv (L := L) (θ + φ) = (rotEquiv φ).trans (rotEquiv θ) := by
  refine LinearEquiv.ext fun f => ?_
  rw [rotEquiv_apply, LinearEquiv.trans_apply, rotEquiv_apply, rotEquiv_apply, rot_add]
  rfl

lemma rotEquiv_zero : rotEquiv (L := L) 0 = LinearEquiv.refl ℝ _ := by
  refine LinearEquiv.ext fun f => ?_
  rw [rotEquiv_apply, rot_zero]
  rfl

/-- **Exact harmonic evolution of the infinite oscillator lattice** as a star automorphism of its
Weyl C*-algebra: the Weyl unitary `W(q, p)` goes to the Weyl unitary of the rotated fields. -/
def oscillatorFlow (θ : ℝ) :
    weylCStarOn (oscSymp (L := L)) Set.univ ≃⋆ₐ[ℂ] weylCStarOn (oscSymp (L := L)) Set.univ :=
  weylAut oscSymp (rotEquiv θ) (oscSymp_rot θ)

lemma oscillatorFlow_weylOp (θ : ℝ) (f : FieldSpace L) :
    ((oscillatorFlow θ ⟨weylOp oscSymp f, weylOp_mem_cstar oscSymp (Set.mem_univ f)⟩ :
      weylCStarOn (oscSymp (L := L)) Set.univ) : HilbertSp (FieldSpace L) →L[ℂ] HilbertSp (FieldSpace L)) =
    weylOp oscSymp (rot L θ f) :=
  weylAut_weylOp oscSymp (rotEquiv θ) (oscSymp_rot θ) f

end InfiniteBosons
