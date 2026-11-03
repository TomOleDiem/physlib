/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.AtomPhotonLattice
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.Representation
/-!

# Growth bounds for the Jaynes-Cummings coupling

## i. Overview

The coupling `g a†σ⁻ + ḡ σ⁺a` is bounded by the photon number plus `|g|²` times the atom number.
The bound is a statement about quadratic forms on the algebraic Fock space.

-/

@[expose] public section

open Finsupp

noncomputable section
namespace InfiniteBosons
variable {L : Type*} [DecidableEq L]

namespace AtomPhotonData

/-- Upper bound of the Jaynes-Cummings coupling by photon and atom number. -/
lemma jaynesCummings_le (x : L) (g : ℂ) (f : SBBasis L →₀ ℂ) :
    (qform (jaynesCummings x g) f).re ≤
      (qform (photonNumber x + ((starRingEnd ℂ g) * g) • atomNumber x) f).re := by
  refine qform_le_of_eq_add (annOpS x + (-g) • lowOpS x) ?_ f
  simp only [jaynesCummings, photonNumber, atomNumber, star_add, star_smul, star_annOpS,
    star_lowOpS, star_neg, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
    Complex.star_def]
  module

/-- Lower bound of the Jaynes-Cummings coupling by photon and atom number. -/
lemma jaynesCummings_ge (x : L) (g : ℂ) (f : SBBasis L →₀ ℂ) :
    -(qform (photonNumber x + ((starRingEnd ℂ g) * g) • atomNumber x) f).re ≤
      (qform (jaynesCummings x g) f).re := by
  have := qform_le_of_eq_add
    (A := (-1 : ℂ) • (photonNumber x + ((starRingEnd ℂ g) * g) • atomNumber x))
    (B := jaynesCummings x g) (annOpS x + g • lowOpS x) (by
      simp only [jaynesCummings, photonNumber, atomNumber, star_add, star_smul, star_annOpS,
        star_lowOpS, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul,
        Complex.star_def]
      module) f
  rw [qform_smul] at this
  simpa using this

lemma qform_photonNumber_nonneg (x : L) (f : SBBasis L →₀ ℂ) :
    0 ≤ (qform (photonNumber x) f).re := by
  have : photonNumber x = star (annOpS x) * annOpS x := by rw [star_annOpS]; rfl
  rw [this, qform_star_mul_self]
  exact pair_self_nonneg _

lemma qform_atomNumber_nonneg (x : L) (f : SBBasis L →₀ ℂ) :
    0 ≤ (qform (atomNumber x) f).re := by
  have : atomNumber x = star (lowOpS x) * lowOpS x := by rw [star_lowOpS]; rfl
  rw [this, qform_star_mul_self]
  exact pair_self_nonneg _

/-- Photon hopping is bounded by the photon numbers of the two cavities. -/
lemma photonHop_le (x y : L) (f : SBBasis L →₀ ℂ) :
    (qform (creOpS x * annOpS y + creOpS y * annOpS x) f).re ≤
      (qform (photonNumber x + photonNumber y) f).re := by
  refine qform_le_of_eq_add (annOpS x + (-1 : ℂ) • annOpS y) ?_ f
  simp only [star_add, star_smul, star_annOpS, photonNumber, mul_add, add_mul, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  simp
  module

lemma photonHop_ge (x y : L) (f : SBBasis L →₀ ℂ) :
    -(qform (photonNumber x + photonNumber y) f).re ≤
      (qform (creOpS x * annOpS y + creOpS y * annOpS x) f).re := by
  have := qform_le_of_eq_add (A := (-1 : ℂ) • (photonNumber x + photonNumber y))
    (B := creOpS x * annOpS y + creOpS y * annOpS x)
    (annOpS x + annOpS y) (by
      simp only [star_add, star_annOpS, photonNumber, mul_add, add_mul, smul_add]
      module) f
  rw [qform_smul] at this
  simpa using this

lemma qform_real_smul (r : ℝ) (A : Adjointable (SBBasis L)) (f : SBBasis L →₀ ℂ) :
    (qform ((r : ℂ) • A) f).re = r * (qform A f).re := by
  rw [qform_smul]; simp

/-- **Site growth bound**: `ω N_ph + ε N_at + JC` is bounded above by a multiple of
`N_ph + N_at`. -/
lemma siteTerm_le (D : AtomPhotonData L) (x : L) (f : SBBasis L →₀ ℂ) :
    (qform (D.siteTerm x) f).re ≤
      (|D.ω x| + 1) * (qform (photonNumber x) f).re +
        (|D.ε x| + Complex.normSq (D.g x)) * (qform (atomNumber x) f).re := by
  have h := jaynesCummings_le x (D.g x) f
  have hp := qform_photonNumber_nonneg x f
  have ha := qform_atomNumber_nonneg x f
  have h1 : D.ω x * (qform (photonNumber x) f).re ≤ |D.ω x| * (qform (photonNumber x) f).re :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hp
  have h2 : D.ε x * (qform (atomNumber x) f).re ≤ |D.ε x| * (qform (atomNumber x) f).re :=
    mul_le_mul_of_nonneg_right (le_abs_self _) ha
  have hc : (starRingEnd ℂ) (D.g x) * D.g x = ((Complex.normSq (D.g x) : ℝ) : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj _
  rw [hc] at h
  unfold siteTerm
  simp only [qform_add, Complex.add_re, qform_real_smul] at h ⊢
  nlinarith [h, h1, h2]

/-- **Bond growth bound** for photon hopping. -/
lemma bondTerm_le (D : AtomPhotonData L) (x y : L) (f : SBBasis L →₀ ℂ) :
    (qform (D.bondTerm x y) f).re ≤
      |D.J x y| * (qform (photonNumber x + photonNumber y) f).re := by
  have hpos : 0 ≤ (qform (photonNumber x + photonNumber y) f).re := by
    rw [qform_add, Complex.add_re]
    exact add_nonneg (qform_photonNumber_nonneg x f) (qform_photonNumber_nonneg y f)
  unfold bondTerm
  split_ifs
  · rw [qform_real_smul]
    have h1 := photonHop_le x y f
    have h2 := photonHop_ge x y f
    rcases le_total 0 (D.J x y) with hJ | hJ
    · rw [abs_of_nonneg hJ]; nlinarith
    · rw [abs_of_nonpos hJ]; nlinarith
  · have h0 : qform (0 : Adjointable (SBBasis L)) f = 0 := by
      simpa using qform_smul 0 (0 : Adjointable (SBBasis L)) f
    rw [h0]; simpa using mul_nonneg (abs_nonneg (D.J x y)) hpos


/-- **Lower site bound.** -/
lemma siteTerm_ge (D : AtomPhotonData L) (x : L) (f : SBBasis L →₀ ℂ) :
    -((|D.ω x| + 1) * (qform (photonNumber x) f).re +
        (|D.ε x| + Complex.normSq (D.g x)) * (qform (atomNumber x) f).re) ≤
      (qform (D.siteTerm x) f).re := by
  have h := jaynesCummings_ge x (D.g x) f
  have hp := qform_photonNumber_nonneg x f
  have ha := qform_atomNumber_nonneg x f
  have h1 : -(|D.ω x| * (qform (photonNumber x) f).re) ≤ D.ω x * (qform (photonNumber x) f).re := by
    nlinarith [neg_abs_le (D.ω x), mul_nonneg (abs_nonneg (D.ω x)) hp,
      mul_le_mul_of_nonneg_right (neg_abs_le (D.ω x)) hp]
  have h2 : -(|D.ε x| * (qform (atomNumber x) f).re) ≤ D.ε x * (qform (atomNumber x) f).re := by
    nlinarith [neg_abs_le (D.ε x), mul_nonneg (abs_nonneg (D.ε x)) ha,
      mul_le_mul_of_nonneg_right (neg_abs_le (D.ε x)) ha]
  have hc : (starRingEnd ℂ) (D.g x) * D.g x = ((Complex.normSq (D.g x) : ℝ) : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj _
  rw [hc] at h
  unfold siteTerm
  simp only [qform_add, Complex.add_re, qform_real_smul] at h ⊢
  nlinarith [h, h1, h2]

/-- **Lower bond bound** for photon hopping. -/
lemma bondTerm_ge (D : AtomPhotonData L) (x y : L) (f : SBBasis L →₀ ℂ) :
    -(|D.J x y| * (qform (photonNumber x + photonNumber y) f).re) ≤
      (qform (D.bondTerm x y) f).re := by
  have hpos : 0 ≤ (qform (photonNumber x + photonNumber y) f).re := by
    rw [qform_add, Complex.add_re]
    exact add_nonneg (qform_photonNumber_nonneg x f) (qform_photonNumber_nonneg y f)
  unfold bondTerm
  split_ifs
  · rw [qform_real_smul]
    have h1 := photonHop_le x y f
    have h2 := photonHop_ge x y f
    rcases le_total 0 (D.J x y) with hJ | hJ
    · rw [abs_of_nonneg hJ]; nlinarith
    · rw [abs_of_nonpos hJ]; nlinarith
  · have h0 : qform (0 : Adjointable (SBBasis L)) f = 0 := by
      simpa using qform_smul 0 (0 : Adjointable (SBBasis L)) f
    rw [h0]; simpa using mul_nonneg (abs_nonneg (D.J x y)) hpos

end AtomPhotonData

end InfiniteBosons
