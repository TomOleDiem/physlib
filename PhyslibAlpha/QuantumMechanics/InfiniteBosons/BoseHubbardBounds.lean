/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.BoseHubbard
/-!

# Growth bounds of the Bose-Hubbard model with pairing

The terms of the Hamiltonian are controlled by number operators as quadratic forms.

## i. Overview

An unbounded polynomial observable is useful when its growth is controlled by the occupation
numbers. The quartic term `N(N-1) = a† a† a a` is positive because it is a square. A repulsive
on-site term is therefore bounded below by `-μ N`. The hopping term is bounded by the number
operators of its two sites. The pairing term is bounded in both directions by
`N_x + |Δ|² (N_y + 1)`, because `N_x + |Δ|² (N_y + 1) ∓ (Δ a_x† a_y† + Δ̄ a_y a_x)` is the square
`(a_x ∓ Δ a_y†)†(a_x ∓ Δ a_y†)`, where the identity `a_y a_y† = N_y + 1` enters. Hence the
quadratic form of every bond term is bounded by the number operators of its two sites, with
constants that depend on the coupling of the bond only. No finite volume is used and the bounds
hold for any lattice.

## ii. Key results

- `InfiniteBosons.qform_numberOp_mul_sub_nonneg`: positivity of `N(N-1)`.
- `InfiniteBosons.BoseHubbardData.siteTerm_ge`: the lower bound of the site term.
- `InfiniteBosons.pairing_le`, `InfiniteBosons.pairing_ge`: the pairing bounds.
- `InfiniteBosons.BoseHubbardData.bondTerm_form_le`: the growth of a bond term.

## iii. Table of contents

- A. The quartic term
- B. Site and pairing terms
- C. Bond terms

## iv. References

* K. Schmüdgen, Unbounded Operator Algebras and Representation Theory, Birkhäuser (1990).
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- `N(N-1) = a† a† a a`, by the canonical commutation relation. -/
lemma numberOp_mul_sub (x : L) :
    numberOp x * numberOp x - numberOp x = creOp x * creOp x * (annOp x * annOp x) := by
  have h := annOp_creOp_comm x x
  simp only [if_true] at h
  unfold numberOp
  calc creOp x * annOp x * (creOp x * annOp x) - creOp x * annOp x
      = creOp x * (annOp x * creOp x) * annOp x - creOp x * annOp x := by noncomm_ring
    _ = creOp x * (creOp x * annOp x + 1) * annOp x - creOp x * annOp x := by rw [h]
    _ = _ := by noncomm_ring

/-- **The quartic on-site term is positive**: `⟨f, N(N-1) f⟩ ≥ 0`. -/
lemma qform_numberOp_mul_sub_nonneg (x : L) (f : FockPre L) :
    0 ≤ (qform (numberOp x * numberOp x - numberOp x) f).re := by
  have : numberOp x * numberOp x - numberOp x = star (annOp x * annOp x) * (annOp x * annOp x) := by
    rw [numberOp_mul_sub, star_mul, star_annOp]
  rw [this, qform_star_mul_self]
  exact pair_self_nonneg _


namespace BoseHubbardData

variable (D : BoseHubbardData L)

lemma qform_sub (A B : adjointable L) (f : FockPre L) :
    qform (A - B) f = qform A f - qform B f := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ B, qform_add, qform_smul]; ring

/-- **Lower bound of the site term**: for a repulsive interaction `U ≥ 0` the site term is bounded
below by `-μ N`, as a quadratic form. -/
lemma siteTerm_ge (x : L) (hU : 0 ≤ D.U x) (f : FockPre L) :
    -(D.μ x) * (qform (numberOp x) f).re ≤ (qform (D.siteTerm x) f).re := by
  unfold siteTerm
  rw [qform_sub, qform_smul, qform_smul, Complex.sub_re, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]
  have h0 := qform_numberOp_mul_sub_nonneg x f
  have hU2 : 0 ≤ D.U x / 2 := by positivity
  nlinarith [mul_nonneg hU2 h0]

end BoseHubbardData


/-- The pairing term `c a_x† a_y† + c̄ a_y a_x`. -/
def pairingTerm (c : ℂ) (x y : L) : adjointable L :=
  c • (creOp x * creOp y) + (starRingEnd ℂ c) • (annOp y * annOp x)

/-- **Upper bound of the pairing term**: `P ≤ N_x + |c|² (N_y + 1)` as quadratic forms. -/
lemma pairing_le (c : ℂ) (x y : L) (f : FockPre L) :
    (qform (pairingTerm c x y) f).re ≤
      (qform (numberOp x + ((starRingEnd ℂ c) * c) • (numberOp y + 1)) f).re := by
  refine qform_le_of_eq_add (annOp x + (-c) • creOp y) ?_ f
  have h := annOp_creOp_comm y y
  simp only [if_true] at h
  simp only [pairingTerm, numberOp, star_add, star_smul, star_annOp, star_creOp, star_neg,
    mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, h, smul_smul, Complex.star_def]
  module

/-- **Lower bound of the pairing term**: `-(N_x + |c|² (N_y + 1)) ≤ P`. -/
lemma pairing_ge (c : ℂ) (x y : L) (f : FockPre L) :
    -(qform (numberOp x + ((starRingEnd ℂ c) * c) • (numberOp y + 1)) f).re ≤
      (qform (pairingTerm c x y) f).re := by
  have := qform_le_of_eq_add (A := (-1 : ℂ) • (numberOp x + ((starRingEnd ℂ c) * c) • (numberOp y + 1)))
    (B := pairingTerm c x y) (annOp x + c • creOp y) (by
      have h := annOp_creOp_comm y y
      simp only [if_true] at h
      simp only [pairingTerm, numberOp, star_add, star_smul, star_annOp, star_creOp,
        mul_add, add_mul, smul_mul_assoc, mul_smul_comm, smul_add, h, smul_smul, Complex.star_def]
      module) f
  rw [qform_smul] at this
  simpa using this

namespace BoseHubbardData

variable (D : BoseHubbardData L)

/-- **Growth of the bond term**: a bond term is bounded above, as a quadratic form, by the number
operators of its two sites. -/
lemma bondTerm_form_le (x y : L) (f : FockPre L) :
    (qform (D.bondTerm x y) f).re ≤
      |D.J x y| * (qform (numberOp x + numberOp y) f).re +
        (qform (numberOp x + ((starRingEnd ℂ (D.Δ x y)) * D.Δ x y) • (numberOp y + 1)) f).re := by
  unfold bondTerm
  split_ifs
  · have e : ((-D.J x y : ℝ) : ℂ) • (creOp x * annOp y + creOp y * annOp x) +
        D.Δ x y • (creOp x * creOp y) + (starRingEnd ℂ (D.Δ x y)) • (annOp y * annOp x) =
        ((-D.J x y : ℝ) : ℂ) • hop x y + pairingTerm (D.Δ x y) x y := by
      unfold hop pairingTerm; abel
    rw [e, qform_add, qform_smul, Complex.add_re, Complex.re_ofReal_mul]
    have h1 := hop_le x y f
    have h2 := hop_ge x y f
    have h3 := pairing_le (D.Δ x y) x y f
    rcases le_total 0 (D.J x y) with hJ | hJ
    · rw [abs_of_nonneg hJ]
      nlinarith
    · rw [abs_of_nonpos hJ]
      nlinarith
  · have hz : qform (0 : adjointable L) f = 0 := by simp [qform, pair_zero_right]
    rw [hz, Complex.zero_re]
    have a1 := qform_numberOp_nonneg x f
    have a2 := qform_numberOp_nonneg y f
    have a3 := pair_self_nonneg f
    have hone : qform (1 : adjointable L) f = pair f f := rfl
    have ht : (starRingEnd ℂ (D.Δ x y)) * D.Δ x y = ((Complex.normSq (D.Δ x y) : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]
    rw [ht]
    simp only [qform_add, qform_smul, Complex.add_re, Complex.re_ofReal_mul, hone]
    have hn := Complex.normSq_nonneg (D.Δ x y)
    have hJ := abs_nonneg (D.J x y)
    nlinarith [mul_nonneg hJ (add_nonneg a1 a2), mul_nonneg hn (add_nonneg a2 a3)]

end BoseHubbardData

end InfiniteBosons
