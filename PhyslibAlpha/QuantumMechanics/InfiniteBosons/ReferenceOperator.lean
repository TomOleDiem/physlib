/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.Representation
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.BoseHubbard
/-!

# Reference operators `K_X = 1 + Σ_{x ∈ X} N_x`

The reference operator of a finite set of modes controls the growth of local polynomial
observables.

## i. Overview

`K_X` is a self-adjoint element of the polynomial algebra. Its quadratic form dominates the norm
squared. The hopping bounds of `Representation.lean` read `±hop x y ≤ K_{x,y}`.

## ii. Key results

- `InfiniteBosons.refOp`: the reference operator.
- `InfiniteBosons.pair_le_qform_refOp`: `‖f‖² ≤ ⟨f, K_X f⟩`.
- `InfiniteBosons.hop_le_refOp`, `InfiniteBosons.hop_ge_refOp`: hopping is bounded by `K`.

## iii. Table of contents

- A. Definition
- B. Bounds

## iv. References

* J. Dereziński, C. Gérard, Mathematics of Quantization and Quantum Fields, Cambridge University
  Press (2013), Section 17.1.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- The reference operator `K_X = 1 + Σ_{x ∈ X} N_x`. -/
def refOp (X : Finset L) : adjointable L := 1 + ∑ x ∈ X, numberOp x

lemma qform_sum {β : Type*} [DecidableEq β] {ι : Type*} (s : Finset ι) (A : ι → Adjointable β)
    (f : β →₀ ℂ) : qform (∑ i ∈ s, A i) f = ∑ i ∈ s, qform (A i) f := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := qform_smul 0 (1 : Adjointable β) f
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, qform_add, ih]

lemma qform_one {β : Type*} [DecidableEq β] (f : β →₀ ℂ) : qform (1 : Adjointable β) f = pair f f :=
  rfl

lemma star_refOp (X : Finset L) : star (refOp X) = refOp X := by
  unfold refOp
  rw [star_add, star_one, star_sum]
  simp [BoseHubbardData.star_numberOp]

/-- The reference operator dominates the identity. -/
lemma pair_le_qform_refOp (X : Finset L) (f : FockPre L) :
    (pair f f).re ≤ (qform (refOp X) f).re := by
  unfold refOp
  rw [qform_add, qform_sum, qform_one, Complex.add_re, Complex.re_sum]
  have : 0 ≤ ∑ x ∈ X, (qform (numberOp x) f).re :=
    Finset.sum_nonneg fun x _ => qform_numberOp_nonneg x f
  linarith

lemma qform_numberOp_le_refOp {X : Finset L} {x : L} (hx : x ∈ X) (f : FockPre L) :
    (qform (numberOp x) f).re ≤ (qform (refOp X) f).re := by
  unfold refOp
  rw [qform_add, qform_sum, qform_one, Complex.add_re, Complex.re_sum]
  have h1 : (qform (numberOp x) f).re ≤ ∑ y ∈ X, (qform (numberOp y) f).re :=
    Finset.single_le_sum (f := fun y => (qform (numberOp y) f).re)
      (fun y _ => qform_numberOp_nonneg y f) hx
  have := pair_self_nonneg f
  linarith

/-- Hopping between two modes of `X` is bounded above by `K_X`. -/
lemma hop_le_refOp {X : Finset L} {x y : L} (hxy : x ≠ y) (hx : x ∈ X) (hy : y ∈ X)
    (f : FockPre L) : (qform (hop x y) f).re ≤ (qform (refOp X) f).re := by
  refine (hop_le x y f).trans ?_
  rw [qform_add, Complex.add_re]
  unfold refOp
  rw [qform_add, qform_sum, qform_one, Complex.add_re, Complex.re_sum]
  have h2 : (qform (numberOp x) f).re + (qform (numberOp y) f).re ≤
      ∑ z ∈ X, (qform (numberOp z) f).re := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun z => (qform (numberOp z) f).re)
      (show ({x, y} : Finset L) ⊆ X by
        intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption)
      (fun z _ _ => qform_numberOp_nonneg z f)
    simpa [Finset.sum_pair hxy] using this
  have := pair_self_nonneg f
  linarith

lemma hop_ge_refOp {X : Finset L} {x y : L} (hxy : x ≠ y) (hx : x ∈ X) (hy : y ∈ X)
    (f : FockPre L) : -(qform (refOp X) f).re ≤ (qform (hop x y) f).re := by
  refine le_trans ?_ (hop_ge x y f)
  rw [neg_le_neg_iff, qform_add, Complex.add_re]
  unfold refOp
  rw [qform_add, qform_sum, qform_one, Complex.add_re, Complex.re_sum]
  have h2 : (qform (numberOp x) f).re + (qform (numberOp y) f).re ≤
      ∑ z ∈ X, (qform (numberOp z) f).re := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun z => (qform (numberOp z) f).re)
      (show ({x, y} : Finset L) ⊆ X by
        intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption)
      (fun z _ _ => qform_numberOp_nonneg z f)
    simpa [Finset.sum_pair hxy] using this
  have := pair_self_nonneg f
  linarith

end InfiniteBosons
