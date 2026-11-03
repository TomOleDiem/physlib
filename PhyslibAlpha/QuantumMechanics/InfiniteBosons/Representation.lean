/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.PolynomialAlgebra
/-!

# The Fock representation as an O*-algebra and quadratic-form bounds

The polynomial CCR algebra acts on the algebraic Fock space, a common invariant domain, and its
elements are bounded by number operators as quadratic forms.

## i. Overview

An O*-algebra is an algebra of operators that all map a fixed dense domain into itself, together
with their adjoints. The algebraic Fock space is such a domain for the polynomial CCR algebra, and
the formal adjoint of every polynomial is again defined on it. This makes products of unbounded
operators legitimate on the domain. A polynomial observable has a quadratic form `f ↦ ⟨f, A f⟩` on
the domain. Operators are compared as quadratic forms. The hopping term is controlled by the number
operators of the two sites,

`-(N_x + N_y) ≤ a_x† a_y + a_y† a_x ≤ N_x + N_y`,

because `N_x + N_y ∓ (a_x† a_y + a_y† a_x)` is the square `(a_x ∓ a_y)†(a_x ∓ a_y)`. The reference
operators `K_X = 1 + Σ_{x ∈ X} N_x` of finite regions measure the growth of observables.

## ii. Key results

- `InfiniteBosons.qform`: the quadratic form of an adjointable operator.
- `InfiniteBosons.hop_le`, `InfiniteBosons.hop_ge`: the hopping bounds.
- `InfiniteBosons.qform_numberOp_nonneg`: positivity of the number operator.

## iii. Table of contents

- A. Quadratic forms
- B. Bounds for hopping

## iv. References

* K. Schmüdgen, Unbounded Operator Algebras and Representation Theory, Birkhäuser (1990).
* J. Dereziński and C. Gérard, Mathematics of Quantization and Quantum Fields, Cambridge
  University Press (2013).
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {β : Type*} [DecidableEq β]

lemma pair_self_nonneg (f : (β →₀ ℂ)) : 0 ≤ (pair f f).re := by
  unfold pair
  simp only [Finsupp.sum, Complex.re_sum]
  refine Finset.sum_nonneg fun α _ => ?_
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (f α).re, sq_nonneg (f α).im]

/-- The quadratic form `f ↦ ⟨f, A f⟩` of an adjointable operator, on the invariant domain. -/
def qform (A : Adjointable β) (f : (β →₀ ℂ)) : ℂ := pair f (A.1.1 f)

lemma qform_add (A B : Adjointable β) (f : (β →₀ ℂ)) :
    qform (A + B) f = qform A f + qform B f := by
  unfold qform
  show pair f (A.1.1 f + B.1.1 f) = _
  rw [pair_add_right]

lemma qform_smul (c : ℂ) (A : Adjointable β) (f : (β →₀ ℂ)) :
    qform (c • A) f = c * qform A f := by
  unfold qform
  show pair f (c • A.1.1 f) = _
  rw [pair_smul_right]

lemma qform_star_mul_self (A : Adjointable β) (f : (β →₀ ℂ)) :
    qform (star A * A) f = pair (A.1.1 f) (A.1.1 f) := by
  unfold qform
  show pair f (toEnd (MulOpposite.unop A.1.2) (A.1.1 f)) = _
  rw [← mem_adjointable.mp A.2]

/-- Quadratic form bound: if `B = A + C* C` then `⟨f, A f⟩ ≤ ⟨f, B f⟩`. -/
lemma qform_le_of_eq_add {A B : Adjointable β} (C : Adjointable β) (h : B = A + star C * C)
    (f : (β →₀ ℂ)) : (qform A f).re ≤ (qform B f).re := by
  rw [h, qform_add, Complex.add_re, qform_star_mul_self]
  linarith [pair_self_nonneg (C.1.1 f)]

variable {L : Type*} [DecidableEq L]

/-- The hopping term `a_x† a_y + a_y† a_x`. -/
def hop (x y : L) : adjointable L := creOp x * annOp y + creOp y * annOp x

lemma hop_le (x y : L) (f : FockPre L) :
    (qform (hop x y) f).re ≤ (qform (numberOp x + numberOp y) f).re := by
  refine qform_le_of_eq_add (annOp x + (-1 : ℂ) • annOp y) ?_ f
  simp only [star_add, star_smul, star_annOp, hop, numberOp, mul_add, add_mul, smul_mul_assoc,
    mul_smul_comm, smul_smul]
  simp
  module


lemma hop_ge (x y : L) (f : FockPre L) :
    -(qform (numberOp x + numberOp y) f).re ≤ (qform (hop x y) f).re := by
  have := qform_le_of_eq_add (A := (-1 : ℂ) • (numberOp x + numberOp y)) (B := hop x y)
    (annOp x + annOp y) (by
      simp only [star_add, star_annOp, hop, numberOp, mul_add, add_mul, smul_add]
      module) f
  rw [qform_smul] at this
  simpa using this


/-- The number operator is positive as a quadratic form. -/
lemma qform_numberOp_nonneg (x : L) (f : FockPre L) : 0 ≤ (qform (numberOp x) f).re := by
  have : numberOp x = star (annOp x) * annOp x := by rw [star_annOp]; rfl
  rw [this, qform_star_mul_self]
  exact pair_self_nonneg _

/-- **The domain is invariant**: every formally adjointable operator maps the algebraic Fock space
into itself, and so does its formal adjoint. -/
lemma domain_invariant (A : adjointable L) (f : FockPre L) :
    A.1.1 f ∈ (⊤ : Submodule ℂ (FockPre L)) ∧
      toEnd (MulOpposite.unop A.1.2) f ∈ (⊤ : Submodule ℂ (FockPre L)) :=
  ⟨Submodule.mem_top, Submodule.mem_top⟩

end InfiniteBosons
