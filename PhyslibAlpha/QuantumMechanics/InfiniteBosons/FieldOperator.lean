/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.Locality
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.OscillatorLattice
/-!

# Field operators and the symplectic form

The field operator `φ(f)` of a phase space vector is a self-adjoint element of the polynomial
algebra. Its commutator is the symplectic form of the oscillator lattice.

## i. Overview

A phase space vector `f = (q, p)` of finite support defines the field operator
`φ(f) = Σ_x (c_x a_x + c̄_x a_x†)` with `c_x = -(p_x + i q_x)/√2`. The canonical commutation
relations of the polynomial algebra give `[φ(f), φ(g)] = i σ(f, g)` with
`σ(f, g) = q_f · p_g - p_f · q_g`. This is the infinitesimal form of the Weyl relations
`W(f) W(g) = exp(-iσ(f, g)/2) W(f + g)` of the Weyl net of `WeylCStar.lean` for `W(f) = exp(iφ(f))`.
It identifies the symplectic space of the Weyl net with the commutator form of the polynomial
algebra `P(L)`. The exponentials are not constructed here: they need the essential self-adjointness
of `φ(f)` which is a separate statement.

## ii. Key results

- `InfiniteBosons.fieldTerm`: the single-mode term `c a_x + c̄ a_x†`.
- `InfiniteBosons.fieldOp`: the field operator over a finite set of modes.
- `InfiniteBosons.fieldOp_commutator`: the commutator as a sum over modes.
- `InfiniteBosons.fieldOp_commutator_oscSymp`: the commutator is `i σ(f, g)`.

## iii. Table of contents

- A. Single-mode terms
- B. The field operator
- C. The commutator

## iv. References

* J. Dereziński, C. Gérard, Mathematics of Quantization and Quantum Fields, Cambridge University
  Press (2013), Section 8.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- The single-site combination `c a_x + c̄ a_x†`. -/
def fieldTerm (x : L) (c : ℂ) : adjointable L := c • annOp x + (starRingEnd ℂ c) • creOp x

lemma fieldTerm_comm_same (x : L) (c d : ℂ) :
    fieldTerm x c * fieldTerm x d - fieldTerm x d * fieldTerm x c =
      (c * starRingEnd ℂ d - starRingEnd ℂ c * d) • (1 : adjointable L) := by
  have h1 := annOp_creOp_comm x x
  simp only [if_true] at h1
  have h2 : creOp x * annOp x = annOp x * creOp x - 1 := by rw [h1]; abel
  simp only [fieldTerm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [h1, h2]
  module

lemma fieldTerm_comm_ne {x y : L} (hxy : x ≠ y) (c d : ℂ) :
    fieldTerm x c * fieldTerm y d = fieldTerm y d * fieldTerm x c := by
  simp only [fieldTerm, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    annOp_comm_annOp x y, creOp_comm_creOp x y, annOp_comm_creOp hxy, creOp_comm_annOp hxy]
  module


lemma commutator_sum {R ι : Type*} [Ring R] [DecidableEq ι] (S : Finset ι) (A B : ι → R)
    (h : ∀ x y, x ≠ y → A x * B y = B y * A x) :
    (∑ x ∈ S, A x) * (∑ y ∈ S, B y) - (∑ y ∈ S, B y) * (∑ x ∈ S, A x) =
      ∑ x ∈ S, (A x * B x - B x * A x) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun y x => B y * A x),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single x]
  · intro y _ hyx
    rw [h x y (Ne.symm hyx), sub_self]
  · intro hx'; exact absurd hx hx'

/-- The coefficient of `a_x` in the field operator of the phase space vector `f = (q, p)`. -/
def fieldCoeff (q p : L →₀ ℝ) (x : L) : ℂ := ((-p x : ℝ) + Complex.I * (-q x : ℝ)) / Real.sqrt 2

/-- The field operator `φ(f) = Σ_{x ∈ S} (c_x a_x + c̄_x a_x†)` of a phase space vector. -/
def fieldOp (S : Finset L) (q p : L →₀ ℝ) : adjointable L :=
  ∑ x ∈ S, fieldTerm x (fieldCoeff q p x)

/-- **The commutator of two field operators is the symplectic form.**
`[φ(f), φ(g)] = i σ_S(f, g)`, with `σ_S = Σ_{x ∈ S} (q_x p'_x - p_x q'_x)`. -/
theorem fieldOp_commutator (S : Finset L) (q p q' p' : L →₀ ℝ) :
    fieldOp S q p * fieldOp S q' p' - fieldOp S q' p' * fieldOp S q p =
      (Complex.I * ((∑ x ∈ S, (q x * p' x - p x * q' x) : ℝ) : ℂ)) • (1 : adjointable L) := by
  unfold fieldOp
  rw [commutator_sum S _ _ (fun x y hxy => fieldTerm_comm_ne hxy _ _)]
  simp only [fieldTerm_comm_same]
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [fieldCoeff]
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hs; norm_num at hs
  simp only [map_div₀, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, map_neg]
  field_simp
  ring_nf
  rw [hs]


lemma dotF_eq_sum (a b : L →₀ ℝ) (S : Finset L) (hS : a.support ⊆ S) :
    dotF a b = ∑ x ∈ S, a x * b x := by
  conv_lhs => rw [← Finsupp.sum_single a]
  rw [Finsupp.sum, map_sum]
  simp only [LinearMap.sum_apply, dotF_single_left]
  exact Finset.sum_subset hS (fun x _ hx => by simp [Finsupp.notMem_support_iff.mp hx]) |>.trans rfl

/-- **The field commutator is the symplectic form of the oscillator lattice.** If the supports of
`f` and `g` lie in `S` then `[φ(f), φ(g)] = i σ(f, g)`. -/
theorem fieldOp_commutator_oscSymp (S : Finset L) (f g : FieldSpace L)
    (hf1 : f.1.support ⊆ S) (hf2 : f.2.support ⊆ S) :
    fieldOp S f.1 f.2 * fieldOp S g.1 g.2 - fieldOp S g.1 g.2 * fieldOp S f.1 f.2 =
      (Complex.I * (oscSymp f g : ℂ)) • (1 : adjointable L) := by
  rw [fieldOp_commutator, oscSymp_apply, dotF_eq_sum _ _ S hf1, dotF_eq_sum _ _ S hf2,
    ← Finset.sum_sub_distrib]

lemma star_fieldTerm (x : L) (c : ℂ) : star (fieldTerm x c) = fieldTerm x c := by
  simp only [fieldTerm, star_add, star_smul, star_annOp, star_creOp, Complex.star_def,
    Complex.conj_conj]
  rw [add_comm]

/-- **The field operator is self-adjoint** as an element of the polynomial algebra. -/
lemma star_fieldOp (S : Finset L) (q p : L →₀ ℝ) : star (fieldOp S q p) = fieldOp S q p := by
  unfold fieldOp
  rw [star_sum]
  exact Finset.sum_congr rfl fun x _ => star_fieldTerm x _

end InfiniteBosons
