/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Meta.TODO.Basic
public import Physlib.QuantumMechanics.OperatorAlgebra.Lie
public import Mathlib.Algebra.Symmetrized

/-!

# Jordan structure on observables

The symmetric part of a C⋆-algebra product, the **Jordan product** `a ∘ b = ½(ab + ba)`, also
lands back in the observables: commutative, generally non-associative. Together with the Lie
bracket `⁅·,·⁆ₒ` of `OperatorAlgebra.Lie` it recovers the original product:
`ab = a ∘ b + (i/2) ⁅a, b⁆ₒ` (`mul_eq_jordan_add_obsBracket`). So schematically, a C⋆-algebra gives
Jordan geometry (states, positivity, the observable order) plus Lie dynamics (commutators,
generators, symmetry) on the *same* underlying real vector space of observables.

This is useful conceptually — e.g. the qubit's Jordan product is the Euclidean dot product and
its Lie bracket is the cross product (`Qubit.σ_mul_σ`/`Qubit.σ_commutator` are exactly this,
specialized) — but stays a *derived* structure here, not a replacement for the C⋆-algebra as the
foundation.

`∘` satisfies the Jordan identity, in the shape Mathlib itself uses
(`IsCommJordan.lmul_comm_rmul_rmul : a * b * (a * a) = a * (b * (a * a))`) — proved not by hand
but by transporting it from Mathlib's symmetrization construction `Aˢʸᵐ`, i.e. `SymAlg`
(`Mathlib.Algebra.Symmetrized`). For any `[Ring A] [Invertible (2 : A)]`, `Aˢʸᵐ` is `IsCommJordan`
*for free*, no proof obligation at all — `∘` is exactly `SymAlg.sym_mul_sym` specialized, and
`sym_coe_jordan` shows `jordan` and `Aˢʸᵐ`'s multiplication agree under `SymAlg.sym`. `Invertible
(2 : A)` itself needs constructing (`(2⁻¹ : ℝ) • (1 : A)`, not available for a general
`CStarAlgebra A` off the shelf) — done once below, safely: it is a *new* instance, nothing in
Mathlib already provides `Invertible (2 : A)` for a general `CStarAlgebra A` to diamond against.

What's *not* done is registering `Mul (Observable A) := jordan` and an `IsCommJordan (Observable
A)` instance outright — `selfAdjoint` already carries its own global `Mul` instance whenever `A`
happens to be commutative (`Mathlib.Algebra.Star.SelfAdjoint`, `NonUnitalCommRing` case), and a
second, merely propositionally-equal `Mul (Observable A)` from `jordan` would diamond with it.
Left as a `TODO` below; the Jordan identity itself no longer needs it.

-/

@[expose] public section

namespace OperatorAlgebra

variable {A : Type*} [CStarAlgebra A]

namespace Observable

/-- `ab + ba` is self-adjoint whenever `a` and `b` are — no commutativity of `a` and `b` needed. -/
lemma isSelfAdjoint_mul_add_mul {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint (a * b + b * a) := by
  rw [isSelfAdjoint_iff, star_add, star_mul, star_mul, ha.star_eq, hb.star_eq, add_comm]

/-- The Jordan product `a ∘ b = ½(ab + ba)`: commutative, generally non-associative, the
symmetric part of the algebra product. -/
noncomputable def jordan (a b : Observable A) : Observable A :=
  (2⁻¹ : ℝ) •
    (⟨(a : A) * b + (b : A) * a, isSelfAdjoint_mul_add_mul a.property b.property⟩ : Observable A)

lemma coe_jordan (a b : Observable A) :
    (jordan a b : A) = (2⁻¹ : ℝ) • ((a : A) * b + (b : A) * a) :=
  rfl

/-- The algebra product decomposes into its Jordan (symmetric) and Lie (antisymmetric) parts:
`ab = a ∘ b + (i/2) ⁅a, b⁆ₒ`. -/
lemma mul_eq_jordan_add_obsBracket (a b : Observable A) :
    (a : A) * b = (jordan a b : A) + (Complex.I / 2) • (obsBracket a b : A) := by
  rw [coe_jordan, coe_obsBracket, smul_smul]
  have hI : (Complex.I / 2 * Complex.I) = (-2⁻¹ : ℂ) := by
    rw [div_mul_eq_mul_div, Complex.I_mul_I]; ring
  rw [hI]
  module

/-! ### `∘` makes the observables a Jordan algebra

`jordan_comm`/`jordan_self`/`add_jordan`/`jordan_smul` are transported from the corresponding fact
about `A`'s own product, in the same style as the Lie side (`OperatorAlgebra.Lie`). The Jordan
identity itself (`jordan_lmul_comm_rmul_rmul`) is transported instead from `Aˢʸᵐ`'s already-proven
`IsCommJordan` instance — see the module docstring. -/

lemma jordan_comm (a b : Observable A) : jordan a b = jordan b a := by
  apply Subtype.ext
  simp only [coe_jordan, add_comm]

/-- `a ∘ a = a * a`: the one place the `2⁻¹` in the Jordan product disappears for free, since both
terms of `coe_jordan`'s sum coincide when the two arguments are equal. -/
lemma jordan_self (a : Observable A) : (jordan a a : A) = (a : A) * a := by
  rw [coe_jordan]
  module

lemma add_jordan (a b c : Observable A) : jordan (a + b) c = jordan a c + jordan b c := by
  apply Subtype.ext
  simp only [coe_jordan, AddSubgroup.coe_add, mul_add, add_mul]
  module

lemma jordan_smul (t : ℝ) (a b : Observable A) : jordan a (t • b) = t • jordan a b := by
  apply Subtype.ext
  show (jordan a (t • b) : A) = ((t • jordan a b : Observable A) : A)
  simp only [coe_jordan, selfAdjoint.val_smul]
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, smul_smul, smul_smul, mul_comm (2⁻¹ : ℝ) t]

/-! ### The Jordan identity, transported from `Aˢʸᵐ`

`Aˢʸᵐ` (`SymAlg`, `Mathlib.Algebra.Symmetrized`) is `IsCommJordan` for free once `Invertible
(2 : A)` holds — no proof obligation at all. `Invertible (2 : A)` itself is easy to build (`(2⁻¹ :
ℝ) • (1 : A)` is a two-sided inverse of `2`), and `sym_coe_jordan` shows `jordan` agrees with
`Aˢʸᵐ`'s multiplication under `SymAlg.sym`, so the Jordan identity for `jordan` is just `Aˢʸᵐ`'s,
pulled back through `sym`'s injectivity — no `noncomm_ring` bookkeeping of our own needed. -/

private lemma two_eq_two_smul_one : (2 : A) = (2 : ℝ) • (1 : A) := by
  rw [two_smul]; norm_num

/-- `2` is invertible in any `CStarAlgebra`: `(2⁻¹ : ℝ) • (1 : A)` is a two-sided inverse. A *new*
instance — nothing in Mathlib already provides `Invertible (2 : A)` for a general `CStarAlgebra A`
for this to diamond against (unlike registering `Mul (Observable A)`, see the module docstring). -/
noncomputable instance instInvertibleTwo : Invertible (2 : A) where
  invOf := (2⁻¹ : ℝ) • (1 : A)
  invOf_mul_self := by
    rw [smul_mul_assoc, one_mul, two_eq_two_smul_one, smul_smul]; norm_num
  mul_invOf_self := by
    rw [mul_smul_comm, mul_one, two_eq_two_smul_one, smul_smul]; norm_num

/-- `jordan` agrees with `Aˢʸᵐ`'s own multiplication under `SymAlg.sym`. -/
lemma sym_coe_jordan (a b : Observable A) :
    SymAlg.sym (jordan a b : A) = SymAlg.sym (a : A) * SymAlg.sym (b : A) := by
  rw [SymAlg.sym_mul_sym, coe_jordan]
  congr 1
  show (2⁻¹ : ℝ) • ((a : A) * b + (b : A) * a) = ⅟(2 : A) * ((a : A) * b + (b : A) * a)
  rw [show (⅟(2 : A) : A) = (2⁻¹ : ℝ) • (1 : A) from rfl, smul_mul_assoc, one_mul]

/-- The Jordan identity, in the shape Mathlib's `IsCommJordan` uses: `(a ∘ b) ∘ (a ∘ a) = a ∘ (b ∘
(a ∘ a))`. Pulled back from `Aˢʸᵐ`'s `IsCommJordan.lmul_comm_rmul_rmul`, not proved by hand. -/
lemma jordan_lmul_comm_rmul_rmul (a b : Observable A) :
    jordan (jordan a b) (jordan a a) = jordan a (jordan b (jordan a a)) := by
  apply Subtype.ext
  apply SymAlg.sym_injective
  simp only [sym_coe_jordan]
  exact IsCommJordan.lmul_comm_rmul_rmul (SymAlg.sym (a : A)) (SymAlg.sym (b : A))

TODO "Register a genuine `IsCommJordan (Observable A)` instance (`Mathlib.Algebra.Jordan.Basic`)
  with `jordan` as its `Mul`, rather than stating `jordan_comm`/`jordan_lmul_comm_rmul_rmul` as
  standalone facts as above. Needs care around `selfAdjoint`'s own `Mul` instance for commutative
  `A` (`Mathlib.Algebra.Star.SelfAdjoint`) to avoid a diamond — see the module docstring. The
  identity itself no longer blocks this (`jordan_lmul_comm_rmul_rmul`); only the instance
  registration is left."

end Observable

end OperatorAlgebra
