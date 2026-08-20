/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

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

`Mul (Observable A) := jordan` is *not* registered directly — `selfAdjoint` already carries its
own global `Mul` instance whenever `A` happens to be commutative too
(`Mathlib.Algebra.Star.SelfAdjoint`, `NonUnitalCommRing` case), and a second, merely
propositionally-equal `Mul (Observable A)` from `jordan` would diamond with it. Instead,
`JordanObservable A` — a copy of `Observable A`, exactly the `SymAlg` device applied one level up
— carries `Mul`/`IsCommJordan`, so it never has to compete with `selfAdjoint`'s own instance; see
the last section below.

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

/-! ### `Observable A`'s Jordan product, as a genuine `IsCommJordan` instance

Registering `Mul (Observable A) := jordan` directly would diamond with `selfAdjoint`'s own `Mul`
instance whenever `A` happens to be commutative too (`Mathlib.Algebra.Star.SelfAdjoint`,
`NonUnitalCommRing` case) — see the module docstring. `JordanObservable A` carries the Jordan
product instead, on a *copy* of the same underlying type: the same device `Aˢʸᵐ`/`SymAlg` itself
uses for exactly this problem, one level up. Since `JordanObservable A` is a distinct type from
`Observable A` (not `abbrev`, so not transparent to instance search), its `Mul` never has a chance
to compete with `selfAdjoint`'s. -/

/-- A copy of `Observable A` carrying the Jordan product as its `Mul`, kept as a separate type so
it never competes with `selfAdjoint`'s own `Mul` instance for commutative `A` — see the section
docstring above. Same underlying data as `Observable A`, definitionally. -/
def JordanObservable (A : Type*) [CStarAlgebra A] : Type _ := Observable A

namespace JordanObservable

variable {A : Type*} [CStarAlgebra A]

noncomputable instance : AddCommGroup (JordanObservable A) :=
  (inferInstance : AddCommGroup (Observable A))

noncomputable instance : Module ℝ (JordanObservable A) :=
  (inferInstance : Module ℝ (Observable A))

/-- `JordanObservable A`'s multiplication is exactly `jordan`. -/
noncomputable instance instMul : Mul (JordanObservable A) := ⟨jordan⟩

noncomputable instance instCommMagma : CommMagma (JordanObservable A) where
  mul_comm := jordan_comm (A := A)

/-- `JordanObservable A` is a genuine (commutative) Jordan algebra, in Mathlib's own sense —
`IsJordan` (and everything built on it in `Mathlib.Algebra.Jordan.Basic`) is now available for it
for free, via `IsCommJordan.toIsJordan`. -/
noncomputable instance instIsCommJordan : IsCommJordan (JordanObservable A) where
  lmul_comm_rmul_rmul := jordan_lmul_comm_rmul_rmul (A := A)

end JordanObservable

end Observable

end OperatorAlgebra
