/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Basic
public import Physlib.Meta.TODO.Basic
public import Mathlib.Algebra.Lie.OfAssociative

/-!

# Jordan and Lie structure on observables

Every C⋆-algebra product splits into a symmetric and an antisymmetric part, both of which land
back in the observables:

* the **Jordan product** `a ∘ b = ½(ab + ba)` — commutative, generally non-associative;
* the **observable Lie bracket** `⁅a, b⁆ₒ = -i(ab - ba)` — antisymmetric, and self-adjoint
  precisely because of the factor of `i` (the raw commutator `ab - ba` is *skew*-adjoint).

Together they recover the original product: `ab = a ∘ b + (i/2) ⁅a, b⁆ₒ`. So schematically,
a C⋆-algebra gives Jordan geometry (states, positivity, the observable order) plus Lie dynamics
(commutators, generators, symmetry) on the *same* underlying real vector space of observables.

This is useful conceptually — e.g. the qubit's Jordan product is the Euclidean dot product and
its Lie bracket is the cross product (`Qubit.σ_mul_σ`/`Qubit.σ_commutator` are exactly this,
specialized) — but stays a *derived* structure here, not a replacement for the C⋆-algebra as the
foundation.

Both brackets are then shown to satisfy the algebraic laws their names promise. `⁅·,·⁆ₒ` is
registered as a genuine `LieRing`/`LieAlgebra ℝ` instance (Mathlib's own notion — the Jacobi
identity ultimately comes from associativity of `A`, via the ring-commutator Lie ring Mathlib
already builds for any associative ring, `Mathlib.Algebra.Lie.OfAssociative`).

`∘` is shown to satisfy the Jordan identity `(a ∘ a) ∘ (b ∘ a) = ((a ∘ a) ∘ b) ∘ a` directly, as a
concrete fact about `jordan`, rather than through a registered `IsCommJordan (Observable A)`
instance. Mathlib *does* have Jordan algebras (`Mathlib.Algebra.Jordan.Basic`: `IsJordan`,
`IsCommJordan`), and even the general symmetrization construction `Aˢʸᵐ` this file is really an
instance of (`Mathlib.Algebra.Symmetrized`: for any `[Ring A] [Invertible (2 : A)]`, `Aˢʸᵐ` is
`IsCommJordan` for free — no proof obligation at all, `∘` is exactly `SymAlg.sym_mul_sym`
specialized). Registering that instance *on* `Observable A` itself is left as a `TODO` below: it
needs `Invertible (2 : A)` (not available for a general `CStarAlgebra A` off the shelf) and some
care, since `selfAdjoint` already carries its own `Mul` instance when `A` happens to be
commutative (`Mathlib.Algebra.Star.SelfAdjoint`, `NonUnitalCommRing` case) — registering a second,
merely propositionally-equal `Mul (Observable A)` from `jordan` would create a diamond with it.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

/-! ### Two associative-ring facts, used to transport identities from `A` to `Observable A` -/

/-- The Leibniz/Jacobi identity for the ring commutator of an associative ring, spelled out
directly (rather than going through the `LieRing` instance, which Mathlib deliberately keeps
`local` to avoid a diamond with `LieRingModule.ofAssociativeModule` — see the note on
`LieRingModule.ofAssociativeModule`). Pure associative-ring algebra, closed by `noncomm_ring`. -/
private theorem leibniz_lie_A (x y z : A) : ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring

/-- The Jordan identity for the ring anticommutator `x * y + y * x`, unscaled. This is the
associative-ring computation underlying every special Jordan algebra: expand both sides in terms
of `x`, `x*x`, `x*x*x`, `y` and check the same four terms appear. Mathlib proves the analogous
fact abstractly for `Aˢʸᵐ` (`SymAlg`'s `IsCommJordan` instance, `Mathlib.Algebra.Symmetrized`);
this is the same computation, spelled out concretely for the anticommutator on `A` itself. -/
private theorem raw_jordan_identity (x y : A) :
    x * x * (y * x + x * y) + (y * x + x * y) * (x * x)
      = (x * x * y + y * (x * x)) * x + x * (x * x * y + y * (x * x)) := by
  noncomm_ring

namespace Observable

/-- `ab + ba` is self-adjoint whenever `a` and `b` are — no commutativity of `a` and `b` needed. -/
theorem isSelfAdjoint_mul_add_mul {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint (a * b + b * a) := by
  rw [isSelfAdjoint_iff, star_add, star_mul, star_mul, ha.star_eq, hb.star_eq, add_comm]

/-- The Jordan product `a ∘ b = ½(ab + ba)`: commutative, generally non-associative, the
symmetric part of the algebra product. -/
noncomputable def jordan (a b : Observable A) : Observable A :=
  (2⁻¹ : ℝ) •
    (⟨(a : A) * b + (b : A) * a, isSelfAdjoint_mul_add_mul a.property b.property⟩ : Observable A)

theorem coe_jordan (a b : Observable A) :
    (jordan a b : A) = (2⁻¹ : ℝ) • ((a : A) * b + (b : A) * a) :=
  rfl

/-- `i(ba - ab)` is self-adjoint whenever `a` and `b` are: the raw commutator `ab - ba` is
skew-adjoint, and `i` times a skew-adjoint element is self-adjoint. -/
theorem isSelfAdjoint_I_smul_mul_sub_mul {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint (Complex.I • (b * a - a * b)) := by
  rw [isSelfAdjoint_iff, star_smul, star_sub, star_mul, star_mul, ha.star_eq, hb.star_eq,
    Complex.star_def, Complex.conj_I]
  module

/-- The observable Lie bracket `⁅a, b⁆ₒ = -i(ab - ba) = i(ba - ab)`: the antisymmetric part of
the algebra product, landing back in the observables. -/
noncomputable def obsBracket (a b : Observable A) : Observable A :=
  ⟨Complex.I • ((b : A) * a - (a : A) * b), isSelfAdjoint_I_smul_mul_sub_mul a.property b.property⟩

theorem coe_obsBracket (a b : Observable A) :
    (obsBracket a b : A) = Complex.I • ((b : A) * a - (a : A) * b) :=
  rfl

/-- The algebra product decomposes into its Jordan (symmetric) and Lie (antisymmetric) parts:
`ab = a ∘ b + (i/2) ⁅a, b⁆ₒ`. -/
theorem mul_eq_jordan_add_obsBracket (a b : Observable A) :
    (a : A) * b = (jordan a b : A) + (Complex.I / 2) • (obsBracket a b : A) := by
  rw [coe_jordan, coe_obsBracket, smul_smul]
  have hI : (Complex.I / 2 * Complex.I) = (-2⁻¹ : ℂ) := by
    rw [div_mul_eq_mul_div, Complex.I_mul_I]; ring
  rw [hI]
  module

/-! ### `⁅·,·⁆ₒ` makes the observables a Lie algebra

The bracket is `-i` times the ring commutator: `coe_bracket` records this, and every axiom below
is transported from the corresponding fact about the ring commutator on `A` itself
(`leibniz_lie_A` above, `smul_lie_A`/`lie_smul_A` below), using that `Complex.I` is a central,
`ℝ`/`ℂ`-scalar acting on `A`. -/

noncomputable instance instBracket : Bracket (Observable A) (Observable A) := ⟨obsBracket⟩

theorem bracket_def (a b : Observable A) : ⁅a, b⁆ = obsBracket a b := rfl

theorem coe_bracket (a b : Observable A) :
    ((⁅a, b⁆ : Observable A) : A) = (-Complex.I) • ⁅(a : A), (b : A)⁆ := by
  rw [bracket_def, coe_obsBracket, Ring.lie_def, neg_smul, ← smul_neg, neg_sub]

/-- `(-i) * (-i) = -1`, the constant that appears whenever two nested observable brackets are
unfolded into raw ring commutators. -/
private theorem neg_I_mul_neg_I : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
  rw [neg_mul_neg, Complex.I_mul_I]

private theorem lie_smul_A (r : ℂ) (x y : A) : ⁅x, r • y⁆ = r • ⁅x, y⁆ := by
  simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]

private theorem smul_lie_A (r : ℂ) (x y : A) : ⁅r • x, y⁆ = r • ⁅x, y⁆ := by
  simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]

private theorem lie_smul_A_real (t : ℝ) (x y : A) : ⁅x, t • y⁆ = t • ⁅x, y⁆ := by
  simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]

noncomputable instance instLieRing : LieRing (Observable A) where
  add_lie a b c := by
    apply Subtype.ext
    simp only [bracket_def, coe_obsBracket, AddSubgroup.coe_add, mul_add, add_mul]
    module
  lie_add a b c := by
    apply Subtype.ext
    simp only [bracket_def, coe_obsBracket, AddSubgroup.coe_add, mul_add, add_mul]
    module
  lie_self a := by
    apply Subtype.ext
    simp [bracket_def, coe_obsBracket]
  leibniz_lie a b c := by
    apply Subtype.ext
    rw [AddSubgroup.coe_add]
    have hL : ((⁅a, ⁅b, c⁆⁆ : Observable A) : A) = (-1 : ℂ) • ⁅(a : A), ⁅(b : A), (c : A)⁆⁆ := by
      rw [coe_bracket, coe_bracket, lie_smul_A, smul_smul, neg_I_mul_neg_I]
    have hR : ((⁅⁅a, b⁆, c⁆ : Observable A) : A) + ((⁅b, ⁅a, c⁆⁆ : Observable A) : A)
        = (-1 : ℂ) • (⁅⁅(a : A), (b : A)⁆, (c : A)⁆ + ⁅(b : A), ⁅(a : A), (c : A)⁆⁆) := by
      rw [coe_bracket, coe_bracket, coe_bracket, coe_bracket, smul_lie_A, lie_smul_A, smul_smul,
        smul_smul, neg_I_mul_neg_I, ← smul_add]
    rw [hL, hR, ← leibniz_lie_A]

noncomputable instance instLieAlgebra : LieAlgebra ℝ (Observable A) where
  toModule := inferInstance
  lie_smul t a b := by
    apply Subtype.ext
    show ((⁅a, t • b⁆ : Observable A) : A) = ((t • ⁅a, b⁆ : Observable A) : A)
    rw [coe_bracket, selfAdjoint.val_smul, lie_smul_A_real, selfAdjoint.val_smul, coe_bracket,
      smul_comm]

/-! ### `∘` makes the observables a Jordan algebra

Every fact below is transported from the corresponding fact about `A`'s own product, in the same
style as the Lie side above. `jordan_self` collapses one layer of `2⁻¹`-bookkeeping for free
(`a ∘ a = a * a` on the nose), which is what makes `jordan_jordan_identity`'s bookkeeping
tractable: both sides reduce to `4⁻¹ •` the same associative-ring expression, `raw_jordan_identity`
from the top of the file. -/

theorem jordan_comm (a b : Observable A) : jordan a b = jordan b a := by
  apply Subtype.ext
  simp only [coe_jordan, add_comm]

/-- `a ∘ a = a * a`: the one place the `2⁻¹` in the Jordan product disappears for free, since both
terms of `coe_jordan`'s sum coincide when the two arguments are equal. -/
theorem jordan_self (a : Observable A) : (jordan a a : A) = (a : A) * a := by
  rw [coe_jordan]
  module

theorem add_jordan (a b c : Observable A) : jordan (a + b) c = jordan a c + jordan b c := by
  apply Subtype.ext
  simp only [coe_jordan, AddSubgroup.coe_add, mul_add, add_mul]
  module

theorem jordan_smul (t : ℝ) (a b : Observable A) : jordan a (t • b) = t • jordan a b := by
  apply Subtype.ext
  show (jordan a (t • b) : A) = ((t • jordan a b : Observable A) : A)
  simp only [coe_jordan, selfAdjoint.val_smul]
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add, smul_smul, smul_smul, mul_comm (2⁻¹ : ℝ) t]

/-- The Jordan identity `(a ∘ a) ∘ (b ∘ a) = ((a ∘ a) ∘ b) ∘ a`: both sides reduce, via
`jordan_self`, to `4⁻¹ •` the same associative-ring expression in `A` (`raw_jordan_identity`). -/
theorem jordan_jordan_identity (a b : Observable A) :
    jordan (jordan a a) (jordan b a) = jordan (jordan (jordan a a) b) a := by
  apply Subtype.ext
  have hL : (jordan (jordan a a) (jordan b a) : A)
      = (4⁻¹ : ℝ) • ((a : A) * a * ((b : A) * a + a * b) + ((b : A) * a + a * b) * ((a : A) * a)) := by
    rw [coe_jordan, jordan_self, coe_jordan, mul_smul_comm, smul_mul_assoc, ← smul_add, smul_smul,
      show (2⁻¹ : ℝ) * 2⁻¹ = (4⁻¹ : ℝ) by norm_num]
  have hR : (jordan (jordan (jordan a a) b) a : A)
      = (4⁻¹ : ℝ) • ((((a : A) * a) * b + b * ((a : A) * a)) * a
          + a * (((a : A) * a) * b + b * ((a : A) * a))) := by
    rw [coe_jordan, coe_jordan, jordan_self, smul_mul_assoc, mul_smul_comm, ← smul_add, smul_smul,
      show (2⁻¹ : ℝ) * 2⁻¹ = (4⁻¹ : ℝ) by norm_num]
  rw [hL, hR]
  congr 1
  exact raw_jordan_identity (a : A) (b : A)

TODO "Register a genuine `IsCommJordan (Observable A)` instance (`Mathlib.Algebra.Jordan.Basic`)
  with `jordan` as its `Mul`, rather than stating `jordan_comm`/`jordan_jordan_identity` as
  standalone facts as above. Needs `Invertible (2 : A)` (constructible from `(2⁻¹ : ℝ) • (1 : A)`,
  not yet set up) and care around `selfAdjoint`'s own `Mul` instance for commutative `A`
  (`Mathlib.Algebra.Star.SelfAdjoint`) to avoid a diamond — see the module docstring."

end Observable

end OperatorAlgebra
