/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Basic
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.OfAssociative

/-!

# Lie structure on observables

The antisymmetric part of a C⋆-algebra product, `⁅a, b⁆ₒ = -i(ab - ba)`, lands back in the
observables: the raw commutator `ab - ba` is *skew*-adjoint whenever `a` and `b` are self-adjoint,
and `i` times a skew-adjoint element is self-adjoint. This makes `Observable A` a genuine
`LieRing`/`LieAlgebra ℝ` (Mathlib's own notion) — the Jacobi identity is transported from
associativity of `A`, via the ring-commutator Lie ring Mathlib already builds for any associative
ring (`Mathlib.Algebra.Lie.OfAssociative`) — kept `local` there deliberately (to avoid a diamond
with `LieRingModule.ofAssociativeModule`), so the transport has to be done by hand once, here.

`1` is central (`obsBracket_one_right`, `one_mem_center`) — the qubit's `su(2)` (`Qubit.τLieEquiv`)
is therefore realized as a proper *subalgebra* of `Observable A` (the traceless generators), not
all of it.

The *symmetric* part of the product — the Jordan product `∘` — is a separate, independent
structure on the same underlying real vector space; see `OperatorAlgebra.Jordan`.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

/-- The Leibniz/Jacobi identity for the ring commutator of an associative ring, spelled out
directly (rather than going through the `LieRing` instance, which Mathlib deliberately keeps
`local` to avoid a diamond with `LieRingModule.ofAssociativeModule` — see the note on
`LieRingModule.ofAssociativeModule`). Pure associative-ring algebra, closed by `noncomm_ring`. -/
private lemma leibniz_lie_A (x y z : A) : ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  simp only [Ring.lie_def]
  noncomm_ring

namespace Observable

/-- `i(ba - ab)` is self-adjoint whenever `a` and `b` are: the raw commutator `ab - ba` is
skew-adjoint, and `i` times a skew-adjoint element is self-adjoint. -/
lemma isSelfAdjoint_I_smul_mul_sub_mul {a b : A} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) :
    IsSelfAdjoint (Complex.I • (b * a - a * b)) := by
  rw [isSelfAdjoint_iff, star_smul, star_sub, star_mul, star_mul, ha.star_eq, hb.star_eq,
    Complex.star_def, Complex.conj_I]
  module

/-- The observable Lie bracket `⁅a, b⁆ₒ = -i(ab - ba) = i(ba - ab)`: the antisymmetric part of
the algebra product, landing back in the observables. -/
noncomputable def obsBracket (a b : Observable A) : Observable A :=
  ⟨Complex.I • ((b : A) * a - (a : A) * b), isSelfAdjoint_I_smul_mul_sub_mul a.property b.property⟩

lemma coe_obsBracket (a b : Observable A) :
    (obsBracket a b : A) = Complex.I • ((b : A) * a - (a : A) * b) :=
  rfl

/-! ### `⁅·,·⁆ₒ` makes the observables a Lie algebra

The bracket is `-i` times the ring commutator: `coe_bracket` records this, and every axiom below
is transported from the corresponding fact about the ring commutator on `A` itself
(`leibniz_lie_A` above, `smul_lie_A`/`lie_smul_A` below), using that `Complex.I` is a central,
`ℝ`/`ℂ`-scalar acting on `A`. -/

noncomputable instance instBracket : Bracket (Observable A) (Observable A) := ⟨obsBracket⟩

lemma bracket_def (a b : Observable A) : ⁅a, b⁆ = obsBracket a b := rfl

lemma coe_bracket (a b : Observable A) :
    ((⁅a, b⁆ : Observable A) : A) = (-Complex.I) • ⁅(a : A), (b : A)⁆ := by
  rw [bracket_def, coe_obsBracket, Ring.lie_def, neg_smul, ← smul_neg, neg_sub]

/-- `(-i) * (-i) = -1`, the constant that appears whenever two nested observable brackets are
unfolded into raw ring commutators. -/
private lemma neg_I_mul_neg_I : (-Complex.I) * (-Complex.I) = (-1 : ℂ) := by
  rw [neg_mul_neg, Complex.I_mul_I]

private lemma lie_smul_A (r : ℂ) (x y : A) : ⁅x, r • y⁆ = r • ⁅x, y⁆ := by
  simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]

private lemma smul_lie_A (r : ℂ) (x y : A) : ⁅r • x, y⁆ = r • ⁅x, y⁆ := by
  simp only [Ring.lie_def, mul_smul_comm, smul_mul_assoc, smul_sub]

private lemma lie_smul_A_real (t : ℝ) (x y : A) : ⁅x, t • y⁆ = t • ⁅x, y⁆ := by
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

/-! ### `1` is central -/

/-- `1` brackets to `0` with everything: it commutes with every element of `A`, so the raw
commutator vanishes outright. -/
lemma obsBracket_one_right (a : Observable A) : obsBracket a 1 = 0 := by
  apply Subtype.ext
  simp [coe_obsBracket]

/-- `1` lies in the center of the Lie algebra `Observable A`: `Observable A` as a whole is *not*
`su(2)`, only a subalgebra of it is (the traceless generators, `Qubit.τHom.range`). -/
lemma one_mem_center : (1 : Observable A) ∈ LieAlgebra.center ℝ (Observable A) := by
  show (1 : Observable A) ∈ LieModule.maxTrivSubmodule ℝ (Observable A) (Observable A)
  rw [LieModule.mem_maxTrivSubmodule]
  intro x
  rw [bracket_def]
  exact obsBracket_one_right x

end Observable

end OperatorAlgebra
