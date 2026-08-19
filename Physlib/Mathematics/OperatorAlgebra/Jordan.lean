/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OperatorAlgebra.Basic

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

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

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

end Observable

end OperatorAlgebra
