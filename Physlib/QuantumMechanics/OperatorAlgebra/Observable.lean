/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

/-!

# Self-adjoint elements in a star-fixed basis

If a basis of a C⋆-algebra `A` consists entirely of self-adjoint vectors, an element of `A` is
self-adjoint exactly when all of its coordinates in that basis are real.

This is the general fact behind `Qubit`'s Pauli decomposition: `1, gen 0, gen 1, gen 2` are each
self-adjoint, so an algebra element is an observable iff its four Pauli coefficients are real.
Stated once here for any `OperatorAlgebra A` and any `Basis ι ℂ A` of self-adjoint vectors,
rather than re-derived by hand for each concrete basis a development happens to use.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra
open Module

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (basis : Basis ι ℂ A)

/-- `basis.repr` reads off the coordinates of *any* explicit combination in `basis`, not just the
canonical one `Basis.repr` produces internally — the basis property makes the two agree. -/
lemma repr_eq_of_eq_sum {a : A} {c : ι → ℂ} (h : a = ∑ i, c i • (basis i : A)) (i : ι) :
    basis.repr a i = c i := by
  rw [h, map_sum]
  simp [Basis.repr_self, Finsupp.single_apply, Finset.sum_ite_eq']

/-- If every basis vector is self-adjoint, `star` conjugates every coordinate. -/
lemma repr_star_of_forall_isSelfAdjoint (basis_selfAdjoint : ∀ i, IsSelfAdjoint (basis i))
    (a : A) (i : ι) : basis.repr (star a : A) i = (starRingEnd ℂ) (basis.repr a i) := by
  refine repr_eq_of_eq_sum basis (c := fun j => (starRingEnd ℂ) (basis.repr a j)) ?_ i
  conv_lhs => rw [← basis.sum_repr a]
  rw [star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_smul, (basis_selfAdjoint j).star_eq]
  rfl

/-- If every basis vector is self-adjoint, an element is self-adjoint exactly when every one of
its coordinates in that basis is real. -/
lemma isSelfAdjoint_iff_forall_repr_im_eq_zero (basis_selfAdjoint : ∀ i, IsSelfAdjoint (basis i))
    (a : A) : IsSelfAdjoint a ↔ ∀ i, (basis.repr a i).im = 0 := by
  constructor
  · intro ha i
    have h := repr_star_of_forall_isSelfAdjoint basis basis_selfAdjoint a i
    rw [ha.star_eq] at h
    exact Complex.conj_eq_iff_im.mp h.symm
  · intro h
    have ha : a = ∑ j, basis.repr a j • (basis j : A) := (basis.sum_repr a).symm
    have hstar : star (a : A) = ∑ j, basis.repr a j • (basis j : A) := by
      conv_lhs => rw [ha]
      rw [star_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [star_smul, (basis_selfAdjoint j).star_eq, Complex.star_def,
        Complex.conj_eq_iff_im.mpr (h j)]
    rw [IsSelfAdjoint, hstar, ← ha]

end OperatorAlgebra
