/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Basic
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

/-- If `basis` consists of self-adjoint vectors, and real scalars act on `A` the same way whether
taken directly or through `ℂ` (`real_smul_eq_complex_smul`), `Observable A` is real-linearly
equivalent to `ι → ℝ`: every observable is a unique real-linear combination of `basis`, by
`isSelfAdjoint_iff_forall_repr_im_eq_zero`. -/
noncomputable def basisRealEquiv (basis_selfAdjoint : ∀ i, IsSelfAdjoint (basis i))
    (real_smul_eq_complex_smul : ∀ (r : ℝ) (a : A), r • a = (r : ℂ) • a) :
    Observable A ≃ₗ[ℝ] (ι → ℝ) where
  toFun a i := (basis.repr (a : A) i).re
  invFun c := ⟨∑ i, (c i : ℂ) • (basis i : A), isSelfAdjoint_sum _ fun i _ => by
    simp [isSelfAdjoint_iff, star_smul, (basis_selfAdjoint i).star_eq]⟩
  map_add' a b := by ext i; simp [AddSubgroup.coe_add]
  map_smul' r a := by
    ext i
    show (basis.repr (r • (a : A)) i).re = r * (basis.repr (a : A) i).re
    rw [real_smul_eq_complex_smul, map_smul, Finsupp.smul_apply, smul_eq_mul,
      Complex.re_ofReal_mul]
  left_inv a := by
    have hre : ∀ i, ((basis.repr (a : A) i).re : ℂ) = basis.repr (a : A) i := fun i => by
      have him := (isSelfAdjoint_iff_forall_repr_im_eq_zero basis basis_selfAdjoint (a : A)).mp
        a.2 i
      apply Complex.ext <;> simp [him]
    ext
    show ∑ i, ((basis.repr (a : A) i).re : ℂ) • (basis i : A) = (a : A)
    simp_rw [hre]
    exact basis.sum_repr (a : A)
  right_inv c := by
    ext i
    show (basis.repr (∑ j, (c j : ℂ) • (basis j : A)) i).re = c i
    rw [repr_eq_of_eq_sum basis rfl i, Complex.ofReal_re]

end OperatorAlgebra
