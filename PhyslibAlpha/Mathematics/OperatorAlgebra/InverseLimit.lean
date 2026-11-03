/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.lpSpace
/-!

# Bounded inverse limits of C*-algebras

The C*-algebra of bounded compatible sequences in a tower of C*-algebras.

## i. Overview

A tower `⋯ → A (n+1) → A n → ⋯ → A 0` of C*-algebras with star homomorphisms `κ n : A (n+1) → A n`
has the inverse limit `inverseLimit κ` of the bounded sequences `x n ∈ A n` with
`κ n (x (n+1)) = x n`. It is a closed star subalgebra of the `ℓ∞` product `lp A ∞`. Hence it is a
C*-algebra for the supremum norm.

A compatible family of star homomorphisms between two towers induces a star homomorphism of the
limits. A compatible family of star isomorphisms induces a star isomorphism. The towers of
observable algebras of infinite quantum systems have this form: an automorphic dynamics is a
family of automorphisms of the finite sectors that commute with the connecting maps.

## ii. Key results

- `InverseLimit.inverseLimit`: the star subalgebra of compatible bounded sequences.
- `InverseLimit.isClosed`: it is closed in `lp A ∞`.
- `InverseLimit.proj`: the coordinate projections, which are contractive.
- `InverseLimit.map`: the star homomorphism induced by a compatible family.
- `InverseLimit.mapEquiv`: the star isomorphism induced by a compatible family of isomorphisms.

## iii. Table of contents

- A. The limit
- B. Functoriality

## iv. References

* None.
-/

@[expose] public section

open scoped ENNReal

namespace InverseLimit

noncomputable section

variable {A : ℕ → Type*} [∀ n, CStarAlgebra (A n)] [∀ n, Nontrivial (A n)]
  (κ : ∀ n, A (n + 1) →⋆ₐ[ℂ] A n)

/-!

## A. The limit

-/

/-- The bounded sequences `x` with `κ n (x (n + 1)) = x n` for all `n`. -/
def inverseLimit : StarSubalgebra ℂ (lp A ∞) where
  carrier := {x | ∀ n, κ n (x (n + 1)) = x n}
  add_mem' {x y} hx hy n := by simp [map_add, hx n, hy n]
  zero_mem' n := by simp
  mul_mem' {x y} hx hy n := by simp [map_mul, hx n, hy n]
  one_mem' n := by simp
  algebraMap_mem' r n := by simp [Algebra.algebraMap_eq_smul_one]
  star_mem' {x} hx n := by simp [map_star, hx n]

lemma continuous_apply (n : ℕ) : Continuous fun x : lp A ∞ => x n := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => ?_)
  simpa [dist_eq_norm] using lp.norm_apply_le_norm ENNReal.top_ne_zero (x - y) n

/-- The inverse limit is closed in `lp A ∞`. -/
lemma isClosed : IsClosed (inverseLimit κ : Set (lp A ∞)) := by
  have : (inverseLimit κ : Set (lp A ∞)) = ⋂ n, {x | κ n (x (n + 1)) = x n} := by
    ext x
    simp only [Set.mem_iInter]
    exact Iff.rfl
  rw [this]
  refine isClosed_iInter fun n => isClosed_eq ?_ (continuous_apply n)
  have hκ : Continuous (κ n) := by
    refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => ?_)
    simpa [dist_eq_norm, ← map_sub] using NonUnitalStarAlgHom.norm_apply_le (κ n) (x - y)
  exact hκ.comp (continuous_apply (n + 1))

instance : CompleteSpace (inverseLimit κ) := (isClosed κ).completeSpace_coe

/-- **The bounded inverse limit is a C*-algebra.** -/
instance : CStarAlgebra (inverseLimit κ) where

/-- The coordinate projection onto the `n`-th algebra. -/
def proj (n : ℕ) : inverseLimit κ →⋆ₐ[ℂ] A n where
  toFun x := x.1 n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/-- The coordinate projections are contractive. -/
lemma norm_proj_le (n : ℕ) (x : inverseLimit κ) : ‖proj κ n x‖ ≤ ‖x‖ :=
  lp.norm_apply_le_norm ENNReal.top_ne_zero x.1 n

/-!

## B. Functoriality

-/

section Functoriality

variable {B : ℕ → Type*} [∀ n, CStarAlgebra (B n)] [∀ n, Nontrivial (B n)]
  (κ' : ∀ n, B (n + 1) →⋆ₐ[ℂ] B n)

/-- A compatible family of star homomorphisms induces a star homomorphism of the limits. -/
def map (f : ∀ n, A n →⋆ₐ[ℂ] B n) (hf : ∀ n x, κ' n (f (n + 1) x) = f n (κ n x)) :
    inverseLimit κ →⋆ₐ[ℂ] inverseLimit κ' where
  toFun x := ⟨⟨fun n => f n (x.1 n), memℓp_infty ⟨‖x‖, by
      rintro _ ⟨n, rfl⟩
      exact (NonUnitalStarAlgHom.norm_apply_le (f n) _).trans (norm_proj_le κ n x)⟩⟩, fun n => by
    show κ' n (f (n + 1) (x.1 (n + 1))) = f n (x.1 n)
    rw [hf, x.2 n]⟩
  map_one' := by ext n; exact map_one (f n)
  map_mul' x y := by ext n; exact map_mul (f n) _ _
  map_zero' := by ext n; exact map_zero (f n)
  map_add' x y := by ext n; exact map_add (f n) _ _
  commutes' r := by ext n; exact (f n).commutes r
  map_star' x := by ext n; exact map_star (f n) _

@[simp] lemma map_apply (f : ∀ n, A n →⋆ₐ[ℂ] B n) (hf) (x : inverseLimit κ) (n : ℕ) :
    (map κ κ' f hf x).1 n = f n (x.1 n) := rfl

/-- **Compatible automorphisms act on the limit.** A compatible family of star isomorphisms
induces a star isomorphism of the bounded inverse limits. -/
def mapEquiv (α : ∀ n, A n ≃⋆ₐ[ℂ] B n)
    (hα : ∀ n x, κ' n (α (n + 1) x) = α n (κ n x)) :
    inverseLimit κ ≃⋆ₐ[ℂ] inverseLimit κ' :=
  StarAlgEquiv.ofStarAlgHom
    (map κ κ' (fun n => (α n).toStarAlgHom) hα)
    (map κ' κ (fun n => (α n).symm.toStarAlgHom) fun n y => by
      show κ n ((α (n + 1)).symm y) = (α n).symm (κ' n y)
      apply EquivLike.injective (α n)
      rw [(α n).apply_symm_apply, ← hα, (α (n + 1)).apply_symm_apply])
    (by ext x n; exact (α n).symm_apply_apply (x.1 n))
    (by ext x n; exact (α n).apply_symm_apply (x.1 n))

end Functoriality

end

end InverseLimit
