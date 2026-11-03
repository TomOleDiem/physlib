/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.PolynomialAlgebra
public import Mathlib.RingTheory.TensorProduct.Maps
/-!

# Polynomial operators tensored with a finite matrix algebra

For spin-boson systems the bosonic polynomial operators act together with a finite-dimensional
matrix algebra, for example the Pauli matrices of a two-level atom.

## i. Overview

Let `B` index a basis of the algebraic space and let `n` be a finite type. The space with basis
`B × n` is the tensor product of the algebraic space with `ℂⁿ`. For an adjointable operator `A` and a
matrix `M` the operator `A ⊗ M` acts on a basis vector `(β, i)` by `Σ_j M_{ji} (A β, j)`. The formal
adjoint is `A* ⊗ Mᴴ`. The construction is multiplicative in both factors, is compatible with the star
and sends `(1, 1)` to `1`. Hence it is the product map of a star algebra tensor product. No lattice
or particle-number restriction enters.

## ii. Key results

- `InfiniteBosons.kron`: the operator `A ⊗ M` as an adjointable operator.
- `InfiniteBosons.kron_mul`: `(A A') ⊗ (M M') = (A ⊗ M)(A' ⊗ M')`.
- `InfiniteBosons.kron_star`: `(A ⊗ M)* = A* ⊗ Mᴴ`.
- `InfiniteBosons.kron_one`: `1 ⊗ 1 = 1`.

## iii. Table of contents

- A. Sums of pairings
- B. The Kronecker product of operators
- C. The adjointable operator

## iv. References

* K. Schmüdgen, Unbounded Operator Algebras and Representation Theory, Birkhäuser (1990),
  Section 3.
-/

@[expose] public section

open Finsupp
open scoped TensorProduct

noncomputable section
namespace InfiniteBosons

section Pairing

variable {B : Type*} [DecidableEq B]

lemma pair_sum_left {ι : Type*} (s : Finset ι) (u : ι → (B →₀ ℂ)) (g : B →₀ ℂ) :
    pair (∑ i ∈ s, u i) g = ∑ i ∈ s, pair (u i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pair_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pair_add_left, ih]

lemma pair_sum_right {ι : Type*} (s : Finset ι) (f : B →₀ ℂ) (u : ι → (B →₀ ℂ)) :
    pair f (∑ i ∈ s, u i) = ∑ i ∈ s, pair f (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pair_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pair_add_right, ih]

end Pairing

section Kron

variable {B n : Type*} [DecidableEq B] [Fintype n] [DecidableEq n]

/-- The vector `u` placed in the layer `j`. -/
def layer (j : n) (u : B →₀ ℂ) : B × n →₀ ℂ := Finsupp.mapDomain (fun b => (b, j)) u

lemma layer_smul (j : n) (c : ℂ) (u : B →₀ ℂ) : layer j (c • u) = c • layer j u := by
  simp [layer, Finsupp.mapDomain_smul]

lemma layer_single (j : n) (b : B) (c : ℂ) : layer j (single b c) = single (b, j) c := by
  simp [layer]

lemma pair_layer_single (j i' : n) (u : B →₀ ℂ) (β' : B) :
    pair (layer j u) (single (β', i') (1 : ℂ)) = if j = i' then pair u (single β' 1) else 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp [layer, pair_zero_left]
  | add f g hf hg =>
    simp only [layer, Finsupp.mapDomain_add] at hf hg ⊢
    rw [pair_add_left, hf, hg, pair_add_left]
    split_ifs <;> simp
  | single b c =>
    rw [layer_single, pair_single_single, pair_single_single]
    by_cases hj : j = i' <;> by_cases hb : b = β' <;> simp [hj, hb]

lemma pair_single_layer (i j : n) (β : B) (u : B →₀ ℂ) :
    pair (single (β, i) (1 : ℂ)) (layer j u) = if i = j then pair (single β 1) u else 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp [layer, pair_zero_right]
  | add f g hf hg =>
    simp only [layer, Finsupp.mapDomain_add] at hf hg ⊢
    rw [pair_add_right, hf, hg, pair_add_right]
    split_ifs <;> simp
  | single b c =>
    rw [layer_single, pair_single_single, pair_single_single]
    by_cases hj : i = j <;> by_cases hb : β = b <;> simp [hj, hb]

/-- The Kronecker product of an operator of `B →₀ ℂ` and a matrix on `n`. -/
def kronLin (T : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)) (M : Matrix n n ℂ) :
    (B × n →₀ ℂ) →ₗ[ℂ] (B × n →₀ ℂ) :=
  Finsupp.lsum ℂ fun p => LinearMap.toSpanSingleton ℂ _
    (∑ j, M j p.2 • layer j (T (single p.1 1)))

lemma kronLin_single (T : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)) (M : Matrix n n ℂ) (β : B) (i : n) :
    kronLin T M (single (β, i) 1) = ∑ j, M j i • layer j (T (single β 1)) := by
  simp [kronLin, Finsupp.lsum_single]

lemma pair_kron_basis (T S : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)) (M : Matrix n n ℂ)
    (h : ∀ β β' : B, pair (T (single β 1)) (single β' 1) = pair (single β 1) (S (single β' 1)))
    (p p' : B × n) :
    pair (kronLin T M (single p 1)) (single p' 1) =
      pair (single p 1) (kronLin S M.conjTranspose (single p' 1)) := by
  obtain ⟨β, i⟩ := p
  obtain ⟨β', i'⟩ := p'
  rw [kronLin_single, kronLin_single, pair_sum_left, pair_sum_right]
  simp only [pair_smul_left, pair_smul_right, pair_layer_single, pair_single_layer]
  simp [h β β', Matrix.conjTranspose_apply]


lemma kronLin_layer (T : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)) (M : Matrix n n ℂ) (j : n) (u : B →₀ ℂ) :
    kronLin T M (layer j u) = ∑ k, M k j • layer k (T u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp [layer]
  | add f g hf hg =>
    have : layer j (f + g) = layer j f + layer j g := by simp [layer, Finsupp.mapDomain_add]
    rw [this, map_add, hf, hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add]
    simp only [layer, Finsupp.mapDomain_add, smul_add]
  | single b c =>
    have h1 : (single b c : B →₀ ℂ) = c • single b 1 := by simp [Finsupp.smul_single]
    rw [h1, map_smul]
    have h2 : layer j (c • single b (1 : ℂ)) = c • single (b, j) (1 : ℂ) := by
      rw [show c • single b (1 : ℂ) = single b c by simp [Finsupp.smul_single], layer_single]
      simp [Finsupp.smul_single]
    rw [h2, map_smul, kronLin_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [layer_smul, smul_comm]

lemma kronLin_mul (T T' : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)) (M M' : Matrix n n ℂ) :
    kronLin (T * T') (M * M') = kronLin T M * kronLin T' M' := by
  refine linearMap_ext_basis fun p => ?_
  obtain ⟨β, i⟩ := p
  rw [Module.End.mul_apply, kronLin_single, kronLin_single, map_sum]
  simp only [map_smul, kronLin_layer, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul]
  simp [Matrix.mul_apply, Module.End.mul_apply]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _


lemma kronLin_one : kronLin (1 : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)) (1 : Matrix n n ℂ) = 1 := by
  refine linearMap_ext_basis fun p => ?_
  obtain ⟨β, i⟩ := p
  rw [kronLin_single]
  simp [Matrix.one_apply, layer_single, Finset.sum_ite_eq]

end Kron


section Kron2

variable {B n : Type*} [DecidableEq B] [Fintype n] [DecidableEq n]

/-- **Tensor product with a finite matrix algebra.** The operator `A ⊗ M` of the polynomial
operators on the space with basis `B` and the matrix algebra of `n`, as an adjointable operator on
the space with basis `B × n`. -/
def kron (A : Adjointable B) (M : Matrix n n ℂ) : Adjointable (B × n) :=
  ⟨(kronLin A.1.1 M,
      MulOpposite.op (ofEnd (kronLin (toEnd (MulOpposite.unop A.1.2)) M.conjTranspose))), by
    rw [mem_adjointable]
    intro f g
    simp only [MulOpposite.unop_op, toEnd_ofEnd]
    refine pair_eq_of_basis (fun p p' => ?_) f g
    refine pair_kron_basis _ _ M (fun β β' => ?_) p p'
    exact mem_adjointable.mp A.2 (single β 1) (single β' 1)⟩

lemma kron_fst (A : Adjointable B) (M : Matrix n n ℂ) : (kron A M).1.1 = kronLin A.1.1 M := rfl

lemma kron_star (A : Adjointable B) (M : Matrix n n ℂ) :
    star (kron A M) = kron (star A) M.conjTranspose := by
  refine adjointable_ext ?_
  show toEnd (MulOpposite.unop (kron A M).1.2) = kronLin (star A).1.1 M.conjTranspose
  simp only [kron, MulOpposite.unop_op, toEnd_ofEnd]
  rfl

lemma kron_mul (A A' : Adjointable B) (M M' : Matrix n n ℂ) :
    kron (A * A') (M * M') = kron A M * kron A' M' :=
  adjointable_ext (kronLin_mul A.1.1 A'.1.1 M M')

lemma kron_one : kron (1 : Adjointable B) (1 : Matrix n n ℂ) = 1 :=
  adjointable_ext kronLin_one

end Kron2

section Algebra

variable {B n : Type*} [DecidableEq B] [Fintype n] [DecidableEq n]

lemma kronLin_add_left (T T' : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)) (M : Matrix n n ℂ) :
    kronLin (T + T') M = kronLin T M + kronLin T' M := by
  refine linearMap_ext_basis fun p => ?_
  obtain ⟨β, i⟩ := p
  simp only [LinearMap.add_apply, kronLin_single, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_add]
  congr 1
  simp [layer, Finsupp.mapDomain_add]

lemma kronLin_add_right (T : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)) (M M' : Matrix n n ℂ) :
    kronLin T (M + M') = kronLin T M + kronLin T M' := by
  refine linearMap_ext_basis fun p => ?_
  obtain ⟨β, i⟩ := p
  simp only [LinearMap.add_apply, kronLin_single, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [add_smul]

lemma kronLin_smul_left (c : ℂ) (T : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)) (M : Matrix n n ℂ) :
    kronLin (c • T) M = c • kronLin T M := by
  refine linearMap_ext_basis fun p => ?_
  obtain ⟨β, i⟩ := p
  simp only [LinearMap.smul_apply, kronLin_single, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [layer_smul, smul_comm]

lemma kronLin_smul_right (c : ℂ) (T : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)) (M : Matrix n n ℂ) :
    kronLin T (c • M) = c • kronLin T M := by
  refine linearMap_ext_basis fun p => ?_
  obtain ⟨β, i⟩ := p
  simp only [LinearMap.smul_apply, kronLin_single, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [smul_smul]

lemma kron_add_left (A A' : Adjointable B) (M : Matrix n n ℂ) :
    kron (A + A') M = kron A M + kron A' M :=
  adjointable_ext (kronLin_add_left A.1.1 A'.1.1 M)

lemma kron_add_right (A : Adjointable B) (M M' : Matrix n n ℂ) :
    kron A (M + M') = kron A M + kron A M' :=
  adjointable_ext (kronLin_add_right A.1.1 M M')

lemma kron_smul_left (c : ℂ) (A : Adjointable B) (M : Matrix n n ℂ) :
    kron (c • A) M = c • kron A M :=
  adjointable_ext (kronLin_smul_left c A.1.1 M)

lemma kron_smul_right (c : ℂ) (A : Adjointable B) (M : Matrix n n ℂ) :
    kron A (c • M) = c • kron A M :=
  adjointable_ext (kronLin_smul_right c A.1.1 M)

/-- The embedding of the bosonic factor. -/
def kronLeft : Adjointable B →⋆ₐ[ℂ] Adjointable (B × n) where
  toFun A := kron A (1 : Matrix n n ℂ)
  map_one' := kron_one
  map_mul' A A' := by
    have := kron_mul A A' (1 : Matrix n n ℂ) 1
    rwa [one_mul] at this
  map_zero' := by
    have := kron_smul_left (0 : ℂ) (0 : Adjointable B) (1 : Matrix n n ℂ)
    simpa using this
  commutes' c := by
    have := kron_smul_left c (1 : Adjointable B) (1 : Matrix n n ℂ)
    rw [kron_one] at this
    simpa [Algebra.algebraMap_eq_smul_one] using this
  map_star' A := by
    have := kron_star A (1 : Matrix n n ℂ)
    rw [Matrix.conjTranspose_one] at this
    exact this.symm
  map_add' A A' := kron_add_left A A' 1

/-- The embedding of the matrix factor. -/
def kronRight : Matrix n n ℂ →⋆ₐ[ℂ] Adjointable (B × n) where
  toFun M := kron (1 : Adjointable B) M
  map_one' := kron_one
  map_mul' M M' := by
    have := kron_mul (1 : Adjointable B) 1 M M'
    rwa [one_mul] at this
  map_zero' := by
    have := kron_smul_right (0 : ℂ) (1 : Adjointable B) (1 : Matrix n n ℂ)
    simpa using this
  commutes' c := by
    have := kron_smul_right c (1 : Adjointable B) (1 : Matrix n n ℂ)
    rw [kron_one] at this
    simpa [Algebra.algebraMap_eq_smul_one] using this
  map_star' M := by
    have := kron_star (1 : Adjointable B) M
    rw [star_one] at this
    rw [Matrix.star_eq_conjTranspose]
    exact this.symm
  map_add' M M' := kron_add_right 1 M M'

lemma kronLeft_kronRight_comm (A : Adjointable B) (M : Matrix n n ℂ) :
    Commute (kronLeft A : Adjointable (B × n)) (kronRight M) := by
  show kron A 1 * kron 1 M = kron 1 M * kron A 1
  rw [← kron_mul, ← kron_mul, mul_one, one_mul, one_mul, mul_one]

/-- **The algebra tensor product** `P ⊗ M_n → Adjointable (B × n)`, `A ⊗ M ↦ A ⊗ M`. -/
def kronTensor : Adjointable B ⊗[ℂ] Matrix n n ℂ →ₐ[ℂ] Adjointable (B × n) :=
  Algebra.TensorProduct.lift (kronLeft : Adjointable B →⋆ₐ[ℂ] Adjointable (B × n)).toAlgHom
    (kronRight : Matrix n n ℂ →⋆ₐ[ℂ] Adjointable (B × n)).toAlgHom
    (fun A M => kronLeft_kronRight_comm A M)

lemma kronTensor_tmul (A : Adjointable B) (M : Matrix n n ℂ) :
    kronTensor (A ⊗ₜ[ℂ] M) = kron A M := by
  show kronLeft A * kronRight M = kron A M
  show kron A 1 * kron 1 M = kron A M
  rw [← kron_mul, mul_one, one_mul]

lemma kronTensor_star_tmul (A : Adjointable B) (M : Matrix n n ℂ) :
    star (kronTensor (A ⊗ₜ[ℂ] M)) = kronTensor (star A ⊗ₜ[ℂ] star M) := by
  rw [kronTensor_tmul, kronTensor_tmul, kron_star, Matrix.star_eq_conjTranspose]

end Algebra

end InfiniteBosons
