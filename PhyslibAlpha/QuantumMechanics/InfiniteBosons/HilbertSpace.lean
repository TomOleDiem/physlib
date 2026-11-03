/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.PolynomialAlgebra
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.l2Space
/-!

# Polynomial observables as closable operators on a Hilbert space

The algebraic Fock space sits densely in `ℓ²` of its basis, and every polynomial observable is a
closable operator there.

## i. Overview

The algebraic space with basis `B` is the space of finite linear combinations of basis vectors. Its
completion is the Hilbert space `ℓ²(B)`. The embedding preserves the sesquilinear pairing, and its
range is dense. A formally adjointable operator is a densely defined operator on the range. The
formal adjoint is a densely defined operator that is a formal adjoint in the sense of Hilbert space
operators, so the Hilbert adjoint of the formal adjoint is a closed extension. Hence every
formally adjointable operator, and in particular every polynomial in the creation and annihilation
operators, is closable. This is the first arrow of the bridge from polynomial observables to bounded
ones: polynomial → closable operator. The next arrows need essential self-adjointness and the
spectral theorem, and they hold under explicit hypotheses.

## ii. Key results

- `InfiniteBosons.HilbertSp`: the Hilbert space `ℓ²(B)`.
- `InfiniteBosons.embed`, `InfiniteBosons.inner_embed`, `InfiniteBosons.dense_range_embed`.
- `InfiniteBosons.polyOp`: an adjointable operator as a densely defined operator.
- `InfiniteBosons.polyOp_isClosable`: it is closable.

## iii. Table of contents

- A. The Hilbert space and the embedding
- B. Densely defined operators
- C. Closability

## iv. References

* K. Schmüdgen, Unbounded Self-adjoint Operators on Hilbert Space, Springer (2012), Chapter 1.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {B : Type*} [DecidableEq B]

/-- The Hilbert completion `ℓ²(B)` of the algebraic space with basis `B`. -/
abbrev HilbertSp (B : Type*) := lp (fun _ : B => ℂ) 2

/-- Finite linear combinations of basis vectors as elements of `ℓ²(B)`. -/
def embed : (B →₀ ℂ) →ₗ[ℂ] HilbertSp B :=
  Finsupp.lsum ℂ fun α => (lp.singleContinuousLinearMap ℂ (fun _ : B => ℂ) 2 α).toLinearMap

lemma embed_single (α : B) (c : ℂ) : embed (single α c) = lp.single 2 α c := by
  simp [embed, Finsupp.lsum_single]

lemma embed_apply (f : B →₀ ℂ) (α : B) : (embed f : HilbertSp B) α = f α := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single β c =>
    rw [embed_single]
    by_cases h : β = α
    · subst h; simp
    · simp [lp.single_apply_ne _ _ _ (Ne.symm h), Finsupp.single_apply, h]

lemma embed_injective : Function.Injective (embed : (B →₀ ℂ) →ₗ[ℂ] HilbertSp B) := by
  intro f g h
  ext α
  rw [← embed_apply f α, ← embed_apply g α, h]

lemma inner_embed (f g : B →₀ ℂ) : inner ℂ (embed f) (embed g) = pair f g := by
  induction f using Finsupp.induction_linear with
  | zero => simp [pair_zero_left]
  | add f f' hf hf' => rw [map_add, inner_add_left, hf, hf', pair_add_left]
  | single α c =>
    induction g using Finsupp.induction_linear with
    | zero => simp [pair_zero_right]
    | add g g' hg hg' => rw [map_add, inner_add_right, hg, hg', pair_add_right]
    | single β d =>
      rw [embed_single, embed_single, pair_single_single, lp.inner_single_left]
      by_cases h : α = β
      · subst h; simp [mul_comm]
      · simp [lp.single_apply_ne _ _ _ (Ne.symm h), h]


lemma dense_range_embed :
    Dense (LinearMap.range (embed : (B →₀ ℂ) →ₗ[ℂ] HilbertSp B) : Set (HilbertSp B)) := by
  intro f
  have h := lp.hasSum_single (E := fun _ : B => ℂ) (p := 2) ENNReal.ofNat_ne_top f
  refine mem_closure_of_tendsto h (Filter.Eventually.of_forall fun t => ?_)
  refine Submodule.sum_mem _ fun i _ => ?_
  exact ⟨single i (f i), embed_single i (f i)⟩

/-- The algebraic operator `A` as a densely defined operator of `ℓ²(B)`. -/
def toPMap (A : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)) : HilbertSp B →ₗ.[ℂ] HilbertSp B where
  domain := LinearMap.range embed
  toFun := (embed ∘ₗ A) ∘ₗ (LinearEquiv.ofInjective embed embed_injective).symm.toLinearMap

lemma toPMap_embed (A : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)) (f : B →₀ ℂ) :
    toPMap A ⟨embed f, LinearMap.mem_range_self embed f⟩ = embed (A f) := by
  show (embed ∘ₗ A) ((LinearEquiv.ofInjective embed embed_injective).symm ⟨embed f, LinearMap.mem_range_self embed f⟩) = _
  have : (LinearEquiv.ofInjective embed embed_injective).symm ⟨embed f, LinearMap.mem_range_self embed f⟩ = f := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  rw [this]; rfl


/-- The densely defined operator of an adjointable operator. -/
def polyOp (p : Adjointable B) : HilbertSp B →ₗ.[ℂ] HilbertSp B := toPMap p.1.1

lemma dense_domain_polyOp (p : Adjointable B) : Dense ((polyOp p).domain : Set (HilbertSp B)) :=
  dense_range_embed

lemma polyOp_embed (p : Adjointable B) (f : B →₀ ℂ) :
    polyOp p ⟨embed f, LinearMap.mem_range_self embed f⟩ = embed (p.1.1 f) :=
  toPMap_embed p.1.1 f

lemma star_fst_pair (p : Adjointable B) (f g : B →₀ ℂ) :
    pair ((star p).1.1 f) g = pair f (p.1.1 g) := by
  have h := mem_adjointable.mp (star p).2 f g
  have e : toEnd (MulOpposite.unop (star p).1.2) = p.1.1 := by
    show toEnd (MulOpposite.unop (MulOpposite.op (ofEnd p.1.1))) = p.1.1
    simp [toEnd_ofEnd]
  rw [e] at h
  exact h

/-- **The operator of `p*` is a formal adjoint of the operator of `p`.** -/
lemma polyOp_formalAdjoint (p : Adjointable B) : (polyOp (star p)).IsFormalAdjoint (polyOp p) := by
  rintro ⟨_, ⟨f, rfl⟩⟩ ⟨_, ⟨g, rfl⟩⟩
  show inner ℂ (polyOp (star p) ⟨embed f, LinearMap.mem_range_self embed f⟩) (embed g) =
    inner ℂ (embed f) (polyOp p ⟨embed g, LinearMap.mem_range_self embed g⟩)
  rw [polyOp_embed, polyOp_embed, inner_embed, inner_embed, star_fst_pair]

/-- **Every polynomial is a closable operator** of the Hilbert space `ℓ²(B)`. -/
theorem polyOp_isClosable (p : Adjointable B) : (polyOp p).IsClosable := by
  rw [LinearPMap.isClosable_iff_exists_closed_extension]
  refine ⟨(polyOp (star p)).adjoint, LinearPMap.adjoint_isClosed (dense_domain_polyOp _), ?_⟩
  exact LinearPMap.IsFormalAdjoint.le_adjoint (dense_domain_polyOp _) (polyOp_formalAdjoint p)

end InfiniteBosons
