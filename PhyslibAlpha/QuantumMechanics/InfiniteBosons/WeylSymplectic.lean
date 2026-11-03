/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.WeylCStar
public import Mathlib.Analysis.CStarAlgebra.Spectrum
/-!

# Symplectic maps as automorphisms of the Weyl C*-algebra

Exact quadratic dynamics of an infinite bosonic system as automorphisms of the CCR C*-algebra.

## i. Overview

A symplectic linear equivalence `S` of `V` acts on `ℓ²(V)` by the unitary `ψ ↦ ψ ∘ S⁻¹`. This
unitary intertwines `W(f)` and `W(S f)`. Conjugation by it is therefore a star automorphism of the
Weyl C*-algebra, determined by `W(f) ↦ W(S f)`. It carries the algebra of a region onto the algebra
of the image region. The automorphisms form a group. No Fock representation is used, so the
statement does not require the symplectic map to be unitarily implementable in a Fock space. The
time evolution of a quadratic Hamiltonian is a one-parameter group of symplectic maps and acts
this way. The continuity of the group in time is not claimed.

## ii. Key results

- `InfiniteBosons.symplecticU_weylU`: covariance of the regular representation.
- `InfiniteBosons.conj_mem_weylCStarOn`: covariance of the net.
- `InfiniteBosons.weylAut`: the automorphism of the Weyl C*-algebra.

## iii. Table of contents

- A. Implementing unitaries
- B. Covariance of the net
- C. The automorphism

## iv. References

* J. Dereziński and C. Gérard, Mathematics of Quantization and Quantum Fields, Cambridge
  University Press (2013), Chapter 17.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (σ : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- The unitary implementing a symplectic linear equivalence on `ℓ²(V)`. -/
def symplecticU (S : V ≃ₗ[ℝ] V) : HilbertSp V ≃ₗᵢ[ℂ] HilbertSp V :=
  reindexEquiv S.symm.toEquiv

lemma symplecticU_apply (S : V ≃ₗ[ℝ] V) (ψ : HilbertSp V) (h : V) :
    (symplecticU S ψ : HilbertSp V) h = ψ (S.symm h) := rfl

/-- **Covariance of the regular representation**: a symplectic map `S` is implemented by a unitary
that intertwines `W(f)` and `W(S f)`. -/
lemma symplecticU_weylU (S : V ≃ₗ[ℝ] V) (hS : ∀ f g, σ (S f) (S g) = σ f g) (f : V)
    (ψ : HilbertSp V) :
    symplecticU S (weylU σ f ψ) = weylU σ (S f) (symplecticU S ψ) := by
  refine Subtype.ext (funext fun h => ?_)
  rw [symplecticU_apply, weylU_apply, weylU_apply, symplecticU_apply]
  have e1 : S.symm (h - S f) = S.symm h - f := by simp
  have e2 : weylPhase σ f (S.symm h) = weylPhase σ (S f) h := by
    unfold weylPhase
    congr 3
    have := hS f (S.symm h)
    simp at this
    rw [this]
  rw [e1, e2]


/-- Conjugation by the implementing unitary maps `W(f)` to `W(S f)`. -/
lemma conj_weylOp (S : V ≃ₗ[ℝ] V) (hS : ∀ f g, σ (S f) (S g) = σ f g) (f : V) :
    (symplecticU S).conjStarAlgEquiv (weylOp σ f) = weylOp σ (S f) := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, weylOp_apply, weylOp_apply]
  have := symplecticU_weylU σ S hS f ((symplecticU S).symm ψ)
  rw [LinearIsometryEquiv.apply_symm_apply] at this
  exact this

/-- **Covariance of the Weyl C*-net**: a symplectic map carries the algebra of a region onto the
algebra of its image. -/
lemma conj_mem_weylCStarOn (S : V ≃ₗ[ℝ] V) (hS : ∀ f g, σ (S f) (S g) = σ f g) {T : Set V}
    {X : HilbertSp V →L[ℂ] HilbertSp V} (hX : X ∈ weylCStarOn σ T) :
    (symplecticU S).conjStarAlgEquiv X ∈ weylCStarOn σ (S '' T) := by
  letI : CStarAlgebra (HilbertSp V →L[ℂ] HilbertSp V) := inferInstance
  let f := (symplecticU S).conjStarAlgEquiv
  let R : StarSubalgebra ℂ (HilbertSp V →L[ℂ] HilbertSp V) :=
    (weylCStarOn σ (S '' T)).comap f.toStarAlgHom
  have hRc : IsClosed (R : Set (HilbertSp V →L[ℂ] HilbertSp V)) := by
    have hc : Continuous f := by
      refine AddMonoidHomClass.continuous_of_bound f 1 fun A => ?_
      simpa using NonUnitalStarAlgHom.norm_apply_le f A
    exact (isClosed_weylCStarOn σ (S '' T)).preimage hc
  have hgen : (weylOp σ '' T) ⊆ (R : Set _) := by
    rintro _ ⟨g, hg, rfl⟩
    show f (weylOp σ g) ∈ weylCStarOn σ (S '' T)
    rw [conj_weylOp σ S hS]
    exact weylOp_mem_cstar σ ⟨g, hg, rfl⟩
  have hle : weylCStarOn σ T ≤ R :=
    StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le hgen) hRc
  exact hle hX


lemma symplecticU_trans (S₁ S₂ : V ≃ₗ[ℝ] V) :
    symplecticU (S₁.trans S₂) = (symplecticU S₁).trans (symplecticU S₂) := by
  refine LinearIsometryEquiv.ext fun ψ => Subtype.ext (funext fun h => ?_)
  rfl

lemma symplecticU_refl : symplecticU (LinearEquiv.refl ℝ V) = LinearIsometryEquiv.refl ℂ _ := by
  refine LinearIsometryEquiv.ext fun ψ => Subtype.ext (funext fun h => ?_)
  rfl

/-- A symplectic map acts on the whole Weyl C*-algebra by a star endomorphism. -/
def weylHom (S : V ≃ₗ[ℝ] V) (hS : ∀ f g, σ (S f) (S g) = σ f g) :
    weylCStarOn σ Set.univ →⋆ₐ[ℂ] weylCStarOn σ Set.univ where
  toFun X := ⟨(symplecticU S).conjStarAlgEquiv X, by
    have := conj_mem_weylCStarOn σ S hS X.2
    have e : S '' (Set.univ : Set V) = Set.univ := by
      ext h; simp
    rwa [e] at this⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' X Y := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' X Y := Subtype.ext (map_add _ _ _)
  commutes' r := Subtype.ext (AlgEquivClass.commutes _ r)
  map_star' X := Subtype.ext (map_star _ _)


lemma conj_comp_symm (S : V ≃ₗ[ℝ] V) (X : HilbertSp V →L[ℂ] HilbertSp V) :
    (symplecticU S.symm).conjStarAlgEquiv ((symplecticU S).conjStarAlgEquiv X) = X := by
  have h1 : S.trans S.symm = LinearEquiv.refl ℝ V := by
    refine LinearEquiv.ext fun f => ?_
    simp
  have h2 := symplecticU_trans S S.symm
  rw [h1, symplecticU_refl] at h2
  have h3 : (symplecticU S.symm).conjStarAlgEquiv ((symplecticU S).conjStarAlgEquiv X) =
      ((symplecticU S).trans (symplecticU S.symm)).conjStarAlgEquiv X := rfl
  rw [h3, ← h2]
  rfl

lemma conj_symm_comp (S : V ≃ₗ[ℝ] V) (X : HilbertSp V →L[ℂ] HilbertSp V) :
    (symplecticU S).conjStarAlgEquiv ((symplecticU S.symm).conjStarAlgEquiv X) = X := by
  have := conj_comp_symm S.symm X
  simpa using this

/-- **A symplectic map is an automorphism of the Weyl C*-algebra.** The automorphism sends the Weyl
unitary `W(f)` to `W(S f)`. -/
def weylAut (S : V ≃ₗ[ℝ] V) (hS : ∀ f g, σ (S f) (S g) = σ f g) :
    weylCStarOn σ Set.univ ≃⋆ₐ[ℂ] weylCStarOn σ Set.univ :=
  have hS' : ∀ f g, σ (S.symm f) (S.symm g) = σ f g := fun f g => by
    have := hS (S.symm f) (S.symm g)
    simpa using this.symm
  StarAlgEquiv.ofStarAlgHom (weylHom σ S hS) (weylHom σ S.symm hS')
    (StarAlgHom.ext fun X => Subtype.ext (conj_comp_symm S _))
    (StarAlgHom.ext fun X => Subtype.ext (conj_symm_comp S _))


lemma weylAut_weylOp (S : V ≃ₗ[ℝ] V) (hS : ∀ f g, σ (S f) (S g) = σ f g) (f : V) :
    ((weylAut σ S hS ⟨weylOp σ f, weylOp_mem_cstar σ (Set.mem_univ f)⟩ :
      weylCStarOn σ Set.univ) : HilbertSp V →L[ℂ] HilbertSp V) = weylOp σ (S f) :=
  conj_weylOp σ S hS f

end InfiniteBosons
