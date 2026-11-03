/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Boson.Covariance
public import Mathlib.Analysis.CStarAlgebra.Exponential
/-!

# Free dynamics of the Buchholz algebra

The free evolution of an infinite bosonic system by a bounded self-adjoint one-particle
Hamiltonian.

## i. Overview

A bounded self-adjoint operator `a` on the one-particle space generates the unitary group
`U_t = exp(i t a)`. Each `U_t` acts on the Buchholz algebra by an automorphism, and the
automorphisms form a group. The evolution is algebraic. No continuity in `t` is claimed.

## ii. Key results

- `Boson.buchholzEquiv_trans`: the action of a composite is the composite of the actions.
- `Boson.freeU`: the one-parameter unitary group of a self-adjoint operator.
- `Boson.freeDynamics`: the free dynamics on the Buchholz algebra.
- `Boson.freeDynamics_add`: the group law.

## iii. Table of contents

- A. The action of unitaries
- B. The free dynamics

## iv. References

* A. Deuchert, J. Lampart and M. Lemm, Dynamics and equilibrium states of infinite systems of
  lattice bosons, arXiv:2505.13170, Section 3.
-/

@[expose] public section

universe u

open HilbertPower

noncomputable section

namespace Boson

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]
  [Nontrivial h]

/-!

## A. The action of unitaries

-/

lemma buchholzEquiv_apply_coe {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (U : h ≃ₗᵢ[ℂ] h)
    (x : buchholzAlgebra hφ) (n : ℕ) :
    ((buchholzEquiv hφ U x : buchholzAlgebra hφ).1 n : sectorAlgebra h n) =
      sectorEquiv h U n (x.1 n) := rfl

set_option maxHeartbeats 1600000 in
lemma buchholzEquiv_ext {φ : ℕ → h} (hφ : Orthonormal ℂ φ)
    (e e' : buchholzAlgebra hφ ≃⋆ₐ[ℂ] buchholzAlgebra hφ)
    (H : ∀ x n, ((e x : buchholzAlgebra hφ).1 n : sectorAlgebra h n) =
      ((e' x : buchholzAlgebra hφ).1 n : sectorAlgebra h n)) : e = e' := by
  refine StarAlgEquiv.ext fun x => Subtype.ext (Subtype.ext (funext fun n => ?_))
  exact H x n

set_option maxHeartbeats 1600000 in
/-- **The action on the Buchholz algebra respects composition.** -/
lemma buchholzEquiv_trans {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (U V : h ≃ₗᵢ[ℂ] h) :
    buchholzEquiv hφ (U.trans V) = (buchholzEquiv hφ U).trans (buchholzEquiv hφ V) := by
  refine buchholzEquiv_ext hφ _ _ fun x n => ?_
  show sectorEquiv h (U.trans V) n (x.1 n) = sectorEquiv h V n (sectorEquiv h U n (x.1 n))
  rw [sectorEquiv_apply, sectorEquiv_apply, sectorEquiv_apply, sectorHom_trans]
  rfl

/-!

## B. The free dynamics

-/

/-- A one-parameter group of one-particle unitaries. -/
structure UnitaryGroup (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h] where
  /-- The unitary at time `t`. -/
  U : ℝ → (h ≃ₗᵢ[ℂ] h)
  /-- The unitary at time zero is the identity. -/
  zero : U 0 = LinearIsometryEquiv.refl ℂ h
  /-- The group law. -/
  add : ∀ s t, U (s + t) = (U t).trans (U s)

/-- **The dynamics of the Buchholz algebra induced by a one-parameter unitary group.** -/
def freeDynamics {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (G : UnitaryGroup h) (t : ℝ) :
    buchholzAlgebra hφ ≃⋆ₐ[ℂ] buchholzAlgebra hφ :=
  buchholzEquiv hφ (G.U t)

lemma sectorEquiv_trans_apply (U V : h ≃ₗᵢ[ℂ] h) (n : ℕ) (X : sectorAlgebra h n) :
    sectorEquiv h (U.trans V) n X = sectorEquiv h V n (sectorEquiv h U n X) := by
  rw [sectorEquiv_apply, sectorEquiv_apply, sectorEquiv_apply, sectorHom_trans]
  rfl

lemma sectorEquiv_refl_apply (n : ℕ) (X : sectorAlgebra h n) :
    sectorEquiv h (LinearIsometryEquiv.refl ℂ h) n X = X := by
  rw [sectorEquiv_apply]
  refine Subtype.ext ?_
  rw [sectorHom_apply]
  have hu : (symUnitary h (LinearIsometryEquiv.refl ℂ h) n : sym h n →L[ℂ] sym h n) = 1 := by
    show symAct (opOf h (LinearIsometryEquiv.refl ℂ h)) n = 1
    have : opOf h (LinearIsometryEquiv.refl ℂ h) = ContinuousLinearMap.id ℂ h := rfl
    rw [this, symAct_id]; rfl
  have hs : star (1 : sym h n →L[ℂ] sym h n) = 1 := by
    rw [ContinuousLinearMap.star_eq_adjoint]; exact ContinuousLinearMap.adjoint_id
  rw [hu, hs, mul_one, one_mul]

set_option maxHeartbeats 3200000 in
/-- **The group law of the dynamics, on elements**: `τ_{s+t} = τ_s ∘ τ_t` componentwise. -/
lemma freeDynamics_add_apply {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (G : UnitaryGroup h) (s t : ℝ)
    (x : buchholzAlgebra hφ) (n : ℕ) :
    ((freeDynamics hφ G (s + t) x : buchholzAlgebra hφ).1 n : sectorAlgebra h n) =
      ((freeDynamics hφ G s (freeDynamics hφ G t x) : buchholzAlgebra hφ).1 n :
        sectorAlgebra h n) := by
  have e0 := buchholzEquiv_apply_coe hφ (G.U (s + t)) x n
  have e1 := buchholzEquiv_apply_coe hφ (G.U s) (buchholzEquiv hφ (G.U t) x) n
  have e2 := buchholzEquiv_apply_coe hφ (G.U t) x n
  have e3 : sectorEquiv h (G.U (s + t)) n (x.1 n) =
      sectorEquiv h (G.U s) n (sectorEquiv h (G.U t) n (x.1 n)) := by
    rw [G.add s t, sectorEquiv_trans_apply]
  exact e0.trans (e3.trans ((congrArg (sectorEquiv h (G.U s) n) e2.symm).trans e1.symm))

set_option maxHeartbeats 3200000 in
/-- **The dynamics at time zero is the identity**, componentwise. -/
lemma freeDynamics_zero_apply {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (G : UnitaryGroup h)
    (x : buchholzAlgebra hφ) (n : ℕ) :
    ((freeDynamics hφ G 0 x : buchholzAlgebra hφ).1 n : sectorAlgebra h n) = x.1 n := by
  have e0 := buchholzEquiv_apply_coe hφ (G.U 0) x n
  have e3 : sectorEquiv h (G.U 0) n (x.1 n) = x.1 n := by
    rw [G.zero, sectorEquiv_refl_apply]
  exact e0.trans e3

/-!

## C. The unitary group of a self-adjoint operator

-/

/-- The self-adjoint element `t a` for a real `t`. -/
def realSmul (a : h →L[ℂ] h) (ha : IsSelfAdjoint a) (t : ℝ) : selfAdjoint (h →L[ℂ] h) :=
  ⟨(t : ℂ) • a, by
    rw [selfAdjoint.mem_iff, star_smul, ha.star_eq]
    simp⟩

/-- **The unitary group `exp(i t a)` of a bounded self-adjoint operator.** -/
def expGroup (a : h →L[ℂ] h) (ha : IsSelfAdjoint a) : UnitaryGroup h where
  U t := Unitary.linearIsometryEquiv (selfAdjoint.expUnitary (realSmul a ha t))
  zero := by
    have : realSmul a ha 0 = 0 := Subtype.ext (by simp [realSmul])
    rw [this, selfAdjoint.expUnitary_zero, map_one]
    rfl
  add s t := by
    have hc : Commute ((realSmul a ha s : selfAdjoint (h →L[ℂ] h)) : h →L[ℂ] h)
        ((realSmul a ha t : selfAdjoint (h →L[ℂ] h)) : h →L[ℂ] h) := by
      simp only [realSmul]
      exact ((Commute.refl a).smul_left _).smul_right _
    have : realSmul a ha (s + t) = realSmul a ha s + realSmul a ha t :=
      Subtype.ext (by simp [realSmul, add_smul])
    rw [this, Commute.expUnitary_add hc, map_mul]
    rfl

end Boson
