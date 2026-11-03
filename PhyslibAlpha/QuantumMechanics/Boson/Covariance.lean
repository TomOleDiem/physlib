/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Boson.BuchholzAlgebra
/-!

# Covariance of the connecting maps and automorphisms of the Buchholz algebra

One-particle unitaries commute with the connecting homomorphisms and act on the Buchholz algebra.

## i. Overview

A star homomorphism out of a sector algebra is determined by its values on the generators, since
it is continuous and the generators generate a dense star subalgebra. The connecting homomorphism
and the automorphisms induced by a one-particle unitary agree on the generators up to the order of
composition. Hence they commute. A one-particle unitary therefore induces an automorphism of the
whole Buchholz algebra. For `U = e^{ith}` this is the free time evolution.

## ii. Key results

- `Boson.sectorAlgebra_hom_ext`: star homomorphisms out of `𝔎_n` are determined on generators.

## iii. Table of contents

- A. Extensionality on generators

## iv. References

* A. Deuchert, J. Lampart and M. Lemm, Dynamics and equilibrium states of infinite systems of
  lattice bosons, arXiv:2505.13170, Section 3.
-/

@[expose] public section

universe u

open HilbertPower Filter Topology

noncomputable section

namespace Boson

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]

/-!

## A. Extensionality on generators

-/

/-- **Star homomorphisms out of a sector algebra are determined on the generators.** -/
lemma sectorAlgebra_hom_ext {n : ℕ} {T : Type*} [CStarAlgebra T]
    (f g : sectorAlgebra h n →⋆ₐ[ℂ] T)
    (hgen : ∀ (A : sym h n →L[ℂ] sym h n) (hA : A ∈ genSet h n),
      f ⟨A, StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ hA)⟩ =
        g ⟨A, StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ hA)⟩) :
    f = g := by
  letI : CStarAlgebra (sym h n →L[ℂ] sym h n) := inferInstance
  let E : StarSubalgebra ℂ (sectorAlgebra h n) := StarAlgHom.equalizer f g
  have hfc : Continuous f := by
    refine AddMonoidHomClass.continuous_of_bound f 1 fun A => ?_
    simpa using NonUnitalStarAlgHom.norm_apply_le f A
  have hgc : Continuous g := by
    refine AddMonoidHomClass.continuous_of_bound g 1 fun A => ?_
    simpa using NonUnitalStarAlgHom.norm_apply_le g A
  have hE : IsClosed (E : Set (sectorAlgebra h n)) :=
    isClosed_eq hfc hgc
  have hSc : IsClosed ((sectorAlgebra h n : Set (sym h n →L[ℂ] sym h n))) :=
    isClosed_sectorAlgebra h n
  have hEm : IsClosed ((E.map (sectorAlgebra h n).subtype : StarSubalgebra ℂ _) :
      Set (sym h n →L[ℂ] sym h n)) := by
    have : ((E.map (sectorAlgebra h n).subtype : StarSubalgebra ℂ _) :
        Set (sym h n →L[ℂ] sym h n)) = Subtype.val '' (E : Set (sectorAlgebra h n)) := by
      ext x; simp [StarSubalgebra.coe_map]
    rw [this]
    have hemb : Topology.IsClosedEmbedding
        (Subtype.val : sectorAlgebra h n → (sym h n →L[ℂ] sym h n)) :=
      Topology.IsClosedEmbedding.subtypeVal hSc
    exact hemb.isClosedMap _ hE
  have hgenE : genSet h n ⊆ (E.map (sectorAlgebra h n).subtype : Set _) := by
    intro A hA
    exact ⟨⟨A, StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ hA)⟩,
      hgen A hA, rfl⟩
  have hle : sectorAlgebra h n ≤ E.map (sectorAlgebra h n).subtype :=
    StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le hgenE) hEm
  refine StarAlgHom.ext fun X => ?_
  obtain ⟨Y, hY, hYX⟩ := hle X.2
  have : Y = X := Subtype.ext hYX
  rw [← this]
  exact hY

/-!

## B. The connecting homomorphism on generators

-/

lemma gen_mem (n : ℕ) {A : sym h n →L[ℂ] sym h n} (hA : A ∈ genSet h n) : A ∈ sectorAlgebra h n :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ hA)

/-- **The connecting homomorphism on a generator with free factors.** -/
lemma kappa_gen_succ {φ : ℕ → h} (hφ : Orthonormal ℂ φ) {m : ℕ} (K : sym h m →L[ℂ] sym h m)
    (hK : IsCompactOperator K) (hK' : IsCompactOperator (ContinuousLinearMap.adjoint K)) (k : ℕ) :
    ((kappa hφ (m + k) ⟨(gen K (k + 1) : sym h (m + k + 1) →L[ℂ] sym h (m + k + 1)),
        gen_mem _ ⟨m, k + 1, rfl, K, hK, hK', rfl⟩⟩ : sectorAlgebra h (m + k)) :
          sym h (m + k) →L[ℂ] sym h (m + k)) =
      ((k + 1 : ℂ) / (m + k + 1 : ℂ)) • gen K k :=
  kappaHom_gen hφ (m + k) ⟨m, k + 1, rfl, K, hK, hK', rfl⟩ (intertwines_gen_succ hφ K hK k)

/-- **The connecting homomorphism kills a generator with no free factors.** -/
lemma kappa_gen_zero {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (n : ℕ)
    (K : sym h (n + 1) →L[ℂ] sym h (n + 1)) (hK : IsCompactOperator K)
    (hK' : IsCompactOperator (ContinuousLinearMap.adjoint K)) :
    ((kappa hφ n ⟨K, gen_mem _ (A := K) (by
        refine ⟨n + 1, 0, rfl, K, hK, hK', ?_⟩
        exact (gen_zero K).symm)⟩ : sectorAlgebra h n) : sym h n →L[ℂ] sym h n) = 0 :=
  kappaHom_gen hφ n (A := K) (by
        refine ⟨n + 1, 0, rfl, K, hK, hK', ?_⟩
        exact (gen_zero K).symm) (by
    change AsymptoticIntertwiner.Intertwines (creSeq φ n) K 0
    exact intertwines_compact hφ K hK)

/-!

## C. Covariance

-/

set_option maxHeartbeats 1600000 in
/-- **One-particle unitaries commute with the connecting homomorphism.** -/
theorem kappa_comp_sectorHom {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (U : h ≃ₗᵢ[ℂ] h) (n : ℕ) :
    (kappa hφ n).comp (sectorHom h U (n + 1)) = (sectorHom h U n).comp (kappa hφ n) := by
  refine sectorAlgebra_hom_ext _ _ fun A hA => ?_
  obtain ⟨m, k, e, K, hK, hK', hAeq⟩ := hA
  subst hAeq
  rcases k with _ | k
  · obtain rfl : m = n + 1 := e
    suffices H : ∀ X : sectorAlgebra h (n + 1),
        (X : sym h (n + 1) →L[ℂ] sym h (n + 1)) = K →
        (kappa hφ n) (sectorHom h U (n + 1) X) = (sectorHom h U n) (kappa hφ n X) from
      H _ (gen_zero K)
    intro X hX
    set K' : sym h (n + 1) →L[ℂ] sym h (n + 1) :=
      (symUnitary h U (n + 1) : sym h (n + 1) →L[ℂ] sym h (n + 1)) * K *
        star (symUnitary h U (n + 1) : sym h (n + 1) →L[ℂ] sym h (n + 1)) with hK'def
    have hc1 : IsCompactOperator K' := isCompact_conj h (symUnitary h U (n + 1)) hK
    have hc2 : IsCompactOperator (ContinuousLinearMap.adjoint K') :=
      isCompact_conj_adjoint h (symUnitary h U (n + 1)) hK'
    have hK0 : K ∈ genSet h (n + 1) := ⟨n + 1, 0, rfl, K, hK, hK', (gen_zero K).symm⟩
    have hK0' : K' ∈ genSet h (n + 1) := ⟨n + 1, 0, rfl, K', hc1, hc2, (gen_zero K').symm⟩
    have hX' : X = ⟨K, gen_mem _ hK0⟩ := Subtype.ext hX
    have hs : sectorHom h U (n + 1) X = ⟨K', gen_mem _ hK0'⟩ :=
      Subtype.ext (by rw [sectorHom_apply, hX])
    rw [hs, hX']
    apply Subtype.ext
    have e1 := kappa_gen_zero hφ n K' hc1 hc2
    have e2 := kappa_gen_zero hφ n K hK hK'
    rw [e1, sectorHom_apply, e2]
    simp
  · obtain rfl : n = m + k := (Nat.succ.inj e).symm
    set K' : sym h m →L[ℂ] sym h m := (symUnitary h U m : sym h m →L[ℂ] sym h m) * K *
      star (symUnitary h U m : sym h m →L[ℂ] sym h m) with hK'def
    have hc1 : IsCompactOperator K' := isCompact_conj h (symUnitary h U m) hK
    have hc2 : IsCompactOperator (ContinuousLinearMap.adjoint K') :=
      isCompact_conj_adjoint h (symUnitary h U m) hK'
    have hG : (gen K (k + 1) : sym h (m + k + 1) →L[ℂ] sym h (m + k + 1)) ∈
        genSet h (m + k + 1) := ⟨m, k + 1, rfl, K, hK, hK', rfl⟩
    have hG' : (gen K' (k + 1) : sym h (m + k + 1) →L[ℂ] sym h (m + k + 1)) ∈
        genSet h (m + k + 1) := ⟨m, k + 1, rfl, K', hc1, hc2, rfl⟩
    have hs : sectorHom h U (m + k + 1) ⟨gen K (k + 1), gen_mem _ hG⟩ =
        ⟨gen K' (k + 1), gen_mem _ hG'⟩ :=
      Subtype.ext (by rw [sectorHom_apply]; exact conj_gen h U K (k + 1))
    change (kappa hφ (m + k)) ((sectorHom h U (m + k + 1)) ⟨gen K (k + 1), gen_mem _ hG⟩) =
      (sectorHom h U (m + k)) ((kappa hφ (m + k)) ⟨gen K (k + 1), gen_mem _ hG⟩)
    rw [hs]
    apply Subtype.ext
    have e1 : ((kappa hφ (m + k) ⟨gen K' (k + 1), gen_mem _ hG'⟩ : sectorAlgebra h (m + k)) :
        sym h (m + k) →L[ℂ] sym h (m + k)) =
        ((k + 1 : ℂ) / (m + k + 1 : ℂ)) • gen K' k := kappa_gen_succ hφ K' hc1 hc2 k
    have e2 : ((kappa hφ (m + k) ⟨gen K (k + 1), gen_mem _ hG⟩ : sectorAlgebra h (m + k)) :
        sym h (m + k) →L[ℂ] sym h (m + k)) =
        ((k + 1 : ℂ) / (m + k + 1 : ℂ)) • gen K k := kappa_gen_succ hφ K hK hK' k
    have e3 : ((sectorHom h U (m + k) (kappa hφ (m + k) ⟨gen K (k + 1), gen_mem _ hG⟩) :
        sectorAlgebra h (m + k)) : sym h (m + k) →L[ℂ] sym h (m + k)) =
        (symUnitary h U (m + k) : sym h (m + k) →L[ℂ] sym h (m + k)) *
          (((k + 1 : ℂ) / (m + k + 1 : ℂ)) • gen K k) *
          star (symUnitary h U (m + k) : sym h (m + k) →L[ℂ] sym h (m + k)) := by
      rw [sectorHom_apply, e2]
    letI : CStarAlgebra (sym h (m + k) →L[ℂ] sym h (m + k)) := inferInstance
    rw [e1, e3, mul_smul_comm, smul_mul_assoc, conj_gen h U K k]

/-!

## D. Automorphisms of the Buchholz algebra

-/

lemma sectorEquiv_apply (U : h ≃ₗᵢ[ℂ] h) (n : ℕ) (X : sectorAlgebra h n) :
    sectorEquiv h U n X = sectorHom h U n X := rfl

lemma kappa_sectorEquiv {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (U : h ≃ₗᵢ[ℂ] h) (n : ℕ)
    (x : sectorAlgebra h (n + 1)) :
    kappa hφ n (sectorEquiv h U (n + 1) x) = sectorEquiv h U n (kappa hφ n x) :=
  congrArg (fun f => f x) (kappa_comp_sectorHom hφ U n)

set_option maxHeartbeats 6400000 in
/-- **A one-particle unitary acts on the Buchholz algebra.** The automorphisms of the sector
algebras commute with the connecting homomorphisms and therefore induce an automorphism of the
bounded inverse limit. -/
def buchholzEquiv [Nontrivial h] {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (U : h ≃ₗᵢ[ℂ] h) :
    buchholzAlgebra hφ ≃⋆ₐ[ℂ] buchholzAlgebra hφ :=
  InverseLimit.mapEquiv (fun n => kappa hφ n) (fun n => kappa hφ n)
    (fun n => sectorEquiv h U n) (kappa_sectorEquiv hφ U)

end Boson
