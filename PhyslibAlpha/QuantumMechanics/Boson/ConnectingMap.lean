/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Boson.SectorAlgebra
public import PhyslibAlpha.QuantumMechanics.Boson.Intertwining
public import PhyslibAlpha.Mathematics.OperatorAlgebra.AsymptoticIntertwiner
/-!

# The connecting maps of the particle-sector algebras

The homomorphism that sends an `n`-particle observable to the observable of the remaining
`n - 1` particles when one particle escapes to infinity.

## i. Overview

Let `φ_j` be an orthonormal sequence in the one-particle space. The creation operators
`a†(φ_j)` from the `(n-1)`-particle space to the `n`-particle space are uniformly bounded and
asymptotically isometric. An operator on `Sym^n` whose adjoint also has an asymptotic intertwiner
along `a†(φ_j)` has a unique intertwiner on `Sym^{n-1}`. The assignment is a star homomorphism.
The generators of the sector algebra have intertwiners: `gen K (k+1)` goes to
`((k+1)/(m+k+1))` times `gen K k`, and `gen K 0` goes to zero.

## ii. Key results

- `Boson.creSeq`: the sequence `a†(φ_j)`.
- `Boson.gen_zero`: `gen K 0 = K`.

## iii. Table of contents

- A. The sequence of creation operators
- B. Generators have intertwiners

## iv. References

* A. Deuchert, J. Lampart and M. Lemm, Dynamics and equilibrium states of infinite systems of
  lattice bosons, arXiv:2505.13170, Eq. (13).
-/

@[expose] public section

universe u

open Filter Topology HilbertPower
open scoped InnerProductSpace

noncomputable section

namespace Boson

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]

/-!

## A. The sequence of creation operators

-/

/-- The creation operators of an orthonormal sequence. -/
def creSeq (φ : ℕ → h) (n : ℕ) : ℕ → sym h n →L[ℂ] sym h (n + 1) := fun j => cre (φ j) n

lemma norm_creSeq_le {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (n : ℕ) (j : ℕ) :
    ‖creSeq φ n j‖ ≤ Real.sqrt (n + 1) := by
  simpa [creSeq, hφ.norm_eq_one j] using norm_cre_le (φ j) n

lemma tendsto_creSeq_inner {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (n : ℕ) (x z : sym h n) :
    Tendsto (fun j => ⟪creSeq φ n j x, creSeq φ n j z⟫_ℂ) atTop (𝓝 ⟪x, z⟫_ℂ) :=
  tendsto_inner_cre hφ n x z

/-- The generator with no free factors is the compact operator itself. -/
lemma gen_zero {m : ℕ} (K : sym h m →L[ℂ] sym h m) : gen K 0 = K := by
  ext ψ
  have h1 : (sym h m).orthogonalProjectionOnto ((ψ : TPow h m)) = ψ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ψ
  have h2 : ((gen K 0 ψ : sym h m) : TPow h m) = symProj h m (embed K ψ) := by
    rw [coe_gen]; rfl
  rw [h2]
  simp only [embed, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, h1]
  have := coe_proj_of_mem (K ψ).2
  rwa [coe_orthogonalProjectionOnto] at this

/-!

## B. Generators have intertwiners

-/

open AsymptoticIntertwiner

lemma intertwines_gen_succ {φ : ℕ → h} (hφ : Orthonormal ℂ φ) {m : ℕ} (K : sym h m →L[ℂ] sym h m)
    (hK : IsCompactOperator K) (k : ℕ) :
    Intertwines (creSeq φ (m + k)) (gen K (k + 1) : sym h (m + k + 1) →L[ℂ] sym h (m + k + 1))
      (((k + 1 : ℂ) / (m + k + 1 : ℂ)) • gen K k) := fun ψ => by
  have := tendsto_gen_cre K hK hφ k ψ
  simpa [creSeq, map_smul] using this

lemma intertwines_compact {φ : ℕ → h} (hφ : Orthonormal ℂ φ) {n : ℕ}
    (K : sym h (n + 1) →L[ℂ] sym h (n + 1)) (hK : IsCompactOperator K) :
    Intertwines (creSeq φ n) K (0 : sym h n →L[ℂ] sym h n) := fun ψ => by
  have := tendsto_apply_cre_of_compact K hK hφ ψ
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [creSeq] using this

/-- **Every generator has an intertwiner in the smaller sector algebra.** -/
lemma genSet_partner {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (n : ℕ) {A : sym h (n + 1) →L[ℂ] sym h (n + 1)}
    (hA : A ∈ genSet h (n + 1)) :
    ∃ B ∈ sectorAlgebra h n, Intertwines (creSeq φ n) A B := by
  obtain ⟨m, k, e, K, hK, hK', rfl⟩ := hA
  rcases k with _ | k
  · obtain rfl : m = n + 1 := e
    refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    change Intertwines (creSeq φ n) (gen K 0) 0
    rw [gen_zero]; exact intertwines_compact hφ K hK
  · obtain rfl : n = m + k := (Nat.succ.inj e).symm
    refine ⟨((k + 1 : ℂ) / (m + k + 1 : ℂ)) • gen K k, Subalgebra.smul_mem _
      (gen_mem_sectorAlgebra h hK hK') _, ?_⟩
    exact intertwines_gen_succ hφ K hK k

lemma star_mem_genSet {n : ℕ} {A : sym h n →L[ℂ] sym h n} (hA : A ∈ genSet h n) :
    star A ∈ genSet h n := by
  obtain ⟨m, k, e, K, hK, hK', rfl⟩ := hA
  refine ⟨m, k, e, ContinuousLinearMap.adjoint K, hK', ?_, ?_⟩
  · rwa [ContinuousLinearMap.adjoint_adjoint]
  · subst e
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_gen]

/-- Every generator lies in the domain of the intertwiner homomorphism. -/
lemma genSet_subset_domain {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (n : ℕ) :
    genSet h (n + 1) ⊆ domain (creSeq φ n) := fun A hA =>
  ⟨(genSet_partner hφ n hA).imp fun _ h => h.2, (genSet_partner hφ n (star_mem_genSet hA)).imp
    fun _ h => h.2⟩

/-!

## C. The connecting homomorphism

-/

section Kappa

variable {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (n : ℕ)

/-- The algebra of `(n+1)`-particle operators with intertwiners along `a†(φ_j)`. -/
abbrev intertwinerAlgebra : StarSubalgebra ℂ (sym h (n + 1) →L[ℂ] sym h (n + 1)) :=
  AsymptoticIntertwiner.algebra (V := creSeq φ n) (norm_creSeq_le hφ n)
    (tendsto_creSeq_inner hφ n)

lemma sectorAlgebra_le_intertwinerAlgebra :
    sectorAlgebra h (n + 1) ≤ intertwinerAlgebra hφ n :=
  StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le (genSet_subset_domain hφ n))
    (AsymptoticIntertwiner.isClosed_algebra _ _)

/-- **The connecting homomorphism** `κ : 𝔎_{n+1} → B(Sym^n)`. -/
def kappaHom : sectorAlgebra h (n + 1) →⋆ₐ[ℂ] (sym h n →L[ℂ] sym h n) :=
  (AsymptoticIntertwiner.hom (V := creSeq φ n) (norm_creSeq_le hφ n) (tendsto_creSeq_inner hφ n)).comp
    (StarSubalgebra.inclusion (sectorAlgebra_le_intertwinerAlgebra hφ n))

lemma kappaHom_spec (X : sectorAlgebra h (n + 1)) :
    Intertwines (creSeq φ n) (X : sym h (n + 1) →L[ℂ] sym h (n + 1)) (kappaHom hφ n X) :=
  AsymptoticIntertwiner.hom_spec (V := creSeq φ n) (norm_creSeq_le hφ n)
    (tendsto_creSeq_inner hφ n) ⟨X, sectorAlgebra_le_intertwinerAlgebra hφ n X.2⟩

lemma kappaHom_contractive (X : sectorAlgebra h (n + 1)) : ‖kappaHom hφ n X‖ ≤ ‖X‖ :=
  (kappaHom_spec hφ n X).norm_le (norm_creSeq_le hφ n) (tendsto_creSeq_inner hφ n)

/-- On generators the connecting homomorphism is the explicit intertwiner. -/
lemma kappaHom_gen {A : sym h (n + 1) →L[ℂ] sym h (n + 1)} (hA : A ∈ genSet h (n + 1))
    {B : sym h n →L[ℂ] sym h n} (hB : Intertwines (creSeq φ n) A B) :
    kappaHom hφ n ⟨A, StarSubalgebra.le_topologicalClosure _
      (StarAlgebra.subset_adjoin ℂ _ hA)⟩ = B :=
  Intertwines.unique (norm_creSeq_le hφ n) (tendsto_creSeq_inner hφ n)
    (kappaHom_spec hφ n ⟨A, StarSubalgebra.le_topologicalClosure _
      (StarAlgebra.subset_adjoin ℂ _ hA)⟩) hB

/-- **The connecting homomorphism maps into the smaller sector algebra.** -/
lemma kappaHom_mem (X : sectorAlgebra h (n + 1)) : kappaHom hφ n X ∈ sectorAlgebra h n := by
  set D := intertwinerAlgebra hφ n with hD
  let κ := AsymptoticIntertwiner.hom (V := creSeq φ n) (norm_creSeq_le hφ n)
    (tendsto_creSeq_inner hφ n)
  have hκc : Continuous κ := by
    refine AddMonoidHomClass.continuous_of_bound κ 1 fun A => ?_
    simpa using AsymptoticIntertwiner.norm_hom_le (norm_creSeq_le hφ n) (tendsto_creSeq_inner hφ n) A
  let T : StarSubalgebra ℂ D := (sectorAlgebra h n).comap κ
  have hT : IsClosed (T : Set D) := (isClosed_sectorAlgebra h n).preimage hκc
  have hDc : IsClosed (D : Set (sym h (n + 1) →L[ℂ] sym h (n + 1))) :=
    AsymptoticIntertwiner.isClosed_algebra _ _
  have hTm : IsClosed ((T.map D.subtype : StarSubalgebra ℂ _) :
      Set (sym h (n + 1) →L[ℂ] sym h (n + 1))) := by
    have : ((T.map D.subtype : StarSubalgebra ℂ _) : Set (sym h (n + 1) →L[ℂ] sym h (n + 1))) =
        Subtype.val '' (T : Set D) := by
      ext x; simp [StarSubalgebra.coe_map]
    rw [this]
    have hemb : Topology.IsClosedEmbedding
        (Subtype.val : D → (sym h (n + 1) →L[ℂ] sym h (n + 1))) :=
      Topology.IsClosedEmbedding.subtypeVal hDc
    exact hemb.isClosedMap _ hT
  have hgen : genSet h (n + 1) ⊆ (T.map D.subtype : Set _) := by
    intro A hA
    obtain ⟨B, hBs, hB⟩ := genSet_partner hφ n hA
    have hAD : A ∈ D := genSet_subset_domain hφ n hA
    refine ⟨⟨A, hAD⟩, ?_, rfl⟩
    show κ ⟨A, hAD⟩ ∈ sectorAlgebra h n
    have := kappaHom_gen hφ n hA hB
    have e : κ ⟨A, hAD⟩ = B := Intertwines.unique (norm_creSeq_le hφ n) (tendsto_creSeq_inner hφ n)
      (AsymptoticIntertwiner.hom_spec (V := creSeq φ n) (norm_creSeq_le hφ n)
        (tendsto_creSeq_inner hφ n) ⟨A, hAD⟩) hB
    rw [e]; exact hBs
  have hle : sectorAlgebra h (n + 1) ≤ T.map D.subtype :=
    StarSubalgebra.topologicalClosure_minimal (StarAlgebra.adjoin_le hgen) hTm
  obtain ⟨Y, hY, hYX⟩ := hle X.2
  have hY' : Y = ⟨X, sectorAlgebra_le_intertwinerAlgebra hφ n X.2⟩ := Subtype.ext hYX
  show κ ⟨X, sectorAlgebra_le_intertwinerAlgebra hφ n X.2⟩ ∈ sectorAlgebra h n
  rw [← hY']; exact hY

/-- **The connecting homomorphism between the sector algebras**, `κ_{n+1} : 𝔎_{n+1} → 𝔎_n`. -/
def kappa : sectorAlgebra h (n + 1) →⋆ₐ[ℂ] sectorAlgebra h n where
  toFun X := ⟨kappaHom hφ n X, kappaHom_mem hφ n X⟩
  map_one' := Subtype.ext (map_one (kappaHom hφ n))
  map_mul' X Y := Subtype.ext (map_mul (kappaHom hφ n) X Y)
  map_zero' := Subtype.ext (map_zero (kappaHom hφ n))
  map_add' X Y := Subtype.ext (map_add (kappaHom hφ n) X Y)
  commutes' r := Subtype.ext ((kappaHom hφ n).commutes r)
  map_star' X := Subtype.ext (map_star (kappaHom hφ n) X)

@[simp] lemma kappa_coe (X : sectorAlgebra h (n + 1)) :
    ((kappa hφ n X : sectorAlgebra h n) : sym h n →L[ℂ] sym h n) = kappaHom hφ n X := rfl

end Kappa

end Boson
