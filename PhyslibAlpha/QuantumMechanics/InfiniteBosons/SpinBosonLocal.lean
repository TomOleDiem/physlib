/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.SpinBoson
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.LocalAlgebra
/-!

# Locality of the atom-photon lattice

Photon and atom operators at different sites commute, so the atom-photon algebra is a local algebra.

## i. Overview

The photon operators `a_x`, `a_x†` obey the canonical commutation relations. The atom operators
`σ_x^±` at different sites commute. Photon and atom operators always commute. Hence the four
operators at a site form a star-closed family of local generators in the sense of
`LocalGenerators`. This gives the finite support of polynomials, locality, and the Heisenberg
derivation of any locally finite polynomial interaction of photons and atoms, with no particle
number sector.

## ii. Key results

- `InfiniteBosons.sbGenerators`: the local generators of the atom-photon lattice.
- `InfiniteBosons.annS_annS_comm`, `InfiniteBosons.lowS_raiseS_comm_ne` and further commutation
  relations of the operators.

## iii. Table of contents

- A. Photons at a fixed set of excited atoms
- B. Commutation relations
- C. The local generators

## iv. References

* E. T. Jaynes and F. W. Cummings, Proc. IEEE 51, 89 (1963).
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- The photon space embedded at a fixed set of excited atoms. -/
def embedS (s : Finset L) : FockPre L →ₗ[ℂ] SBPre L :=
  Finsupp.lmapDomain ℂ ℂ (fun α => (α, s))

lemma embedS_single (s : Finset L) (α : Occ L) (c : ℂ) :
    embedS s (single α c) = single (α, s) c := by
  simp [embedS, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

lemma annS_comp_embedS (x : L) (s : Finset L) : annS x ∘ₗ embedS s = embedS s ∘ₗ ann x := by
  refine linearMap_ext_basis fun α => ?_
  simp only [LinearMap.comp_apply]
  rw [embedS_single, annS_single, ann_single, embedS_single]

lemma creS_comp_embedS (x : L) (s : Finset L) : creS x ∘ₗ embedS s = embedS s ∘ₗ cre x := by
  refine linearMap_ext_basis fun α => ?_
  simp only [LinearMap.comp_apply]
  rw [embedS_single, creS_single, cre_single, embedS_single]

lemma annS_apply_embedS (x : L) (s : Finset L) (f : FockPre L) :
    annS x (embedS s f) = embedS s (ann x f) := congrArg (fun T => T f) (annS_comp_embedS x s)

lemma creS_apply_embedS (x : L) (s : Finset L) (f : FockPre L) :
    creS x (embedS s f) = embedS s (cre x f) := congrArg (fun T => T f) (creS_comp_embedS x s)

lemma single_eq_embedS (α : Occ L) (s : Finset L) :
    (single (α, s) 1 : SBPre L) = embedS s (single α 1) := (embedS_single s α 1).symm

lemma annS_annS_comm (x y : L) : annS x ∘ₗ annS y = annS y ∘ₗ annS x := by
  refine linearMap_ext_basis fun b => ?_
  obtain ⟨α, s⟩ := b
  simp only [LinearMap.comp_apply]
  rw [single_eq_embedS, annS_apply_embedS, annS_apply_embedS, annS_apply_embedS,
    annS_apply_embedS]
  have := congrArg (fun T => T (single α 1)) (ann_comm x y)
  simpa using congrArg (embedS s) this

lemma creS_creS_comm (x y : L) : creS x ∘ₗ creS y = creS y ∘ₗ creS x := by
  refine linearMap_ext_basis fun b => ?_
  obtain ⟨α, s⟩ := b
  simp only [LinearMap.comp_apply]
  rw [single_eq_embedS, creS_apply_embedS, creS_apply_embedS, creS_apply_embedS,
    creS_apply_embedS]
  have := congrArg (fun T => T (single α 1)) (cre_comm x y)
  simpa using congrArg (embedS s) this

lemma annS_creS_comm_ne {x y : L} (hxy : x ≠ y) : annS x ∘ₗ creS y = creS y ∘ₗ annS x := by
  refine linearMap_ext_basis fun b => ?_
  obtain ⟨α, s⟩ := b
  simp only [LinearMap.comp_apply]
  rw [single_eq_embedS, creS_apply_embedS, annS_apply_embedS, annS_apply_embedS,
    creS_apply_embedS]
  have := congrArg (fun T => T (single α 1)) (ann_cre_comm_ne hxy)
  simpa using congrArg (embedS s) this


lemma annS_lowS_comm (x y : L) : annS x ∘ₗ lowS y = lowS y ∘ₗ annS x := by
  refine linearMap_ext_basis fun b => ?_
  simp only [LinearMap.comp_apply]
  rw [lowS_single, annS_single, lowS_single]
  by_cases hy : y ∈ b.2 <;> simp [hy, annS_single]

lemma annS_raiseS_comm (x y : L) : annS x ∘ₗ raiseS y = raiseS y ∘ₗ annS x := by
  refine linearMap_ext_basis fun b => ?_
  simp only [LinearMap.comp_apply]
  rw [raiseS_single, annS_single, raiseS_single]
  by_cases hy : y ∈ b.2 <;> simp [hy, annS_single]

lemma creS_lowS_comm (x y : L) : creS x ∘ₗ lowS y = lowS y ∘ₗ creS x := by
  refine linearMap_ext_basis fun b => ?_
  simp only [LinearMap.comp_apply]
  rw [lowS_single, creS_single, lowS_single]
  by_cases hy : y ∈ b.2 <;> simp [hy, creS_single]

lemma creS_raiseS_comm (x y : L) : creS x ∘ₗ raiseS y = raiseS y ∘ₗ creS x := by
  refine linearMap_ext_basis fun b => ?_
  simp only [LinearMap.comp_apply]
  rw [raiseS_single, creS_single, raiseS_single]
  by_cases hy : y ∈ b.2 <;> simp [hy, creS_single]

lemma lowS_lowS_comm {x y : L} (hxy : x ≠ y) : lowS x ∘ₗ lowS y = lowS y ∘ₗ lowS x := by
  refine linearMap_ext_basis fun b => ?_
  simp only [LinearMap.comp_apply]
  rw [lowS_single, lowS_single]
  by_cases hy : y ∈ b.2 <;> by_cases hx : x ∈ b.2 <;>
    simp [hy, hx, lowS_single, Finset.erase_right_comm, hxy, Ne.symm hxy]

lemma raiseS_raiseS_comm {x y : L} (hxy : x ≠ y) :
    raiseS x ∘ₗ raiseS y = raiseS y ∘ₗ raiseS x := by
  refine linearMap_ext_basis fun b => ?_
  simp only [LinearMap.comp_apply]
  rw [raiseS_single, raiseS_single]
  by_cases hy : y ∈ b.2 <;> by_cases hx : x ∈ b.2 <;>
    simp [hy, hx, raiseS_single, Finset.insert_comm, hxy, Ne.symm hxy]

lemma lowS_raiseS_comm_ne {x y : L} (hxy : x ≠ y) :
    lowS x ∘ₗ raiseS y = raiseS y ∘ₗ lowS x := by
  refine linearMap_ext_basis fun b => ?_
  simp only [LinearMap.comp_apply]
  rw [raiseS_single, lowS_single]
  by_cases hy : y ∈ b.2 <;> by_cases hx : x ∈ b.2 <;>
    simp [hy, hx, raiseS_single, lowS_single, Finset.erase_insert_of_ne, hxy, Ne.symm hxy,
      Finset.mem_insert, Finset.mem_erase, Finset.insert_erase]


lemma opComm {a b : Adjointable (SBBasis L)} (h : a.1.1 ∘ₗ b.1.1 = b.1.1 ∘ₗ a.1.1) : Commute a b := by
  show a * b = b * a
  apply adjointable_ext
  exact h

/-- The local generators of the atom-photon lattice: photon and atom operators at a site. -/
def sbGenerators (L : Type*) [DecidableEq L] : LocalGenerators L (Adjointable (SBBasis L)) where
  gen x := {annOpS x, creOpS x, lowOpS x, raiseOpS x}
  star_mem x a ha := by
    rcases ha with rfl | rfl | rfl | rfl
    · simp [star_annOpS]
    · simp [star_creOpS]
    · simp [star_lowOpS]
    · simp [star_raiseOpS]
  commute x y hxy a ha b hb := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
    · exact opComm (annS_annS_comm x y)
    · exact opComm (annS_creS_comm_ne hxy)
    · exact opComm (annS_lowS_comm x y)
    · exact opComm (annS_raiseS_comm x y)
    · exact opComm (annS_creS_comm_ne (Ne.symm hxy)).symm
    · exact opComm (creS_creS_comm x y)
    · exact opComm (creS_lowS_comm x y)
    · exact opComm (creS_raiseS_comm x y)
    · exact opComm (annS_lowS_comm y x).symm
    · exact opComm (creS_lowS_comm y x).symm
    · exact opComm (lowS_lowS_comm hxy)
    · exact opComm (lowS_raiseS_comm_ne hxy)
    · exact opComm (annS_raiseS_comm y x).symm
    · exact opComm (creS_raiseS_comm y x).symm
    · exact opComm (lowS_raiseS_comm_ne (Ne.symm hxy)).symm
    · exact opComm (raiseS_raiseS_comm hxy)

end InfiniteBosons
