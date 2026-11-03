/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.AtomPhotonNet
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FockNet
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.SpinBoson
/-!

# The Fock-type representation of the atom-photon net

The local net of the atom-photon lattice acts on `ℓ²(Occ L × Finset L)`.

## i. Overview

A basis vector of the algebraic atom-photon space records the photon occupations and the finite set
of excited atoms. Along a finite region `X` it splits into the photon number and the atom state at
each cavity of `X` and the data outside `X`. This identifies `ℓ²(Occ L × Finset L)` with the tensor
product of `ℓ²((ℕ × Bool)^X)` and the outside space. An observable of `X` acts as `T ⊗ 1`. The
representation is compatible with the inclusions of `atomPhotonNet`. Hence it is a representation of
the algebraic inductive limit. No particle-number sector enters.

## ii. Key results

- `InfiniteBosons.sbSplit`: the splitting of atom-photon basis vectors along a region.
- `InfiniteBosons.sbFockRep`: the representation of the observables of a region.
- `InfiniteBosons.sbFockRep_incl`: compatibility with the net inclusions.

## iii. Table of contents

- A. Splitting
- B. The representation

## iv. References

* B. W. Shore, P. L. Knight, The Jaynes-Cummings model, J. Mod. Opt. 40 (1993) 1195.
-/

@[expose] public section

open Finsupp

noncomputable section
namespace InfiniteBosons
open CondensedMatter.QuasiLocal

variable {L : Type*} [DecidableEq L]

/-- Atom-photon states supported outside the region `X`. -/
abbrev SBOut (X : Finset L) : Type _ :=
  {b : SBBasis L // ∀ x ∈ X, b.1 x = 0 ∧ x ∉ b.2}

/-- The excited atoms of a configuration of the region `X`. -/
def inAtoms (X : Finset L) (c : Cfg (fun _ : L => ℕ × Bool) X) : Finset L :=
  X.filter fun l => (if h : l ∈ X then (c ⟨l, h⟩).2 else false) = true

/-- The state of the region `X` as an atom-photon basis vector. -/
def inState (X : Finset L) (c : Cfg (fun _ : L => ℕ × Bool) X) : SBBasis L :=
  (inOcc X (fun x => (c x).1), inAtoms X c)

/-- Atom-photon basis vectors split into the state of the region `X` and the state outside. -/
def sbSplit (X : Finset L) : SBBasis L ≃ Cfg (fun _ : L => ℕ × Bool) X × SBOut X where
  toFun b := (fun x => (b.1 x.1, decide (x.1 ∈ b.2)),
    ⟨(Finsupp.filter (fun l => l ∉ X) b.1, b.2.filter (fun l => l ∉ X)), fun x hx => by
      simp [hx]⟩)
  invFun p := ((inState X p.1).1 + p.2.1.1, inAtoms X p.1 ∪ p.2.1.2)
  left_inv b := by
    refine Prod.ext ?_ ?_
    · ext l
      by_cases h : l ∈ X <;> simp [inState, inOcc_apply, h]
    · ext l
      by_cases h : l ∈ X <;> simp [inAtoms, h]
  right_inv p := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · funext x
      have h1 := (p.2.2 x.1 x.2).1
      have h2 := (p.2.2 x.1 x.2).2
      simp [inState, inOcc_apply, inAtoms, x.2, h1, h2]
    · refine Prod.ext ?_ ?_
      · ext l
        by_cases h : l ∈ X
        · simp [inState, inOcc_apply, h, (p.2.2 l h).1]
        · simp [inState, inOcc_apply, h]
      · ext l
        by_cases h : l ∈ X
        · simp [inAtoms, h, (p.2.2 l h).2]
        · simp [inAtoms, h]


lemma sbSplit_symm_fst (X : Finset L) (c : Cfg (fun _ : L => ℕ × Bool) X) (o : SBOut X) (l : L) :
    ((sbSplit X).symm (c, o)).1 l = (if h : l ∈ X then (c ⟨l, h⟩).1 else 0) + o.1.1 l := by
  simp [sbSplit, inState, inOcc_apply]

lemma sbSplit_symm_snd (X : Finset L) (c : Cfg (fun _ : L => ℕ × Bool) X) (o : SBOut X) (l : L) :
    l ∈ ((sbSplit X).symm (c, o)).2 ↔ (l ∈ X ∧ ∃ h : l ∈ X, (c ⟨l, h⟩).2 = true) ∨ l ∈ o.1.2 := by
  simp [sbSplit, inAtoms]

/-- The Fock-type representation of the atom-photon net on `ℓ²(SBBasis L)`. -/
def sbFockRep (X : Finset L) : (HilbertSp (Cfg (fun _ : L => ℕ × Bool) X) →L[ℂ]
    HilbertSp (Cfg (fun _ : L => ℕ × Bool) X)) →⋆ₐ[ℂ]
    (HilbertSp (SBBasis L) →L[ℂ] HilbertSp (SBBasis L)) :=
  inclE (sbSplit X)

/-- **The atom-photon representation is compatible with the net inclusions.** -/
lemma sbFockRep_incl {X Y : Finset L} (h : X ≤ Y)
    (T : HilbertSp (Cfg (fun _ : L => ℕ × Bool) X) →L[ℂ]
      HilbertSp (Cfg (fun _ : L => ℕ × Bool) X)) :
    sbFockRep Y ((atomPhotonNet L).incl h T) = sbFockRep X T := by
  symm
  refine inclE_comp (splitEquiv h) (sbSplit Y) (sbSplit X) (fun d => rfl) (fun d a => ?_) T
  refine Prod.ext ?_ ?_
  · ext l
    rw [sbSplit_symm_fst, sbSplit_symm_fst]
    by_cases hY : l ∈ Y
    · by_cases hX : l ∈ X
      · have : ((sbSplit Y) d).2.1.1 l = 0 := (((sbSplit Y) d).2.2 l hY).1
        simp [splitEquiv, sbSplit, hX, hY, this]
      · simp [splitEquiv, sbSplit, hX, hY]
    · have hX : l ∉ X := fun hx => hY (h hx)
      simp [splitEquiv, sbSplit, hX, hY]
  · ext l
    rw [sbSplit_symm_snd, sbSplit_symm_snd]
    by_cases hY : l ∈ Y
    · by_cases hX : l ∈ X
      · have : l ∉ ((sbSplit Y) d).2.1.2 := (((sbSplit Y) d).2.2 l hY).2
        simp [splitEquiv, sbSplit, hX, hY, this]
      · simp [splitEquiv, sbSplit, hX, hY]
    · have hX : l ∉ X := fun hx => hY (h hx)
      simp [splitEquiv, sbSplit, hX, hY]

end InfiniteBosons
