/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.EmbeddingSpaceGroup
public import Physlib.CondensedMatter.Crystal.Symmetry.Isometries

/-!
# Elements of the space group as symmetries

An affine isometry that preserves the positions of an embedded crystal is the action of a
distance-preserving symmetry of the crystal.

## i. Overview

A rigid motion of space that carries every atom of a crystal onto an atom also acts on the crystal
itself. It sends each atom to another atom, so it shuffles the atoms among themselves, and it
moves each lattice vector to another lattice vector. Since it keeps all distances, this
relabelling of the atoms is a symmetry of the abstract crystal that keeps all distances.

For a square lattice, a quarter turn about an atom sends the atom at `(m, n)` to the atom at
`(-n, m)`. The lattice vector `(1, 0)` goes to `(0, 1)`. To make this precise the placement has to
be faithful: different lattice steps give different vectors, different atoms sit at different
points, and the shifts that carry atoms onto atoms are exactly the lattice steps.

## ii. Key results

- `Crystal.Embedding.exists_lattice_equiv` : the linear part of an element of the space group
  is a lattice automorphism.
- `Crystal.Embedding.exists_site_equiv` : an element of the space group permutes the sites.
- `Crystal.Embedding.exists_isometry` : every element of the space group is the action of a
  distance-preserving symmetry.

## iii. Table of contents

- A. The lattice automorphism and the permutation of the sites
- B. The symmetry

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

open Euclidean

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (R : Embedding C E) {ψ : E ≃ᵃⁱ[ℝ] E}

/-! ## A. The lattice automorphism and the permutation of the sites -/

/-- The linear part of an element of the space group is an additive map of the lattice. -/
lemma exists_lattice_hom (hv : Function.Injective R.vector) (hprim : R.IsPrimitive)
    (hψ : ψ ∈ R.spaceGroup) :
    ∃ A : G →+ G, ∀ a, R.vector (A a) = ψ.linearIsometryEquiv (R.vector a) := by
  choose A hA using R.exists_lattice_vector_eq_linear hprim hψ
  refine ⟨AddMonoidHom.mk' A ?_, hA⟩
  intro a b
  apply hv
  simp [hA]

/-- The linear part of an element of the space group is a lattice automorphism. -/
lemma exists_lattice_equiv (hv : Function.Injective R.vector) (hprim : R.IsPrimitive)
    (hψ : ψ ∈ R.spaceGroup) :
    ∃ A : G ≃+ G, ∀ a, R.vector (A a) = ψ.linearIsometryEquiv (R.vector a) := by
  obtain ⟨A, hA⟩ := R.exists_lattice_hom hv hprim hψ
  obtain ⟨A', hA'⟩ := R.exists_lattice_hom hv hprim (inv_mem hψ)
  refine ⟨AddMonoidHom.toAddEquiv A A' ?_ ?_, hA⟩
  · ext a
    apply hv
    rw [AddMonoidHom.comp_apply, hA', hA, linearIsometryEquiv_inv]
    exact LinearIsometryEquiv.symm_apply_apply _ _
  · ext a
    apply hv
    rw [AddMonoidHom.comp_apply, hA, hA', linearIsometryEquiv_inv]
    exact LinearIsometryEquiv.apply_symm_apply _ _

/-- An element of the space group moves every position to a position. -/
lemma exists_site_position_eq (hψ : ψ ∈ R.spaceGroup) (x : C.Site) :
    ∃ y : C.Site, R.position y = ψ (R.position x) := by
  have := Set.mem_image_of_mem ψ (Set.mem_range_self (f := R.position) x)
  rw [R.mem_spaceGroup_iff.1 hψ] at this
  exact this

/-- Maps of sites that realise two mutually inverse affine isometries are mutually inverse. -/
lemma left_inv_of_position (hp : Function.Injective R.position) {f f' : C.Site → C.Site}
    {ψ' ψ'' : E ≃ᵃⁱ[ℝ] E} (hf : ∀ x, R.position (f x) = ψ' (R.position x))
    (hf' : ∀ x, R.position (f' x) = ψ'' (R.position x)) (h : ∀ y, ψ'' (ψ' y) = y) (x : C.Site) :
    f' (f x) = x := by
  apply hp
  rw [hf', hf, h]

/-- An element of the space group permutes the sites, through the positions. -/
lemma exists_site_equiv (hp : Function.Injective R.position) (hψ : ψ ∈ R.spaceGroup) :
    ∃ e : C.Site ≃ C.Site, ∀ x, R.position (e x) = ψ (R.position x) := by
  choose f hf using R.exists_site_position_eq hψ
  choose f' hf' using R.exists_site_position_eq (inv_mem hψ)
  refine ⟨⟨f, f', ?_, ?_⟩, hf⟩
  · intro x
    exact R.left_inv_of_position hp hf hf' ψ.symm_apply_apply x
  · intro x
    exact R.left_inv_of_position hp hf' hf ψ.apply_symm_apply x

/-! ## B. The symmetry -/

/-- The permutation of the sites and the lattice automorphism of an element of the space group
intertwine the translations. -/
lemma site_equiv_vadd (hp : Function.Injective R.position) {A : G ≃+ G} {e : C.Site ≃ C.Site}
    (hA : ∀ a, R.vector (A a) = ψ.linearIsometryEquiv (R.vector a))
    (he : ∀ x, R.position (e x) = ψ (R.position x)) (a : G) (x : C.Site) :
    e (a +ᵥ x) = A a +ᵥ e x := by
  apply hp
  rw [he, R.position_vadd, R.position_vadd, hA, he]
  simpa only [vadd_eq_add] using ψ.map_vadd (R.position x) (R.vector a)

/-- **Every element of the space group is the action of a distance-preserving symmetry**, when the
vectors and the positions are injective and the embedding is primitive. -/
lemma exists_isometry (hv : Function.Injective R.vector) (hp : Function.Injective R.position)
    (hprim : R.IsPrimitive) (hψ : ψ ∈ R.spaceGroup) :
    ∃ φ : Symmetry C, φ ∈ R.isometries ∧ ∀ x, R.position (φ x) = ψ (R.position x) := by
  obtain ⟨A, hA⟩ := R.exists_lattice_equiv hv hprim hψ
  obtain ⟨e, he⟩ := R.exists_site_equiv hp hψ
  refine ⟨⟨A, ⟨e, R.site_equiv_vadd hp hA he⟩, e.bijective⟩, ?_, he⟩
  intro x y
  show dist (R.position (e x)) (R.position (e y)) = _
  rw [he, he]
  exact ψ.dist_map _ _

end Embedding

end Physlib.CondensedMatter.Crystal
