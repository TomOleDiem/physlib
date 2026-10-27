/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.EmbeddingSpaceGroup
public import Physlib.CondensedMatter.Crystal.Symmetry.Isometries
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Isometries of space and symmetries of a crystal

The affine isometries that preserve an embedded crystal are exactly the extensions of its
distance-preserving symmetries.

## i. Overview

The space group of an embedding consists of the affine isometries of space that map the positions
of the sites onto themselves. A distance-preserving symmetry of the abstract crystal permutes the
sites in the same way. The two descriptions agree.

If an affine isometry preserves the positions, it moves every site to a site. When the embedding
is primitive, its linear part maps the lattice vectors to lattice vectors, which gives an
automorphism of the translation group. If the vectors and the positions are distinct, these data
form a symmetry of the abstract crystal, and it preserves distances.

Conversely, let the embedding fill space and let a symmetry preserve distances. The inner products
of the lattice vectors are preserved, which gives a linear isometry of space. The label positions
are then moved by this isometry up to a common constant, and the resulting affine isometry
extends the symmetry.

## ii. Key results

- `Crystal.Embedding.exists_isometry` : every element of the space group is the action of a
  distance-preserving symmetry.
- `Crystal.Embedding.exists_mem_spaceGroup` : every distance-preserving symmetry is the
  restriction of an element of the space group.
- `Crystal.Embedding.mem_isometries_iff_exists` : a symmetry preserves distances exactly when it
  is the restriction of an element of the space group.
- `Crystal.exists_linearIsometryEquiv` : families of vectors with the same inner products differ
  by a linear isometry.

## iii. Table of contents

- A. A linear isometry from inner products
- B. From the space group to symmetries
- C. From symmetries to the space group

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

/-! ## A. A linear isometry from inner products -/

section LinearIsometry

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {u w : ι → E}

/-- Linear combinations of families with the same inner products have the same inner products. -/
lemma inner_linearCombination_eq (h : ∀ a b, inner ℝ (w a) (w b) = inner ℝ (u a) (u b))
    (c c' : ι →₀ ℝ) : inner ℝ (Finsupp.linearCombination ℝ w c) (Finsupp.linearCombination ℝ w c') =
      inner ℝ (Finsupp.linearCombination ℝ u c) (Finsupp.linearCombination ℝ u c') := by
  simp [Finsupp.linearCombination_apply, Finsupp.sum_inner, Finsupp.inner_sum,
    real_inner_smul_left, real_inner_smul_right, h]

/-- A linear combination of `w` vanishes when the same combination of `u` does. -/
lemma linearCombination_eq_zero (h : ∀ a b, inner ℝ (w a) (w b) = inner ℝ (u a) (u b))
    {c : ι →₀ ℝ} (hc : Finsupp.linearCombination ℝ u c = 0) :
    Finsupp.linearCombination ℝ w c = 0 := by
  have := inner_linearCombination_eq h c c
  rwa [hc, inner_zero_left, inner_self_eq_zero] at this

/-- The linear combinations of a spanning family reach every vector. -/
lemma linearCombination_surjective (hu : Submodule.span ℝ (Set.range u) = ⊤) :
    Function.Surjective (Finsupp.linearCombination ℝ u) := by
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
  exact hu

/-- A linear map carries the linear combinations of `u` to those of `w`. -/
lemma exists_linearMap_comp (hu : Submodule.span ℝ (Set.range u) = ⊤)
    (h : ∀ a b, inner ℝ (w a) (w b) = inner ℝ (u a) (u b)) :
    ∃ T : E →ₗ[ℝ] E,
      ∀ c, T (Finsupp.linearCombination ℝ u c) = Finsupp.linearCombination ℝ w c := by
  obtain ⟨s, hs⟩ := (Finsupp.linearCombination ℝ u).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (linearCombination_surjective hu))
  refine ⟨Finsupp.linearCombination ℝ w ∘ₗ s, fun c => ?_⟩
  have h0 : Finsupp.linearCombination ℝ u (s (Finsupp.linearCombination ℝ u c) - c) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact LinearMap.congr_fun hs _
  simpa [sub_eq_zero] using linearCombination_eq_zero h h0

/-- Two spanning families with the same inner products differ by a linear isometry. -/
lemma exists_linearIsometryEquiv [FiniteDimensional ℝ E]
    (hu : Submodule.span ℝ (Set.range u) = ⊤)
    (h : ∀ a b, inner ℝ (w a) (w b) = inner ℝ (u a) (u b)) :
    ∃ L : E ≃ₗᵢ[ℝ] E, ∀ a, L (u a) = w a := by
  obtain ⟨T, hT⟩ := exists_linearMap_comp hu h
  have hinner : ∀ x y, inner ℝ (T x) (T y) = inner ℝ x y := fun x y => by
    obtain ⟨c, rfl⟩ := linearCombination_surjective hu x
    obtain ⟨c', rfl⟩ := linearCombination_surjective hu y
    rw [hT, hT, inner_linearCombination_eq h]
  refine ⟨(T.isometryOfInner hinner).toLinearIsometryEquiv rfl, fun a => ?_⟩
  simpa using hT (Finsupp.single a 1)

end LinearIsometry

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] (R : Embedding C E)

/-! ## B. From the space group to symmetries -/

section NormedSpace

variable [NormedSpace ℝ E] {ψ : E ≃ᵃⁱ[ℝ] E}

/-- An element of the space group moves every position to a position. -/
lemma exists_site_position_eq (hψ : ψ ∈ R.spaceGroup) (x : C.Site) :
    ∃ y : C.Site, R.position y = ψ (R.position x) := by
  have : ψ (R.position x) ∈ ψ '' Set.range R.position := ⟨_, ⟨x, rfl⟩, rfl⟩
  rwa [show ψ '' Set.range R.position = Set.range R.position from hψ] at this

/-- The linear part of the inverse is the inverse of the linear part. -/
lemma linear_inv (ψ : E ≃ᵃⁱ[ℝ] E) : ψ⁻¹.linearIsometryEquiv = ψ.linearIsometryEquiv.symm :=
  map_inv linearHom ψ

/-- The linear part of an element of the space group is a lattice automorphism. -/
lemma exists_lattice_equiv (hv : Function.Injective R.vector) (hprim : R.IsPrimitive)
    (hψ : ψ ∈ R.spaceGroup) :
    ∃ A : G ≃+ G, ∀ a, R.vector (A a) = ψ.linearIsometryEquiv (R.vector a) := by
  choose A hA using R.exists_lattice_vector_eq_linear hprim hψ
  choose A' hA' using R.exists_lattice_vector_eq_linear hprim (inv_mem hψ)
  refine ⟨⟨⟨A, A', fun a => hv ?_, fun a => hv ?_⟩, fun a b => hv (by simp [hA])⟩, hA⟩
  · rw [hA', hA, linear_inv, LinearIsometryEquiv.symm_apply_apply]
  · rw [hA, hA', linear_inv, LinearIsometryEquiv.apply_symm_apply]

/-- An element of the space group permutes the sites, through the positions. -/
lemma exists_site_equiv (hp : Function.Injective R.position) (hψ : ψ ∈ R.spaceGroup) :
    ∃ e : C.Site ≃ C.Site, ∀ x, R.position (e x) = ψ (R.position x) := by
  choose f hf using R.exists_site_position_eq hψ
  choose f' hf' using R.exists_site_position_eq (inv_mem hψ)
  exact ⟨⟨f, f', fun x => hp (by rw [hf', hf]; exact ψ.symm_apply_apply _),
    fun x => hp (by rw [hf, hf']; exact ψ.apply_symm_apply _)⟩, hf⟩

/-- The permutation of the sites and the lattice automorphism of an element of the space group
are compatible with the translations. -/
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
  refine ⟨⟨A, ⟨e, R.site_equiv_vadd hp hA he⟩, e.bijective⟩, fun x y => ?_, he⟩
  show dist (R.position (e x)) (R.position (e y)) = _
  rw [he, he]
  exact ψ.dist_map _ _

end NormedSpace

/-! ## C. From symmetries to the space group -/

section InnerProduct

variable [InnerProductSpace ℝ E] {φ : Symmetry C} {L : E ≃ₗᵢ[ℝ] E}

/-- A linear isometry that agrees with a distance-preserving symmetry on the translation vectors
carries the inner products with the images of the translation vectors to those with the vectors,
on all of space. -/
lemma inner_linear_eq (hR : R.IsSpaceFilling) (hL : ∀ a, L (R.vector a) = R.vector (φ.lattice a))
    {P Q : E} (h : ∀ d, inner ℝ (R.vector (φ.lattice d)) P = inner ℝ (R.vector d) Q) (x : E) :
    inner ℝ (L x) P = inner ℝ x Q := by
  have := LinearMap.ext_on (f := (innerSL ℝ P).toLinearMap ∘ₗ L.toLinearMap)
    (g := (innerSL ℝ Q).toLinearMap) hR (by
      rintro _ ⟨d, rfl⟩
      simpa [real_inner_comm, hL] using h d)
  simpa [real_inner_comm] using congr($this x)

/-- A linear isometry that agrees with a distance-preserving symmetry on the translation vectors
carries the differences of the label positions to their images. -/
lemma position_sub_eq_linear (hR : R.IsSpaceFilling) (hφ : φ ∈ R.isometries)
    (hL : ∀ a, L (R.vector a) = R.vector (φ.lattice a)) (i j : C.UnitCell) :
    R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩) = L (R.basis i - R.basis j) := by
  set z := R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩) - L (R.basis i - R.basis j)
  have h0 := R.inner_linear_eq hR hL (R.inner_lattice_position hφ i j) (L.symm z)
  have h1 := L.inner_map_map (L.symm z) (R.basis i - R.basis j)
  rw [L.apply_symm_apply] at h0 h1
  rw [← sub_eq_zero]
  refine (inner_self_eq_zero (𝕜 := ℝ)).1 ?_
  rw [inner_sub_right z, h0, h1, sub_self]

/-- The label positions of a distance-preserving symmetry are the images under a linear isometry,
up to a common constant. -/
lemma exists_position_const (hR : R.IsSpaceFilling) (hφ : φ ∈ R.isometries)
    (hL : ∀ a, L (R.vector a) = R.vector (φ.lattice a)) :
    ∃ t : E, ∀ i, R.position (φ ⟨0, i⟩) = L (R.basis i) + t := by
  refine ⟨R.position (φ ⟨0, Classical.arbitrary _⟩) - L (R.basis (Classical.arbitrary _)),
    fun i => ?_⟩
  have := R.position_sub_eq_linear hR hφ hL i (Classical.arbitrary _)
  rw [map_sub, sub_eq_iff_eq_add] at this
  rw [this]
  abel

/-- A linear isometry and a constant carry the label positions of a distance-preserving symmetry
to their images. -/
lemma exists_linear_position (hR : R.IsSpaceFilling) (hφ : φ ∈ R.isometries) :
    ∃ (L : E ≃ₗᵢ[ℝ] E) (t : E), (∀ a, L (R.vector a) = R.vector (φ.lattice a)) ∧
      ∀ i, R.position (φ ⟨0, i⟩) = L (R.basis i) + t := by
  have := hR.finiteDimensional
  obtain ⟨L, hL⟩ := exists_linearIsometryEquiv (u := R.vector)
    (w := fun d => R.vector (φ.lattice d)) hR
    (R.inner_vector_lattice_of_norm (R.norm_vector_lattice hφ))
  exact ⟨L, (R.exists_position_const hR hφ hL).choose, hL,
    (R.exists_position_const hR hφ hL).choose_spec⟩

/-- An isometric symmetry of a space-filling embedding is the restriction of an affine isometry of
space. -/
lemma exists_affineIsometryEquiv (hR : R.IsSpaceFilling) (hφ : φ ∈ R.isometries) :
    ∃ ψ : E ≃ᵃⁱ[ℝ] E, ∀ x, ψ (R.position x) = R.position (φ x) := by
  obtain ⟨L, t, hL, ht⟩ := R.exists_linear_position hR hφ
  refine ⟨L.toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ E t), fun x => ?_⟩
  show t + L (R.position x) = R.position (φ x)
  rw [R.position_apply (φ := φ) x, ht x.label, show R.position x = R.vector x.cell + R.basis x.label
    from rfl, map_add, hL]
  abel

/-- An isometric symmetry of a space-filling embedding is the restriction of an element of the
space group. -/
lemma exists_mem_spaceGroup (hR : R.IsSpaceFilling) (hφ : φ ∈ R.isometries) :
    ∃ ψ ∈ R.spaceGroup, ∀ x, ψ (R.position x) = R.position (φ x) := by
  obtain ⟨ψ, h⟩ := R.exists_affineIsometryEquiv hR hφ
  refine ⟨ψ, ?_, h⟩
  show ψ '' Set.range R.position = Set.range R.position
  rw [← Set.range_comp, show ψ ∘ R.position = R.position ∘ φ from funext h, Set.range_comp,
    show Set.range ⇑φ = Set.univ from φ.bijective.surjective.range_eq, Set.image_univ]

/-- **A symmetry preserves distances exactly when it is the restriction of an element of the space
group.** -/
lemma mem_isometries_iff_exists (hR : R.IsSpaceFilling) :
    φ ∈ R.isometries ↔ ∃ ψ ∈ R.spaceGroup, ∀ x, ψ (R.position x) = R.position (φ x) :=
  ⟨R.exists_mem_spaceGroup hR, fun ⟨ψ, _, h⟩ x y => by
    rw [← h x, ← h y]
    exact ψ.dist_map _ _⟩

end InnerProduct

end Embedding

end Physlib.CondensedMatter.Crystal
