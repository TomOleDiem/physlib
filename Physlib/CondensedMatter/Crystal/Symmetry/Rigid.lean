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

/-- Two families that span the space and have the same inner products differ by a linear isometry
of the space. -/
lemma exists_linearIsometryEquiv {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {u w : ι → E} (hu : Submodule.span ℝ (Set.range u) = ⊤)
    (h : ∀ a b, inner ℝ (w a) (w b) = inner ℝ (u a) (u b)) :
    ∃ L : E ≃ₗᵢ[ℝ] E, ∀ a, L (u a) = w a := by
  classical
  let Φu := Finsupp.linearCombination ℝ u
  let Φw := Finsupp.linearCombination ℝ w
  have hΦ : ∀ c c', inner ℝ (Φw c) (Φw c') = inner ℝ (Φu c) (Φu c') := by
    intro c c'
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp [map_add, inner_add_left, hf, hg]
    | single a r =>
      induction c' using Finsupp.induction_linear with
      | zero => simp
      | add f g hf hg => simp [map_add, inner_add_right, hf, hg]
      | single b t => simp [Φu, Φw, real_inner_smul_left, real_inner_smul_right, h]
  have hsurj : Function.Surjective Φu := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hu
  obtain ⟨s, hs⟩ := Φu.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  have hker : ∀ c, Φu c = 0 → Φw c = 0 := fun c hc => by
    have := hΦ c c
    rwa [hc, inner_zero_left, inner_self_eq_zero] at this
  have hL : ∀ c, (Φw ∘ₗ s) (Φu c) = Φw c := fun c => by
    have h0 : Φu (s (Φu c) - c) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact LinearMap.congr_fun hs (Φu c)
    simpa [sub_eq_zero] using hker _ h0
  have hinner : ∀ x y, inner ℝ ((Φw ∘ₗ s) x) ((Φw ∘ₗ s) y) = inner ℝ x y := by
    intro x y
    obtain ⟨c, rfl⟩ := hsurj x
    obtain ⟨c', rfl⟩ := hsurj y
    rw [hL, hL, hΦ]
  refine ⟨((Φw ∘ₗ s).isometryOfInner hinner).toLinearIsometryEquiv rfl, fun a => ?_⟩
  have := hL (Finsupp.single a 1)
  simp only [Φu, Φw, Finsupp.linearCombination_single, one_smul] at this
  simpa using this

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] (R : Embedding C E)

/-! ## B. From the space group to symmetries -/

section NormedSpace

variable [NormedSpace ℝ E] {ψ : E ≃ᵃⁱ[ℝ] E}

/-- Conjugating a translation by an affine isometry translates by the linear part of the vector. -/
lemma mul_translationHom_mul_inv (ψ : E ≃ᵃⁱ[ℝ] E) (v : E) :
    ψ * translationHom (Multiplicative.ofAdd v) * ψ⁻¹ =
      translationHom (Multiplicative.ofAdd (ψ.linearIsometryEquiv v)) := by
  ext x
  show ψ (v + ψ.symm x) = ψ.linearIsometryEquiv v + x
  simpa using ψ.map_vadd (ψ.symm x) v

/-- The linear part of an element of the space group of a primitive embedding maps lattice vectors
to lattice vectors. -/
lemma exists_lattice_vector_eq_linear (hprim : R.IsPrimitive) (hψ : ψ ∈ R.spaceGroup) (a : G) :
    ∃ b : G, R.vector b = ψ.linearIsometryEquiv (R.vector a) := by
  refine (hprim _).1 ?_
  rw [← mul_translationHom_mul_inv]
  exact mul_mem (mul_mem hψ ((hprim _).2 ⟨a, rfl⟩)) (inv_mem hψ)

/-- An element of the space group moves every position to a position. -/
lemma exists_site_position_eq (hψ : ψ ∈ R.spaceGroup) (x : C.Site) :
    ∃ y : C.Site, R.position y = ψ (R.position x) := by
  have : ψ (R.position x) ∈ ψ '' Set.range R.position := ⟨_, ⟨x, rfl⟩, rfl⟩
  rwa [show ψ '' Set.range R.position = Set.range R.position from hψ] at this

/-- The linear part of the inverse is the inverse of the linear part. -/
lemma linear_inv (ψ : E ≃ᵃⁱ[ℝ] E) : ψ⁻¹.linearIsometryEquiv = ψ.linearIsometryEquiv.symm :=
  map_inv linearHom ψ

/-- **Every element of the space group is the action of a distance-preserving symmetry**, when the
vectors and the positions are injective and the embedding is primitive. -/
lemma exists_isometry (hv : Function.Injective R.vector) (hp : Function.Injective R.position)
    (hprim : R.IsPrimitive) (hψ : ψ ∈ R.spaceGroup) :
    ∃ φ : Symmetry C, φ ∈ R.isometries ∧ ∀ x, R.position (φ x) = ψ (R.position x) := by
  choose f hf using R.exists_site_position_eq hψ
  choose A hA using R.exists_lattice_vector_eq_linear hprim hψ
  choose f' hf' using R.exists_site_position_eq (inv_mem hψ)
  choose A' hA' using R.exists_lattice_vector_eq_linear hprim (inv_mem hψ)
  have hleft : ∀ x, f' (f x) = x := fun x => hp (by rw [hf', hf]; exact ψ.symm_apply_apply _)
  have hright : ∀ x, f (f' x) = x := fun x => hp (by rw [hf, hf']; exact ψ.apply_symm_apply _)
  let φ : Symmetry C :=
    { lattice :=
        { toFun := A, invFun := A'
          left_inv a := hv (by rw [hA', hA, linear_inv, LinearIsometryEquiv.symm_apply_apply])
          right_inv a := hv (by
            rw [hA, hA', linear_inv, LinearIsometryEquiv.apply_symm_apply])
          map_add' a b := hv (by simp only [map_add, hA]) }
      toHom :=
        { toFun := f
          map_vadd' a x := hp (by
            show R.position (f (a +ᵥ x)) = R.position (A a +ᵥ f x)
            rw [hf, R.position_vadd, R.position_vadd, hA, hf]
            simpa only [vadd_eq_add] using ψ.map_vadd (R.position x) (R.vector a)) }
      bijective := ⟨Function.LeftInverse.injective hleft, Function.LeftInverse.surjective hright⟩ }
  refine ⟨φ, fun x y => ?_, hf⟩
  show dist (R.position (f x)) (R.position (f y)) = _
  rw [hf, hf]
  exact ψ.dist_map _ _

end NormedSpace

/-! ## C. From symmetries to the space group -/

section InnerProduct

variable [InnerProductSpace ℝ E]

/-- An isometric symmetry of a space-filling embedding is the restriction of an affine isometry of
space. -/
lemma exists_affineIsometryEquiv (hR : R.IsSpaceFilling) {φ : Symmetry C}
    (hφ : φ ∈ R.isometries) : ∃ ψ : E ≃ᵃⁱ[ℝ] E, ∀ x, ψ (R.position x) = R.position (φ x) := by
  have := hR.finiteDimensional
  obtain ⟨L, hL⟩ := exists_linearIsometryEquiv (u := R.vector)
    (w := fun d => R.vector (φ.lattice d)) hR
    (R.inner_vector_lattice_of_norm (R.norm_vector_lattice hφ))
  have key : ∀ i j, R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩) =
      L (R.basis i - R.basis j) := by
    intro i j
    have h : ∀ x, inner ℝ (L x) (R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩)) =
        inner ℝ x (R.basis i - R.basis j) := by
      intro x
      have hx : x ∈ Submodule.span ℝ (Set.range R.vector) := hR ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨d, rfl⟩ := hy
        rw [hL]
        exact R.inner_lattice_position hφ i j d
      | zero => simp
      | add x y _ _ hx hy => simp [inner_add_left, hx, hy]
      | smul c x _ hx => simp [real_inner_smul_left, hx]
    have hz : ∀ x, inner ℝ (L x) (R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩) -
        L (R.basis i - R.basis j)) = 0 := fun x => by
      rw [inner_sub_right, h, L.inner_map_map, sub_self]
    have := hz (L.symm (R.position (φ ⟨0, i⟩) - R.position (φ ⟨0, j⟩) -
      L (R.basis i - R.basis j)))
    rwa [L.apply_symm_apply, inner_self_eq_zero, sub_eq_zero] at this
  set i₀ : C.UnitCell := Classical.arbitrary _
  have ht : ∀ i, R.position (φ ⟨0, i⟩) =
      L (R.basis i) + (R.position (φ ⟨0, i₀⟩) - L (R.basis i₀)) := fun i => by
    have := key i i₀
    rw [map_sub, sub_eq_iff_eq_add] at this
    rw [this]
    abel
  refine ⟨L.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.constVAdd ℝ E (R.position (φ ⟨0, i₀⟩) - L (R.basis i₀))), fun x => ?_⟩
  show (R.position (φ ⟨0, i₀⟩) - L (R.basis i₀)) + L (R.position x) = R.position (φ x)
  rw [R.position_apply (φ := φ) x, ht x.label]
  rw [show R.position x = R.vector x.cell + R.basis x.label from rfl, map_add, hL]
  abel

/-- An isometric symmetry of a space-filling embedding is the restriction of an element of the
space group. -/
lemma exists_mem_spaceGroup (hR : R.IsSpaceFilling) {φ : Symmetry C} (hφ : φ ∈ R.isometries) :
    ∃ ψ ∈ R.spaceGroup, ∀ x, ψ (R.position x) = R.position (φ x) := by
  obtain ⟨ψ, h⟩ := R.exists_affineIsometryEquiv hR hφ
  refine ⟨ψ, ?_, h⟩
  show ψ '' Set.range R.position = Set.range R.position
  rw [← Set.range_comp, show ψ ∘ R.position = R.position ∘ φ from funext h, Set.range_comp,
    show Set.range ⇑φ = Set.univ from φ.bijective.surjective.range_eq, Set.image_univ]

/-- **A symmetry preserves distances exactly when it is the restriction of an element of the space
group.** -/
lemma mem_isometries_iff_exists (hR : R.IsSpaceFilling) {φ : Symmetry C} :
    φ ∈ R.isometries ↔ ∃ ψ ∈ R.spaceGroup, ∀ x, ψ (R.position x) = R.position (φ x) :=
  ⟨R.exists_mem_spaceGroup hR, fun ⟨ψ, _, h⟩ x y => by
    rw [← h x, ← h y]
    exact ψ.dist_map _ _⟩

end InnerProduct

end Embedding

end Physlib.CondensedMatter.Crystal
