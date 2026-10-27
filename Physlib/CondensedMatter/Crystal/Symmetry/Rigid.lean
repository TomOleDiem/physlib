/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding.SpaceGroup
public import Physlib.CondensedMatter.Crystal.Symmetry.Isometries

/-!
# Isometries of space as symmetries of a crystal

An affine isometry that preserves the positions of an embedded crystal is the action of a
symmetry of the abstract crystal that preserves distances.

## i. Overview

Embed a crystal in a real normed space so that distinct translations have distinct vectors,
distinct sites have distinct positions, and the lattice is exactly the translations of the
crystal. An affine isometry that maps the set of positions onto itself then moves every site to a
site. Its linear part maps the lattice to itself, which gives an automorphism of the translation
group. Together they form a symmetry of the abstract crystal, and it preserves the distances
between the positions.

## ii. Key results

- `Embedding.exists_lattice_vector_eq_linear`: The linear part of an element of the space group
  maps lattice vectors to lattice vectors.
- `Embedding.exists_site_position_eq`: An element of the space group moves every position to a
  position.
- `Embedding.exists_isometry`: Every element of the space group is the action of an isometric
  symmetry of the abstract crystal.

## iii. Table of contents

- A. The linear part preserves the lattice
- B. From an isometry of space to a symmetry

## iv. References

* N. W. Ashcroft and N. D. Mermin, *Solid State Physics*, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : Embedding C E)

/-! ## A. The linear part preserves the lattice -/

omit [NormedSpace ℝ E] in
/-- A translation by a lattice vector maps the set of positions onto itself. -/
lemma image_vadd_range_position (a : G) :
    (HAdd.hAdd (R.vector a)) '' Set.range R.position = Set.range R.position := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨a +ᵥ x, R.position_vadd a x⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨R.position ((-a) +ᵥ x), ⟨_, rfl⟩, ?_⟩
    rw [R.position_vadd, ← add_assoc, map_neg, add_neg_cancel, zero_add]

/-- The linear part of an isometry in the space group maps lattice vectors to lattice vectors,
when the lattice is the full translation group of the placed crystal. -/
lemma exists_lattice_vector_eq_linear (hprim : R.IsPrimitive) {ψ : E ≃ᵃⁱ[ℝ] E}
    (hψ : ψ ∈ R.spaceGroup) (a : G) :
    ∃ b : G, R.vector b = ψ.linearIsometryEquiv (R.vector a) := by
  have hψ' : ψ '' Set.range R.position = Set.range R.position := hψ
  have key : ∀ c : G, ∀ s ∈ Set.range R.position,
      ψ.linearIsometryEquiv (R.vector c) + s ∈ Set.range R.position := by
    intro c s hs
    have hs' : s ∈ ψ '' Set.range R.position := by
      rw [hψ']
      exact hs
    obtain ⟨s0, hs0, rfl⟩ := hs'
    have h1 : R.vector c + s0 ∈ Set.range R.position := by
      rw [← R.image_vadd_range_position c]
      exact ⟨s0, hs0, rfl⟩
    have h2 : ψ (R.vector c + s0) ∈ Set.range R.position := by
      rw [← hψ']
      exact ⟨_, h1, rfl⟩
    have h3 := ψ.map_vadd s0 (R.vector c)
    simp only [vadd_eq_add] at h3
    rw [← h3]
    exact h2
  have heq : (HAdd.hAdd (ψ.linearIsometryEquiv (R.vector a))) '' Set.range R.position =
      Set.range R.position := by
    apply Set.Subset.antisymm
    · rintro _ ⟨s, hs, rfl⟩
      exact key a s hs
    · intro s hs
      refine ⟨ψ.linearIsometryEquiv (R.vector (-a)) + s, key (-a) s hs, ?_⟩
      rw [← add_assoc, map_neg R.vector, map_neg ψ.linearIsometryEquiv, add_neg_cancel, zero_add]
  exact (hprim _).1 heq

/-! ## B. From an isometry of space to a symmetry -/

/-- An isometry in the space group moves every position to a position. -/
lemma exists_site_position_eq {ψ : E ≃ᵃⁱ[ℝ] E} (hψ : ψ ∈ R.spaceGroup) (x : C.Site) :
    ∃ y : C.Site, R.position y = ψ (R.position x) := by
  have hψ' : ψ '' Set.range R.position = Set.range R.position := hψ
  have : ψ (R.position x) ∈ Set.range R.position := by
    rw [← hψ']
    exact ⟨_, ⟨x, rfl⟩, rfl⟩
  exact this

/-- The linear part of the inverse undoes the linear part. -/
lemma linear_inv_linear (ψ : E ≃ᵃⁱ[ℝ] E) (v : E) :
    ψ⁻¹.linearIsometryEquiv (ψ.linearIsometryEquiv v) = v := by
  show (linearHom ψ⁻¹ * linearHom ψ) v = v
  rw [← map_mul, inv_mul_cancel, map_one]
  rfl

/-- The linear part undoes the linear part of the inverse. -/
lemma linear_linear_inv (ψ : E ≃ᵃⁱ[ℝ] E) (v : E) :
    ψ.linearIsometryEquiv (ψ⁻¹.linearIsometryEquiv v) = v := by
  show (linearHom ψ * linearHom ψ⁻¹) v = v
  rw [← map_mul, mul_inv_cancel, map_one]
  rfl

/-- **Every element of the space group is the action of an isometric symmetry**, when the
translation vectors and the positions are injective and the lattice is the full translation group
of the placed crystal. -/
lemma exists_isometry (hv : Function.Injective R.vector) (hp : Function.Injective R.position)
    (hprim : R.IsPrimitive) {ψ : E ≃ᵃⁱ[ℝ] E} (hψ : ψ ∈ R.spaceGroup) :
    ∃ φ : Symmetry C, φ ∈ R.isometries ∧ ∀ x, R.position (φ x) = ψ (R.position x) := by
  have hψi : ψ⁻¹ ∈ R.spaceGroup := inv_mem hψ
  choose f hf using R.exists_site_position_eq hψ
  choose A hA using R.exists_lattice_vector_eq_linear hprim hψ
  choose f' hf' using R.exists_site_position_eq hψi
  choose A' hA' using R.exists_lattice_vector_eq_linear hprim hψi
  have hAadd : ∀ a b : G, A (a + b) = A a + A b := by
    intro a b
    apply hv
    calc R.vector (A (a + b)) = ψ.linearIsometryEquiv (R.vector (a + b)) := hA _
      _ = ψ.linearIsometryEquiv (R.vector a) + ψ.linearIsometryEquiv (R.vector b) := by
        rw [map_add, map_add]
      _ = R.vector (A a) + R.vector (A b) := by rw [hA, hA]
      _ = R.vector (A a + A b) := (map_add _ _ _).symm
  have hleft : ∀ a : G, A' (A a) = a := by
    intro a
    apply hv
    rw [hA', hA, linear_inv_linear]
  have hright : ∀ a : G, A (A' a) = a := by
    intro a
    apply hv
    rw [hA, hA', linear_linear_inv]
  have hequiv : ∀ (a : G) (x : C.Site), f (a +ᵥ x) = A a +ᵥ f x := by
    intro a x
    apply hp
    rw [hf, R.position_vadd, R.position_vadd, hA, hf]
    have h := ψ.map_vadd (R.position x) (R.vector a)
    simpa only [vadd_eq_add] using h
  have hinv1 : ∀ x : C.Site, f' (f x) = x := by
    intro x
    apply hp
    rw [hf', hf]
    exact ψ.symm_apply_apply _
  have hinv2 : ∀ x : C.Site, f (f' x) = x := by
    intro x
    apply hp
    rw [hf, hf']
    exact ψ.apply_symm_apply _
  refine ⟨{ lattice := { toFun := A, invFun := A', left_inv := hleft, right_inv := hright,
                         map_add' := hAadd }
            toHom := { toFun := f, map_vadd' := hequiv }
            bijective := ⟨Function.LeftInverse.injective hinv1,
              Function.LeftInverse.surjective hinv2⟩ }, ?_, ?_⟩
  · rw [mem_isometries_iff]
    intro x y
    show dist (R.position (f x)) (R.position (f y)) = dist (R.position x) (R.position y)
    rw [hf, hf]
    exact ψ.dist_map _ _
  · intro x
    exact hf x


end Embedding

end Physlib.CondensedMatter.Crystal
