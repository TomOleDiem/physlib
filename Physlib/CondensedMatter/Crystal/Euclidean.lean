/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Embedding
public import Mathlib.Analysis.Normed.Affine.Isometry
public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import Mathlib.Tactic.Abel
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# A crystal in a real normed space

Placing a crystal in a real normed space, and the isometries that preserve it.

## i. Overview

An embedding of a crystal in a real normed space `E` sends each translation `a ∈ G` to a vector
`vector a ∈ E` and each site to a position, such that translating a site by `a` translates its
position by `vector a`. Nothing here needs `E` to be a Euclidean space or `G` to have a particular
rank. The usual picture is `G = ℤᵈ` and `E = ℝᵈ`.

The dimension is right when the translation vectors span `E`: the crystal is then periodic in every
direction. It does not have to be: a chain placed in the plane has translation vectors spanning
only a line. Whenever `E` is finite dimensional, the span of the translation vectors has dimension
at most that of `E`, with equality exactly when they span.

By the Mazur–Ulam theorem every isometry of `E` onto itself is affine, so the symmetries of the
placed crystal are the affine isometries that map the set of positions onto itself. They form the
space group. Sending an affine isometry to its linear part is a homomorphism whose kernel is the
translations. Translations that preserve the positions are those by the vectors of the lattice when
the translation group is exactly the translations of the crystal. In that case the quotient of the
space group by these translations is the point group, the group of linear parts.

## ii. Key results

- `Crystal.LatticeEmbedding` : translation vectors and positions, compatible with translation.
- `Crystal.LatticeEmbedding.IsFullRank` : the translation vectors span the space.
- `Crystal.LatticeEmbedding.isFullRank_iff_finrank` : full rank is a statement about dimensions.
- `Crystal.LatticeEmbedding.spaceGroup` : the affine isometries that preserve the positions.
- `Crystal.LatticeEmbedding.pointGroup` : the linear parts of the space group.
- `Crystal.LatticeEmbedding.spaceGroupQuotientEquiv` : the space group modulo its translations is
  the point group.
- `Crystal.LatticeEmbedding.rigidSymmetries` : the symmetries of the abstract crystal that keep the
  distances between the placed sites, a subgroup of all symmetries.

## iii. Table of contents

- A. Translation vectors and positions
- B. The dimension
- C. The space group
- D. The point group
- E. Rigid symmetries

## iv. References

* None.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

/-! ## A. Translation vectors and positions -/

/-- A crystal in a real normed space: a vector for each translation and a position for each site,
such that translating a site translates its position. -/
structure LatticeEmbedding (C : Crystal G) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] where
  /-- The vector of a translation. -/
  vector : G →+ E
  /-- The position of a site. -/
  position : C.Site → E
  /-- Translating a site translates its position. -/
  position_vadd : ∀ (a : G) (x : C.Site), position (a +ᵥ x) = vector a + position x

namespace LatticeEmbedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (R : LatticeEmbedding C E)

/-! ## B. The dimension -/

/-- The translation vectors span the space, so that the crystal is periodic in every direction. -/
def IsFullRank : Prop := Submodule.span ℝ (Set.range R.vector) = ⊤

/-- The translation vectors span at most the dimension of the space. -/
lemma finrank_span_le [FiniteDimensional ℝ E] :
    Module.finrank ℝ (Submodule.span ℝ (Set.range R.vector)) ≤ Module.finrank ℝ E :=
  Submodule.finrank_le _

/-- The translation vectors span the space exactly when their span has the dimension of the
space. -/
lemma isFullRank_iff_finrank [FiniteDimensional ℝ E] :
    R.IsFullRank ↔
      Module.finrank ℝ (Submodule.span ℝ (Set.range R.vector)) = Module.finrank ℝ E := by
  constructor
  · intro h
    rw [IsFullRank] at h
    rw [h]
    exact finrank_top ℝ E
  · intro h
    exact Submodule.eq_top_of_finrank_eq h

/-! ## C. The space group -/

/-- The linear part of an affine isometry is the difference of the images of a point and the
origin. -/
lemma linear_apply (ψ : E ≃ᵃⁱ[ℝ] E) (v : E) : ψ.linearIsometryEquiv v = ψ v - ψ 0 := by
  simpa using ψ.map_vsub v 0

/-- The linear part of an affine isometry, as a homomorphism. -/
noncomputable def linearHom : (E ≃ᵃⁱ[ℝ] E) →* (E ≃ₗᵢ[ℝ] E) where
  toFun ψ := ψ.linearIsometryEquiv
  map_one' := by
    ext v
    show (1 : E ≃ᵃⁱ[ℝ] E).linearIsometryEquiv v = v
    rw [linear_apply]
    simp
  map_mul' ψ χ := by
    ext v
    show (ψ * χ).linearIsometryEquiv v = ψ.linearIsometryEquiv (χ.linearIsometryEquiv v)
    rw [linear_apply, linear_apply χ, map_sub, linear_apply ψ, linear_apply ψ (χ 0)]
    simp only [AffineIsometryEquiv.coe_mul, Function.comp_apply]
    abel

/-- Translation by a vector, as an affine isometry. -/
noncomputable def translationHom : Multiplicative E →* (E ≃ᵃⁱ[ℝ] E) where
  toFun v := AffineIsometryEquiv.constVAdd ℝ E (Multiplicative.toAdd v)
  map_one' := by
    ext v
    exact zero_add v
  map_mul' a b := by
    ext v
    exact add_assoc _ _ _

/-- An affine isometry with trivial linear part is a translation. -/
lemma eq_translation_of_linear_eq_one (ψ : E ≃ᵃⁱ[ℝ] E) (h : linearHom ψ = 1) :
    ψ = translationHom (Multiplicative.ofAdd (ψ 0)) := by
  ext v
  have hv : ψ.linearIsometryEquiv v = v := DFunLike.congr_fun h v
  rw [linear_apply] at hv
  exact sub_eq_iff_eq_add'.1 hv

/-- The linear part of a translation is trivial. -/
lemma linearHom_translationHom (v : E) :
    linearHom (translationHom (Multiplicative.ofAdd v)) = 1 := by
  ext w
  show (translationHom (Multiplicative.ofAdd v)).linearIsometryEquiv w = w
  rw [linear_apply]
  show v + w - (v + 0) = w
  simp

/-- The kernel of the linear part is the translations. -/
lemma ker_linearHom : (linearHom (E := E)).ker = (translationHom (E := E)).range := by
  ext ψ
  constructor
  · intro h
    exact ⟨_, (eq_translation_of_linear_eq_one ψ h).symm⟩
  · rintro ⟨v, rfl⟩
    exact linearHom_translationHom (Multiplicative.toAdd v)

/-- The affine isometries that map the set of positions onto itself. By the Mazur–Ulam theorem,
these are all the isometries of `E` that preserve the placed crystal. -/
def spaceGroup : Subgroup (E ≃ᵃⁱ[ℝ] E) where
  carrier := {ψ | ψ '' Set.range R.position = Set.range R.position}
  one_mem' := by simp
  mul_mem' {ψ χ} hψ hχ := by
    show (⇑ψ ∘ ⇑χ) '' Set.range R.position = Set.range R.position
    rw [Set.image_comp, hχ, hψ]
  inv_mem' {ψ} hψ := by
    show ⇑ψ.symm '' Set.range R.position = Set.range R.position
    conv_lhs => rw [← hψ]
    rw [← Set.image_comp]
    simp

/-- A translation is in the space group when it maps the set of positions onto itself. -/
lemma translation_mem_spaceGroup_iff (v : E) :
    translationHom (Multiplicative.ofAdd v) ∈ R.spaceGroup ↔
      (HAdd.hAdd v) '' Set.range R.position = Set.range R.position := Iff.rfl

/-- The lattice is the full translation group of the placed crystal: a translation maps the
positions onto themselves exactly when its vector is a translation vector of the lattice. -/
def IsPrimitive : Prop :=
  ∀ v : E, (HAdd.hAdd v) '' Set.range R.position = Set.range R.position ↔
    v ∈ Set.range R.vector

/-! ## D. The point group -/

/-- The point group: the linear parts of the space group. -/
noncomputable def pointGroup : Subgroup (E ≃ₗᵢ[ℝ] E) := R.spaceGroup.map linearHom

/-- The homomorphism from the space group to the point group. -/
noncomputable def spaceGroupToPointGroup : R.spaceGroup →* R.pointGroup :=
  (linearHom.comp R.spaceGroup.subtype).codRestrict _ (by
    intro ψ
    exact ⟨ψ, ψ.2, rfl⟩)

/-- Every element of the point group is the linear part of an element of the space group. -/
lemma spaceGroupToPointGroup_surjective : Function.Surjective R.spaceGroupToPointGroup := by
  rintro ⟨φ, ψ, hψ, rfl⟩
  exact ⟨⟨ψ, hψ⟩, rfl⟩

/-- **The space group modulo its translations is the point group.** -/
noncomputable def spaceGroupQuotientEquiv :
    R.spaceGroup ⧸ R.spaceGroupToPointGroup.ker ≃* R.pointGroup :=
  QuotientGroup.quotientKerEquivOfSurjective _ R.spaceGroupToPointGroup_surjective

/-- The kernel of the map to the point group consists of translations of the space group. -/
lemma mem_ker_spaceGroupToPointGroup_iff (ψ : R.spaceGroup) :
    ψ ∈ R.spaceGroupToPointGroup.ker ↔ ∃ v : E, (ψ : E ≃ᵃⁱ[ℝ] E) =
      translationHom (Multiplicative.ofAdd v) := by
  constructor
  · intro h
    have h1 : linearHom (ψ : E ≃ᵃⁱ[ℝ] E) = 1 := congrArg Subtype.val h
    exact ⟨_, eq_translation_of_linear_eq_one _ h1⟩
  · rintro ⟨v, hv⟩
    apply Subtype.ext
    show linearHom (ψ : E ≃ᵃⁱ[ℝ] E) = 1
    rw [hv]
    exact linearHom_translationHom v

/-- When the lattice is the full translation group of the crystal, the translations of the space
group are exactly the translations by lattice vectors. -/
lemma mem_ker_spaceGroupToPointGroup_iff_of_isPrimitive (hR : R.IsPrimitive) (ψ : R.spaceGroup) :
    ψ ∈ R.spaceGroupToPointGroup.ker ↔ ∃ a : G,
      (ψ : E ≃ᵃⁱ[ℝ] E) = translationHom (Multiplicative.ofAdd (R.vector a)) := by
  rw [mem_ker_spaceGroupToPointGroup_iff]
  constructor
  · rintro ⟨v, hv⟩
    have hmem : translationHom (Multiplicative.ofAdd v) ∈ R.spaceGroup := hv ▸ ψ.2
    obtain ⟨a, rfl⟩ := (hR v).1 ((R.translation_mem_spaceGroup_iff v).1 hmem)
    exact ⟨a, hv⟩
  · rintro ⟨a, ha⟩
    exact ⟨_, ha⟩

/-! ## E. Rigid symmetries -/

/-- The translation group acts on the space by its translation vectors. -/
abbrev action : AddAction G E := AddAction.compHom E R.vector

/-- The positions of the sites, as a placement of the crystal in a metric space. -/
def toEmbedding : @Embedding G _ _ C E _ R.action :=
  @Embedding.mk G _ _ C E _ R.action R.position R.position_vadd

/-- The symmetries of the abstract crystal that keep the distances between the placed sites. This
is a subgroup of the symmetries: the placement is more rigid than the lattice alone. -/
def rigidSymmetries : Subgroup (Symmetry C) :=
  letI := R.action
  R.toEmbedding.isometries

/-- A symmetry is rigid when it keeps the distance between the positions of any two sites. -/
lemma mem_rigidSymmetries_iff (φ : Symmetry C) :
    φ ∈ R.rigidSymmetries ↔ ∀ x y : C.Site,
      dist (R.position (φ x)) (R.position (φ y)) = dist (R.position x) (R.position y) := Iff.rfl

/-- Translations are rigid. -/
lemma translations_le_rigidSymmetries : Symmetry.translations C ≤ R.rigidSymmetries := by
  rintro _ ⟨b, rfl⟩ x y
  show dist (R.position (Multiplicative.toAdd b +ᵥ x)) (R.position (Multiplicative.toAdd b +ᵥ y)) =
    dist (R.position x) (R.position y)
  rw [R.position_vadd, R.position_vadd, dist_add_left]

end LatticeEmbedding

end Physlib.CondensedMatter.Crystal
