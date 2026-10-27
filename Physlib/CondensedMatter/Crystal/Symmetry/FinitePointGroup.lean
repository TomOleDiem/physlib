/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetry.EmbeddingSpaceGroup
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Finiteness of the point group

The point group of a primitive, space-filling embedding with a discrete lattice is finite.

## i. Overview

The point group of an embedding consists of the linear parts of its space group. Each of them is a
linear isometry that maps the lattice vectors to lattice vectors. A linear map is determined by
its values on finitely many generators of the lattice, and the images of a generator are lattice
vectors of the same length. A discrete lattice has only finitely many vectors of bounded length, so
there are only finitely many choices for these values.

## ii. Key results

- `Crystal.Embedding.finite_lattice_ball` : a discrete lattice has finitely many vectors in a ball.
- `Crystal.Embedding.finite_pointGroup` : the point group of a primitive, space-filling embedding
  with a discrete lattice is finite.

## iii. Table of contents

- A. Lattice vectors of bounded length
- B. The point group

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (R : Embedding C E)

/-! ## A. Lattice vectors of bounded length -/

omit [NormedSpace ℝ E] in
/-- A discrete lattice has finitely many vectors in a ball. -/
lemma finite_lattice_ball [ProperSpace E] [DiscreteTopology R.vector.range] (r : ℝ) :
    (Metric.closedBall (0 : E) r ∩ R.vector.range).Finite :=
  Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete Metric.isBounded_closedBall
    (AddSubgroup.isClosed_of_discreteTopology (U := R.vector.range))

/-! ## B. The point group -/

/-- The point group maps lattice vectors to lattice vectors. -/
lemma pointGroup_apply_mem (hprim : R.IsPrimitive) {L : E ≃ₗᵢ[ℝ] E} (hL : L ∈ R.pointGroup)
    (a : G) : L (R.vector a) ∈ R.vector.range := by
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.1 hL
  exact R.exists_lattice_vector_eq_linear hprim hψ a

/-- The point group maps a lattice vector of bounded length to a lattice vector in the same
ball. -/
lemma pointGroup_apply_mem_ball (hprim : R.IsPrimitive) {L : E ≃ₗᵢ[ℝ] E} (hL : L ∈ R.pointGroup)
    {a : G} {r : ℝ} (hr : ‖R.vector a‖ ≤ r) :
    L (R.vector a) ∈ Metric.closedBall (0 : E) r ∩ R.vector.range :=
  ⟨by simpa using hr, R.pointGroup_apply_mem hprim hL a⟩

/-- Two linear isometries that agree on the vectors of generators of a space-filling embedding
are equal. -/
lemma linearIsometryEquiv_ext {S : Set G} (hS : AddSubgroup.closure S = ⊤)
    (hR : R.IsSpaceFilling) {L L' : E ≃ₗᵢ[ℝ] E} (h : ∀ s ∈ S, L (R.vector s) = L' (R.vector s)) :
    L = L' := by
  refine LinearIsometryEquiv.toLinearEquiv_injective (LinearEquiv.toLinearMap_injective ?_)
  refine LinearMap.ext_on ((R.isSpaceFilling_iff hS).1 hR) ?_
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

/-- The point group is finite if the generators of the translation group are finite and the
lattice is discrete. -/
lemma finite_pointGroup_of_generators [DiscreteTopology R.vector.range] {S : Set G}
    (hS : AddSubgroup.closure S = ⊤) (hfin : S.Finite) (hR : R.IsSpaceFilling)
    (hprim : R.IsPrimitive) : Finite R.pointGroup := by
  have := hR.finiteDimensional
  obtain ⟨r, hr⟩ := (hfin.image R.vector).isBounded.exists_norm_le
  have := (R.finite_lattice_ball r).to_subtype
  have := hfin.to_subtype
  refine Finite.of_injective (fun (L : R.pointGroup) (s : S) =>
    (⟨L.1 (R.vector s), R.pointGroup_apply_mem_ball hprim L.2 (hr _ ⟨s, s.2, rfl⟩)⟩ :
      ↥(Metric.closedBall (0 : E) r ∩ R.vector.range))) fun L L' h => ?_
  exact Subtype.ext (R.linearIsometryEquiv_ext hS hR fun s hs =>
    congrArg Subtype.val (congrFun h ⟨s, hs⟩))

/-- **The point group of a primitive, space-filling embedding with a discrete lattice is
finite.** -/
lemma finite_pointGroup [DiscreteTopology R.vector.range] (hR : R.IsSpaceFilling)
    (hprim : R.IsPrimitive) : Finite R.pointGroup := by
  obtain ⟨S, hS, hfin⟩ := (AddSubgroup.fg_iff _).1 (AddGroup.fg_def.1 ‹AddGroup.FG G›)
  exact R.finite_pointGroup_of_generators hS hfin hR hprim

end Embedding

end Physlib.CondensedMatter.Crystal
