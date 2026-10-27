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

Finiteness of the point group is the first step towards the restriction of the rotations that a
crystal can have. Every element of the point group of a primitive embedding is a linear isometry
that maps the lattice vectors to lattice vectors. The images of finitely many generators of the
lattice are lattice vectors of the same lengths as the generators, and a discrete lattice has only
finitely many vectors of bounded length. A linear map is determined by its values on generators,
so there are only finitely many choices, and the point group is finite.

## ii. Key results

- `Crystal.Euclidean.finite_closedBall_inter` : a discrete additive subgroup has finitely many
  elements in a ball.
- `Crystal.Embedding.finite_pointGroup` : the point group of a primitive, space-filling embedding
  with a discrete lattice is finite.

## iii. Table of contents

- A. Elements of bounded length
- B. The point group

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

/-! ## A. Elements of bounded length -/

namespace Euclidean

/-- A discrete additive subgroup of a proper normed group has finitely many elements in a ball. -/
lemma finite_closedBall_inter {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (L : AddSubgroup E) [DiscreteTopology L] (r : ℝ) :
    (Metric.closedBall (0 : E) r ∩ L).Finite := by
  exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    Metric.isBounded_closedBall (AddSubgroup.isClosed_of_discreteTopology (U := L))

end Euclidean

open Euclidean

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Embedding

variable {C : Crystal G} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (R : Embedding C E)

/-! ## B. The point group -/

/-- The point group maps lattice vectors to lattice vectors. -/
lemma pointGroup_apply_mem (hprim : R.IsPrimitive) {L : E ≃ₗᵢ[ℝ] E} (hL : L ∈ R.pointGroup)
    (a : G) : L (R.vector a) ∈ R.vector.range := by
  obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.1 hL
  exact R.exists_lattice_vector_eq_linear hprim hψ a

/-- Two linear isometries that agree on the vectors of generators of a space-filling embedding
are equal. -/
lemma linearIsometryEquiv_ext {S : Set G} (hS : AddSubgroup.closure S = ⊤)
    (hR : R.IsSpaceFilling) {L L' : E ≃ₗᵢ[ℝ] E} (h : ∀ s ∈ S, L (R.vector s) = L' (R.vector s)) :
    L = L' := by
  refine LinearIsometryEquiv.toLinearEquiv_injective (LinearEquiv.toLinearMap_injective ?_)
  refine LinearMap.ext_on ((R.isSpaceFilling_iff hS).1 hR) ?_
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

/-- The values of an element of the point group on generators, as lattice vectors in a ball. -/
noncomputable def ballValues (hprim : R.IsPrimitive) {S : Set G} {r : ℝ}
    (hr : ∀ s ∈ S, ‖R.vector s‖ ≤ r) (L : R.pointGroup) (s : S) :
    ↥(Metric.closedBall (0 : E) r ∩ R.vector.range) := by
  refine ⟨L.1 (R.vector s), ?_, R.pointGroup_apply_mem hprim L.2 s⟩
  simpa using hr s s.2

/-- An element of the point group is determined by its values on generators. -/
lemma injective_ballValues (hprim : R.IsPrimitive) (hR : R.IsSpaceFilling) {S : Set G}
    (hS : AddSubgroup.closure S = ⊤) {r : ℝ} (hr : ∀ s ∈ S, ‖R.vector s‖ ≤ r) :
    Function.Injective (R.ballValues hprim hr) := by
  intro L L' h
  refine Subtype.ext (R.linearIsometryEquiv_ext hS hR ?_)
  intro s hs
  exact congrArg Subtype.val (congrFun h ⟨s, hs⟩)

/-- **The point group of a primitive, space-filling embedding with a discrete lattice is
finite.** -/
lemma finite_pointGroup [DiscreteTopology R.vector.range] (hR : R.IsSpaceFilling)
    (hprim : R.IsPrimitive) : Finite R.pointGroup := by
  have := hR.finiteDimensional
  obtain ⟨S, hS, hfin⟩ := AddGroup.fg_iff.1 ‹AddGroup.FG G›
  obtain ⟨r, hr⟩ := (hfin.image R.vector).isBounded.exists_norm_le
  have := (finite_closedBall_inter R.vector.range r).to_subtype
  have := hfin.to_subtype
  have hr' : ∀ s ∈ S, ‖R.vector s‖ ≤ r := by
    intro s hs
    exact hr _ ⟨s, hs, rfl⟩
  exact Finite.of_injective _ (R.injective_ballValues hprim hR hS hr')

end Embedding

end Physlib.CondensedMatter.Crystal
