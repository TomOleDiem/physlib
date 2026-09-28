/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.ProbTheory.OrderUnit.Lattice
public import PhyslibAlpha.ProbTheory.State.Separation
public import PhyslibAlpha.Mathematics.Convex.DominatedCone
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Tensor cones of order-unit spaces

## i. Overview

Two systems with observables `E` and `F` are combined into a composite system whose observables
are the tensor products `E ⊗ F`. Which composite observables are nonnegative is not fixed by the
parts; there are two extreme choices.

The minimal cone contains only the sums of products `x ⊗ y` of nonnegative observables: nonnegative
local observations. The maximal cone contains every composite observable that no pair of local
preparations `φ ⊗ ψ` can assign a negative value. Every minimal-cone observable is in the maximal
cone. A system is nuclear when, for every other system, the maximal cone lies in the closure of the
minimal cone: its composites are unique.

## ii. Key results

- `PositiveLinearMap.tensor` : the product functional `φ ⊗ ψ`.
- `minTensorCone E F` : sums of products of nonnegative observables.
- `maxTensorCone E F` : composite observables that product functionals keep nonnegative.
- `minTensorCone_subset_maxTensorCone` : the minimal cone lies in the maximal cone.
- `isDominatedCone_minTensorCone` : every composite observable plus a large multiple of `1 ⊗ 1` lies
  in the minimal cone.
- `minTensorClosure E F` : the Archimedean closure of the minimal cone.
- `IsNuclear E` : composition with every Archimedean system is unique, up to closure.
- `mem_maxTensorCone_iff_rslice` : for Archimedean `E`, the maximal cone consists of the composite
  observables that stay nonnegative when a positive functional is applied to the second factor.

## iii. Table of contents

- A. Slices and product functionals
- B. The minimal and the maximal cone

-/

@[expose] public section

open TensorProduct

variable {E F : Type*} [OrderUnitSpace E] [OrderUnitSpace F]

/-! ## A. Slices and product functionals -/

namespace PositiveLinearMap

/-- Apply a positive functional to the second factor. -/
noncomputable def rslice (ψ : F →ₚ[ℝ] ℝ) : E ⊗[ℝ] F →ₗ[ℝ] E :=
  (TensorProduct.rid ℝ E).toLinearMap ∘ₗ TensorProduct.map LinearMap.id ψ.toLinearMap

/-- Apply a positive functional to the first factor. -/
noncomputable def lslice (φ : E →ₚ[ℝ] ℝ) : E ⊗[ℝ] F →ₗ[ℝ] F :=
  (TensorProduct.lid ℝ F).toLinearMap ∘ₗ TensorProduct.map φ.toLinearMap LinearMap.id

@[simp]
lemma rslice_tmul (ψ : F →ₚ[ℝ] ℝ) (x : E) (y : F) : rslice ψ (x ⊗ₜ[ℝ] y) = ψ y • x := by
  simp [rslice]

@[simp]
lemma lslice_tmul (φ : E →ₚ[ℝ] ℝ) (x : E) (y : F) : lslice φ (x ⊗ₜ[ℝ] y) = φ x • y := by
  simp [lslice]

/-- The product functional `φ ⊗ ψ`. -/
noncomputable def tensor (φ : E →ₚ[ℝ] ℝ) (ψ : F →ₚ[ℝ] ℝ) : E ⊗[ℝ] F →ₗ[ℝ] ℝ :=
  φ.toLinearMap ∘ₗ rslice ψ

@[simp]
lemma tensor_tmul (φ : E →ₚ[ℝ] ℝ) (ψ : F →ₚ[ℝ] ℝ) (x : E) (y : F) :
    tensor φ ψ (x ⊗ₜ[ℝ] y) = φ x * ψ y := by
  simp [tensor, mul_comm]

lemma tensor_apply (φ : E →ₚ[ℝ] ℝ) (ψ : F →ₚ[ℝ] ℝ) (z : E ⊗[ℝ] F) :
    tensor φ ψ z = φ (rslice ψ z) :=
  rfl

lemma tensor_apply_eq_lslice (φ : E →ₚ[ℝ] ℝ) (ψ : F →ₚ[ℝ] ℝ) (z : E ⊗[ℝ] F) :
    tensor φ ψ z = ψ (lslice φ z) := by
  change tensor φ ψ z = (ψ.toLinearMap ∘ₗ lslice φ) z
  congr 1
  exact TensorProduct.ext' fun x y => by simp

end PositiveLinearMap

/-! ## B. The minimal and the maximal cone -/

open PositiveLinearMap

variable (E F) in
/-- The minimal tensor cone: sums of products of nonnegative observables. -/
def minTensorCone : Set (E ⊗[ℝ] F) :=
  AddSubmonoid.closure {z | ∃ (x : E) (y : F), 0 ≤ x ∧ 0 ≤ y ∧ z = x ⊗ₜ[ℝ] y}

variable (E F) in
/-- The maximal tensor cone: composite observables to which no product of positive functionals
assigns a negative value. -/
def maxTensorCone : Set (E ⊗[ℝ] F) :=
  {z | ∀ (φ : E →ₚ[ℝ] ℝ) (ψ : F →ₚ[ℝ] ℝ), 0 ≤ tensor φ ψ z}

lemma tmul_mem_minTensorCone {x : E} {y : F} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ⊗ₜ[ℝ] y ∈ minTensorCone E F :=
  AddSubmonoid.subset_closure ⟨x, y, hx, hy, rfl⟩

/-- Every observable in the minimal cone is in the maximal cone. -/
lemma minTensorCone_subset_maxTensorCone : minTensorCone E F ⊆ maxTensorCone E F := by
  intro z hz φ ψ
  induction hz using AddSubmonoid.closure_induction with
  | mem _ h =>
    obtain ⟨x, y, hx, hy, rfl⟩ := h
    simpa using mul_nonneg (map_nonneg φ hx) (map_nonneg ψ hy)
  | zero => simp
  | add _ _ _ _ h₁ h₂ => rw [map_add]; exact add_nonneg h₁ h₂

lemma smul_mem_minTensorCone {c : ℝ} (hc : 0 ≤ c) {w : E ⊗[ℝ] F} (hw : w ∈ minTensorCone E F) :
    c • w ∈ minTensorCone E F := by
  induction hw using AddSubmonoid.closure_induction with
  | mem _ h =>
    obtain ⟨x, y, hx, hy, rfl⟩ := h
    rw [smul_tmul']; exact tmul_mem_minTensorCone (smul_nonneg hc hx) hy
  | zero => rw [smul_zero]; exact AddSubmonoid.zero_mem _
  | add _ _ _ _ h₁ h₂ => rw [smul_add]; exact AddSubmonoid.add_mem _ h₁ h₂

/-- A product plus a large enough multiple of `1 ⊗ 1` lies in the minimal cone:
`x ⊗ y + (a * b) • (1 ⊗ 1)` is half the sum of `(a • 1 ± x) ⊗ (b • 1 ± y)`. -/
lemma exists_tmul_add_smul_mem (x : E) (y : F) :
    ∃ t : ℝ, x ⊗ₜ[ℝ] y + t • ((1 : E) ⊗ₜ[ℝ] (1 : F)) ∈ minTensorCone E F := by
  obtain ⟨a, hxlo, hxhi⟩ := OrderUnitSpace.exists_two_sided_bound x
  obtain ⟨b, hylo, hyhi⟩ := OrderUnitSpace.exists_two_sided_bound y
  rw [← Nat.cast_smul_eq_nsmul ℝ] at hxlo hxhi hylo hyhi
  have h₁ := tmul_mem_minTensorCone (neg_le_iff_add_nonneg'.1 hxlo) (neg_le_iff_add_nonneg'.1 hylo)
  have h₂ := tmul_mem_minTensorCone (sub_nonneg.2 hxhi) (sub_nonneg.2 hyhi)
  refine ⟨(a : ℝ) * b, ?_⟩
  have := smul_mem_minTensorCone (by norm_num : (0 : ℝ) ≤ 1 / 2) (AddSubmonoid.add_mem _ h₁ h₂)
  convert this using 1
  simp only [add_tmul, tmul_add, sub_tmul, tmul_sub, ← smul_tmul', tmul_smul, smul_smul,
    smul_add, smul_sub]
  module

/-- Every composite observable plus a large enough multiple of `1 ⊗ 1` lies in the minimal cone. -/
lemma exists_add_smul_mem (z : E ⊗[ℝ] F) :
    ∃ t : ℝ, z + t • ((1 : E) ⊗ₜ[ℝ] (1 : F)) ∈ minTensorCone E F := by
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact exists_tmul_add_smul_mem x y
  | add z z' hz hz' =>
    obtain ⟨t, ht⟩ := hz
    obtain ⟨t', ht'⟩ := hz'
    refine ⟨t + t', ?_⟩
    have e : z + z' + (t + t') • ((1 : E) ⊗ₜ[ℝ] (1 : F)) =
        (z + t • ((1 : E) ⊗ₜ[ℝ] (1 : F))) + (z' + t' • ((1 : E) ⊗ₜ[ℝ] (1 : F))) := by
      rw [add_smul]; abel
    rw [e]; exact AddSubmonoid.add_mem _ ht ht'

/-- The minimal cone is a convex cone dominated by `1 ⊗ 1`. -/
lemma isDominatedCone_minTensorCone :
    IsDominatedCone (minTensorCone E F) ((1 : E) ⊗ₜ[ℝ] (1 : F)) where
  zero_mem := AddSubmonoid.zero_mem _
  add_mem _ ha _ hb := AddSubmonoid.add_mem _ ha hb
  smul_mem _ hc _ ha := smul_mem_minTensorCone hc ha
  mem := tmul_mem_minTensorCone OrderUnitSpace.one_nonneg OrderUnitSpace.one_nonneg
  dominates := exists_add_smul_mem

variable (E F) in
/-- The Archimedean closure of the minimal cone: composite observables that become sums of products
of nonnegative observables after adding any positive multiple of the unit `1 ⊗ 1`. -/
def minTensorClosure : Set (E ⊗[ℝ] F) :=
  {z | ∀ ε : ℝ, 0 < ε → z + ε • ((1 : E) ⊗ₜ[ℝ] (1 : F)) ∈ minTensorCone E F}

lemma minTensorCone_subset_closure : minTensorCone E F ⊆ minTensorClosure E F := by
  intro z hz ε hε
  have h : (ε • (1 : E)) ⊗ₜ[ℝ] (1 : F) ∈ minTensorCone E F :=
    tmul_mem_minTensorCone (smul_nonneg hε.le OrderUnitSpace.one_nonneg) OrderUnitSpace.one_nonneg
  rw [← smul_tmul'] at h
  exact AddSubmonoid.add_mem _ hz h

/-- The closure of the minimal cone lies in the maximal cone. -/
lemma minTensorClosure_subset_maxTensorCone : minTensorClosure E F ⊆ maxTensorCone E F :=
  fun z hz φ ψ => le_of_forall_pos_le_add fun ε hε => by
    have hφ : 0 ≤ φ 1 := map_nonneg φ OrderUnitSpace.one_nonneg
    have hψ : 0 ≤ ψ 1 := map_nonneg ψ OrderUnitSpace.one_nonneg
    have := minTensorCone_subset_maxTensorCone
      (hz (ε / (φ 1 * ψ 1 + 1)) (by positivity)) φ ψ
    rw [map_add, map_smul, tensor_tmul, smul_eq_mul] at this
    have h : ε / (φ 1 * ψ 1 + 1) * (φ 1 * ψ 1) ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith

variable (E) in
/-- A system is nuclear when it composes uniquely with every Archimedean system: every composite
observable in the maximal cone lies in the closure of the minimal cone. -/
def IsNuclear : Prop :=
  ∀ (F : Type) [ArchimedeanOrderUnitSpace F], maxTensorCone E F ⊆ minTensorClosure E F

section Archimedean

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

/-- For Archimedean `E`, a composite observable is in the maximal cone exactly when applying any
positive functional to the second factor leaves a nonnegative observable. -/
lemma mem_maxTensorCone_iff_rslice {z : E ⊗[ℝ] F} :
    z ∈ maxTensorCone E F ↔ ∀ ψ : F →ₚ[ℝ] ℝ, 0 ≤ rslice ψ z := by
  refine ⟨fun h ψ => (UnitalPositiveLinearMap.nonneg_iff_forall_state_nonneg _).2 fun ω => ?_,
    fun h φ ψ => map_nonneg φ (h ψ)⟩
  exact h ω.toPositiveLinearMap ψ

end Archimedean
