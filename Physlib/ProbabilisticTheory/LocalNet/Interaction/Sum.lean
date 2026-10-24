/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.LocalNet.Interaction.Basic
public import Physlib.ProbabilisticTheory.Channel.Norm
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!

# The sum of an interaction over a region

The sum over a region adds up the pieces seen in it.

## i. Overview

The sum over a region is the integral of its pieces over the labels. Discrete labels use the
counting measure. The continuum uses the Lebesgue measure. An infinite system has no total, only the
sums over regions.

The sum over a larger region is the sum over a smaller region plus a coupling. The sum over a region
that holds two separate regions is the two sums plus the pieces that cross between them.

## ii. Key results

- `Interaction.sumIn` : the sum over a region.
- `Interaction.sumIn_split` : larger region, smaller region and coupling.
- `Interaction.sumIn_disjoint` : two separate regions and the pieces that cross.
- `Interaction.sumIn_add`, `Interaction.sumIn_smul` : linearity.
- `Interaction.norm_sumIn_le` : the norm bound.

## iii. Table of contents

- A. The sum over a region
- B. Larger and smaller regions
- C. Two regions
- D. Discrete labels

## iv. References

* None.

-/

@[expose] public section

namespace ProbabilisticTheory

open MeasureTheory
open scoped ArchimedeanOrderUnitSpace

variable {R : Type*} [Preorder R] {A : R → Type*} [∀ X, ArchimedeanOrderUnitSpace (A X)]
  {N : LocalNet R A} {ι : Type*}

namespace Interaction

variable (Φ : Interaction N ι)

lemma norm_piece_le (Λ : R) (i : ι) : ‖Φ.piece Λ i‖ ≤ ‖Φ.term i‖ := by
  by_cases h : Φ.supp i ≤ Λ
  · simpa [piece, h] using (N.incl h).norm_apply_le (Φ.term i)
  · simp [piece, h]

variable [MeasurableSpace ι] (μ : Measure ι)

/-! ## A. The sum over a region -/

/-- The sum over the region `Λ`: the pieces seen in `Λ`, integrated over their labels. -/
noncomputable def sumIn (Λ : R) : A Λ := ∫ i, Φ.piece Λ i ∂μ

/-- **Norm bound.** The norm of the sum is at most the integral of the norms of the pieces. -/
lemma norm_sumIn_le (Λ : R) : ‖Φ.sumIn μ Λ‖ ≤ ∫ i, ‖Φ.piece Λ i‖ ∂μ :=
  norm_integral_le_integral_norm _

/-- The sum is additive in the pieces, for fixed regions. -/
lemma sumIn_add (s : ι → R) (t t' : ∀ i, A (s i)) {Λ : R}
    (h : Integrable ((⟨s, t⟩ : Interaction N ι).piece Λ) μ)
    (h' : Integrable ((⟨s, t'⟩ : Interaction N ι).piece Λ) μ) :
    (⟨s, t + t'⟩ : Interaction N ι).sumIn μ Λ =
      (⟨s, t⟩ : Interaction N ι).sumIn μ Λ + (⟨s, t'⟩ : Interaction N ι).sumIn μ Λ := by
  simp only [sumIn, piece_add s t t' Λ]
  exact integral_add h h'

/-- The sum is homogeneous in the pieces, for fixed regions. -/
lemma sumIn_smul (s : ι → R) (c : ℝ) (t : ∀ i, A (s i)) (Λ : R) :
    (⟨s, c • t⟩ : Interaction N ι).sumIn μ Λ = c • (⟨s, t⟩ : Interaction N ι).sumIn μ Λ := by
  simp only [sumIn, piece_smul s c t Λ]
  exact integral_smul c _

section Complete

variable [∀ X, CompleteSpace (A X)]

/-- Integrating, over the labels in `Λ`, the pieces seen in a larger region gives the sum over `Λ`
included into the larger region. -/
lemma setIntegral_labelsIn {Λ Λ' : R} (h : Λ ≤ Λ') (hS : MeasurableSet (Φ.labelsIn Λ))
    (h1 : Integrable (Φ.piece Λ) μ) :
    ∫ i in Φ.labelsIn Λ, Φ.piece Λ' i ∂μ = N.incl h (Φ.sumIn μ Λ) := by
  have e := (N.incl h).toContinuousLinearMap.integral_comp_comm h1
  simp only [UnitalPositiveLinearMap.toContinuousLinearMap_apply, Φ.incl_piece h] at e
  rwa [integral_indicator hS] at e

/-! ## B. Larger and smaller regions -/

/-- The coupling between `Λ` and `Λ'`: the pieces seen in `Λ'` that do not live in `Λ`. -/
noncomputable def coupling (Λ Λ' : R) : A Λ' := ∫ i in (Φ.labelsIn Λ)ᶜ, Φ.piece Λ' i ∂μ

/-- **Larger and smaller region.** The sum over a larger region is the sum over a smaller region
plus the coupling. -/
lemma sumIn_split {Λ Λ' : R} (h : Λ ≤ Λ') (hS : MeasurableSet (Φ.labelsIn Λ))
    (h1 : Integrable (Φ.piece Λ) μ) (h2 : Integrable (Φ.piece Λ') μ) :
    Φ.sumIn μ Λ' = N.incl h (Φ.sumIn μ Λ) + Φ.coupling μ Λ Λ' := by
  rw [← Φ.setIntegral_labelsIn μ h hS h1, coupling, integral_add_compl hS h2]
  rfl

/-! ## C. Two regions -/

/-- The pieces that cross between `Λ₁` and `Λ₂` inside `Λ`: those seen in `Λ` that live in neither
of the two regions. -/
noncomputable def crossingIn (Λ₁ Λ₂ Λ : R) : A Λ :=
  ∫ i in (Φ.labelsIn Λ₁ ∪ Φ.labelsIn Λ₂)ᶜ, Φ.piece Λ i ∂μ

/-- **Two regions.** The sum over a region that holds two separate regions is the sum over each of
them plus the pieces that cross between them. -/
lemma sumIn_disjoint {Λ₁ Λ₂ Λ : R} (h₁ : Λ₁ ≤ Λ) (h₂ : Λ₂ ≤ Λ)
    (hd : Disjoint (Φ.labelsIn Λ₁) (Φ.labelsIn Λ₂)) (m₁ : MeasurableSet (Φ.labelsIn Λ₁))
    (m₂ : MeasurableSet (Φ.labelsIn Λ₂)) (g₁ : Integrable (Φ.piece Λ₁) μ)
    (g₂ : Integrable (Φ.piece Λ₂) μ) (g : Integrable (Φ.piece Λ) μ) :
    Φ.sumIn μ Λ = N.incl h₁ (Φ.sumIn μ Λ₁) + N.incl h₂ (Φ.sumIn μ Λ₂) +
      Φ.crossingIn μ Λ₁ Λ₂ Λ := by
  rw [← Φ.setIntegral_labelsIn μ h₁ m₁ g₁, ← Φ.setIntegral_labelsIn μ h₂ m₂ g₂, crossingIn,
    ← setIntegral_union hd m₂ g.integrableOn g.integrableOn, integral_add_compl (m₁.union m₂) g]
  rfl

/-! ## D. Discrete labels -/

variable [MeasurableSingletonClass ι]

/-- With finitely many labels, the sum over a region is the sum of its pieces. -/
lemma sumIn_count [Fintype ι] (Λ : R) : Φ.sumIn Measure.count Λ = ∑ i, Φ.piece Λ i := by
  simp [sumIn]

/-- With countably many labels, the sum over a region is the sum of its pieces. -/
lemma sumIn_count_tsum [Countable ι] {Λ : R} (h : Integrable (Φ.piece Λ) Measure.count) :
    Φ.sumIn Measure.count Λ = ∑' i, Φ.piece Λ i := by
  simp [sumIn, integral_countable h]

end Complete

end Interaction

end ProbabilisticTheory
