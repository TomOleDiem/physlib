/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Operators.SpectralTheory.Symmetric

/-!
# General essential-self-adjointness criteria

This file contains criteria that turn a concrete total family of eigenvectors into an analytic
essential-self-adjointness proof.  The criterion is deliberately stated for `LinearPMap`, so it
does not assume a pre-existing adjoint or spectral measure.

The argument is the deficiency-space proof.  If `v i` is an eigenvector with real eigenvalue
`λ i`, then every vector orthogonal to the range of `T - z` is orthogonal to `v i`, because
`(T - z) v i = (λ i - z) v i` and the coefficient is nonzero off the real axis.  Totality of the
eigenvectors then makes the deficiency space trivial at both `z = I` and `z = -I`, and the von
Neumann criterion supplies essential self-adjointness.
-/

@[expose] public section

noncomputable section

open Set
open scoped InnerProductSpace

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Vanishing deficiency numbers from a total family of real eigenvectors. -/
lemma defectNumber_eq_zero_of_dense_eigenvectors
    {T : H →ₗ.[ℂ] H} (hT : T.IsSymmetric) (hdense : T.HasDenseDomain)
    {ι : Type*} (v : ι → H) (eigenvalue : ι → ℝ)
    (hv : ∀ i, v i ∈ T.domain)
    (heigen : ∀ i, T ⟨v i, hv i⟩ = (eigenvalue i : ℂ) • v i)
    (hnonreal : ∀ i, (eigenvalue i : ℂ) ≠ Complex.I ∧ (eigenvalue i : ℂ) ≠ -Complex.I)
    (hspan : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    T.defectNumber Complex.I = 0 ∧ T.defectNumber (-Complex.I) = 0 := by
  have hdefect (z : ℂ) (hz : ∀ i, (eigenvalue i : ℂ) ≠ z) : T.defectNumber z = 0 := by
    show Module.rank ℂ ↥((T - z • 1).toFun.rangeᗮ) = 0
    apply Submodule.rank_eq_zero.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hxrange : ∀ u ∈ (T - z • 1).toFun.range, ⟪x, u⟫_ℂ = 0 := by
      exact (Submodule.mem_orthogonal' _ x).mp hx
    have hxv : ∀ i, ⟪x, v i⟫_ℂ = 0 := by
      intro i
      let xi : (T - z • 1).domain := ⟨v i, by simp [sub_domain, hv i]⟩
      have hxi := hxrange ((T - z • 1) xi) (by
        exact ⟨xi, rfl⟩)
      have heq : (T - z • 1) xi = ((eigenvalue i : ℂ) - z) • v i := by
        rw [sub_apply, heigen]
        simp [xi, smul_apply, sub_eq_add_neg, add_smul]
      rw [heq, inner_smul_right] at hxi
      have hne : (eigenvalue i : ℂ) - z ≠ 0 := sub_ne_zero.mpr (hz i)
      exact (mul_eq_zero.mp hxi).resolve_left hne
    have hxspan : x ∈ (Submodule.span ℂ (Set.range v))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction (p := fun y _ ↦ ⟪x, y⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
      · rintro y ⟨i, rfl⟩
        exact hxv i
      · simp
      · intro y₁ y₂ _ _ hy₁ hy₂
        simp [inner_add_right, hy₁, hy₂]
      · intro c y _ hy
        simp [inner_smul_right, hy]
    have hspan_bot : (Submodule.span ℂ (Set.range v))ᗮ = (⊥ : Submodule ℂ H) :=
      Submodule.topologicalClosure_eq_top_iff.mp hspan
    have : x ∈ (⊥ : Submodule ℂ H) := hspan_bot ▸ hxspan
    exact (Submodule.mem_bot ℂ).mp this
  exact ⟨hdefect Complex.I (fun i ↦ (hnonreal i).1),
    hdefect (-Complex.I) (fun i ↦ (hnonreal i).2)⟩

/-- A symmetric operator with a total real eigenvector family is essentially self-adjoint. -/
theorem isEssentiallySelfAdjoint_of_dense_eigenvectors
    {T : H →ₗ.[ℂ] H} (hT : T.IsSymmetric) (hdense : T.HasDenseDomain)
    {ι : Type*} (v : ι → H) (eigenvalue : ι → ℝ)
    (hv : ∀ i, v i ∈ T.domain)
    (heigen : ∀ i, T ⟨v i, hv i⟩ = (eigenvalue i : ℂ) • v i)
    (hnonreal : ∀ i, (eigenvalue i : ℂ) ≠ Complex.I ∧ (eigenvalue i : ℂ) ≠ -Complex.I)
    (hspan : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    T.IsEssentiallySelfAdjoint := by
  rcases defectNumber_eq_zero_of_dense_eigenvectors hT hdense v eigenvalue hv heigen hnonreal hspan with
    ⟨hpos, hneg⟩
  exact hT.isEssentiallySelfAdjoint_of_defectNumber_eq_zero hdense hpos hneg

end LinearPMap
