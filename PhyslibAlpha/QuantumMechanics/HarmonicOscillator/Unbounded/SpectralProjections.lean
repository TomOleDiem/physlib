/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.HarmonicOscillator.Unbounded.DifferentialCore
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.EigenvectorSpectralAtom

/-! # The explicit Hermite discrete-sum spectral-projection formula

`DifferentialCore.lean` builds the abstract spectral measure
    `differentialHamiltonianSpectralMeasure`
of the differential oscillator Hamiltonian and identifies its maximal spectral integral with the
canonical closure. `Unbounded/EigenvectorSpectralAtom.lean` proves the general fact that an exact
eigenvector is fixed by its eigenvalue's spectral projection (and annihilated by every other
atomic projection).

This file specializes that general machinery to the (transported) Hermite eigenbasis to get the
textbook "physicist's" formula for the spectral projection onto a Borel set `S`,

`E(S) = Σ_{n : eigenvalue n ∈ S} |eₙ⟩⟨eₙ|`,

expressed rigorously as a `HasSum` statement (`hermiteSpectralProjection_hasSum`): for every
`x`, the vector series `n ↦ if eigenvalue n ∈ S then ⟪eₙ, x⟫ • eₙ else 0` sums to `E(S) x`. No new
spectral theory is proved here — every step is either already-established general
`EigenvectorSpectralAtom.lean` content, the `HilbertBasis` expansion of an arbitrary vector, or
elementary measure-theoretic bookkeeping.

## Main results

* `OperatorAlgebra.spectralMeasure_apply_eq_zero_of_disjoint_of_isEigenvector` : a general
  (non-oscillator-specific) extension of `atom_apply_eq_zero_of_isEigenvector_of_ne` from
  singletons to arbitrary measurable sets disjoint from the eigenvalue.
* `OperatorAlgebra.spectralMeasure_apply_eq_self_of_mem_of_isEigenvector` : the complementary
  general fact — an eigenvector is fixed by the spectral projection of any measurable set
  containing its eigenvalue.
* `QuantumMechanics.HarmonicOscillator.DifferentialCore.eigenValue_injective` : the oscillator's
  eigenvalue labelling `n ↦ (n + ½)ℏω` is injective.
* `hermiteBasisSpectralMeasure_apply` : the spectral projection of a Borel set `S` applied to a
  single (transported) Hermite basis vector is `eₙ` or `0` according to membership of `eigenvalue
  n` in `S`.
* `hermiteSpectralProjection_hasSum` : the discrete-sum formula for a general vector `x`.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace Classical
open MeasureTheory Set

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **General extension of `atom_apply_eq_zero_of_isEigenvector_of_ne` from singletons to
arbitrary measurable sets.** An eigenvector is annihilated by the spectral projection of any
measurable set that misses its eigenvalue. -/
lemma spectralMeasure_apply_eq_zero_of_disjoint_of_isEigenvector
    {T : H →ₗ.[ℂ] H} {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}
    (D : DomainAwareSelfAdjointSpectralTheorem T μS)
    {v : H} (hv : v ∈ T.domain) {a : ℝ} (hav : T ⟨v, hv⟩ = (a : ℂ) • v)
    {S : Set ℝ} (hS : MeasurableSet S) (haS : a ∉ S) :
    μS S v = 0 := by
  have hfix : μS {a} v = v := mem_atom_range_of_isEigenvector D hv hav
  have hdisj : Disjoint S ({a} : Set ℝ) := by
    simp [Set.disjoint_singleton_right, haS]
  have hcomp : μS S * μS {a} = 0 :=
    (μS.comp_eq_of_inter hS (measurableSet_singleton a)).trans (by
      rw [Set.disjoint_iff_inter_eq_empty.mp hdisj]; simp)
  have hcompv := congrArg (fun A : H →WOT[ℂ] H => A v) hcomp
  change μS S (μS {a} v) = 0 at hcompv
  rwa [hfix] at hcompv

/-- **General complementary fact.** An eigenvector is fixed by the spectral projection of any
measurable set containing its eigenvalue. -/
lemma spectralMeasure_apply_eq_self_of_mem_of_isEigenvector
    {T : H →ₗ.[ℂ] H} {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}
    (D : DomainAwareSelfAdjointSpectralTheorem T μS)
    {v : H} (hv : v ∈ T.domain) {a : ℝ} (hav : T ⟨v, hv⟩ = (a : ℂ) • v)
    {S : Set ℝ} (hS : MeasurableSet S) (haS : a ∈ S) :
    μS S v = v := by
  have hzero : μS (S \ {a}) v = 0 :=
    spectralMeasure_apply_eq_zero_of_disjoint_of_isEigenvector D hv hav
      (hS.diff (measurableSet_singleton a)) (by simp)
  have hfix : μS {a} v = v := mem_atom_range_of_isEigenvector D hv hav
  have hunion : ({a} : Set ℝ) ∪ (S \ {a}) = S := by
    ext r
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff]
    constructor
    · rintro (rfl | ⟨hr, -⟩)
      · exact haS
      · exact hr
    · intro hr
      by_cases hra : r = a
      · exact Or.inl hra
      · exact Or.inr ⟨hr, hra⟩
  have hsum : μS S v = μS {a} v + μS (S \ {a}) v := by
    have := congrArg (fun A : H →WOT[ℂ] H => A v)
      (μS.of_union (Set.disjoint_sdiff_right) (measurableSet_singleton a)
        (hS.diff (measurableSet_singleton a)))
    rw [hunion] at this
    exact this
  rw [hsum, hzero, hfix, add_zero]

end OperatorAlgebra

namespace QuantumMechanics.HarmonicOscillator.DifferentialCore

open _root_.QuantumMechanics.OneDimension.HarmonicOscillator (eigenValue)

variable (q : OldOscillator)

/-! ## The eigenvalue labelling is injective -/

/-- **The oscillator's eigenvalue labelling `n ↦ (n + ½)ℏω` is injective.** Distinct occupation
numbers give distinct energies, so each eigenvalue picks out a unique Hermite eigenfunction. -/
lemma eigenValue_injective : Function.Injective q.eigenValue := by
  have hℏω : (Constants.ℏ : ℝ) * q.ω ≠ 0 :=
    mul_ne_zero Constants.ℏ_ne_zero q.ω_ne_zero
  intro n₁ n₂ h
  simp only [_root_.QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue,
    mul_assoc] at h
  have h' : (n₁ : ℝ) + 1 / 2 = (n₂ : ℝ) + 1 / 2 := mul_right_cancel₀ hℏω h
  have : (n₁ : ℝ) = (n₂ : ℝ) := by linarith
  exact_mod_cast this

/-! ## The action of the spectral projection on a single Hermite basis vector -/

/-- **The spectral projection of `S` applied to a single (transported) Hermite basis vector**:
`eₙ` if `eigenvalue n ∈ S`, `0` otherwise. This is `spectralMeasure_apply_eq_self_of_mem_of_
isEigenvector`/`spectralMeasure_apply_eq_zero_of_disjoint_of_isEigenvector` specialized to the
Hermite eigenbasis, via `differentialHamiltonianClosure_apply_eigenfunction`. -/
lemma hermiteBasisSpectralMeasure_apply (n : ℕ) {S : Set ℝ} (hS : MeasurableSet S) :
    differentialHamiltonianSpectralMeasure q S (transportedEigenbasis q n) =
      if q.eigenValue n ∈ S then transportedEigenbasis q n else 0 := by
  have heq : eigenfunctionSpace q n = transportedEigenbasis q n :=
    eigenfunctionSpace_eq_transportedEigenbasis q n
  have hv : transportedEigenbasis q n ∈ (differentialHamiltonianClosure q).domain :=
    heq ▸ differentialHamiltonian_mem_closure_domain q n
  have hav : differentialHamiltonianClosure q ⟨transportedEigenbasis q n, hv⟩ =
      (q.eigenValue n : ℂ) • transportedEigenbasis q n := by
    have hsub : (⟨eigenfunctionSpace q n, differentialHamiltonian_mem_closure_domain q n⟩ :
        (differentialHamiltonianClosure q).domain) = ⟨transportedEigenbasis q n, hv⟩ :=
      Subtype.ext heq
    rw [← hsub, differentialHamiltonianClosure_apply_eigenfunction q n, heq]
  split_ifs with h
  · exact OperatorAlgebra.spectralMeasure_apply_eq_self_of_mem_of_isEigenvector
      (differentialHamiltonianSpectralTheorem q) hv hav hS h
  · exact OperatorAlgebra.spectralMeasure_apply_eq_zero_of_disjoint_of_isEigenvector
      (differentialHamiltonianSpectralTheorem q) hv hav hS h

/-! ## The discrete-sum formula for a general vector -/

/-- **The explicit Hermite discrete-sum spectral-projection formula.**

For any Borel set `S` and any vector `x`, the vector series
`n ↦ if eigenvalue n ∈ S then ⟪eₙ, x⟫ • eₙ else 0` sums to `E(S) x`, i.e.
`E(S) = Σ_{n : eigenvalue n ∈ S} |eₙ⟩⟨eₙ|` as a `HasSum` statement.

Proof: expand `x` in the (transported) Hermite `HilbertBasis` (`HilbertBasis.hasSum_repr`), then
push the sum through the bounded linear map underlying `E(S)` (`ContinuousLinearMap.hasSum`),
using `hermiteBasisSpectralMeasure_apply` to evaluate `E(S)` on each basis vector. -/
lemma hermiteSpectralProjection_hasSum {S : Set ℝ} (hS : MeasurableSet S) (x : NewHilbertSpace) :
    HasSum
      (fun n : ℕ => if q.eigenValue n ∈ S then
        (⟪transportedEigenbasis q n, x⟫_ℂ) • transportedEigenbasis q n else 0)
      (differentialHamiltonianSpectralMeasure q S x) := by
  have hrepr : HasSum (fun n : ℕ => (⟪transportedEigenbasis q n, x⟫_ℂ) • transportedEigenbasis q n)
      x := by
    simpa only [(transportedEigenbasis q).repr_apply_apply] using
      (transportedEigenbasis q).hasSum_repr x
  have hmap := (differentialHamiltonianSpectralMeasure q S).toCLM.hasSum hrepr
  simp only [ContinuousLinearMapWOT.toCLM_apply] at hmap
  have hcongr : (fun n : ℕ =>
      differentialHamiltonianSpectralMeasure q S
        ((⟪transportedEigenbasis q n, x⟫_ℂ) • transportedEigenbasis q n)) =
      fun n : ℕ => if q.eigenValue n ∈ S then
        (⟪transportedEigenbasis q n, x⟫_ℂ) • transportedEigenbasis q n else 0 := by
    funext n
    have hsmul : differentialHamiltonianSpectralMeasure q S
        ((⟪transportedEigenbasis q n, x⟫_ℂ) • transportedEigenbasis q n) =
        (⟪transportedEigenbasis q n, x⟫_ℂ) •
          differentialHamiltonianSpectralMeasure q S (transportedEigenbasis q n) := by
      have h := (differentialHamiltonianSpectralMeasure q S).toCLM.map_smul
        (⟪transportedEigenbasis q n, x⟫_ℂ) (transportedEigenbasis q n)
      simpa only [ContinuousLinearMapWOT.toCLM_apply] using h
    rw [hsmul, hermiteBasisSpectralMeasure_apply q n hS]
    split_ifs with h
    · rfl
    · rw [smul_zero]
  rwa [hcongr] at hmap

end QuantumMechanics.HarmonicOscillator.DifferentialCore
end
