/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Affiliation.NormalAffiliatedCanonical
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Spectral.Cayley
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Spectral.CayleySpectralData
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Representation.NormalRepresentation
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Affiliation.AffiliationSpectralTheorem

/-!
# Cayley affiliation for normal affiliated observables

The Cayley transform is the bounded-transform boundary of the self-adjoint unbounded theory.  This
file packages it at the normal-affiliated level: a real normal affiliated observable has a
canonical unitary Cayley element, and any normal representation sends that element to the Cayley
unitary of the represented maximal self-adjoint operator.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra Function InnerProductSpace
open OperatorAlgebra MeasureTheory Set

namespace OperatorAlgebra

variable {A : Type*} [WStarAlgebra A]

namespace NormalAffiliatedObservable

variable (T : NormalAffiliatedObservable A)

/-- The canonical bounded Cayley transform of a real normal affiliated observable. -/
noncomputable def canonicalCayleyUnitary : unitary A := by
  let hbounded : ∃ C : ℝ, ∀ x, ‖cayley x‖ ≤ C :=
    ⟨1, fun x => by simpa [cayley_norm x]⟩
  let hunitary : T.canonicalBoundedFC cayley measurable_cayley hbounded ∈ unitary A := by
    apply T.canonicalBorelCalculus.boundedFC_mem_unitary measurable_cayley hbounded
    intro x
    rw [mul_comm]
    change cayley x * (starRingEnd ℂ) (cayley x) = 1
    rw [Complex.mul_conj, ← Complex.sq_norm]
    rw [cayley_norm]
    norm_num
  exact ⟨T.canonicalBoundedFC cayley measurable_cayley hbounded, hunitary⟩

@[simp]
lemma canonicalCayleyUnitary_coe :
    (NormalAffiliatedObservable.canonicalCayleyUnitary T : A) =
      T.canonicalBoundedFC cayley measurable_cayley
        (show ∃ C : ℝ, ∀ x, ‖cayley x‖ ≤ C from
          ⟨1, fun x => by simpa [cayley_norm x]⟩) := by
  simp [canonicalCayleyUnitary]

end NormalAffiliatedObservable

namespace NormalAffiliationBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (bridge : NormalOperatorAffiliationBridge (A := A) (H := H))

/-- The represented Cayley element is the bounded Cayley transform of the represented maximal
self-adjoint operator. -/
theorem representation_canonicalCayleyUnitary_eq_boundedIntegral
    (T : NormalAffiliatedObservable A) :
    bridge.representation (NormalAffiliatedObservable.canonicalCayleyUnitary T : A) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toNormalAffiliationBridge.representedSpectralMeasure T) cayley measurable_cayley
        (show ∃ C : ℝ, ∀ x, ‖cayley x‖ ≤ C from
          ⟨1, fun x => by simpa [cayley_norm x]⟩)).toCLM := by
    let hbounded : ∃ C : ℝ, ∀ x, ‖cayley x‖ ≤ C :=
      ⟨1, fun x => by simpa [cayley_norm x]⟩
    rw [NormalAffiliatedObservable.canonicalCayleyUnitary_coe]
    exact bridge.representation_canonicalBoundedFC T cayley measurable_cayley hbounded

end NormalAffiliationBridge

end OperatorAlgebra

namespace QuantumMechanics.WOTSpectralMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private lemma cayley_eq_one_sub_resolventMultiplier_minus_I (r : ℝ) :
    cayley r = 1 - (2 * Complex.I) * resolventMultiplier (-Complex.I) r := by
  unfold cayley resolventMultiplier
  have hden : (r : ℂ) + Complex.I ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  rw [show (r : ℂ) - Complex.I = ((r : ℂ) + Complex.I) - 2 * Complex.I by ring]
  rw [sub_div, div_self hden, div_eq_mul_inv]
  ring

/-- The bounded WOT integral of the scalar Cayley function is the bounded Cayley transform of the
maximal self-adjoint operator reconstructed from the same real spectral measure. -/
theorem boundedIntegral_cayley_eq_cayleyContinuousLinearMap
    (μS : WOTSpectralMeasure ℝ H) :
    (boundedIntegral μS cayley measurable_cayley
      (show ∃ C : ℝ, ∀ r, ‖cayley r‖ ≤ C from
        ⟨1, fun r => by simpa [cayley_norm r]⟩)).toCLM =
      cayleyContinuousLinearMap
        (maximalSpectralIntegral μS)
        (maximalSpectralIntegral_isSelfAdjoint μS) := by
  let M := maximalSpectralIntegral μS
  let hM : IsSelfAdjoint M := maximalSpectralIntegral_isSelfAdjoint μS
  let g : ℝ → ℂ := resolventMultiplier (-Complex.I)
  let hg : Measurable g := resolventMultiplier_measurable (-Complex.I)
  let hgb : ∃ C : ℝ, ∀ r, ‖g r‖ ≤ C :=
    resolventMultiplier_bounded (z := -Complex.I) (by norm_num)
  let hk : ℝ → ℂ := fun r => (2 * Complex.I) * g r
  let hkb : ∃ C : ℝ, ∀ r, ‖hk r‖ ≤ C := by
    rcases hgb with ⟨C, hC⟩
    refine ⟨‖2 * Complex.I‖ * C, fun r => ?_⟩
    simp only [hk, norm_mul]
    exact mul_le_mul_of_nonneg_left (hC r) (by positivity)
  have hkm : Measurable hk := measurable_const.mul hg
  have hconst : ∃ C : ℝ, ∀ r : ℝ, ‖(1 : ℂ)‖ ≤ C :=
    ⟨1, fun _ => by norm_num⟩
  have hsubb : ∃ C : ℝ, ∀ r : ℝ, ‖(1 : ℂ) - hk r‖ ≤ C := by
    rcases hkb with ⟨C, hC⟩
    refine ⟨1 + C, fun r => ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add (by simp) (hC r))
  have hfun : ∀ r : ℝ, cayley r = (fun _ : ℝ => (1 : ℂ)) r - hk r := by
    intro r
    exact cayley_eq_one_sub_resolventMultiplier_minus_I r
  have hcalc : boundedIntegral μS cayley measurable_cayley
      (show ∃ C : ℝ, ∀ r, ‖cayley r‖ ≤ C from
        ⟨1, fun r => by simpa [cayley_norm r]⟩) =
      boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const hconst -
        boundedIntegral μS hk hkm hkb := by
    calc
      _ = boundedIntegral μS ((fun _ : ℝ => (1 : ℂ)) - hk)
          (measurable_const.sub hkm) hsubb := by
        refine _root_.QuantumMechanics.WOTSpectralMeasure.boundedIntegral_congr
          (μS := μS) (f := cayley) (g := (fun _ : ℝ => (1 : ℂ)) - hk)
          measurable_cayley (measurable_const.sub hkm) ?_ hsubb hfun
      _ = _ := _root_.QuantumMechanics.WOTSpectralMeasure.boundedIntegral_sub
        μS measurable_const hkm hconst hkb
  apply ContinuousLinearMap.ext
  intro x
  have hinv := maximalSpectralIntegral_resolvent_inverse_apply
    (μS := μS) (z := -Complex.I) (by norm_num) x
  have htopdom : (M.resolvent (-Complex.I)).domain = ⊤ := by
    rw [LinearPMap.resolvent, LinearPMap.inverse_domain]
    simpa [M] using
      (maximalSpectralIntegral_resolvent_range (μS := μS) (z := -Complex.I) (by norm_num))
  have hcont : Continuous (M.resolvent (-Complex.I)).toFun :=
    (LinearPMap.IsSelfAdjoint.mem_resolventSet_of_im_ne_zero hM
      (z := -Complex.I) (by norm_num)).2.2
  rw [hcalc]
  change (boundedIntegral μS (fun _ : ℝ => (1 : ℂ)) measurable_const hconst x -
      boundedIntegral μS hk hkm hkb x) = _
  rw [boundedIntegral_const]
  have hksmul := boundedIntegral_smul μS (2 * Complex.I) hg hgb
  rw [show boundedIntegral μS hk hkm hkb =
      (2 * Complex.I) • boundedIntegral μS g hg hgb by
        simpa [hk] using hksmul]
  simp only [ContinuousLinearMapWOT.smul_apply]
  simp only [ContinuousLinearMapWOT.one_apply, one_smul]
  simp only [cayleyContinuousLinearMap, sub_apply, smul_apply]
  change (1 : H →L[ℂ] H) x - (2 * Complex.I) • boundedIntegral μS g hg hgb x =
    ((1 : H →L[ℂ] H) - (2 * Complex.I) • topDomainToContinuousLinearMap
      (M.resolvent (-Complex.I)) htopdom hcont) x
  have htop_apply := topDomainToContinuousLinearMap_apply
    (M.resolvent (-Complex.I)) htopdom hcont x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
  rw [htop_apply]
  simpa [M, g] using hinv.symm

end QuantumMechanics.WOTSpectralMeasure

namespace OperatorAlgebra.NormalAffiliationBridge

variable {A H : Type*} [WStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (bridge : NormalOperatorAffiliationBridge (A := A) (H := H))

/-- The represented abstract Cayley unitary is the concrete Cayley transform of the maximal
self-adjoint operator reconstructed from the represented spectral measure. -/
theorem representation_canonicalCayleyUnitary_eq_cayleyContinuousLinearMap
    (T : NormalAffiliatedObservable A) :
    bridge.representation (NormalAffiliatedObservable.canonicalCayleyUnitary T : A) =
      cayleyContinuousLinearMap
        (bridge.toNormalAffiliationBridge.representedSelfAdjointOperator T)
        (bridge.toNormalAffiliationBridge.representedSelfAdjointOperator_isSelfAdjoint T) := by
  calc
    bridge.representation (NormalAffiliatedObservable.canonicalCayleyUnitary T : A) =
        (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
          (bridge.toNormalAffiliationBridge.representedSpectralMeasure T) cayley
          measurable_cayley
          (show ∃ C : ℝ, ∀ x, ‖cayley x‖ ≤ C from
            ⟨1, fun x => by simpa [cayley_norm x]⟩)).toCLM :=
      representation_canonicalCayleyUnitary_eq_boundedIntegral bridge T
    _ = _ := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_cayley_eq_cayleyContinuousLinearMap
      (bridge.toNormalAffiliationBridge.representedSpectralMeasure T)

end OperatorAlgebra.NormalAffiliationBridge

end
