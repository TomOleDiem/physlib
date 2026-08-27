/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.StoneAPI

/-!
# The `e⁻ⁱᵗᵀ` Stone convention

The spectral integral in `StoneAPI` uses the mathematically convenient convention
`e⁺ⁱᵗᵀ`.  Quantum dynamics is usually written `e⁻ⁱᵗᵀ`.  This file provides the latter as
the same strongly continuous unitary group with time reversed.  Consequently no second spectral
construction is needed, and the generator sign is exposed explicitly.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology InnerProductSpace Function

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

namespace DomainAwareSelfAdjointSpectralTheorem

variable (D : DomainAwareSelfAdjointSpectralTheorem T μS)

include D

/-- The quantum-dynamics convention `e⁻ⁱᵗᵀ`, obtained by reversing the parameter of the
canonical `e⁺ⁱᵗᵀ` group. -/
noncomputable def negativeExpUnitaryGroup :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup H where
  toFun t := D.expUnitaryGroup (-t)
  mem_unitary t := D.expUnitaryGroup.mem_unitary (-t)
  map_zero := by simp
  map_add := by
    intro t s
    rw [show -(t + s) = -t + -s by ring]
    exact D.expUnitaryGroup_add (-t) (-s)
  strong_continuous := by
    intro x
    exact (D.expUnitaryGroup_continuous_apply x).comp continuous_neg

@[simp]
lemma negativeExpUnitaryGroup_zero : D.negativeExpUnitaryGroup 0 = 1 := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.zero _

lemma negativeExpUnitaryGroup_add (t s : ℝ) :
    D.negativeExpUnitaryGroup (t + s) =
      D.negativeExpUnitaryGroup t * D.negativeExpUnitaryGroup s := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.add _ t s

lemma negativeExpUnitaryGroup_continuous_apply (x : H) :
    Continuous (fun t => D.negativeExpUnitaryGroup t x) := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.continuous_apply _ x

lemma negativeExpUnitaryGroup_hasDerivAt_zero
    (x : T.domain) :
    HasDerivAt (fun t : ℝ => D.negativeExpUnitaryGroup t (x : H))
      (-Complex.I • T x) 0 := by
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) 0 :=
    hasDerivAt_neg' 0
  have houter : HasDerivAt (fun t : ℝ => D.expUnitaryGroup t (x : H))
      (Complex.I • T x) (-0) := by
    simpa using D.expUnitaryGroup_hasDerivAt_zero x
  have h := houter.scomp 0 hneg
  convert h using 1 <;> simp [negativeExpUnitaryGroup, Function.comp_def, smul_smul]

/- The reverse implication is included in the public theorem below.  Keeping it separate from the
positive-convention theorem makes the sign conversion visible and prevents a silent convention
change in downstream dynamics code. -/
theorem negativeExpUnitaryGroup_hasDerivAt_zero_iff (x : H) (y : H) :
    HasDerivAt (fun t : ℝ => D.negativeExpUnitaryGroup t x) y 0 ↔
      ∃ hx : x ∈ T.domain, y = -Complex.I • T ⟨x, hx⟩ := by
  constructor
  · intro hy
    have hneg : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) 0 :=
      hasDerivAt_neg' 0
    have houter : HasDerivAt (fun t : ℝ => D.negativeExpUnitaryGroup t x) y (-0) := by
      simpa using hy
    have h := houter.scomp 0 hneg
    have hpos : HasDerivAt (fun t : ℝ => D.expUnitaryGroup t x) (-y) 0 := by
      convert h using 1 <;> simp [negativeExpUnitaryGroup, Function.comp_def, smul_smul]
    rcases (D.expUnitaryGroup_hasDerivAt_zero_iff x (-y)).mp hpos with ⟨hx, hxy⟩
    refine ⟨hx, ?_⟩
    calc
      y = -(-y) := by simp
      _ = -(Complex.I • T ⟨x, hx⟩) := congrArg Neg.neg hxy
      _ = -Complex.I • T ⟨x, hx⟩ := by rw [neg_smul]
  · rintro ⟨hx, rfl⟩
    exact D.negativeExpUnitaryGroup_hasDerivAt_zero ⟨x, hx⟩

/-- The quantum-dynamics group satisfies the same star/inverse law as the canonical group, with
the sign inherited from the time reversal. -/
theorem negativeExpUnitaryGroup_star (t : ℝ) :
    star (D.negativeExpUnitaryGroup t) = D.negativeExpUnitaryGroup (-t) := by
  have h := D.expUnitaryGroup_star (-t)
  simpa [negativeExpUnitaryGroup, neg_neg] using h

end DomainAwareSelfAdjointSpectralTheorem

end OperatorAlgebra

end
