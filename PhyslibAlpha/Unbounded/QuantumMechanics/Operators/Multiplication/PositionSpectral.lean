/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Operators.Position
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.Multiplication.Spectral

/-!
# The Schwartz core of position

The position module defines the maximal multiplication operator.  This file records the reusable
analytic fact that its natural Schwartz restriction has the same closure, and consequently has
the same domain-aware spectral theorem.  It is the position-side analogue of
`MomentumSpectral.lean`; no oscillator-specific facts enter.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory
open scoped ComplexOrder

namespace QuantumMechanics

open Space SpaceDHilbertSpace SchwartzMap SchwartzSubmodule

variable {d : ℕ}

/-- The complex-valued position coordinate used by the Schwartz multiplication restriction. -/
def positionCoordinateComplex (i : Fin d) : Space d → ℂ :=
  fun x => (Space.coord i x : ℂ)

lemma positionCoordinateComplex_hasTemperateGrowth (i : Fin d) :
    HasTemperateGrowth (positionCoordinateComplex i) := by
  apply Function.Complex.hasTemperateGrowth_ofReal.comp
  have heq : Space.coord i = ⇑(Space.coordCLM i) := by
    funext x
    exact (Space.coordCLM_apply i x).symm
  rw [heq]
  exact (Space.coordCLM i).hasTemperateGrowth

/-- The position operator restricted to Schwartz vectors. -/
def schwartzPositionOperator (i : Fin d) :
    SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d :=
  schwartzMulOperator
    (f := positionCoordinateComplex i)
    (positionCoordinateComplex_hasTemperateGrowth i)

lemma positionOperator_eq_realMultiplicationOperator (i : Fin d) :
    positionOperator (μ := volume) i =
      realMultiplicationOperator (μ := volume) (Space.coord i) := by
  apply LinearPMap.ext
  · rfl
  · intro x hx hy
    rfl

lemma schwartzPositionOperator_closure_eq_positionOperator
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    (schwartzPositionOperator i).closure = positionOperator (μ := volume) i := by
  rw [positionOperator_eq_realMultiplicationOperator i]
  change (schwartzMulOperator
      (f := positionCoordinateComplex i)
      (positionCoordinateComplex_hasTemperateGrowth i)).closure = _
  exact schwartzMulOperator_closure_eq_mulOperator
    (positionCoordinateComplex_hasTemperateGrowth i)

lemma schwartzPositionOperator_isEssentiallySelfAdjoint
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    (schwartzPositionOperator i).IsEssentiallySelfAdjoint := by
  change IsSelfAdjoint (schwartzPositionOperator i).closure
  rw [schwartzPositionOperator_closure_eq_positionOperator i]
  exact positionOperator_isSelfAdjoint volume i

/-- Full spectral data for the maximal position operator itself. -/
def positionOperator_spectralData
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    OperatorAlgebra.EssentialSelfAdjointSpectralData (positionOperator (μ := volume) i) := by
  rw [positionOperator_eq_realMultiplicationOperator i]
  exact realMultiplicationOperator_spectralData (μ := volume) (by
    have heq : Space.coord i = ⇑(Space.coordCLM i) := by
      funext x
      exact (Space.coordCLM_apply i x).symm
    rw [heq]
    exact (Space.coordCLM i).continuous.measurable)

/-- Full spectral data for the Schwartz position restriction. -/
def schwartzPositionOperator_spectralData
    [IsFiniteMeasureOnCompacts (volume : Measure (Space d))] (i : Fin d) :
    OperatorAlgebra.EssentialSelfAdjointSpectralData (schwartzPositionOperator i) where
  essentiallySelfAdjoint := schwartzPositionOperator_isEssentiallySelfAdjoint i
  spectralMeasure := multiplicationSpectralMeasure (μ := volume) (Space.coord i)
    (by
      have heq : Space.coord i = ⇑(Space.coordCLM i) := by
        funext x
        exact (Space.coordCLM_apply i x).symm
      rw [heq]
      exact (Space.coordCLM i).continuous.measurable)
  spectralTheorem := by
    rw [schwartzPositionOperator_closure_eq_positionOperator i,
      positionOperator_eq_realMultiplicationOperator i]
    exact realMultiplicationOperator_domainAwareSelfAdjointSpectralTheorem
      (μ := volume) (by
        have heq : Space.coord i = ⇑(Space.coordCLM i) := by
          funext x
          exact (Space.coordCLM_apply i x).symm
        rw [heq]
        exact (Space.coordCLM i).continuous.measurable)

end QuantumMechanics

end
