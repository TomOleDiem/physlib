/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.MeasureTheory.BoundedMeasurable
public import PhyslibAlpha.ProbTheory.OrderUnit.Lattice
public import PhyslibAlpha.ProbTheory.Measurement.EffectValuedMeasure

/-!
# Classical systems

## i. Overview

A classical system with outcomes in a measurable space `Ω` has as observables the bounded
measurable functions on `Ω`, ordered pointwise, with the constant function `1` as order unit. For a
mechanical system, `Ω` is its phase space. Asking whether the outcome lies in a measurable set `A`
is the effect `1_A`; these effects form the effect-valued measure of the outcome.

## ii. Key results

- `ClassicalSystem Ω` : the classical system with outcomes in `Ω`, an order-unit lattice.
- `ClassicalSystem.indicatorEffect` : the effect testing whether the outcome lies in a set.
- `ClassicalSystem.outcomeMeasurement` : the effect-valued measure of the outcome.

## iii. Table of contents

- A. The order-unit space
- B. Indicator effects

-/

@[expose] public section

/-!

## A. The order-unit space

-/

variable (Ω : Type*) [MeasurableSpace Ω] in
/-- The classical system with outcomes in `Ω`: bounded measurable observables. -/
abbrev ClassicalSystem : Type _ := BoundedMeasurable Ω

namespace ClassicalSystem

open BoundedMeasurable

variable {Ω : Type*} [MeasurableSpace Ω]

instance : OrderUnitSpace (ClassicalSystem Ω) where
  one_nonneg := le_def.2 fun _ => by simp
  exists_nsmul_one_le f := by
    obtain ⟨C, hC⟩ := f.exists_bound
    exact ⟨⌈C⌉₊, le_def.2 fun x => by
      simpa using (le_abs_self _).trans ((hC x).trans (Nat.le_ceil C))⟩

instance : ArchimedeanOrderUnitSpace (ClassicalSystem Ω) where
  le_zero_of_forall_pos_smul_one_le f h := le_def.2 fun x =>
    le_of_forall_pos_le_add fun ε hε => by simpa using le_def.1 (h ε hε) x

instance : OrderUnitLattice (ClassicalSystem Ω) :=
  { (inferInstance : ArchimedeanOrderUnitSpace (ClassicalSystem Ω)),
    (inferInstance : Lattice (ClassicalSystem Ω)) with }

end ClassicalSystem

namespace ClassicalSystem

open BoundedMeasurable

variable {Ω : Type*} [MeasurableSpace Ω]

/-!

## B. Indicator effects

-/

/-- The effect testing whether the outcome lies in `s`. -/
noncomputable def indicatorEffect (s : Set Ω) (hs : MeasurableSet s) :
    Effect (ClassicalSystem Ω) :=
  ⟨indicator s hs, indicator_nonneg s hs, indicator_le_one s hs⟩

@[simp] lemma coe_indicatorEffect (s : Set Ω) (hs : MeasurableSet s) :
    (indicatorEffect s hs : ClassicalSystem Ω) = indicator s hs := rfl

/-- The effect-valued measure of the outcome: the set `A` is the effect `1_A`. -/
noncomputable def outcomeMeasurement : EffectValuedMeasure Ω (ClassicalSystem Ω) where
  toFun := indicatorEffect
  map_empty' := Subtype.ext (ext fun x => by simp)
  map_univ' := Subtype.ext (ext fun x => by simp)
  countably_additive' _ hs hd := isLUB_sum_indicator hs hd

end ClassicalSystem
