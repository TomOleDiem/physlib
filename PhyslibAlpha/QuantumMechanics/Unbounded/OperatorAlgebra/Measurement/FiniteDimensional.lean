/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Measurement.FinitePOVM
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Measurement.POVM
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.HilbertSpace

/-! # Finite-dimensional measurements

The general finite-outcome measurement interface specializes directly to bounded operators on a
finite-dimensional Hilbert space. No basis is chosen: matrix coordinates are an optional later
layer. The measurable-space PVM/POVM conversion is inherited from the general measurement API.
-/

@[expose] public section

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- A finite-outcome POVM on a finite-dimensional Hilbert space. -/
abbrev FiniteDimensionalPOVM (X : Type*) [Fintype X] := FinitePOVM (B(H)) X

/-- A finite-dimensional sharp measurement is a general PVM on `B(H)` over a finite measurable
space. For finite outcomes, use `FinitePOVM` together with projection-valued effects. -/
abbrev FiniteDimensionalPVM (X : Type*) [MeasurableSpace X] := PVM X (B(H))

end OperatorAlgebra
