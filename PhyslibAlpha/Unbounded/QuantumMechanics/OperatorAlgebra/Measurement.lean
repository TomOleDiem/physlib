/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.FinitePOVM
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.PVM
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.NormalPVM
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.NormalPOVM
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.POVM
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.FiniteDimensional

/-! # Quantum measurements

This umbrella owns the general measurable-space PVM/POVM interfaces, their normal variants, and
the finite-outcome specialization. State objects and state-dependent statistical identities live
under `OperatorAlgebra.States`.
-/
