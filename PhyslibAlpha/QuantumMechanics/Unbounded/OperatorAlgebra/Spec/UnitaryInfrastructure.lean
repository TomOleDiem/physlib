/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.UnitaryInfrastructure.P1
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.UnitaryInfrastructure.P2

/-!
# Infrastructure for the bounded-unitary spectral theorem

Aggregator for the two-part split (`UnitaryInfrastructure/{P1,P2}.lean`) of this file, kept under
the 1500-line style limit. See those files' module docs, in order, for the full overview: the
complete bounded-normal spectral-measure construction used by the Cayley adapter, culminating in
`cfcSpectralMeasure`.
-/
