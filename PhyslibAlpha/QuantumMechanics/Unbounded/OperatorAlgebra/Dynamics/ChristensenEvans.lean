/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Dynamics.ChristensenEvans.P1
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Dynamics.ChristensenEvans.P2

/-!
# Christensen-Evans data for bounded irreversible dynamics

Aggregator for the two-part split (`ChristensenEvans/{Part1,Part2}.lean`) of this file, kept
under the 1500-line style limit. See those files' module docs, in order, for the full overview:
the C*-algebraic Christensen-Evans layer underneath the finite-noise Lindblad/Kraus presentation,
and the bounded quantum dynamical semigroup generator data built from it.
-/
