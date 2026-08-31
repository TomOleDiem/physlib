/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Core.AnalyticVector.Basic
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Core.AnalyticVector.Local
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Core.AnalyticVector.Nelson

/-!
# Analytic vectors for an unbounded operator

Aggregator for the three-part split (`AnalyticVector/{Basic,Local,Nelson}.lean`) of this file,
kept under the 1500-line style limit. See those files' module docs, in order, for the full
citation list and result-by-result overview: Nelson's analytic-vector essential-self-adjointness
theorem (Reed-Simon Vol. II, Theorem X.39), proved here as a genuine checked Lean proof.
-/
