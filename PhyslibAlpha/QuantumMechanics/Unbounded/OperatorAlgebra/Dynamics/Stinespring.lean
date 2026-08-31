/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Dynamics.Stinespring.Core
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Dynamics.Stinespring.Canonical
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Dynamics.Stinespring.Converse

/-!
# The tensor-product core of Stinespring's construction

Aggregator for the three-part split (`Stinespring/{Core,Canonical,ChristensenEvans}.lean`) of
this file, kept under the 1500-line style limit. See those files' module docs, in order, for the
full result-by-result overview: the tensor-product GNS/Kolmogorov factorization of canonical and
Evans-Lewis positive-operator kernels, and the resulting Christensen-Evans converse for `B(H)`.
-/
