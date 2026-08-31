/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.CayleySpectralData.P1
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Spec.CayleySpectralData.P2

/-!
# Bounded spectral data for a Cayley transform

Aggregator for the two-part split (`CayleySpectralData/{P1,P2}.lean`) of this file, kept under
the 1500-line style limit. See those files' module docs for the full overview: the adapter
between the spectrum-valued bounded-unitary construction and the ambient `ℂ`-valued certificate
consumed by the Cayley transform.
-/
