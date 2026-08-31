/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.Operators.SpectralTheory.WeakSpectralMeasure.A
public import PhyslibAlpha.QuantumMechanics.Unbounded.Operators.SpectralTheory.WeakSpectralMeasure.B

/-!
# Weak-operator spectral measures

Aggregator for the two-part split (`WeakSpectralMeasure/{P1,P2}.lean`) of this file, kept under
the 1500-line style limit. See those files' module docs, in order, for the full overview: the
representation-level (weak-operator-topology) replacement for the norm-valued `SpectralMeasure`,
needed because a family of orthogonal projections is generally sigma-additive in the weak
operator topology, not in operator norm, in infinite dimension.
-/
