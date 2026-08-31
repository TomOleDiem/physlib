/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Spec.Cayley
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Spec.CayleySpectralData

/-!
# Canonical Cayley spectral certificates

`Cayley.lean` defines the certificate-shaped compatibility API, while
`CayleySpectralData.lean` contains the actual bounded-unitary construction and the inverse-Cayley
reconstruction proof.  This module joins those two layers: a self-adjoint partial operator now
has a canonical `CayleySpectralCertificate`, with no extra witness fields for clients to fill.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The canonical Cayley spectral certificate for a self-adjoint `LinearPMap`.

The bounded component is the c⋆-constructed spectral measure of the Cayley unitary, and the
reconstruction component is the proved inverse-Cayley moment theorem. -/
noncomputable def CayleySpectralCertificate.ofSelfAdjoint
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) : CayleySpectralCertificate T hT where
  bounded := cayleyBoundedUnitarySpectralData T hT
  reconstruction := cayleyRealSpectralMeasure_isWeakSpectralResolution T hT

@[simp]
lemma CayleySpectralCertificate.ofSelfAdjoint_bounded
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    (CayleySpectralCertificate.ofSelfAdjoint T hT).bounded =
      cayleyBoundedUnitarySpectralData T hT := rfl

lemma CayleySpectralCertificate.ofSelfAdjoint_realSpectralMeasure
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    (CayleySpectralCertificate.ofSelfAdjoint T hT).bounded.realSpectralMeasure =
      cayleyRealSpectralMeasure T hT := rfl

end OperatorAlgebra

end
