/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Spectral.CayleySpectralData
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Core.EssentialSelfAdjointCriteria
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Dynamics.NegativeStoneAPI
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Core.RealAnalytic
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Dynamics.StoneAPI

/-!
# The essential-self-adjoint core handoff

This module is the small public boundary between model-specific analysis and the general
unbounded spectral theorem.  A model supplies a `LinearPMap` and proves that it is essentially
self-adjoint.  `EssentialSelfAdjointCore` then exposes, canonically:

* the graph closure;
* its self-adjointness and uniqueness among self-adjoint extensions;
* the Cayley-constructed real spectral measure;
* the exact square-moment domain theorem;
* the unitary group and its generator-domain API.

No spectral theorem is assumed in this package.  The spectral data are obtained from the proved
Cayley construction in `CayleySpectralData.lean`.  The package is intentionally independent of
any oscillator or Hermite-function facts.
-/

@[expose] public section

noncomputable section

open Set
open scoped InnerProductSpace

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A densely-defined model operator together with the analytic fact needed by the Cayley route.

The operator remains a `LinearPMap`: its domain is explicit and the closure is the canonical graph
closure supplied by the partial-operator infrastructure.  This keeps model files responsible
only for their actual analysis, while all spectral consequences are shared. -/
structure EssentialSelfAdjointCore where
  operator : H →ₗ.[ℂ] H
  essentiallySelfAdjoint : LinearPMap.IsEssentiallySelfAdjoint operator

/-- Build the core package from a total real-eigenvector criterion.

The model only supplies the symmetry and density of its partial operator, domain membership and
the eigenvalue equation on a total family, and density of that family's span.  The non-real
deficiency parameters `± I` are discharged automatically because all supplied eigenvalues are
real. -/
noncomputable def EssentialSelfAdjointCore.ofDenseRealEigenvectors
    {T : H →ₗ.[ℂ] H} (hT : T.IsSymmetric) (hdense : T.HasDenseDomain)
    {ι : Type*} (v : ι → H) (eigenvalue : ι → ℝ)
    (hv : ∀ i, v i ∈ T.domain)
    (heigen : ∀ i, T ⟨v i, hv i⟩ = (eigenvalue i : ℂ) • v i)
    (hspan : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    EssentialSelfAdjointCore (H := H) := by
  refine { operator := T, essentiallySelfAdjoint := ?_ }
  apply LinearPMap.isEssentiallySelfAdjoint_of_dense_eigenvectors hT hdense v eigenvalue hv heigen
  · intro i
    constructor
    · intro h
      have him := congrArg Complex.im h
      simp at him
    · intro h
      have him := congrArg Complex.im h
      simp at him
  · exact hspan

/-- Build the core package from the stronger exact-domain Hilbert-basis criterion.

This is the shortest model-facing entry point when the operator is defined on the algebraic span
of a Hilbert basis of eigenvectors.  The criterion proves symmetry, density, and vanishing
deficiency indices internally; the model supplies only the domain equality and eigenvalue
equations. -/
noncomputable def EssentialSelfAdjointCore.ofHilbertBasisEigenvectors
    {ι : Type*} (e : HilbertBasis ι ℂ H) (T : H →ₗ.[ℂ] H) (eigenvalue : ι → ℝ)
    (hdom : T.domain = Submodule.span ℂ (Set.range e))
    (heigen : ∀ i, T ⟨e i, hdom ▸ Submodule.subset_span ⟨i, rfl⟩⟩ =
      (eigenvalue i : ℂ) • e i) :
    EssentialSelfAdjointCore (H := H) :=
  { operator := T
    essentiallySelfAdjoint :=
      OperatorAlgebra.isEssentiallySelfAdjoint_of_hilbertBasis_eigenvectors
        e T eigenvalue hdom heigen }

namespace EssentialSelfAdjointCore

variable (C : EssentialSelfAdjointCore (H := H))

include C

/-- The canonical self-adjoint closure of the model operator. -/
abbrev closure : H →ₗ.[ℂ] H := C.operator.closure

/-- The closure of an essentially self-adjoint core is self-adjoint. -/
lemma closure_isSelfAdjoint : IsSelfAdjoint C.closure :=
  C.essentiallySelfAdjoint

/-- The canonical closure is closed. -/
lemma closure_isClosed : C.closure.IsClosed :=
  C.closure_isSelfAdjoint.isClosed

/-- The core is contained in its canonical closure. -/
lemma le_closure : C.operator ≤ C.closure :=
  C.operator.le_closure

/-- Any self-adjoint extension of the core is the canonical closure. -/
lemma unique_selfAdjoint_extension {S : H →ₗ.[ℂ] H}
    (hCS : C.operator ≤ S) (hS : IsSelfAdjoint S) : S = C.closure :=
  LinearPMap.IsEssentiallySelfAdjoint.unique_self_adjoint_extension
    C.essentiallySelfAdjoint hCS hS

/-- The real spectral measure canonically attached to the closure by Cayley transport. -/
noncomputable abbrev spectralMeasure : QuantumMechanics.WOTSpectralMeasure ℝ H :=
  cayleyRealSpectralMeasure C.closure C.closure_isSelfAdjoint

/-- The full domain-aware unbounded spectral theorem for the closure. -/
noncomputable abbrev spectralTheorem :
    DomainAwareSelfAdjointSpectralTheorem C.closure C.spectralMeasure :=
  unboundedSpectralTheorem C.closure C.closure_isSelfAdjoint

/-- The operator is exactly the maximal square-moment spectral integral. -/
lemma maximalSpectralIntegral_eq :
    QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral C.spectralMeasure = C.closure :=
  C.spectralTheorem.maximal_eq

/-- The closure domain is exactly the finite-second-moment domain of the spectral measure. -/
lemma domain_eq_squareMoment :
    C.closure.domain = spectralSquareMomentDomain C.spectralMeasure :=
  C.spectralTheorem.domain_eq_squareMoment

/-- The core's spectral data in the package used by affiliation bridges. -/
noncomputable def spectralData : EssentialSelfAdjointSpectralData C.operator where
  essentiallySelfAdjoint := C.essentiallySelfAdjoint
  spectralMeasure := C.spectralMeasure
  spectralTheorem := C.spectralTheorem

/-- The unitary group generated by the closure. -/
noncomputable abbrev expUnitaryGroup :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup H :=
  C.spectralTheorem.expUnitaryGroup

/-- The conventional quantum-dynamics group generated by the closure, with value
`e⁻ⁱᵗᶜˡᵒˢᵘʳᵉ`. -/
noncomputable abbrev negativeExpUnitaryGroup :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup H :=
  C.spectralTheorem.negativeExpUnitaryGroup

/-- At time zero, differentiability of the unitary orbit is equivalent to membership in the
closure domain, and the derivative is `Complex.I • closure x`. -/
theorem hasDerivAt_zero_iff (x y : H) :
    HasDerivAt (fun t : ℝ => C.expUnitaryGroup t x) y 0 ↔
      ∃ hx : x ∈ C.closure.domain, y = Complex.I • C.closure ⟨x, hx⟩ :=
  C.spectralTheorem.expUnitaryGroup_hasDerivAt_zero_iff x y

/-- Membership in the closure domain can be tested by differentiability of the orbit at any
time, not only at zero. -/
theorem mem_domain_iff_hasDerivAt (x : H) (s : ℝ) :
    x ∈ C.closure.domain ↔
      ∃ y : H, HasDerivAt (fun t : ℝ => C.expUnitaryGroup t x) y s :=
  C.spectralTheorem.mem_domain_iff_expUnitaryGroup_hasDerivAt x s

/-- The derivative of an orbit at any time is the evolved generator vector. -/
theorem hasDerivAt_iff (x y : H) (s : ℝ) :
    HasDerivAt (fun t : ℝ => C.expUnitaryGroup t x) y s ↔
      ∃ hx : x ∈ C.closure.domain,
        y = C.expUnitaryGroup s (Complex.I • C.closure ⟨x, hx⟩) :=
  C.spectralTheorem.expUnitaryGroup_hasDerivAt_iff x y s

/-- At zero, the conventional `e⁻ⁱᵗᶜˡᵒˢᵘʳᵉ` orbit is differentiable exactly on the closure
domain, with derivative `-i • closure x`. -/
theorem negative_hasDerivAt_zero_iff (x y : H) :
    HasDerivAt (fun t : ℝ => C.negativeExpUnitaryGroup t x) y 0 ↔
      ∃ hx : x ∈ C.closure.domain, y = -Complex.I • C.closure ⟨x, hx⟩ :=
  C.spectralTheorem.negativeExpUnitaryGroup_hasDerivAt_zero_iff x y

end EssentialSelfAdjointCore

end OperatorAlgebra
