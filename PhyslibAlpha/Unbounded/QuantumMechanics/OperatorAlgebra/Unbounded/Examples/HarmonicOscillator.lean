/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Core.RealAnalytic
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Spectral.CayleySpectralData
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Core.ClosureAPI
public import PhyslibAlpha.Unbounded.QuantumMechanics.HarmonicOscillator.OneDimension.PlancherelBridge
public import Physlib.QuantumMechanics.HarmonicOscillator.OneDimension.TISE
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The harmonic-oscillator Hamiltonian is essentially self-adjoint on its eigenbasis domain

This file assembles a genuine `LinearPMap` on the one-dimensional Hilbert space
`QuantumMechanics.OneDimension.HilbertSpace` (`= MeasureTheory.Lp ℂ 2`) whose domain is exactly
the algebraic span of the harmonic-oscillator eigenfunctions, and whose action on each
eigenfunction is multiplication by the corresponding physical eigenvalue. Essential
self-adjointness of this `LinearPMap` follows directly from
`OperatorAlgebra.isEssentiallySelfAdjoint_of_hilbertBasis_eigenvectors`
(`Physlib/QuantumMechanics/OperatorAlgebra/Unbounded/RealAnalytic.lean`), once the eigenfunctions
are packaged as a `HilbertBasis`.

## Main definitions/results

* `QuantumMechanics.OneDimension.HarmonicOscillator.eigenbasis` : the harmonic-oscillator
  eigenfunctions, packaged as a `HilbertBasis ℕ ℂ HilbertSpace` — built from orthonormality
  (`eigenfunction_orthonormal`) and the unconditional completeness statement
  `eigenfunction_completeness'`.
* `OperatorAlgebra.Unbounded.Example.hamiltonianPMap` : the `LinearPMap` with domain the
  algebraic span of `eigenbasis`, acting on each basis vector by its physical eigenvalue
  `Q.eigenValue n`.
* `OperatorAlgebra.Unbounded.Example.hamiltonianPMap_isEssentiallySelfAdjoint` : **the main
result** — `hamiltonianPMap` is essentially self-adjoint, with no proof holes.

## Scope note

`hamiltonianPMap` is defined directly from the eigenbasis (domain = span of eigenvectors, action
= eigenvalue multiplication), *not* derived as a restriction of the differential Schrödinger
operator or of a `LinearPMap` built from `positionOperatorSchwartz`/`momentumOperatorSchwartz`.
It is a legitimate, physically meaningful witness — "the harmonic oscillator has an essentially
self-adjoint restriction on its natural eigenbasis domain" — but connecting it back to those
differential/Schwartz-space operators as a literal restriction is not attempted here.
-/

@[expose] public section

noncomputable section

namespace QuantumMechanics

namespace OneDimension
namespace HarmonicOscillator

open _root_.QuantumMechanics.OneDimension.HilbertSpace

variable (Q : HarmonicOscillator)

/-- The harmonic-oscillator eigenfunctions, packaged as a `HilbertBasis` of
`QuantumMechanics.OneDimension.HilbertSpace`. This uses orthonormality
(`eigenfunction_orthonormal`) together with the unconditional density of their span
(`eigenfunction_completeness'`), bridged to the trivial-orthogonal-complement form via
`Submodule.topologicalClosure_eq_top_iff`. -/
def eigenbasis : HilbertBasis ℕ ℂ HilbertSpace :=
  HilbertBasis.mkOfOrthogonalEqBot Q.eigenfunction_orthonormal
    (Submodule.topologicalClosure_eq_top_iff.mp Q.eigenfunction_completeness')

@[simp]
lemma eigenbasis_apply (n : ℕ) : Q.eigenbasis n = HilbertSpace.mk (Q.eigenfunction_memHS n) := by
  simp [eigenbasis]

end HarmonicOscillator
end OneDimension
end QuantumMechanics

namespace OperatorAlgebra.Unbounded.Example

open QuantumMechanics OneDimension HarmonicOscillator

variable (Q : HarmonicOscillator)

/-- The harmonic-oscillator eigenfunctions are linearly independent (a corollary of
orthonormality), needed to view their span as spanned by a genuine `Basis`. -/
lemma eigenbasis_linearIndependent :
    LinearIndependent ℂ (⇑(Q.eigenbasis)) :=
  Q.eigenbasis.orthonormal.linearIndependent

/-- The linear map on the algebraic span of the eigenbasis sending each basis vector `eigenbasis
n` to `eigenValue n • eigenbasis n`, built from `Basis.constr` on the `Basis.span` of the
eigenbasis. -/
def hamiltonianLinearMap :
    (Submodule.span ℂ (Set.range (⇑(Q.eigenbasis)))) →ₗ[ℂ] HilbertSpace :=
  Module.Basis.constr (Module.Basis.span (eigenbasis_linearIndependent Q)) ℂ
    (fun n => (Q.eigenValue n : ℂ) • Q.eigenbasis n)

/-- **The harmonic-oscillator Hamiltonian on its natural eigenbasis domain.** A genuine
`LinearPMap` on `HilbertSpace` whose domain is exactly the algebraic span of the
harmonic-oscillator eigenfunctions and whose action on each eigenfunction is multiplication by
its physical eigenvalue `Q.eigenValue n`. -/
def hamiltonianPMap : HilbertSpace →ₗ.[ℂ] HilbertSpace where
  domain := Submodule.span ℂ (Set.range (⇑(Q.eigenbasis)))
  toFun := hamiltonianLinearMap Q

lemma hamiltonianPMap_domain :
    (hamiltonianPMap Q).domain = Submodule.span ℂ (Set.range (⇑(Q.eigenbasis))) := rfl

lemma hamiltonianPMap_apply_eigenbasis (n : ℕ)
    (hn : Q.eigenbasis n ∈ Submodule.span ℂ (Set.range (⇑(Q.eigenbasis))) :=
      Submodule.subset_span ⟨n, rfl⟩) :
    (hamiltonianPMap Q) ⟨Q.eigenbasis n, hn⟩ = (Q.eigenValue n : ℂ) • Q.eigenbasis n := by
  have heq : (⟨Q.eigenbasis n, hn⟩ : Submodule.span ℂ (Set.range (⇑(Q.eigenbasis))))
      = (Module.Basis.span (eigenbasis_linearIndependent Q) n :
          (Submodule.span ℂ (Set.range (⇑(Q.eigenbasis))))) := by
    apply Subtype.ext
    rw [Module.Basis.coe_span_apply]
  change hamiltonianLinearMap Q
      (⟨Q.eigenbasis n, hn⟩ : Submodule.span ℂ (Set.range (⇑(Q.eigenbasis)))) = _
  rw [heq]
  unfold hamiltonianLinearMap
  rw [Module.Basis.constr_basis]

/-- The eigenbasis-domain Hamiltonian packaged for the closure/Cayley API. -/
noncomputable def hamiltonianCore :
    OperatorAlgebra.EssentialSelfAdjointCore (H := HilbertSpace) :=
  OperatorAlgebra.EssentialSelfAdjointCore.ofHilbertBasisEigenvectors
    (Q.eigenbasis) (hamiltonianPMap Q) (Q.eigenValue)
    (hamiltonianPMap_domain Q) (fun n => hamiltonianPMap_apply_eigenbasis Q n)

/-- **Main result.** The harmonic-oscillator Hamiltonian, viewed as the `LinearPMap` on
`HilbertSpace` whose domain is exactly the algebraic span of the eigenfunctions and whose action
on the `n`-th eigenfunction is `eigenValue n • eigenfunction n`, is essentially self-adjoint.
This is the Reed–Simon-style "eigenbasis density" criterion
(`OperatorAlgebra.isEssentiallySelfAdjoint_of_hilbertBasis_eigenvectors`), applied to the
harmonic-oscillator eigenbasis. -/
theorem hamiltonianPMap_isEssentiallySelfAdjoint :
    (hamiltonianPMap Q).IsEssentiallySelfAdjoint :=
  (hamiltonianCore Q).essentiallySelfAdjoint


/-! ## Spectral data and dynamics of the witness operator

The Cayley/PVM infrastructure now turns this essential-self-adjointness certificate into the
full domain-aware spectral package.  The measure is canonical for the self-adjoint closure; no
choice of eigenfunction expansion is made here. -/

noncomputable def hamiltonianSpectralData :
    OperatorAlgebra.EssentialSelfAdjointSpectralData (hamiltonianPMap Q) where
  essentiallySelfAdjoint := hamiltonianPMap_isEssentiallySelfAdjoint Q
  spectralMeasure :=
    OperatorAlgebra.cayleyRealSpectralMeasure (hamiltonianPMap Q).closure
      (hamiltonianPMap_isEssentiallySelfAdjoint Q)
  spectralTheorem :=
    OperatorAlgebra.cayleyDomainAwareSelfAdjointSpectralTheorem (hamiltonianPMap Q).closure
      (hamiltonianPMap_isEssentiallySelfAdjoint Q)

theorem hamiltonianDomainAwareSpectralTheorem :
    OperatorAlgebra.DomainAwareSelfAdjointSpectralTheorem
      (hamiltonianPMap Q).closure (hamiltonianSpectralData Q).spectralMeasure := by
  exact OperatorAlgebra.cayleyDomainAwareSelfAdjointSpectralTheorem
    (hamiltonianPMap Q).closure (hamiltonianPMap_isEssentiallySelfAdjoint Q)

noncomputable def hamiltonianUnitaryGroup :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup HilbertSpace :=
  (hamiltonianDomainAwareSpectralTheorem Q).expUnitaryGroup

/-- The canonical closure selected by the essential-self-adjoint core package is self-adjoint. -/
theorem hamiltonianClosure_isSelfAdjoint :
    IsSelfAdjoint (hamiltonianPMap Q).closure :=
  (hamiltonianCore Q).closure_isSelfAdjoint

/-- The closure is the maximal square-moment spectral integral of its Cayley spectral measure. -/
theorem hamiltonianMaximalSpectralIntegral_eq :
    QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
        ((hamiltonianCore Q).spectralMeasure) = (hamiltonianPMap Q).closure :=
  (hamiltonianCore Q).maximalSpectralIntegral_eq

/-- The closure domain is exactly the finite-second-moment domain of the oscillator's spectral
measure. -/
theorem hamiltonianDomain_eq_squareMoment :
    (hamiltonianPMap Q).closure.domain =
      OperatorAlgebra.spectralSquareMomentDomain (hamiltonianCore Q).spectralMeasure :=
  (hamiltonianCore Q).domain_eq_squareMoment

theorem hamiltonianUnitaryGroup_zero :
    hamiltonianUnitaryGroup Q 0 = 1 := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.zero _

theorem hamiltonianUnitaryGroup_add (t s : ℝ) :
    hamiltonianUnitaryGroup Q (t + s) =
      hamiltonianUnitaryGroup Q t * hamiltonianUnitaryGroup Q s := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.add _ t s

theorem hamiltonian_mem_domain_iff_hasDerivAt (x : HilbertSpace) (s : ℝ) :
    x ∈ (hamiltonianPMap Q).closure.domain ↔
      ∃ y : HilbertSpace,
        HasDerivAt (fun t : ℝ => hamiltonianUnitaryGroup Q t x) y s := by
  exact (hamiltonianCore Q).mem_domain_iff_hasDerivAt x s

end OperatorAlgebra.Unbounded.Example
