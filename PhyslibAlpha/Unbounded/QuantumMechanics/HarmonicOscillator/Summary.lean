/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.HarmonicOscillator.DifferentialSpectrum

/-! # HarmonicOscillator/Summary

The oscillator's headline results, one after another, with no new proofs — each theorem here is a
direct citation of a theorem proved elsewhere in this tree (`DifferentialCore.lean`,
`SpectralProjections.lean`, `DifferentialSpectrum.lean`). Read this file, in order, for the whole
physical story without the operator-algebra machinery those files needed to prove it:

`q : OldOscillator` is a genuine, physical, one-dimensional quantum harmonic oscillator: mass
`q.m`, angular frequency `q.ω`, both positive. Its Hamiltonian is the actual unbounded
differential operator `-ℏ²/(2m) ψ'' + ½ m ω² x² ψ` on `L²(ℝ)` — nothing here is a finite-
dimensional stand-in.

1. The energy levels are `ℏω(n + ½)`, `n = 0, 1, 2, …` — by definition.
2. The `n`-th eigenfunction is the textbook Hermite-polynomial-times-Gaussian wavefunction.
3. The Hamiltonian is essentially self-adjoint, so "the energy operator" genuinely has one
   well-defined self-adjoint closure, not an ambiguity to be resolved by hand.
4. Every one of those Hermite wavefunctions really is an eigenvector of that closure, with the
   claimed eigenvalue.
5. The spectrum is pure point: the Hermite eigenfunctions alone already span the whole Hilbert
   space, so there is nothing else to find — no continuous or scattering spectrum.
6. Put together: a real number `E` is an energy level of the physical Hamiltonian if and only if
   `E = ℏω(n + ½)` for some `n` — the textbook answer, and the whole answer.
7. **Stone's theorem** turns that self-adjoint closure into a genuine time-evolution operator:
   `differentialHamiltonianEvolution q t` — the conventional `exp(-itH)` — is unitary at every
   time `t`, built from the closure, not assumed.
-/

@[expose] public section
noncomputable section

namespace QuantumMechanics
namespace HarmonicOscillator
namespace DifferentialCore

open scoped InnerProductSpace
open QuantumMechanics.WOTSpectralMeasure

variable (q : OldOscillator)

/-- 1. **The energy levels are `ℏω(n + ½)`.** -/
theorem summary_eigenvalue_formula (n : ℕ) :
    q.eigenValue n = (n + 1 / 2) * Constants.ℏ * q.ω :=
  rfl

/-- 2. **The `n`-th eigenfunction is the textbook Hermite-times-Gaussian wavefunction** — the
same formula anyone would write on a blackboard, `q.eigenfunction n`, is genuinely the pointwise
value of the actual Hilbert-space eigenvector `eigenfunctionSpace q n`. -/
theorem summary_eigenfunction_formula (n : ℕ) (x : Space 1) :
    eigenfunctionSpaceSchwartz q n x = q.eigenfunction n (x 0) :=
  eigenfunctionSpaceSchwartz_apply q n x

/-- 3. **Essential self-adjointness.** The differential Hamiltonian has one, and only one,
self-adjoint closure — this is the one analytic fact the whole theory rests on. -/
theorem summary_selfAdjoint : IsSelfAdjoint (differentialHamiltonianClosure q) :=
  differentialHamiltonianClosure_isSelfAdjoint q

/-- 4. **Every Hermite wavefunction is a genuine eigenvector** of the self-adjoint closure, with
exactly the eigenvalue from item 1. -/
theorem summary_eigenfunction_is_eigenvector (n : ℕ) :
    differentialHamiltonianClosure q
        ⟨eigenfunctionSpace q n, differentialHamiltonian_mem_closure_domain q n⟩ =
      (q.eigenValue n : ℂ) • eigenfunctionSpace q n :=
  differentialHamiltonianClosure_apply_eigenfunction q n

/-- 5. **Pure point spectrum, diagonal form.** The Hermite eigenvectors already span the whole
Hilbert space, so the Hamiltonian is diagonal in that basis — there is no continuous or
scattering part left over to find. -/
theorem summary_pure_point_spectrum :
    H_pp (differentialHamiltonianSpectralMeasure q) = ⊤ :=
  H_pp_eq_top q

/-- 6. **The full answer.** `E` is an energy level of the actual physical Hamiltonian if and only
if `E = ℏω(n + ½)` for some natural number `n` — no other real number is an energy level. -/
theorem summary_energy_levels (E : ℝ) :
    (∃ (x : NewHilbertSpace) (_ : x ≠ 0) (hx : x ∈ (differentialHamiltonianClosure q).domain),
      differentialHamiltonianClosure q ⟨x, hx⟩ = (E : ℂ) • x) ↔
    ∃ n : ℕ, E = q.eigenValue n :=
  harmonicOscillator_isEigenvalue_iff q E

/-- 7. **Stone's theorem, invoked.** The conventional time-evolution operator
`exp(-itH)` — built from the self-adjoint closure (item 3) via Stone's theorem — is unitary at
every time `t`. -/
theorem summary_stone_time_evolution (t : ℝ) :
    differentialHamiltonianEvolution q t ∈ unitary (NewHilbertSpace →WOT[ℂ] NewHilbertSpace) :=
  (differentialHamiltonianEvolution q).mem_unitary t

end DifferentialCore
end HarmonicOscillator
end QuantumMechanics
end
