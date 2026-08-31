/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.HarmonicOscillator.SpectralProjections

/-! # The energy levels of the quantum harmonic oscillator

This file states, for the *actual* physical Hamiltonian of the one-dimensional quantum harmonic
oscillator — `-ℏ²/2m · ψ'' + ½mω²x²ψ`, a genuine unbounded differential operator on `L²(ℝ)`, not a
stand-in — the textbook energy-quantization theorem:

> the possible energies are exactly `ℏω(n + ½)` for `n = 0, 1, 2, …`, and there are no others.

`HarmonicOscillator/DifferentialCore.lean` already proves the Hamiltonian is essentially
self-adjoint (unconditionally, from the actual differential equation, via the Hermite functions as
a dense family of eigenvectors) and builds its spectral measure.
`HarmonicOscillator/SpectralProjections.lean` already proves each Hermite eigenfunction is fixed by
its own spectral projection. What was still missing — proved here — is the *converse*: nothing
else carries any spectral weight, so the eigenvalues found are the complete list. This file adapts
`Unbounded/Examples/HarmonicOscillatorSpectrum.lean`'s `H_pp`/`pointSpectrumSet` argument (proved
there for a hand-built stand-in operator matching the eigenbasis by construction) to the genuine
differential closure — the same argument, now applied to the operator it was always meant for.

## Main result

- `harmonicOscillator_isEigenvalue_iff` : **the headline theorem.** A real number `E` is an energy
  level of the oscillator (i.e. `∃` a nonzero state fixed up to the scalar `E` by the Hamiltonian)
  if and only if `E = ℏω(n + ½)` for some natural number `n`. Stated purely in eigenvector/
  eigenvalue language — no spectral-measure vocabulary appears in the statement, only in the proof.
- `H_pp_eq_top` : every state is built entirely out of energy eigenstates (no continuous spectrum,
  no scattering states) — the fact that makes the eigenvalue list in the headline theorem
  *complete*, not just a list of some energies that happen to work.
-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace
open MeasureTheory Set
open QuantumMechanics.WOTSpectralMeasure

namespace QuantumMechanics
namespace HarmonicOscillator
namespace DifferentialCore

/-- A witness oscillator, used only to exhibit *some* countable `HilbertBasis` of
`NewHilbertSpace` and hence establish separability of the ambient space (mirrors
`Unbounded/Examples/HarmonicOscillatorSpectrum.lean`'s `separabilityWitness`; `NewHilbertSpace`
itself does not depend on the oscillator's physical parameters, so this applies uniformly). -/
def separabilityWitness : OldOscillator := ⟨1, 1, one_pos, one_pos⟩

/-- **`NewHilbertSpace` is separable.** Any transported oscillator eigenbasis is countable and its
algebraic span is dense (`HilbertBasis.dense_span`); a countable set's algebraic span over the
separable field `ℂ` is separable, and separability passes to the closure, which is the whole
space. -/
instance : TopologicalSpace.SeparableSpace NewHilbertSpace := by
  set b := transportedEigenbasis separabilityWitness
  have hcount : (Set.range (⇑b)).Countable := Set.countable_range _
  have hspan : TopologicalSpace.IsSeparable
      (Submodule.span ℂ (Set.range (⇑b)) : Set NewHilbertSpace) :=
    hcount.isSeparable.span
  have hclosure : TopologicalSpace.IsSeparable
      (closure (Submodule.span ℂ (Set.range (⇑b)) : Set NewHilbertSpace)) :=
    hspan.closure
  have heq : closure (Submodule.span ℂ (Set.range (⇑b)) : Set NewHilbertSpace) = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, b.dense_span]
    rfl
  rw [heq] at hclosure
  exact TopologicalSpace.isSeparable_univ_iff.mp hclosure

variable (q : OldOscillator)

/-! ## Every eigenfunction lies in the pure-point subspace -/

/-- **Every (transported) Hermite eigenfunction lies in the pure-point subspace.** Immediate from
`hermiteBasisSpectralMeasure_apply`: `pointSpectrumSet` contains `eigenValue n` (the projection
doesn't kill `eₙ`), and the projection at that singleton fixes `eₙ`, exhibiting `eₙ` as being in
the range of `E(pointSpectrumSet)`. -/
lemma transportedEigenbasis_mem_H_pp (n : ℕ) :
    transportedEigenbasis q n ∈ H_pp (differentialHamiltonianSpectralMeasure q) := by
  set E := differentialHamiltonianSpectralMeasure q with hE
  set S := pointSpectrumSet E with hS
  have hSmeas : MeasurableSet S := measurableSet_pointSpectrumSet E
  have hne : transportedEigenbasis q n ≠ 0 := (transportedEigenbasis q).orthonormal.ne_zero n
  have hmem : q.eigenValue n ∈ S := by
    rw [hS, pointSpectrumSet, Set.mem_setOf_eq]
    intro hz
    apply hne
    have h1 := hermiteBasisSpectralMeasure_apply q n (measurableSet_singleton (q.eigenValue n))
    rw [if_pos (Set.mem_singleton _)] at h1
    rw [hz] at h1
    simpa using h1.symm
  have hcSingle : MeasurableSet ({q.eigenValue n} : Set ℝ) := measurableSet_singleton _
  have hinter : S ∩ {q.eigenValue n} = {q.eigenValue n} :=
    Set.inter_eq_self_of_subset_right (Set.singleton_subset_iff.mpr hmem)
  have hcomp : E S * E ({q.eigenValue n} : Set ℝ) = E ({q.eigenValue n} : Set ℝ) := by
    rw [E.comp_eq_of_inter hSmeas hcSingle, hinter]
  have hfix : E S (transportedEigenbasis q n) = transportedEigenbasis q n := by
    have h1 := congrArg
      (fun A : NewHilbertSpace →WOT[ℂ] NewHilbertSpace => A (transportedEigenbasis q n)) hcomp
    change E S (E ({q.eigenValue n} : Set ℝ) (transportedEigenbasis q n)) =
      E ({q.eigenValue n} : Set ℝ) (transportedEigenbasis q n) at h1
    rw [hermiteBasisSpectralMeasure_apply q n hcSingle, if_pos (Set.mem_singleton _)] at h1
    exact h1
  exact ⟨transportedEigenbasis q n, hfix⟩

/-! ## No continuous spectrum -/

/-- **The oscillator's Hamiltonian has purely point spectrum: `H_pp = ⊤`.** Every state is built
entirely out of energy eigenstates — no continuous spectrum, no scattering states. `H_pp` is a
closed subspace (`isClosed_H_pp`) containing every Hermite eigenfunction, hence containing the
(dense) closure of their span, i.e. the whole space. -/
lemma H_pp_eq_top :
    H_pp (differentialHamiltonianSpectralMeasure q) = ⊤ := by
  set E := differentialHamiltonianSpectralMeasure q with hE
  have hspan_le : Submodule.span ℂ (Set.range (⇑(transportedEigenbasis q))) ≤ H_pp E := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact transportedEigenbasis_mem_H_pp q n
  have hle : (Submodule.span ℂ (Set.range (⇑(transportedEigenbasis q)))).topologicalClosure ≤
      H_pp E :=
    Submodule.topologicalClosure_minimal _ hspan_le (isClosed_H_pp E)
  rw [(transportedEigenbasis q).dense_span] at hle
  exact top_le_iff.mp hle

/-- **The continuous subspace is trivial.** -/
lemma H_cont_eq_bot :
    H_cont (differentialHamiltonianSpectralMeasure q) = ⊥ := by
  rw [H_cont, H_pp_eq_top q, Submodule.top_orthogonal_eq_bot]

/-- **The absolutely-continuous subspace is trivial.** -/
lemma H_ac_eq_bot :
    H_ac (differentialHamiltonianSpectralMeasure q) = ⊥ := by
  set E := differentialHamiltonianSpectralMeasure q with hE
  have hle : H_ac E ≤ H_cont E := E.H_cont.map_subtype_le E.isPureAC_submodule
  rw [H_cont_eq_bot q] at hle
  exact le_bot_iff.mp hle

/-- **The singular-continuous subspace is trivial.** -/
lemma H_sc_eq_bot :
    H_sc (differentialHamiltonianSpectralMeasure q) = ⊥ := by
  set E := differentialHamiltonianSpectralMeasure q with hE
  have hle : H_sc E ≤ H_cont E := E.H_cont.map_subtype_le E.isPureSC_submodule
  rw [H_cont_eq_bot q] at hle
  exact le_bot_iff.mp hle

/-! ## The complete list of energy levels -/

/-- **Every physical energy level is an atom of the spectral measure** (the `⊇` direction of
`pointSpectrumSet_eq_range_eigenValue`). -/
lemma range_eigenValue_subset_pointSpectrumSet :
    Set.range q.eigenValue ⊆
      pointSpectrumSet (differentialHamiltonianSpectralMeasure q) := by
  rintro _ ⟨n, rfl⟩
  have h1 := hermiteBasisSpectralMeasure_apply q n (measurableSet_singleton (q.eigenValue n))
  rw [if_pos (Set.mem_singleton _)] at h1
  rw [pointSpectrumSet, Set.mem_setOf_eq]
  intro hz
  exact (transportedEigenbasis q).orthonormal.ne_zero n (by rw [hz] at h1; simpa using h1.symm)

/-- **The oscillator's spectral measure has no atoms outside the physical energy levels**, hence
(with `range_eigenValue_subset_pointSpectrumSet`) exactly the physical energy levels.

Same non-degeneracy argument as `Unbounded/Examples/HarmonicOscillatorSpectrum.lean`'s
`pointSpectrumSet_eq_range_eigenValue`, now for the genuine differential closure: if `c` were an
atom outside `Set.range q.eigenValue`, disjointness of `{c}` from every `{eigenValue n}` would
force every Fourier coefficient of the corresponding nonzero vector against the (complete) Hermite
basis to vanish — contradiction. -/
lemma pointSpectrumSet_eq_range_eigenValue :
    pointSpectrumSet (differentialHamiltonianSpectralMeasure q) = Set.range q.eigenValue := by
  refine Set.eq_of_subset_of_subset ?_ (range_eigenValue_subset_pointSpectrumSet q)
  intro c hc
  by_contra hcon
  set E := differentialHamiltonianSpectralMeasure q with hE
  obtain ⟨x, hx⟩ := E.exists_apply_ne_zero_of_mem_pointSpectrumSet hc
  apply hx
  have horth : ∀ n : ℕ, ⟪transportedEigenbasis q n, E {c} x⟫_ℂ = 0 := by
    intro n
    have hcne : c ≠ q.eigenValue n := fun h => hcon ⟨n, h.symm⟩
    have hdisj : Disjoint ({c} : Set ℝ) ({q.eigenValue n} : Set ℝ) := by simp [hcne]
    have heig := hermiteBasisSpectralMeasure_apply q n (measurableSet_singleton (q.eigenValue n))
    rw [if_pos (Set.mem_singleton _)] at heig
    have hzero := E.inner_apply_apply_eq_zero_of_disjoint hdisj
      (measurableSet_singleton c) (measurableSet_singleton (q.eigenValue n)) x
      (transportedEigenbasis q n)
    rw [heig] at hzero
    exact inner_eq_zero_symm.mp hzero
  have hreprzero : (transportedEigenbasis q).repr (E {c} x) = 0 := by
    ext n
    simpa using ((transportedEigenbasis q).repr_apply_apply (E {c} x) n).trans (horth n)
  exact (transportedEigenbasis q).repr.injective (by rw [hreprzero, map_zero])

/-! ## The headline theorem -/

/-- **The energy levels of the quantum harmonic oscillator are exactly `ℏω(n + ½)`, `n = 0, 1, 2,
…`, and there are no others.**

`E` is an energy level — meaning some nonzero physical state `x` is fixed by the Hamiltonian up to
the scalar `E`, i.e. `x` is a stationary state of energy `E` — if and only if `E = ℏω(n + ½)` for
some natural number `n`.

This is the actual quantization-of-energy theorem: `E`, the differential Hamiltonian's closure,
and "fixed up to a scalar" are all literal, standard operator-theoretic notions (no bespoke
spectral-measure vocabulary appears in the statement); the completeness of the list — that there
is no other kind of energy level, e.g. from a continuous or scattering spectrum — is exactly
`H_pp_eq_top`, used internally in the proof. -/
lemma harmonicOscillator_isEigenvalue_iff (E : ℝ) :
    (∃ (x : NewHilbertSpace) (_ : x ≠ 0) (hx : x ∈ (differentialHamiltonianClosure q).domain),
      differentialHamiltonianClosure q ⟨x, hx⟩ = (E : ℂ) • x) ↔
    ∃ n : ℕ, E = q.eigenValue n := by
  constructor
  · rintro ⟨x, hx0, hx, hEx⟩
    have hfix := OperatorAlgebra.mem_atom_range_of_isEigenvector
      (differentialHamiltonianSpectralTheorem q) hx hEx
    have hmem : E ∈ pointSpectrumSet (differentialHamiltonianSpectralMeasure q) := by
      rw [pointSpectrumSet, Set.mem_setOf_eq]
      intro hz
      exact hx0 (by rw [hz] at hfix; simpa using hfix.symm)
    rw [pointSpectrumSet_eq_range_eigenValue] at hmem
    obtain ⟨n, hn⟩ := hmem
    exact ⟨n, hn.symm⟩
  · rintro ⟨n, rfl⟩
    have hne : transportedEigenbasis q n ≠ 0 := (transportedEigenbasis q).orthonormal.ne_zero n
    have heq : eigenfunctionSpace q n = transportedEigenbasis q n :=
      eigenfunctionSpace_eq_transportedEigenbasis q n
    refine ⟨transportedEigenbasis q n, hne, heq ▸ differentialHamiltonian_mem_closure_domain q n,
      ?_⟩
    have hsub : (⟨eigenfunctionSpace q n, differentialHamiltonian_mem_closure_domain q n⟩ :
        (differentialHamiltonianClosure q).domain) =
        ⟨transportedEigenbasis q n, heq ▸ differentialHamiltonian_mem_closure_domain q n⟩ :=
      Subtype.ext heq
    rw [← hsub, differentialHamiltonianClosure_apply_eigenfunction q n, heq]

end DifferentialCore
end HarmonicOscillator
end QuantumMechanics
end
