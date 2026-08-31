/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Examples.HarmonicOscillator
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Spectral.EigenvectorSpectralAtom
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Dynamics.Stone

/-!
# The harmonic oscillator has purely point spectrum

This file applies the general eigenvector/atom theory of `EigenvectorSpectralAtom.lean` and the
spectral-type decomposition of `SpectralTypeDecomposition.lean` to the concrete harmonic
oscillator of `Example/HarmonicOscillator.lean`.

## Main results

* `QuantumMechanics.OneDimension.HarmonicOscillator.eigenValue_strictMono`/`_injective` : the
  physical eigenvalues `(n + 1/2) ℏ ω` are strictly increasing in `n`, hence injective.
* `QuantumMechanics.OneDimension.instSeparableSpaceHilbertSpace` : `HilbertSpace` is separable
  (via the countable dense span of any harmonic-oscillator eigenbasis), needed to invoke the
  pp/ac/sc spectral-type machinery.
* `OperatorAlgebra.Unbounded.Example.hamiltonianSpectralMeasure_apply_eigenbasis` : each
  eigenbasis vector is fixed by the spectral projection at its eigenvalue.
* `OperatorAlgebra.Unbounded.Example.H_pp_eq_top` : the oscillator's pure-point subspace is the
  whole Hilbert space, i.e. `H_ac = H_sc = ⊥` (`H_ac_eq_bot`, `H_sc_eq_bot`) — **the oscillator has
  purely point spectrum**.
* `OperatorAlgebra.Unbounded.Example.range_eigenValue_subset_pointSpectrumSet` and
  `.pointSpectrumSet_eq_range_eigenValue` : every physical eigenvalue is an atom of the spectral
  measure, and conversely there are no atoms outside the physical eigenvalues — the oscillator's
  spectrum is exactly `Set.range Q.eigenValue`.
* `OperatorAlgebra.Unbounded.Example.hamiltonianUnitaryGroup_hasDerivAt_zero` : Stone's theorem
  specialized to the oscillator's unitary group.
-/

@[expose] public section

noncomputable section

open scoped Topology InnerProductSpace
open MeasureTheory Set
open QuantumMechanics.WOTSpectralMeasure

namespace QuantumMechanics
namespace OneDimension
namespace HarmonicOscillator

open Constants

variable (Q : HarmonicOscillator)

/-- **The physical eigenvalues are strictly increasing in `n`.** `(n + 1/2) ℏ ω` is an affine
function of `n` with positive slope `ℏ ω`. -/
theorem eigenValue_strictMono : StrictMono Q.eigenValue := by
  intro n m hnm
  have hnm' : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hpos : 0 < ℏ * Q.ω := mul_pos ℏ_pos Q.ω_pos
  unfold eigenValue
  nlinarith [hpos]

/-- **The physical eigenvalues are pairwise distinct.** -/
theorem eigenValue_injective : Function.Injective Q.eigenValue :=
  Q.eigenValue_strictMono.injective

end HarmonicOscillator

open HarmonicOscillator

/-- A fixed witness harmonic oscillator, used only to exhibit *some* countable
`HilbertBasis` of `HilbertSpace` and hence establish separability of the ambient space. Since
`HilbertSpace` itself does not depend on the oscillator's physical parameters, this instance
applies uniformly regardless of which `HarmonicOscillator` is under study elsewhere. -/
private def separabilityWitness : HarmonicOscillator := ⟨1, 1, one_pos, one_pos⟩

/-- **`HilbertSpace` is separable.** Any harmonic-oscillator eigenbasis is countable and its
algebraic span is dense (`HilbertBasis.dense_span`); a countable set's algebraic span over the
separable field `ℂ` is separable (`TopologicalSpace.IsSeparable.span`), and separability passes to
the closure, which is the whole space. -/
instance : TopologicalSpace.SeparableSpace HilbertSpace := by
  set b := separabilityWitness.eigenbasis
  have hcount : (Set.range (⇑b)).Countable := Set.countable_range _
  have hspan : TopologicalSpace.IsSeparable
      (Submodule.span ℂ (Set.range (⇑b)) : Set HilbertSpace) :=
    hcount.isSeparable.span
  have hclosure : TopologicalSpace.IsSeparable
      (closure (Submodule.span ℂ (Set.range (⇑b)) : Set HilbertSpace)) :=
    hspan.closure
  have heq : closure (Submodule.span ℂ (Set.range (⇑b)) : Set HilbertSpace) = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, b.dense_span]
    rfl
  rw [heq] at hclosure
  exact TopologicalSpace.isSeparable_univ_iff.mp hclosure

end OneDimension
end QuantumMechanics

namespace OperatorAlgebra.Unbounded.Example

open QuantumMechanics OneDimension HarmonicOscillator

variable (Q : HarmonicOscillator)

/-- **Each eigenbasis vector is an eigenvector of the closed Hamiltonian, with eigenvalue
`Q.eigenValue n`.** A transport of `hamiltonianPMap_apply_eigenbasis` along
`(hamiltonianPMap Q).le_closure`. -/
theorem eigenbasis_mem_hamiltonianPMap_domain (n : ℕ) :
    Q.eigenbasis n ∈ (hamiltonianPMap Q).domain :=
  Submodule.subset_span ⟨n, rfl⟩

theorem eigenbasis_mem_hamiltonianPMapClosure_domain (n : ℕ) :
    Q.eigenbasis n ∈ (hamiltonianPMap Q).closure.domain :=
  (hamiltonianPMap Q).le_closure.1 (eigenbasis_mem_hamiltonianPMap_domain Q n)

theorem hamiltonianPMapClosure_apply_eigenbasis (n : ℕ) :
    (hamiltonianPMap Q).closure ⟨Q.eigenbasis n, eigenbasis_mem_hamiltonianPMapClosure_domain Q n⟩
      = (Q.eigenValue n : ℂ) • Q.eigenbasis n := by
  have hn : Q.eigenbasis n ∈ (hamiltonianPMap Q).domain := eigenbasis_mem_hamiltonianPMap_domain Q n
  have hcl : (hamiltonianPMap Q) ⟨Q.eigenbasis n, hn⟩ =
      (hamiltonianPMap Q).closure
        ⟨Q.eigenbasis n, eigenbasis_mem_hamiltonianPMapClosure_domain Q n⟩ :=
    (hamiltonianPMap Q).le_closure.2 rfl
  rw [hamiltonianPMap_apply_eigenbasis Q n hn] at hcl
  exact hcl.symm

/-- **Each eigenbasis vector is fixed by the spectral projection at its eigenvalue.** The
concrete instantiation of `OperatorAlgebra.mem_atom_range_of_isEigenvector` for the oscillator. -/
theorem hamiltonianSpectralMeasure_apply_eigenbasis (n : ℕ) :
    (hamiltonianSpectralData Q).spectralMeasure {(Q.eigenValue n : ℝ)} (Q.eigenbasis n) =
      Q.eigenbasis n :=
  OperatorAlgebra.mem_atom_range_of_isEigenvector (hamiltonianDomainAwareSpectralTheorem Q)
    (eigenbasis_mem_hamiltonianPMapClosure_domain Q n)
    (hamiltonianPMapClosure_apply_eigenbasis Q n)

/-- **Every physical eigenvalue is an atom of the oscillator's spectral measure.** -/
theorem eigenValue_mem_pointSpectrumSet (n : ℕ) :
    Q.eigenValue n ∈
      WOTSpectralMeasure.pointSpectrumSet (hamiltonianSpectralData Q).spectralMeasure := by
  rw [WOTSpectralMeasure.pointSpectrumSet, Set.mem_setOf_eq]
  intro hz
  have h0 : Q.eigenbasis n = 0 := by
    have h1 := hamiltonianSpectralMeasure_apply_eigenbasis Q n
    rw [hz] at h1
    simpa using h1.symm
  have hnorm : ‖Q.eigenbasis n‖ = 1 := Q.eigenbasis.orthonormal.1 n
  rw [h0, norm_zero] at hnorm
  norm_num at hnorm

/-- **Every eigenbasis vector lies in the pure-point subspace.** -/
theorem eigenbasis_mem_H_pp (n : ℕ) :
    Q.eigenbasis n ∈ WOTSpectralMeasure.H_pp (hamiltonianSpectralData Q).spectralMeasure := by
  set E := (hamiltonianSpectralData Q).spectralMeasure with hE
  set S := WOTSpectralMeasure.pointSpectrumSet E with hS
  have hSmeas : MeasurableSet S := WOTSpectralMeasure.measurableSet_pointSpectrumSet E
  have hcSingle : MeasurableSet ({Q.eigenValue n} : Set ℝ) := measurableSet_singleton _
  have hsub : ({Q.eigenValue n} : Set ℝ) ⊆ S :=
    Set.singleton_subset_iff.mpr (eigenValue_mem_pointSpectrumSet Q n)
  have hinter : S ∩ {Q.eigenValue n} = {Q.eigenValue n} := Set.inter_eq_self_of_subset_right hsub
  have hcomp : E S * E ({Q.eigenValue n} : Set ℝ) = E ({Q.eigenValue n} : Set ℝ) := by
    rw [E.comp_eq_of_inter hSmeas hcSingle, hinter]
  have hfix : E S (Q.eigenbasis n) = Q.eigenbasis n := by
    have h1 := congrArg (fun A : HilbertSpace →WOT[ℂ] HilbertSpace => A (Q.eigenbasis n)) hcomp
    change E S (E ({Q.eigenValue n} : Set ℝ) (Q.eigenbasis n)) =
      E ({Q.eigenValue n} : Set ℝ) (Q.eigenbasis n) at h1
    rwa [hamiltonianSpectralMeasure_apply_eigenbasis Q n] at h1
  exact ⟨Q.eigenbasis n, hfix⟩

/-- **The harmonic oscillator has purely point spectrum: `H_pp = ⊤`.** `H_pp` is a closed
submodule (`isClosed_H_pp`) containing every eigenbasis vector, hence containing the (dense)
closure of their span, i.e. the whole space. -/
theorem H_pp_eq_top :
    WOTSpectralMeasure.H_pp (hamiltonianSpectralData Q).spectralMeasure = ⊤ := by
  set E := (hamiltonianSpectralData Q).spectralMeasure with hE
  have hspan_le : Submodule.span ℂ (Set.range (⇑Q.eigenbasis)) ≤ WOTSpectralMeasure.H_pp E := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact eigenbasis_mem_H_pp Q n
  have hle : (Submodule.span ℂ (Set.range (⇑Q.eigenbasis))).topologicalClosure ≤
      WOTSpectralMeasure.H_pp E :=
    Submodule.topologicalClosure_minimal _ hspan_le (WOTSpectralMeasure.isClosed_H_pp E)
  rw [Q.eigenbasis.dense_span] at hle
  exact top_le_iff.mp hle

/-- **The continuous subspace is trivial.** -/
theorem H_cont_eq_bot :
    WOTSpectralMeasure.H_cont (hamiltonianSpectralData Q).spectralMeasure = ⊥ := by
  rw [WOTSpectralMeasure.H_cont, H_pp_eq_top Q, Submodule.top_orthogonal_eq_bot]

/-- **The absolutely-continuous subspace is trivial.** -/
theorem H_ac_eq_bot :
    WOTSpectralMeasure.H_ac (hamiltonianSpectralData Q).spectralMeasure = ⊥ := by
  set E := (hamiltonianSpectralData Q).spectralMeasure with hE
  have hle : WOTSpectralMeasure.H_ac E ≤ WOTSpectralMeasure.H_cont E :=
    E.H_cont.map_subtype_le E.isPureAC_submodule
  rw [H_cont_eq_bot Q] at hle
  exact le_bot_iff.mp hle

/-- **The singular-continuous subspace is trivial.** -/
theorem H_sc_eq_bot :
    WOTSpectralMeasure.H_sc (hamiltonianSpectralData Q).spectralMeasure = ⊥ := by
  set E := (hamiltonianSpectralData Q).spectralMeasure with hE
  have hle : WOTSpectralMeasure.H_sc E ≤ WOTSpectralMeasure.H_cont E :=
    E.H_cont.map_subtype_le E.isPureSC_submodule
  rw [H_cont_eq_bot Q] at hle
  exact le_bot_iff.mp hle

/-- **Every physical eigenvalue is an atom of the spectral measure** (the `⊇` direction of
`pointSpectrumSet_eq_range_eigenValue`). -/
theorem range_eigenValue_subset_pointSpectrumSet :
    Set.range Q.eigenValue ⊆
      WOTSpectralMeasure.pointSpectrumSet (hamiltonianSpectralData Q).spectralMeasure := by
  rintro _ ⟨n, rfl⟩
  exact eigenValue_mem_pointSpectrumSet Q n

/-- **The oscillator's spectrum is exactly the set of physical eigenvalues.**

The `⊇` direction is `range_eigenValue_subset_pointSpectrumSet` (every eigenvalue is an atom). For
the `⊆` direction, suppose `c` is an atom of the spectral measure `E` but `c ∉ Set.range
Q.eigenValue`. Pick `x` with `v := E {c} x ≠ 0`. For each `n`, `c ≠ Q.eigenValue n`, so `{c}` and
`{Q.eigenValue n}` are disjoint; since `E {Q.eigenValue n} (Q.eigenbasis n) = Q.eigenbasis n`
(`hamiltonianSpectralMeasure_apply_eigenbasis`), the general disjoint-orthogonality lemma
`WOTSpectralMeasure.inner_apply_apply_eq_zero_of_disjoint` gives `⟪Q.eigenbasis n, v⟫ = 0` for
every `n`. Hence every Fourier coefficient of `v` against the Hilbert basis `Q.eigenbasis` vanishes,
so `v = 0` (`HilbertBasis.repr` is injective and `repr v` would be the zero sequence) —
    contradicting
`v ≠ 0`. This is the standard non-degeneracy argument (Reed & Simon, *Methods of Modern Mathematical
Physics I*, the discrete-spectrum discussion following Theorem VIII.6). -/
theorem pointSpectrumSet_eq_range_eigenValue :
    WOTSpectralMeasure.pointSpectrumSet (hamiltonianSpectralData Q).spectralMeasure =
      Set.range Q.eigenValue := by
  refine Set.eq_of_subset_of_subset ?_ (range_eigenValue_subset_pointSpectrumSet Q)
  intro c hc
  by_contra hcon
  set E := (hamiltonianSpectralData Q).spectralMeasure with hE
  obtain ⟨x, hx⟩ := E.exists_apply_ne_zero_of_mem_pointSpectrumSet hc
  apply hx
  have horth : ∀ n : ℕ, ⟪Q.eigenbasis n, E {c} x⟫_ℂ = 0 := by
    intro n
    have hcne : c ≠ Q.eigenValue n := fun h => hcon ⟨n, h.symm⟩
    have hdisj : Disjoint ({c} : Set ℝ) ({Q.eigenValue n} : Set ℝ) := by
      simp [hcne]
    have heig := hamiltonianSpectralMeasure_apply_eigenbasis Q n
    rw [← hE] at heig
    have hzero := E.inner_apply_apply_eq_zero_of_disjoint hdisj
      (measurableSet_singleton c) (measurableSet_singleton (Q.eigenValue n)) x (Q.eigenbasis n)
    rw [heig] at hzero
    exact inner_eq_zero_symm.mp hzero
  have hreprzero : Q.eigenbasis.repr (E {c} x) = 0 := by
    ext n
    simpa using (Q.eigenbasis.repr_apply_apply (E {c} x) n).trans (horth n)
  exact Q.eigenbasis.repr.injective (by rw [hreprzero, map_zero])

/-- **Stone's theorem for the oscillator.** The strong derivative of the oscillator's unitary
group at `t = 0`, on the domain of the closed Hamiltonian, is `i • H`. A one-line specialization
of `OperatorAlgebra.DomainAwareSelfAdjointSpectralTheorem.expUnitaryGroup_hasDerivAt_zero`. -/
theorem hamiltonianUnitaryGroup_hasDerivAt_zero (x : (hamiltonianPMap Q).closure.domain) :
    HasDerivAt (fun t : ℝ => hamiltonianUnitaryGroup Q t (x : HilbertSpace))
      (Complex.I • (hamiltonianPMap Q).closure x) 0 :=
  (hamiltonianDomainAwareSpectralTheorem Q).expUnitaryGroup_hasDerivAt_zero x

end OperatorAlgebra.Unbounded.Example
