/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Core.Core
public import Physlib.Meta.TODO.Basic

/-!

# Spectral decomposition and symmetry reduction

This file supplies the layer of general, model-independent spectral vocabulary that sits between
"`A` is affiliated" (`Affiliated.lean`) and "`A` is a specific Hamiltonian" (the oscillator,
hydrogen, ...): `spectrum`, `pointSpectrum`, `discreteSpectrum`, `essentialSpectrum`, all read off
the spectral measure `A.spectralMeasure` directly, plus the general bridge from algebraic symmetry
to invariant spectral subspaces. None of this is specific to any particular Hamiltonian — a
concrete model only has to (a) prove essential self-adjointness/affiliation and (b) compute *its*
`spectralMeasure`; everything here then applies for free.

## Architecture (for context)

```
C⋆-algebra A            — bounded physical algebra (Basic.lean)
W⋆-algebra M             — spectral projections / measurable structure (Measurement/PVM.lean)
AffiliatedObservable M   — unbounded self-adjoint observables, spectral measure (Affiliated.lean)
  ├── spectral analysis  — spectrum, point/discrete/essential spectrum (this file)
  └── symmetry reduction — strong commutation ⇒ invariant spectral sectors (this file, Core.lean)
```

Model-specific work (the oscillator's `E_n = ℏω(n+½)`, hydrogen's `E_n = -C/n²`) instantiates this
general machinery; it does not have to reprove any of it.

## Key results

- `AffiliatedObservable.spectrum` : `σ(A)`, the topological support of the spectral measure.
- `AffiliatedObservable.pointSpectrum` : `σₚ(A)`, the atoms of the spectral measure.
- `pointSpectrum_subset_spectrum` : `σₚ(A) ⊆ σ(A)`.
- `AffiliatedObservable.discreteSpectrum`/`essentialSpectrum` : `σ(A)` split into isolated points
  and the rest (a topological stand-in for the usual finite-multiplicity discrete/essential split
  — see the honesty note on `discreteSpectrum`).
- `preserves_range_of_commute` : a bounded symmetry commuting with a spectral projection maps its
  range into itself, under any representation — the general content behind "symmetry algebra +
  spectral projections ⇒ representations on energy sectors".

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra
open MeasureTheory Set

namespace OperatorAlgebra

namespace AffiliatedObservable

variable {A : Type*} [OperatorAlgebra A] (T : AffiliatedObservable A)

/-! ## Spectral projections are monotone in the underlying set -/

/-- A PVM's projections are monotone: if `S ⊆ T` (both measurable), `E_A(S) ≤ E_A(T)` in the
ambient star order — `E_A(S)` "lives inside" `E_A(T)`. -/
lemma spectralProjection_mono {S U : Set ℝ} (hS : MeasurableSet S) (hU : MeasurableSet U)
    (hSU : S ⊆ U) : (T.spectralProjection S : A) ≤ (T.spectralProjection U : A) := by
  have hinter : S ∩ U = S := Set.inter_eq_self_of_subset_left hSU
  have hmul : (T.spectralProjection S : A) * (T.spectralProjection U : A) =
      T.spectralProjection S := by
    show (T.spectralMeasure S : A) * (T.spectralMeasure U : A) = T.spectralMeasure S
    rw [T.spectralMeasure.comp_eq_of_inter hS hU, hinter]
  exact (IsStarProjection.le_iff_mul_eq_left (T.spectralProjection S).2
    (T.spectralProjection U).2).mpr hmul

/-! ## The spectrum -/

/-- **The spectrum of an affiliated observable**, `σ(A)`: the topological support of its spectral
measure — points every neighborhood of which carries nonzero spectral weight. This is the
general, model-independent notion the top-level architecture note calls for; a concrete
Hamiltonian's *actual* spectrum (`E_n = ℏω(n+½)`, `E_n = -C/n²`, ...) is always a computation
*using* this definition, never a redefinition of it. -/
def spectrum : Set ℝ :=
  {l : ℝ | ∀ ε > 0, (T.spectralProjection (Set.Ioo (l - ε) (l + ε)) : A) ≠ 0}

/-- **The point spectrum**, `σₚ(A)`: the atoms of the spectral measure, i.e. points carrying
nonzero spectral weight *by themselves*, not merely in every neighborhood. -/
def pointSpectrum : Set ℝ := {l : ℝ | (T.spectralProjection {l} : A) ≠ 0}

/-- **Eigenvalues are spectral**: `σₚ(A) ⊆ σ(A)`. Every neighborhood of an atom `l` contains
`{l}` itself, so `spectralProjection_mono` transports nonvanishing of `E_A({l})` to nonvanishing
of `E_A` on every neighborhood — an honest proof, not an assumption, of the standard inclusion
"eigenvalues are spectral values". -/
theorem pointSpectrum_subset_spectrum : T.pointSpectrum ⊆ T.spectrum := by
  intro l0 hl0 ε hε hzero
  apply hl0
  have hsub : ({l0} : Set ℝ) ⊆ Set.Ioo (l0 - ε) (l0 + ε) := by
    simp only [Set.singleton_subset_iff, Set.mem_Ioo]
    constructor <;> linarith
  have hle := T.spectralProjection_mono (measurableSet_singleton l0) measurableSet_Ioo hsub
  rw [hzero] at hle
  have h0 : (0 : A) ≤ (T.spectralProjection {l0} : A) := (Projection.mem_effect _).1
  exact le_antisymm hle h0

/-! ## Discrete and essential spectrum -/

/-- **The (topologically) discrete spectrum**: isolated points of `σ(A)`.

Honesty note: the textbook notion of "discrete spectrum" additionally requires each isolated
eigenvalue to have *finite multiplicity* — a Murray–von Neumann finiteness/comparison-of-
projections condition on `E_A({l})` that needs a trace or dimension function on `M`, which
neither Mathlib nor this development has yet (see `Measurement/PVM.lean`'s honesty note on the same
gap). This definition is the purely topological approximation: isolated points of the spectrum,
without the finite-multiplicity refinement. It agrees with the textbook notion whenever `M` is,
e.g., a type I factor with all eigenspaces automatically finite-dimensional (as for the oscillator
and hydrogen), but is not the fully general statement. -/
def discreteSpectrum : Set ℝ := {l ∈ T.spectrum | ∃ ε > 0, T.spectrum ∩ Set.Ioo (l - ε) (l + ε) = {l}}

/-- **The essential spectrum**: everything in `σ(A)` that is not (topologically) discrete —
accumulation points of the spectrum. Inherits `discreteSpectrum`'s honesty caveat: this excludes
isolated points regardless of their multiplicity, rather than only isolated points of *finite*
multiplicity. -/
def essentialSpectrum : Set ℝ := T.spectrum \ T.discreteSpectrum

@[simp]
lemma spectrum_eq_discrete_union_essential :
    T.discreteSpectrum ∪ T.essentialSpectrum = T.spectrum := by
  rw [essentialSpectrum, Set.union_sdiff_cancel]
  exact fun _ h => h.1

lemma discreteSpectrum_disjoint_essentialSpectrum :
    Disjoint T.discreteSpectrum T.essentialSpectrum :=
  disjoint_sdiff_self_right

/-! ## Symmetry reduction: strong commutation ⇒ invariant spectral sectors -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **The general bridge from algebraic symmetry to invariant spectral subspaces.** If `p` (in
particular a spectral projection) commutes, under some representation `π`, with a bounded
operator `u`, then `π u` maps `(π p).range` into itself — no idempotency or self-adjointness of
`p` is even needed, just `π p * π u = π u * π p`. This is the elementary linear-algebra content
behind "symmetry algebra + spectral projections ⇒ representations on energy sectors": specialized
to `p := T.spectralProjection S` and `u` a symmetry commuting with `T` (in the sense `Commute u
(T.spectralProjection S : A)` for every Borel `S`, i.e. `u` strongly commutes with `T`), every
spectral sector `E_T(S)` becomes `u`-invariant. -/
theorem preserves_range_of_commute (π : Representation A H) {p u : A}
    (hcomm : Commute u p) :
    ∀ x ∈ LinearMap.range (π p).toLinearMap, π u x ∈ LinearMap.range (π p).toLinearMap := by
  rintro x ⟨y, rfl⟩
  refine ⟨π u y, ?_⟩
  have hcomm' : (π p : B(H)) * (π u : B(H)) = (π u : B(H)) * (π p : B(H)) := by
    rw [← map_mul, ← map_mul, hcomm]
  have hy := congrArg (fun f : B(H) => f y) hcomm'
  simpa using hy

/-- **Every spectral sector of a strongly-commuting (bounded) symmetry is invariant.** For `u ∈ A`
commuting with *every* spectral projection of `T` (the natural notion of "`u` is a symmetry of
`T`"), and any representation `π`, every spectral sector `π(T.spectralProjection S)` is
`π u`-invariant. This is the concrete instance of `preserves_range_of_commute` the architecture
note's "symmetry algebra + spectral projections ⇒ representations on energy sectors" refers to. -/
theorem spectralSector_invariant_of_commute (π : Representation A H) {u : A}
    (hcomm : ∀ S : Set ℝ, Commute u (T.spectralProjection S : A)) (S : Set ℝ) :
    ∀ x ∈ LinearMap.range (π (T.spectralProjection S : A)).toLinearMap,
      π u x ∈ LinearMap.range (π (T.spectralProjection S : A)).toLinearMap :=
  preserves_range_of_commute π (hcomm S)

/-- **Strong commutation (`Core.lean`) preserves spectral subspaces.** Under any representation
`π`, if `S` strongly commutes with `T` (`Core.lean`'s `AffiliatedOperator.StronglyCommutes`), then
`T`'s spectral projection `E_T(Y)` maps `S`'s spectral subspace `(π (E_S(X))).range` into itself —
`Core.lean`'s `StronglyCommutes.preserves_spectralSubspace`, proved here (rather than in
`Core.lean`, to avoid a circular import) as a direct instance of `preserves_range_of_commute`
applied to the two commuting spectral projections `E_S(X)`, `E_T(Y)`. -/
theorem _root_.OperatorAlgebra.AffiliatedOperator.StronglyCommutes.preserves_spectralSubspace
    {S U : AffiliatedOperator A} (h : S.StronglyCommutes U) (π : Representation A H)
    (X Y : Set ℂ) :
    ∀ x ∈ LinearMap.range (π (S.spectralMeasure.spectralProjection X : A)).toLinearMap,
      π (U.spectralMeasure.spectralProjection Y : A) x ∈
        LinearMap.range (π (S.spectralMeasure.spectralProjection X : A)).toLinearMap :=
  preserves_range_of_commute π (h.spectralProjection_comm X Y).symm

end AffiliatedObservable

end OperatorAlgebra
