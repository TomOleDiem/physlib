/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Affil.Affiliated

/-!

# Spectral measurement statistics: distribution, moments, expectation, variance

For `A : AffiliatedObservable M` and a normal state `ω`, the distribution `A.distribution ω` is
the ordinary scalar probability measure `μ_{ω,A}(S) = ω(E_A(S))` (`PVM.distribution` specialized
to the real spectral measure). Unlike the bounded case (`States/Expectation.lean`), an unbounded
observable need not have finite expectation or variance in every state — e.g. a heavy-tailed
`μ_{ω,A}` gives `ω⟨A⟩` no meaning at all. We therefore define the finite-moment predicates first,
and only *then* expectation and variance, each gated by the relevant integrability hypothesis, so
the API cannot be misused to silently assume finiteness.

## Key results

- `AffiliatedObservable.distribution` : `μ_{ω,A}`, as a `ProbabilityMeasure ℝ`.
- `AffiliatedObservable.HasFiniteMoment` : the `n`-th moment of `μ_{ω,A}` is finite.
- `AffiliatedObservable.moment` : the `n`-th moment of `μ_{ω,A}`, given `HasFiniteMoment`.
- `AffiliatedObservable.expectation`/`variance` : specializations to `n = 1, 2`.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra
open MeasureTheory Set

namespace OperatorAlgebra

namespace AffiliatedObservable

variable {A : Type*} [WStarAlgebra A] (T : AffiliatedObservable A) (ω : NormalState A)

/-! ## The spectral distribution -/

/-- The distribution of `T` in the state `ω`: the scalar probability measure `μ_{ω,T}(S) =
ω(E_T(S))` obtained by evaluating `T`'s (real) spectral measure against `ω`. -/
def distribution : ProbabilityMeasure ℝ := T.spectralMeasure.distribution ω

@[simp]
lemma distribution_eq_spectralMeasure_distribution :
    T.distribution ω = T.spectralMeasure.distribution ω := rfl

/-! ## Finite moments -/

/-- The `n`-th moment of `T`'s distribution in the state `ω` is finite, i.e. `x ↦ x ^ n` is
integrable against `μ_{ω,T}`. Unbounded observables need not satisfy this for any particular
`n`, `ω` pair — this is exactly the honesty condition the top-level TL;DR asks for: "do not
pretend every unbounded observable has finite expectation or variance". -/
def HasFiniteMoment (n : ℕ) : Prop :=
  MeasureTheory.Integrable (fun x : ℝ => x ^ n) (T.distribution ω : Measure ℝ)

/-- The `n`-th moment of `T`'s distribution in the state `ω`, given that it is finite. -/
def moment {n : ℕ} (_ : T.HasFiniteMoment ω n) : ℝ :=
  ∫ x, x ^ n ∂(T.distribution ω : Measure ℝ)

/-! ## Expectation and variance -/

/-- The expectation `ω⟨T⟩ = ∫ λ \, dμ_{ω,T}(λ)`, defined only when `T` has a finite first moment
in the state `ω`. Mirrors `States/Expectation.lean`'s `State.expectation` for bounded observables,
but — unlike there — is only meaningful under an explicit finiteness hypothesis. -/
def expectation (h : T.HasFiniteMoment ω 1) : ℝ := T.moment ω h

/-- The variance `Var_ω(T) = ω⟨T²⟩ - ω⟨T⟩²`, defined only when `T` has finite first and second
moments in the state `ω`. -/
def variance (h1 : T.HasFiniteMoment ω 1) (h2 : T.HasFiniteMoment ω 2) : ℝ :=
  T.moment ω h2 - (T.expectation ω h1) ^ 2

/-- Every bounded observable, viewed as an affiliated observable via the canonical inclusion, has
finite moments of every order in every state.  The proof uses the bounded-support certificate
carried by `BorelFunctionalCalculus`, together with the fact that a probability measure gives
zero mass to the complement of that support. -/
lemma _root_.OperatorAlgebra.Observable.toAffiliatedObservable_hasFiniteMoment
    {A : Type*} [WStarAlgebra A] [BorelFunctionalCalculus A]
    (a : Observable A) (ω : NormalState A) (n : ℕ) :
    (Observable.toAffiliatedObservable a).HasFiniteMoment ω n := by
  obtain ⟨C, hC, hsupport⟩ := BorelFunctionalCalculus.spectralSupport a
  let T : AffiliatedObservable A := Observable.toAffiliatedObservable a
  let K : Set ℝ := Set.Icc (-C) C
  have hK : MeasurableSet K := measurableSet_Icc
  have hdisj : Disjoint Kᶜ K := by
    refine Set.disjoint_left.2 ?_
    intro x hx hxK
    exact hx hxK
  have hzero : T.spectralMeasure Kᶜ = 0 := by
    exact hsupport Kᶜ hK.compl hdisj
  have hμzero : (T.distribution ω : Measure ℝ) Kᶜ = 0 := by
    rw [T.distribution_eq_spectralMeasure_distribution,
      PVM.distribution_apply T.spectralMeasure ω Kᶜ hK.compl]
    rw [hzero]
    simp
  have hmem : ∀ᵐ x ∂(T.distribution ω : Measure ℝ), x ∈ K := by
    apply ae_iff.mpr
    change (T.distribution ω : Measure ℝ) Kᶜ = 0
    exact hμzero
  have hbound : ∀ᵐ x ∂(T.distribution ω : Measure ℝ),
      ‖x ^ n‖ ≤ C ^ n := by
    filter_upwards [hmem] with x hx
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg x) (abs_le.2 hx) n
  exact Integrable.of_bound (measurable_id.pow_const n).aestronglyMeasurable (C ^ n) hbound

end AffiliatedObservable

end OperatorAlgebra
