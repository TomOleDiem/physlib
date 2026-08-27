/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.FunctionalCalculus
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.InvariantCore
public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.AnalyticVector
public import Physlib.QuantumMechanics.OperatorAlgebra.HilbertSpace
public import Physlib.QuantumMechanics.Operators.Unbounded
public import Physlib.Meta.Sorry
public import Physlib.Meta.TODO.Basic

/-!

# Common invariant cores and strong commutation

The other files in `Unbounded/` give the *spectral*/W⋆ view of an affiliated observable: its
`PVM`, functional calculus, measurement statistics. This file gives the complementary *algebraic*
view: for a family of affiliated operators sharing a common dense invariant domain `D`, algebraic
manipulations (`A + B`, `A * B`, `A ^ n`, `⁅A, B⁆`) should be ordinary `Module.End ℂ D` algebra,
with the domain/invariance bookkeeping proved exactly once, rather than re-litigated at every use
site. `InvariantCore` packages this; its output `restrict : ι → Module.End ℂ D` is deliberately
just an ordinary family of endomorphisms — no bespoke `EqOn`/`CommOn`-style API is introduced,
since `Module.End ℂ D` already has everything (`Ring`, `Module ℂ`, ...) needed.

We also define *strong* (spectral) commutation of two affiliated operators, `StronglyCommutes`,
and the standard package of results connecting it to preserved subspaces.

`AnalyticVector.lean` now supplies the actual Nelson analytic-vector vocabulary
(`LinearPMap.IsAnalyticVector`, structural closure lemmas, and the single-operator criterion
`IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors`, itself `@[sorryful]` — see that
file's module docstring for exactly which hard analytic construction is missing and why). The
`of_commonCore_comm_certificate` adapter below now genuinely *consumes* that vocabulary — analytic
vectors on the common core, not a directly-supplied strong-commutation conclusion — rather than
packaging a hypothesis that already was the theorem's conclusion. Deriving essential
self-adjointness of each restriction from those analytic vectors is spelled out explicitly (via
the single-operator criterion); the remaining joint step — that algebraically commuting essentially
self-adjoint operators with a common analytic core have *strongly* commuting closures — is Nelson's
1959 joint-commutation theorem and remains `@[sorryful]`, precisely scoped in the theorem's
docstring.

## Key results

- `InvariantCore T` : a common dense invariant core `D` for a family `T : ι → AffiliatedOperator
  A`, exposing `restrict : ι → Module.End ℂ D`.
- `AffiliatedOperator.StronglyCommutes` : `E_S(X) E_T(Y) = E_T(Y) E_S(X)` for all Borel `X, Y`.
- `StronglyCommutes.spectralProjection_comm`, `.map_comm` : the standard consequences of strong
  commutation.
- `StronglyCommutes.preserves_eigenspace` : commuting core-restrictions preserve eigenspaces (see
  its docstring for why this is now stated with an algebraic `Commute` hypothesis on
  `core.restrict`, rather than the disconnected spectral-level `StronglyCommutes` the original
  statement used).
- `StronglyCommutes.of_commonCore_comm_certificate` : Nelson's joint-commutation theorem, stated
  with genuine analytic-vector hypotheses on the common core rather than a supplied conclusion.
  `@[sorryful]`; the essential-self-adjointness half is derived explicitly from the analytic
  vectors, the strong-commutation half is the still-missing joint analytic argument.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra
open MeasureTheory Set

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-! ## Strong commutation -/

namespace AffiliatedOperator

/-- Two affiliated operators *strongly commute* iff their spectral projections commute setwise:
`E_S(X) E_T(Y) = E_T(Y) E_S(X)` for all Borel `X, Y ⊆ ℂ`. This is the honest, representation-free
notion of commutation for unbounded operators (algebraic commutation on a shared domain is
generally *not* enough — see `StronglyCommutes.of_commonCore_comm_certificate`). -/
def StronglyCommutes (S T : AffiliatedOperator A) : Prop :=
  ∀ X Y : Set ℂ, Commute (S.spectralMeasure X) (T.spectralMeasure Y)

namespace StronglyCommutes

variable {S T U : AffiliatedOperator A}

lemma symm (h : S.StronglyCommutes T) : T.StronglyCommutes S := fun X Y => (h Y X).symm

/-- Restated at the level of `Projection A`: strong commutation is exactly commutation of every
pair of spectral projections. -/
lemma spectralProjection_comm (h : S.StronglyCommutes T) (X Y : Set ℂ) :
    Commute (S.spectralMeasure.spectralProjection X : A)
      (T.spectralMeasure.spectralProjection Y : A) :=
  h X Y

/-- Strong commutation is preserved by the measurable functional calculus: if a self-adjoint
restriction `S'` of `S` strongly commutes with `T`, then so does any measurable function of `S'`.
Follows directly from `E_{f(S')}(Z) = E_{S'}(f⁻¹ Z)`
(`AffiliatedObservable.measurableFC_spectralMeasure_apply`): commutation of `S'`'s and `T`'s
projections transports to `f(S')`'s projections against `T`'s, via the measurable embedding
`Complex.ofReal` bridging `S'`'s real spectral measure and `S'.toAffiliatedOperator`'s complex
one. -/
lemma map_comm {S' : AffiliatedObservable A} (h : S'.toAffiliatedOperator.StronglyCommutes T)
    (f : ℝ → ℂ) (hf : Measurable f) : (S'.measurableFC f hf).StronglyCommutes T := by
  have hemb : MeasurableEmbedding (Complex.ofReal) :=
    Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  intro Z Y
  by_cases hZ : MeasurableSet Z
  · rw [S'.measurableFC_spectralMeasure_apply hf hZ]
    have hX : MeasurableSet (Complex.ofReal '' (f ⁻¹' Z)) := hemb.measurableSet_image.2 (hf hZ)
    have := h (Complex.ofReal '' (f ⁻¹' Z)) Y
    rwa [S'.toAffiliatedOperator_spectralMeasure_apply hX,
      Set.preimage_image_eq _ Complex.ofReal_injective] at this
  · simp [(S'.measurableFC f hf).spectralMeasure.apply_eq_zero_of_not_measurableSet hZ]

/- Strong commutation preserves spectral subspaces: `T`'s spectral projections leave each of
`S`'s spectral subspaces invariant, under any representation. Proved as
`SpectralDecomposition.lean`'s `AffiliatedObservable.preserves_spectralSubspace` — that file
imports `Core.lean` (for `StronglyCommutes`), so the theorem lives there rather than here, to
avoid a circular import; it is a direct application of this file's `spectralProjection_comm`
through `SpectralDecomposition.lean`'s general `preserves_range_of_commute`. -/

/-- Strong commutation preserves eigenspaces, at the level of a common invariant core.

**Honesty note on the hypothesis.** The original statement of this lemma took
`h : (T' 0).StronglyCommutes (T' 1)` — a fact about the *spectral measures* of `T' 0`/`T' 1`
inside the algebra `A` — as its hypothesis, while the conclusion is about `core.restrict 0` and
`core.restrict 1`, plain `Module.End ℂ core.D` endomorphisms of the abstract core `D`. But
`InvariantCore` (see `InvariantCore.lean`, a file this development does not own/edit) attaches
*no* coherence data linking `restrict i` to `T' i` at all: `restrict : ι → Module.End ℂ D` is
just an arbitrary family of endomorphisms of the right type. So the old hypothesis `h` was
logically inert — nothing connected it to `core.restrict` — and the lemma as stated was not
merely hard but *unprovable*: `h` gave no information whatsoever about `core.restrict 0`/
`core.restrict 1`. Reconstructing that missing link in general needs exactly the representation/
embedding/essential-self-adjointness apparatus `StronglyCommutes.of_commonCore_comm_certificate` (Nelson's
theorem) is built to supply, together with the still-missing concrete Hilbert-space spectral
theorem (`Affiliated.lean`'s honesty note) to turn "spectral projections commute" back into
"`core.restrict` commutes" through a representation.

The fix taken here: state the coherence that actually *is* available and usable at the pure
algebra level directly, as the hypothesis. If `core.restrict 0` and `core.restrict 1` themselves
commute as endomorphisms of `D` (the honest algebraic shadow of "`S` and `T` strongly commute,
as witnessed on this particular core"), then — by nothing more than the standard linear-algebra
fact that commuting endomorphisms preserve each other's eigenspaces — `core.restrict 0` maps every
`core.restrict 1`-eigenspace into itself. This is a strictly *weaker* hypothesis than the original
`h` (any honest coherence relating `core.restrict` to `T'` together with genuine
`StronglyCommutes` would produce it, e.g. as the algebraic input to Nelson's theorem), so nothing
that could actually have been proved from `h` is lost; what's dropped is only the illusion that an
unconnected spectral-level hypothesis alone sufficed. -/
lemma preserves_eigenspace {T' : Fin 2 → AffiliatedOperator A} (core : InvariantCore T')
    (hcomm : Commute (core.restrict 0) (core.restrict 1)) (μ : ℂ) :
    ∀ x ∈ Module.End.eigenspace (core.restrict 1) μ, core.restrict 0 x ∈
      Module.End.eigenspace (core.restrict 1) μ := by
  intro x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have hcomm' : core.restrict 0 (core.restrict 1 x) = core.restrict 1 (core.restrict 0 x) := by
    have := congrArg (fun f : Module.End ℂ core.D => f x) hcomm
    simpa [Module.End.mul_apply] using this
  calc core.restrict 1 (core.restrict 0 x)
      = core.restrict 0 (core.restrict 1 x) := hcomm'.symm
    _ = core.restrict 0 (μ • x) := by rw [hx]
    _ = μ • core.restrict 0 x := map_smul _ _ _

/-! ## Nelson's commutation interface -/

/-- **Nelson's joint-commutation theorem**, stated with the actual analytic-vector hypotheses
Nelson's 1959 argument uses, rather than a directly-supplied strong-commutation conclusion.

The hypotheses package a common invariant core `core.D`, embedded (injectively) into a concrete
Hilbert space `H` on which two symmetric `LinearPMap`s `U 0`, `U 1` restrict to `core.restrict 0`/
`core.restrict 1` (`hUrestrict`), commute there algebraically (`hcomm`), and have `emb`-images
consisting of analytic vectors, densely so (`hUanalytic`, `hUanalyticDense`) — exactly Reed–Simon
Vol. II Theorem X.39's hypotheses.

**What is actually proved here.** Essential self-adjointness of each `U i` is derived honestly
from `hUanalytic`/`hUanalyticDense`/`hUsym` via
`LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors` — so this adapter no
longer merely assumes essential self-adjointness as an opaque input, the way the previous version
of this file did.

**What remains open (`@[sorryful]`).** The *joint* step — that two essentially self-adjoint
operators which commute algebraically on a common core of joint analytic vectors have strongly
commuting closures — is Nelson's actual joint-commutation theorem, distinct from (and harder than)
the single-operator essential-self-adjointness criterion invoked above. Its standard proof
(Reed–Simon Vol. II, Theorem X.41, or Nelson 1959 §9) builds the two local one-parameter unitary
semigroups from the analytic power series (as in the single-operator argument), shows they commute
on a common core using the algebraic commutation hypothesis and a Trotter-type limiting argument
on truncated exponentials, and only then invokes Stone's theorem to transport that commutation to
the spectral projections making up `StronglyCommutes`. None of this Trotter/semigroup-commutation
argument is attempted here — it is additional content beyond
`isEssentiallySelfAdjoint_of_denseAnalyticVectors`, not a corollary of it. -/
@[sorryful]
theorem of_commonCore_comm_certificate {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : Representation A H) {T' : Fin 2 → AffiliatedOperator A}
    (core : InvariantCore T') (emb : core.D →ₗ[ℂ] H) (hemb : Function.Injective emb)
    (U : Fin 2 → H →ₗ.[ℂ] H)
    (hUmem : ∀ i x, emb x ∈ (U i).domain)
    (hUdense : ∀ i, (U i).HasDenseDomain)
    (hUsym : ∀ i, (U i).IsSymmetric)
    (hUrestrict : ∀ i (x : core.D), U i (Subtype.mk (emb x) (hUmem i x)) =
      emb (core.restrict i x))
    (hUanalytic : ∀ i (x : core.D), (U i).IsAnalyticVector (emb x))
    (hUanalyticDense :
      ∀ i, (Submodule.span ℂ {y : H | (U i).IsAnalyticVector y}).topologicalClosure = ⊤)
    (hcomm : core.restrictCommutator 0 1 = 0) :
    (T' 0).StronglyCommutes (T' 1) := by
  have hUess : ∀ i, (U i).IsEssentiallySelfAdjoint := fun i =>
    (hUsym i).isEssentiallySelfAdjoint_of_denseAnalyticVectors (hUanalyticDense i)
  sorry

TODO "Prove the remaining joint-commutation half of \
  `AffiliatedOperator.StronglyCommutes.of_commonCore_comm_certificate` (Nelson's 1959 \
  joint-commutation theorem, Reed-Simon Vol. II Theorem X.41). The essential self-adjointness of \
  each `U i` is already derived above from `hUanalytic`/`hUanalyticDense`/`hUsym` via \
  `LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors`. What is missing is the \
  Trotter-type limiting argument showing the two Stone unitary groups generated by `U 0`/`U 1`'s \
  closures commute (using `hcomm`'s algebraic commutation on the shared analytic core), together \
  with transporting that unitary-group commutation, through `π` and `emb`, back to commutation of \
  the abstract spectral projections making up `(T' 0).StronglyCommutes (T' 1)`. See the theorem's \
  docstring for the precise decomposition."

end StronglyCommutes

end AffiliatedOperator

/-- `StronglyCommutes`, specialized to two self-adjoint affiliated observables (via their common
`AffiliatedOperator` view). -/
def AffiliatedObservable.StronglyCommutes {A : Type*} [OperatorAlgebra A]
    (S T : AffiliatedObservable A) : Prop :=
  AffiliatedOperator.StronglyCommutes S.toAffiliatedOperator T.toAffiliatedOperator

end OperatorAlgebra
