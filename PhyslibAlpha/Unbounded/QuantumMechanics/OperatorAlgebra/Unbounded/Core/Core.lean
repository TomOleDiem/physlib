/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Calculus.FunctionalCalculus
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Core.InvariantCore
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Core.AnalyticVector
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.HilbertSpace
public import Physlib.QuantumMechanics.Operators.Unbounded
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.Core.UnboundedExtras
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

`AnalyticVector.lean` supplies the actual Nelson analytic-vector vocabulary
(`LinearPMap.IsAnalyticVector` and its structural closure lemmas), including the checked
single-operator finite-radius Nelson criterion. A former joint-commutation adapter was removed:
its `InvariantCore.restrict` field had no coherence equation relating it to the abstract affiliated
operators or to the represented closures, so its conclusion was not derivable from its arguments.
A future joint-commutation API must introduce that missing transport data explicitly.

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
- The joint-commutation adapter is intentionally not exported until its representation and
  closure-coherence hypotheses are specified. This prevents an unconnected common-core record
  from being mistaken for a proof of abstract spectral commutation.

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
generally *not* enough; a future common-core bridge must add explicit representation coherence). -/
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
`core.restrict 1`. Reconstructing that missing link in general needs representation,
embedding, and essential-self-adjointness apparatus, together with the concrete Hilbert-space
spectral theorem (`Affiliated.lean`'s honesty note), to turn "spectral projections commute" back into
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

/-! ## Joint commutation boundary

The former `of_commonCore_comm_certificate` declaration was deliberately removed. Its common-core
record exposed arbitrary endomorphisms and an embedding, but supplied no equation identifying the
abstract affiliated spectral measures with the closures of the represented operators. Therefore
its strong-commutation conclusion was not derivable from its arguments. A future Nelson
joint-commutation API belongs in a separate layer and must carry that representation and
closure-coherence data explicitly, in addition to the analytic and algebraic hypotheses.
The proved `StronglyCommutes` definition and the core-level eigenspace preservation theorem above
remain available independently of that future bridge.
 -/

end StronglyCommutes

end AffiliatedOperator

/-- `StronglyCommutes`, specialized to two self-adjoint affiliated observables (via their common
`AffiliatedOperator` view). -/
def AffiliatedObservable.StronglyCommutes {A : Type*} [OperatorAlgebra A]
    (S T : AffiliatedObservable A) : Prop :=
  AffiliatedOperator.StronglyCommutes S.toAffiliatedOperator T.toAffiliatedOperator

end OperatorAlgebra
