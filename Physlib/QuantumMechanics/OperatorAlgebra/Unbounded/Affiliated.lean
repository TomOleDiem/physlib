/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Unbounded.NormalState

/-!

# Affiliated operators and observables

This file extends the bounded C⋆-algebra theory of `Observable A`
(`OperatorAlgebra/Basic.lean`) to *affiliated* operators: the (generally unbounded, densely
defined) operators belonging to a W⋆-algebra `A` in the sense that all of their spectral
projections lie in `A`.

## Honesty note on the representation

The standard textbook definition of "`T` affiliated to a von Neumann algebra `M ⊆ B(H)`" is
representation-dependent (`u T u⁻¹ = T` for every unitary `u` in the commutant `M′`), or
equivalently, purely algebraically, via Kaplansky's bounded transform (`T` corresponds to an
element `a ∈ M` with `‖a‖ ≤ 1` and `1 - a⋆a` having dense range). Reconstructing either
characterization from scratch is exactly the content of "the unbounded self-adjoint spectral
theorem", which is a representation-bridge theorem beyond the representation-free spectral-data
layer developed here.

We instead take the *spectral measure itself* as the defining datum of an affiliated operator:
`AffiliatedOperator A` is a normal operator's `PVM ℂ A`, and `AffiliatedObservable A` restricts
this to a *real* `PVM ℝ A` — spectrally, that is exactly what self-adjointness means. This keeps
the public API entirely representation-free (no Hilbert space `H` anywhere in sight, per the
architecture diagram), at the cost of only modelling *normal* affiliated operators (every
self-adjoint operator is normal, so this loses nothing for `AffiliatedObservable`, which is the
main object of interest here). The genuine bounded-transform characterization of affiliation
(linking this back to concrete unbounded operators on a chosen Hilbert space) remains an explicit
representation-bridge milestone.

## Key results

- `AffiliatedOperator A` : a normal operator affiliated to `A`, via its spectral measure
  `PVM ℂ A`.
- `AffiliatedObservable A` : a self-adjoint affiliated operator, via a *real* spectral measure
  `PVM ℝ A`.
- `AffiliatedObservable.spectralProjection` : `A.spectralMeasure S`, packaged as a `Projection A`.
- `Observable.toAffiliatedObservable` : the canonical inclusion of bounded observables into
  affiliated ones.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra
open MeasureTheory Set

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-! ## Affiliated operators -/

/-- A (normal) operator affiliated to `A`, packaged as its spectral measure `PVM ℂ A`. See the
module docstring for why this representation-free definition only captures normal operators, and
why that is enough for `AffiliatedObservable`. -/
structure AffiliatedOperator (A : Type*) [OperatorAlgebra A] where
  /-- The spectral measure `E_T : \Borel(ℂ) → Projection A` of an affiliated operator `T`,
  representing `T = ∫ z \, dE_T(z)`. -/
  spectralMeasure : PVM ℂ A

/-- A self-adjoint affiliated operator: an `AffiliatedOperator` whose spectral measure is
supported on the reals, matching the spectral characterization of self-adjointness
(`σ(T) ⊆ ℝ`). -/
structure AffiliatedObservable (A : Type*) [OperatorAlgebra A] where
  /-- The (real) spectral measure `E_A : \Borel(ℝ) → Projection A` of a self-adjoint affiliated
  operator `A`, representing `A = ∫ λ \, dE_A(λ)`. -/
  spectralMeasure : PVM ℝ A

namespace AffiliatedObservable

variable (T : AffiliatedObservable A)

/-- Every self-adjoint affiliated operator is, in particular, a (normal) affiliated operator: its
complex spectral measure is the pushforward of its real one along `ℝ ↪ ℂ`, via `PVM.map`
(`NormalState.lean`) — genuinely built, not merely a signature, since `PVM.map` needs only
measurability of the embedding, never continuity/boundedness. -/
def toAffiliatedOperator (T : AffiliatedObservable A) : AffiliatedOperator A where
  spectralMeasure := T.spectralMeasure.map Complex.ofReal Complex.measurable_ofReal

/-- The defining property of `toAffiliatedOperator`: its complex spectral measure recovers the
real one on the preimage of any Borel set, `E_{T.toAffiliatedOperator}(S) = E_T(ofReal ⁻¹' S)`. -/
@[simp]
lemma toAffiliatedOperator_spectralMeasure_apply (T : AffiliatedObservable A) {S : Set ℂ}
    (hS : MeasurableSet S) :
    (T.toAffiliatedOperator.spectralMeasure S : A) = T.spectralMeasure (Complex.ofReal ⁻¹' S) :=
  T.spectralMeasure.map_apply Complex.measurable_ofReal hS

noncomputable instance instCoeAffiliatedOperator :
    Coe (AffiliatedObservable A) (AffiliatedOperator A) :=
  ⟨toAffiliatedOperator⟩

/-! ## The spectral theorem API -/

/-- The spectral projection `E_A(S) ∈ A` associated to a Borel set `S ⊆ ℝ`. -/
def spectralProjection (S : Set ℝ) : Projection A := T.spectralMeasure.spectralProjection S

@[simp]
lemma spectralMeasure_coe_spectralProjection (S : Set ℝ) :
    (T.spectralProjection S : A) = T.spectralMeasure S := rfl

@[simp]
lemma spectralProjection_univ : T.spectralProjection univ = ⟨1, IsStarProjection.one A⟩ :=
  Subtype.ext T.spectralMeasure.univ

@[ext]
theorem ext {S U : AffiliatedObservable A}
    (h : ∀ X : Set ℝ, MeasurableSet X → S.spectralMeasure X = U.spectralMeasure X) :
    S = U := by
  cases S with
  | mk S =>
    cases U with
    | mk U =>
      congr
      exact PVM.ext h

/- **The unbounded self-adjoint spectral theorem.** The concrete theorem now lives in
`Operators/SpectralTheory/UnboundedSpectralIntegral.lean`: a self-adjoint `LinearPMap` whose weak
matrix elements are reconstructed by a real WOT spectral measure is equal, including domain, to
the canonical maximal square-moment integral. The representation-free `AffiliatedObservable` has
no Hilbert-space domain, so its remaining task is only the representation-level bridge to that
concrete theorem. -/
/- Boundary: connecting `AffiliatedObservable` to the concrete domain-aware theorem requires a
faithful normal representation together with an explicit WOT-to-norm PVM bridge. The spectral-data
object above is already the representation-free façade; the representation-dependent realization
is supplied in `Representation.lean` through `AffiliationBridge`. -/

end AffiliatedObservable

end OperatorAlgebra

/-! ## Transport along a star-algebra isomorphism

`AffiliatedObservable` (and `AffiliatedOperator`) are functorial in `A` along `StarAlgEquiv`s: a
star-algebra isomorphism `β : A ≃⋆ₐ[ℂ] B` transports spectral data by pushing the underlying vector
measure forward through `β` (viewed as a continuous additive map — continuity comes for free since
every star-algebra isomorphism of C⋆-algebras is isometric, `StarAlgEquiv.isometry`). Functoriality
(`id ↦ id`, composition ↦ composition) is then a direct consequence of the corresponding facts for
`β` itself; representation-compatibility with this transport is proved in `Representation.lean`,
where a Hilbert-space representation is already available to state it against.

This section is declared in the root `StarAlgEquiv` namespace (rather than nested under
`OperatorAlgebra`, matching `Dynamics/Automorphism.lean`'s `StarAlgEquiv.observable`), so that
`β.affiliatedObservable` etc. resolve as dot notation on `β : A ≃⋆ₐ[ℂ] B`. -/

section StarAlgEquivAffiliatedObservable

open OperatorAlgebra

variable {A B C : Type*} [OperatorAlgebra A] [OperatorAlgebra B] [OperatorAlgebra C]

/-- The additive-monoid-homomorphism view of a star-algebra isomorphism, used only to push a
`VectorMeasure` forward through it (`VectorMeasure.mapRange` wants an `→+`, not the bundled
`≃⋆ₐ` type). -/
def StarAlgEquiv.toAddMonoidHom' (β : A ≃⋆ₐ[ℂ] B) : A →+ B where
  toFun := β
  map_zero' := map_zero β
  map_add' := map_add β

/-- Continuity of the additive-monoid-homomorphism view, proved directly from the isometry bound
(`StarAlgEquiv.norm_map`) rather than by reusing `Isometry.continuous`: the latter's `Continuous`
proof lives at a different (but defeq) topological-instance path than the one
`VectorMeasure.mapRange` expects, so going through the norm bound avoids an instance-diamond
mismatch. -/
lemma StarAlgEquiv.continuous_toAddMonoidHom' (β : A ≃⋆ₐ[ℂ] B) :
    Continuous (StarAlgEquiv.toAddMonoidHom' β) := by
  apply AddMonoidHomClass.continuous_of_bound (StarAlgEquiv.toAddMonoidHom' β) 1
  intro a
  simp [StarAlgEquiv.toAddMonoidHom', StarAlgEquiv.norm_map β a]

/-- Transport an `AffiliatedObservable` along a star-algebra isomorphism, by pushing its spectral
measure forward: `E_{β.affiliatedObservable T}(S) = β(E_T(S))`. -/
noncomputable def StarAlgEquiv.affiliatedObservable (β : A ≃⋆ₐ[ℂ] B) (T : AffiliatedObservable A) :
    AffiliatedObservable B where
  spectralMeasure :=
  { toVectorMeasure :=
      T.spectralMeasure.toVectorMeasure.mapRange (StarAlgEquiv.toAddMonoidHom' β)
        (StarAlgEquiv.continuous_toAddMonoidHom' β)
    isStarProjection' := fun S => by
      change IsStarProjection (β (T.spectralMeasure S))
      refine ⟨?_, ?_⟩
      · change β (T.spectralMeasure S) * β (T.spectralMeasure S) = β (T.spectralMeasure S)
        rw [← map_mul]
        exact congrArg β (T.spectralMeasure.isStarProjection S).isIdempotentElem
      · change star (β (T.spectralMeasure S)) = β (T.spectralMeasure S)
        rw [← map_star]
        exact congrArg β (T.spectralMeasure.isStarProjection S).isSelfAdjoint
    univ' := by
      change β (T.spectralMeasure univ) = 1
      rw [T.spectralMeasure.univ, map_one] }

@[simp]
lemma StarAlgEquiv.affiliatedObservable_spectralMeasure_apply (β : A ≃⋆ₐ[ℂ] B)
    (T : AffiliatedObservable A) (S : Set ℝ) :
    (β.affiliatedObservable T).spectralMeasure S = β (T.spectralMeasure S) := by
  change (T.spectralMeasure.toVectorMeasure.mapRange (StarAlgEquiv.toAddMonoidHom' β)
    (StarAlgEquiv.continuous_toAddMonoidHom' β)) S = _
  rw [MeasureTheory.VectorMeasure.mapRange_apply]
  rfl

@[simp]
lemma StarAlgEquiv.refl_affiliatedObservable (T : AffiliatedObservable A) :
    (StarAlgEquiv.refl (R := ℂ) (A := A)).affiliatedObservable T = T := by
  apply AffiliatedObservable.ext
  intro S _
  simp [StarAlgEquiv.affiliatedObservable_spectralMeasure_apply]

/-- Functoriality of the transport under composition (`β` acts first, matching
`StarAlgEquiv.trans_apply`). -/
lemma StarAlgEquiv.trans_affiliatedObservable (β : A ≃⋆ₐ[ℂ] B) (γ : B ≃⋆ₐ[ℂ] C)
    (T : AffiliatedObservable A) :
    (β.trans γ).affiliatedObservable T = γ.affiliatedObservable (β.affiliatedObservable T) := by
  apply AffiliatedObservable.ext
  intro S _
  rw [StarAlgEquiv.affiliatedObservable_spectralMeasure_apply,
    StarAlgEquiv.affiliatedObservable_spectralMeasure_apply,
    StarAlgEquiv.affiliatedObservable_spectralMeasure_apply]
  rfl

/-- The transport along a star-algebra isomorphism is injective, since `β` itself is: two
affiliated observables with the same transported spectral measure already agreed at every set
before transporting. This is the uniqueness half of functoriality. -/
lemma StarAlgEquiv.affiliatedObservable_injective (β : A ≃⋆ₐ[ℂ] B) :
    Function.Injective
      (β.affiliatedObservable : AffiliatedObservable A → AffiliatedObservable B) := by
  intro T U h
  apply AffiliatedObservable.ext
  intro S _
  have hTU := congrArg (fun V : AffiliatedObservable B => V.spectralMeasure S) h
  simp only [StarAlgEquiv.affiliatedObservable_spectralMeasure_apply] at hTU
  exact EquivLike.injective β hTU

end StarAlgEquivAffiliatedObservable

namespace OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-! ## The canonical bounded inclusion -/

/-- The extra input needed to include bounded self-adjoint observables in the spectral-data
layer. A bare C⋆-algebra has only continuous functional calculus; a PVM requires the Borel
functional calculus supplied by a von Neumann representation (or an equivalent construction).
Keeping that input explicit prevents the canonical inclusion from hiding a nonexistent
projection-valued measure in an arbitrary C⋆-algebra. -/
class BorelFunctionalCalculus (A : Type*) [OperatorAlgebra A] where
  /-- The Borel functional-calculus spectral measure `E_a` supplied for a bounded observable
  `a : Observable A`. -/
  spectralMeasure : Observable A → PVM ℝ A
  /-- The spectral measure supplied for a bounded observable is supported in a bounded
  interval. This is the part of the bounded Borel calculus which is needed to transport the
  usual bounded-observable API to the affiliated layer. We record the bound explicitly rather
  than attempting to recover it from the mere existence of a PVM: the latter has no connection
  to the norm of the original observable. -/
  spectralSupport : ∀ a : Observable A, ∃ C : ℝ, 0 ≤ C ∧
    ∀ S : Set ℝ, MeasurableSet S → Disjoint S (Set.Icc (-C) C) →
      spectralMeasure a S = 0

namespace Observable

variable [BorelFunctionalCalculus A] (a : Observable A)

/-- The canonical inclusion of a bounded observable into the affiliated observables: `a`'s
spectral measure is the Borel functional calculus of `a` restricted to real Borel sets,
`E_a(S) = 1_S(a)`. Mathlib has no Borel functional calculus for C⋆-algebra elements yet (only the
*continuous* functional calculus); the required Borel construction is kept explicit in the
`BorelFunctionalCalculus` capability. -/
def toAffiliatedObservable (a : Observable A) : AffiliatedObservable A where
  spectralMeasure := BorelFunctionalCalculus.spectralMeasure a

/- Boundary: constructing `BorelFunctionalCalculus A` from a faithful normal representation of a
von Neumann algebra, and proving agreement with continuous functional calculus, belongs to the
von Neumann/predual layer. It is kept as an explicit capability here so arbitrary C⋆-algebras do
not acquire unjustified Borel projections. -/

/-- The bounded inclusion is compatible with the spectral projection at `univ`: it sends `a` to
an affiliated observable whose total spectral projection is `1`, i.e. it lands in genuine
probability-normalized spectral measures, matching `AffiliatedObservable.spectralProjection_univ`
automatically via the shared `PVM` structure (no extra content beyond what `PVM.univ` already
gives, recorded here as the promised "basic compatibility lemma"; already provable by `simp` via
`AffiliatedObservable.spectralProjection_univ`, so not separately tagged `@[simp]`). -/
lemma toAffiliatedObservable_spectralProjection_univ :
    (Observable.toAffiliatedObservable a).spectralProjection univ = ⟨1, IsStarProjection.one A⟩ :=
  AffiliatedObservable.spectralProjection_univ _

/- The bounded inclusion recovers `a` itself as the affiliated operator's spectral integral of
the identity — the honest compatibility statement between the bounded and affiliated pictures.
Deferred, as it depends on the same Borel functional calculus as `toAffiliatedObservable` itself
and on the measurable functional calculus of `FunctionalCalculus.lean`. -/
/- Boundary: recovering `a` from the spectral integral of the identity requires the same
von Neumann/predual realization as `BorelFunctionalCalculus`; the measurable spectral-data API
and the concrete representation bridge are available independently above. -/

end Observable

end OperatorAlgebra
