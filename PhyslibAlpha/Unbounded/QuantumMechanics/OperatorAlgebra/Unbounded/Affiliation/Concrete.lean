/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.HilbertSpace
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Affiliation.Affiliated
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Measurement.PVM
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Core.RealAnalytic
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.SpectralTheory.WeakSpectralMeasure
public import Physlib.QuantumMechanics.Operators.SpectralTheory.Symmetric
public import Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint
public import Physlib.QuantumMechanics.Operators.Unbounded
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.Core.UnboundedExtras
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!

# Concrete affiliated observables

`AffiliatedObservable A` is deliberately representation-free.  The actual spectral theorem,
however, is a theorem about a self-adjoint operator on a Hilbert space and its weak-operator
spectral measure.  This file is the representation-level API that the abstract algebraic layer
can consume once a von Neumann algebra/predual instance is available.

The important distinction is visible in the type: the spectral measure is a
`WOTSpectralMeasure`, not the norm-valued `PVM` from `Unbounded.NormalState`.

This distinction is mathematically substantive.  In infinite dimension a
spectral measure on `B(H)` is generally σ-additive only in the strong/WOT (or
normal-functional) sense; it need not be σ-additive in operator norm.  Thus
`AffiliationBridge.toPVM` is deliberately an explicit capability and cannot be
manufactured from faithfulness alone.  A future von Neumann realization should
use a normal/ultraweak PVM interface rather than silently coercing a WOT
spectral measure to the norm-valued `PVM` used by the current abstract layer.

-/

@[expose] public section

noncomputable section

open scoped ComplexOrder CStarAlgebra Topology InnerProductSpace Function
open MeasureTheory Set

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Concrete spectral data -/

/-- A self-adjoint observable represented on a Hilbert space by its weak-operator spectral
measure.  This is the representation-dependent form of an affiliated observable. -/
structure ConcreteAffiliatedObservable (α : Type*) [MeasurableSpace α]
    (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The observable's spectral measure, represented on `H`. -/
  spectralMeasure : QuantumMechanics.WOTSpectralMeasure α H

/-- A representation of an affiliated observable by a weak-operator spectral measure.

This is the public representation-level package.  The `AffiliatedObservable` is the algebraic
object, while `spectralMeasure` is its realization on `H`; the last field is the compatibility
equation saying that every abstract spectral projection is represented by the corresponding
bounded operator.  In particular, a concrete self-adjoint operator is not itself the public
object: its affiliated observable is. -/
structure RepresentedAffiliatedObservable (A H : Type*) [OperatorAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The Hilbert-space representation of `A`. -/
  representation : Representation A H
  /-- The underlying abstract affiliated observable. -/
  observable : AffiliatedObservable A
  /-- The observable's spectral measure, represented on `H`. -/
  spectralMeasure : QuantumMechanics.WOTSpectralMeasure ℝ H
  spectralProjection_apply : ∀ S : Set ℝ,
    representation (observable.spectralProjection S : A) = (spectralMeasure S).toCLM

namespace RepresentedAffiliatedObservable

variable {A : Type*} [OperatorAlgebra A]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : RepresentedAffiliatedObservable A H)

/-- Forget the abstract algebraic packaging and retain the represented WOT spectral data. -/
def toConcreteAffiliatedObservable : ConcreteAffiliatedObservable ℝ H :=
  ⟨T.spectralMeasure⟩

lemma spectralProjection_representation_apply (S : Set ℝ) :
    T.representation (T.observable.spectralProjection S : A) =
      (T.toConcreteAffiliatedObservable.spectralMeasure S).toCLM :=
  T.spectralProjection_apply S

end RepresentedAffiliatedObservable

/-! ## The representation bridge -/

/-- The extra structure needed to turn a Hilbert-space WOT spectral measure into the abstract
algebraic `PVM` used by `AffiliatedObservable`. The equality field is deliberately explicit:
it says that the abstract PVM is represented by the given bounded operators, while its
norm-valued countable additivity is the part that cannot be inferred from WOT additivity in
infinite dimension. -/
structure AffiliationBridge (A H : Type*) [OperatorAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The Hilbert-space representation of `A`. -/
  representation : Representation A H
  /-- The abstract PVM built from a WOT spectral measure. -/
  toPVM : QuantumMechanics.WOTSpectralMeasure ℝ H → PVM ℝ A
  toPVM_apply : ∀ (μS : QuantumMechanics.WOTSpectralMeasure ℝ H) (S : Set ℝ),
    representation (toPVM μS S : A) = (μS S).toCLM

namespace AffiliationBridge

variable {A : Type*} [OperatorAlgebra A]
variable (bridge : AffiliationBridge A H)

/-- Package concrete real spectral data once an explicit normal/WOT-to-PVM bridge is supplied. -/
def toAffiliatedObservable
    (T : ConcreteAffiliatedObservable ℝ H) : AffiliatedObservable A where
  spectralMeasure := bridge.toPVM T.spectralMeasure

/-- Expose the representation together with the affiliated observable and its spectral measure. -/
def toRepresentedAffiliatedObservable
    (T : ConcreteAffiliatedObservable ℝ H) :
    RepresentedAffiliatedObservable A H where
  representation := bridge.representation
  observable := bridge.toAffiliatedObservable T
  spectralMeasure := T.spectralMeasure
  spectralProjection_apply := by
    intro S
    change bridge.representation (bridge.toPVM T.spectralMeasure S : A) = _
    exact bridge.toPVM_apply T.spectralMeasure S

@[simp]
lemma toRepresentedAffiliatedObservable_observable
    (T : ConcreteAffiliatedObservable ℝ H) :
    (bridge.toRepresentedAffiliatedObservable T).observable =
      bridge.toAffiliatedObservable T := rfl

@[simp]
lemma toRepresentedAffiliatedObservable_spectralMeasure
    (T : ConcreteAffiliatedObservable ℝ H) :
    (bridge.toRepresentedAffiliatedObservable T).spectralMeasure = T.spectralMeasure := rfl

lemma toAffiliatedObservable_spectralProjection_apply
    (T : ConcreteAffiliatedObservable ℝ H) (S : Set ℝ) :
    bridge.representation ((bridge.toAffiliatedObservable T).spectralProjection S : A) =
      (T.spectralMeasure S).toCLM := by
  exact bridge.toPVM_apply T.spectralMeasure S

end AffiliationBridge

/-! ## Faithful representation bridges

The compatibility equation in `AffiliationBridge` says how an abstract projection is represented,
but it does not by itself permit recovering the abstract projection.  The missing hypothesis is
faithfulness of the representation.  We keep it as a separate extension so existing concrete
bridges do not acquire an artificial obligation, while the uniqueness statements below can use it
exactly where it is mathematically needed. -/

/-- An `AffiliationBridge` whose representation is faithful, so the abstract projection can be
recovered from its represented form. -/
structure FaithfulAffiliationBridge (A H : Type*) [OperatorAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends AffiliationBridge A H where
  /-- Distinct abstract algebra elements remain distinct after representation. -/
  faithful : Function.Injective representation

namespace FaithfulAffiliationBridge

variable {A : Type*} [OperatorAlgebra A]
variable (bridge : FaithfulAffiliationBridge A H)

lemma representation_injective : Function.Injective bridge.representation :=
  bridge.faithful

/-- A faithful bridge reflects equality of the abstract PVM values from equality of their
represented bounded operators. -/
lemma toPVM_ext
    {μ ν : QuantumMechanics.WOTSpectralMeasure ℝ H}
    (h : ∀ S : Set ℝ, MeasurableSet S →
      bridge.representation (bridge.toPVM μ S : A) =
        bridge.representation (bridge.toPVM ν S : A)) :
    bridge.toPVM μ = bridge.toPVM ν := by
  apply PVM.ext
  intro S hS
  apply bridge.faithful
  exact h S hS

/-- In a faithful representation, an affiliated observable is determined by the represented
spectral projections.  This is the uniqueness half of the abstract/concrete affiliation bridge. -/
lemma affiliatedObservable_ext
    (T U : AffiliatedObservable A)
    (h : ∀ S : Set ℝ,
      bridge.representation (T.spectralMeasure S : A) =
        bridge.representation (U.spectralMeasure S : A)) :
    T = U := by
  cases T with
  | mk μ =>
    cases U with
    | mk ν =>
      congr
      apply PVM.ext
      intro S hS
      apply bridge.faithful
      exact h S

end FaithfulAffiliationBridge

namespace ConcreteAffiliatedObservable

variable {α : Type*} [MeasurableSpace α]
variable (T : ConcreteAffiliatedObservable α H)

/-- The bounded operator underlying a weak-operator spectral projection. -/
def spectralProjection (S : Set α) : Projection B(H) :=
  ⟨(T.spectralMeasure S).toCLM, by
    refine ⟨?_, ?_⟩
    · change (T.spectralMeasure S).toCLM * (T.spectralMeasure S).toCLM =
        (T.spectralMeasure S).toCLM
      rw [← ContinuousLinearMapWOT.toCLM_mul]
      exact congrArg ContinuousLinearMapWOT.toCLM
        (T.spectralMeasure.isStarProjection S).isIdempotentElem
    · change star (T.spectralMeasure S).toCLM = (T.spectralMeasure S).toCLM
      exact congrArg ContinuousLinearMapWOT.toCLM
        (T.spectralMeasure.isStarProjection S).isSelfAdjoint⟩

lemma re_inner_nonneg (S : Set α) (x : H) :
    0 ≤ (⟪x, T.spectralMeasure S x⟫_ℂ).re := by
  let p : B(H) := (T.spectralMeasure S).toCLM
  have hp := T.spectralMeasure.isStarProjection S
  have hmul : p * p = p := by
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isIdempotentElem
  have hstar : ContinuousLinearMap.adjoint p = p := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact congrArg ContinuousLinearMapWOT.toCLM hp.isSelfAdjoint
  have hinner : ⟪x, p x⟫_ℂ = ⟪p x, p x⟫_ℂ := by
    calc
      ⟪x, p x⟫_ℂ = ⟪x, p (p x)⟫_ℂ := by
        congr 1
        exact (congrArg (fun q : B(H) => q x) hmul).symm
      _ = ⟪x, ContinuousLinearMap.adjoint p (p x)⟫_ℂ := by rw [hstar]
      _ = ⟪p x, p x⟫_ℂ := ContinuousLinearMap.adjoint_inner_right p x (p x)
  change 0 ≤ (⟪x, p x⟫_ℂ).re
  rw [hinner]
  exact inner_self_nonneg (𝕜 := ℂ) (x := p x)

/-! ## Vector-state statistics -/

/-- The probability distribution of this spectral measure in a unit vector state. -/
def vectorDistribution (x : H) (hx : ‖x‖ = 1) : ProbabilityMeasure α := by
  let m : ∀ S : Set α, MeasurableSet S → ENNReal :=
    fun S _ => ENNReal.ofReal (⟪x, T.spectralMeasure S x⟫_ℂ).re
  have hm_empty : m ∅ MeasurableSet.empty = 0 := by simp [m]
  have hm_iUnion : ∀ ⦃f : ℕ → Set α⦄ (hf : ∀ i, MeasurableSet (f i)),
      Pairwise (Disjoint on f) →
        m (⋃ i, f i) (MeasurableSet.iUnion hf) = ∑' i, m (f i) (hf i) := by
    intro f hf hdisj
    have hs := T.spectralMeasure.hasSum_inner hf hdisj x x
    have hre : HasSum (fun i ↦ (⟪x, T.spectralMeasure (f i) x⟫_ℂ).re)
        (⟪x, T.spectralMeasure (⋃ i, f i) x⟫_ℂ).re :=
      hs.map Complex.reCLM.toAddMonoidHom Complex.reCLM.continuous
    have hnonneg : ∀ i, 0 ≤ (⟪x, T.spectralMeasure (f i) x⟫_ℂ).re :=
      fun i ↦ T.re_inner_nonneg (f i) x
    dsimp [m]
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hre.summable]
    exact congrArg ENNReal.ofReal hre.tsum_eq.symm
  let μ : Measure α := Measure.ofMeasurable m hm_empty hm_iUnion
  have hμ_univ : μ Set.univ = 1 := by
    dsimp [μ]
    rw [Measure.ofMeasurable_apply _ MeasurableSet.univ]
    dsimp [m]
    rw [T.spectralMeasure.univ]
    change ENNReal.ofReal (⟪x, x⟫_ℂ).re = 1
    have hi : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
    rw [hi, hx]
    norm_num
  exact ⟨μ, ⟨hμ_univ⟩⟩

lemma vectorDistribution_apply (x : H) (hx : ‖x‖ = 1) (S : Set α)
    (hS : MeasurableSet S) :
    (T.vectorDistribution x hx : Measure α) S =
      ENNReal.ofReal (⟪x, T.spectralMeasure S x⟫_ℂ).re := by
  simp only [vectorDistribution, ProbabilityMeasure.coe_mk, Measure.ofMeasurable_apply _ hS]

@[simp]
lemma spectralProjection_apply (S : Set α) :
    (T.spectralProjection S : B(H)) = (T.spectralMeasure S).toCLM := rfl

@[simp]
lemma spectralProjection_univ : T.spectralProjection univ =
    ⟨1, IsStarProjection.one B(H)⟩ := by
  apply Subtype.ext
  rw [spectralProjection_apply, T.spectralMeasure.univ]
  rfl

lemma spectralProjection_comp_eq_of_inter {S U : Set α}
    (hS : MeasurableSet S) (hU : MeasurableSet U) :
    (T.spectralProjection S : B(H)) * T.spectralProjection U =
      T.spectralProjection (S ∩ U) := by
  rw [spectralProjection_apply, spectralProjection_apply, spectralProjection_apply,
    ← ContinuousLinearMapWOT.toCLM_mul, T.spectralMeasure.comp_eq_of_inter hS hU]

lemma spectralProjection_commute (S U : Set α) :
    Commute (T.spectralProjection S : B(H)) (T.spectralProjection U : B(H)) := by
  rw [spectralProjection_apply, spectralProjection_apply]
  change (T.spectralMeasure S).toCLM * (T.spectralMeasure U).toCLM =
    (T.spectralMeasure U).toCLM * (T.spectralMeasure S).toCLM
  rw [← ContinuousLinearMapWOT.toCLM_mul, ← ContinuousLinearMapWOT.toCLM_mul]
  exact congrArg ContinuousLinearMapWOT.toCLM (T.spectralMeasure.commute S U)

end ConcreteAffiliatedObservable

/-! ## The operator-to-spectrum interface -/

/-! ### Essential self-adjointness and closure -/

/-
The closure is not an extra choice. For a core operator `T`, essential
self-adjointness is precisely the assertion that the canonical graph closure
`T.closure` is self-adjoint. Keeping this as a small data structure gives
concrete constructions (the oscillator, multiplication operators, and later
Schrödinger operators) one common entry point without smuggling a spectral
measure into the definition.
-/

/-- The analytic input needed before applying the unbounded spectral theorem. -/
structure SelfAdjointClosureData
    (T : H →ₗ.[ℂ] H) where
  essentiallySelfAdjoint : LinearPMap.IsEssentiallySelfAdjoint T

namespace SelfAdjointClosureData

variable {T : H →ₗ.[ℂ] H} (D : SelfAdjointClosureData T)

include D

/-- Essential self-adjointness makes the canonical closure self-adjoint. -/
lemma closure_isSelfAdjoint : IsSelfAdjoint T.closure :=
  D.essentiallySelfAdjoint

/-- In particular, the canonical closure is closed. -/
lemma closure_isClosed : T.closure.IsClosed :=
  D.closure_isSelfAdjoint.isClosed

/-- The core operator is contained in its canonical self-adjoint closure. -/
@[nolint unusedArguments]
lemma le_closure : T ≤ T.closure :=
  T.le_closure

/-- The canonical closure is the unique self-adjoint extension of the core. -/
lemma unique_selfAdjoint_extension {S : H →ₗ.[ℂ] H}
    (hTS : T ≤ S) (hS : IsSelfAdjoint S) : S = T.closure :=
  LinearPMap.IsEssentiallySelfAdjoint.unique_self_adjoint_extension
    D.essentiallySelfAdjoint hTS hS

/-- Build closure data from the von Neumann defect-number criterion. -/
def ofDefectNumberEqZero
    (hT : T.IsSymmetric)
    (hdense : T.HasDenseDomain)
    (hpos : T.defectNumber Complex.I = 0)
    (hneg : T.defectNumber (-Complex.I) = 0) :
    SelfAdjointClosureData T :=
  ⟨hT.isEssentiallySelfAdjoint_of_defectNumber_eq_zero hdense hpos hneg⟩

/-- Package the reusable defect-index certificate as closure data. -/
def ofDefectIndexCertificate {T : H →ₗ.[ℂ] H}
    (C : DefectIndexCertificate T) : SelfAdjointClosureData T :=
  ⟨C.essentiallySelfAdjoint⟩

end SelfAdjointClosureData

/-- The data a concrete unbounded spectral theorem must provide for a self-adjoint `LinearPMap`.
This is an interface, not an axiom hidden in an example: the operator, essential
self-adjointness, and its weak-operator spectral measure are explicit fields.  Construction
theorems (multiplication, oscillator, Schrödinger operators) can implement this interface
independently and then reuse all affiliated-observable lemmas. -/
def IsWeakSpectralResolution
    (T : H →ₗ.[ℂ] H)
    (μS : QuantumMechanics.WOTSpectralMeasure ℝ H) : Prop :=
  ∀ x : T.domain,
    (∀ y : H, (μS.scalarMeasure (x : H) y).Integrable id) ∧
      ∀ y : H, ⟪y, T x⟫_ℂ = μS.weakIntegral id (x : H) y

/-- The self-adjoint operator is reconstructed from its spectral measure in the weak sense.
The integrability clause is essential: the identity function is generally unbounded, so this
cannot be replaced by the bounded PVM axioms alone. -/
structure SelfAdjointSpectralTheorem
    (T : H →ₗ.[ℂ] H)
    (μS : QuantumMechanics.WOTSpectralMeasure ℝ H) where
  isSelfAdjoint : IsSelfAdjoint T
  reconstruction : IsWeakSpectralResolution T μS

/-!
### The domain-aware boundary

`SelfAdjointSpectralTheorem` deliberately records only the weak identity-integral
law.  That law is enough for matrix-element reconstruction on the given domain,
but it does not say which vectors belong to the domain.  The latter is the
square-moment condition and must be stated separately before we can claim an
equality of unbounded operators.
-/

/-- The square-moment domain associated to a real weak spectral measure.

For a projection-valued measure this is the usual condition
`∫ λ² d⟪x, E(λ)x⟫ < ∞`.  It is expressed using the positive diagonal
measure, rather than the variation of a complex off-diagonal scalar measure;
this is the measure that controls the actual graph norm of the unbounded
operator. -/
def spectralSquareMomentDomain
    (μS : QuantumMechanics.WOTSpectralMeasure ℝ H) : Set H :=
  {x | Integrable (fun (r : ℝ) ↦ r ^ 2) (μS.diagonalMeasure x)}

lemma mem_spectralSquareMomentDomain_iff
    (μS : QuantumMechanics.WOTSpectralMeasure ℝ H) (x : H) :
    x ∈ spectralSquareMomentDomain μS ↔
      Integrable (fun (r : ℝ) ↦ r ^ 2) (μS.diagonalMeasure x) :=
  Iff.rfl

/-- A boundedly supported spectral measure has no domain restriction: every vector has a finite
second spectral moment.  This is the domain half of the bounded/unbounded interface and is useful
even before a spectral measure has been identified with an operator. -/
def HasBoundedSpectralSupport
    (μS : QuantumMechanics.WOTSpectralMeasure ℝ H) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ S : Set ℝ, MeasurableSet S → Disjoint S (Set.Icc (-C) C) → μS S = 0

lemma spectralSquareMomentDomain_eq_univ_of_boundedSupport
    (μS : QuantumMechanics.WOTSpectralMeasure ℝ H) {C : ℝ}
    (hC : HasBoundedSpectralSupport μS C) :
    spectralSquareMomentDomain μS = Set.univ := by
  ext x
  constructor
  · intro _
    trivial
  · intro _
    rw [mem_spectralSquareMomentDomain_iff]
    have hK : MeasurableSet (Set.Icc (-C) C) := measurableSet_Icc
    have hKc : MeasurableSet (Set.Icc (-C) C)ᶜ := hK.compl
    have hμKc : μS (Set.Icc (-C) C)ᶜ = 0 :=
    hC.2 _ hKc disjoint_compl_left
    have hdiagKc : μS.diagonalMeasure x (Set.Icc (-C) C)ᶜ = 0 := by
      rw [μS.diagonalMeasure_apply x _ hKc, hμKc]
      simp
    have hK_ae : ∀ᵐ r ∂μS.diagonalMeasure x, r ∈ Set.Icc (-C) C := by
      rw [ae_iff]
      have hset : {r : ℝ | r ∉ Set.Icc (-C) C} = (Set.Icc (-C) C)ᶜ := by
        rfl
      rw [hset]
      exact hdiagKc
    apply Integrable.of_bound (by fun_prop) (C ^ 2)
    filter_upwards [hK_ae] with r hr
    change |r ^ 2| ≤ C ^ 2
    rw [abs_of_nonneg (sq_nonneg r)]
    exact sq_le_sq' hr.1 hr.2

/-- A domain-aware concrete spectral theorem.

This is the interface required by measurable functional calculus: in addition
to self-adjointness and weak reconstruction, it identifies the operator domain
with the square-moment domain of the PVM.  The Cayley spectral-data theorem and
the maximal-integral uniqueness theorem construct this package for every
self-adjoint `LinearPMap`; model-specific work remains only for proving
self-adjointness of a smaller core and identifying its closure. -/
structure DomainAwareSelfAdjointSpectralTheorem
    (T : H →ₗ.[ℂ] H)
    (μS : QuantumMechanics.WOTSpectralMeasure ℝ H)
    extends SelfAdjointSpectralTheorem T μS where
  domain_eq_squareMoment : T.domain = spectralSquareMomentDomain μS

namespace DomainAwareSelfAdjointSpectralTheorem

variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

/-- A bounded self-adjoint realization automatically has the maximal square-moment domain when
its spectral measure is boundedly supported. -/
def ofBoundedSupport (D : SelfAdjointSpectralTheorem T μS)
    (hdom : (T.domain : Set H) = Set.univ) {C : ℝ}
    (hC : HasBoundedSpectralSupport μS C) :
    DomainAwareSelfAdjointSpectralTheorem T μS where
  toSelfAdjointSpectralTheorem := D
  domain_eq_squareMoment :=
    hdom.trans (spectralSquareMomentDomain_eq_univ_of_boundedSupport μS hC).symm

/-- The self-adjointness part of a domain-aware spectral theorem. -/
lemma isSelfAdjoint_of (D : DomainAwareSelfAdjointSpectralTheorem T μS) :
    IsSelfAdjoint T :=
  D.toSelfAdjointSpectralTheorem.isSelfAdjoint

/-- The weak reconstruction part of a domain-aware spectral theorem. -/
lemma reconstruction_of (D : DomainAwareSelfAdjointSpectralTheorem T μS) :
    IsWeakSpectralResolution T μS :=
  D.toSelfAdjointSpectralTheorem.reconstruction

/-- The domain is exactly the vectors with finite second spectral moment. -/
lemma mem_domain_iff (D : DomainAwareSelfAdjointSpectralTheorem T μS) (x : H) :
    x ∈ T.domain ↔ x ∈ spectralSquareMomentDomain μS := by
  change x ∈ (T.domain : Set H) ↔ x ∈ spectralSquareMomentDomain μS
  rw [D.domain_eq_squareMoment]

/-- The strongly continuous unitary group attached to a domain-aware spectral theorem.  Its strong
Stone generator and exact generator domain are proved in `Unbounded.Stone`. -/
@[nolint unusedArguments]
noncomputable def expUnitaryGroup
    (D : DomainAwareSelfAdjointSpectralTheorem T μS) :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup H :=
  QuantumMechanics.WOTSpectralMeasure.expUnitaryGroup μS

lemma expUnitaryGroup_zero (D : DomainAwareSelfAdjointSpectralTheorem T μS) :
    D.expUnitaryGroup 0 = 1 := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.zero _

lemma expUnitaryGroup_add (D : DomainAwareSelfAdjointSpectralTheorem T μS) (t s : ℝ) :
    D.expUnitaryGroup (t + s) = D.expUnitaryGroup t * D.expUnitaryGroup s := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.add _ t s

lemma expUnitaryGroup_continuous_apply
    (D : DomainAwareSelfAdjointSpectralTheorem T μS) (x : H) :
    Continuous (fun t => D.expUnitaryGroup t x) := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.continuous_apply _ x

end DomainAwareSelfAdjointSpectralTheorem

namespace SelfAdjointSpectralTheorem

variable {T : H →ₗ.[ℂ] H} {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

/-- Transport an unbounded spectral theorem through a Hilbert-space unitary.  This is the
representation-level engine: once the theorem is proved for a multiplication model, this
constructor gives it for every unitarily equivalent self-adjoint operator. -/
def unitaryConj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (D : SelfAdjointSpectralTheorem T μS) (u : H ≃ₗᵢ[ℂ] H') :
    SelfAdjointSpectralTheorem (LinearPMap.unitaryConj u T)
      (QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u μS) where
  isSelfAdjoint := LinearPMap.unitaryConj_isSelfAdjoint u D.isSelfAdjoint
  reconstruction := by
    intro x
    let x' : T.domain :=
      ⟨u.symm (x : H'), (LinearPMap.mem_unitaryConj_domain_iff u T).mp x.2⟩
    refine ⟨?_, ?_⟩
    · intro y
      rw [QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure_scalarMeasure]
      exact (D.reconstruction x').1 (u.symm y)
    · intro y
      have h := (D.reconstruction x').2 (u.symm y)
      calc
        ⟪y, LinearPMap.unitaryConj u T x⟫_ℂ = ⟪u.symm y, T x'⟫_ℂ := by
          rw [LinearPMap.unitaryConj_apply]
          exact (u.symm.inner_map_eq_flip _ _).symm
        _ = μS.weakIntegral id (x' : H) (u.symm y) := h
        _ = (QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u μS).weakIntegral
            id (x : H') y := by
          symm
          exact QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure_weakIntegral
            u μS id x y

end SelfAdjointSpectralTheorem

namespace DomainAwareSelfAdjointSpectralTheorem

variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

/-- Transport the domain-aware theorem through a Hilbert-space unitary.  The only
additional input beyond the weak transport is the diagonal-measure equivariance
lemma, which makes the square-moment domain equivariant as well. -/
def unitaryConj {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [CompleteSpace H'] (D : DomainAwareSelfAdjointSpectralTheorem T μS)
    (u : H ≃ₗᵢ[ℂ] H') :
    DomainAwareSelfAdjointSpectralTheorem (LinearPMap.unitaryConj u T)
      (QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u μS) where
  toSelfAdjointSpectralTheorem := D.toSelfAdjointSpectralTheorem.unitaryConj u
  domain_eq_squareMoment := by
    ext x
    change x ∈ (LinearPMap.unitaryConj u T).domain ↔
      x ∈ spectralSquareMomentDomain
        (QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u μS)
    rw [LinearPMap.mem_unitaryConj_domain_iff]
    change u.symm x ∈ T.domain ↔
      Integrable (fun r : ℝ ↦ r ^ 2)
        ((QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure u μS).diagonalMeasure x)
    rw [QuantumMechanics.WOTSpectralMeasure.unitaryConjSpectralMeasure_diagonalMeasure]
    exact D.mem_domain_iff (u.symm x)

end DomainAwareSelfAdjointSpectralTheorem

/-- A self-adjoint operator together with its weak-operator spectral measure and the
corresponding spectral theorem. -/
structure SelfAdjointSpectralData
    (T : H →ₗ.[ℂ] H) where
  isSelfAdjoint : IsSelfAdjoint T
  /-- The operator's spectral measure. -/
  spectralMeasure : QuantumMechanics.WOTSpectralMeasure ℝ H
  spectralTheorem : SelfAdjointSpectralTheorem T spectralMeasure

/-- A spectral-data package built from an essentially self-adjoint operator. The closure is the
self-adjoint operator represented by the spectral measure, and `spectralTheorem` records both the
weak unbounded integral law and the exact square-moment domain. -/
structure EssentialSelfAdjointSpectralData
    (T : H →ₗ.[ℂ] H) where
  essentiallySelfAdjoint : LinearPMap.IsEssentiallySelfAdjoint T
  /-- The operator's spectral measure (of the closure). -/
  spectralMeasure : QuantumMechanics.WOTSpectralMeasure ℝ H
  spectralTheorem : DomainAwareSelfAdjointSpectralTheorem T.closure spectralMeasure

namespace EssentialSelfAdjointSpectralData

variable {T : H →ₗ.[ℂ] H} (D : EssentialSelfAdjointSpectralData T)

include D

lemma closure_isSelfAdjoint : IsSelfAdjoint T.closure :=
  EssentialSelfAdjointSpectralData.essentiallySelfAdjoint D

lemma spectralReconstruction : IsWeakSpectralResolution T.closure D.spectralMeasure :=
  D.spectralTheorem.reconstruction_of

lemma spectralDomain : T.closure.domain = spectralSquareMomentDomain D.spectralMeasure :=
  D.spectralTheorem.domain_eq_squareMoment

/-- The closure portion of the spectral data, separated from the still-to-be-proved
operator-to-PVM reconstruction theorem. -/
def closureData : SelfAdjointClosureData T :=
  ⟨D.essentiallySelfAdjoint⟩

lemma closure_isClosed : T.closure.IsClosed :=
  SelfAdjointClosureData.closure_isClosed D.closureData

lemma le_closure : T ≤ T.closure :=
  SelfAdjointClosureData.le_closure D.closureData

lemma unique_selfAdjoint_extension {S : H →ₗ.[ℂ] H}
    (hTS : T ≤ S) (hS : IsSelfAdjoint S) : S = T.closure :=
  SelfAdjointClosureData.unique_selfAdjoint_extension D.closureData hTS hS

/-- The closure's spectral data, forgetting the algebraic packaging. -/
def toConcreteAffiliatedObservable : ConcreteAffiliatedObservable ℝ H :=
  ⟨D.spectralMeasure⟩

/-- The public affiliated-observable endpoint of the concrete analytic pipeline.

The `LinearPMap` and weak spectral measure are proof data for a represented realization; the
object exported to the operator-algebra API is an `AffiliatedObservable`.  The bridge is explicit
because a WOT-countably-additive spectral measure need not be norm-countably-additive in an
infinite-dimensional operator algebra. -/
def toAffiliatedObservable {A : Type*} [OperatorAlgebra A]
    (bridge : AffiliationBridge A H) : AffiliatedObservable A :=
  bridge.toAffiliatedObservable D.toConcreteAffiliatedObservable

/-- The same construction with the representation and compatibility equation exposed. -/
def toRepresentedAffiliatedObservable {A : Type*} [OperatorAlgebra A]
    (bridge : AffiliationBridge A H) : RepresentedAffiliatedObservable A H :=
  bridge.toRepresentedAffiliatedObservable D.toConcreteAffiliatedObservable

lemma toAffiliatedObservable_spectralProjection_apply {A : Type*} [OperatorAlgebra A]
    (bridge : AffiliationBridge A H)
    (S : Set ℝ) :
    bridge.representation ((D.toAffiliatedObservable bridge).spectralProjection S : A) =
      (D.spectralMeasure S).toCLM := by
  exact bridge.toPVM_apply D.spectralMeasure S

end EssentialSelfAdjointSpectralData

end OperatorAlgebra

end
