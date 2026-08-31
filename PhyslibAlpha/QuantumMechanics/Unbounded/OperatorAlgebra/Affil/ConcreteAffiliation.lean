/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.UnitaryCovariance
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Flow.NegativeStoneAPI
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Core.ClosureAPI
public import Mathlib.Analysis.VonNeumannAlgebra.Basic

/-!
# Concrete affiliation through the Cayley transform

For a concrete von Neumann algebra `M ⊆ B(H)`, a self-adjoint operator is affiliated to `M`
when its bounded Cayley spectral projections belong to `M`.  Mathlib's concrete
von Neumann algebra is defined by the double commutant, so this is equivalent to commuting
with every bounded operator in `M'`.

This file is deliberately phrased using the Cayley-side spectral measure already constructed in
`CayleySpectralData.lean`.  Thus it does not assume a bounded transform theorem: the bounded
transform is the Cayley spectral measure itself, and the unbounded operator is recovered by the
existing domain-aware Cayley spectral theorem.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace
open MeasureTheory Set

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace VonNeumannAlgebra

/-! ### The projection-level commutant criterion -/

lemma cayleySpectralProjection_isStarProjection
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (S : Set ℂ) :
    IsStarProjection
      (ContinuousLinearMapWOT.toCLM (cayleyBoundedSpectralMeasure T hT S)) := by
  refine ⟨?_, ?_⟩
  · change (ContinuousLinearMapWOT.toCLM (cayleyBoundedSpectralMeasure T hT S)) *
      (ContinuousLinearMapWOT.toCLM (cayleyBoundedSpectralMeasure T hT S)) = _
    simpa only [ContinuousLinearMapWOT.toCLM_mul] using
      congrArg ContinuousLinearMapWOT.toCLM
        ((cayleyBoundedSpectralMeasure T hT).comp_self S)
  · change (star (cayleyBoundedSpectralMeasure T hT S)).toCLM = _
    rw [(cayleyBoundedSpectralMeasure T hT).isStarProjection S |>.isSelfAdjoint]

lemma realSpectralProjection_isStarProjection
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) (S : Set ℝ) :
    IsStarProjection
      (ContinuousLinearMapWOT.toCLM (cayleyRealSpectralMeasure T hT S)) := by
  refine ⟨?_, ?_⟩
  · change (ContinuousLinearMapWOT.toCLM (cayleyRealSpectralMeasure T hT S)) *
      (ContinuousLinearMapWOT.toCLM (cayleyRealSpectralMeasure T hT S)) = _
    simpa only [ContinuousLinearMapWOT.toCLM_mul] using
      congrArg ContinuousLinearMapWOT.toCLM
        ((cayleyRealSpectralMeasure T hT).comp_self S)
  · change (star (cayleyRealSpectralMeasure T hT S)).toCLM = _
    rw [(cayleyRealSpectralMeasure T hT).isStarProjection S |>.isSelfAdjoint]

lemma projection_mem_iff_commutes_commutant
    {e : H →L[ℂ] H} (he : IsStarProjection e) (M : VonNeumannAlgebra H) :
    e ∈ M ↔ ∀ y ∈ M.commutant, Commute y e := by
  constructor
  · intro hem y hym
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hym) e hem |>.symm
  · intro h
    apply (VonNeumannAlgebra.IsStarProjection.mem_iff he M).2
    intro y hym
    have hie : IsIdempotentElem e := he.isIdempotentElem
    apply ContinuousLinearMap.IsIdempotentElem.range_mem_invtSubmodule hie
    apply ContinuousLinearMap.ext
    intro x
    change e (y (e x)) = y (e x)
    have hxy := congrArg (fun f : H →L[ℂ] H => f x) (h y hym).eq
    have hxy' : y (e x) = e (y x) := by
      simpa only [mul_apply_eq_comp] using hxy
    have hee := congrArg (fun f : H →L[ℂ] H => f (y x)) he.isIdempotentElem
    have hee' : e (e (y x)) = e (y x) := by
      simpa only [mul_apply_eq_comp] using hee
    calc
      e (y (e x)) = e (e (y x)) := by rw [hxy']
      _ = e (y x) := hee'
      _ = y (e x) := hxy'.symm

/-! ### Self-adjoint affiliation -/

/-- Concrete affiliation of a self-adjoint operator to a von Neumann algebra.

The definition uses the bounded Cayley spectral projections.  This is equivalent to the usual
statement that every spectral projection belongs to `M`; the Cayley transform is injective on the
real line and its pushforward identifies the two spectral measures.
-/
def IsAffiliated (M : VonNeumannAlgebra H) (T : H →ₗ.[ℂ] H)
    (hT : IsSelfAdjoint T) : Prop :=
  ∀ S : Set ℂ, MeasurableSet S →
    ContinuousLinearMapWOT.toCLM (cayleyBoundedSpectralMeasure T hT S) ∈ M

namespace IsAffiliated

variable {M : VonNeumannAlgebra H} {T : H →ₗ.[ℂ] H} {hT : IsSelfAdjoint T}

lemma mono {N : VonNeumannAlgebra H} (hMN : M ≤ N) (h : IsAffiliated M T hT) :
    IsAffiliated N T hT := by
  intro S hS
  exact hMN (h S hS)

lemma cayleyProjection_mem (h : IsAffiliated M T hT) (S : Set ℂ) (hS : MeasurableSet S) :
    ContinuousLinearMapWOT.toCLM (cayleyBoundedSpectralMeasure T hT S) ∈ M :=
  h S hS

lemma cayleyProjection_commutes_commutant (h : IsAffiliated M T hT)
    {S : Set ℂ} (hS : MeasurableSet S) {y : H →L[ℂ] H} (hy : y ∈ M.commutant) :
    Commute y (ContinuousLinearMapWOT.toCLM (cayleyBoundedSpectralMeasure T hT S)) := by
  exact (projection_mem_iff_commutes_commutant
    (cayleySpectralProjection_isStarProjection T hT S) M).mp (h S hS) y hy

/-! ### The usual unitary-commutant consequences -/

/-- An affiliated self-adjoint operator is fixed by conjugation with every unitary in the
commutant.  The proof uses the Cayley transform to reduce the unbounded statement to the bounded
spectral projections, then invokes the domain-aware self-adjoint spectral theorem. -/
lemma unitaryConj_eq (h : IsAffiliated M T hT) (u : H ≃ₗᵢ[ℂ] H)
    (hu : u.toLinearIsometry.toContinuousLinearMap ∈ M.commutant) :
    LinearPMap.unitaryConj u T = T := by
  apply SelfAdjointSpectralTheorem.unitaryConj_eq_of_cayley_projection_commute T hT u
  intro S hS
  exact h.cayleyProjection_commutes_commutant hS hu

/-- The Stone group of an affiliated self-adjoint operator is fixed by every commutant unitary. -/
lemma expIntegral_eq (h : IsAffiliated M T hT) (u : H ≃ₗᵢ[ℂ] H)
    (hu : u.toLinearIsometry.toContinuousLinearMap ∈ M.commutant) (t : ℝ) :
    QuantumMechanics.WOTSpectralMeasure.unitaryConj u
        (QuantumMechanics.WOTSpectralMeasure.expIntegral
          (cayleyRealSpectralMeasure T hT) t) =
      QuantumMechanics.WOTSpectralMeasure.expIntegral
        (cayleyRealSpectralMeasure T hT) t := by
  apply SelfAdjointSpectralTheorem.expIntegral_eq_of_cayley_projection_commute T hT u
  intro S hS
  exact h.cayleyProjection_commutes_commutant hS hu

lemma iff_cayleyProjection_commutes_commutant :
    IsAffiliated M T hT ↔
      ∀ S : Set ℂ, MeasurableSet S → ∀ y ∈ M.commutant,
        Commute y (ContinuousLinearMapWOT.toCLM
          (cayleyBoundedSpectralMeasure T hT S)) := by
  constructor
  · intro h S hS y hy
    exact cayleyProjection_commutes_commutant h hS hy
  · intro h S hS
    apply (projection_mem_iff_commutes_commutant
      (cayleySpectralProjection_isStarProjection T hT S) M).mpr
    intro y hy
    exact h S hS y hy

end IsAffiliated

/-! ### Bundled affiliated self-adjoint operators -/

/-- A self-adjoint Hilbert-space operator affiliated with a concrete von Neumann algebra.

This is the convenient object-level API corresponding to `IsAffiliated`: the operator and its
self-adjointness proof are stored once, while the Cayley spectral-projection condition supplies
the affiliation certificate.  All spectral and dynamical consequences can then be accessed
without repeating the dependent self-adjointness argument at every call site. -/
structure AffiliatedSelfAdjointOperator (M : VonNeumannAlgebra H) where
  /-- The underlying (partially defined) operator. -/
  operator : H →ₗ.[ℂ] H
  isSelfAdjoint : IsSelfAdjoint operator
  affiliated : IsAffiliated M operator isSelfAdjoint

namespace AffiliatedSelfAdjointOperator

variable {M : VonNeumannAlgebra H}

/-! ### Handoffs from model-specific cores -/

/-- Package the canonical closure of an essentially self-adjoint model core as a concrete
affiliated self-adjoint operator.

This is the intended boundary between model analysis and the general affiliation API: a model
proves essential self-adjointness in `ClosureAPI`, and separately proves that the closure's Cayley
spectral projections lie in the chosen concrete von Neumann algebra.  Once those facts are
provided, all spectral and Stone accessors below apply to the closure without duplicating the
dependent self-adjointness proof. -/
noncomputable def ofEssentialSelfAdjointCore
    (C : EssentialSelfAdjointCore (H := H))
    (hAff : IsAffiliated M C.closure C.closure_isSelfAdjoint) :
    AffiliatedSelfAdjointOperator M :=
  { operator := C.closure
    isSelfAdjoint := C.closure_isSelfAdjoint
    affiliated := hAff }

@[simp]
lemma ofEssentialSelfAdjointCore_operator
    (C : EssentialSelfAdjointCore (H := H))
    (hAff : IsAffiliated M C.closure C.closure_isSelfAdjoint) :
    (ofEssentialSelfAdjointCore C hAff).operator = C.closure := rfl

/-- Affiliation is monotone in the ambient concrete von Neumann algebra. -/
def mono {N : VonNeumannAlgebra H} (hMN : M ≤ N)
    (T : AffiliatedSelfAdjointOperator M) : AffiliatedSelfAdjointOperator N :=
  { operator := T.operator
    isSelfAdjoint := T.isSelfAdjoint
    affiliated := T.affiliated.mono hMN }

@[simp]
lemma mono_operator {N : VonNeumannAlgebra H} (hMN : M ≤ N)
    (T : AffiliatedSelfAdjointOperator M) : (T.mono hMN).operator = T.operator := rfl

end AffiliatedSelfAdjointOperator

/-- The full concrete von Neumann algebra `B(H)`.  Mathlib currently does not install a `Top`
instance for `VonNeumannAlgebra`, so the full algebra is named explicitly. -/
noncomputable def full : VonNeumannAlgebra H where
  toStarSubalgebra := ⊤
  centralizer_centralizer' := by simp

@[simp]
lemma mem_full (e : H →L[ℂ] H) : e ∈ full := by
  change e ∈ (⊤ : StarSubalgebra ℂ (H →L[ℂ] H))
  simp

/-- Every self-adjoint operator is affiliated to the full concrete algebra `B(H)`. -/
lemma full_isAffiliated (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    IsAffiliated full T hT := by
  intro S hS
  exact mem_full _

/-- Package any self-adjoint Hilbert-space operator as an affiliated operator in `B(H)`. -/
noncomputable def fullAffiliatedSelfAdjointOperator
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    AffiliatedSelfAdjointOperator (full (H := H)) :=
  { operator := T
    isSelfAdjoint := hT
    affiliated := full_isAffiliated T hT }

@[simp]
lemma fullAffiliatedSelfAdjointOperator_operator
    (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    (fullAffiliatedSelfAdjointOperator T hT).operator = T := rfl

/-! ### Interaction with the unbounded spectral theorem -/

lemma affiliated_of_cayleyProjection_commutes_commutant
    (M : VonNeumannAlgebra H) (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T)
    (hcomm : ∀ S : Set ℂ, MeasurableSet S → ∀ y ∈ M.commutant,
      Commute y (ContinuousLinearMapWOT.toCLM
        (cayleyBoundedSpectralMeasure T hT S))) :
    IsAffiliated M T hT :=
  (IsAffiliated.iff_cayleyProjection_commutes_commutant).2 hcomm

namespace AffiliatedSelfAdjointOperator

variable {M : VonNeumannAlgebra H}

/-- Construct the affiliated closure directly from the usual concrete commutant certificate.

This constructor is convenient for models whose natural proof is that every Cayley spectral
projection commutes with the commutant of `M`; it packages the certificate through the projection
criterion and exposes the same domain-aware spectral and Stone API as
`ofEssentialSelfAdjointCore`. -/
noncomputable def ofEssentialSelfAdjointCoreOfCayleyProjectionCommutesCommutant
    (C : EssentialSelfAdjointCore (H := H))
    (hcomm : ∀ S : Set ℂ, MeasurableSet S → ∀ y ∈ M.commutant,
      Commute y (ContinuousLinearMapWOT.toCLM
        (cayleyBoundedSpectralMeasure C.closure C.closure_isSelfAdjoint S))) :
    AffiliatedSelfAdjointOperator M :=
  ofEssentialSelfAdjointCore C
    (affiliated_of_cayleyProjection_commutes_commutant M C.closure C.closure_isSelfAdjoint hcomm)

@[simp]
lemma ofEssentialSelfAdjointCore_of_cayleyProjection_commutes_commutant_operator
    (C : EssentialSelfAdjointCore (H := H))
    (hcomm : ∀ S : Set ℂ, MeasurableSet S → ∀ y ∈ M.commutant,
      Commute y (ContinuousLinearMapWOT.toCLM
        (cayleyBoundedSpectralMeasure C.closure C.closure_isSelfAdjoint S))) :
    (ofEssentialSelfAdjointCoreOfCayleyProjectionCommutesCommutant C hcomm).operator =
      C.closure := rfl

end AffiliatedSelfAdjointOperator

/-- The Cayley-side definition is equivalent to the usual spectral-projection definition.

The forward direction pulls a measurable real set back along `cayleyInverse`; the reverse
direction uses the direct map formula for `cayleyMap`.  No assumption about a Borel inverse on all
of `ℂ` is needed, because the real-to-circle Cayley map is used in the forward direction and its
explicit inverse in the reverse direction.
-/
lemma isAffiliated_iff_realSpectralProjection_mem
    (M : VonNeumannAlgebra H) (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    IsAffiliated M T hT ↔
      ∀ S : Set ℝ, MeasurableSet S →
        ContinuousLinearMapWOT.toCLM (cayleyRealSpectralMeasure T hT S) ∈ M := by
  constructor
  · intro h S hS
    let U : Set ℂ := cayleyInverse ⁻¹' S
    have hU : MeasurableSet U := hS.preimage measurable_cayleyInverse
    have hmem := h U hU
    have hmap := cayleyMap_cayleyRealSpectralMeasure T hT
    have hmapU : cayleyBoundedSpectralMeasure T hT U =
        (QuantumMechanics.WOTSpectralMeasure.cayleyMap
          (cayleyRealSpectralMeasure T hT)) U := by
      rw [hmap]
    have hreal : (QuantumMechanics.WOTSpectralMeasure.cayleyMap
          (cayleyRealSpectralMeasure T hT)) U =
        cayleyRealSpectralMeasure T hT S := by
      change (cayleyRealSpectralMeasure T hT).map cayley measurable_cayley U = _
      rw [(cayleyRealSpectralMeasure T hT).map_apply cayley measurable_cayley hU]
      congr 1
      ext x
      simp [U, Set.mem_preimage, cayleyInverse_cayley]
    rw [← hreal, ← hmapU]
    exact hmem
  · intro h S hS
    have hmap := cayleyMap_cayleyRealSpectralMeasure T hT
    have hmapS : cayleyBoundedSpectralMeasure T hT S =
        (QuantumMechanics.WOTSpectralMeasure.cayleyMap
          (cayleyRealSpectralMeasure T hT)) S := by
      rw [hmap]
    rw [hmapS]
    change ContinuousLinearMapWOT.toCLM
      ((cayleyRealSpectralMeasure T hT).map cayley measurable_cayley S) ∈ M
    rw [(cayleyRealSpectralMeasure T hT).map_apply cayley measurable_cayley hS]
    exact h (cayley ⁻¹' S) (hS.preimage measurable_cayley)

namespace AffiliatedSelfAdjointOperator

variable {M : VonNeumannAlgebra H}

/-- Construct the affiliated closure from membership of all real spectral projections in the
chosen concrete von Neumann algebra. -/
noncomputable def ofEssentialSelfAdjointCoreOfRealSpectralProjectionMem
    (C : EssentialSelfAdjointCore (H := H))
    (hmem : ∀ S : Set ℝ, MeasurableSet S →
      ContinuousLinearMapWOT.toCLM
        (cayleyRealSpectralMeasure C.closure C.closure_isSelfAdjoint S) ∈ M) :
    AffiliatedSelfAdjointOperator M :=
  ofEssentialSelfAdjointCore C
    ((isAffiliated_iff_realSpectralProjection_mem
      M C.closure C.closure_isSelfAdjoint).2 hmem)

@[simp]
lemma ofEssentialSelfAdjointCore_of_realSpectralProjection_mem_operator
    (C : EssentialSelfAdjointCore (H := H))
    (hmem : ∀ S : Set ℝ, MeasurableSet S →
      ContinuousLinearMapWOT.toCLM
        (cayleyRealSpectralMeasure C.closure C.closure_isSelfAdjoint S) ∈ M) :
    (ofEssentialSelfAdjointCoreOfRealSpectralProjectionMem C hmem).operator = C.closure := rfl

end AffiliatedSelfAdjointOperator

lemma isAffiliated_iff_realSpectralProjection_commutes_commutant
    (M : VonNeumannAlgebra H) (T : H →ₗ.[ℂ] H) (hT : IsSelfAdjoint T) :
    IsAffiliated M T hT ↔
      ∀ S : Set ℝ, MeasurableSet S → ∀ y ∈ M.commutant,
        Commute y (ContinuousLinearMapWOT.toCLM
          (cayleyRealSpectralMeasure T hT S)) := by
  constructor
  · intro h S hS y hy
    exact (projection_mem_iff_commutes_commutant
      (realSpectralProjection_isStarProjection T hT S) M).mp
      ((isAffiliated_iff_realSpectralProjection_mem M T hT).mp h S hS) y hy
  · intro h
    apply (isAffiliated_iff_realSpectralProjection_mem M T hT).mpr
    intro S hS
    apply (projection_mem_iff_commutes_commutant
      (realSpectralProjection_isStarProjection T hT S) M).mpr
    intro y hy
    exact h S hS y hy

namespace AffiliatedSelfAdjointOperator

variable {M : VonNeumannAlgebra H} (T : AffiliatedSelfAdjointOperator M)

/-- Construct the affiliated closure from commutation of its real spectral projections with the
commutant.  This is the real-coordinate model-facing form of
`ofEssentialSelfAdjointCoreOfCayleyProjectionCommutesCommutant`. -/
noncomputable def ofEssentialSelfAdjointCoreOfRealSpectralProjectionCommutesCommutant
    (C : EssentialSelfAdjointCore (H := H))
    (hcomm : ∀ S : Set ℝ, MeasurableSet S → ∀ y ∈ M.commutant,
      Commute y (ContinuousLinearMapWOT.toCLM
        (cayleyRealSpectralMeasure C.closure C.closure_isSelfAdjoint S))) :
    AffiliatedSelfAdjointOperator M :=
  ofEssentialSelfAdjointCore C
    ((isAffiliated_iff_realSpectralProjection_commutes_commutant
      M C.closure C.closure_isSelfAdjoint).2 hcomm)

@[simp]
lemma ofEssentialSelfAdjointCore_of_realSpectralProjection_commutes_commutant_operator
    (C : EssentialSelfAdjointCore (H := H))
    (hcomm : ∀ S : Set ℝ, MeasurableSet S → ∀ y ∈ M.commutant,
      Commute y (ContinuousLinearMapWOT.toCLM
        (cayleyRealSpectralMeasure C.closure C.closure_isSelfAdjoint S))) :
    (ofEssentialSelfAdjointCoreOfRealSpectralProjectionCommutesCommutant C hcomm).operator =
      C.closure := rfl

/-- The canonical real spectral measure of the affiliated operator. -/
noncomputable abbrev spectralMeasure : QuantumMechanics.WOTSpectralMeasure ℝ H :=
  cayleyRealSpectralMeasure T.operator T.isSelfAdjoint

/-- The domain-aware unbounded spectral theorem attached to the affiliated operator. -/
noncomputable abbrev spectralTheorem :
    DomainAwareSelfAdjointSpectralTheorem T.operator T.spectralMeasure :=
  unboundedSpectralTheorem T.operator T.isSelfAdjoint

lemma operator_isSelfAdjoint : IsSelfAdjoint T.operator := T.isSelfAdjoint

lemma maximalSpectralIntegral_eq :
    QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral T.spectralMeasure =
      T.operator :=
  T.spectralTheorem.maximal_eq

lemma domain_eq_squareMoment :
    T.operator.domain = spectralSquareMomentDomain T.spectralMeasure :=
  T.spectralTheorem.domain_eq_squareMoment

/-! ### The Stone groups -/

/-- The canonical `exp (i t T)` group generated by the affiliated operator. -/
noncomputable abbrev expUnitaryGroup :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup H :=
  T.spectralTheorem.expUnitaryGroup

/-- The conventional quantum-dynamics group `exp (-i t T)`. -/
noncomputable abbrev negativeExpUnitaryGroup :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup H :=
  DomainAwareSelfAdjointSpectralTheorem.negativeExpUnitaryGroup T.spectralTheorem

lemma expUnitaryGroup_zero : T.expUnitaryGroup 0 = 1 :=
  T.spectralTheorem.expUnitaryGroup_zero

lemma expUnitaryGroup_add (t s : ℝ) :
    T.expUnitaryGroup (t + s) = T.expUnitaryGroup t * T.expUnitaryGroup s :=
  T.spectralTheorem.expUnitaryGroup_add t s

lemma expUnitaryGroup_continuous_apply (x : H) :
    Continuous (fun t => T.expUnitaryGroup t x) :=
  T.spectralTheorem.expUnitaryGroup_continuous_apply x

lemma expUnitaryGroup_hasDerivAt_zero_iff (x y : H) :
    HasDerivAt (fun t : ℝ => T.expUnitaryGroup t x) y 0 ↔
      ∃ hx : x ∈ T.operator.domain,
        y = Complex.I • T.operator ⟨x, hx⟩ :=
  T.spectralTheorem.expUnitaryGroup_hasDerivAt_zero_iff x y

lemma expUnitaryGroup_mem_domain_iff_hasDerivAt (x : H) (s : ℝ) :
    x ∈ T.operator.domain ↔
      ∃ y : H, HasDerivAt (fun t : ℝ => T.expUnitaryGroup t x) y s :=
  T.spectralTheorem.mem_domain_iff_expUnitaryGroup_hasDerivAt x s

lemma expUnitaryGroup_hasDerivAt_iff (x y : H) (s : ℝ) :
    HasDerivAt (fun t : ℝ => T.expUnitaryGroup t x) y s ↔
      ∃ hx : x ∈ T.operator.domain,
        y = T.expUnitaryGroup s (Complex.I • T.operator ⟨x, hx⟩) :=
  T.spectralTheorem.expUnitaryGroup_hasDerivAt_iff x y s

lemma negativeExpUnitaryGroup_zero : T.negativeExpUnitaryGroup 0 = 1 :=
  DomainAwareSelfAdjointSpectralTheorem.negativeExpUnitaryGroup_zero T.spectralTheorem

lemma negativeExpUnitaryGroup_add (t s : ℝ) :
    T.negativeExpUnitaryGroup (t + s) =
      T.negativeExpUnitaryGroup t * T.negativeExpUnitaryGroup s :=
  DomainAwareSelfAdjointSpectralTheorem.negativeExpUnitaryGroup_add T.spectralTheorem t s

lemma negativeExpUnitaryGroup_continuous_apply (x : H) :
    Continuous (fun t => T.negativeExpUnitaryGroup t x) :=
  DomainAwareSelfAdjointSpectralTheorem.negativeExpUnitaryGroup_continuous_apply
    T.spectralTheorem x

lemma negativeExpUnitaryGroup_hasDerivAt_zero_iff (x y : H) :
    HasDerivAt (fun t : ℝ => T.negativeExpUnitaryGroup t x) y 0 ↔
      ∃ hx : x ∈ T.operator.domain,
        y = -Complex.I • T.operator ⟨x, hx⟩ :=
  DomainAwareSelfAdjointSpectralTheorem.negativeExpUnitaryGroup_hasDerivAt_zero_iff
    T.spectralTheorem x y

lemma negativeExpUnitaryGroup_mem_domain_iff_hasDerivAt (x : H) (s : ℝ) :
    x ∈ T.operator.domain ↔
      ∃ y : H, HasDerivAt (fun t : ℝ => T.negativeExpUnitaryGroup t x) y s :=
  DomainAwareSelfAdjointSpectralTheorem.mem_domain_iff_negativeExpUnitaryGroup_hasDerivAt
    T.spectralTheorem x s

lemma negativeExpUnitaryGroup_hasDerivAt_iff (x y : H) (s : ℝ) :
    HasDerivAt (fun t : ℝ => T.negativeExpUnitaryGroup t x) y s ↔
      ∃ hx : x ∈ T.operator.domain,
        y = T.negativeExpUnitaryGroup s (-Complex.I • T.operator ⟨x, hx⟩) :=
  DomainAwareSelfAdjointSpectralTheorem.negativeExpUnitaryGroup_hasDerivAt_iff
    T.spectralTheorem x y s

lemma cayleyProjection_mem (S : Set ℂ) (hS : MeasurableSet S) :
    ContinuousLinearMapWOT.toCLM
        (cayleyBoundedSpectralMeasure T.operator T.isSelfAdjoint S) ∈ M :=
  T.affiliated.cayleyProjection_mem S hS

lemma realSpectralProjection_mem (S : Set ℝ) (hS : MeasurableSet S) :
    ContinuousLinearMapWOT.toCLM
        (cayleyRealSpectralMeasure T.operator T.isSelfAdjoint S) ∈ M := by
  exact (isAffiliated_iff_realSpectralProjection_mem M T.operator T.isSelfAdjoint).mp
    T.affiliated S hS

lemma realSpectralProjection_commutes_commutant (S : Set ℝ) (hS : MeasurableSet S)
    {y : H →L[ℂ] H} (hy : y ∈ M.commutant) :
    Commute y (ContinuousLinearMapWOT.toCLM
      (cayleyRealSpectralMeasure T.operator T.isSelfAdjoint S)) :=
  (isAffiliated_iff_realSpectralProjection_commutes_commutant
    M T.operator T.isSelfAdjoint).mp T.affiliated S hS y hy

lemma cayleyProjection_commutes_commutant (S : Set ℂ) (hS : MeasurableSet S)
    {y : H →L[ℂ] H} (hy : y ∈ M.commutant) :
    Commute y (ContinuousLinearMapWOT.toCLM
      (cayleyBoundedSpectralMeasure T.operator T.isSelfAdjoint S)) :=
  T.affiliated.cayleyProjection_commutes_commutant hS hy

lemma unitaryConj_eq (u : H ≃ₗᵢ[ℂ] H)
    (hu : u.toLinearIsometry.toContinuousLinearMap ∈ M.commutant) :
    LinearPMap.unitaryConj u T.operator = T.operator :=
  T.affiliated.unitaryConj_eq u hu

lemma expIntegral_eq (u : H ≃ₗᵢ[ℂ] H)
    (hu : u.toLinearIsometry.toContinuousLinearMap ∈ M.commutant) (t : ℝ) :
    QuantumMechanics.WOTSpectralMeasure.unitaryConj u
        (QuantumMechanics.WOTSpectralMeasure.expIntegral
          (cayleyRealSpectralMeasure T.operator T.isSelfAdjoint) t) =
      QuantumMechanics.WOTSpectralMeasure.expIntegral
        (cayleyRealSpectralMeasure T.operator T.isSelfAdjoint) t :=
  IsAffiliated.expIntegral_eq T.affiliated u hu t

lemma iff_realSpectralProjection_commutes_commutant :
    IsAffiliated M T.operator T.isSelfAdjoint ↔
      ∀ S : Set ℝ, MeasurableSet S → ∀ y ∈ M.commutant,
        Commute y (ContinuousLinearMapWOT.toCLM
          (cayleyRealSpectralMeasure T.operator T.isSelfAdjoint S)) :=
  isAffiliated_iff_realSpectralProjection_commutes_commutant M T.operator T.isSelfAdjoint

end AffiliatedSelfAdjointOperator

end VonNeumannAlgebra

end OperatorAlgebra

end
