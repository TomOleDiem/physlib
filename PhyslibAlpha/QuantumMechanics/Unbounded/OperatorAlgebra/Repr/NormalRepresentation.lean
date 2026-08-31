/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.NormalAffiliated
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.NormalCanonical
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Calculus.WeakStarCalculus
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Affil.Concrete
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Repr.Representation
public import PhyslibAlpha.QuantumMechanics.Unbounded.Operators.SpectralTheory.SpectralIntegral
public import PhyslibAlpha.QuantumMechanics.Unbounded.Operators.SpectralTheory.Stone
public import Mathlib.Analysis.LocallyConvex.WeakDual

/-!
# Normal affiliated observables in a Hilbert-space representation

`NormalAffiliatedObservable` is the representation-free normal-PVM façade.  A Hilbert-space
representation still needs one analytic compatibility datum: it must turn that normal PVM into a
weak-operator PVM.  This file records that datum explicitly and then obtains the canonical
unbounded operator by the maximal square-moment integral.

The explicit bridge is intentional.  A representation of a C⋆-algebra does not, by itself, make
an arbitrary normal-functional PVM countably additive in the weak operator topology; that is the
normality/ultraweak-continuity theorem for the chosen representation.  Once supplied, all domain
and operator equalities are formal consequences of the reusable unbounded spectral-integral API.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ComplexOrder CStarAlgebra InnerProductSpace Topology Function BigOperators
open ContinuousLinearMapWOT

namespace OperatorAlgebra

variable {A H : Type*} [WStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Constructing the WOT measure from its normality certificate -/

namespace NormalPVM

/-- The exact normality condition needed to represent a normal-functional PVM as a WOT PVM.
It is stated for all matrix coefficients, which are the continuous linear functionals defining the
weak operator topology.  `NormalRepresentation` below derives this certificate from weak-star
continuity, while an explicit predual coefficient certificate gives the converse construction. -/
def IsWOTCountablyAdditive {X : Type*} [MeasurableSpace X]
    (E : NormalPVM X A) (π : Representation A H) : Prop :=
  ∀ (s : ℕ → Set X), (∀ n, MeasurableSet (s n)) → Pairwise (Disjoint on s) →
    ∀ x y : H, HasSum (fun n => ⟪y, π (E (s n)) x⟫_ℂ)
      (⟪y, π (E (⋃ n, s n)) x⟫_ℂ)

/-- The diagonal form of the WOT normality certificate.  For projection-valued measures the
diagonal coefficients determine all matrix coefficients by polarization, so this is a smaller
and usually more natural certificate to prove in concrete representations. -/
def IsDiagonalCountablyAdditive {X : Type*} [MeasurableSpace X]
    (E : NormalPVM X A) (π : Representation A H) : Prop :=
  ∀ (s : ℕ → Set X), (∀ n, MeasurableSet (s n)) → Pairwise (Disjoint on s) →
    ∀ x : H, HasSum (fun n => ⟪x, π (E (s n)) x⟫_ℂ)
      (⟪x, π (E (⋃ n, s n)) x⟫_ℂ)

/-- A certificate that the vector states of a representation are normal for the chosen predual.
Only unit vectors are stored, since arbitrary diagonal coefficients are positive scalar multiples
of unit-vector states.  The certificate is deliberately explicit: a concrete representation proves
it from its chosen predual, while this structure lets the spectral theory consume that theorem
without baking it in as an axiom. -/
structure NormalVectorStateCertificate (π : Representation A H) where
  /-- The normal state at each unit vector. -/
  state : ∀ x : H, ‖x‖ = 1 → NormalState A
  apply : ∀ (x : H) (hx : ‖x‖ = 1) (a : A), state x hx a = ⟪x, π a x⟫_ℂ

namespace NormalVectorStateCertificate

variable {π : Representation A H} (C : NormalVectorStateCertificate π)
include C

lemma diagonal_hasSum {X : Type*} [MeasurableSpace X] (E : NormalPVM X A)
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (Disjoint on s)) (x : H) :
    HasSum (fun n => ⟪x, π (E (s n)) x⟫_ℂ)
      (⟪x, π (E (⋃ n, s n)) x⟫_ℂ) := by
  by_cases hx : x = 0
  · subst x
    simp
  let r : ℝ := ‖x‖
  have hr : 0 < r := (norm_pos_iff.mpr hx)
  let u : H := (r⁻¹ : ℂ) • x
  have hu : ‖u‖ = 1 := by
    dsimp [u, r]
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg x)]
    rw [inv_mul_cancel₀ (ne_of_gt hr)]
  have hxu : x = (r : ℂ) • u := by
    have hrc : (r : ℂ) * (r⁻¹ : ℂ) = 1 :=
      mul_inv_cancel₀ (by exact_mod_cast (ne_of_gt hr))
    calc
      x = (1 : ℂ) • x := (one_smul ℂ x).symm
      _ = ((r : ℂ) * (r⁻¹ : ℂ)) • x := by
        rw [hrc]
      _ = (r : ℂ) • ((r⁻¹ : ℂ) • x) :=
        (smul_smul (r : ℂ) (r⁻¹ : ℂ) x).symm
      _ = (r : ℂ) • u := rfl
  have hcoeff (S : Set X) :
      ⟪x, π (E S) x⟫_ℂ = (r ^ 2 : ℝ) * C.state u hu (E S) := by
    rw [hxu, map_smul, inner_smul_right ((r : ℂ) • u) (π (E S) u) (r : ℂ),
      inner_smul_left u (π (E S) u) (r : ℂ)]
    simp [C.apply u hu, pow_two, mul_assoc]
  have hstate := E.m_iUnion s hs hdisj (C.state u hu)
  have hscaled := hstate.const_smul (r ^ 2 : ℂ)
  convert hscaled using 1
  · funext n
    simpa [smul_eq_mul] using hcoeff (s n)
  · simpa [smul_eq_mul] using hcoeff (⋃ n, s n)

end NormalVectorStateCertificate

/-! ### Direct predual control of matrix coefficients

The diagonal-state route above is convenient when vector states are already known to be normal.
For an actual von Neumann predual, the more direct statement is that every matrix coefficient is a
predual functional.  The following certificate records exactly that fact and consumes the
`PredualPVM` refinement, avoiding any positivity or polarization detour. -/

/-- A representation whose bounded matrix coefficients are represented by the chosen predual. -/
structure PredualMatrixCoefficientCertificate (π : Representation A H) where
  /-- The predual vector representing each matrix coefficient. -/
  coefficient : H → H → WStarAlgebra.Predual A
  apply : ∀ (x y : H) (a : A),
    WStarAlgebra.predualPairing (coefficient x y) a = ⟪y, π a x⟫_ℂ

namespace PredualMatrixCoefficientCertificate

variable {π : Representation A H} (C : PredualMatrixCoefficientCertificate π)
include C

/-- Predual additivity of the spectral measure gives the full WOT countable-additivity condition
for the representation. -/
lemma isWOTCountablyAdditive {X : Type*} [MeasurableSpace X]
    (E : PredualPVM X A) :
    NormalPVM.IsWOTCountablyAdditive E.toNormalPVM π := by
  intro s hs hdisj x y
  have hsum := E.m_iUnion s hs hdisj (C.coefficient x y)
  convert hsum using 1
  · funext n
    rw [C.apply]
  · rw [C.apply]

end PredualMatrixCoefficientCertificate

/-- Normality of the unit-vector states supplies the diagonal certificate for every normal PVM.
This is the point where a concrete predual theorem plugs into the representation bridge. -/
lemma isDiagonalCountablyAdditive_of_normalVectorStateCertificate
    {X : Type*} [MeasurableSpace X] (E : NormalPVM X A)
    (π : Representation A H) (C : NormalVectorStateCertificate π) :
    IsDiagonalCountablyAdditive E π := by
  intro s hs hdisj x
  exact C.diagonal_hasSum E s hs hdisj x

lemma representation_projection_isSelfAdjoint {X : Type*} [MeasurableSpace X]
    (E : NormalPVM X A) (π : Representation A H) (S : Set X) :
    IsSelfAdjoint (π (E S) : H →L[ℂ] H) := by
  change star (π (E S)) = π (E S)
  rw [← map_star]
  exact congrArg π (E.isStarProjection S).isSelfAdjoint

/-- Diagonal countable additivity implies the full matrix-coefficient certificate. -/
lemma isWOTCountablyAdditive_of_diagonal {X : Type*} [MeasurableSpace X]
    (E : NormalPVM X A) (π : Representation A H)
    (hE : IsDiagonalCountablyAdditive E π) :
    IsWOTCountablyAdditive E π := by
  unfold IsWOTCountablyAdditive
  intro s hs hdisj x y
  have hdiag_to_map (v : H) :
      HasSum (fun n => ⟪π (E (s n)) v, v⟫_ℂ)
        (⟪π (E (⋃ n, s n)) v, v⟫_ℂ) := by
    have h := hE s hs hdisj v
    change Tendsto (fun t : Finset ℕ => t.sum (fun n =>
      ⟪π (E (s n)) v, v⟫_ℂ)) _
      (𝓝 ⟪π (E (⋃ n, s n)) v, v⟫_ℂ)
    change Tendsto (fun t : Finset ℕ => t.sum (fun n =>
      ⟪v, π (E (s n)) v⟫_ℂ)) _
      (𝓝 ⟪v, π (E (⋃ n, s n)) v⟫_ℂ) at h
    convert h using 1
    · funext t
      induction t using Finset.induction_on with
      | empty => simp
      | @insert n t hn ih =>
          simp only [Finset.sum_insert hn]
          have hn' : ⟪π (E (s n)) v, v⟫_ℂ = ⟪v, π (E (s n)) v⟫_ℂ := by
            simpa using (representation_projection_isSelfAdjoint E π (s n)).isSymmetric v v
          rw [hn', ih]
    · exact congrArg (fun z : ℂ => 𝓝 z)
        ((representation_projection_isSelfAdjoint E π (⋃ n, s n)).isSymmetric v v)
  have hpolar (S : Set X) :
      ⟪y, π (E S) x⟫_ℂ =
        (⟪π (E S) (x + y), x + y⟫_ℂ -
            ⟪π (E S) (x - y), x - y⟫_ℂ +
            Complex.I * ⟪π (E S) (x + Complex.I • y), x + Complex.I • y⟫_ℂ -
          Complex.I * ⟪π (E S) (x - Complex.I • y), x - Complex.I • y⟫_ℂ) / 4 := by
    calc
      ⟪y, π (E S) x⟫_ℂ = ⟪π (E S) y, x⟫_ℂ :=
        ((representation_projection_isSelfAdjoint E π S).isSymmetric y x).symm
      _ = _ := inner_map_polarization (π (E S) : H →ₗ[ℂ] H) x y
  have hsumAB := (hdiag_to_map (x + y)).sub (hdiag_to_map (x - y))
  have hsumCD :=
    (hdiag_to_map (x + Complex.I • y)).const_smul Complex.I |>.sub
      ((hdiag_to_map (x - Complex.I • y)).const_smul Complex.I)
  have hsumABC := hsumAB.add hsumCD
  have hsum := hsumABC.const_smul (4 : ℂ)⁻¹
  have hsum' : HasSum (fun n =>
      (⟪π (E (s n)) (x + y), x + y⟫_ℂ -
          ⟪π (E (s n)) (x - y), x - y⟫_ℂ +
          (Complex.I * ⟪π (E (s n)) (x + Complex.I • y), x + Complex.I • y⟫_ℂ -
            Complex.I * ⟪π (E (s n)) (x - Complex.I • y), x - Complex.I • y⟫_ℂ)) / 4)
      ((⟪π (E (⋃ n, s n)) (x + y), x + y⟫_ℂ -
          ⟪π (E (⋃ n, s n)) (x - y), x - y⟫_ℂ +
          (Complex.I * ⟪π (E (⋃ n, s n)) (x + Complex.I • y), x + Complex.I • y⟫_ℂ -
            Complex.I * ⟪π (E (⋃ n, s n)) (x - Complex.I • y), x - Complex.I • y⟫_ℂ)) / 4) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hsum
  rw [hpolar (⋃ n, s n)]
  unfold HasSum
  unfold HasSum at hsum'
  change Tendsto (fun t : Finset ℕ => t.sum (fun n =>
    (⟪π (E (s n)) (x + y), x + y⟫_ℂ -
        ⟪π (E (s n)) (x - y), x - y⟫_ℂ +
        (Complex.I * ⟪π (E (s n)) (x + Complex.I • y), x + Complex.I • y⟫_ℂ -
          Complex.I * ⟪π (E (s n)) (x - Complex.I • y), x - Complex.I • y⟫_ℂ)) / 4)) _ _ at hsum'
  convert hsum' using 1
  · funext t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert n t hn ih =>
        simp only [Finset.sum_insert hn]
        rw [hpolar, ih]
        simp [div_eq_mul_inv]
        ring
  · congr 1; ring

/-- The full matrix-coefficient certificate supplied by normal unit-vector states. -/
lemma isWOTCountablyAdditive_of_normalVectorStateCertificate
    {X : Type*} [MeasurableSpace X] (E : NormalPVM X A)
    (π : Representation A H) (C : NormalVectorStateCertificate π) :
    IsWOTCountablyAdditive E π := by
  exact isWOTCountablyAdditive_of_diagonal E π
    (isDiagonalCountablyAdditive_of_normalVectorStateCertificate E π C)

/-- Measurable pushforward also preserves the diagonal normality certificate. -/
lemma isDiagonalCountablyAdditive_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (E : NormalPVM X A) (π : Representation A H)
    (hE : IsDiagonalCountablyAdditive E π) {f : X → Y} (hf : Measurable f) :
    IsDiagonalCountablyAdditive (E.map f hf) π := by
  unfold IsDiagonalCountablyAdditive
  intro s hs hdisj x
  have hpre : ∀ n, MeasurableSet (f ⁻¹' s n) := fun n => hf (hs n)
  have hpre_disj : Pairwise (Disjoint on fun n => f ⁻¹' s n) := by
    intro i j hij
    exact (hdisj hij).preimage f
  have hsum := hE (fun n => f ⁻¹' s n) hpre hpre_disj x
  simpa only [E.map_apply hf (hs _),
    E.map_apply hf (MeasurableSet.iUnion hs), preimage_iUnion] using hsum

/-! ### The norm-additive special case -/

/-- A norm-additive `PVM` automatically has the WOT countable-additivity certificate after a
bounded representation.  This is the concrete bridge used whenever the source PVM is already
available in the norm-valued layer: map the vector-measure sum through the representation and then
through a matrix-coefficient functional.  The converse is deliberately not asserted, since weak
operator sums need not converge in operator norm. -/
lemma isWOTCountablyAdditive_ofPVM {X : Type*} [MeasurableSpace X]
    (E : PVM X A) (π : Representation A H) :
    IsWOTCountablyAdditive (NormalPVM.ofPVM E) π := by
  unfold IsWOTCountablyAdditive
  intro s hs hdisj x y
  let g : (H →WOT[ℂ] H) →+ ℂ :=
    { toFun := fun T ↦ ⟪y, T x⟫_ℂ
      map_zero' := by simp
      map_add' := by
        intro T U
        change ⟪y, T x + U x⟫_ℂ = _
        rw [inner_add_right] }
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have h := E.toVectorMeasure.m_iUnion hs hdisj
  have hπ := h.map (representationToWOT π) (continuous_representationToWOT π)
  have hπg := hπ.map g hg
  change HasSum (fun n => g (representationToWOT π (E (s n))))
    (g (representationToWOT π (E (⋃ n, s n)))) at hπg
  simpa [g, representationToWOT, ContinuousLinearMapWOT.ofCLM_apply] using hπg

/-- The diagonal form of the norm-additive bridge, useful when composing it with the polarization
reduction. -/
lemma isDiagonalCountablyAdditive_ofPVM {X : Type*} [MeasurableSpace X]
    (E : PVM X A) (π : Representation A H) :
    IsDiagonalCountablyAdditive (NormalPVM.ofPVM E) π := by
  intro s hs hdisj x
  exact isWOTCountablyAdditive_ofPVM E π s hs hdisj x x


/-- Measurable pushforward preserves the matrix-coefficient normality certificate. -/
lemma isWOTCountablyAdditive_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (E : NormalPVM X A) (π : Representation A H)
    (hE : IsWOTCountablyAdditive E π) {f : X → Y} (hf : Measurable f) :
    IsWOTCountablyAdditive (E.map f hf) π := by
  unfold IsWOTCountablyAdditive
  intro s hs hdisj x y
  have hpre : ∀ n, MeasurableSet (f ⁻¹' s n) := fun n => hf (hs n)
  have hpre_disj : Pairwise (Disjoint on fun n => f ⁻¹' s n) := by
    intro i j hij
    exact (hdisj hij).preimage f
  have hsum := hE (fun n => f ⁻¹' s n) hpre hpre_disj x y
  simpa only [E.map_apply hf (hs _),
    E.map_apply hf (MeasurableSet.iUnion hs), preimage_iUnion] using hsum

/-- Represent a normal PVM by the bounded operators supplied by a star-representation.  The
`IsWOTCountablyAdditive` hypothesis is exactly what is needed to prove the vector-measure
σ-additivity field; all projection and normalization laws follow from the star-homomorphism laws. -/
noncomputable def toWOTSpectralMeasure {X : Type*} [MeasurableSpace X]
    (E : NormalPVM X A) (π : Representation A H)
    (hE : IsWOTCountablyAdditive E π) : QuantumMechanics.WOTSpectralMeasure X H where
  toVectorMeasure := {
    measureOf' := fun S =>
      ContinuousLinearMapWOT.ofCLM (π (E S))
    empty' := by
      simp
    not_measurable' := by
      intro S hS
      rw [E.apply_eq_zero_of_not_measurableSet hS, map_zero]
      rfl
    m_iUnion' := by
      intro s hs hdisj
      change HasSum (fun n => ContinuousLinearMapWOT.ofCLM (π (E (s n))))
        (ContinuousLinearMapWOT.ofCLM (π (E (⋃ n, s n))))
      change Tendsto
        (fun t : Finset ℕ => t.sum (fun n =>
          ContinuousLinearMapWOT.ofCLM (π (E (s n)))))
        _ (𝓝 (ContinuousLinearMapWOT.ofCLM (π (E (⋃ n, s n)))))
      rw [ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto]
      intro x y
      have hxy := hE s hs hdisj x y
      change Tendsto (fun t : Finset ℕ => t.sum (fun n =>
        ⟪y, π (E (s n)) x⟫_ℂ)) _
        (𝓝 ⟪y, π (E (⋃ n, s n)) x⟫_ℂ) at hxy
      convert hxy using 1
      · funext t
        induction t using Finset.induction_on with
        | empty => simp
        | @insert n t hn ih =>
            simp only [Finset.sum_insert hn]
            rw [ContinuousLinearMapWOT.add_apply, inner_add_right, ih]
            rfl
      · rfl }
  isStarProjection' := by
    intro S
    change IsStarProjection (ContinuousLinearMapWOT.ofCLM (π (E S)))
    refine ⟨?_, ?_⟩
    · change ContinuousLinearMapWOT.ofCLM (π (E S)) *
        ContinuousLinearMapWOT.ofCLM (π (E S)) = _
      rw [← ContinuousLinearMapWOT.ofCLM_mul, ← map_mul]
      exact congrArg (fun a : A => ContinuousLinearMapWOT.ofCLM (π a))
        (E.isStarProjection S).isIdempotentElem
    · apply ContinuousLinearMapWOT.toCLM_injective
      change star (π (E S)) = π (E S)
      rw [← map_star]
      exact congrArg π (E.isStarProjection S).isSelfAdjoint
  univ' := by
    change ContinuousLinearMapWOT.ofCLM (π (E (Set.univ : Set X))) = 1
    rw [E.univ, map_one]
    rfl

@[simp]
lemma toWOTSpectralMeasure_apply {X : Type*} [MeasurableSpace X]
    (E : NormalPVM X A) (π : Representation A H)
    (hE : IsWOTCountablyAdditive E π) (S : Set X) :
    toWOTSpectralMeasure E π hE S =
      ContinuousLinearMapWOT.ofCLM (π (E S)) := by
  rfl

/-! ### Direct adapter for predual-certified PVMs -/

/-- Consume a `PredualPVM` and a predual realization of all matrix coefficients directly.

This is intentionally an adapter rather than an automatic constructor from `NormalPVM`: the
extra predual additivity field is the substantive normality theorem for a weakly additive PVM.
Once it is present, the WOT spectral measure is obtained by the same general construction as
above. -/
noncomputable def toWOTSpectralMeasureOfPredual {X : Type*} [MeasurableSpace X]
    (E : PredualPVM X A) (π : Representation A H)
    (C : PredualMatrixCoefficientCertificate π) :
    QuantumMechanics.WOTSpectralMeasure X H :=
  toWOTSpectralMeasure E.toNormalPVM π (C.isWOTCountablyAdditive E)

@[simp]
lemma toWOTSpectralMeasure_of_predual_apply {X : Type*} [MeasurableSpace X]
    (E : PredualPVM X A) (π : Representation A H)
    (C : PredualMatrixCoefficientCertificate π) (S : Set X) :
    toWOTSpectralMeasureOfPredual E π C S =
      ContinuousLinearMapWOT.ofCLM (π (E S)) := by
  rfl

lemma toWOTSpectralMeasure_map {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (E : NormalPVM X A) (π : Representation A H)
    (hE : IsWOTCountablyAdditive E π) {f : X → Y} (hf : Measurable f) :
    toWOTSpectralMeasure (E.map f hf) π (isWOTCountablyAdditive_map E π hE hf) =
      (toWOTSpectralMeasure E π hE).map f hf := by
  rw [QuantumMechanics.WOTSpectralMeasure.mk.injEq]
  apply MeasureTheory.VectorMeasure.ext
  intro S hS
  change ContinuousLinearMapWOT.ofCLM (π ((E.map f hf) S)) =
    (toWOTSpectralMeasure E π hE).map f hf S
  rw [E.map_apply hf hS,
    (toWOTSpectralMeasure E π hE).map_apply f hf hS,
    toWOTSpectralMeasure_apply]

lemma toWOTSpectralMeasure_of_predual_map {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (E : PredualPVM X A) (π : Representation A H)
    (C : PredualMatrixCoefficientCertificate π) {f : X → Y} (hf : Measurable f) :
    toWOTSpectralMeasureOfPredual (E.map f hf) π C =
      (toWOTSpectralMeasureOfPredual E π C).map f hf := by
  unfold toWOTSpectralMeasureOfPredual
  exact toWOTSpectralMeasure_map E.toNormalPVM π _ hf

end NormalPVM

/-! ## Normal representations and their predual coefficients -/

/-- The bounded matrix coefficient of a representation.  Keeping this as a linear map makes the
weak-star continuity hypothesis on a normal representation directly consumable by the predual
duality theorem. -/
def matrixCoefficientLinearMap (π : Representation A H) (x y : H) : A →ₗ[ℂ] ℂ where
  toFun a := ⟪y, π a x⟫_ℂ
  map_add' a b := by simp [map_add]
  map_smul' c a := by simp [map_smul]

@[simp] lemma matrixCoefficientLinearMap_apply (π : Representation A H) (x y : H) (a : A) :
    matrixCoefficientLinearMap π x y a = ⟪y, π a x⟫_ℂ := rfl

/-- A representation is normal when all of its bounded matrix coefficients are weak-star
continuous for the chosen von Neumann predual. -/
structure NormalRepresentation where
  /-- The underlying Hilbert-space representation. -/
  representation : Representation A H
  matrixCoefficient_continuous : ∀ x y : H,
    Continuous[WStarAlgebra.weakStarTopology A, inferInstance]
      (matrixCoefficientLinearMap representation x y)

/-- The algebra/predual identification used to transport a matrix coefficient to the weak dual. -/
def normalCoeffTopologyEquiv : A ≃ₗ[ℂ] WeakDual ℂ (WStarAlgebra.Predual A) where
  toFun a := StrongDual.toWeakDual (WStarAlgebra.toDual a)
  invFun φ := (WStarAlgebra.toDual (A := A)).symm (WeakDual.toStrongDual φ)
  left_inv a := by simp
  right_inv φ := by simp
  map_add' a b := by simp
  map_smul' c a := by simp

lemma continuous_normalCoeffTopologyEquiv_inv :
    Continuous[(inferInstance : TopologicalSpace (WeakDual ℂ (WStarAlgebra.Predual A))),
      WStarAlgebra.weakStarTopology A]
      (normalCoeffTopologyEquiv (A := A)).symm := by
  change Continuous[(inferInstance : TopologicalSpace (WeakDual ℂ (WStarAlgebra.Predual A))),
    TopologicalSpace.induced
      (fun a : A => StrongDual.toWeakDual (WStarAlgebra.toDual a)) inferInstance]
      (normalCoeffTopologyEquiv (A := A)).symm
  rw [continuous_induced_rng]
  convert continuous_id using 1
  funext φ
  simp [normalCoeffTopologyEquiv]

/-- `matrixCoefficientLinearMap`, transported along the algebra/predual identification to a
linear functional on `WeakDual ℂ (WStarAlgebra.Predual A)`. -/
def normalCoeffOnWeakDual (π : Representation A H) (x y : H) :
    WeakDual ℂ (WStarAlgebra.Predual A) →ₗ[ℂ] ℂ :=
  (matrixCoefficientLinearMap π x y).comp
    ((WStarAlgebra.toDual (A := A)).symm.toLinearMap.comp
      (WeakDual.toStrongDual (𝕜 := ℂ) (E := WStarAlgebra.Predual A)).toLinearMap)

lemma continuous_normalCoeffOnWeakDual (π : Representation A H) (x y : H)
    (h : Continuous[WStarAlgebra.weakStarTopology A, inferInstance]
      (matrixCoefficientLinearMap π x y)) :
    Continuous (normalCoeffOnWeakDual π x y) := by
  change Continuous (fun φ : WeakDual ℂ (WStarAlgebra.Predual A) =>
    matrixCoefficientLinearMap π x y ((normalCoeffTopologyEquiv (A := A)).symm φ))
  exact @Continuous.comp
    (WeakDual ℂ (WStarAlgebra.Predual A)) A ℂ
    (inferInstance : TopologicalSpace (WeakDual ℂ (WStarAlgebra.Predual A)))
    (WStarAlgebra.weakStarTopology A) inferInstance _ _ h
    (continuous_normalCoeffTopologyEquiv_inv (A := A))

/-- Every weak-star continuous matrix coefficient is represented by a predual vector. -/
lemma continuousCoeff_exists_predual (π : Representation A H) (x y : H)
    (h : Continuous[WStarAlgebra.weakStarTopology A, inferInstance]
      (matrixCoefficientLinearMap π x y)) :
    ∃ ξ : WStarAlgebra.Predual A, ∀ a : A,
      WStarAlgebra.predualPairing ξ a = matrixCoefficientLinearMap π x y a := by
  let φ : WeakDual ℂ (WStarAlgebra.Predual A) →ₗ[ℂ] ℂ :=
    normalCoeffOnWeakDual π x y
  have hφ : Continuous φ := continuous_normalCoeffOnWeakDual π x y h
  let Φ : StrongDual ℂ (WeakDual ℂ (WStarAlgebra.Predual A)) :=
    ContinuousLinearMap.mk φ hφ
  obtain ⟨ξ, hξ⟩ := LinearMap.dualEmbedding_surjective
    (topDualPairing ℂ (WStarAlgebra.Predual A)) Φ
  refine ⟨ξ, ?_⟩
  intro a
  have ha := congrArg (fun q : StrongDual ℂ (WeakDual ℂ (WStarAlgebra.Predual A)) => q
      (normalCoeffTopologyEquiv (A := A) a)) hξ
  change (topDualPairing ℂ (WStarAlgebra.Predual A)
      (normalCoeffTopologyEquiv (A := A) a) ξ) =
    normalCoeffOnWeakDual π x y (normalCoeffTopologyEquiv (A := A) a) at ha
  have htop : topDualPairing ℂ (WStarAlgebra.Predual A)
      (StrongDual.toWeakDual (WStarAlgebra.toDual a)) ξ =
      (WStarAlgebra.toDual a) ξ := by
    rfl
  change (topDualPairing ℂ (WStarAlgebra.Predual A)
      (StrongDual.toWeakDual (WStarAlgebra.toDual a))) ξ =
    normalCoeffOnWeakDual π x y (StrongDual.toWeakDual (WStarAlgebra.toDual a)) at ha
  rw [htop] at ha
  change WStarAlgebra.predualPairing ξ a = _
  simpa [normalCoeffOnWeakDual, normalCoeffTopologyEquiv,
    matrixCoefficientLinearMap] using ha

lemma normalCoeff_exists_predual (π : NormalRepresentation) (x y : H) :
    ∃ ξ : WStarAlgebra.Predual A, ∀ a : A,
      WStarAlgebra.predualPairing ξ a = ⟪y, π.representation a x⟫_ℂ := by
  exact continuousCoeff_exists_predual π.representation x y
    (π.matrixCoefficient_continuous x y)

namespace NormalRepresentation

/-- The predual representation theorem specialized to a normal representation. -/
lemma continuousCoeff_exists_predual (π : NormalRepresentation (A := A) (H := H))
    (x y : H) :
    ∃ ξ : WStarAlgebra.Predual A, ∀ a : A,
      WStarAlgebra.predualPairing ξ a = ⟪y, π.representation a x⟫_ℂ :=
  normalCoeff_exists_predual π x y

/-- Construct a normal representation from an explicit predual realization of all its matrix
coefficients.  The weak-star continuity is then exactly continuity of the predual pairing. -/
noncomputable def ofPredualMatrixCoefficientCertificate
    (π : Representation A H)
    (C : NormalPVM.PredualMatrixCoefficientCertificate π) :
    NormalRepresentation (A := A) (H := H) where
  representation := π
  matrixCoefficient_continuous := by
    intro x y
    have h := WStarAlgebra.predualPairing_weakStar_continuous
      (A := A) (C.coefficient x y)
    have heq : (matrixCoefficientLinearMap π x y : A → ℂ) =
        WStarAlgebra.predualPairing (C.coefficient x y) := by
      funext a
      exact (C.apply x y a).symm
    rw [heq]
    exact h

end NormalRepresentation

/-- The normal vector state at a unit vector `x`, for a normal representation. -/
noncomputable def normalVectorState
    (π : NormalRepresentation (A := A) (H := H)) (x : H) (hx : ‖x‖ = 1) :
    NormalState A where
  toState := {
    toPositiveLinearMap := PositiveLinearMap.mk₀
      (matrixCoefficientLinearMap π.representation x x)
      (fun a ha => by
        have hπa : 0 ≤ (π.representation a : B(H)) := map_nonneg π.representation ha
        exact ((operator_nonneg_iff_isPositive _).mp hπa).inner_nonneg_right x)
    map_one := by
      change ⟪x, π.representation (1 : A) x⟫_ℂ = 1
      rw [map_one, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hx]
      norm_num }
  weakStar_continuous := by
    exact π.matrixCoefficient_continuous x x

@[simp] lemma normalVectorState_apply
    (π : NormalRepresentation (A := A) (H := H)) (x : H) (hx : ‖x‖ = 1)
    (a : A) : normalVectorState π x hx a = ⟪x, π.representation a x⟫_ℂ := rfl

/-- Package the coefficientwise predual representation supplied by normality into the certificate
consumed by `NormalPVM.toWOTSpectralMeasureOfPredual`. -/
noncomputable def NormalRepresentation.toPredualMatrixCoefficientCertificate
    (π : NormalRepresentation (A := A) (H := H)) :
    NormalPVM.PredualMatrixCoefficientCertificate π.representation where
  coefficient := fun x y => Classical.choose (normalCoeff_exists_predual π x y)
  apply := by
    intro x y a
    exact Classical.choose_spec (normalCoeff_exists_predual π x y) a

/-! ## The representation boundary -/

/-- A normality witness for a representation of the normal PVM layer. -/
structure NormalAffiliationBridge where
  /-- The underlying Hilbert-space representation. -/
  representation : Representation A H
  /-- The represented weak-operator spectral measure of an abstract normal PVM. -/
  toWOTSpectralMeasure : NormalPVM ℝ A → QuantumMechanics.WOTSpectralMeasure ℝ H
  toWOTSpectralMeasure_apply :
    ∀ (E : NormalPVM ℝ A) (S : Set ℝ),
      representation (E S) = (toWOTSpectralMeasure E S).toCLM
  toWOTSpectralMeasure_map :
    ∀ (E : NormalPVM ℝ A) {f : ℝ → ℝ} (hf : Measurable f),
      toWOTSpectralMeasure (E.map f hf) =
        (toWOTSpectralMeasure E).map f hf

/-! ### Abstract Borel calculus versus represented spectral integrals -/

/- A representation bridge turns normal PVMs into WOT PVMs, but it does not by itself prove that
the abstract bounded Borel functional calculus takes the same values as the Hilbert-space
integral.  The following certificate records exactly that remaining compatibility theorem.  It is
the reusable seam for a future concrete von Neumann-algebra implementation (and is immediately
available for any calculus whose values have already been identified by another argument).

**Restricting `calculus` (P5 boundary note).** `WeakStarFunctionalCalculus.lean` (P3) proves
`NormalBorelFunctionalCalculus.ofNormalPVM`: every `NormalPVM` already carries a bounded Borel
calculus, with *no* extra hypothesis. So the `calculus` field below no longer needs to be supplied
externally — it is a theorem, not a genuine boundary. `NormalBorelRepresentationWitness` below
packages exactly the part that *is* still a genuine external representation theorem (the
normality/monotone-completeness statement identifying the canonically-constructed calculus with
the concrete Hilbert-space integral), and `NormalBorelRepresentationWitness.certificate` upgrades
it to a full `NormalBorelRepresentationCertificate` for free. The certificate structure itself is
kept (rather than deleted) only because it is strictly more general — it also accepts a
hand-supplied `calculus` that is *not* `ofNormalPVM`, which the witness route cannot express — but
every concrete user should go through the witness constructor. -/

/-- Compatibility of an abstract normal Borel calculus with its represented WOT spectral integral.

The field `represented_boundedFC` is the substantive normality/monotone-completeness statement.
All consequences below are formal: indicators, exponentials, and resolvents need no separate
affiliation argument once this certificate is supplied. -/
structure NormalBorelRepresentationCertificate
    (bridge : NormalAffiliationBridge (A := A) (H := H)) where
  /-- The abstract normal Borel functional calculus attached to each normal PVM. -/
  calculus : ∀ E : NormalPVM ℝ A, NormalBorelFunctionalCalculus E
  represented_boundedFC :
    ∀ (E : NormalPVM ℝ A) (f : ℝ → ℂ)
      (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C),
      bridge.representation ((calculus E).boundedFC f hf hfb) =
        (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
          (bridge.toWOTSpectralMeasure E) f hf hfb).toCLM

namespace NormalBorelRepresentationCertificate

variable {bridge : NormalAffiliationBridge (A := A) (H := H)}
variable (C : NormalBorelRepresentationCertificate bridge)
include C

lemma represented_boundedFC_eq
    (E : NormalPVM ℝ A) (f : ℝ → ℂ)
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    bridge.representation ((C.calculus E).boundedFC f hf hfb) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasure E) f hf hfb).toCLM :=
  C.represented_boundedFC E f hf hfb

/-- The abstract projection is represented by the indicator spectral integral. -/
lemma represented_indicator
    (E : NormalPVM ℝ A) (S : Set ℝ) (hS : MeasurableSet S) :
    bridge.representation (E S) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasure E)
        (normalIndicatorFunction S)
        (normalIndicatorFunction_measurable hS)
        (normalIndicatorFunction_bounded S)).toCLM := by
  calc
    bridge.representation (E S) =
        bridge.representation ((C.calculus E).boundedFC
          (normalIndicatorFunction S)
          (normalIndicatorFunction_measurable hS)
          (normalIndicatorFunction_bounded S)) := by
      rw [(C.calculus E).boundedFC_indicator S hS]
    _ = _ := C.represented_boundedFC E _ _ _

/-- Exponentiation in the abstract calculus agrees with the concrete unitary spectral integral. -/
lemma represented_exp
    (E : NormalPVM ℝ A) (t : ℝ) :
    bridge.representation ((C.calculus E).boundedFC
        (QuantumMechanics.WOTSpectralMeasure.expFunction t)
        (QuantumMechanics.WOTSpectralMeasure.expFunction_measurable t)
        (QuantumMechanics.WOTSpectralMeasure.expFunction_bounded t)) =
      (QuantumMechanics.WOTSpectralMeasure.expIntegral
        (bridge.toWOTSpectralMeasure E) t).toCLM := by
  exact C.represented_boundedFC E _ _ _

/-- The abstract resolvent agrees with the represented bounded resolvent integral. -/
lemma represented_resolvent
    (E : NormalPVM ℝ A) (z : ℂ) (hz : z.im ≠ 0) :
    bridge.representation ((C.calculus E).boundedFC
        (AffiliatedObservable.resolventFunction z)
        (AffiliatedObservable.resolventFunction_measurable z)
        (AffiliatedObservable.resolventFunction_bounded z hz)) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasure E)
        (AffiliatedObservable.resolventFunction z)
        (AffiliatedObservable.resolventFunction_measurable z)
        (AffiliatedObservable.resolventFunction_bounded z hz)).toCLM := by
  exact C.represented_boundedFC E _ _ _

/-! ### Affiliated-observable packaging -/

/-- The abstract unitary generated by a normal affiliated observable, using the calculus selected
by the representation certificate. -/
noncomputable def abstractExpUnitary
    (T : NormalAffiliatedObservable A) (t : ℝ) : unitary A :=
  T.expUnitary (C.calculus T.spectralMeasure) t

lemma represented_abstractExpUnitary
    (T : NormalAffiliatedObservable A) (t : ℝ) :
    bridge.representation ((C.abstractExpUnitary T t : unitary A) : A) =
      (QuantumMechanics.WOTSpectralMeasure.expIntegral
        (bridge.toWOTSpectralMeasure T.spectralMeasure) t).toCLM := by
  change bridge.representation ((C.calculus T.spectralMeasure).boundedFC
      (AffiliatedObservable.expFunction t)
      (AffiliatedObservable.expFunction_measurable t)
      (AffiliatedObservable.expFunction_bounded t)) = _
  exact C.represented_exp T.spectralMeasure t

/-- The abstract resolvent generated by a normal affiliated observable, using the calculus selected
by the representation certificate. -/
noncomputable def abstractResolvent
    (T : NormalAffiliatedObservable A) (z : ℂ) (hz : z.im ≠ 0) : A :=
  T.resolvent (C.calculus T.spectralMeasure) z hz

lemma represented_abstractResolvent
    (T : NormalAffiliatedObservable A) (z : ℂ) (hz : z.im ≠ 0) :
    bridge.representation (C.abstractResolvent T z hz) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasure T.spectralMeasure)
        (AffiliatedObservable.resolventFunction z)
        (AffiliatedObservable.resolventFunction_measurable z)
        (AffiliatedObservable.resolventFunction_bounded z hz)).toCLM := by
  exact C.represented_resolvent T.spectralMeasure z hz

end NormalBorelRepresentationCertificate

/-! ### The reduced witness (P5 boundary)

`NormalBorelFunctionalCalculus.ofNormalPVM` (P3, `WeakStarFunctionalCalculus.lean`) proves that
`calculus` above is never genuinely extra data: it always exists, with no hypothesis, for every
`NormalPVM`.  So the only honest remaining representation theorem is that the *canonical*
`ofNormalPVM` calculus is represented correctly.  `NormalBorelRepresentationWitness` records
exactly that, and nothing more; `.certificate` upgrades it to the full (more general, but strictly
less economical) `NormalBorelRepresentationCertificate` above for free, so every downstream lemma
of that namespace remains available. -/

/-- The reduced representation witness: only the compatibility of the *canonical* `ofNormalPVM`
calculus with the represented WOT spectral integral is required.  This is the named boundary that
replaces `NormalBorelRepresentationCertificate.calculus` per the roadmap: a genuinely external
representation theorem, not a certificate for data P3 already constructs. -/
structure NormalBorelRepresentationWitness
    (bridge : NormalAffiliationBridge (A := A) (H := H)) where
  represented_boundedFC :
    ∀ (E : NormalPVM ℝ A) (f : ℝ → ℂ)
      (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C),
      bridge.representation
          ((NormalBorelFunctionalCalculus.ofNormalPVM E).boundedFC f hf hfb) =
        (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
          (bridge.toWOTSpectralMeasure E) f hf hfb).toCLM

namespace NormalBorelRepresentationWitness

variable {bridge : NormalAffiliationBridge (A := A) (H := H)}

/-- Every witness upgrades to a full certificate, using the canonical `ofNormalPVM` calculus. -/
def certificate (W : NormalBorelRepresentationWitness bridge) :
    NormalBorelRepresentationCertificate bridge where
  calculus := fun E => NormalBorelFunctionalCalculus.ofNormalPVM E
  represented_boundedFC := W.represented_boundedFC

end NormalBorelRepresentationWitness

/-! The real bridge above is enough for self-adjoint observables.  The affiliated-operator façade
also contains genuinely complex normal operators, so expose the corresponding complex bridge
without weakening the real API or pretending that normality is automatic. -/

/-- A normal-PVM representation bridge for both real observables and complex normal affiliated
operators.  The inherited real part is used for self-adjoint domains; the complex part supplies
the representation compatibility of arbitrary measurable complex functional calculus. -/
structure NormalOperatorAffiliationBridge
    extends NormalAffiliationBridge (A := A) (H := H) where
  /-- The represented weak-operator spectral measure of an abstract complex normal PVM. -/
  toWOTSpectralMeasureComplex : NormalPVM ℂ A → QuantumMechanics.WOTSpectralMeasure ℂ H
  toWOTSpectralMeasureComplex_apply :
    ∀ (E : NormalPVM ℂ A) (S : Set ℂ),
      representation (E S) = (toWOTSpectralMeasureComplex E S).toCLM
  toWOTSpectralMeasureComplex_map :
    ∀ (E : NormalPVM ℂ A) {f : ℂ → ℂ} (hf : Measurable f),
      toWOTSpectralMeasureComplex (E.map f hf) =
        (toWOTSpectralMeasureComplex E).map f hf

/-- The real-and-complex version of `NormalBorelRepresentationCertificate`.  The real component
is inherited for self-adjoint observables; the complex component is the additional compatibility
needed for arbitrary normal affiliated operators. -/
structure NormalOperatorBorelRepresentationCertificate
    (bridge : NormalOperatorAffiliationBridge (A := A) (H := H))
    extends NormalBorelRepresentationCertificate
      (bridge.toNormalAffiliationBridge) where
  /-- The abstract normal Borel functional calculus attached to each complex normal PVM. -/
  calculusComplex : ∀ E : NormalPVM ℂ A, NormalBorelFunctionalCalculus E
  represented_boundedFCComplex :
    ∀ (E : NormalPVM ℂ A) (f : ℂ → ℂ)
      (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C),
      bridge.representation ((calculusComplex E).boundedFC f hf hfb) =
        (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
          (bridge.toWOTSpectralMeasureComplex E) f hf hfb).toCLM

namespace NormalOperatorBorelRepresentationCertificate

variable {bridge : NormalOperatorAffiliationBridge (A := A) (H := H)}
variable (C : NormalOperatorBorelRepresentationCertificate bridge)
include C

lemma represented_boundedFCComplex_eq
    (E : NormalPVM ℂ A) (f : ℂ → ℂ)
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    bridge.representation ((C.calculusComplex E).boundedFC f hf hfb) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasureComplex E) f hf hfb).toCLM :=
  C.represented_boundedFCComplex E f hf hfb

lemma represented_indicator
    (E : NormalPVM ℂ A) (S : Set ℂ) (hS : MeasurableSet S) :
    bridge.representation (E S) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasureComplex E)
        (normalIndicatorFunction S)
        (normalIndicatorFunction_measurable hS)
        (normalIndicatorFunction_bounded S)).toCLM := by
  calc
    bridge.representation (E S) =
        bridge.representation ((C.calculusComplex E).boundedFC
          (normalIndicatorFunction S)
          (normalIndicatorFunction_measurable hS)
          (normalIndicatorFunction_bounded S)) := by
      rw [(C.calculusComplex E).boundedFC_indicator S hS]
    _ = _ := C.represented_boundedFCComplex E _ _ _

/-! The represented complex normal affiliated operator uses the complex component of the
certificate, so arbitrary measurable complex functional calculus is available at the algebra
boundary as soon as this one compatibility theorem has been supplied. -/

/-- The abstract complex bounded functional calculus of a normal affiliated operator, via the
certificate's complex calculus. -/
noncomputable def abstractBoundedFC
    (T : NormalAffiliatedOperator A) (f : ℂ → ℂ)
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) : A :=
  NormalAffiliatedOperator.boundedFC T (C.calculusComplex T.spectralMeasure) f hf hfb

lemma represented_abstractBoundedFC
    (T : NormalAffiliatedOperator A) (f : ℂ → ℂ)
    (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) :
    bridge.representation (C.abstractBoundedFC T f hf hfb) =
      (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.toWOTSpectralMeasureComplex T.spectralMeasure) f hf hfb).toCLM := by
  exact C.represented_boundedFCComplex_eq T.spectralMeasure f hf hfb

end NormalOperatorBorelRepresentationCertificate

/-! ### The reduced complex witness (P5 boundary)

The complex analogue of `NormalBorelRepresentationWitness`: `calculusComplex` is likewise never
genuine data (`NormalBorelFunctionalCalculus.ofNormalPVM` supplies it for every `NormalPVM ℂ A`
with no hypothesis), so only the two `represented_boundedFC*` compatibility statements for the
canonical calculi remain as the genuine external representation theorem. -/

/-- The reduced real-and-complex representation witness. -/
structure NormalOperatorBorelRepresentationWitness
    (bridge : NormalOperatorAffiliationBridge (A := A) (H := H)) where
  real : NormalBorelRepresentationWitness bridge.toNormalAffiliationBridge
  represented_boundedFCComplex :
    ∀ (E : NormalPVM ℂ A) (f : ℂ → ℂ)
      (hf : Measurable f) (hfb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C),
      bridge.representation
          ((NormalBorelFunctionalCalculus.ofNormalPVM E).boundedFC f hf hfb) =
        (QuantumMechanics.WOTSpectralMeasure.boundedIntegral
          (bridge.toWOTSpectralMeasureComplex E) f hf hfb).toCLM

namespace NormalOperatorBorelRepresentationWitness

variable {bridge : NormalOperatorAffiliationBridge (A := A) (H := H)}

/-- Every complex witness upgrades to a full `NormalOperatorBorelRepresentationCertificate`, using
the canonical `ofNormalPVM` calculus on both the real and complex spectral spaces. -/
def certificate (W : NormalOperatorBorelRepresentationWitness bridge) :
    NormalOperatorBorelRepresentationCertificate bridge where
  toNormalBorelRepresentationCertificate := W.real.certificate
  calculusComplex := fun E => NormalBorelFunctionalCalculus.ofNormalPVM E
  represented_boundedFCComplex := W.represented_boundedFCComplex

end NormalOperatorBorelRepresentationWitness

/-! ## Faithful normal bridges -/

/-- A faithful normal-affiliation bridge.  Faithfulness is kept separate from the representation
bridge itself because constructing a faithful normal representation is a von Neumann-algebra
question, while the uniqueness arguments below need only injectivity. -/
structure FaithfulNormalAffiliationBridge
    extends NormalAffiliationBridge (A := A) (H := H) where
  faithful : Function.Injective representation

namespace FaithfulNormalAffiliationBridge

variable (bridge : FaithfulNormalAffiliationBridge (A := A) (H := H))

lemma representation_injective : Function.Injective bridge.representation :=
  bridge.faithful

/-- A faithful normal representation reflects equality of the values of two normal PVMs when
their represented WOT spectral measures agree. -/
lemma normalPVM_ext
    {E F : NormalPVM ℝ A}
    (h : ∀ S : Set ℝ,
      MeasurableSet S →
      bridge.toWOTSpectralMeasure E S = bridge.toWOTSpectralMeasure F S) :
    E = F := by
  apply NormalPVM.ext
  intro S hS
  apply bridge.faithful
  calc
    bridge.representation (E S) = (bridge.toWOTSpectralMeasure E S).toCLM :=
      bridge.toWOTSpectralMeasure_apply E S
    _ = (bridge.toWOTSpectralMeasure F S).toCLM := congrArg (fun U => U.toCLM) (h S hS)
    _ = bridge.representation (F S) := (bridge.toWOTSpectralMeasure_apply F S).symm

/-- In a faithful normal representation, a normal affiliated observable is determined by its
represented WOT spectral measure. -/
lemma normalAffiliatedObservable_ext
    (T U : NormalAffiliatedObservable A)
    (h : ∀ S : Set ℝ,
      MeasurableSet S →
      bridge.toNormalAffiliationBridge.toWOTSpectralMeasure T.spectralMeasure S =
        bridge.toNormalAffiliationBridge.toWOTSpectralMeasure U.spectralMeasure S) :
    T = U := by
  apply NormalAffiliatedObservable.ext
  intro S hS
  have hEF : T.spectralMeasure = U.spectralMeasure :=
    FaithfulNormalAffiliationBridge.normalPVM_ext bridge (fun S hS => h S hS)
  exact congrArg (fun E : NormalPVM ℝ A => E S) hEF

end FaithfulNormalAffiliationBridge

/-- The faithful version of the real-and-complex normal bridge. -/
structure FaithfulNormalOperatorAffiliationBridge
    extends NormalOperatorAffiliationBridge (A := A) (H := H) where
  faithful : Function.Injective representation

namespace FaithfulNormalOperatorAffiliationBridge

variable (bridge : FaithfulNormalOperatorAffiliationBridge (A := A) (H := H))

lemma representation_injective : Function.Injective bridge.representation :=
  bridge.faithful

/-- A faithful normal representation reflects equality of complex normal PVMs from equality of
their represented WOT spectral measures. -/
lemma normalPVM_ext
    {E F : NormalPVM ℂ A}
    (h : ∀ S : Set ℂ,
      MeasurableSet S →
      bridge.toWOTSpectralMeasureComplex E S =
        bridge.toWOTSpectralMeasureComplex F S) :
    E = F := by
  apply NormalPVM.ext
  intro S hS
  apply bridge.faithful
  calc
    bridge.representation (E S) =
        (bridge.toWOTSpectralMeasureComplex E S).toCLM :=
      bridge.toWOTSpectralMeasureComplex_apply E S
    _ = (bridge.toWOTSpectralMeasureComplex F S).toCLM :=
      congrArg (fun U => U.toCLM) (h S hS)
    _ = bridge.representation (F S) :=
      (bridge.toWOTSpectralMeasureComplex_apply F S).symm

/-- In a faithful normal representation, a complex normal affiliated operator is determined by its
represented WOT spectral measure. -/
lemma normalAffiliatedOperator_ext
    (T U : NormalAffiliatedOperator A)
    (h : ∀ S : Set ℂ,
      MeasurableSet S →
      bridge.toWOTSpectralMeasureComplex T.spectralMeasure S =
        bridge.toWOTSpectralMeasureComplex U.spectralMeasure S) :
    T = U := by
  apply NormalAffiliatedOperator.ext
  intro S hS
  have hEF : T.spectralMeasure = U.spectralMeasure :=
    FaithfulNormalOperatorAffiliationBridge.normalPVM_ext bridge (fun S hS => h S hS)
  exact congrArg (fun E : NormalPVM ℂ A => E S) hEF

end FaithfulNormalOperatorAffiliationBridge

namespace NormalAffiliationBridge

variable (bridge : NormalAffiliationBridge (A := A) (H := H))

/-- Build the real normal-affiliation bridge from a representation that supplies matrix-coefficient
σ-additivity for every normal PVM.  This is the reusable constructor; the analytic theorem that a
particular faithful normal representation supplies the certificate remains a separate input. -/
noncomputable def ofRepresentation (π : Representation A H)
    (hnormal : ∀ E : NormalPVM ℝ A,
      NormalPVM.IsWOTCountablyAdditive E π) : NormalAffiliationBridge (A := A) (H := H) where
  representation := π
  toWOTSpectralMeasure := fun E => NormalPVM.toWOTSpectralMeasure E π (hnormal E)
  toWOTSpectralMeasure_apply := by
    intro E S
    rw [NormalPVM.toWOTSpectralMeasure_apply]
  toWOTSpectralMeasure_map := by
    intro E f hf
    exact NormalPVM.toWOTSpectralMeasure_map E π (hnormal E) hf

/-- Build a real affiliation bridge from an explicit predual lift of every normal PVM.

The lift is required to be compatible with measurable pushforward.  This constructor is useful
when the concrete von Neumann theorem naturally produces predual-functional additivity rather
than a matrix-coefficient statement; `PredualMatrixCoefficientCertificate` supplies the latter
without a positivity or polarization detour.  The lift and its compatibility remain explicit
because they are precisely the nontrivial infinite-dimensional normality theorem. -/
noncomputable def ofPredualRepresentation (π : Representation A H)
    (predual : ∀ E : NormalPVM ℝ A, PredualPVM ℝ A)
    (hpredual : ∀ E : NormalPVM ℝ A, (predual E).toNormalPVM = E)
    (C : NormalPVM.PredualMatrixCoefficientCertificate π)
    (hmap : ∀ (E : NormalPVM ℝ A) {f : ℝ → ℝ} (hf : Measurable f),
      predual (E.map f hf) = (predual E).map f hf) :
    NormalAffiliationBridge (A := A) (H := H) where
  representation := π
  toWOTSpectralMeasure := fun E =>
    NormalPVM.toWOTSpectralMeasureOfPredual (predual E) π C
  toWOTSpectralMeasure_apply := by
    intro E S
    change π (E S) =
      (NormalPVM.toWOTSpectralMeasureOfPredual (predual E) π C S).toCLM
    calc
      π (E S) = π ((predual E).toNormalPVM S) := by rw [hpredual E]
      _ = π ((predual E) S) := rfl
      _ = (NormalPVM.toWOTSpectralMeasureOfPredual
          (predual E) π C S).toCLM := by
        rw [NormalPVM.toWOTSpectralMeasure_of_predual_apply]
  toWOTSpectralMeasure_map := by
    intro E f hf
    change NormalPVM.toWOTSpectralMeasureOfPredual
        (predual (E.map f hf)) π C =
      (NormalPVM.toWOTSpectralMeasureOfPredual (predual E) π C).map f hf
    rw [hmap E hf]
    exact NormalPVM.toWOTSpectralMeasure_of_predual_map (predual E) π C hf

/-- The faithful version of `ofPredualRepresentation`. -/
noncomputable def ofFaithfulPredualRepresentation (π : Representation A H)
    (predual : ∀ E : NormalPVM ℝ A, PredualPVM ℝ A)
    (hpredual : ∀ E : NormalPVM ℝ A, (predual E).toNormalPVM = E)
    (C : NormalPVM.PredualMatrixCoefficientCertificate π)
    (hmap : ∀ (E : NormalPVM ℝ A) {f : ℝ → ℝ} (hf : Measurable f),
      predual (E.map f hf) = (predual E).map f hf)
    (hfaithful : Function.Injective π) :
    FaithfulNormalAffiliationBridge (A := A) (H := H) :=
  { ofPredualRepresentation π predual hpredual C hmap with faithful := hfaithful }

/-! The diagonal variant is the preferred entry point when normality is proved from vector
quadratic forms. -/

/-- Build a real representation bridge from diagonal matrix-coefficient σ-additivity. -/
noncomputable def ofDiagonalRepresentation (π : Representation A H)
    (hdiagonal : ∀ E : NormalPVM ℝ A,
      NormalPVM.IsDiagonalCountablyAdditive E π) :
    NormalAffiliationBridge (A := A) (H := H) :=
  ofRepresentation π (fun E =>
    NormalPVM.isWOTCountablyAdditive_of_diagonal E π (hdiagonal E))

/-- Build the real representation bridge from the normality of all unit-vector states. -/
noncomputable def ofNormalVectorStateCertificate (π : Representation A H)
    (C : NormalPVM.NormalVectorStateCertificate π) :
    NormalAffiliationBridge (A := A) (H := H) :=
  ofDiagonalRepresentation π (fun E =>
    NormalPVM.isDiagonalCountablyAdditive_of_normalVectorStateCertificate E π C)

/-- Build a faithful real normal bridge from the normality of unit-vector states and an injective
representation. -/
noncomputable def ofFaithfulNormalVectorStateCertificate (π : Representation A H)
    (C : NormalPVM.NormalVectorStateCertificate π) (hfaithful : Function.Injective π) :
    FaithfulNormalAffiliationBridge (A := A) (H := H) :=
  { ofNormalVectorStateCertificate π C with faithful := hfaithful }

/-! ### Complex predual bridges -/

/-- Extend a real normal bridge to complex normal affiliated operators using an explicit predual
representation of matrix coefficients for complex-valued PVMs. -/
noncomputable def NormalOperatorAffiliationBridge.ofPredualRepresentation
    (realBridge : NormalAffiliationBridge (A := A) (H := H))
    (predual : ∀ E : NormalPVM ℂ A, PredualPVM ℂ A)
    (hpredual : ∀ E : NormalPVM ℂ A, (predual E).toNormalPVM = E)
    (C : NormalPVM.PredualMatrixCoefficientCertificate realBridge.representation)
    (hmap : ∀ (E : NormalPVM ℂ A) {f : ℂ → ℂ} (hf : Measurable f),
      predual (E.map f hf) = (predual E).map f hf) :
    NormalOperatorAffiliationBridge (A := A) (H := H) where
  toNormalAffiliationBridge := realBridge
  toWOTSpectralMeasureComplex := fun E =>
    NormalPVM.toWOTSpectralMeasureOfPredual (predual E) realBridge.representation C
  toWOTSpectralMeasureComplex_apply := by
    intro E S
    change realBridge.representation (E S) =
      (NormalPVM.toWOTSpectralMeasureOfPredual
        (predual E) realBridge.representation C S).toCLM
    calc
      realBridge.representation (E S) =
          realBridge.representation ((predual E).toNormalPVM S) := by rw [hpredual E]
      _ = realBridge.representation ((predual E) S) := rfl
      _ = (NormalPVM.toWOTSpectralMeasureOfPredual
          (predual E) realBridge.representation C S).toCLM := by
        rw [NormalPVM.toWOTSpectralMeasure_of_predual_apply]
  toWOTSpectralMeasureComplex_map := by
    intro E f hf
    change NormalPVM.toWOTSpectralMeasureOfPredual
        (predual (E.map f hf)) realBridge.representation C =
      (NormalPVM.toWOTSpectralMeasureOfPredual
        (predual E) realBridge.representation C).map f hf
    rw [hmap E hf]
    exact NormalPVM.toWOTSpectralMeasure_of_predual_map (predual E)
      realBridge.representation C hf

/-- The faithful version of the complex predual extension. -/
noncomputable def FaithfulNormalOperatorAffiliationBridge.ofPredualRepresentation
    (realBridge : FaithfulNormalAffiliationBridge (A := A) (H := H))
    (predual : ∀ E : NormalPVM ℂ A, PredualPVM ℂ A)
    (hpredual : ∀ E : NormalPVM ℂ A, (predual E).toNormalPVM = E)
    (C : NormalPVM.PredualMatrixCoefficientCertificate realBridge.representation)
    (hmap : ∀ (E : NormalPVM ℂ A) {f : ℂ → ℂ} (hf : Measurable f),
      predual (E.map f hf) = (predual E).map f hf)
    (hfaithful : Function.Injective realBridge.representation) :
    FaithfulNormalOperatorAffiliationBridge (A := A) (H := H) :=
  { NormalOperatorAffiliationBridge.ofPredualRepresentation
      realBridge.toNormalAffiliationBridge predual hpredual C hmap with
    faithful := hfaithful }

/-! ## Canonical represented operator -/

/-- The weak-operator spectral measure obtained from a normal affiliated observable. -/
def representedSpectralMeasure (T : NormalAffiliatedObservable A) :
    QuantumMechanics.WOTSpectralMeasure ℝ H :=
  bridge.toWOTSpectralMeasure T.spectralMeasure

@[simp]
lemma representedSpectralMeasure_apply (T : NormalAffiliatedObservable A) (S : Set ℝ) :
    bridge.representedSpectralMeasure T S =
      ContinuousLinearMapWOT.ofCLM (bridge.representation (T.spectralMeasure S)) := by
  rw [bridge.toWOTSpectralMeasure_apply]
  rfl

lemma representedSpectralMeasure_projection_apply (T : NormalAffiliatedObservable A)
    (S : Set ℝ) :
    bridge.representation (T.spectralMeasure S) =
      (bridge.representedSpectralMeasure T S).toCLM := by
  exact bridge.toWOTSpectralMeasure_apply T.spectralMeasure S

lemma representedSpectralMeasure_measurableRealFC
    (T : NormalAffiliatedObservable A) {f : ℝ → ℝ} (hf : Measurable f) :
    bridge.representedSpectralMeasure (T.measurableRealFC f hf) =
      (bridge.representedSpectralMeasure T).map f hf := by
  exact bridge.toWOTSpectralMeasure_map T.spectralMeasure hf

/-- The canonical (maximal-domain) self-adjoint operator represented by `T`. -/
noncomputable def representedSelfAdjointOperator
    (T : NormalAffiliatedObservable A) : H →ₗ.[ℂ] H :=
  QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
    (bridge.representedSpectralMeasure T)

lemma representedSelfAdjointOperator_isSelfAdjoint
    (T : NormalAffiliatedObservable A) :
    IsSelfAdjoint (bridge.representedSelfAdjointOperator T) := by
  exact QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_isSelfAdjoint _

lemma representedSelfAdjointOperator_domain
    (T : NormalAffiliatedObservable A) :
    (bridge.representedSelfAdjointOperator T).domain =
      spectralSquareMomentDomain (bridge.representedSpectralMeasure T) := by
  rfl

lemma representedSelfAdjointOperator_measurableRealFC
    (T : NormalAffiliatedObservable A) {f : ℝ → ℝ} (hf : Measurable f) :
    bridge.representedSelfAdjointOperator (T.measurableRealFC f hf) =
      QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
        ((bridge.representedSpectralMeasure T).map f hf) := by
  change QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
    (bridge.representedSpectralMeasure (T.measurableRealFC f hf)) = _
  rw [bridge.representedSpectralMeasure_measurableRealFC T hf]

/-! ## The represented unitary dynamics -/

/-- The strongly continuous unitary group generated by the represented normal affiliated
observable.  Its value at `t` is the bounded spectral integral of
`λ ↦ exp (i t λ)`. -/
noncomputable def expUnitaryGroup
    (T : NormalAffiliatedObservable A) :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup H :=
  QuantumMechanics.WOTSpectralMeasure.expUnitaryGroup
    (bridge.representedSpectralMeasure T)

lemma expUnitaryGroup_zero (T : NormalAffiliatedObservable A) :
    bridge.expUnitaryGroup T 0 = 1 := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.zero _

lemma expUnitaryGroup_add (T : NormalAffiliatedObservable A) (t s : ℝ) :
    bridge.expUnitaryGroup T (t + s) =
      bridge.expUnitaryGroup T t * bridge.expUnitaryGroup T s := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.add _ t s

lemma expUnitaryGroup_continuous_apply (T : NormalAffiliatedObservable A) (x : H) :
    Continuous (fun t => bridge.expUnitaryGroup T t x) := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.continuous_apply _ x

lemma expUnitaryGroup_eq_expIntegral (T : NormalAffiliatedObservable A) (t : ℝ) :
    bridge.expUnitaryGroup T t =
      QuantumMechanics.WOTSpectralMeasure.expIntegral
        (bridge.representedSpectralMeasure T) t := by
  rfl

/-! ### Compatibility with the canonical abstract calculus -/

/-- The canonical algebra-level `exp (i t T)` is represented by the concrete spectral integral. -/
lemma represented_canonicalExpUnitary
    (W : NormalBorelRepresentationWitness bridge)
    (T : NormalAffiliatedObservable A) (t : ℝ) :
    bridge.representation ((T.canonicalExpUnitary t : unitary A) : A) =
      (bridge.expUnitaryGroup T t).toCLM := by
  change bridge.representation
      ((NormalBorelFunctionalCalculus.ofNormalPVM T.spectralMeasure).boundedFC
        (AffiliatedObservable.expFunction t)
        (AffiliatedObservable.expFunction_measurable t)
        (AffiliatedObservable.expFunction_bounded t)) = _
  exact W.represented_boundedFC T.spectralMeasure _ _ _

/-- The canonical algebra-level `exp (-i t T)` is represented by the time-reversed concrete
spectral integral. -/
lemma represented_canonicalNegativeExpUnitary
    (W : NormalBorelRepresentationWitness bridge)
    (T : NormalAffiliatedObservable A) (t : ℝ) :
    bridge.representation ((T.canonicalNegativeExpUnitary t : unitary A) : A) =
      (bridge.expUnitaryGroup T (-t)).toCLM := by
  change bridge.representation
      ((NormalBorelFunctionalCalculus.ofNormalPVM T.spectralMeasure).boundedFC
        (AffiliatedObservable.expFunction (-t))
        (AffiliatedObservable.expFunction_measurable (-t))
        (AffiliatedObservable.expFunction_bounded (-t))) = _
  exact W.represented_boundedFC T.spectralMeasure _ _ _

/-! ### The conventional quantum-dynamics sign -/

/-- The represented quantum-dynamics group `exp (-i t T)`, obtained by time reversal of
the canonical `exp (i t T)` group. -/
noncomputable def negativeExpUnitaryGroup
    (T : NormalAffiliatedObservable A) :
    QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup H :=
  { toFun := fun t => bridge.expUnitaryGroup T (-t)
    mem_unitary := fun t =>
      (bridge.expUnitaryGroup T).mem_unitary (-t)
    map_zero := by
      simpa using bridge.expUnitaryGroup_zero T
    map_add := by
      intro t s
      change bridge.expUnitaryGroup T (-(t + s)) =
        bridge.expUnitaryGroup T (-t) * bridge.expUnitaryGroup T (-s)
      rw [show -(t + s) = -t + -s by ring]
      exact bridge.expUnitaryGroup_add T (-t) (-s)
    strong_continuous := by
      intro x
      simpa [Function.comp_def] using
        (bridge.expUnitaryGroup_continuous_apply T x).comp continuous_neg }

lemma negativeExpUnitaryGroup_zero (T : NormalAffiliatedObservable A) :
    bridge.negativeExpUnitaryGroup T 0 = 1 := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.zero _

lemma negativeExpUnitaryGroup_add (T : NormalAffiliatedObservable A) (t s : ℝ) :
    bridge.negativeExpUnitaryGroup T (t + s) =
      bridge.negativeExpUnitaryGroup T t * bridge.negativeExpUnitaryGroup T s := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.add _ t s

lemma negativeExpUnitaryGroup_continuous_apply
    (T : NormalAffiliatedObservable A) (x : H) :
    Continuous (fun t => bridge.negativeExpUnitaryGroup T t x) := by
  exact QuantumMechanics.WOTSpectralMeasure.StrongUnitaryOneParameterGroup.continuous_apply _ x

/-! ### The star/inverse law -/

/-- The represented canonical group satisfies the star/inverse law: adjoint at time `t` equals
the group value at `-t`.  This is the `WOT`-level identity `expIntegral_star`, transported through
the represented spectral measure. -/
theorem expUnitaryGroup_star (T : NormalAffiliatedObservable A) (t : ℝ) :
    star (bridge.expUnitaryGroup T t) = bridge.expUnitaryGroup T (-t) :=
  QuantumMechanics.WOTSpectralMeasure.expIntegral_star (bridge.representedSpectralMeasure T) t

/-- The represented quantum-dynamics group satisfies the same star/inverse law, with the sign
inherited from the time reversal. -/
theorem negativeExpUnitaryGroup_star (T : NormalAffiliatedObservable A) (t : ℝ) :
    star (bridge.negativeExpUnitaryGroup T t) = bridge.negativeExpUnitaryGroup T (-t) := by
  have h := bridge.expUnitaryGroup_star T (-t)
  simpa [negativeExpUnitaryGroup, neg_neg] using h

/-! ## The represented resolvent -/

/-- The concrete bounded resolvent of the represented maximal realization.

This is deliberately a `WOT` operator rather than an element of `A`: the latter requires a
normal Borel-functional-calculus certificate on the abstract side.  The Hilbert-space spectral
integral already gives the bounded operator for every `z ∉ ℝ`, and the identity below makes its
resolvent law available without any additional affiliation assumptions. -/
noncomputable def representedResolvent
    (T : NormalAffiliatedObservable A) (z : ℂ) (hz : z.im ≠ 0) : H →WOT[ℂ] H :=
  QuantumMechanics.WOTSpectralMeasure.boundedIntegral
    (bridge.representedSpectralMeasure T)
    (AffiliatedObservable.resolventFunction z)
    (AffiliatedObservable.resolventFunction_measurable z)
    (AffiliatedObservable.resolventFunction_bounded z hz)

@[simp]
lemma representedResolvent_eq_boundedIntegral
    (T : NormalAffiliatedObservable A) (z : ℂ) (hz : z.im ≠ 0) :
    bridge.representedResolvent T z hz =
      QuantumMechanics.WOTSpectralMeasure.boundedIntegral
        (bridge.representedSpectralMeasure T)
        (AffiliatedObservable.resolventFunction z)
        (AffiliatedObservable.resolventFunction_measurable z)
        (AffiliatedObservable.resolventFunction_bounded z hz) := by
  rfl

/-- The represented bounded resolvent is the ordinary partial-map resolvent of the represented
maximal self-adjoint operator.  This is the general-parameter version of the two Cayley-shift
lemmas below; it is the theorem downstream applications should use when they need the resolvent
of the unbounded operator itself. -/
lemma representedResolvent_apply
    (T : NormalAffiliatedObservable A) (z : ℂ) (hz : z.im ≠ 0) (x : H) :
    bridge.representedResolvent T z hz x =
      (LinearPMap.resolvent (bridge.representedSelfAdjointOperator T) z)
        (⟨x, by
          rw [LinearPMap.inverse_domain]
          change x ∈
            (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
              (bridge.representedSpectralMeasure T) - z • (1 : H →ₗ.[ℂ] H)).toFun.range
          rw [QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_resolvent_range hz]
          exact Submodule.mem_top⟩) := by
  dsimp only [representedResolvent, representedSelfAdjointOperator]
  have hfun : AffiliatedObservable.resolventFunction z =
      QuantumMechanics.WOTSpectralMeasure.resolventMultiplier z := by
    funext r
    rfl
  have hconv := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_congr
    (μS := bridge.representedSpectralMeasure T)
    (AffiliatedObservable.resolventFunction_measurable z)
    (QuantumMechanics.WOTSpectralMeasure.resolventMultiplier_measurable z)
    (AffiliatedObservable.resolventFunction_bounded z hz)
    (QuantumMechanics.WOTSpectralMeasure.resolventMultiplier_bounded hz)
    (congrFun hfun)
  rw [hconv]
  exact (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_resolvent_apply
    (μS := bridge.representedSpectralMeasure T) hz x).symm

lemma representedResolvent_identity
    (T : NormalAffiliatedObservable A) (z w : ℂ)
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    bridge.representedResolvent T z hz - bridge.representedResolvent T w hw =
      (z - w) • (bridge.representedResolvent T z hz *
        bridge.representedResolvent T w hw) := by
  let μS := bridge.representedSpectralMeasure T
  let fz := AffiliatedObservable.resolventFunction z
  let fw := AffiliatedObservable.resolventFunction w
  have hfz : Measurable fz := AffiliatedObservable.resolventFunction_measurable z
  have hfw : Measurable fw := AffiliatedObservable.resolventFunction_measurable w
  have hbfz : ∃ C : ℝ, ∀ x, ‖fz x‖ ≤ C :=
    AffiliatedObservable.resolventFunction_bounded z hz
  have hbfw : ∃ C : ℝ, ∀ x, ‖fw x‖ ≤ C :=
    AffiliatedObservable.resolventFunction_bounded w hw
  have hprod : ∃ C : ℝ, ∀ x, ‖fz x * fw x‖ ≤ C := by
    rcases hbfz with ⟨Cz, hCz⟩
    rcases hbfw with ⟨Cw, hCw⟩
    refine ⟨Cz * Cw, fun x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hCz x) (hCw x) (norm_nonneg _)
      ((norm_nonneg (fz 0)).trans (hCz 0))
  have hscaled : ∃ C : ℝ, ∀ x, ‖(z - w) * (fz x * fw x)‖ ≤ C := by
    rcases hbfz with ⟨Cz, hCz⟩
    rcases hbfw with ⟨Cw, hCw⟩
    refine ⟨‖z - w‖ * (Cz * Cw), fun x => ?_⟩
    rw [norm_mul, norm_mul]
    exact mul_le_mul (le_rfl)
      (mul_le_mul (hCz x) (hCw x) (norm_nonneg _)
        ((norm_nonneg (fz 0)).trans (hCz 0)))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hdiff : ∃ C : ℝ, ∀ x, ‖(fz - fw) x‖ ≤ C := by
    rcases hbfz with ⟨Cz, hCz⟩
    rcases hbfw with ⟨Cw, hCw⟩
    refine ⟨Cz + Cw, fun x => ?_⟩
    simpa only [Pi.sub_apply] using
      (show ‖fz x - fw x‖ ≤ Cz + Cw from
        (norm_sub_le _ _).trans (add_le_add (hCz x) (hCw x)))
  have hsub := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_sub
    (μS := μS) hfz hfw hbfz hbfw
  have hmul := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_mul
    (μS := μS) hfz hfw hbfz hbfw
  have hsmul := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_smul
    (μS := μS) (z - w) (hfz.mul hfw) hprod
  calc
    bridge.representedResolvent T z hz - bridge.representedResolvent T w hw =
        QuantumMechanics.WOTSpectralMeasure.boundedIntegral μS (fz - fw)
          (hfz.sub hfw) hdiff := by
      exact hsub.symm
    _ = QuantumMechanics.WOTSpectralMeasure.boundedIntegral μS
        (fun x => (z - w) * (fz x * fw x))
        (measurable_const.mul (hfz.mul hfw)) hscaled := by
      apply QuantumMechanics.WOTSpectralMeasure.boundedIntegral_congr
        (μS := μS) (hfz.sub hfw) (measurable_const.mul (hfz.mul hfw)) hdiff hscaled
      intro x
      dsimp [fz, fw, AffiliatedObservable.resolventFunction]
      have hne_z : (x : ℂ) - z ≠ 0 := by
        intro h
        apply hz
        simpa using congrArg Complex.im h
      have hne_w : (x : ℂ) - w ≠ 0 := by
        intro h
        apply hw
        simpa using congrArg Complex.im h
      field_simp
      ring
    _ = (z - w) • QuantumMechanics.WOTSpectralMeasure.boundedIntegral μS
        (fz * fw) (hfz.mul hfw) hprod := hsmul
    _ = (z - w) • (bridge.representedResolvent T z hz *
        bridge.representedResolvent T w hw) := by
      rw [hmul]
      rfl

lemma representedSelfAdjointOperator_plus_resolvent_inverse_apply
    (T : NormalAffiliatedObservable A) (x : H) :
    (bridge.representedSelfAdjointOperator T + Complex.I • (1 : H →ₗ.[ℂ] H)).inverse
        ⟨x, by
          rw [LinearPMap.inverse_domain]
          change x ∈
            (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
              (bridge.representedSpectralMeasure T) + Complex.I •
                (1 : H →ₗ.[ℂ] H)).toFun.range
          rw [QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_plus_resolvent_range]
          exact Submodule.mem_top⟩ =
      bridge.representedResolvent T (-Complex.I) (by norm_num) x := by
  dsimp only [representedSelfAdjointOperator]
  have h :=
    QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_plus_resolvent_inverse_apply
      (μS := bridge.representedSpectralMeasure T) x
  have hfun : AffiliatedObservable.resolventFunction (-Complex.I) =
      QuantumMechanics.WOTSpectralMeasure.plusResolventMultiplier := by
    funext r
    simp [AffiliatedObservable.resolventFunction,
      QuantumMechanics.WOTSpectralMeasure.plusResolventMultiplier]
  have hconv := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_congr
    (μS := bridge.representedSpectralMeasure T)
    (AffiliatedObservable.resolventFunction_measurable (-Complex.I))
    QuantumMechanics.WOTSpectralMeasure.plusResolventMultiplier_measurable
    (AffiliatedObservable.resolventFunction_bounded (-Complex.I) (by norm_num))
    QuantumMechanics.WOTSpectralMeasure.plusResolventMultiplier_bounded (congrFun hfun)
  dsimp only [representedResolvent]
  rw [hconv]
  exact h

lemma representedSelfAdjointOperator_minus_resolvent_inverse_apply
    (T : NormalAffiliatedObservable A) (x : H) :
    (bridge.representedSelfAdjointOperator T - Complex.I • (1 : H →ₗ.[ℂ] H)).inverse
        ⟨x, by
          rw [LinearPMap.inverse_domain]
          change x ∈
            (QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
              (bridge.representedSpectralMeasure T) - Complex.I •
                (1 : H →ₗ.[ℂ] H)).toFun.range
          rw [QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_minus_resolvent_range]
          exact Submodule.mem_top⟩ =
      bridge.representedResolvent T Complex.I (by norm_num) x := by
  dsimp only [representedSelfAdjointOperator]
  have h :=
    QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral_minus_resolvent_inverse_apply
      (μS := bridge.representedSpectralMeasure T) x
  have hfun : AffiliatedObservable.resolventFunction Complex.I =
      QuantumMechanics.WOTSpectralMeasure.minusResolventMultiplier := by
    funext r
    simp [AffiliatedObservable.resolventFunction,
      QuantumMechanics.WOTSpectralMeasure.minusResolventMultiplier]
  have hconv := QuantumMechanics.WOTSpectralMeasure.boundedIntegral_congr
    (μS := bridge.representedSpectralMeasure T)
    (AffiliatedObservable.resolventFunction_measurable Complex.I)
    QuantumMechanics.WOTSpectralMeasure.minusResolventMultiplier_measurable
    (AffiliatedObservable.resolventFunction_bounded Complex.I (by norm_num))
    QuantumMechanics.WOTSpectralMeasure.minusResolventMultiplier_bounded (congrFun hfun)
  dsimp only [representedResolvent]
  rw [hconv]
  exact h

/-! ## The represented Stone generator -/

lemma expUnitaryGroup_strong_slope_tendsto
    (T : NormalAffiliatedObservable A)
    (x : (bridge.representedSelfAdjointOperator T).domain) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ •
        (bridge.expUnitaryGroup T t (x : H) - (x : H)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (Complex.I • bridge.representedSelfAdjointOperator T x)) := by
  cases x with
  | mk x hx =>
      change Filter.Tendsto
        (fun t : ℝ => t⁻¹ •
          (QuantumMechanics.WOTSpectralMeasure.expIntegral
            (bridge.representedSpectralMeasure T) t x - x))
        (𝓝[≠] (0 : ℝ))
        (𝓝 (Complex.I •
          QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
            (bridge.representedSpectralMeasure T) (⟨x, hx⟩)))
      exact QuantumMechanics.WOTSpectralMeasure.expIntegral_strong_slope_tendsto
        (bridge.representedSpectralMeasure T) x hx

lemma expUnitaryGroup_hasDerivAt_zero
    (T : NormalAffiliatedObservable A)
    (x : (bridge.representedSelfAdjointOperator T).domain) :
    HasDerivAt (fun t : ℝ => bridge.expUnitaryGroup T t (x : H))
      (Complex.I • bridge.representedSelfAdjointOperator T x) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  convert bridge.expUnitaryGroup_strong_slope_tendsto T x using 1
  funext t
  simp [slope, bridge.expUnitaryGroup_zero T]

theorem representedSelfAdjointOperator_measurableRealFC_eq_measurableSpectralIntegral
    (T : NormalAffiliatedObservable A) {f : ℝ → ℝ} (hf : Measurable f) :
    bridge.representedSelfAdjointOperator (T.measurableRealFC f hf) =
      QuantumMechanics.WOTSpectralMeasure.measurableSpectralIntegral
        (bridge.representedSpectralMeasure T) f hf := by
  exact bridge.representedSelfAdjointOperator_measurableRealFC T hf

end NormalAffiliationBridge

namespace NormalOperatorAffiliationBridge

variable (bridge : NormalOperatorAffiliationBridge (A := A) (H := H))

/-! ### Constructing the complex bridge -/

/-- Build the real-and-complex representation bridge from matrix-coefficient σ-additivity.

The two certificates are kept separate because the real and complex affiliated façades have
different spectral spaces.  In a concrete von Neumann algebra representation they normally come
from the same normality theorem, but requiring both here prevents an accidental use of a real
certificate for a genuinely complex normal operator. -/
noncomputable def ofRepresentation (π : Representation A H)
    (hreal : ∀ E : NormalPVM ℝ A,
      NormalPVM.IsWOTCountablyAdditive E π)
    (hcomplex : ∀ E : NormalPVM ℂ A,
      NormalPVM.IsWOTCountablyAdditive E π) :
    NormalOperatorAffiliationBridge (A := A) (H := H) where
  representation := π
  toWOTSpectralMeasure := fun E => NormalPVM.toWOTSpectralMeasure E π (hreal E)
  toWOTSpectralMeasure_apply := by
    intro E S
    rw [NormalPVM.toWOTSpectralMeasure_apply]
  toWOTSpectralMeasure_map := by
    intro E f hf
    exact NormalPVM.toWOTSpectralMeasure_map E π (hreal E) hf
  toWOTSpectralMeasureComplex :=
    fun E => NormalPVM.toWOTSpectralMeasure E π (hcomplex E)
  toWOTSpectralMeasureComplex_apply := by
    intro E S
    rw [NormalPVM.toWOTSpectralMeasure_apply]
  toWOTSpectralMeasureComplex_map := by
    intro E f hf
    exact NormalPVM.toWOTSpectralMeasure_map E π (hcomplex E) hf

/-- Build the real-and-complex representation bridge from diagonal matrix-coefficient
σ-additivity. -/
noncomputable def ofDiagonalRepresentation (π : Representation A H)
    (hreal : ∀ E : NormalPVM ℝ A,
      NormalPVM.IsDiagonalCountablyAdditive E π)
    (hcomplex : ∀ E : NormalPVM ℂ A,
      NormalPVM.IsDiagonalCountablyAdditive E π) :
    NormalOperatorAffiliationBridge (A := A) (H := H) :=
  NormalOperatorAffiliationBridge.ofRepresentation π
    (fun E => NormalPVM.isWOTCountablyAdditive_of_diagonal E π (hreal E))
    (fun E => NormalPVM.isWOTCountablyAdditive_of_diagonal E π (hcomplex E))

/-- Build the real-and-complex representation bridge from the normality of all unit-vector
states.  The same vector-state certificate applies to both measurable spectral spaces. -/
noncomputable def ofNormalVectorStateCertificate (π : Representation A H)
    (C : NormalPVM.NormalVectorStateCertificate π) :
    NormalOperatorAffiliationBridge (A := A) (H := H) :=
  NormalOperatorAffiliationBridge.ofDiagonalRepresentation π
    (fun E => NormalPVM.isDiagonalCountablyAdditive_of_normalVectorStateCertificate E π C)
    (fun E => NormalPVM.isDiagonalCountablyAdditive_of_normalVectorStateCertificate E π C)

/-- Build a faithful real-and-complex normal bridge from the normality of unit-vector states and an
injective representation. -/
noncomputable def ofFaithfulNormalVectorStateCertificate (π : Representation A H)
    (C : NormalPVM.NormalVectorStateCertificate π) (hfaithful : Function.Injective π) :
    FaithfulNormalOperatorAffiliationBridge (A := A) (H := H) :=
  { ofNormalVectorStateCertificate π C with faithful := hfaithful }

/-- The weak-operator spectral measure represented by a complex normal affiliated operator. -/
def representedSpectralMeasure (T : NormalAffiliatedOperator A) :
    QuantumMechanics.WOTSpectralMeasure ℂ H :=
  bridge.toWOTSpectralMeasureComplex T.spectralMeasure

@[simp]
lemma representedSpectralMeasure_apply (T : NormalAffiliatedOperator A) (S : Set ℂ) :
    bridge.representedSpectralMeasure T S =
      ContinuousLinearMapWOT.ofCLM (bridge.representation (T.spectralMeasure S)) := by
  rw [bridge.toWOTSpectralMeasureComplex_apply]
  rfl

lemma representedSpectralMeasure_measurableFC
    (T : NormalAffiliatedOperator A) {f : ℂ → ℂ} (hf : Measurable f) :
    bridge.representedSpectralMeasure (T.measurableFC f hf) =
      (bridge.representedSpectralMeasure T).map f hf := by
  exact bridge.toWOTSpectralMeasureComplex_map T.spectralMeasure hf

end NormalOperatorAffiliationBridge

/-- The predual vector-state certificate produced by weak-star continuity of all matrix
coefficients. -/
noncomputable def NormalRepresentation.toNormalVectorStateCertificate
    (π : NormalRepresentation (A := A) (H := H)) :
    NormalPVM.NormalVectorStateCertificate π.representation where
  state := fun x hx => normalVectorState π x hx
  apply := by intro x hx a; rfl

/-- Construct the real normal-affiliation bridge directly from a normal representation. -/
noncomputable def NormalRepresentation.toNormalAffiliationBridge
    (π : NormalRepresentation (A := A) (H := H)) :
    NormalAffiliationBridge (A := A) (H := H) :=
  NormalAffiliationBridge.ofNormalVectorStateCertificate
    π.representation π.toNormalVectorStateCertificate

/-- Construct a faithful real normal-affiliation bridge directly from a faithful normal
representation. -/
noncomputable def NormalRepresentation.toFaithfulNormalAffiliationBridge
    (π : NormalRepresentation (A := A) (H := H))
    (hfaithful : Function.Injective π.representation) :
    FaithfulNormalAffiliationBridge (A := A) (H := H) :=
  NormalAffiliationBridge.ofFaithfulNormalVectorStateCertificate
    π.representation π.toNormalVectorStateCertificate hfaithful

/-- Construct the real-and-complex normal-affiliation bridge directly from a normal
representation. -/
noncomputable def NormalRepresentation.toNormalOperatorAffiliationBridge
    (π : NormalRepresentation (A := A) (H := H)) :
    NormalOperatorAffiliationBridge (A := A) (H := H) :=
  NormalOperatorAffiliationBridge.ofNormalVectorStateCertificate
    π.representation π.toNormalVectorStateCertificate

/-- Construct a faithful real-and-complex normal-affiliation bridge directly from a faithful
normal representation. -/
noncomputable def NormalRepresentation.toFaithfulNormalOperatorAffiliationBridge
    (π : NormalRepresentation (A := A) (H := H))
    (hfaithful : Function.Injective π.representation) :
    FaithfulNormalOperatorAffiliationBridge (A := A) (H := H) :=
  NormalOperatorAffiliationBridge.ofFaithfulNormalVectorStateCertificate
    π.representation π.toNormalVectorStateCertificate hfaithful

namespace DomainAwareSelfAdjointSpectralTheorem

variable {T : H →ₗ.[ℂ] H}
variable {μS : QuantumMechanics.WOTSpectralMeasure ℝ H}

/-! ## Consuming a domain-aware theorem -/

/-- A domain-aware spectral theorem identifies the bridge's canonical maximal realization with the
given self-adjoint operator, once its represented spectral measure is identified with the theorem's
measure. -/
theorem representedNormalSelfAdjointOperator_eq
    (D : DomainAwareSelfAdjointSpectralTheorem T μS)
    (bridge : NormalAffiliationBridge (A := A) (H := H))
    (S : NormalAffiliatedObservable A)
    (hS : bridge.representedSpectralMeasure S = μS) :
    bridge.representedSelfAdjointOperator S = T := by
  change QuantumMechanics.WOTSpectralMeasure.maximalSpectralIntegral
    (bridge.representedSpectralMeasure S) = T
  rw [hS]
  exact D.maximal_eq

end DomainAwareSelfAdjointSpectralTheorem

end OperatorAlgebra

end
