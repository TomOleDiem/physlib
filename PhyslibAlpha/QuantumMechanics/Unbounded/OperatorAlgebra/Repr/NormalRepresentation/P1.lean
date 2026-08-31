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
# Normal affiliated observables in a Hilbert-space representation (part 1 of 2)

Split out of `NormalRepresentation.lean` to stay under the file-length style limit; see
`NormalRepresentation.lean` for the full module overview. This part covers the WOT-measure
construction from a normality certificate through the finite-dimensional and Borel representation
certificates.
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

end OperatorAlgebra

end
