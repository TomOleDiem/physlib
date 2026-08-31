/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.FiniteDim.StateRepresentation
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.VectorState

/-!

# Pure states in finite dimensions

The finite-dimensional pure-state theory: vector states are pure, every finite-dimensional state
is a finite convex mixture of vector states (from the spectral decomposition of its density
operator), and a state is pure exactly when its density operator is a rank-one projector.

`vectorState` itself is the general, non-finite-dimensional one from `OperatorAlgebra.
VectorState`; this file only adds the finite-dimensional fact that it corresponds to the
rank-one density operator (`stateToDensityOperator_vectorState`).

The central geometric fact is `densityOperator_rankOne_extreme`: a rank-one density operator is
an extreme point of the convex set of density operators. This is proved from one reusable
positive-operator lemma, `eq_smul_rankOne_of_nonneg_of_orthogonal_kernel`: a positive operator
that vanishes on the orthogonal complement of a unit vector `ψ` is a nonnegative scalar multiple
of the rank-one projector onto `ψ`.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

/-- The density operator of a vector state is the rank-one projector onto that vector. -/
@[simp]
lemma stateToDensityOperator_vectorState (ψ : H) (hψ : ‖ψ‖ = 1) :
    stateToDensityOperator (vectorState ψ hψ) = DensityOperator.rankOne ψ hψ := by
  apply Subtype.ext
  show densityOperatorOfState (vectorState ψ hψ) = InnerProductSpace.rankOne ℂ ψ ψ
  have hlin : (vectorState ψ hψ).toPositiveLinearMap.toLinearMap =
      operatorTracePairing (InnerProductSpace.rankOne ℂ ψ ψ) :=
    LinearMap.ext fun A => (operatorTracePairing_rankOne_left ψ ψ A).symm
  show (LinearMap.BilinForm.toDual (operatorTracePairing (H := H))
    operatorTracePairing_nondegenerate).symm
    (vectorState ψ hψ).toPositiveLinearMap.toLinearMap = _
  rw [hlin]
  exact (LinearMap.BilinForm.toDual (operatorTracePairing (H := H))
    operatorTracePairing_nondegenerate).symm_apply_apply _

/-!
## Rank-one extremality

A rank-one density operator is an extreme point of the convex set of density operators.
-/

omit [FiniteDimensional ℂ H] in
/-- A positive operator bounded above by a rank-one projector `|ψ⟩⟨ψ|` vanishes on the
orthogonal complement of `ψ`. -/
lemma apply_eq_zero_of_nonneg_of_le_rankOne {T : B(H)} (hT : 0 ≤ T) (ψ x : H)
    (hle : T ≤ InnerProductSpace.rankOne ℂ ψ ψ) (hx : ⟪ψ, x⟫_ℂ = 0) :
    T x = 0 := by
  have hPx : InnerProductSpace.rankOne ℂ ψ ψ x = 0 := by
    simp [InnerProductSpace.rankOne_apply, hx]
  have h1 := ((operator_nonneg_iff_isPositive _).mp (sub_nonneg.mpr hle)).inner_nonneg_right x
  have h2 := ((operator_nonneg_iff_isPositive T).mp hT).inner_nonneg_right x
  rw [sub_apply, inner_sub_right, hPx, inner_zero_right, zero_sub] at h1
  have hz : ⟪x, T x⟫_ℂ = 0 := by
    apply Complex.ext
    · have hre1 := (Complex.le_def.mp h1).1
      have hre2 := (Complex.le_def.mp h2).1
      simp only [Complex.neg_re, Complex.zero_re] at hre1 hre2 ⊢
      linarith
    · simpa using (Complex.le_def.mp h2).2.symm
  apply operator_apply_eq_zero_of_inner_eq_zero hT x
  rw [← inner_conj_symm, hz]
  simp

omit [FiniteDimensional ℂ H] in
/-- A positive operator supported on a one-dimensional projection is a nonnegative scalar
multiple of that projection: if `T ≥ 0` vanishes on the orthogonal complement of a unit vector
`ψ`, then `T = c • |ψ⟩⟨ψ|` for some `c ≥ 0`. -/
lemma eq_smul_rankOne_of_nonneg_of_orthogonal_kernel {T : B(H)} (hT : 0 ≤ T)
    (ψ : H) (hψ : ‖ψ‖ = 1) (hker : ∀ x, ⟪ψ, x⟫_ℂ = 0 → T x = 0) :
    ∃ c : ℝ, 0 ≤ c ∧ T = (c : ℂ) • InnerProductSpace.rankOne ℂ ψ ψ := by
  let P : B(H) := InnerProductSpace.rankOne ℂ ψ ψ
  have hright : T = T * P := by
    apply ContinuousLinearMap.ext
    intro x
    have hy : ⟪ψ, x - P x⟫_ℂ = 0 := by
      simp [P, InnerProductSpace.rankOne_apply, inner_self_eq_norm_sq_to_K, hψ]
    have hzero := hker (x - P x) hy
    calc
      T x = T (P x + (x - P x)) := by congr 1; abel
      _ = T (P x) + T (x - P x) := map_add _ _ _
      _ = T (P x) := by rw [hzero, add_zero]
      _ = (T * P) x := rfl
  have hTstar : star T = T := (IsSelfAdjoint.of_nonneg hT).star_eq
  have hPstar : star P = P :=
    (IsSelfAdjoint.of_nonneg
      ((operator_nonneg_iff_isPositive P).mpr
        (InnerProductSpace.isPositive_rankOne_self ψ))).star_eq
  have hleft : P * T = T := by
    have h := congrArg star hright
    simpa [star_mul, hTstar, hPstar] using h.symm
  have hcompression : T = P * T * P := by
    have hp := congrArg (fun S : B(H) => P * S) hright
    calc
      T = P * T := hleft.symm
      _ = P * T * P := by simpa [mul_assoc] using hp
  have hscalar : T = ⟪ψ, T ψ⟫_ℂ • P := by
    rw [hcompression]
    apply ContinuousLinearMap.ext
    intro x
    simp [mul_apply_eq_comp, P, InnerProductSpace.rankOne_apply,
      inner_self_eq_norm_sq_to_K, hψ, smul_smul]
    module
  have hpos := ((operator_nonneg_iff_isPositive T).mp hT).inner_nonneg_right ψ
  set c : ℝ := (⟪ψ, T ψ⟫_ℂ).re with hcdef
  have hceq : ⟪ψ, T ψ⟫_ℂ = (c : ℂ) := by
    apply Complex.ext
    · simp [hcdef]
    · simpa using (Complex.le_def.mp hpos).2.symm
  exact ⟨c, (Complex.le_def.mp hpos).1, by rw [hscalar, hceq]⟩

/-- A density operator with kernel orthogonal to a unit vector `ψ` is the rank-one projector
onto `ψ`: the trace-one normalization of `eq_smul_rankOne_of_nonneg_of_orthogonal_kernel`. -/
lemma densityOperator_eq_rankOne_of_orthogonal_kernel (σ : DensityOperator H) (ψ : H)
    (hψ : ‖ψ‖ = 1) (hker : ∀ x, ⟪ψ, x⟫_ℂ = 0 → σ.1 x = 0) :
    σ = DensityOperator.rankOne ψ hψ := by
  obtain ⟨c, _, hc⟩ := eq_smul_rankOne_of_nonneg_of_orthogonal_kernel σ.2.1 ψ hψ hker
  have htr := σ.2.2
  rw [hc, ContinuousLinearMap.toLinearMap_smul, map_smul,
    InnerProductSpace.trace_rankOne, inner_self_eq_norm_sq_to_K, hψ] at htr
  have hc1 : c = 1 := by exact_mod_cast show (c : ℂ) = 1 by simpa using htr
  exact Subtype.ext (by simp [hc, hc1])

/-- A rank-one density operator is an extreme point of the convex set of density operators. -/
theorem densityOperator_rankOne_extreme (σ τ : DensityOperator H) (ψ : H) (hψ : ‖ψ‖ = 1)
    (t : ℝ) (ht₀ : 0 < t) (ht₁ : t < 1)
    (hmix : (t : ℂ) • σ.1 + ((1 - t : ℝ) : ℂ) • τ.1 =
      InnerProductSpace.rankOne ℂ ψ ψ) :
    σ = DensityOperator.rankOne ψ hψ ∧ τ = DensityOperator.rankOne ψ hψ := by
  have htC : (0 : ℂ) ≤ (t : ℂ) := RCLike.ofReal_nonneg.mpr ht₀.le
  have ht'C : (0 : ℂ) ≤ ((1 - t : ℝ) : ℂ) := RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr ht₁.le)
  have htne : (t : ℂ) ≠ 0 := by exact_mod_cast ht₀.ne'
  have ht'ne : ((1 - t : ℝ) : ℂ) ≠ 0 := by
    have h : (1 - t : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr ht₁)
    exact_mod_cast h
  have hσpos : 0 ≤ (t : ℂ) • σ.1 :=
    (operator_nonneg_iff_isPositive _).mpr
      (((operator_nonneg_iff_isPositive σ.1).mp σ.2.1).smul_of_nonneg htC)
  have hτpos : 0 ≤ ((1 - t : ℝ) : ℂ) • τ.1 :=
    (operator_nonneg_iff_isPositive _).mpr
      (((operator_nonneg_iff_isPositive τ.1).mp τ.2.1).smul_of_nonneg ht'C)
  have hσle : (t : ℂ) • σ.1 ≤ InnerProductSpace.rankOne ℂ ψ ψ := by
    rw [← hmix]; exact le_add_of_nonneg_right hτpos
  have hτle : ((1 - t : ℝ) : ℂ) • τ.1 ≤ InnerProductSpace.rankOne ℂ ψ ψ := by
    rw [← hmix, add_comm]; exact le_add_of_nonneg_right hσpos
  have hσzero : ∀ x, ⟪ψ, x⟫_ℂ = 0 → σ.1 x = 0 := fun x hx => by
    have h0 := apply_eq_zero_of_nonneg_of_le_rankOne hσpos ψ x hσle hx
    rw [smul_apply, smul_eq_zero] at h0
    exact h0.resolve_left htne
  have hτzero : ∀ x, ⟪ψ, x⟫_ℂ = 0 → τ.1 x = 0 := fun x hx => by
    have h0 := apply_eq_zero_of_nonneg_of_le_rankOne hτpos ψ x hτle hx
    rw [smul_apply, smul_eq_zero] at h0
    exact h0.resolve_left ht'ne
  exact ⟨densityOperator_eq_rankOne_of_orthogonal_kernel σ ψ hψ hσzero,
    densityOperator_eq_rankOne_of_orthogonal_kernel τ ψ hψ hτzero⟩

/-!
## Vector states are pure, and every state is a finite mixture of them
-/

/-- A unit vector defines a pure state. -/
lemma vectorState_isPure (ψ : H) (hψ : ‖ψ‖ = 1) :
    State.IsPure (vectorState ψ hψ) := by
  intro φ χ t ht₀ ht₁ hmix
  have hop : (t : ℂ) • (stateToDensityOperator φ).1 +
      ((1 - t : ℝ) : ℂ) • (stateToDensityOperator χ).1 =
      InnerProductSpace.rankOne ℂ ψ ψ := by
    have h := congrArg densityOperatorOfState hmix
    rw [densityOperatorOfState_mix] at h
    have hv : densityOperatorOfState (vectorState ψ hψ) =
        InnerProductSpace.rankOne ℂ ψ ψ :=
      congrArg Subtype.val (stateToDensityOperator_vectorState ψ hψ)
    rwa [hv] at h
  obtain ⟨hφ, hχ⟩ := densityOperator_rankOne_extreme
    (stateToDensityOperator φ) (stateToDensityOperator χ) ψ hψ t ht₀ ht₁ hop
  refine ⟨stateEquivDensityOperator.injective ?_, stateEquivDensityOperator.injective ?_⟩
  · simp [hφ]
  · simp [hχ]

/-- The spectral decomposition of a state, bundled as an equality with a finite convex mixture
of pure vector states. The weights and vectors come from the spectral decomposition of the
state's density operator. -/
theorem state_eq_finiteMix_spectralDecomposition (ω : State (B(H))) :
    ∃ (p : Fin (Module.finrank ℂ H) → ℝ)
      (ψ : Fin (Module.finrank ℂ H) → H)
      (hψ : ∀ i, ‖ψ i‖ = 1)
      (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1),
      (∀ i, State.IsPure (vectorState (ψ i) (hψ i))) ∧
        State.finiteMix (fun i => vectorState (ψ i) (hψ i)) p hp hsum = ω := by
  obtain ⟨p, ψ, hp, hψ, hsum, hop⟩ :=
    DensityOperator.spectralDecomposition (stateToDensityOperator ω)
  refine ⟨p, ψ, hψ, hp, hsum, fun i => vectorState_isPure (ψ i) (hψ i), ?_⟩
  rw [State.mk.injEq]
  apply PositiveLinearMap.ext
  intro A
  rw [State.finiteMix_apply, stateEquivDensityOperator_expectation]
  change (∑ i, (p i : ℂ) * vectorState (ψ i) (hψ i) A) =
    operatorTracePairing (stateToDensityOperator ω).1 A
  rw [hop, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change (p i : ℂ) * vectorState (ψ i) (hψ i) A =
    operatorTracePairing ((p i : ℂ) • InnerProductSpace.rankOne ℂ (ψ i) (ψ i)) A
  rw [map_smul, LinearMap.smul_apply, vectorState_apply, operatorTracePairing_rankOne_left]
  rfl

/-- Every finite-dimensional state is a finite convex combination of pure vector states. -/
theorem state_spectralDecomposition (ω : State (B(H))) :
    ∃ (p : Fin (Module.finrank ℂ H) → ℝ)
      (ψ : Fin (Module.finrank ℂ H) → H)
      (hψ : ∀ i, ‖ψ i‖ = 1),
      (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
        (∀ i, State.IsPure (vectorState (ψ i) (hψ i))) ∧
          ∀ A, ω A = ∑ i, (p i : ℂ) * vectorState (ψ i) (hψ i) A := by
  obtain ⟨p, ψ, hψ, hp, hsum, hpure, hmix⟩ := state_eq_finiteMix_spectralDecomposition ω
  exact ⟨p, ψ, hψ, hp, hsum, hpure, fun A => by rw [← hmix, State.finiteMix_apply]⟩

/-!
## Pure states are exactly rank-one density operators
-/

/-- A state on `B(H)` is pure exactly when its density operator is a rank-one projector. -/
theorem state_isPure_iff_densityOperator_isRankOneProjector
    (ω : State (B(H))) :
    ω.IsPure ↔ DensityOperator.IsRankOneProjector (stateToDensityOperator ω) := by
  constructor
  · intro hω
    obtain ⟨p, ψ, hψ, hp, hsum, _, hmix⟩ :=
      state_eq_finiteMix_spectralDecomposition ω
    have hex : ∃ i, 0 < p i := by
      by_contra h
      push Not at h
      have hz : ∀ i, p i = 0 := fun i => le_antisymm (h i) (hp i)
      have : ∑ i, p i = 0 := by simp [hz]
      linarith
    obtain ⟨i, hi⟩ := hex
    have hstate := State.IsPure.eq_of_finiteMix ω hω
      (fun i => vectorState (ψ i) (hψ i)) p hp hsum hmix hi
    refine ⟨ψ i, hψ i, ?_⟩
    have hd : densityOperatorOfState (vectorState (ψ i) (hψ i)) =
        densityOperatorOfState ω := congrArg densityOperatorOfState hstate
    have hv : densityOperatorOfState (vectorState (ψ i) (hψ i)) =
        InnerProductSpace.rankOne ℂ (ψ i) (ψ i) :=
      congrArg Subtype.val (stateToDensityOperator_vectorState (ψ i) (hψ i))
    calc
      (stateToDensityOperator ω).1 = densityOperatorOfState ω := rfl
      _ = densityOperatorOfState (vectorState (ψ i) (hψ i)) := hd.symm
      _ = InnerProductSpace.rankOne ℂ (ψ i) (ψ i) := hv
  · rintro ⟨ψ, hψ, hρ⟩
    have hd : stateToDensityOperator ω = DensityOperator.rankOne ψ hψ := Subtype.ext hρ
    have hstate : ω = vectorState ψ hψ := by
      apply stateEquivDensityOperator.injective
      simp [hd]
    rw [hstate]
    exact vectorState_isPure ψ hψ

end OperatorAlgebra
