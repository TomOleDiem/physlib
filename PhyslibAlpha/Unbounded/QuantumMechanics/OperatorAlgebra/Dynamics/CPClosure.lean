/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Basic

/-!
# Closure of complete positivity

The cone of completely positive maps is closed under pointwise limits of bounded linear maps.  This
is the analytic lemma needed whenever a quantum evolution is obtained as a limit of CP
approximants, for example through a product formula or a Dyson series.

The statement is intentionally independent of Hilbert-space representations and finite
dimensionality.  The only topology used is the operator-norm topology on the bounded linear maps;
positivity of each matrix amplification is closed in the finite matrix C⋆-algebra.
-/

@[expose] public section

namespace OperatorAlgebra

open Filter
open scoped CStarAlgebra NNReal

variable {A B : Type*} [OperatorAlgebra A] [OperatorAlgebra B]

noncomputable local instance cpClosureNormedAlgebraRat : NormedAlgebra ℚ (A →L[ℂ] A) :=
  .restrictScalars ℚ ℂ (A →L[ℂ] A)

noncomputable local instance cpClosureNormedAlgebraReal : NormedAlgebra ℝ (A →L[ℂ] A) :=
  .restrictScalars ℝ ℂ (A →L[ℂ] A)

/-! ### Algebraic closure operations -/

/-- Every completely positive linear map is bounded, hence has a canonical continuous extension.

This is the bridge between the algebraic CP API and the Banach-space exponential. -/
noncomputable def completelyPositiveMap_toContinuousLinearMap
    (φ : CompletelyPositiveMap A B) : A →L[ℂ] B := by
  let h := PositiveLinearMap.exists_norm_apply_le (PositiveLinearMap.ofClass φ)
  let C : NNReal := Classical.choose h
  exact LinearMap.mkContinuousOfExistsBound φ.toLinearMap
    ⟨(C : ℝ), by
      intro a
      change ‖(PositiveLinearMap.ofClass φ) a‖ ≤ (C : ℝ) * ‖a‖
      simpa [C] using (Classical.choose_spec h a)⟩

@[simp]
lemma completelyPositiveMap_toContinuousLinearMap_apply
    (φ : CompletelyPositiveMap A B) (a : A) :
    completelyPositiveMap_toContinuousLinearMap φ a = φ a := by
  change φ.toLinearMap a = φ a
  rfl

/-- The identity bounded map, packaged as a completely positive map. -/
noncomputable def completelyPositiveMap_id (A : Type*) [OperatorAlgebra A] :
    CompletelyPositiveMap A A := by
  refine { toLinearMap := ContinuousLinearMap.id ℂ A, map_cstarMatrix_nonneg' := ?_ }
  intro k M hM
  simpa using hM

@[simp]
lemma completelyPositiveMap_id_toLinearMap (A : Type*) [OperatorAlgebra A] :
    (completelyPositiveMap_id A).toLinearMap = ContinuousLinearMap.id ℂ A :=
  rfl

@[simp]
lemma completelyPositiveMap_id_apply (A : Type*) [OperatorAlgebra A] (a : A) :
    completelyPositiveMap_id A a = a := by
  rfl

/-! ### Completely positive conjugations -/

/-- Conjugation by an element of a C⋆-algebra is completely positive.

This is the algebraic version of the familiar map `a ↦ W⋆ a W`.  It is used by the
Christensen–Evans construction and does not require a Hilbert-space representation. -/
noncomputable def completelyPositiveMap_conjugation (W : A) : A →CP A := by
  refine CompletelyPositiveMap.mk
    (ContinuousLinearMap.mulLeftRight ℂ A (star W) W).toLinearMap ?_
  intro k M hM
  let C : CStarMatrix (Fin k) (Fin k) A := Matrix.diagonal (fun _ => W)
  have h := star_left_conjugate_nonneg hM C
  convert h using 1
  apply CStarMatrix.ext
  intro i j
  change star W * M i j * W =
    ∑ l, (∑ q, star (if q = i then W else 0) * M q l) *
      (if l = j then W else 0)
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_eq_single i]
    · simp
    · intro q hq hqi
      simp [hqi]
    · simp
  · intro l hl hlj
    simp [hlj]
  · simp

@[simp]
lemma completelyPositiveMap_conjugation_apply (W a : A) :
    completelyPositiveMap_conjugation W a = star W * a * W :=
  rfl

lemma completelyPositiveMap_conjugation_toContinuousLinearMap (W : A) :
    completelyPositiveMap_toContinuousLinearMap (completelyPositiveMap_conjugation W) =
      ContinuousLinearMap.mulLeftRight ℂ A (star W) W := by
  ext a
  simp [completelyPositiveMap_conjugation_apply,
    ContinuousLinearMap.mulLeftRight_apply]

lemma completelyPositiveMap_comp_toContinuousLinearMap
    {A B C : Type*} [OperatorAlgebra A] [OperatorAlgebra B] [OperatorAlgebra C]
    (φ : B →CP C) (ψ : A →CP B) :
    completelyPositiveMap_toContinuousLinearMap (completelyPositiveMap_comp φ ψ) =
      (completelyPositiveMap_toContinuousLinearMap φ).comp
        (completelyPositiveMap_toContinuousLinearMap ψ) := by
  ext a
  rfl

lemma completelyPositiveMap_comp_toContinuousLinearMap_self
    {A : Type*} [OperatorAlgebra A]
    (φ ψ : A →CP A) :
    completelyPositiveMap_toContinuousLinearMap (completelyPositiveMap_comp φ ψ) =
      completelyPositiveMap_toContinuousLinearMap φ *
        completelyPositiveMap_toContinuousLinearMap ψ := by
  ext a
  simp [mul_apply_eq_comp]

lemma completelyPositiveMap_map_star (φ : A →CP A) (a : A) :
    star (φ a) = φ (star a) := by
  obtain ⟨x, hx, _, ha⟩ := CStarAlgebra.exists_sum_four_nonneg a
  rw [ha]
  simp only [map_sum, map_smul, star_sum, star_smul]
  apply Finset.sum_congr rfl
  intro i hi
  have hxi : IsSelfAdjoint (x i) := IsSelfAdjoint.of_nonneg (hx i)
  have hφxi : IsSelfAdjoint (φ (x i)) :=
    IsSelfAdjoint.of_nonneg ((PositiveLinearMap.ofClass φ).map_nonneg (hx i))
  rw [hφxi.star_eq, hxi.star_eq]

/-- Sums of completely positive maps with the same source and target are completely positive. -/
noncomputable def completelyPositiveMap_add
    (φ ψ : CompletelyPositiveMap A B) : CompletelyPositiveMap A B := by
  refine { toLinearMap := φ.toLinearMap + ψ.toLinearMap, map_cstarMatrix_nonneg' := ?_ }
  intro k M hM
  have hφ := φ.map_cstarMatrix_nonneg' k M hM
  have hψ := ψ.map_cstarMatrix_nonneg' k M hM
  have hsum : 0 ≤ M.map φ.toLinearMap + M.map ψ.toLinearMap := add_nonneg hφ hψ
  convert hsum using 1
  ext i j
  rfl

@[simp]
lemma completelyPositiveMap_add_apply (φ ψ : CompletelyPositiveMap A B) (a : A) :
    completelyPositiveMap_add φ ψ a = φ a + ψ a :=
  rfl

@[simp]
lemma completelyPositiveMap_add_toLinearMap (φ ψ : CompletelyPositiveMap A B) :
    (completelyPositiveMap_add φ ψ).toLinearMap = φ.toLinearMap + ψ.toLinearMap :=
  rfl

/-! ### Completely positive semigroups -/

/-- A norm-continuous semigroup of completely positive maps.

Unlike a `Channel` semigroup, this structure does not require unitality.  It is therefore the
right intermediate object for the no-jump evolution in a Lindblad/Dyson expansion. -/
structure CompletelyPositiveSemigroup (A : Type*) [OperatorAlgebra A] where
  /-- The completely positive map at each nonnegative time. -/
  map : ℝ≥0 → A →CP A
  /-- The map at time zero is the identity. -/
  map_zero : map 0 = completelyPositiveMap_id A
  /-- The semigroup composition law. -/
  map_add : ∀ s t,
    map (s + t) = completelyPositiveMap_comp (map s) (map t)
  /-- Continuity in the operator norm. -/
  continuous : Continuous (fun t =>
    completelyPositiveMap_toContinuousLinearMap (map t))

namespace CompletelyPositiveSemigroup

variable {A : Type*} [OperatorAlgebra A]

@[simp]
lemma map_zero_apply (Φ : CompletelyPositiveSemigroup A) (a : A) :
    Φ.map 0 a = a := by
  rw [Φ.map_zero]
  rfl

lemma map_add_apply (Φ : CompletelyPositiveSemigroup A) (s t : ℝ≥0) (a : A) :
    Φ.map (s + t) a = Φ.map s (Φ.map t a) := by
  rw [Φ.map_add, completelyPositiveMap_comp_apply]

end CompletelyPositiveSemigroup

/-- The zero map is completely positive. -/
noncomputable def completelyPositiveMap_zero : CompletelyPositiveMap A B := by
  refine { toLinearMap := 0, map_cstarMatrix_nonneg' := ?_ }
  intro k M hM
  change 0 ≤ (0 : CStarMatrix (Fin k) (Fin k) B)
  exact le_rfl

@[simp]
lemma completelyPositiveMap_zero_apply (a : A) :
    completelyPositiveMap_zero (A := A) (B := B) a = 0 :=
  rfl

@[simp]
lemma completelyPositiveMap_zero_toLinearMap :
    (completelyPositiveMap_zero (A := A) (B := B)).toLinearMap = 0 :=
  rfl

instance completelyPositiveMap_add_commutative :
    Std.Commutative (completelyPositiveMap_add (A := A) (B := B)) where
  comm φ ψ := by
    apply DFunLike.coe_injective
    funext a
    simp [add_comm]

instance completelyPositiveMap_add_associative :
    Std.Associative (completelyPositiveMap_add (A := A) (B := B)) where
  assoc φ ψ χ := by
    apply DFunLike.coe_injective
    funext a
    simp [add_assoc]

/- A finite sum of completely positive maps is completely positive. -/
noncomputable def completelyPositiveMap_finsetSum {ι : Type*} (s : Finset ι)
    (φ : ι → CompletelyPositiveMap A B) : CompletelyPositiveMap A B :=
  Finset.fold (completelyPositiveMap_add (A := A) (B := B))
    completelyPositiveMap_zero φ s

lemma completelyPositiveMap_finsetSum_toLinearMap {ι : Type*} (s : Finset ι)
    (φ : ι → CompletelyPositiveMap A B) :
    (completelyPositiveMap_finsetSum s φ).toLinearMap =
      ∑ i ∈ s, (φ i).toLinearMap := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [completelyPositiveMap_finsetSum]
  | @insert i s hi ih =>
      rw [completelyPositiveMap_finsetSum, Finset.fold_insert hi,
        completelyPositiveMap_add_toLinearMap]
      have ih' :
          (Finset.fold (completelyPositiveMap_add (A := A) (B := B))
            completelyPositiveMap_zero φ s).toLinearMap =
            ∑ i ∈ s, (φ i).toLinearMap := by
        exact ih
      rw [ih', Finset.sum_insert hi]

lemma completelyPositiveMap_finsetSum_apply {ι : Type*} (s : Finset ι)
    (φ : ι → CompletelyPositiveMap A B) (a : A) :
    completelyPositiveMap_finsetSum s φ a = ∑ i ∈ s, φ i a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [completelyPositiveMap_finsetSum]
  | @insert i s hi ih =>
      rw [completelyPositiveMap_finsetSum, Finset.fold_insert hi]
      simp only [completelyPositiveMap_add_apply, Finset.sum_insert hi]
      have ih' :
          (Finset.fold (completelyPositiveMap_add (A := A) (B := B))
            completelyPositiveMap_zero φ s) a =
            ∑ i ∈ s, φ i a := by
        exact ih
      rw [ih']

/-- Multiplication of a completely positive map by a nonnegative real scalar. -/
noncomputable def completelyPositiveMap_real_smul
    (r : ℝ) (hr : 0 ≤ r) (φ : CompletelyPositiveMap A B) :
    CompletelyPositiveMap A B := by
  refine { toLinearMap := (r : ℂ) • φ.toLinearMap, map_cstarMatrix_nonneg' := ?_ }
  intro k M hM
  have hφ := φ.map_cstarMatrix_nonneg' k M hM
  have h := smul_nonneg hr hφ
  convert h using 1
  ext i j
  simp

@[simp]
lemma completelyPositiveMap_real_smul_apply
    (r : ℝ) (hr : 0 ≤ r) (φ : CompletelyPositiveMap A B) (a : A) :
    completelyPositiveMap_real_smul r hr φ a = (r : ℂ) • φ a :=
  rfl

@[simp]
lemma completelyPositiveMap_real_smul_toLinearMap
    (r : ℝ) (hr : 0 ≤ r) (φ : CompletelyPositiveMap A B) :
    (completelyPositiveMap_real_smul r hr φ).toLinearMap = (r : ℂ) • φ.toLinearMap :=
  rfl

/-! ### Positive exponential approximants -/

noncomputable def cpPow (φ : CompletelyPositiveMap A A) : ℕ → CompletelyPositiveMap A A
  | 0 => completelyPositiveMap_id A
  | n + 1 => completelyPositiveMap_comp φ (cpPow φ n)

lemma cpPow_toLinearMap (φ : CompletelyPositiveMap A A) (n : ℕ) :
    (cpPow φ n).toLinearMap = φ.toLinearMap ^ n := by
  induction n with
  | zero =>
    ext a
    simp [cpPow, completelyPositiveMap_id]
  | succ n ih =>
    change φ.toLinearMap.comp (cpPow φ n).toLinearMap = _
    rw [ih, pow_succ']
    rfl

lemma cpPow_apply (φ : CompletelyPositiveMap A A) (n : ℕ) (a : A) :
    cpPow φ n a = (φ.toLinearMap ^ n) a := by
  change (cpPow φ n).toLinearMap a = _
  rw [cpPow_toLinearMap]

lemma cpPow_id (n : ℕ) :
    cpPow (completelyPositiveMap_id A) n = completelyPositiveMap_id A := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cpPow, ih]
    apply DFunLike.coe_injective
    funext a
    simp [completelyPositiveMap_comp_apply]

/-- The first `n + 1` terms of the exponential of a CP map at a nonnegative time.

Every approximant is CP term-by-term.  The nonnegativity restriction is essential: a negative
scalar multiple of a CP map need not be CP. -/
noncomputable def cpExpPartial (φ : CompletelyPositiveMap A A) (t : ℝ) (n : ℕ)
    (ht : 0 ≤ t) : CompletelyPositiveMap A A :=
  match n with
  | 0 => completelyPositiveMap_id A
  | n + 1 =>
    completelyPositiveMap_add (cpExpPartial φ t n ht)
      (completelyPositiveMap_real_smul ((Nat.factorial (n + 1) : ℝ)⁻¹) (by positivity)
        (cpPow (completelyPositiveMap_real_smul t ht φ) (n + 1)))

lemma cpExpPartial_toLinearMap (φ : CompletelyPositiveMap A A) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) :
    (cpExpPartial φ t n ht).toLinearMap =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.factorial k : ℝ)⁻¹ •
          (t • completelyPositiveMap_toContinuousLinearMap φ) ^ k := by
  induction n with
  | zero =>
    ext a
    simp [cpExpPartial, completelyPositiveMap_id]
  | succ n ih =>
    rw [cpExpPartial]
    rw [completelyPositiveMap_add_toLinearMap,
      completelyPositiveMap_real_smul_toLinearMap]
    rw [ih, Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    congr 1
    · simp only [Finset.sum_range_succ]
    · rw [cpPow_toLinearMap]
      ext a
      simp [show (t • completelyPositiveMap_toContinuousLinearMap φ).toLinearMap =
        (t : ℂ) • φ.toLinearMap by rfl, pow_succ]
      congr 2
      norm_num

noncomputable def cpExpPartialCLM (φ : CompletelyPositiveMap A A) (t : ℝ)
    (n : ℕ) (ht : 0 ≤ t) : A →L[ℂ] A :=
  completelyPositiveMap_toContinuousLinearMap (cpExpPartial φ t n ht)

lemma cpExpPartialCLM_eq_sum (φ : CompletelyPositiveMap A A) (t : ℝ)
    (ht : 0 ≤ t) (n : ℕ) :
    cpExpPartialCLM φ t n ht =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.factorial k : ℝ)⁻¹ •
          (t • completelyPositiveMap_toContinuousLinearMap φ) ^ k := by
  ext a
  change (cpExpPartial φ t n ht).toLinearMap a = _
  rw [show (cpExpPartial φ t n ht).toLinearMap =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.factorial k : ℝ)⁻¹ •
          (t • completelyPositiveMap_toContinuousLinearMap φ) ^ k by
    exact cpExpPartial_toLinearMap φ t ht n]
  rfl

/-- A pointwise operator-norm limit of completely positive bounded maps is completely positive.

The hypothesis is written at the matrix-amplification level so it can be fed directly by finite
product-formula approximants without first constructing bundled CP maps for every approximant. -/
noncomputable def completelyPositiveMap_of_tendsto
    (φn : ℕ → A →L[ℂ] B)
    (hCP : ∀ n k (M : CStarMatrix (Fin k) (Fin k) A),
      0 ≤ M → 0 ≤ M.map (φn n).toLinearMap)
    (φ : A →L[ℂ] B)
    (hlim : Tendsto φn atTop (nhds φ)) :
    CompletelyPositiveMap A B := by
  refine { toLinearMap := φ.toLinearMap, map_cstarMatrix_nonneg' := ?_ }
  intro k M hM
  refine CStarAlgebra.isClosed_nonneg.mem_of_tendsto
    (f := fun n => M.map (φn n).toLinearMap) (b := (atTop : Filter ℕ))
    (x := M.map φ.toLinearMap) ?_ ?_
  · apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    change Tendsto (fun n => (φn n) (M i j)) atTop (nhds (φ (M i j)))
    exact ((ContinuousLinearMap.apply ℂ B (M i j)).continuous.continuousAt.tendsto).comp hlim
  · filter_upwards [] with n
    exact hCP n k M hM

/-- The bundled form of `completelyPositiveMap_of_tendsto`.

This is the form used by product formulas: the approximants already carry complete positivity,
while convergence is checked only for their bounded linear realizations. -/
noncomputable def completelyPositiveMap_of_tendsto_bundled
    (φn : ℕ → (A →CP B)) (φ : A →L[ℂ] B)
    (hlim : Tendsto
      (fun n => completelyPositiveMap_toContinuousLinearMap (φn n))
      atTop (nhds φ)) :
    CompletelyPositiveMap A B := by
  apply completelyPositiveMap_of_tendsto
    (fun n => completelyPositiveMap_toContinuousLinearMap (φn n))
    (hCP := by
      intro n k M hM
      change 0 ≤ M.map (φn n).toLinearMap
      exact (φn n).map_cstarMatrix_nonneg' k M hM)
    (φ := φ) hlim

/-! ### Semigroups obtained by CP limits -/

/-- The bounded map underlying a CP limit is exactly the map used to build it. -/
lemma completelyPositiveMap_of_tendsto_toContinuousLinearMap
    (φn : ℕ → (A →CP B)) (φ : A →L[ℂ] B)
    (hlim : Tendsto
      (fun n => completelyPositiveMap_toContinuousLinearMap (φn n))
      atTop (nhds φ)) :
    completelyPositiveMap_toContinuousLinearMap
      (completelyPositiveMap_of_tendsto_bundled φn φ hlim) = φ := by
  ext a
  rfl

/-- Construct a norm-continuous CP semigroup from norm-convergent CP approximants.

The approximants need not themselves satisfy the semigroup law.  It is enough that their bounded
limits do; this is the form used by product formulas, where finite-step maps are CP and the
semigroup law appears only after taking the limit. -/
noncomputable def CompletelyPositiveSemigroup.of_tendsto
    (approx : ℝ≥0 → ℕ → (A →CP A))
    (limit : ℝ≥0 → A →L[ℂ] A)
    (hlim : ∀ t,
      Tendsto
        (fun n => completelyPositiveMap_toContinuousLinearMap (approx t n))
        atTop (nhds (limit t)))
    (hzero : limit 0 = (1 : A →L[ℂ] A))
    (hadd : ∀ s t, limit (s + t) = limit s * limit t)
    (hcont : Continuous limit) : CompletelyPositiveSemigroup A where
  map := fun t => completelyPositiveMap_of_tendsto_bundled
    (fun n => approx t n) (limit t) (hlim t)
  map_zero := by
    apply DFunLike.coe_injective
    funext a
    change limit 0 a = a
    rw [hzero]
    rfl
  map_add := by
    intro s t
    apply DFunLike.coe_injective
    funext a
    change limit (s + t) a = limit s (limit t a)
    rw [hadd]
    rfl
  continuous := by
    change Continuous limit
    exact hcont

/-! ### Positive exponential limits -/

/-- The exponential of a completely positive map is completely positive at nonnegative time.

This is a closure theorem for the positive exponential series.  It is deliberately separate from
the GKSL theorem: a GKSL generator is generally not itself CP, so its exponential requires the
Euler/product-formula argument supplied by the dynamics layer. -/
noncomputable def completelyPositiveMap_exp_of_nonneg
    (φ : CompletelyPositiveMap A A) (t : ℝ) (ht : 0 ≤ t) :
    CompletelyPositiveMap A A := by
  let J : A →L[ℂ] A := completelyPositiveMap_toContinuousLinearMap φ
  let φn : ℕ → A →L[ℂ] A := fun n => cpExpPartialCLM φ t n ht
  have hlim : Tendsto φn atTop (nhds (NormedSpace.exp (t • J))) := by
    have hseries :=
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • J)).tendsto_sum_nat
    have hshift := hseries.comp (tendsto_add_atTop_nat 1)
    simpa [φn, cpExpPartialCLM_eq_sum, J, Function.comp_def] using hshift
  refine completelyPositiveMap_of_tendsto φn ?_ (NormedSpace.exp (t • J)) hlim
  intro n k M hM
  exact (cpExpPartial φ t n ht).map_cstarMatrix_nonneg' k M hM

end OperatorAlgebra
