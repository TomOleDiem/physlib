/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Dynamics.Semigroup
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Dynamics.CPClosure
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Dynamics.Trotter
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Dynamics.ChristensenEvans
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Dynamics.Stinespring
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.HilbertSpace
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Bounded Lindblad generators

For bounded operators, the GKSL/Lindblad expression is a bounded linear operator on the Banach
space `B(H)`.  We define that expression for finitely many noise operators and prove the purely
analytic fact that its exponential satisfies the semigroup law.

The separate channel-realization structure below exposes the finite-noise construction.  The
general bounded `B(H)` theorem, with an arbitrary completely positive jump map and its canonical
Christensen--Evans realization, is exported by `Dynamics.Stinespring`; the finite-noise API here
also connects to that abstract form.
-/

@[expose] public section

namespace OperatorAlgebra

open Filter
open scoped ComplexOrder CStarAlgebra NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

/-- The exponential on superoperators uses the rational restriction of the complex algebra
structure, exactly as for exponentials of bounded operators themselves. -/
noncomputable local instance : NormedAlgebra ℚ (B(H) →L[ℂ] B(H)) :=
  .restrictScalars ℚ ℂ (B(H) →L[ℂ] B(H))

noncomputable local instance : NormedAlgebra ℝ (B(H) →L[ℂ] B(H)) :=
  .restrictScalars ℝ ℂ (B(H) →L[ℂ] B(H))

noncomputable local instance : NormedAlgebra ℚ (B(H)) :=
  .restrictScalars ℚ ℂ (B(H))

/-! ### Completely positive conjugations -/

/-- The diagonal amplification of a bounded operator. -/
noncomputable def operatorDiagonal {n : Type*} [Fintype n] [DecidableEq n] (W : B(H)) :
    CStarMatrix n n (B(H)) :=
  Matrix.diagonal (fun _ => W)

/-- Conjugation by a bounded operator is completely positive.

This is the CP map underlying both the Hamiltonian no-jump evolution and every Lindblad jump
term.  The proof is representation-free at the level of `B(H)`: at matrix level it is the
positive conjugation `M ↦ C⋆ M C` by the diagonal matrix `C` with entries `W`. -/
noncomputable def conjugationCPMap (W : B(H)) : B(H) →CP B(H) := by
  refine CompletelyPositiveMap.mk
    (ContinuousLinearMap.mulLeftRight ℂ (B(H)) (star W) W).toLinearMap ?_
  intro k M hM
  let C : CStarMatrix (Fin k) (Fin k) (B(H)) := operatorDiagonal W
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
lemma conjugationCPMap_apply (W A : B(H)) :
    conjugationCPMap W A = star W * A * W := by
  rfl

@[simp]
lemma conjugationCPMap_one (W : B(H)) :
    conjugationCPMap W 1 = star W * W := by
  simp [conjugationCPMap_apply]

lemma conjugationCPMap_toContinuousLinearMap (W : B(H)) :
    completelyPositiveMap_toContinuousLinearMap (conjugationCPMap W) =
      ContinuousLinearMap.mulLeftRight ℂ (B(H)) (star W) W := by
  ext A
  simp [conjugationCPMap_apply, ContinuousLinearMap.mulLeftRight_apply]

/-- Bounded Hamiltonian and finitely many bounded noise operators. -/
structure LindbladData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ι : Type*) [Fintype ι] where
  /-- The self-adjoint Hamiltonian part. -/
  hamiltonian : Observable (B(H))
  /-- The bounded noise/Lindblad operators. -/
  noise : ι → B(H)

namespace LindbladData

/-! ### The no-jump/jump decomposition -/

/-- The bounded effective operator containing the Hamiltonian and damping terms. -/
noncomputable def noJumpOperator (D : LindbladData H ι) : B(H) :=
  -Complex.I • (D.hamiltonian : B(H)) -
    (2 : ℂ)⁻¹ • ∑ i, star (D.noise i) * D.noise i

/-- The CP jump part of a bounded Lindblad generator. -/
noncomputable def jumpMap (D : LindbladData H ι) : B(H) →L[ℂ] B(H) :=
  ∑ i, completelyPositiveMap_toContinuousLinearMap (conjugationCPMap (D.noise i))

/- The same jump part, retained as a bundled completely positive map. -/
noncomputable def jumpCPMap (D : LindbladData H ι) : B(H) →CP B(H) :=
  completelyPositiveMap_finsetSum Finset.univ
    (fun i => conjugationCPMap (D.noise i))

lemma jumpCPMap_eq_finiteKrausCPMap (D : LindbladData H ι) :
    D.jumpCPMap = StinespringWitness.finiteKrausCPMap D.noise := by
  apply DFunLike.coe_injective
  funext A
  simp [LindbladData.jumpCPMap, StinespringWitness.finiteKrausCPMap,
    completelyPositiveMap_finsetSum_apply, conjugationCPMap_apply,
    completelyPositiveMap_conjugation_apply]

/-- The finite-noise jump map has a Stinespring witness on the finite Hilbert sum. -/
noncomputable def jumpStinespringWitness (D : LindbladData H ι) :
    StinespringWitness (B(H)) H (PiLp 2 (fun _ : ι => H)) D.jumpCPMap := by
  rw [D.jumpCPMap_eq_finiteKrausCPMap]
  exact StinespringWitness.finiteKraus D.noise

/-- The no-jump part of a bounded Lindblad generator. -/
noncomputable def noJumpMap (D : LindbladData H ι) : B(H) →L[ℂ] B(H) :=
  ContinuousLinearMap.mulLeftRight ℂ (B(H)) (star D.noJumpOperator) 1 +
    ContinuousLinearMap.mulLeftRight ℂ (B(H)) 1 D.noJumpOperator

@[simp]
lemma jumpMap_apply (D : LindbladData H ι) (A : B(H)) :
    D.jumpMap A = ∑ i, star (D.noise i) * A * D.noise i := by
  simp [jumpMap, conjugationCPMap_apply, ContinuousLinearMap.sum_apply]

@[simp]
lemma jumpCPMap_apply (D : LindbladData H ι) (A : B(H)) :
    D.jumpCPMap A = ∑ i, star (D.noise i) * A * D.noise i := by
  change completelyPositiveMap_finsetSum Finset.univ
    (fun i => conjugationCPMap (D.noise i)) A = _
  rw [completelyPositiveMap_finsetSum_apply]
  simp [conjugationCPMap_apply]

lemma jumpCPMap_toContinuousLinearMap (D : LindbladData H ι) :
    completelyPositiveMap_toContinuousLinearMap D.jumpCPMap = D.jumpMap := by
  ext A
  rw [completelyPositiveMap_toContinuousLinearMap_apply, jumpCPMap_apply, jumpMap_apply]

@[simp]
lemma noJumpMap_apply (D : LindbladData H ι) (A : B(H)) :
    D.noJumpMap A = star D.noJumpOperator * A + A * D.noJumpOperator := by
  simp [noJumpMap, ContinuousLinearMap.mulLeftRight_apply]

/-- The commutator superoperator generated by a bounded Hamiltonian. -/
noncomputable def hamiltonianPart (D : LindbladData H ι) : B(H) →L[ℂ] B(H) :=
  Complex.I •
    (ContinuousLinearMap.mulLeftRight ℂ B(H) (D.hamiltonian : B(H)) 1 -
      ContinuousLinearMap.mulLeftRight ℂ B(H) 1 (D.hamiltonian : B(H)))

/-- The dissipative contribution of one bounded noise operator. -/
noncomputable def dissipativePart (D : LindbladData H ι) (i : ι) : B(H) →L[ℂ] B(H) :=
  let V := D.noise i
  let Q := star V * V
  ContinuousLinearMap.mulLeftRight ℂ B(H) (star V) V -
    (2 : ℂ)⁻¹ •
      (ContinuousLinearMap.mulLeftRight ℂ B(H) Q 1 +
        ContinuousLinearMap.mulLeftRight ℂ B(H) 1 Q)

/-- The bounded GKSL/Lindblad generator in the Heisenberg picture:

`L(A) = i[H,A] + ∑ᵢ (Vᵢ⋆ A Vᵢ - ½(Vᵢ⋆Vᵢ A + A Vᵢ⋆Vᵢ))`.
-/
noncomputable def generator (D : LindbladData H ι) : B(H) →L[ℂ] B(H) :=
  D.hamiltonianPart + ∑ i, D.dissipativePart i

@[simp]
lemma hamiltonianPart_apply (D : LindbladData H ι) (A : B(H)) :
    D.hamiltonianPart A =
      Complex.I • ((D.hamiltonian : B(H)) * A - A * (D.hamiltonian : B(H))) := by
  simp [hamiltonianPart, ContinuousLinearMap.mulLeftRight_apply, sub_eq_add_neg]

@[simp]
lemma dissipativePart_apply (D : LindbladData H ι) (i : ι) (A : B(H)) :
    D.dissipativePart i A =
      star (D.noise i) * A * D.noise i -
        (2 : ℂ)⁻¹ •
          (star (D.noise i) * D.noise i * A +
            A * star (D.noise i) * D.noise i) := by
  simp [dissipativePart, ContinuousLinearMap.mulLeftRight_apply, sub_eq_add_neg, smul_add]
  · exact (mul_assoc A (star (D.noise i)) (D.noise i)).symm

@[simp]
lemma generator_apply (D : LindbladData H ι) (A : B(H)) :
    D.generator A =
      Complex.I • ((D.hamiltonian : B(H)) * A - A * (D.hamiltonian : B(H))) +
        ∑ i, (star (D.noise i) * A * D.noise i -
          (2 : ℂ)⁻¹ •
            (star (D.noise i) * D.noise i * A +
          A * star (D.noise i) * D.noise i)) := by
  simp [generator]

lemma generator_eq_noJumpMap_add_jumpMap (D : LindbladData H ι) :
    D.generator = D.noJumpMap + D.jumpMap := by
  apply ContinuousLinearMap.ext
  intro A
  change D.generator A = D.noJumpMap A + D.jumpMap A
  rw [generator_apply, noJumpMap_apply, jumpMap_apply]
  have hleft :
      (∑ i, (2 : ℂ)⁻¹ •
        (star (D.noise i) * D.noise i * A)) =
        (∑ i, (2 : ℂ)⁻¹ • (star (D.noise i) * D.noise i)) * A := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    simp [smul_eq_mul, mul_assoc]
  have hright :
      (∑ i, (2 : ℂ)⁻¹ •
        (A * star (D.noise i) * D.noise i)) =
        A * (∑ i, (2 : ℂ)⁻¹ • (star (D.noise i) * D.noise i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [smul_eq_mul, mul_assoc, mul_comm]
  simp [noJumpOperator, star_sub, star_smul, star_mul, star_star, star_sum,
    smul_add, smul_sub, sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg,
    Finset.sum_mul, Finset.mul_sum,
    Finset.sum_add_distrib, Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
    hleft, hright]
  noncomm_ring

/-- The CP no-jump evolution generated by the effective operator. -/
noncomputable def noJumpEvolution (D : LindbladData H ι) (t : ℝ) :
    B(H) →CP B(H) :=
  conjugationCPMap (NormedSpace.exp (t • D.noJumpOperator))

@[simp]
lemma noJumpEvolution_apply (D : LindbladData H ι) (t : ℝ) (A : B(H)) :
    D.noJumpEvolution t A =
      star (NormedSpace.exp (t • D.noJumpOperator)) * A *
        NormedSpace.exp (t • D.noJumpOperator) := by
  rfl

@[simp]
lemma noJumpEvolution_zero (D : LindbladData H ι) :
    D.noJumpEvolution 0 = completelyPositiveMap_id (B(H)) := by
  apply DFunLike.coe_injective
  funext A
  simp [noJumpEvolution]

lemma noJumpEvolution_add (D : LindbladData H ι) (s t : ℝ) :
    D.noJumpEvolution (s + t) =
      completelyPositiveMap_comp (D.noJumpEvolution s) (D.noJumpEvolution t) := by
  apply DFunLike.coe_injective
  funext A
  rw [completelyPositiveMap_comp_apply, noJumpEvolution_apply,
    noJumpEvolution_apply, noJumpEvolution_apply]
  let X := NormedSpace.exp (s • D.noJumpOperator)
  let Y := NormedSpace.exp (t • D.noJumpOperator)
  have hcommST : Commute (s • D.noJumpOperator) (t • D.noJumpOperator) := by
    rw [commute_iff_eq]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm s t]
  have hcomm : Commute X Y := by
    dsimp [X, Y]
    exact hcommST.exp_left.exp_right
  have hexp : NormedSpace.exp ((s + t) • D.noJumpOperator) = X * Y := by
    rw [add_smul]
    exact NormedSpace.exp_add_of_commute hcommST
  rw [hexp]
  change star (X * Y) * A * (X * Y) = star X * (star Y * A * Y) * X
  rw [star_mul]
  have hright : Y * X = X * Y := hcomm.symm.eq
  have hstar : star Y * star X = star X * star Y := by
    have h := congrArg star hright
    simpa only [star_mul] using h.symm
  rw [hstar]
  simp only [mul_assoc]
  rw [hright]

/-! ### The no-jump CP semigroup -/

/-- The no-jump evolution restricted to physical, nonnegative times. -/
noncomputable def noJumpEvolutionNNReal (D : LindbladData H ι) (t : ℝ≥0) :
    B(H) →CP B(H) :=
  D.noJumpEvolution (t : ℝ)

@[simp]
lemma noJumpEvolutionNNReal_zero (D : LindbladData H ι) :
    D.noJumpEvolutionNNReal 0 = completelyPositiveMap_id (B(H)) := by
  exact D.noJumpEvolution_zero

lemma noJumpEvolutionNNReal_add (D : LindbladData H ι) (s t : ℝ≥0) :
    D.noJumpEvolutionNNReal (s + t) =
      completelyPositiveMap_comp (D.noJumpEvolutionNNReal s)
        (D.noJumpEvolutionNNReal t) := by
  simpa only [noJumpEvolutionNNReal, NNReal.coe_add] using
    D.noJumpEvolution_add (s : ℝ) (t : ℝ)

lemma noJumpEvolutionNNReal_continuous (D : LindbladData H ι) :
    Continuous (fun t : ℝ≥0 =>
      completelyPositiveMap_toContinuousLinearMap (D.noJumpEvolutionNNReal t)) := by
  have hfun :
      (fun t : ℝ≥0 =>
        completelyPositiveMap_toContinuousLinearMap (D.noJumpEvolutionNNReal t)) =
        (fun t : ℝ≥0 =>
          ContinuousLinearMap.mulLeftRight ℂ (B(H))
            (star (NormedSpace.exp ((t : ℝ) • D.noJumpOperator)))
            (NormedSpace.exp ((t : ℝ) • D.noJumpOperator))) := by
    funext t
    simp only [noJumpEvolutionNNReal, noJumpEvolution,
      conjugationCPMap_toContinuousLinearMap]
  rw [hfun]
  fun_prop

/-- The no-jump part is a norm-continuous completely positive semigroup. -/
noncomputable def noJumpSemigroup (D : LindbladData H ι) :
    CompletelyPositiveSemigroup (B(H)) where
  map := D.noJumpEvolutionNNReal
  map_zero := D.noJumpEvolutionNNReal_zero
  map_add := D.noJumpEvolutionNNReal_add
  continuous := D.noJumpEvolutionNNReal_continuous

/-! ### Euler/Trotter approximants -/

/-- The positive Euler step for the jump part.

`id + t J` is completely positive for `t ≥ 0`; it is not asserted to be unital because the jump
part alone need not preserve the identity. -/
noncomputable def jumpEulerStep (D : LindbladData H ι) (t : ℝ≥0) :
    B(H) →CP B(H) :=
  completelyPositiveMap_add (completelyPositiveMap_id (B(H)))
    (completelyPositiveMap_real_smul (t : ℝ) (by positivity) D.jumpCPMap)

@[simp]
lemma jumpEulerStep_zero (D : LindbladData H ι) :
    D.jumpEulerStep 0 = completelyPositiveMap_id (B(H)) := by
  apply DFunLike.coe_injective
  funext A
  simp [jumpEulerStep]

@[simp]
lemma jumpEulerStep_apply (D : LindbladData H ι) (t : ℝ≥0) (A : B(H)) :
    D.jumpEulerStep t A = A + (t : ℂ) • D.jumpCPMap A := by
  simp [jumpEulerStep]

lemma jumpEulerStep_toContinuousLinearMap (D : LindbladData H ι) (t : ℝ≥0) :
    completelyPositiveMap_toContinuousLinearMap (D.jumpEulerStep t) =
      (1 : B(H) →L[ℂ] B(H)) + (t : ℂ) • D.jumpMap := by
  ext A
  simp [jumpEulerStep, D.jumpCPMap_toContinuousLinearMap]

/-- One completely positive Euler/Trotter step for a bounded Lindblad generator.

The order is the usual product-formula order: first apply the jump Euler step, then the no-jump
evolution.  Both factors are CP, so this statement is available before the product-formula limit
has been proved. -/
noncomputable def eulerStep (D : LindbladData H ι) (t : ℝ≥0) (n : ℕ) :
    B(H) →CP B(H) :=
  completelyPositiveMap_comp
    (D.noJumpEvolutionNNReal (t / (n + 1)))
    (D.jumpEulerStep (t / (n + 1)))

@[simp]
lemma eulerStep_zero (D : LindbladData H ι) (n : ℕ) :
    D.eulerStep 0 n = completelyPositiveMap_id (B(H)) := by
  apply DFunLike.coe_injective
  funext A
  simp [eulerStep]

lemma eulerStep_apply (D : LindbladData H ι) (t : ℝ≥0) (n : ℕ) (A : B(H)) :
    D.eulerStep t n A =
      D.noJumpEvolutionNNReal (t / (n + 1))
        (D.jumpEulerStep (t / (n + 1)) A) := by
  rfl

lemma eulerStep_toContinuousLinearMap (D : LindbladData H ι) (t : ℝ≥0) (n : ℕ) :
    completelyPositiveMap_toContinuousLinearMap (D.eulerStep t n) =
    completelyPositiveMap_toContinuousLinearMap
        (D.noJumpEvolutionNNReal (t / (n + 1))) *
        ((1 : B(H) →L[ℂ] B(H)) +
          ((t / (n + 1) : ℝ≥0) : ℂ) • D.jumpMap) := by
  apply ContinuousLinearMap.ext
  intro A
  simp [eulerStep, jumpEulerStep, ContinuousLinearMap.mul_apply,
    D.jumpCPMap_toContinuousLinearMap]

/-- The `n`th CP product-formula approximant.

The exponent is `n + 1` so that the step size is always defined, including the zeroth
approximant. -/
noncomputable def eulerApproximation (D : LindbladData H ι) (t : ℝ≥0) (n : ℕ) :
    B(H) →CP B(H) :=
  cpPow (D.eulerStep t n) (n + 1)

@[simp]
lemma eulerApproximation_zero (D : LindbladData H ι) (n : ℕ) :
    D.eulerApproximation 0 n = completelyPositiveMap_id (B(H)) := by
  rw [eulerApproximation, eulerStep_zero, cpPow_id]

lemma eulerApproximation_toContinuousLinearMap (D : LindbladData H ι) (t : ℝ≥0) (n : ℕ) :
    completelyPositiveMap_toContinuousLinearMap (D.eulerApproximation t n) =
      (completelyPositiveMap_toContinuousLinearMap (D.eulerStep t n)) ^ (n + 1) := by
  apply ContinuousLinearMap.ext
  intro A
  rw [completelyPositiveMap_toContinuousLinearMap_apply]
  change (cpPow (D.eulerStep t n) (n + 1)).toLinearMap A = _
  rw [cpPow_toLinearMap]
  let P := completelyPositiveMap_toContinuousLinearMap (D.eulerStep t n)
  have hP : P.toLinearMap = (D.eulerStep t n).toLinearMap := by
    apply LinearMap.ext
    intro B
    rfl
  have hpow := ContinuousLinearMap.toLinearMap_pow P (n + 1)
  have hpowA := congrArg (fun f : B(H) →ₗ[ℂ] B(H) => f A) hpow
  change ((D.eulerStep t n).toLinearMap ^ (n + 1)) A = (P ^ (n + 1)) A
  rw [← hP]
  exact hpowA.symm

/-! ### The norm-convergent Lindblad product formula -/

/-- The completely positive Euler products converge in operator norm to the bounded Lindblad
 exponential.  This is the bounded GKSL sufficiency step: complete positivity is inherited from
 the approximants by closedness of the CP cone, while the limit itself is the Lie product formula
 for the no-jump and jump parts. -/
lemma eulerApproximation_tendsto (D : LindbladData H ι) [Nontrivial H] (t : ℝ≥0) :
    Tendsto
      (fun n => completelyPositiveMap_toContinuousLinearMap (D.eulerApproximation t n))
      atTop (nhds (NormedSpace.exp ((t : ℝ) • D.generator))) := by
  let N : B(H) := D.noJumpOperator
  let J : B(H) →L[ℂ] B(H) := D.jumpMap
  let A : (B(H) →L[ℂ] B(H)) := D.noJumpMap
  let c : ℝ := 2 * ‖N‖ + ‖J‖
  let a : ℝ → (B(H) →L[ℂ] B(H)) := fun s =>
    ContinuousLinearMap.mulLeftRight ℂ (B(H))
      (star (NormedSpace.exp (s • N))) (NormedSpace.exp (s • N))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ha0 : a 0 = 1 := by
    ext X
    simp [a]
  have ha : HasDerivAt a A 0 := by
    have he : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • D.noJumpOperator))
        D.noJumpOperator 0 := by
      simpa using hasDerivAt_exp_smul_const D.noJumpOperator (0 : ℝ)
    have hstar : HasDerivAt (fun s : ℝ => star (NormedSpace.exp (s • D.noJumpOperator)))
        (star D.noJumpOperator) 0 := by
      simpa using he.star
    have hp := hstar.prodMk he
    let b : B(H) × B(H) → (B(H) →L[ℂ] B(H)) := fun p =>
      ContinuousLinearMap.mulLeftRight ℂ (B(H)) p.1 p.2
    have hb : IsBoundedBilinearMap ℝ b := by
      refine { add_left := ?_, smul_left := ?_, add_right := ?_, smul_right := ?_, bound := ?_ }
      · intro u v w; simp [b]
      · intro r u v
        simp [b, Algebra.smul_def]
        ext z
        simp [ContinuousLinearMap.mulLeftRight_apply, ← Algebra.smul_def]
      · intro u v w; simp [b]
      · intro r u v
        simp [b, Algebra.smul_def]
        ext z
        simp [ContinuousLinearMap.mulLeftRight_apply, ← Algebra.smul_def]
      · refine ⟨1, one_pos, ?_⟩
        intro u v
        simpa [b] using
          (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℂ (B(H)) u v)
    have hcomp := (hb.hasFDerivAt
      (star (NormedSpace.exp ((0 : ℝ) • D.noJumpOperator)),
        NormedSpace.exp ((0 : ℝ) • D.noJumpOperator))).comp 0 hp.hasFDerivAt
    have hd := hcomp.hasDerivAt
    have hfun : ((fun p => b p) ∘ fun s : ℝ =>
        (star (NormedSpace.exp (s • D.noJumpOperator)),
          NormedSpace.exp (s • D.noJumpOperator))) =
        (fun s : ℝ => b (star (NormedSpace.exp (s • D.noJumpOperator)),
          NormedSpace.exp (s • D.noJumpOperator))) := by
      rfl
    rw [hfun] at hd
    simpa [a, b, N, A, IsBoundedBilinearMap.deriv_apply,
      ContinuousLinearMap.mulLeftRight_apply, LindbladData.noJumpMap, add_comm] using hd
  have hqa : ∀ n : ℕ, ‖a ((t : ℝ) / (n + 1 : ℝ)) *
      (1 + (((t : ℝ) / (n + 1 : ℝ)) : ℝ) • J)‖ ≤
        Real.exp ((((t : ℝ) / (n + 1 : ℝ)) : ℝ) * c) := by
    intro n
    let h : ℝ := (t : ℝ) / (n + 1 : ℝ)
    have hh : 0 ≤ h := by dsimp [h]; positivity
    have hNnorm : ‖h • N‖ = h * ‖N‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    have he : ‖NormedSpace.exp (h • N)‖ ≤ Real.exp (h * ‖N‖) := by
      simpa [hNnorm] using norm_exp_le_exp_norm (h • N)
    have ha' : ‖a h‖ ≤ Real.exp (h * (2 * ‖N‖)) := by
      calc
        ‖a h‖ ≤ ‖star (NormedSpace.exp (h • N))‖ * ‖NormedSpace.exp (h • N)‖ := by
          simpa [a] using ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℂ (B(H))
            (star (NormedSpace.exp (h • N))) (NormedSpace.exp (h • N))
        _ = ‖NormedSpace.exp (h • N)‖ * ‖NormedSpace.exp (h • N)‖ := by rw [norm_star]
        _ ≤ Real.exp (h * ‖N‖) * Real.exp (h * ‖N‖) :=
          mul_le_mul he he (norm_nonneg _) (by positivity)
        _ = Real.exp (h * (2 * ‖N‖)) := by rw [← Real.exp_add]; congr 1 <;> ring
    have hlin : ‖(1 : B(H) →L[ℂ] B(H)) + h • J‖ ≤ 1 + h * ‖J‖ := by
      calc
        ‖(1 : B(H) →L[ℂ] B(H)) + h • J‖ ≤
            ‖(1 : B(H) →L[ℂ] B(H))‖ + ‖h • J‖ := norm_add_le _ _
        _ = 1 + h * ‖J‖ := by rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    have hlinexp : 1 + h * ‖J‖ ≤ Real.exp (h * ‖J‖) := by
      simpa [add_comm] using Real.add_one_le_exp (h * ‖J‖)
    calc
      ‖a h * (1 + h • J)‖ ≤ ‖a h‖ * ‖(1 : B(H) →L[ℂ] B(H)) + h • J‖ := norm_mul_le _ _
      _ ≤ Real.exp (h * (2 * ‖N‖)) * (1 + h * ‖J‖) :=
        mul_le_mul ha' hlin (norm_nonneg _) (by positivity)
      _ ≤ Real.exp (h * (2 * ‖N‖)) * Real.exp (h * ‖J‖) :=
        mul_le_mul_of_nonneg_left hlinexp (by positivity)
      _ = Real.exp (h * c) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [c]
        ring
  have hr : ∀ n : ℕ, ‖(1 : B(H) →L[ℂ] B(H)) +
      (((t : ℝ) / (n + 1 : ℝ)) : ℝ) • (A + J)‖ ≤
        Real.exp ((((t : ℝ) / (n + 1 : ℝ)) : ℝ) * c) := by
    intro n
    let h : ℝ := (t : ℝ) / (n + 1 : ℝ)
    have hh : 0 ≤ h := by dsimp [h]; positivity
    have hnorm : ‖A + J‖ ≤ c := by
      dsimp [A, N]
      have hleft : ‖ContinuousLinearMap.mulLeftRight ℂ (B(H))
          (star D.noJumpOperator) 1‖ ≤ ‖D.noJumpOperator‖ := by
        exact (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℂ (B(H))
          (star D.noJumpOperator) (1 : B(H))).trans_eq (by rw [norm_star, norm_one, mul_one])
      have hright : ‖ContinuousLinearMap.mulLeftRight ℂ (B(H))
          1 D.noJumpOperator‖ ≤ ‖D.noJumpOperator‖ := by
        exact (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℂ (B(H))
          (1 : B(H)) D.noJumpOperator).trans_eq (by rw [norm_one, one_mul])
      have hA : ‖D.noJumpMap‖ ≤ 2 * ‖D.noJumpOperator‖ := by
        rw [LindbladData.noJumpMap]
        calc
          ‖ContinuousLinearMap.mulLeftRight ℂ (B(H)) (star D.noJumpOperator) 1 +
              ContinuousLinearMap.mulLeftRight ℂ (B(H)) 1 D.noJumpOperator‖ ≤
              ‖ContinuousLinearMap.mulLeftRight ℂ (B(H)) (star D.noJumpOperator) 1‖ +
                ‖ContinuousLinearMap.mulLeftRight ℂ (B(H)) 1 D.noJumpOperator‖ :=
            norm_add_le _ _
          _ ≤ 2 * ‖D.noJumpOperator‖ := by
            calc
              _ ≤ ‖D.noJumpOperator‖ + ‖D.noJumpOperator‖ :=
                add_le_add hleft hright
              _ = 2 * ‖D.noJumpOperator‖ := by ring
      calc
        ‖A + J‖ ≤ ‖A‖ + ‖J‖ := norm_add_le _ _
        _ ≤ 2 * ‖D.noJumpOperator‖ + ‖J‖ :=
          add_le_add hA le_rfl
        _ = c := by rfl
    have hlin : ‖(1 : B(H) →L[ℂ] B(H)) + h • (A + J)‖ ≤ 1 + h * c := by
      calc
        ‖(1 : B(H) →L[ℂ] B(H)) + h • (A + J)‖ ≤
            ‖(1 : B(H) →L[ℂ] B(H))‖ + ‖h • (A + J)‖ := norm_add_le _ _
        _ ≤ 1 + h * c := by
          rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
          simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hnorm hh) 1
    calc
      ‖(1 : B(H) →L[ℂ] B(H)) + h • (A + J)‖ ≤ 1 + h * c := hlin
      _ ≤ Real.exp (h * c) := by simpa [add_comm] using Real.add_one_le_exp (h * c)
  have hprod := lie_product_formula_of_step a A J c (t : ℝ) (by positivity) hc ha0 ha hqa hr
  change Tendsto (fun n => completelyPositiveMap_toContinuousLinearMap (D.eulerApproximation t n))
      atTop (nhds (NormedSpace.exp ((t : ℝ) • D.generator)))
  rw [D.generator_eq_noJumpMap_add_jumpMap]
  convert hprod using 1
  · funext n
    rw [D.eulerApproximation_toContinuousLinearMap, D.eulerStep_toContinuousLinearMap]
    simp [a, J, N, LindbladData.noJumpEvolutionNNReal, LindbladData.noJumpEvolution,
      conjugationCPMap_toContinuousLinearMap]
    congr 2
    congr 1
    convert (RCLike.real_smul_eq_coe_smul (K := ℂ)
        ((↑t : ℝ) / (↑n + 1)) D.jumpMap).symm using 1 <;> norm_num

/-- If the Euler products converge in operator norm to a bounded map, that limit is completely
positive.  This is the exact closure step needed in the bounded GKSL sufficiency proof. -/
noncomputable def completelyPositiveMap_of_eulerLimit
    (D : LindbladData H ι) (t : ℝ≥0) (Φ : B(H) →L[ℂ] B(H))
    (hlim : Tendsto
      (fun n => completelyPositiveMap_toContinuousLinearMap (D.eulerApproximation t n))
      atTop (nhds Φ)) : CompletelyPositiveMap (B(H)) (B(H)) := by
  exact completelyPositiveMap_of_tendsto_bundled
    (fun n => D.eulerApproximation t n) Φ hlim

@[simp]
lemma generator_apply_one (D : LindbladData H ι) :
    D.generator 1 = 0 := by
  rw [generator_apply]
  simp only [mul_one, one_mul, sub_self, smul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← two_smul ℂ]
  simp [smul_smul]

lemma generator_star (D : LindbladData H ι) (A : B(H)) :
    star (D.generator A) = D.generator (star A) := by
  rw [generator_apply, generator_apply]
  simp only [star_add, star_smul, star_sub, star_mul, star_star, star_sum]
  rw [selfAdjoint.star_val_eq]
  simp [add_comm, mul_assoc]
  rw [← smul_neg]
  congr 1
  noncomm_ring

/-- Regard finite-noise Lindblad data as representation-independent Christensen–Evans data.

The bundled jump map retains the finite Kraus presentation, while the target type only sees the
completely positive map.  This is the compatibility bridge between the original `B(H)` API and
the general C⋆-algebra API. -/
noncomputable def toChristensenEvansData (D : LindbladData H ι) :
    ChristensenEvansData (B(H)) where
  hamiltonian := D.hamiltonian
  jump := D.jumpCPMap

lemma toChristensenEvansData_generator (D : LindbladData H ι) :
    D.toChristensenEvansData.generator = D.generator := by
  ext A
  rw [ChristensenEvansData.generator_apply, LindbladData.generator_apply]
  simp [toChristensenEvansData, jumpCPMap_apply, jumpMap_apply,
    ChristensenEvansData.jumpMap, LindbladData.hamiltonianPart,
    LindbladData.dissipativePart, ContinuousLinearMap.mulLeftRight_apply,
    sub_eq_add_neg, smul_add]
  simp only [Finset.sum_add_distrib]
  simp only [Finset.sum_neg_distrib, ← Finset.smul_sum]
  abel

/-- The finite-noise Lindblad presentation supplies the packaged Evans--Lewis factorisation
needed by the general bounded Christensen--Evans interface. -/
noncomputable def toEvansLewisKernelFactorization (D : LindbladData H ι) :
    StinespringWitness.EvansLewisKernelFactorization
      (K := PiLp 2 (fun _ : ι => H)) D.generator where
  jump := D.jumpCPMap
  witness := D.jumpStinespringWitness
  kernel_eq := by
    intro a b
    rw [← D.toChristensenEvansData_generator]
    change evansLewisKernel
        (D.jumpStinespringWitness.toChristensenEvansData D.hamiltonian).generator a b = _
    rw [StinespringWitness.evansLewisKernel_generator_eq_cpKernel
      D.jumpStinespringWitness D.hamiltonian]
    rw [StinespringWitness.evansLewisKernel_generator_eq_cpKernel
      D.jumpStinespringWitness (Subtype.mk 0 (by simp))]

lemma toEvansLewisKernelFactorization_isChristensenEvansGenerator
    [Nontrivial H]
    (D : LindbladData H ι) :
    IsChristensenEvansGenerator D.generator := by
  exact D.toEvansLewisKernelFactorization.isChristensenEvansGenerator
    D.generator_apply_one D.generator_star

lemma generator_isHermitianPreserving (D : LindbladData H ι) :
    ∀ ⦃A : B(H)⦄, IsSelfAdjoint A → IsSelfAdjoint (D.generator A) := by
  intro A hA
  rw [isSelfAdjoint_iff]
  rw [D.generator_star, hA.star_eq]

end LindbladData

section Exponential

/-- The linear evolution generated by a bounded Lindblad expression. -/
noncomputable def lindbladLinearEvolution (D : LindbladData H ι) (z : ℂ) :
    B(H) →L[ℂ] B(H) :=
  NormedSpace.exp (z • D.generator)

/-- The bounded Lindblad evolution with a real scalar parameter.  This version is useful for
stating the generator equation without introducing a one-sided derivative. -/
noncomputable def lindbladRealEvolution (D : LindbladData H ι) (t : ℝ) :
    B(H) →L[ℂ] B(H) :=
  NormedSpace.exp (t • D.generator)

lemma lindbladRealEvolution_hasDerivAt (D : LindbladData H ι) (t : ℝ) :
    HasDerivAt (fun s : ℝ => lindbladRealEvolution D s)
      (lindbladRealEvolution D t * D.generator) t := by
  simpa only [lindbladRealEvolution] using
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) (𝔸 := B(H) →L[ℂ] B(H)) D.generator t)

lemma lindbladRealEvolution_hasDerivAt_apply (D : LindbladData H ι) (t : ℝ) (A : B(H)) :
    HasDerivAt (fun s : ℝ => lindbladRealEvolution D s A)
      (lindbladRealEvolution D t (D.generator A)) t := by
  have h := lindbladRealEvolution_hasDerivAt D t
  let ev : (B(H) →L[ℂ] B(H)) →L[ℝ] B(H) :=
    (ContinuousLinearMap.apply ℂ B(H) A).restrictScalars ℝ
  have happly := ev.hasFDerivAt.comp t h.hasFDerivAt
  have hderiv :
      (ev ∘SL ContinuousLinearMap.toSpanSingleton ℝ
        (lindbladRealEvolution D t * D.generator)) 1 =
        lindbladRealEvolution D t (D.generator A) := by
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply_one]
    change (lindbladRealEvolution D t * D.generator) A =
      lindbladRealEvolution D t (D.generator A)
    rw [mul_apply_eq_comp]
  have hfun : (⇑ev ∘ fun s => lindbladRealEvolution D s) =
      (fun s => lindbladRealEvolution D s A) := by
    funext s
    rfl
  have happly' := happly.hasDerivAt
  rw [hfun, hderiv] at happly'
  exact happly'

@[simp]
lemma lindbladLinearEvolution_zero (D : LindbladData H ι) :
    lindbladLinearEvolution D 0 = (1 : B(H) →L[ℂ] B(H)) := by
  rw [lindbladLinearEvolution]
  rw [zero_smul ℂ D.generator, NormedSpace.exp_zero]

lemma lindbladLinearEvolution_add (D : LindbladData H ι) (s t : ℂ) :
    lindbladLinearEvolution D (s + t) =
      lindbladLinearEvolution D s * lindbladLinearEvolution D t := by
  rw [lindbladLinearEvolution, lindbladLinearEvolution, lindbladLinearEvolution]
  rw [add_smul s t D.generator]
  apply NormedSpace.exp_add_of_commute
  rw [commute_iff_eq]
  ext A
  simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.smul_comp, smul_smul, mul_comm]

/-- The same bounded evolution restricted to physical, nonnegative times. -/
noncomputable def lindbladNonnegativeEvolution (D : LindbladData H ι) (t : ℝ≥0) :
    B(H) →L[ℂ] B(H) :=
  lindbladLinearEvolution D (t : ℂ)

@[simp]
lemma lindbladLinearEvolution_apply_one (D : LindbladData H ι) (z : ℂ) :
    lindbladLinearEvolution D z 1 = 1 := by
  exact BoundedQuantumDynamicalSemigroup.exp_apply_of_apply_eq_zero
    D.generator 1 D.generator_apply_one z

@[simp]
lemma lindbladNonnegativeEvolution_apply_one (D : LindbladData H ι) (t : ℝ≥0) :
    lindbladNonnegativeEvolution D t 1 = 1 := by
  exact lindbladLinearEvolution_apply_one D (t : ℂ)

/-! ### Turning the product-formula limit into a channel -/

/-- A norm-convergent Euler product yields a channel for the Lindblad exponential.

The CP part comes from closedness of the CP cone; unitality is supplied by the exact exponential
identity above. -/
noncomputable def LindbladData.channel_of_eulerLimit
    (D : LindbladData H ι) (t : ℝ≥0)
    (hlim : Tendsto
      (fun n => completelyPositiveMap_toContinuousLinearMap (D.eulerApproximation t n))
      atTop (nhds (lindbladNonnegativeEvolution D t))) :
    Channel (B(H)) (B(H)) := by
  let Φ : B(H) →CP B(H) := D.completelyPositiveMap_of_eulerLimit t
    (lindbladNonnegativeEvolution D t) hlim
  refine ⟨Φ, ?_⟩
  change lindbladNonnegativeEvolution D t 1 = 1
  exact lindbladNonnegativeEvolution_apply_one D t

@[simp]
lemma lindbladNonnegativeEvolution_zero (D : LindbladData H ι) :
    lindbladNonnegativeEvolution D 0 = (1 : B(H) →L[ℂ] B(H)) := by
  change lindbladLinearEvolution D (0 : ℂ) = (1 : B(H) →L[ℂ] B(H))
  exact lindbladLinearEvolution_zero D

lemma lindbladNonnegativeEvolution_add (D : LindbladData H ι) (s t : ℝ≥0) :
    lindbladNonnegativeEvolution D (s + t) =
      lindbladNonnegativeEvolution D s * lindbladNonnegativeEvolution D t := by
  simpa only [lindbladNonnegativeEvolution, NNReal.coe_add, Complex.ofReal_add] using
    lindbladLinearEvolution_add D (s : ℂ) (t : ℂ)

lemma lindbladNonnegativeEvolution_add_apply (D : LindbladData H ι) (s t : ℝ≥0) (A : B(H)) :
    lindbladNonnegativeEvolution D (s + t) A =
      lindbladNonnegativeEvolution D s (lindbladNonnegativeEvolution D t A) := by
  rw [lindbladNonnegativeEvolution_add]
  rfl

lemma lindbladNonnegativeEvolution_continuous (D : LindbladData H ι) :
    Continuous (lindbladNonnegativeEvolution D) := by
  change Continuous (fun t : ℝ≥0 => NormedSpace.exp ((t : ℂ) • D.generator))
  apply NormedSpace.exp_continuous.comp
  fun_prop

/-- The full Lindblad exponential is a completely positive semigroup as soon as the Euler
product-formula limits have been established in operator norm. -/
noncomputable def LindbladData.completelyPositiveSemigroup_of_eulerLimit
    (D : LindbladData H ι)
    (hlim : ∀ t : ℝ≥0,
      Tendsto
        (fun n => completelyPositiveMap_toContinuousLinearMap (D.eulerApproximation t n))
        atTop (nhds (lindbladNonnegativeEvolution D t))) :
    CompletelyPositiveSemigroup (B(H)) :=
  CompletelyPositiveSemigroup.of_tendsto
    (approx := fun t n => D.eulerApproximation t n)
    (limit := lindbladNonnegativeEvolution D)
    hlim
    (lindbladNonnegativeEvolution_zero D)
    (lindbladNonnegativeEvolution_add D)
    (lindbladNonnegativeEvolution_continuous D)

lemma lindbladRealEvolution_star (D : LindbladData H ι) (t : ℝ) (A : B(H)) :
    star (lindbladRealEvolution D t A) =
      lindbladRealEvolution D t (star A) := by
  change star ((NormedSpace.exp (t • D.generator)) A) =
    (NormedSpace.exp (t • D.generator)) (star A)
  rw [NormedSpace.exp_eq_tsum ℝ]
  let ev : (B(H) →L[ℂ] B(H)) →L[ℂ] B(H) :=
    ContinuousLinearMap.apply ℂ B(H) A
  let evStar : (B(H) →L[ℂ] B(H)) →L[ℂ] B(H) :=
    ContinuousLinearMap.apply ℂ B(H) (star A)
  have hsum : Summable (fun n : ℕ =>
      (Nat.factorial n : ℝ)⁻¹ • (t • D.generator) ^ n) := by
    exact NormedSpace.expSeries_summable' (t • D.generator)
  have hsumStar : Summable (fun n : ℕ =>
      (Nat.factorial n : ℝ)⁻¹ • (t • D.generator) ^ n) := hsum
  change star (ev (∑' n : ℕ,
      (Nat.factorial n : ℝ)⁻¹ • (t • D.generator) ^ n)) =
    evStar (∑' n : ℕ,
      (Nat.factorial n : ℝ)⁻¹ • (t • D.generator) ^ n)
  rw [ev.map_tsum hsum, evStar.map_tsum hsumStar, tsum_star]
  apply tsum_congr
  intro n
  have hpow : ∀ (n : ℕ) (X : B(H)),
      star (((t • D.generator) ^ n) X) =
        ((t • D.generator) ^ n) (star X) := by
    intro m
    induction m with
    | zero => intro X; simp
    | succ m ih =>
        intro X
        rw [pow_succ]
        change star (((t • D.generator) ^ m) ((t • D.generator) X)) = _
        rw [ih]
        simp only [smul_apply, star_smul, star_trivial]
        rw [D.generator_star]
        rfl
  change star ((Nat.factorial n : ℝ)⁻¹ • (((t • D.generator) ^ n) A)) =
    (Nat.factorial n : ℝ)⁻¹ • (((t • D.generator) ^ n) (star A))
  rw [star_smul, hpow n A]
  simp

lemma lindbladRealEvolution_isHermitianPreserving (D : LindbladData H ι) (t : ℝ) :
    ∀ ⦃A : B(H)⦄, IsSelfAdjoint A →
      IsSelfAdjoint (lindbladRealEvolution D t A) := by
  intro A hA
  rw [isSelfAdjoint_iff]
  rw [lindbladRealEvolution_star, hA.star_eq]

lemma lindbladNonnegativeEvolution_eq_real (D : LindbladData H ι) (t : ℝ≥0) :
    lindbladNonnegativeEvolution D t = lindbladRealEvolution D (t : ℝ) := by
  change NormedSpace.exp ((t : ℂ) • D.generator) =
    NormedSpace.exp ((t : ℝ) • D.generator)
  simp only [NormedSpace.exp_eq_tsum ℂ]
  apply tsum_congr
  intro n
  congr 2

lemma LindbladData.eulerApproximation_tendsto_nonnegative
    (D : LindbladData H ι) [Nontrivial H] (t : ℝ≥0) :
    Tendsto
      (fun n => completelyPositiveMap_toContinuousLinearMap (D.eulerApproximation t n))
      atTop (nhds (lindbladNonnegativeEvolution D t)) := by
  rw [lindbladNonnegativeEvolution_eq_real]
  exact D.eulerApproximation_tendsto t

/-- The completely positive semigroup generated by bounded Lindblad data. -/
noncomputable def LindbladData.completelyPositiveSemigroup
    (D : LindbladData H ι) [Nontrivial H] :
    CompletelyPositiveSemigroup (B(H)) :=
  D.completelyPositiveSemigroup_of_eulerLimit
    (fun t => D.eulerApproximation_tendsto_nonnegative t)

lemma lindbladNonnegativeEvolution_star (D : LindbladData H ι) (t : ℝ≥0) (A : B(H)) :
    star (lindbladNonnegativeEvolution D t A) =
      lindbladNonnegativeEvolution D t (star A) := by
  rw [lindbladNonnegativeEvolution_eq_real]
  exact lindbladRealEvolution_star D (t : ℝ) A

lemma lindbladNonnegativeEvolution_isHermitianPreserving (D : LindbladData H ι) (t : ℝ≥0) :
    ∀ ⦃A : B(H)⦄, IsSelfAdjoint A →
      IsSelfAdjoint (lindbladNonnegativeEvolution D t A) := by
  intro A hA
  rw [isSelfAdjoint_iff]
  rw [lindbladNonnegativeEvolution_star, hA.star_eq]

/-! ## The channel-realization boundary -/

/-- A channel-valued realization of a bounded Lindblad exponential.

The channel field is intentional: the GKSL positivity theorem is the nontrivial quantum part.  A
later theorem can construct this field from the Lindblad data; once it is supplied, the semigroup
laws follow from the Banach-algebra exponential identities above.
-/
structure BoundedLindbladDynamics (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ι : Type*) [Fintype ι] where
  /-- Hamiltonian and noise operators. -/
  data : LindbladData H ι
  /-- The channel at every nonnegative time. -/
  map : ℝ≥0 → Channel (B(H)) (B(H))
  /-- The channel agrees pointwise with the Lindblad exponential. -/
  map_eq_exp : ∀ t A, map t A = lindbladNonnegativeEvolution data t A

namespace BoundedLindbladDynamics

/-- Build the channel-valued bounded Lindblad dynamics from a norm-convergent product formula.

This is the sufficiency interface: once the analytic Trotter limit has been established, all
channel, semigroup, continuity, and generator consequences are obtained by the existing bundled
APIs. -/
noncomputable def of_eulerLimit
    (D : LindbladData H ι)
    (hlim : ∀ t : ℝ≥0,
      Tendsto
        (fun n => completelyPositiveMap_toContinuousLinearMap (D.eulerApproximation t n))
        atTop (nhds (lindbladNonnegativeEvolution D t))) :
    BoundedLindbladDynamics H ι where
  data := D
  map := fun t => D.channel_of_eulerLimit t (hlim t)
  map_eq_exp := by
    intro t A
    change lindbladNonnegativeEvolution D t A = _
    rfl

/-- The channel-valued bounded Lindblad dynamics, with convergence supplied by the bounded product
formula. -/
noncomputable def of_lindbladData
    (D : LindbladData H ι) [Nontrivial H] :
    BoundedLindbladDynamics H ι :=
  of_eulerLimit D (fun t => D.eulerApproximation_tendsto_nonnegative t)

/-- Every channel realization of the bounded Lindblad exponential is a quantum dynamical
semigroup. -/
def toQuantumDynamicalSemigroup (D : BoundedLindbladDynamics H ι) :
    QuantumDynamicalSemigroup (B(H)) where
  map := D.map
  map_zero := by
    intro A
    rw [D.map_eq_exp, lindbladNonnegativeEvolution_zero]
    rfl
  map_add := by
    intro s t A
    rw [D.map_eq_exp, lindbladNonnegativeEvolution_add_apply]
    rw [D.map_eq_exp, D.map_eq_exp]
  continuous := by
    intro A
    have hmap : (fun t : ℝ≥0 => D.map t A) =
        (fun t : ℝ≥0 => lindbladNonnegativeEvolution D.data t A) := by
      funext t
      exact D.map_eq_exp t A
    rw [hmap]
    change Continuous (fun t : ℝ≥0 =>
      NormedSpace.exp ((t : ℂ) • D.data.generator) A)
    apply Continuous.clm_apply
    · apply NormedSpace.exp_continuous.comp
      fun_prop
    · fun_prop

/-! ### Compatibility with the abstract Christensen--Evans construction -/

/-- The concrete finite-noise Lindblad semigroup is the Christensen--Evans semigroup for its
bundled completely positive jump map.

This is the point at which the finite-noise API hands control to the representation-independent
bounded theory: both semigroups are identified by the same Banach-space exponential generator. -/
lemma toQuantumDynamicalSemigroup_map_eq_christensenEvans
    (D : BoundedLindbladDynamics H ι) [Nontrivial H] (t : ℝ≥0) (A : B(H)) :
      D.toQuantumDynamicalSemigroup.map t A =
      D.data.toChristensenEvansData.quantumDynamicalSemigroup.map t A := by
  change D.map t A = _
  rw [D.map_eq_exp]
  change NormedSpace.exp ((t : ℂ) • D.data.generator) A =
    D.data.toChristensenEvansData.realEvolution (t : ℝ) A
  rw [ChristensenEvansData.realEvolution_eq_complex]
  rw [D.data.toChristensenEvansData_generator]

/-- The same realization, with its bounded generator exposed through the general bounded-semigroup
interface. -/
noncomputable def toBoundedQuantumDynamicalSemigroup (D : BoundedLindbladDynamics H ι) :
    BoundedQuantumDynamicalSemigroup (B(H)) where
  toQuantumDynamicalSemigroup := D.toQuantumDynamicalSemigroup
  generator := D.data.generator
  map_eq_exp := by
    intro t A
    change D.map t A = _
    rw [D.map_eq_exp]
    rfl

/-! ### The common generator interface -/

/-- The derivative certificate carried by a channel-valued Lindblad realization.

This is the bridge from the Lindblad-specific presentation to the generic bounded-semigroup
API.  In particular, the exponential identity is no longer a second, unrelated generator
notion: it is recovered from the same right derivative certificate used by arbitrary bounded
quantum dynamical semigroups. -/
noncomputable def toHasBoundedGenerator (D : BoundedLindbladDynamics H ι) :
    QuantumDynamicalSemigroup.HasBoundedGenerator D.toQuantumDynamicalSemigroup :=
  D.toBoundedQuantumDynamicalSemigroup.toHasBoundedGenerator

@[simp]
lemma toHasBoundedGenerator_generator (D : BoundedLindbladDynamics H ι) :
    D.toHasBoundedGenerator.generator = D.data.generator :=
  rfl

lemma hasDerivWithinAt_generator (D : BoundedLindbladDynamics H ι) (A : B(H)) :
    HasDerivWithinAt
      (fun t : ℝ => D.toQuantumDynamicalSemigroup.map
        (BoundedQuantumDynamicalSemigroup.nonnegativeTime t) A)
      (D.data.generator A) (Set.Ici 0) 0 := by
  exact D.toHasBoundedGenerator.has_deriv A

lemma isNormContinuous (D : BoundedLindbladDynamics H ι) :
    QuantumDynamicalSemigroup.IsNormContinuous D.toQuantumDynamicalSemigroup := by
  exact D.toBoundedQuantumDynamicalSemigroup.isNormContinuous

lemma map_eq_exp_of_hasBoundedGenerator (D : BoundedLindbladDynamics H ι) (t : ℝ≥0)
    (A : B(H)) :
    D.map t A = NormedSpace.exp ((t : ℂ) • D.toHasBoundedGenerator.generator) A := by
  exact D.toHasBoundedGenerator.map_eq_exp_of_hasBoundedGenerator A t

end BoundedLindbladDynamics

end Exponential

end OperatorAlgebra
