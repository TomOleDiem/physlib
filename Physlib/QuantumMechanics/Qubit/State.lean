/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Qubit.Hamiltonian
public import Physlib.Relativity.PauliMatrices.SelfAdjoint
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.Matrix.Spectrum

/-!

# Qubit states and their time evolution

A qubit density matrix has the Bloch decomposition
`ρ = (I + r₁ σ₁ + r₂ σ₂ + r₃ σ₃) / 2`. This is exactly the Pauli decomposition already provided
by `Physlib.Relativity.PauliMatrices.SelfAdjoint`, applied to `ρ`'s own matrix, so nothing here
is reproved by hand.

This file works entirely with Physlib's own `𝒟[Fin 2]` (`QuantumMechanics.OperatorAlgebra.Basic`)
and Mathlib's `Matrix.IsHermitian` spectral theory; it has no dependency on the external
`QuantumInfo` library. Purity, the spectrum, and von Neumann entropy are given their usual
closed-form descriptions directly.

This file also describes the unitary evolution `ρ(t) = U(t) ρ U(t)⋆`, in the same
scalar-plus-rotation form already established for observables in `QuantumMechanics.Qubit.Hamiltonian`:
the Bloch vector is rotated about the Pauli-vector axis while the scalar part contributes nothing.

## Main results

* `eq_bloch`: the Bloch-sphere form of an arbitrary qubit density matrix.
* `purity_eq_blochRadius`, `vonNeumannEntropy_eq_blochRadius`: the purity and von Neumann entropy
  of a qubit state, in terms of its Bloch radius.
* `evolvedBlochVector_eq_blochTrajectory`: Hamiltonian evolution rotates the Bloch vector by the
  familiar Rodrigues rotation formula.

-/

@[expose] public section

open BigOperators Constants
open scoped PauliMatrix Matrix

noncomputable section

namespace QuantumMechanics.Qubit

variable (rho : 𝒟[Fin 2])


/-!
## Bloch decomposition and state invariants
-/

/-- The density matrix of a qubit state, as a self-adjoint `2 × 2` matrix. -/
noncomputable def densityMat (rho : 𝒟[Fin 2]) : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  Observable.toMatrix (rho : 𝒪[Fin 2])

lemma trace_densityMat : Matrix.trace (densityMat rho : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [densityMat, coe_observable_toMatrix, ← operatorTrace_eq_matrix_trace]
  exact rho.property

/-- The Bloch-vector component `r_i = Tr(σᵢ ρ)`. -/
noncomputable def blochComponent (i : Fin 3) : ℝ :=
  2 * PauliMatrix.pauliCoeff (densityMat rho) (Sum.inr i)

/-- The Bloch vector of a qubit state. -/
noncomputable def blochVector : Fin 3 → ℝ := fun i ↦ blochComponent rho i

/-- Length of the Bloch vector. -/
noncomputable def blochRadius : ℝ := Real.sqrt (∑ i : Fin 3, blochVector rho i ^ 2)

/-- Every qubit density matrix is a real linear combination of the four Pauli matrices. -/
lemma state_eq_sum_pauli :
    densityMat rho =
      ∑ mu, PauliMatrix.pauliCoeff (densityMat rho) mu • PauliMatrix.pauliSelfAdjoint mu :=
  PauliMatrix.eq_sum_pauli (densityMat rho)

/-- The identity coefficient of a density matrix is `1 / 2`, because its trace is one. -/
lemma pauliCoeff_identity : PauliMatrix.pauliCoeff (densityMat rho) (Sum.inl 0) = 1 / 2 := by
  simp [PauliMatrix.pauliCoeff, PauliMatrix.pauliMatrix, trace_densityMat]

/-- The Bloch-sphere form of an arbitrary qubit density matrix. -/
lemma eq_bloch :
    densityMat rho = (1 / 2 : ℝ) •
      ((1 : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) +
        ∑ i : Fin 3, blochComponent rho i • PauliMatrix.pauliSelfAdjoint (Sum.inr i)) := by
  conv_lhs => rw [state_eq_sum_pauli rho]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, pauliCoeff_identity, blochComponent]
  rw [show PauliMatrix.pauliSelfAdjoint (Sum.inl (0 : Fin 1)) =
      (1 : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) from
    Subtype.ext PauliMatrix.pauliMatrix_inl_zero_eq_one]
  rw [smul_add]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul]
  congr 1
  ring

/-- The purity `Tr(ρ²)` of a qubit density matrix. -/
noncomputable def purity (rho : 𝒟[Fin 2]) : ℝ :=
  RCLike.re (Matrix.trace ((densityMat rho : Matrix (Fin 2) (Fin 2) ℂ) *
    (densityMat rho : Matrix (Fin 2) (Fin 2) ℂ)))

/-- The purity is `(1 + |r|²)/2` for a qubit. -/
lemma purity_eq_blochRadius : purity rho = (1 + blochRadius rho ^ 2) / 2 := by
  rw [purity]
  conv_lhs => rw [eq_bloch rho]
  rw [blochRadius, Real.sq_sqrt (by positivity)]
  simp [blochVector, blochComponent, PauliMatrix.pauliCoeff,
    PauliMatrix.pauliSelfAdjoint, PauliMatrix.pauliMatrix, Matrix.trace_fin_two,
    Matrix.one_fin_two, Fin.sum_univ_succ]
  ring_nf

/-- The density matrix is Hermitian. -/
theorem densityMat_isHermitian (rho : 𝒟[Fin 2]) :
    (densityMat rho : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian :=
  (densityMat rho).property

/-- The eigenvalues of a qubit density matrix. -/
noncomputable def spectrum (rho : 𝒟[Fin 2]) : Fin 2 → ℝ :=
  (densityMat_isHermitian rho).eigenvalues

lemma sum_spectrum : ∑ i, spectrum rho i = 1 := by
  rw [spectrum]
  have h := (densityMat_isHermitian rho).trace_eq_sum_eigenvalues (𝕜 := ℂ)
  rw [trace_densityMat] at h
  have hre := congrArg RCLike.re h
  simpa using hre.symm

lemma sum_spectrum_sq_eq_purity : ∑ i, spectrum rho i ^ 2 = purity rho := by
  rw [spectrum]
  have h : ∑ i, ((densityMat_isHermitian rho).eigenvalues i : ℂ) ^ 2 =
      Matrix.trace ((densityMat rho : Matrix (Fin 2) (Fin 2) ℂ) *
        (densityMat rho : Matrix (Fin 2) (Fin 2) ℂ)) := by
    conv_rhs => rw [(densityMat_isHermitian rho).spectral_theorem]
    simp [Matrix.trace_mul_comm, Matrix.mul_assoc]
    ring
  have hre := congrArg RCLike.re h
  simp only [Fin.sum_univ_two, map_add, ← Complex.ofReal_pow] at hre
  rw [purity, Fin.sum_univ_two]
  exact hre

/-- A qubit's von Neumann entropy is the binary entropy determined by its Bloch radius. -/
noncomputable def vonNeumannEntropy (rho : 𝒟[Fin 2]) : ℝ :=
  ∑ i, Real.negMulLog (spectrum rho i)

lemma vonNeumannEntropy_eq_blochRadius :
    vonNeumannEntropy rho = Real.binEntropy ((1 + blochRadius rho) / 2) := by
  have hsum : spectrum rho 0 + spectrum rho 1 = 1 := by
    have h := sum_spectrum rho
    rwa [Fin.sum_univ_two] at h
  have hsq : spectrum rho 0 ^ 2 + spectrum rho 1 ^ 2 = (1 + blochRadius rho ^ 2) / 2 := by
    rw [← purity_eq_blochRadius rho, ← sum_spectrum_sq_eq_purity rho, Fin.sum_univ_two]
  have hr : 0 ≤ blochRadius rho := Real.sqrt_nonneg _
  have hroot : spectrum rho 0 = (1 + blochRadius rho) / 2 ∨
      spectrum rho 0 = (1 - blochRadius rho) / 2 := by
    have hfactor :
        (2 * spectrum rho 0 - 1 - blochRadius rho) *
          (2 * spectrum rho 0 - 1 + blochRadius rho) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with h | h
    · left; nlinarith
    · right; nlinarith
  rw [vonNeumannEntropy, Fin.sum_univ_two]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rcases hroot with h | h
  · rw [h]
    have hq : spectrum rho 1 = 1 - (1 + blochRadius rho) / 2 := by nlinarith
    rw [hq]
  · rw [h]
    have hq : spectrum rho 1 = (1 + blochRadius rho) / 2 := by nlinarith
    have hminus : 1 - (1 + blochRadius rho) / 2 = (1 - blochRadius rho) / 2 := by ring
    rw [hq, hminus, add_comm]


/-!
## Time evolution of the Bloch vector
-/

/-- The evolution matrix generated by the observable with components `(a₀, a)`: the matrix-level
form of `timeEvolutionℏ_apply_observableOfComponents`. -/
noncomputable def evolutionMatrix (a₀ : ℝ) (a : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  operatorToMatrix (Observable.timeEvolutionℏ (observableOfComponents a₀ a) t : 𝒜[Fin 2])

lemma evolutionMatrix_eq (a₀ : ℝ) (a : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    evolutionMatrix a₀ a t =
      Complex.exp (-(t : ℂ) * Complex.I * a₀ / ℏ) •
        ((Real.cos (t * ‖a‖ / ℏ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) -
          ((Real.sin (t * ‖a‖ / ℏ) : ℂ) * Complex.I / ‖a‖) •
            PauliMatrix.vectorMatrix (a : Fin 3 → ℝ)) := by
  show operatorAlgebraEquivMatrix
      (Observable.timeEvolutionℏ (observableOfComponents a₀ a) t : 𝒜[Fin 2]) = _
  rw [timeEvolutionℏ_apply_observableOfComponents, map_smul (M := ℂ) operatorAlgebraEquivMatrix,
    map_sub, map_smul (M := ℂ) operatorAlgebraEquivMatrix,
    map_smul (M := ℂ) operatorAlgebraEquivMatrix, map_one,
    operatorAlgebraEquivMatrix_vectorObservable]

/-- Rodrigues rotation of a Bloch vector about `n` through angle `θ`. -/
noncomputable def rotateBloch (n r : Fin 3 → ℝ) (θ : ℝ) : Fin 3 → ℝ :=
  fun i ↦ Real.cos θ * r i + Real.sin θ * (n ⨯₃ r) i +
    (1 - Real.cos θ) * (n ⬝ᵥ r) * n i

/-- For the observable `a₀ I + a · σ`, the Bloch vector rotates about `a / |a|` through the angle
`2t|a| / ℏ` (constant when `a = 0`). The scalar part `a₀ I` has no effect. -/
noncomputable def blochTrajectory (a : EuclideanSpace ℝ (Fin 3)) (t : ℝ) : Fin 3 → ℝ :=
  let c := Real.cos (t * ‖a‖ / ℏ)
  let q := Real.sin (t * ‖a‖ / ℏ) / ‖a‖
  fun i ↦ c ^ 2 * blochVector rho i + 2 * c * q * ((a : Fin 3 → ℝ) ⨯₃ blochVector rho) i +
    q ^ 2 * (2 * ((a : Fin 3 → ℝ) ⬝ᵥ blochVector rho) * (a : Fin 3 → ℝ) i -
      (∑ j, (a : Fin 3 → ℝ) j ^ 2) * blochVector rho i)

/-- The Bloch vector obtained by evolving `rho` under the observable with components
`(a₀, a)` for time `t`. -/
noncomputable def evolvedBlochVector (a₀ : ℝ) (a : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    Fin 3 → ℝ := fun i ↦
  (Matrix.trace (PauliMatrix.pauliMatrix (Sum.inr i) *
    (evolutionMatrix a₀ a t * (densityMat rho : Matrix (Fin 2) (Fin 2) ℂ) *
      (evolutionMatrix a₀ a t).conjTranspose))).re

set_option maxRecDepth 2000 in
/-- Hamiltonian time evolution rotates the initial Bloch vector according to
`blochTrajectory`. -/
lemma evolvedBlochVector_eq_blochTrajectory (a₀ : ℝ) (a : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    evolvedBlochVector rho a₀ a t = blochTrajectory rho a t := by
  have hphase :
      Complex.exp (-((t : ℂ) * Complex.I * a₀) / ℏ) *
        star (Complex.exp (-((t : ℂ) * Complex.I * a₀) / ℏ)) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp]
    simp
  funext i
  fin_cases i <;>
  by_cases h : ‖a‖ = 0
  case pos | pos | pos =>
    have hevol : evolutionMatrix a₀ a t * (densityMat rho : Matrix (Fin 2) (Fin 2) ℂ) *
        (evolutionMatrix a₀ a t).conjTranspose = (densityMat rho : Matrix (Fin 2) (Fin 2) ℂ) := by
      have heq : evolutionMatrix a₀ a t =
          Complex.exp (-((t : ℂ) * Complex.I * a₀) / ℏ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [evolutionMatrix_eq, h]
        simp
      rw [heq]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one]
      rw [mul_comm (star _) _, hphase]
      simp
    simp only [evolvedBlochVector, hevol]
    simp [blochTrajectory, h, blochVector, blochComponent, PauliMatrix.pauliCoeff, densityMat]
  all_goals
  · let phase := Complex.exp (-((t : ℂ) * Complex.I * a₀) / ℏ)
    let c := Real.cos (t * ‖a‖ / ℏ)
    let q := Real.sin (t * ‖a‖ / ℏ) / ‖a‖
    let av : Fin 3 → ℝ := (a : Fin 3 → ℝ)
    let R : Matrix (Fin 2) (Fin 2) ℂ :=
      (c : ℂ) • 1 + (-(q : ℂ) * Complex.I) • PauliMatrix.vectorMatrix av
    have hevolution : evolutionMatrix a₀ a t = phase • R := by
      rw [evolutionMatrix_eq]
      simp only [phase, R, c, q, av, sub_eq_add_neg]
      rw [show -(t : ℂ) * Complex.I * a₀ / ↑ℏ = -((t : ℂ) * Complex.I * a₀) / ↑ℏ by ring]
      module
    have hcancel :
        (phase • R) * (densityMat rho : Matrix (Fin 2) (Fin 2) ℂ) * (phase • R).conjTranspose =
          R * (densityMat rho : Matrix (Fin 2) (Fin 2) ℂ) * R.conjTranspose := by
      rw [Matrix.conjTranspose_smul]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_comm (star phase) phase, show phase * star phase = 1 by exact hphase]
      simp
    simp only [evolvedBlochVector]
    rw [hevolution, hcancel]
    have hR : R = !![(c : ℂ) - Complex.I * (q * av 2),
        -(q * av 1 : ℝ) - Complex.I * (q * av 0);
        (q * av 1 : ℝ) - Complex.I * (q * av 0),
        (c : ℂ) + Complex.I * (q * av 2)] := by
      ext j k
      fin_cases j <;> fin_cases k <;>
        simp [R, av, PauliMatrix.vectorMatrix, PauliMatrix.pauliMatrix, Fin.sum_univ_succ] <;>
        ring_nf <;> simp [Complex.I_sq]
      all_goals ring
    rw [hR]
    simp [blochTrajectory, av, blochVector, blochComponent, PauliMatrix.pauliCoeff,
      densityMat, PauliMatrix.pauliMatrix, Matrix.trace_fin_two, Matrix.one_fin_two,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, cross_apply]
    dsimp [c, q, av]
    ring

end QuantumMechanics.Qubit
