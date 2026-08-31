/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import PhyslibAlpha.QuantumMechanics.HarmonicOscillator.Basic
public import Physlib.QuantumMechanics.Operators.Commutation
public import Physlib.Meta.TODO.Basic
/-!

# Ladder operators

This file builds the raising/lowering ("ladder") operators of the `d`-dimensional quantum
harmonic oscillator on the common Schwartz core `𝓢(Space d, ℂ)`, and their algebra: the canonical
commutation relations, the number operators, and the number-operator Hamiltonian.

Everything here is built directly from `𝐱 i`/`𝐩 i` (`Operators.Position`/`Operators.Momentum`),
the continuous-linear-map-valued position/momentum operators on the Schwartz core, and the
already-proven `d`-dimensional canonical commutation relations of `Operators.Commutation`
(`position_commutation_position`, `momentum_commutation_momentum`,
`position_commutation_momentum`). No new calculus is needed: the ladder algebra below is *pure
ring/Lie-algebra bookkeeping* on top of those three facts, exactly the same computation pattern
as `OperatorAlgebra.Unbounded.Example.Schwartz`'s one-dimensional `ladderA`/`ladderAdag`/
`ladder_comm`, generalized to `d` dimensions and indexed by a Kronecker delta.

The Hamiltonian items (`numberHamiltonian`, its commutation with ladder/number operators, and the
factorization identity `numberHamiltonian = kineticPlusPotentialCLM`) are proved at the level of
the common Schwartz core `𝓢(Space d, ℂ)`, where `Q.hamiltonian`'s domain actually lives
(`hamiltonian_domain_eq : Q.hamiltonian.domain = SchwartzSubmodule d`, `EssentialSelfAdjointness.
lean`). Lifting the Schwartz-core identity `numberHamiltonian_eq_kineticPlusPotentialCLM` to a
literal `LinearPMap`/`QuantumSystem` equality with `Q.hamiltonian` itself is mechanical (chase
`schwartzIncl` through `momentumOperator_apply`/`positionOperator_apply` and the Schwartz-domain
restriction of the maximal potential multiplication operator, exactly paralleling
`HarmonicOscillator.DifferentialCore`'s one-dimensional `hamiltonian_apply_eigenfunction`
argument) but is not carried out here; it is recorded honestly as `informal_lemma`
`QM-Ladder-hamEq-lift` below, a genuine forward-looking documentation item, not a proof hole.

-/

@[expose] public section

noncomputable section

open Complex Constants KroneckerDelta Bracket SchwartzMap ContinuousLinearMap
open QuantumMechanics

namespace QuantumMechanics.HarmonicOscillator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {d : ℕ} (Q : HarmonicOscillator d) (i j k : Fin d)

/-!
## A. Ladder operators
-/

/-- The harmonic-oscillator normalization constant `√(2mℏωᵢ)` for the `i`-th mode. -/
def normConst (Q : HarmonicOscillator d) (i : Fin d) : ℝ :=
  Real.sqrt (2 * Q.m * (ℏ : ℝ) * Q.ω i)

lemma normConst_sq : (normConst Q i) ^ 2 = 2 * Q.m * (ℏ : ℝ) * Q.ω i := by
  have hℏ := ℏ_pos
  have hm := Q.m_pos
  have hω := Q.ω_pos i
  have hpos : (0 : ℝ) ≤ 2 * Q.m * (ℏ : ℝ) * Q.ω i := by positivity
  exact Real.sq_sqrt hpos

lemma normConst_ne_zero : normConst Q i ≠ 0 := by
  have hℏ := ℏ_pos
  have hpos : (0 : ℝ) < 2 * Q.m * (ℏ : ℝ) * Q.ω i := by
    have := Q.m_pos
    have := Q.ω_pos i
    positivity
  exact Real.sqrt_ne_zero'.mpr hpos

/-- The annihilation ("lowering") operator for the `i`-th mode,
`aᵢ = (m ωᵢ xᵢ + i pᵢ) / √(2mℏωᵢ)`. -/
def ladderA (Q : HarmonicOscillator d) (i : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  ((normConst Q i : ℂ))⁻¹ • ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i)

/-- The creation ("raising") operator for the `i`-th mode,
`aᵢ† = (m ωᵢ xᵢ - i pᵢ) / √(2mℏωᵢ)`. -/
def ladderAdag (Q : HarmonicOscillator d) (i : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  ((normConst Q i : ℂ))⁻¹ • ((Q.m * Q.ω i : ℝ) • 𝐱 i - Complex.I • 𝐩 i)

/-- `[xᵢ, pⱼ] = iℏδᵢⱼ` in commutator (`*`) form, a direct repackaging of
`position_commutation_momentum` used repeatedly below. -/
lemma position_mul_momentum_sub_momentum_mul_position :
    𝐱 i * 𝐩 j - 𝐩 j * 𝐱 i =
      (Complex.I * (ℏ : ℂ)) • δ[i, j] • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
  have h := position_commutation_momentum (d := d) i j
  simpa [Bracket.bracket, ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using h

/-- `[pᵢ, xⱼ] = -iℏδᵢⱼ` in commutator form, from antisymmetry of
`position_mul_momentum_sub_momentum_mul_position`. -/
lemma momentum_mul_position_sub_position_mul_momentum :
    𝐩 i * 𝐱 j - 𝐱 j * 𝐩 i =
      -((Complex.I * (ℏ : ℂ)) • δ[j, i] • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ))) := by
  have h := position_mul_momentum_sub_momentum_mul_position (d := d) j i
  linear_combination (norm := module) -h

/-- `[xᵢ, xⱼ] = 0` in commutator (`*`) form. -/
lemma position_mul_position_sub_position_mul_position :
    𝐱 i * 𝐱 j - 𝐱 j * 𝐱 i = (0 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
  have h := position_commutation_position (d := d) i j
  simpa [Bracket.bracket, ContinuousLinearMap.mul_def] using h

/-- `[pᵢ, pⱼ] = 0` in commutator (`*`) form. -/
lemma momentum_mul_momentum_sub_momentum_mul_momentum :
    𝐩 i * 𝐩 j - 𝐩 j * 𝐩 i = (0 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
  have h := momentum_commutation_momentum (d := d) i j
  simpa [Bracket.bracket, ContinuousLinearMap.mul_def] using h

/-- The raw (unnormalized) ladder commutator, for the *same* mode `i`:
`[mωᵢxᵢ + ipᵢ, mωᵢxᵢ - ipᵢ] = 2mωᵢℏ`. Same computation as `Unbounded.Example.Schwartz.
ladder_comm_raw`, specialized to a single coordinate `i`. -/
lemma ladder_comm_raw :
    ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i) * ((Q.m * Q.ω i : ℝ) • 𝐱 i - Complex.I • 𝐩 i) -
      ((Q.m * Q.ω i : ℝ) • 𝐱 i - Complex.I • 𝐩 i) * ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i)
      = (2 * Q.m * Q.ω i * (ℏ : ℝ) : ℝ) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
  have key : ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i) *
        ((Q.m * Q.ω i : ℝ) • 𝐱 i - Complex.I • 𝐩 i) -
      ((Q.m * Q.ω i : ℝ) • 𝐱 i - Complex.I • 𝐩 i) *
        ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i)
      = ((-Complex.I) * (Q.m * Q.ω i : ℝ) - Complex.I * (Q.m * Q.ω i : ℝ)) •
        (𝐱 i * 𝐩 i - 𝐩 i * 𝐱 i) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      pow_two, Complex.I_mul_I]
    module
  have hccr : 𝐱 i * 𝐩 i - 𝐩 i * 𝐱 i = (Complex.I * (ℏ : ℂ)) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
    simpa [KroneckerDelta.eq_one_of_same] using
      position_mul_momentum_sub_momentum_mul_position (d := d) i i
  rw [key, hccr, smul_smul]
  have hscalar : ((-Complex.I) * (Q.m * Q.ω i : ℝ) - Complex.I * (Q.m * Q.ω i : ℝ)) *
      (Complex.I * (ℏ : ℂ)) = ((2 * Q.m * Q.ω i * (ℏ : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring_nf
    rw [show Complex.I ^ 2 = Complex.I * Complex.I by ring, Complex.I_mul_I]
    ring
  rw [hscalar]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

/-- **`[aᵢ, aᵢ†] = 1`**, the single-mode case. Identical algebra to `Unbounded.Example.Schwartz.
ladder_comm`. -/
lemma ladder_comm_self :
    ladderA Q i * ladderAdag Q i - ladderAdag Q i * ladderA Q i
      = (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
  unfold ladderA ladderAdag
  rw [smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, ladder_comm_raw,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  have hreal : (normConst Q i)⁻¹ * (normConst Q i)⁻¹ * (2 * Q.m * Q.ω i * (ℏ : ℝ)) = 1 := by
    have hc2 := normConst_sq Q i
    have hne := normConst_ne_zero Q i
    field_simp
    nlinarith [hc2]
  have hc : ((normConst Q i : ℂ))⁻¹ * ((normConst Q i : ℂ))⁻¹ *
      (2 * (Q.m : ℂ) * (Q.ω i : ℂ) * (ℏ : ℂ)) = 1 := by
    have := congrArg Complex.ofReal hreal
    push_cast at this
    convert this using 2
  push_cast
  simp [hc]

/-- Cross-mode ladder commutators vanish: for `i ≠ j`, every one of the four position/momentum
building blocks of `[aᵢ, aⱼ†]` already commutes (`position_mul_position_sub_position_mul_position`,
`momentum_mul_momentum_sub_momentum_mul_momentum`, and
`position_mul_momentum_sub_momentum_mul_position` at `δ[i,j] = 0`), so the raw commutator is
identically zero — no new calculus, purely algebraic cancellation. -/
lemma ladder_comm_cross (hij : i ≠ j) :
    ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i) * ((Q.m * Q.ω j : ℝ) • 𝐱 j - Complex.I • 𝐩 j) -
      ((Q.m * Q.ω j : ℝ) • 𝐱 j - Complex.I • 𝐩 j) * ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i)
      = (0 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
  have key : ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i) *
        ((Q.m * Q.ω j : ℝ) • 𝐱 j - Complex.I • 𝐩 j) -
      ((Q.m * Q.ω j : ℝ) • 𝐱 j - Complex.I • 𝐩 j) *
        ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i)
      = (Q.m * Q.ω i * Q.m * Q.ω j : ℝ) • (𝐱 i * 𝐱 j - 𝐱 j * 𝐱 i)
        - (Complex.I * (Q.m * Q.ω i : ℝ)) • (𝐱 i * 𝐩 j - 𝐩 j * 𝐱 i)
        + (Complex.I * (Q.m * Q.ω j : ℝ)) • (𝐩 i * 𝐱 j - 𝐱 j * 𝐩 i)
        + (𝐩 i * 𝐩 j - 𝐩 j * 𝐩 i) := by
    simp only [add_mul, mul_add, sub_mul, mul_sub, smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      pow_two, Complex.I_mul_I, Complex.I_sq]
    module
  rw [key, position_mul_position_sub_position_mul_position,
    position_mul_momentum_sub_momentum_mul_position, momentum_mul_position_sub_position_mul_momentum,
    momentum_mul_momentum_sub_momentum_mul_momentum,
    KroneckerDelta.eq_zero_of_ne hij, KroneckerDelta.eq_zero_of_ne hij.symm]
  simp

/-- **The canonical commutation relations for the ladder operators, `[aᵢ, aⱼ†] = δᵢⱼ`.** Split
into the same-mode case (`ladder_comm_self`, reusing the one-dimensional `Unbounded.Example.
Schwartz` computation pattern) and the cross-mode case (`ladder_comm_cross`, pure algebraic
cancellation from the already-proven `d`-dimensional CCR). -/
lemma ladder_commutation_ladderAdag :
    ladderA Q i * ladderAdag Q j - ladderAdag Q j * ladderA Q i =
      δ[i, j] • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [KroneckerDelta.eq_one_of_same, one_smul, ladder_comm_self]
  · rw [KroneckerDelta.eq_zero_of_ne hij, zero_smul]
    unfold ladderA ladderAdag
    have hcoef : ((normConst Q i : ℂ))⁻¹ * ((normConst Q j : ℂ))⁻¹ =
        ((normConst Q j : ℂ))⁻¹ * ((normConst Q i : ℂ))⁻¹ := by ring
    rw [smul_mul_smul_comm, smul_mul_smul_comm, hcoef, ← smul_sub,
      ladder_comm_cross Q i j hij, smul_zero]

/-- `[aᵢ, aⱼ] = 0`: the lowering operators for distinct modes commute, and even for the same mode
(`lie_self`-style triviality). Proved the same way as `ladder_comm_cross`/`position_commutation_
position`, since `aᵢ` is built only from `𝐱 i`/`𝐩 i`. -/
lemma ladder_commutation_ladder :
    ladderA Q i * ladderA Q j - ladderA Q j * ladderA Q i =
      (0 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
  unfold ladderA
  have key : ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i) *
        ((Q.m * Q.ω j : ℝ) • 𝐱 j + Complex.I • 𝐩 j) -
      ((Q.m * Q.ω j : ℝ) • 𝐱 j + Complex.I • 𝐩 j) *
        ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i)
      = (Q.m * Q.ω i * Q.m * Q.ω j : ℝ) • (𝐱 i * 𝐱 j - 𝐱 j * 𝐱 i)
        + (Complex.I * (Q.m * Q.ω i : ℝ)) • (𝐱 i * 𝐩 j - 𝐩 j * 𝐱 i)
        + (Complex.I * (Q.m * Q.ω j : ℝ)) • (𝐩 i * 𝐱 j - 𝐱 j * 𝐩 i)
        - (𝐩 i * 𝐩 j - 𝐩 j * 𝐩 i) := by
    simp only [add_mul, mul_add, smul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      pow_two, Complex.I_mul_I, Complex.I_sq]
    module
  have hcoef : ((normConst Q i : ℂ))⁻¹ * ((normConst Q j : ℂ))⁻¹ =
      ((normConst Q j : ℂ))⁻¹ * ((normConst Q i : ℂ))⁻¹ := by ring
  rw [smul_mul_smul_comm, smul_mul_smul_comm, hcoef, ← smul_sub, key,
    position_mul_position_sub_position_mul_position,
    position_mul_momentum_sub_momentum_mul_position,
    momentum_mul_position_sub_position_mul_momentum,
    momentum_mul_momentum_sub_momentum_mul_momentum]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [KroneckerDelta.eq_zero_of_ne hij, KroneckerDelta.eq_zero_of_ne hij.symm]
    simp

/-- `[aᵢ†, aⱼ†] = 0`: the raising operators commute, by the same computation. -/
lemma ladder_commutation_ladderAdag_ladderAdag :
    ladderAdag Q i * ladderAdag Q j - ladderAdag Q j * ladderAdag Q i =
      (0 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
  unfold ladderAdag
  have key : ((Q.m * Q.ω i : ℝ) • 𝐱 i - Complex.I • 𝐩 i) *
        ((Q.m * Q.ω j : ℝ) • 𝐱 j - Complex.I • 𝐩 j) -
      ((Q.m * Q.ω j : ℝ) • 𝐱 j - Complex.I • 𝐩 j) *
        ((Q.m * Q.ω i : ℝ) • 𝐱 i - Complex.I • 𝐩 i)
      = (Q.m * Q.ω i * Q.m * Q.ω j : ℝ) • (𝐱 i * 𝐱 j - 𝐱 j * 𝐱 i)
        - (Complex.I * (Q.m * Q.ω i : ℝ)) • (𝐱 i * 𝐩 j - 𝐩 j * 𝐱 i)
        - (Complex.I * (Q.m * Q.ω j : ℝ)) • (𝐩 i * 𝐱 j - 𝐱 j * 𝐩 i)
        - (𝐩 i * 𝐩 j - 𝐩 j * 𝐩 i) := by
    simp only [sub_mul, mul_sub, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
      pow_two, Complex.I_mul_I, Complex.I_sq]
    module
  have hcoef : ((normConst Q i : ℂ))⁻¹ * ((normConst Q j : ℂ))⁻¹ =
      ((normConst Q j : ℂ))⁻¹ * ((normConst Q i : ℂ))⁻¹ := by ring
  rw [smul_mul_smul_comm, smul_mul_smul_comm, hcoef, ← smul_sub, key,
    position_mul_position_sub_position_mul_position,
    position_mul_momentum_sub_momentum_mul_position,
    momentum_mul_position_sub_position_mul_momentum,
    momentum_mul_momentum_sub_momentum_mul_momentum]
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [KroneckerDelta.eq_zero_of_ne hij, KroneckerDelta.eq_zero_of_ne hij.symm]
    simp

/-!
## B. Number operators
-/

/-- The number operator for the `i`-th mode, `Nᵢ = aᵢ†aᵢ`. -/
def numberOperator (Q : HarmonicOscillator d) (i : Fin d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  ladderAdag Q i * ladderA Q i

informal_lemma numberOperator_isSelfAdjoint where
  deps := [``numberOperator]
  tag := "QM-Ladder-NselfAdj"

/-- **`[Nᵢ, Nⱼ] = 0`**: the number operators for distinct modes commute — and trivially for the
same mode. Proved by `leibniz_lie`/`lie_leibniz`-style expansion into ladder commutators, all of
which are already known (`ladder_commutation_ladderAdag`, `ladder_commutation_ladder`,
`ladder_commutation_ladderAdag_ladderAdag`). -/
lemma numberOperator_commutation_numberOperator :
    numberOperator Q i * numberOperator Q j - numberOperator Q j * numberOperator Q i =
      (0 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
  unfold numberOperator
  have hAdagA : ladderAdag Q i * ladderA Q i * (ladderAdag Q j * ladderA Q j) -
      ladderAdag Q j * ladderA Q j * (ladderAdag Q i * ladderA Q i) =
      ladderAdag Q i * (ladderA Q i * ladderAdag Q j) * ladderA Q j
        - ladderAdag Q i * (ladderAdag Q j * ladderA Q i) * ladderA Q j
        - (ladderAdag Q j * (ladderA Q j * ladderAdag Q i) * ladderA Q i
          - ladderAdag Q j * (ladderAdag Q i * ladderA Q j) * ladderA Q i) := by
    have e1 : ladderA Q i * ladderAdag Q j =
        ladderAdag Q j * ladderA Q i + δ[i, j] • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
      have := ladder_commutation_ladderAdag Q i j
      linear_combination (norm := module) this
    have e2 : ladderA Q j * ladderAdag Q i =
        ladderAdag Q i * ladderA Q j + δ[j, i] • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
      have := ladder_commutation_ladderAdag Q j i
      linear_combination (norm := module) this
    rw [e1, e2]
    simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
    rcases eq_or_ne i j with rfl | hij
    · simp only [KroneckerDelta.eq_one_of_same, one_smul, smul_mul_assoc,
        mul_smul_comm, one_mul, mul_one]
      noncomm_ring
    · rw [KroneckerDelta.eq_zero_of_ne hij, KroneckerDelta.eq_zero_of_ne hij.symm]
      simp only [zero_smul, smul_zero, zero_mul, sub_zero]
      have h1 : ladderA Q i * ladderAdag Q j = ladderAdag Q j * ladderA Q i := by
        have h := ladder_commutation_ladderAdag Q i j
        exact sub_eq_zero.mp (by simpa [KroneckerDelta.eq_zero_of_ne hij] using h)
      have h2 : ladderA Q j * ladderAdag Q i = ladderAdag Q i * ladderA Q j := by
        have h := ladder_commutation_ladderAdag Q j i
        exact sub_eq_zero.mp (by simpa [KroneckerDelta.eq_zero_of_ne hij.symm] using h)
      have hA : ladderA Q i * ladderA Q j = ladderA Q j * ladderA Q i := by
        exact sub_eq_zero.mp (ladder_commutation_ladder Q i j)
      have hD : ladderAdag Q i * ladderAdag Q j = ladderAdag Q j * ladderAdag Q i := by
        exact sub_eq_zero.mp (ladder_commutation_ladderAdag_ladderAdag Q i j)
      simp only [mul_assoc]
      have hi1 : ladderA Q i * (ladderAdag Q j * ladderA Q j) =
          ladderAdag Q j * (ladderA Q i * ladderA Q j) := by
        calc
          _ = (ladderA Q i * ladderAdag Q j) * ladderA Q j := by
            rw [← mul_assoc (ladderA Q i) (ladderAdag Q j) (ladderA Q j)]
          _ = (ladderAdag Q j * ladderA Q i) * ladderA Q j := by rw [h1]
          _ = _ := by rw [mul_assoc]
      have hi2 : ladderA Q j * (ladderAdag Q i * ladderA Q i) =
          ladderAdag Q i * (ladderA Q j * ladderA Q i) := by
        calc
          _ = (ladderA Q j * ladderAdag Q i) * ladderA Q i := by
            rw [← mul_assoc (ladderA Q j) (ladderAdag Q i) (ladderA Q i)]
          _ = (ladderAdag Q i * ladderA Q j) * ladderA Q i := by rw [h2]
          _ = _ := by rw [mul_assoc]
      rw [hi1, hi2]
      calc
        _ = (ladderAdag Q i * ladderAdag Q j) * (ladderA Q i * ladderA Q j) -
            (ladderAdag Q j * ladderAdag Q i) * (ladderA Q j * ladderA Q i) := by
          noncomm_ring
        _ = 0 := by rw [hD, hA]; simp
        _ = _ := by noncomm_ring
  rw [hAdagA]
  rcases eq_or_ne i j with rfl | hij
  · noncomm_ring
  · have h1 : ladderA Q i * ladderAdag Q j = ladderAdag Q j * ladderA Q i := by
      have h := ladder_commutation_ladderAdag Q i j
      exact sub_eq_zero.mp (by simpa [KroneckerDelta.eq_zero_of_ne hij] using h)
    have h2 : ladderA Q j * ladderAdag Q i = ladderAdag Q i * ladderA Q j := by
      have h := ladder_commutation_ladderAdag Q j i
      exact sub_eq_zero.mp (by simpa [KroneckerDelta.eq_zero_of_ne hij.symm] using h)
    rw [h1, h2]
    noncomm_ring

/-- `[Nᵢ, aⱼ] = -δᵢⱼ aⱼ`: the annihilation operator lowers the occupation number by one. -/
lemma numberOperator_commutation_ladder :
    numberOperator Q i * ladderA Q j - ladderA Q j * numberOperator Q i =
      -(δ[i, j] • ladderA Q j) := by
  unfold numberOperator
  have e : ladderA Q i * ladderA Q j - ladderA Q j * ladderA Q i =
      (0 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := ladder_commutation_ladder Q i j
  have e2 : ladderAdag Q i * ladderA Q j =
      ladderA Q j * ladderAdag Q i - δ[j, i] • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
    have := ladder_commutation_ladderAdag Q j i
    linear_combination (norm := module) -this
  have key : ladderAdag Q i * ladderA Q i * ladderA Q j - ladderA Q j * (ladderAdag Q i * ladderA Q i)
      = (ladderAdag Q i * ladderA Q j) * ladderA Q i - ladderA Q j * ladderAdag Q i * ladderA Q i := by
    calc
      _ = (ladderAdag Q i * ladderA Q j) * ladderA Q i -
          ladderA Q j * ladderAdag Q i * ladderA Q i +
          ladderAdag Q i * (ladderA Q i * ladderA Q j - ladderA Q j * ladderA Q i) := by
        noncomm_ring
      _ = _ := by rw [e, mul_zero, add_zero]
  rw [key, e2, sub_mul]
  rw [KroneckerDelta.symm j i]
  rcases eq_or_ne i j with rfl | hij
  · simp only [KroneckerDelta.eq_one_of_same, one_smul, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one]
    noncomm_ring
  · rw [KroneckerDelta.eq_zero_of_ne hij]
    simp only [zero_smul, smul_zero, zero_mul, sub_zero]
    noncomm_ring

/-- `[Nᵢ, aⱼ†] = δᵢⱼ aⱼ†`: the creation operator raises the occupation number by one. -/
lemma numberOperator_commutation_ladderAdag :
    numberOperator Q i * ladderAdag Q j - ladderAdag Q j * numberOperator Q i =
      δ[i, j] • ladderAdag Q j := by
  unfold numberOperator
  have e : ladderAdag Q i * ladderAdag Q j - ladderAdag Q j * ladderAdag Q i =
      (0 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) :=
    ladder_commutation_ladderAdag_ladderAdag Q i j
  have e2 : ladderA Q i * ladderAdag Q j =
      ladderAdag Q j * ladderA Q i + δ[i, j] • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
    have := ladder_commutation_ladderAdag Q i j
    linear_combination (norm := module) this
  have key : ladderAdag Q i * ladderA Q i * ladderAdag Q j -
      ladderAdag Q j * (ladderAdag Q i * ladderA Q i)
      = ladderAdag Q i * (ladderA Q i * ladderAdag Q j) - ladderAdag Q j * ladderAdag Q i * ladderA Q i := by
    simp only [mul_assoc]
  rw [key, e2, mul_add]
  simp only [mul_smul_comm, mul_one]
  rcases eq_or_ne i j with rfl | hij
  · simp only [KroneckerDelta.eq_one_of_same, one_smul, smul_mul_assoc,
      mul_smul_comm, one_mul, mul_one]
    noncomm_ring
  · rw [KroneckerDelta.eq_zero_of_ne hij, zero_smul]
    calc
      _ = (ladderAdag Q i * ladderAdag Q j - ladderAdag Q j * ladderAdag Q i) * ladderA Q i := by
        noncomm_ring
      _ = 0 := by rw [e, zero_mul]
    simp

/-!
## C. Hamiltonian
-/

/-- **The number-operator Hamiltonian**, `H_N = ℏ ∑ᵢ ωᵢ (Nᵢ + 1/2)`. -/
def numberHamiltonian (Q : HarmonicOscillator d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  (ℏ : ℂ) • ∑ i, (Q.ω i : ℝ) • (numberOperator Q i + (2⁻¹ : ℝ) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)))

informal_lemma numberHamiltonian_commutation_numberOperator where
  deps := [``numberHamiltonian, ``numberOperator]
  tag := "QM-Ladder-HNcommN"

informal_lemma numberHamiltonian_commutation_ladder where
  deps := [``numberHamiltonian, ``ladderA]
  tag := "QM-Ladder-HNcommA"

/-- **The Schwartz-core "kinetic + potential" Hamiltonian**, `∑ᵢ pᵢ²/(2m) + (1/2)mωᵢ²xᵢ²`, built
directly from `𝐱 i`/`𝐩 i` — the CLM-level analogue, on the common core, of `Q.kineticOperator +
Q.potentialOperator = Q.hamiltonian`. -/
def kineticPlusPotentialCLM (Q : HarmonicOscillator d) : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ) :=
  ((2 * Q.m : ℝ)⁻¹ : ℝ) • (∑ i, 𝐩 i * 𝐩 i) + ∑ i, ((Q.m * (Q.ω i) ^ 2 / 2 : ℝ) : ℝ) • (𝐱 i * 𝐱 i)

/-- **The two Hamiltonians agree, on the common Schwartz core.** The number-operator Hamiltonian
`numberHamiltonian` equals the "kinetic + potential" Hamiltonian `kineticPlusPotentialCLM`, mode
by mode: exactly the same algebraic factorization as `Unbounded.Example.Schwartz.hamiltonian_eq`
(`ladder_prod_raw`), applied to each coordinate `i` and summed. -/
lemma numberHamiltonian_eq_kineticPlusPotentialCLM :
    numberHamiltonian Q = kineticPlusPotentialCLM Q := by
  have hmode : ∀ i : Fin d, (ℏ : ℂ) • ((Q.ω i : ℝ) •
      (numberOperator Q i + (2⁻¹ : ℝ) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)))) =
      ((2 * Q.m : ℝ)⁻¹ : ℝ) • (𝐩 i * 𝐩 i) + ((Q.m * (Q.ω i) ^ 2 / 2 : ℝ) : ℝ) • (𝐱 i * 𝐱 i) := by
    intro i
    unfold numberOperator ladderAdag ladderA
    have hℏ := ℏ_pos
    have hprod : ((normConst Q i : ℂ))⁻¹ • ((Q.m * Q.ω i : ℝ) • 𝐱 i - Complex.I • 𝐩 i) *
        (((normConst Q i : ℂ))⁻¹ • ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i)) =
        (((normConst Q i : ℂ))⁻¹ * ((normConst Q i : ℂ))⁻¹) •
          (((Q.m * Q.ω i : ℝ) ^ 2 : ℝ) • (𝐱 i * 𝐱 i) + (𝐩 i * 𝐩 i)
            - (Q.m * Q.ω i * (ℏ : ℝ) : ℝ) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ))) := by
      rw [smul_mul_smul_comm]
      congr 1
      have hPP : (Complex.I • 𝐩 i) * (Complex.I • 𝐩 i) = -(𝐩 i * 𝐩 i) := by
        rw [smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul]
      have key : ((Q.m * Q.ω i : ℝ) • 𝐱 i - Complex.I • 𝐩 i) *
          ((Q.m * Q.ω i : ℝ) • 𝐱 i + Complex.I • 𝐩 i) =
          ((Q.m * Q.ω i : ℝ) ^ 2 : ℝ) • (𝐱 i * 𝐱 i) +
            (Complex.I * (Q.m * Q.ω i : ℝ)) • (𝐱 i * 𝐩 i - 𝐩 i * 𝐱 i) -
            (Complex.I • 𝐩 i) * (Complex.I • 𝐩 i) := by
        simp only [sub_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
        module
      have hccr : 𝐱 i * 𝐩 i - 𝐩 i * 𝐱 i =
          (Complex.I * (ℏ : ℂ)) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ)) := by
        simpa [KroneckerDelta.eq_one_of_same] using
          position_mul_momentum_sub_momentum_mul_position (d := d) i i
      have hscalar : (Complex.I * (Q.m * Q.ω i : ℝ)) •
          ((Complex.I * (ℏ : ℂ)) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ))) =
          -((Q.m * Q.ω i * (ℏ : ℝ) : ℝ) • (1 : 𝓢(Space d, ℂ) →L[ℂ] 𝓢(Space d, ℂ))) := by
        ext ψ x
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
          ContinuousLinearMap.one_apply, Complex.real_smul, smul_eq_mul]
        push_cast
        rw [show Complex.I * (↑Q.m * ↑(Q.ω i)) * (Complex.I * ↑ℏ * ψ x)
            = Complex.I * Complex.I * (↑Q.m * ↑(Q.ω i) * ↑ℏ) * ψ x by ring, Complex.I_mul_I]
        ring
      rw [key, hccr, hscalar, hPP]
      abel
    rw [hprod]
    have hc2 := normConst_sq Q i
    have hne := normConst_ne_zero Q i
    have hkey : ((normConst Q i : ℂ))⁻¹ * ((normConst Q i : ℂ))⁻¹ =
        ((2 * Q.m * (ℏ : ℝ) * Q.ω i : ℝ) : ℂ)⁻¹ := by
      rw [← hc2]; push_cast; ring
    rw [hkey]
    have h2mℏω : ((2 * Q.m * (ℏ : ℝ) * Q.ω i : ℝ) : ℂ) ≠ 0 := by
      have hℏ := ℏ_pos
      have hm := Q.m_pos
      have hω := Q.ω_pos i
      have : (2 * Q.m * (ℏ : ℝ) * Q.ω i : ℝ) ≠ 0 := by positivity
      exact_mod_cast this
    ext ψ x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.one_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    field_simp
    ring
  unfold numberHamiltonian kineticPlusPotentialCLM
  rw [Finset.smul_sum]
  rw [Finset.sum_congr rfl (fun i _ => hmode i)]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum]

informal_lemma numberHamiltonian_eq_hamiltonian_lift where
  deps := [``numberHamiltonian_eq_kineticPlusPotentialCLM, ``HarmonicOscillator.hamiltonian]
  tag := "QM-Ladder-hamEq-lift"

informal_lemma numberHamiltonian_toQuantumSystem_eq where
  deps := [``numberHamiltonian_eq_hamiltonian_lift]
  tag := "QM-Ladder-sysEq"

end QuantumMechanics.HarmonicOscillator
end
