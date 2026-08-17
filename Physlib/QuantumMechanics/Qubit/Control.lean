/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Qubit.State

/-!
# Piecewise-constant control of a qubit

## TODO: driven qubits and Ramsey spectroscopy

Start from an unknown qubit splitting and a transverse drive,
`H₀ = ω₀ Z / 2` and
`H(t) = H₀ + Ω (cos (ωd t) X + sin (ωd t) Y) / 2`.
In the rotating frame this becomes
`Hrot = (Δ Z + Ω X) / 2`, where `Δ = ω₀ - ωd`.

The intended development is:

1. Prove the detuned Rabi formula
   `P₁(t) = Ω² / (Ω² + Δ²) * sin² (sqrt (Ω² + Δ²) * t / 2)`.
2. Construct finite-duration `π / 2` pulses using the same detuned Hamiltonian.
3. Compose two such pulses with free evolution for time `T` and a final `Z` measurement.
4. Recover the ideal instantaneous-pulse Ramsey probability
   `p(Δ) = (1 + cos (Δ T)) / 2`, whose fringe spacing is `2π / T`.
5. Derive the broad off-resonant envelope from the exact finite-duration pulse sequence. It
   should not be added phenomenologically: the pulse is no longer a perfect `π / 2` rotation
   when `|Δ|` is comparable to or larger than `Ω`.

This provides the deterministic part of Ramsey spectroscopy. Repeated `Z` measurements may then
be modeled by `Kj ~ Binomial N (p Δj)` to estimate `ω₀`, or a field `B` when
`ω₀ = ωref + γ B`.
-/

@[expose] public section

open Constants
open scoped PauliMatrix

noncomputable section

namespace QuantumMechanics.Qubit

/-- Cartesian x-axis on the Bloch sphere. -/
def xAxis : Fin 3 → ℝ := ![1, 0, 0]

/-- Cartesian z-axis on the Bloch sphere. -/
def zAxis : Fin 3 → ℝ := ![0, 0, 1]

/-- Cartesian y-axis on the Bloch sphere. -/
def yAxis : Fin 3 → ℝ := ![0, 1, 0]

/-- Ramsey readout: a y-axis π/2 pulse, free z-precession through phase `φ`, and a
negative-y π/2 pulse convert the accumulated phase into the population signal `cos φ`. -/
lemma ramsey_z_signal (φ : ℝ) :
    rotateBloch (-yAxis)
      (rotateBloch zAxis (rotateBloch yAxis zAxis (Real.pi / 2)) φ)
      (Real.pi / 2) 2 = Real.cos φ := by
  simp [rotateBloch, yAxis, zAxis, dotProduct, cross_apply, Fin.sum_univ_succ]

/-- A constant resonant pulse with Hamiltonian `H = ℏΩ(n·σ)/2`. -/
structure Pulse where
  /-- Rotation axis. -/
  axis : Fin 3 → ℝ
  /-- Rabi frequency. -/
  rabiFrequency : ℝ
  /-- Pulse duration. -/
  duration : ℝ

namespace Pulse

/-- The rotation angle produced by a pulse. -/
def angle (P : Pulse) : ℝ := P.rabiFrequency * P.duration

/-- The constant Hamiltonian applied during a pulse. -/
def hamiltonian (P : Pulse) : Hamiltonian :=
  (ℏ * P.rabiFrequency / 2) •
    ∑ i : Fin 3, P.axis i • PauliMatrix.pauliSelfAdjoint (Sum.inr i)

/-- The explicit matrix applied by a pulse. -/
def evolutionMatrix (P : Pulse) : Matrix (Fin 2) (Fin 2) ℂ :=
  Qubit.evolutionMatrix P.hamiltonian P.duration

/-- A pulse whose duration produces a rotation through `θ`. -/
def ofAngle (axis : Fin 3 → ℝ) (Ω θ : ℝ) : Pulse where
  axis := axis
  rabiFrequency := Ω
  duration := θ / Ω

lemma ofAngle_angle (axis : Fin 3 → ℝ) (Ω θ : ℝ) (hΩ : Ω ≠ 0) :
    (ofAngle axis Ω θ).angle = θ := by
  simp [ofAngle, angle]
  field_simp [hΩ]

/-- A π pulse about `axis`. -/
def piPulse (axis : Fin 3 → ℝ) (Ω : ℝ) : Pulse := ofAngle axis Ω Real.pi

/-- A π/2 pulse about `axis`. -/
def piHalfPulse (axis : Fin 3 → ℝ) (Ω : ℝ) : Pulse := ofAngle axis Ω (Real.pi / 2)

lemma piPulse_angle (axis : Fin 3 → ℝ) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    (piPulse axis Ω).angle = Real.pi := ofAngle_angle axis Ω Real.pi hΩ

lemma piHalfPulse_angle (axis : Fin 3 → ℝ) (Ω : ℝ) (hΩ : Ω ≠ 0) :
    (piHalfPulse axis Ω).angle = Real.pi / 2 := ofAngle_angle axis Ω (Real.pi / 2) hΩ

end Pulse

/-- A piecewise-constant control protocol, in chronological order. -/
abbrev PulseSequence := List Pulse

namespace PulseSequence

/-- Total duration of a pulse sequence. -/
def duration (S : PulseSequence) : ℝ := (S.map Pulse.duration).sum

/-- Ordered product of the pulse matrices. -/
def evolutionMatrix (S : PulseSequence) : Matrix (Fin 2) (Fin 2) ℂ :=
  (S.map Pulse.evolutionMatrix).reverse.prod

@[simp] lemma evolutionMatrix_nil : evolutionMatrix [] = 1 := rfl

@[simp] lemma evolutionMatrix_cons (P : Pulse) (S : PulseSequence) :
    evolutionMatrix (P :: S) = evolutionMatrix S * P.evolutionMatrix := by
  simp [evolutionMatrix]

end PulseSequence

end QuantumMechanics.Qubit
