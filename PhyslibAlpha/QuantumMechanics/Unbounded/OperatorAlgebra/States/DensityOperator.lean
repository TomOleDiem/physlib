/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.Pairing
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.PositiveTrace
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass.TraceAlgebra
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.FiniteDim.Trace
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.States.NormalState
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Measurement.PVM
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.WStarAlgebra.InfiniteDim
public import Physlib.Meta.TODO.Basic

/-!

# Density operators: the concrete `B(H)` realization of `NormalState`

For the concrete case `M = B(H)`, the selected predual is the completed trace-class space
`TraceClass H`, with pairing `ρ ↦ (A ↦ Tr(Aρ))`. Density operators — positive, trace-one
elements of `TraceClass H` — are the standard concrete representatives of normal states on `B(H)`:

```
normal states on B(H)  ⟷  {ρ ∈ 𝒮₁(H) : ρ ≥ 0, Tr ρ = 1}
```

The quadratic-form state in `DensityOperatorQuadraticForm.lean` is the canonical currently
available state constructor. The trace bridge in `DensityOperatorTraceBridge.lean` proves its
agreement with `Tr(√ρ A √ρ)` for positive bounded observables, deliberately avoiding any product
with an unbounded observable: spectral projections are bounded.

## Boundary

The general trace ideal, completed trace-class space, trace pairing, and `WStarAlgebra (B(H))`
instance are proved in `TraceClass/` and `WStarAlgebra/InfiniteDimensional.lean`. This file keeps
`TraceClassRightIdeal` and `DensityOperatorStateCertificate` as compatibility interfaces for the
product-trace constructor; the square-root quadratic-form constructor is the no-capability route.

## Key results

- `DensityOperator H` : a positive, trace-one, trace-class operator.
- `DensityOperator.toState` : the induced state `ω_ρ(A) = Tr(ρA)` on `B(H)`.
- `DensityOperator.toState_apply_one` : `ω_ρ(1) = 1` — proved directly from `trace_eq_one`,
  independent of the ideal/positivity gaps above.

-/

set_option maxHeartbeats 1000000

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Density operators -/

/-- **A density operator**: a positive, trace-one, trace-class operator on `H` — the concrete
`B(H)` realization of a normal state, `ρ ↦ ω_ρ`. -/
structure DensityOperator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The underlying operator. -/
  ρ : B(H)
  /-- A density operator is positive. -/
  nonneg : 0 ≤ ρ
  /-- A density operator is trace class. -/
  traceClass : IsTraceClass ρ
  /-- A density operator has trace one — total probability. -/
  trace_eq_one : trace ρ traceClass = 1

/-- The general trace-ideal theorem supplies the right-ideal property.  It is kept as a named
interface for source compatibility with the finite-dimensional API, but the canonical instance
below is available in every complete Hilbert space. -/
class TraceClassRightIdeal (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Prop where
  mul_right : ∀ {ρ : B(H)}, IsTraceClass ρ → ∀ A : B(H), IsTraceClass (ρ * A)

/-- In finite dimension the ideal obligation is immediate: every bounded operator is trace class.
This instance is intentionally restricted to finite-dimensional Hilbert spaces; the corresponding
infinite-dimensional ideal theorem is a genuine trace-ideal result and remains a separate
construction. -/
noncomputable instance instTraceClassRightIdealFiniteDimensional
    [FiniteDimensional ℂ H] : TraceClassRightIdeal H where
  mul_right := by
    intro ρ hρ A
    exact isTraceClass_of_finiteDimensional (ρ * A)

/-- Trace-class operators are closed under multiplication on the right by every bounded operator.
This is the concrete two-sided ideal theorem, specialized to the operation needed by density
operators; no extra capability or finite-dimensional hypothesis is required. -/
noncomputable instance instTraceClassRightIdeal : TraceClassRightIdeal H where
  mul_right := by
    intro ρ hρ A
    simpa using (TraceClass.isTraceClass_mul_mul (A := (1 : B(H))) (B := A) hρ)

/-- The right-ideal theorem without going through the capability class.  This form is useful in
proofs whose result already carries its own trace-class witness, and also prevents typeclass
search from becoming part of the analytic argument. -/
theorem isTraceClass_mul_right {ρ : B(H)} (hρ : IsTraceClass ρ) (A : B(H)) :
    IsTraceClass (ρ * A) := by
  simpa using (TraceClass.isTraceClass_mul_mul (A := (1 : B(H))) (B := A) hρ)

theorem IsTraceClass.mul_right [TraceClassRightIdeal H] {ρ : B(H)}
    (hρ : IsTraceClass ρ) (A : B(H)) : IsTraceClass (ρ * A) :=
  TraceClassRightIdeal.mul_right hρ A

/-- **The state induced by a density operator**, `ω_ρ(A) = \operatorname{Tr}(\rho A)`. -/
def DensityOperator.toStateFun [TraceClassRightIdeal H] (ρ : DensityOperator H) (A : B(H)) : ℂ :=
  trace (ρ.ρ * A) (ρ.traceClass.mul_right A)

@[simp]
lemma DensityOperator.toStateFun_one [TraceClassRightIdeal H] (ρ : DensityOperator H) :
    ρ.toStateFun 1 = 1 := by
  unfold DensityOperator.toStateFun
  convert ρ.trace_eq_one using 2
  exact mul_one ρ.ρ

/-- The certificate remains an explicit boundary for the product-trace presentation.  The fully
general state construction is available as `DensityOperator.toStateQuadraticForm`, which never
forms an unbounded product and is implemented in `DensityOperatorQuadraticForm.lean`. -/
structure DensityOperatorStateCertificate [TraceClassRightIdeal H]
    (ρ : DensityOperator H) where
  map_add : ∀ A B : B(H), ρ.toStateFun (A + B) = ρ.toStateFun A + ρ.toStateFun B
  map_smul : ∀ (c : ℂ) (A : B(H)), ρ.toStateFun (c • A) = c * ρ.toStateFun A
  map_nonneg : ∀ {A : B(H)}, 0 ≤ A → 0 ≤ ρ.toStateFun A

/-! ### The finite-dimensional certificate

In finite dimension the witness-basis trace is the ordinary linear-map trace, so the existing
finite-dimensional trace pairing supplies all three certificate laws. -/

private lemma trace_eq_linearMap_trace_of_finiteDimensional
    [FiniteDimensional ℂ H] (T : B(H)) (h : IsTraceClass T) :
    trace T h = LinearMap.trace ℂ H T.toLinearMap := by
  unfold trace
  exact (trace_eq_sum_inner_hilbertBasis_of_finiteDimensional T h.choose_spec.choose).symm

/-- The standard density-operator state certificate in finite dimension. -/
theorem densityOperatorStateCertificate_of_finiteDimensional
    [FiniteDimensional ℂ H] (ρ : DensityOperator H) :
    DensityOperatorStateCertificate ρ := by
  have hEq (A : B(H)) : ρ.toStateFun A = operatorTracePairing ρ.ρ A := by
    unfold DensityOperator.toStateFun
    rw [trace_eq_linearMap_trace_of_finiteDimensional]
    exact (operatorTracePairing_apply _ _).symm
  refine { map_add := ?_, map_smul := ?_, map_nonneg := ?_ }
  · intro A B
    rw [hEq, hEq, hEq]
    exact (operatorTracePairing ρ.ρ).map_add A B
  · intro c A
    rw [hEq, hEq]
    simp [smul_eq_mul, (operatorTracePairing ρ.ρ).map_smul c A]
  · intro A hA
    rw [hEq]
    exact operatorTracePairing_nonneg ρ.nonneg hA

/-- Build the normalized state once the trace ideal and positive-pairing facts are supplied. -/
def DensityOperator.toState [TraceClassRightIdeal H] (ρ : DensityOperator H)
    (C : DensityOperatorStateCertificate ρ) : State (B(H)) where
  toPositiveLinearMap := PositiveLinearMap.mk₀
    { toFun := ρ.toStateFun
      map_add' := C.map_add
      map_smul' := by
        intro c A
        simpa [smul_eq_mul] using C.map_smul c A }
    (fun A hA => C.map_nonneg hA)
  map_one := ρ.toStateFun_one

/-- Turn the product-trace state into a normal state for the concrete trace-class predual.

The only compatibility input is the state certificate already required by `toState`; weak-*
continuity is a theorem, because the resulting functional is the predual trace pairing after one
application of cyclicity of the trace. -/
noncomputable def DensityOperator.toNormalState [TraceClassRightIdeal H]
    (ρ : DensityOperator H) (C : DensityOperatorStateCertificate ρ) : NormalState (B(H)) where
  toState := ρ.toState C
  weakStar_continuous := by
    let ξ : TraceClass H := TraceClass.ofOperator ρ.ρ ρ.traceClass
    have hcont := WStarAlgebra.predualPairing_weakStar_continuous
      (A := B(H)) ξ
    have heq : (⇑(ρ.toState C) : B(H) → ℂ) =
        WStarAlgebra.predualPairing ξ := by
      funext A
      change ρ.toStateFun A = _
      unfold DensityOperator.toStateFun
      change trace (ρ.ρ * A) (ρ.traceClass.mul_right A) =
        TraceClass.tracePairing A ξ
      rw [TraceClass.tracePairing_apply]
      change trace (ρ.ρ * A) _ = trace (A * ρ.ρ) _
      exact (TraceClass.trace_mul_cycle (A := A) (T := ρ.ρ) ρ.traceClass).symm
    rw [heq]
    exact hcont

/-
The direct product-trace certificate is deliberately kept here as a design sketch.  The
quadratic-form construction in `DensityOperatorQuadraticForm.lean` is the canonical state API;
the product-trace presentation can be reintroduced in a separate bridge module once its
normality theorem is packaged.

private lemma trace_mul_nonneg_of_nonneg {ρ A : B(H)} (hρ : 0 ≤ ρ)
    (hρclass : IsTraceClass ρ) (hA : 0 ≤ A) :
    0 ≤ trace (ρ * A) (isTraceClass_mul_right hρclass A) := by
  let S : B(H) := CFC.sqrt A
  have hSself : IsSelfAdjoint S := by
    dsimp [S]
    exact .of_nonneg (CFC.sqrt_nonneg A)
  have hSsq : S * S = A := by
    dsimp [S]
    exact CFC.sqrt_mul_sqrt_self A hA
  have hρS : IsTraceClass (ρ * S) := isTraceClass_mul_right hρclass S
  have hSρS : IsTraceClass (S * ρ * S) :=
    TraceClass.isTraceClass_mul_mul (A := S) (B := S) hρclass
  have hpos : 0 ≤ S * ρ * S := by
    have h := star_left_conjugate_nonneg hρ S
    rw [hSself] at h
    exact h
  have hcycle := TraceClass.trace_mul_cycle (A := S) (T := ρ * S) hρS
  have hright : IsTraceClass ((ρ * S) * S) :=
    TraceClass.isTraceClass_mul_mul (A := (1 : B(H))) (B := S) hρS
  have heq : (ρ * S) * S = ρ * A := by
    rw [← mul_assoc, hSsq]
  have htrace : trace ((ρ * S) * S) hright =
      trace (S * ρ * S) hSρS := by
    calc
      trace ((ρ * S) * S) hright = trace (S * (ρ * S))
          (TraceClass.isTraceClass_mul_mul (A := S) (B := (1 : B(H))) hρS) := hcycle.symm
      _ = trace (S * ρ * S) hSρS := by
        congr 1
        simp only [mul_assoc]
  calc
    0 ≤ trace (S * ρ * S) hSρS := TraceClass.trace_nonneg_of_nonneg hpos hSρS
    _ = trace ((ρ * S) * S) hright := htrace.symm
    _ = trace (ρ * A) (isTraceClass_mul_right hρclass A) := by
      rw [heq]

/-- The canonical density-operator state certificate in arbitrary dimension. -/
noncomputable def densityOperatorStateCertificate (ρ : DensityOperator H) :
    DensityOperatorStateCertificate ρ := by
  refine { map_add := ?_, map_smul := ?_, map_nonneg := ?_ }
  · intro A B
    unfold DensityOperator.toStateFun
    have hEq : ρ.ρ * (A + B) = ρ.ρ * A + ρ.ρ * B := mul_add _ _ _
    calc
      trace (ρ.ρ * (A + B)) (isTraceClass_mul_right ρ.traceClass (A + B)) =
          trace (ρ.ρ * A + ρ.ρ * B)
            (hEq ▸ isTraceClass_mul_right ρ.traceClass (A + B)) :=
        TraceClass.trace_transport hEq _
      _ = trace (ρ.ρ * A) (isTraceClass_mul_right ρ.traceClass A) +
          trace (ρ.ρ * B) (isTraceClass_mul_right ρ.traceClass B) := by
        exact TraceClass.trace_add (isTraceClass_mul_right ρ.traceClass A)
          (isTraceClass_mul_right ρ.traceClass B)
  · intro c A
    unfold DensityOperator.toStateFun
    have hEq : ρ.ρ * (c • A) = c • (ρ.ρ * A) := by
      exact mul_smul_comm c ρ.ρ A
    calc
      trace (ρ.ρ * (c • A)) (isTraceClass_mul_right ρ.traceClass (c • A)) =
          trace (c • (ρ.ρ * A)) (hEq ▸ isTraceClass_mul_right ρ.traceClass (c • A)) :=
        TraceClass.trace_transport hEq _
      _ = c * trace (ρ.ρ * A) (ρ.traceClass.mul_right A) := by
        exact TraceClass.trace_smul c (isTraceClass_mul_right ρ.traceClass A)
  · intro A hA
    exact trace_mul_nonneg_of_nonneg ρ.nonneg ρ.traceClass hA


-/

/-! ## The measurement-statistics specialization -/

/-- **The textbook Born rule**, as the concrete `B(H)`-level specialization of
`AffiliatedObservable.distribution`/`PVM.distribution`'s general `μ_ω(S) = ω(E(S))`:
`μ_ρ^H(S) = \operatorname{Tr}(\rho \cdot E_H(S))`. Deliberately at the level of the *bounded*
spectral projection `E_H(S)`, never the potentially ill-defined product `ρH` for unbounded `H` —
exactly the point the module docstring makes. Stated with the trace-pairing spelled out directly
(rather than through the compatibility-only `DensityOperator.toState` constructor) so this
headline formula is visible and checkable independently of the state representation theorem. -/
def bornRule {X : Type*} [MeasurableSpace X] (E : PVM X (B(H))) (ρ : DensityOperator H)
    (S : Set X) (h : IsTraceClass (ρ.ρ * (E S))) : ℂ :=
  trace (ρ.ρ * (E S)) h

end
