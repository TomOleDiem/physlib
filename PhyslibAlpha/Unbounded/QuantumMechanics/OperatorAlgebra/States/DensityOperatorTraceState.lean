/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.DensityOperatorTraceBridge
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.NormalStateRepresentation

/-!
# The canonical trace state of a density operator

The completed trace-class ideal now proves all of the product and cyclicity facts needed to remove
the old `DensityOperatorStateCertificate` boundary.  The only subtle point is positivity: the
positive square root of a trace-class operator is Hilbert--Schmidt, so positivity of `Tr (ρ A)` is
proved by the Hilbert--Schmidt trace cycle

```text
Tr (ρ A) = Tr (√ρ (√ρ A)) = Tr ((√ρ A) √ρ) = Tr (√ρ A √ρ) ≥ 0.
```

The public constructors below therefore give the usual density-operator ↔ normal-state direction
in arbitrary Hilbert-space dimension.  The quadratic-form state remains available and is proved
equal to the trace state on positive observables.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace DensityOperator

variable (ρ : DensityOperator H)

private lemma sqrt_isHilbertSchmidt :
    HilbertSchmidt.IsHilbertSchmidt ρ.sqrtOperator := by
  have h := TraceClass.isHilbertSchmidt_sqrt_abs_of_isTraceClass ρ.traceClass
  rw [CFC.abs_of_nonneg ρ.ρ ρ.nonneg] at h
  exact h

private lemma sqrt_sq : ρ.sqrtOperator * ρ.sqrtOperator = ρ.ρ := by
  exact CFC.sqrt_mul_sqrt_self ρ.ρ ρ.nonneg

private lemma sqrt_selfAdjoint : IsSelfAdjoint ρ.sqrtOperator := by
  exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg ρ.ρ)

/-- The product trace of a density operator against a positive bounded operator is the trace of
the positive square-root sandwich. -/
theorem trace_mul_eq_trace_sandwiched_of_nonneg
    {A : B(H)} (hA : 0 ≤ A) :
    trace (ρ.ρ * A) (isTraceClass_mul_right ρ.traceClass A) =
      trace (ρ.sandwichedOperator A) (ρ.isTraceClass_sandwichedOperator hA) := by
  have hRA : HilbertSchmidt.IsHilbertSchmidt (ρ.sqrtOperator * A) :=
    HilbertSchmidt.isHilbertSchmidt_mul_right ρ.sqrt_isHilbertSchmidt
  have hleft : IsTraceClass (ρ.sqrtOperator * (ρ.sqrtOperator * A)) :=
    TraceClass.isTraceClass_mul_of_isHilbertSchmidt ρ.sqrt_isHilbertSchmidt hRA
  have hright : IsTraceClass ((ρ.sqrtOperator * A) * ρ.sqrtOperator) :=
    TraceClass.isTraceClass_mul_of_isHilbertSchmidt hRA ρ.sqrt_isHilbertSchmidt
  have hcycle := TraceClass.trace_mul_hilbertSchmidt_cycle
    ρ.sqrt_isHilbertSchmidt hRA
  have hleft_eq : ρ.sqrtOperator * (ρ.sqrtOperator * A) = ρ.ρ * A := by
    rw [← mul_assoc, ρ.sqrt_sq]
  have hright_eq : (ρ.sqrtOperator * A) * ρ.sqrtOperator = ρ.sandwichedOperator A := by
    rfl
  calc
    trace (ρ.ρ * A) (isTraceClass_mul_right ρ.traceClass A) =
        trace (ρ.sqrtOperator * (ρ.sqrtOperator * A))
          (hleft_eq ▸ isTraceClass_mul_right ρ.traceClass A) := by
      exact (TraceClass.trace_transport hleft_eq _).symm
    _ = trace ((ρ.sqrtOperator * A) * ρ.sqrtOperator) hright := hcycle
    _ = trace (ρ.sandwichedOperator A)
        (hright_eq ▸ ρ.isTraceClass_sandwichedOperator hA) := by
      exact TraceClass.trace_transport hright_eq _

/-- Positivity of the product-trace functional on positive observables. -/
theorem trace_mul_nonneg_of_nonneg {A : B(H)} (hA : 0 ≤ A) :
    0 ≤ trace (ρ.ρ * A) (isTraceClass_mul_right ρ.traceClass A) := by
  rw [ρ.trace_mul_eq_trace_sandwiched_of_nonneg hA]
  exact TraceClass.trace_nonneg_of_nonneg
    (by
      unfold sandwichedOperator
      have h := star_left_conjugate_nonneg hA ρ.sqrtOperator
      rw [ρ.sqrt_selfAdjoint] at h
      exact h)
    (ρ.isTraceClass_sandwichedOperator hA)

/-- The canonical state certificate for a density operator. -/
noncomputable def stateCertificate : DensityOperatorStateCertificate ρ := by
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
          trace (ρ.ρ * B) (isTraceClass_mul_right ρ.traceClass B) :=
        TraceClass.trace_add (isTraceClass_mul_right ρ.traceClass A)
          (isTraceClass_mul_right ρ.traceClass B)
  · intro c A
    unfold DensityOperator.toStateFun
    have hEq : ρ.ρ * (c • A) = c • (ρ.ρ * A) := mul_smul_comm c ρ.ρ A
    calc
      trace (ρ.ρ * (c • A)) (isTraceClass_mul_right ρ.traceClass (c • A)) =
          trace (c • (ρ.ρ * A))
            (hEq ▸ isTraceClass_mul_right ρ.traceClass (c • A)) :=
        TraceClass.trace_transport hEq _
      _ = c * trace (ρ.ρ * A) (isTraceClass_mul_right ρ.traceClass A) :=
        TraceClass.trace_smul c (isTraceClass_mul_right ρ.traceClass A)
  · intro A hA
    exact ρ.trace_mul_nonneg_of_nonneg hA

/-- The canonical state `A ↦ Tr (ρ A)` associated with a density operator. -/
noncomputable def canonicalState : State (B(H)) :=
  ρ.toState ρ.stateCertificate

@[simp]
lemma canonicalState_apply (A : B(H)) :
    ρ.canonicalState A = trace (ρ.ρ * A) (isTraceClass_mul_right ρ.traceClass A) := by
  rfl

/-- The canonical normal state `A ↦ Tr (ρ A)` associated with a density operator. -/
noncomputable def canonicalNormalState : NormalState (B(H)) :=
  ρ.toNormalState ρ.stateCertificate

@[simp]
lemma canonicalNormalState_toState :
    ρ.canonicalNormalState.toState = ρ.canonicalState := by
  rfl

/-- On positive observables, the canonical trace state agrees with the square-root quadratic-form
state. -/
theorem canonicalState_eq_quadraticForm_of_nonneg {A : B(H)} (hA : 0 ≤ A) :
    ρ.canonicalState A = ρ.quadraticForm A := by
  rw [canonicalState_apply, ρ.trace_mul_eq_trace_sandwiched_of_nonneg hA]
  exact (ρ.quadraticForm_eq_trace_sandwichedOperator hA).symm

/-! ### Identification with the concrete predual -/

/-- The canonical trace state is exactly the state represented by the corresponding trace-class
element under the concrete `B(H)` predual pairing.  The order of the two factors is reconciled by
cyclicity of the trace; this lemma is the useful interface for uniqueness and representation
results, since those are naturally stated using the predual pairing. -/
theorem canonicalNormalState_apply_predualPairing (A : B(H)) :
    ρ.canonicalNormalState A =
      WStarAlgebra.predualPairing
        (TraceClass.ofOperator ρ.ρ ρ.traceClass) A := by
  change trace (ρ.ρ * A) (isTraceClass_mul_right ρ.traceClass A) = _
  rw [WStarAlgebra.predualPairing_apply]
  change trace (ρ.ρ * A) _ = TraceClass.tracePairing A
    (TraceClass.ofOperator ρ.ρ ρ.traceClass)
  rw [TraceClass.tracePairing_apply]
  exact (TraceClass.trace_mul_cycle (A := A) (T := ρ.ρ) ρ.traceClass).symm

end DensityOperator

/-- Two normal states are equal as soon as their underlying states are equal.  The continuity
proofs are propositions, so they carry no additional extensional data. -/
private theorem NormalState.eq_of_toState_eq {ω ν : NormalState (B(H))}
    (h : ω.toState = ν.toState) : ω = ν := by
  cases ω with
  | mk ω hω =>
    cases ν with
    | mk ν hν =>
      dsimp at h ⊢
      cases h
      rfl

private theorem State.eq_of_toPositiveLinearMap_eq {s t : State (B(H))}
    (h : s.toPositiveLinearMap = t.toPositiveLinearMap) : s = t := by
  cases s with
  | mk s hs =>
    cases t with
    | mk t ht =>
      dsimp at h ⊢
      cases h
      rfl

/-- A density operator whose trace pairing represents a normal state produces that state through
the canonical trace construction. -/
theorem DensityOperator.canonicalNormalState_eq_of_predualPairing_eq
    (ρ : DensityOperator H) (ω : NormalState (B(H)))
    (h : ∀ A : B(H),
      WStarAlgebra.predualPairing
          (TraceClass.ofOperator ρ.ρ ρ.traceClass) A = ω A) :
    ρ.canonicalNormalState = ω := by
  apply NormalState.eq_of_toState_eq
  apply State.eq_of_toPositiveLinearMap_eq
  apply PositiveLinearMap.ext
  intro A
  change ρ.canonicalState A = ω A
  calc
    ρ.canonicalState A = ρ.canonicalNormalState A := by rfl
    _ = WStarAlgebra.predualPairing
          (TraceClass.ofOperator ρ.ρ ρ.traceClass) A :=
      ρ.canonicalNormalState_apply_predualPairing A
    _ = ω A := h A

/-- Every normal state on `B(H)` has a unique density operator, and its state is the canonical
trace state.  This is the practical density-operator/state equivalence for the concrete predual.
The older existential theorem remains available as the proof-producing primitive. -/
theorem NormalState.exists_unique_densityOperator (ω : NormalState (B(H))) :
    ∃! ρ : DensityOperator H, ρ.canonicalNormalState = ω := by
  obtain ⟨ρ, hρ⟩ := NormalState.exists_densityOperator ω
  have hρstate := ρ.canonicalNormalState_eq_of_predualPairing_eq ω hρ
  refine ⟨ρ, hρstate, ?_⟩
  intro σ hσ
  apply DensityOperator.ext_of_predualPairing_eq
  intro A
  calc
    WStarAlgebra.predualPairing
          (TraceClass.ofOperator σ.ρ σ.traceClass) A =
        σ.canonicalNormalState A :=
      (σ.canonicalNormalState_apply_predualPairing A).symm
    _ = ω A := congrArg (fun ν : NormalState (B(H)) => ν A) hσ
    _ = ρ.canonicalNormalState A :=
      (congrArg (fun ν : NormalState (B(H)) => ν A) hρstate).symm
    _ = WStarAlgebra.predualPairing
          (TraceClass.ofOperator ρ.ρ ρ.traceClass) A := by
      exact ρ.canonicalNormalState_apply_predualPairing A

/-- The unique density operator representing a normal state on `B(H)`. -/
noncomputable def NormalState.densityOperator (ω : NormalState (B(H))) : DensityOperator H :=
  Classical.choose (NormalState.exists_unique_densityOperator ω)

@[simp]
theorem NormalState.densityOperator_canonicalNormalState (ω : NormalState (B(H))) :
    (NormalState.densityOperator ω).canonicalNormalState = ω := by
  exact (Classical.choose_spec (NormalState.exists_unique_densityOperator ω)).1

theorem NormalState.densityOperator_unique (ω : NormalState (B(H)))
    {ρ : DensityOperator H} (hρ : ρ.canonicalNormalState = ω) :
    ρ = NormalState.densityOperator ω := by
  exact (Classical.choose_spec (NormalState.exists_unique_densityOperator ω)).2 ρ hρ

end OperatorAlgebra

end
