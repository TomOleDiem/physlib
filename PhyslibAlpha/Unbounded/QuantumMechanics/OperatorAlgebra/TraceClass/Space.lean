/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.GeneralProduct
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.IdealNorm
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.TraceClass.PositiveIdeal

/-!
# The trace-class Banach space `𝒮₁(H)`

This file assembles the general (not merely positive) trace-ideal theory of `GeneralProduct.lean`
and `IdealNorm.lean` into the actual object promised by the roadmap: the subtype of trace-class
operators, packaged as a `Submodule ℂ (B(H))` (so it inherits `AddCommGroup`/`Module ℂ` for free),
equipped with the trace norm as an honest `NormedAddCommGroup`/`NormedSpace ℂ` structure, and
proved complete.

## Main definitions

- `traceClassSubmodule H` : the trace-class operators, as a `Submodule ℂ (B(H))`.
- `TraceClass H` : notation for that submodule's carrier type, i.e. `𝒮₁(H)`.
- The `NormedAddCommGroup (TraceClass H)` / `NormedSpace ℂ (TraceClass H)` instances, with norm
  `traceNorm`.
- `instCompleteSpaceTraceClass` : completeness, via the absolutely-convergent-series criterion.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TraceClass

/-- The trace-class operators form a `ℂ`-submodule of `B(H)`: closed under zero, addition (general,
not just positive — `isTraceClass_add`), and scalar multiplication. -/
theorem isTraceClass_zero : IsTraceClass (0 : B(H)) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  exact ⟨w, b, by simp [CFC.abs_zero]⟩

theorem traceNorm_zero : traceNorm (0 : B(H)) isTraceClass_zero = 0 := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  rw [traceNorm_eq_of_hilbertBasis isTraceClass_zero b]
  simp [CFC.abs_zero]

theorem isTraceClass_neg {T : B(H)} (hT : IsTraceClass T) : IsTraceClass (-T) := by
  have h := isTraceClass_smul (-1 : ℂ) hT
  rwa [neg_one_smul] at h

/-- Transporting `traceNorm` across an equality of the underlying operator. Needed because `rw`
cannot rewrite `traceNorm`'s operator argument directly (the motive depends on the witness proof).
    -/
theorem traceNorm_transport {X Y : B(H)} (hEq : X = Y) (hX : IsTraceClass X) :
    traceNorm X hX = traceNorm Y (hEq ▸ hX) := by
  subst hEq; rfl

theorem traceNorm_neg {T : B(H)} (hT : IsTraceClass T) (hnegT : IsTraceClass (-T)) :
    traceNorm (-T) hnegT = traceNorm T hT := by
  have h1 := traceNorm_smul (-1 : ℂ) hT
  have h2 := traceNorm_transport (neg_one_smul ℂ T) (isTraceClass_smul (-1) hT)
  calc
    traceNorm (-T) hnegT =
        traceNorm (-T) (neg_one_smul ℂ T ▸ isTraceClass_smul (-1) hT) := traceNorm_congr
    _ = traceNorm ((-1 : ℂ) • T) (isTraceClass_smul (-1) hT) := h2.symm
    _ = ‖(-1 : ℂ)‖ * traceNorm T hT := h1
    _ = traceNorm T hT := by norm_num

/-- **The trace-class operators, as a `ℂ`-submodule of `B(H)`.** This is the concrete object
underlying the trace-class Banach space: its carrier type inherits `AddCommGroup`/`Module ℂ`
directly from the ambient `Submodule` API, so only the norm structure remains to be supplied. -/
def traceClassSubmodule (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : Submodule ℂ (B(H)) where
  carrier := {T | IsTraceClass T}
  zero_mem' := isTraceClass_zero
  add_mem' ha hb := isTraceClass_add ha hb
  smul_mem' c _ ha := isTraceClass_smul c ha

end TraceClass

/-- **The trace-class Banach space `𝒮₁(H)`.** Deliberately a plain (semireducible) `def`, not an
`abbrev`: the carrier of `traceClassSubmodule H` already has a generic `Submodule`-induced
`NormedAddCommGroup` instance coming from `B(H)`'s *operator* norm, and marking `TraceClass H`
reducible would let typeclass search find that competing instance instead of the trace-norm one
constructed below.  The `AddCommGroup`/`Module ℂ` structure is still recovered for free by
re-exporting the submodule's own instances. -/
def TraceClass (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Type _ :=
  TraceClass.traceClassSubmodule H

namespace TraceClass

noncomputable instance instAddCommGroup : AddCommGroup (TraceClass H) :=
  inferInstanceAs (AddCommGroup (traceClassSubmodule H))

noncomputable instance instModule : Module ℂ (TraceClass H) :=
  inferInstanceAs (Module ℂ (traceClassSubmodule H))

theorem mem_iff {T : B(H)} : T ∈ traceClassSubmodule H ↔ IsTraceClass T := Iff.rfl

/-- The trace-class witness carried by an element of `TraceClass H`. -/
theorem isTraceClass_coe (T : TraceClass H) : IsTraceClass T.1 := T.2

/-- Build an element of `TraceClass H` from an operator and its trace-class witness.  A dedicated
constructor, rather than the anonymous `⟨T, hT⟩`, because `TraceClass H` is deliberately a plain
(semireducible) `def` (see above); this definition's own elaboration unfolds it at full
transparency, so the anonymous-constructor ambiguity that a *usage* site would hit does not arise
here. -/
def ofOperator (T : B(H)) (hT : IsTraceClass T) : TraceClass H := ⟨T, hT⟩

@[simp] theorem ofOperator_coe (T : B(H)) (hT : IsTraceClass T) : (ofOperator T hT).1 = T := rfl

/-- **The trace norm as an `AddGroupNorm`** on the trace-class submodule: nonnegativity, the
triangle inequality (`traceNorm_add_le`), invariance under negation, and the zero-detection
property (via `opNorm_le_traceNorm`) are all already proved. -/
noncomputable def traceClassAddGroupNorm : AddGroupNorm (TraceClass H) where
  toFun T := traceNorm T.1 (isTraceClass_coe T)
  map_zero' := traceNorm_zero
  neg' T := traceNorm_neg (isTraceClass_coe T) (isTraceClass_coe (-T))
  add_le' T T' := traceNorm_add_le (isTraceClass_coe T) (isTraceClass_coe T')
    (isTraceClass_coe (T + T'))
  eq_zero_of_map_eq_zero' T hT0 := by
    have hop : ‖T.1‖ ≤ traceNorm T.1 (isTraceClass_coe T) :=
      opNorm_le_traceNorm (isTraceClass_coe T)
    rw [hT0] at hop
    have : T.1 = 0 := norm_le_zero_iff.mp hop
    exact Subtype.ext this

/-- **The trace-class Banach space's `NormedAddCommGroup` instance**, with norm `traceNorm`. -/
noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (TraceClass H) :=
  AddGroupNorm.toNormedAddCommGroup traceClassAddGroupNorm

theorem norm_eq_traceNorm (T : TraceClass H) :
    ‖T‖ = traceNorm T.1 (isTraceClass_coe T) := rfl

/-- **The trace-class Banach space's `NormedSpace ℂ` instance**: scalar multiplication scales the
trace norm exactly, by `traceNorm_smul`. -/
noncomputable instance instNormedSpace : NormedSpace ℂ (TraceClass H) where
  norm_smul_le c T := by
    rw [norm_eq_traceNorm, norm_eq_traceNorm]
    have hEq : ((c • T : TraceClass H)).1 = c • T.1 := rfl
    have h := traceNorm_transport hEq (isTraceClass_coe (c • T))
    rw [h]
    exact le_of_eq (traceNorm_smul c (isTraceClass_coe T))

end TraceClass

end OperatorAlgebra
