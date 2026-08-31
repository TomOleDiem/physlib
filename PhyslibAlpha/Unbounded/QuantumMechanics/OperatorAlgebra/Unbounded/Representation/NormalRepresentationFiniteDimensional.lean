/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Representation.NormalRepresentation
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.States.DensityOperator
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.WStarAlgebra.FiniteDimensional
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.VectorState

/-!
# The finite-dimensional normal representation of `B(H)`

This module closes the finite-dimensional instance of the normal-representation bridge.  The
representation is the identity action of `B(H)` on `H`; its vector states are normal because every
state is continuous for the finite-dimensional weak-star topology.  Consequently the general
normal-PVM and affiliated-operator API can be used without supplying a normality certificate at
each call site.

The analogous theorem in infinite dimension is deliberately not asserted here: it is the theorem
that identifies the normal functionals on `B(H)` with trace-class operators.
-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra InnerProductSpace
open OperatorAlgebra

noncomputable section

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

namespace FiniteDimensionalNormalRepresentation

/-- The identity representation of the bounded operators on a finite-dimensional Hilbert space. -/
def boundedOperators : Representation (B(H)) H :=
  StarAlgHom.id ℂ B(H)

/--
The vector-state normality certificate for the identity representation.

The `apply` field is definitional for the identity representation; the substantive continuity
statement is supplied by `NormalState.ofStateFiniteDimensional`.
-/
noncomputable def vectorStateCertificate :
    NormalPVM.NormalVectorStateCertificate (boundedOperators (H := H)) where
  state := fun x hx => NormalState.ofStateFiniteDimensional (vectorState x hx)
  apply := by
    intro x hx a
    change (NormalState.ofStateFiniteDimensional (vectorState x hx)).toState a = _
    change (vectorState x hx) a = _
    rfl

/-! In finite dimension the chosen predual is `StrongDual ℂ B(H)`.  The following explicit
matrix-coefficient certificate is the finite-dimensional prototype of the trace-class theorem:
in infinite dimension the same formula is represented by a trace-class rank-one operator. -/

/-- The identity representation's matrix coefficients are elements of the chosen finite-dimensional
predual. -/
noncomputable def predualMatrixCoefficientCertificate :
    NormalPVM.PredualMatrixCoefficientCertificate (boundedOperators (H := H)) where
  coefficient := fun x y =>
    (innerSL ℂ y).comp ((ContinuousLinearMap.apply ℂ H) x)
  apply := by
    intro x y a
    change (WStarAlgebra.predualPairing
      ((innerSL ℂ y).comp ((ContinuousLinearMap.apply ℂ H) x)) a) =
      ⟪y, a x⟫_ℂ
    rw [WStarAlgebra.predualPairing_apply,
      finiteDimensionalWStar_toDual_apply]
    rfl

lemma predualMatrixCoefficientCertificate_apply (x y : H) (a : B(H)) :
    WStarAlgebra.predualPairing
        ((predualMatrixCoefficientCertificate (H := H)).coefficient x y) a =
      ⟪y, a x⟫_ℂ := by
  exact (predualMatrixCoefficientCertificate (H := H)).apply x y a

lemma predualPVM_isWOTCountablyAdditive {X : Type*} [MeasurableSpace X]
    (E : PredualPVM X (B(H))) :
    NormalPVM.IsWOTCountablyAdditive E.toNormalPVM (boundedOperators (H := H)) :=
  (predualMatrixCoefficientCertificate (H := H)).isWOTCountablyAdditive E

@[simp]
lemma vectorStateCertificate_state_toState (x : H) (hx : ‖x‖ = 1) :
    ((vectorStateCertificate (H := H)).state x hx).toState = vectorState x hx := by
  rfl

/-- The faithful normal real-PVM bridge for the identity representation of `B(H)`. -/
noncomputable def affiliationBridge :
    FaithfulNormalAffiliationBridge (A := B(H)) (H := H) :=
  NormalAffiliationBridge.ofFaithfulNormalVectorStateCertificate
    (boundedOperators (H := H)) (vectorStateCertificate (H := H)) (by
      intro a b h
      change a = b at h
      exact h)

/--
The faithful normal complex-PVM bridge for the identity representation of `B(H)`.

This is the entry point for normal affiliated operators with complex spectrum.  Its real-valued
restriction is `affiliationBridge`.
-/
noncomputable def operatorAffiliationBridge :
    FaithfulNormalOperatorAffiliationBridge (A := B(H)) (H := H) :=
  NormalOperatorAffiliationBridge.ofFaithfulNormalVectorStateCertificate
    (boundedOperators (H := H)) (vectorStateCertificate (H := H)) (by
      intro a b h
      change a = b at h
      exact h)

/-- A finite-dimensional density operator, viewed as a normal state. -/
noncomputable def densityOperatorNormalState (ρ : DensityOperator H) : NormalState (B(H)) :=
  NormalState.ofStateFiniteDimensional
    (DensityOperator.toState ρ
      (densityOperatorStateCertificate_of_finiteDimensional ρ))

@[simp]
lemma densityOperatorNormalState_apply (ρ : DensityOperator H) (a : B(H)) :
    densityOperatorNormalState ρ a = ρ.toStateFun a := by
  rfl

end FiniteDimensionalNormalRepresentation

end OperatorAlgebra
