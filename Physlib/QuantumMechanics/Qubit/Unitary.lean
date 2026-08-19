/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Qubit.Observable
public import Physlib.Mathematics.OperatorAlgebra.Unitary
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!

# Unitary conjugation acts on the Bloch ball by rotations

A unitary `U` acts on observables by `a ↦ U a U⋆` (`OperatorAlgebra.Unitary.automorphism`).
Conjugation fixes `1` and, since it is a ⋆-algebra automorphism, preserves self-adjointness — so
it carries the Pauli-vector sector `{σ v}` to itself, inducing a real-linear map `R U` on Bloch
vectors characterized by `U σ(v) U⋆ = σ(R U v)`.

`R U` is an isometry of `Fin 3 → ℝ` (norm-preserving), and `U ↦ R U` is compatible with
multiplication: `R (U * V) = (R U).comp (R V)`, matching how `Unitary.automorphism (U * V) =
Unitary.automorphism U ∘ Unitary.automorphism V` (verified from `Unitary.conjStarAlgAut`'s
`map_mul'`). This realizes the adjoint action `SU(2) → SO(3)`, though landing `R U` inside
`Matrix.specialOrthogonalGroup (Fin 3) ℝ` (fixing a basis, checking the determinant) and
identifying the kernel with the scalar unitaries (the double cover, kernel `{±1}`) are left for
later — see `Qubit/todo.md`.

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra
open Module OperatorAlgebra

namespace Qubit

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [QubitAlgebra A]

/-- The real-linear map on Bloch vectors induced by unitary conjugation, characterized by
`Qubit.coe_R`: `U σ(v) U⋆ = σ(R U v)`. -/
@[sorryful]
noncomputable def R (U : Unitary A) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
  sorry

TODO "Construct `Qubit.R`. First show conjugation fixes the scalar part and preserves the
  traceless sector: `Unitary.automorphism U (σ v)` is self-adjoint (`Qubit.isSelfAdjoint_σ` and
  that ⋆-algebra automorphisms preserve `IsSelfAdjoint`), and has zero `pauliBasis` scalar
  coefficient (expand `U σ(v) U⋆` and use `QubitAlgebra.gen_mul_cyc`/`gen_sq`-style relations,
  or trace/`Observable`-coordinate reasoning once available), so `Qubit.observableEquiv` gives it
  a genuine Bloch vector; take `R U v` to be that vector. Linearity in `v` follows from linearity
  of `σ` and of conjugation."

/-- The defining property of `Qubit.R`: `U σ(v) U⋆ = σ(R U v)`. -/
@[sorryful]
theorem coe_R (U : Unitary A) (v : Fin 3 → ℝ) :
    (U : A) * σ v * star (U : A) = σ (R U v) :=
  sorry

TODO "Prove `Qubit.coe_R` directly from the construction of `Qubit.R` (it should essentially be
  definitional once `R` is built from `Unitary.automorphism`/`Unitary.observable` via
  `Qubit.observableEquiv`, using `OperatorAlgebra.Unitary.automorphism_apply`)."

/-- `R U` is an isometry of Bloch vectors. -/
@[sorryful]
theorem norm_R_apply (U : Unitary A) (v : Fin 3 → ℝ) :
    ‖(WithLp.toLp 2 (R U v) : EuclideanSpace ℝ (Fin 3))‖ =
      ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin 3))‖ :=
  sorry

TODO "Prove `Qubit.norm_R_apply` from `Qubit.coe_R` and `Qubit.σ_sq`: `‖v‖² • 1 = σ v * σ v = U⋆
  (U σ v U⋆)(U σ v U⋆) U = U⋆ σ(R U v) σ(R U v) U = U⋆ (‖R U v‖² • 1) U = ‖R U v‖² • 1` (using
  `U⋆ U = 1`), then cancel and take square roots."

/-- `R` is compatible with multiplication, matching `Unitary.automorphism (U * V) =
Unitary.automorphism U ∘ Unitary.automorphism V`. -/
@[sorryful]
theorem R_comp (U V : Unitary A) : R (U * V) = (R U).comp (R V) :=
  sorry

TODO "Prove `Qubit.R_comp` from `Qubit.coe_R` applied twice and
  `OperatorAlgebra.Unitary.automorphism_apply`'s multiplicativity (`Unitary.conjStarAlgAut`'s
  `map_mul'`: `(U * V) * a * star (U * V) = U * (V * a * star V) * star U`), plus injectivity of
  `Qubit.σ` (from `QubitAlgebra.pauliBasis`) to cancel it from both sides."

/-- The identity unitary induces the identity map on Bloch vectors. -/
@[sorryful]
theorem R_one : R (A := A) 1 = LinearMap.id :=
  sorry

TODO "Prove `Qubit.R_one` from `Qubit.coe_R` at `U = 1` (`1 * σ v * star 1 = σ v`) and
  injectivity of `Qubit.σ`."

end Qubit
