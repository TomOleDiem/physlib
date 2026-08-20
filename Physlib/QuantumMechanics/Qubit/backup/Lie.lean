/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Qubit.backup.PauliVector
public import Mathlib.Algebra.Lie.OfAssociative

/-!

# The traceless sector as `su(2)`

The Pauli commutator `⁅σ u, σ v⁆ = 2i • σ (u ⨯₃ v)` (`Qubit.σ_commutator`) exhibits the traceless
observable sector, after the conventional normalization `τ v = -i/2 • σ v`, as the Lie algebra
`su(2)`: `τ` sends `u ⨯₃ v` to `⁅τ u, τ v⁆` on the nose, no leftover scalar factor, and every
`τ v` is skew-adjoint.

This is proved as a genuine isomorphism, not just a bracket-compatible map:

`ℝ³ with cross product ≃⁅ℝ⁆ su(2) := skew-adjoint traceless qubit generators`

is `Qubit.τLieEquiv`, a `LieEquiv` onto `τHom.range` — `τ` bundled as a Lie algebra
homomorphism (`τHom`) plus injectivity (`τ_injective`).

`Fin 3 → ℝ` already carries this Lie ring structure as `Cross.lieRing`
(`Mathlib.LinearAlgebra.CrossProduct`); `A` carries its commutator bracket generically via
`LieRing.ofAssociativeRing`. `τ` is the bridge between them.

This is a *different* notion of representation from the C⋆-algebra representation `A → B(ℋ)`
of `Qubit/Basic.lean`'s ambient algebra: keep the two separate (see `Qubit/todo.md`, §11).

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra Matrix
open Module OperatorAlgebra

namespace Qubit

variable {A : Type*} [OperatorAlgebra A] [QubitAlgebra A]

/-- The `su(2)`-normalized generator associated with a Pauli vector `v`: `τ v = -i/2 • σ v`. -/
noncomputable def τ (v : Fin 3 → ℝ) : A :=
  (-Complex.I / 2) • σ v

/-- Every `τ v` is skew-adjoint. -/
lemma τ_mem_skewAdjoint (v : Fin 3 → ℝ) : (τ v : A) ∈ skewAdjoint A := by
  rw [τ]
  refine (isSelfAdjoint_σ v).smul_mem_skewAdjoint ?_
  rw [skewAdjoint.mem_iff]
  simp; ring

/-- `τ` exactly intertwines the cross product with the commutator bracket: this is the
identification `ℝ³ with cross product ≃ su(2) ≃ skew-adjoint traceless qubit generators`. -/
lemma τ_mul_sub_mul (u v : Fin 3 → ℝ) :
    (τ u : A) * τ v - τ v * τ u = τ (u ⨯₃ v) := by
  simp only [τ, smul_mul_smul_comm, ← smul_sub, σ_commutator, smul_smul]
  congr 1
  ring_nf
  rw [Complex.I_pow_three]
  ring

/-! ## `τ` is a Lie algebra isomorphism onto its range

The intertwining identity `τ_mul_sub_mul` above only says `τ` is a Lie ring homomorphism; an
isomorphism additionally needs `τ` to be injective (surjectivity onto its own range is
tautological). This section supplies that, and packages the result as a genuine
`LieEquiv ℝ (Fin 3 → ℝ) τHom.range` — `ℝ³` (with the cross product) *is* `su(2)`, realized
concretely as the traceless skew-adjoint generators, not just related to it by an unpackaged
bracket-compatible map.
-/

/-- `τ` is additive. -/
lemma τ_add (u v : Fin 3 → ℝ) : (τ (u + v) : A) = τ u + τ v := by
  rw [τ, τ, τ, σ_add, smul_add]

/-- `τ` is ℝ-homogeneous. -/
lemma τ_smul (r : ℝ) (v : Fin 3 → ℝ) : (τ (r • v) : A) = r • τ v := by
  rw [τ, τ, σ_smul, real_smul_eq_ofReal_smul, real_smul_eq_ofReal_smul, smul_smul, smul_smul,
    mul_comm]

/-- The three generators are linearly independent over `ℂ`: a sub-family of the basis
`QubitAlgebra.pauliBasis`. -/
lemma gen_linearIndependent :
    LinearIndependent ℂ (fun i => (QubitAlgebra.gen (A := A) i : A)) := by
  have h := (QubitAlgebra.pauliBasis (A := A)).linearIndependent
  rw [QubitAlgebra.pauliBasis_eq] at h
  exact h.comp Fin.succ (Fin.succ_injective 3)

/-- `σ` is injective: it is exactly the coordinates against the (linearly independent) Pauli
generators. -/
lemma σ_eq_zero_iff (v : Fin 3 → ℝ) : (σ v : A) = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hg := Fintype.linearIndependent_iff.mp (gen_linearIndependent (A := A))
      (fun i => (v i : ℂ)) (by rw [σ] at h; exact h)
    funext i
    exact_mod_cast hg i
  · rintro rfl
    simp [σ]

/-- `τ` is injective: `su(2)` really is `3`-dimensional, not a further quotient of it. -/
lemma τ_injective : Function.Injective (τ (A := A)) := by
  have hne : (-Complex.I / 2 : ℂ) ≠ 0 := by simp [Complex.ext_iff]
  intro u v huv
  rw [τ, τ] at huv
  have hσ : (σ u : A) = σ v := smul_right_injective A hne huv
  have h0 : (σ (u - v) : A) = 0 := by
    rw [sub_eq_add_neg, σ_add, σ_neg, hσ, add_neg_cancel]
  exact sub_eq_zero.mp ((σ_eq_zero_iff (u - v)).mp h0)

attribute [local instance] Cross.lieRing
attribute [local instance] LieRing.ofAssociativeRing

/-- `Fin 3 → ℝ`, with the cross product as its bracket, is a Lie *algebra* over `ℝ`, not just a
Lie ring: the cross product is `ℝ`-bilinear, `crossProduct` already being an `ℝ`-linear map in
each argument. -/
noncomputable instance : LieAlgebra ℝ (Fin 3 → ℝ) where
  lie_smul r x y := (crossProduct x).map_smul r y

/-- `τ`, bundled as a genuine morphism of Lie algebras: `ℝ`-linear (`τ_add`/`τ_smul`) and
bracket-compatible (`τ_mul_sub_mul`, using that `⁅u, v⁆ = u ⨯₃ v` on `Fin 3 → ℝ`
(`Cross.lieRing`) and `⁅a, b⁆ = a * b - b * a` on `A` (`LieRing.ofAssociativeRing`)). -/
noncomputable def τHom : (Fin 3 → ℝ) →ₗ⁅ℝ⁆ A where
  toFun := τ
  map_add' := τ_add
  map_smul' r v := by simp [τ_smul r v]
  map_lie' {u v} := (τ_mul_sub_mul u v).symm

/-- **`ℝ³` (with the cross product) is `su(2)`**: `τHom` is injective, hence a Lie algebra
isomorphism onto its range — the traceless skew-adjoint qubit generators. This is the genuine
isomorphism promised by the module docstring, not just the bracket-intertwining fact
`τ_mul_sub_mul` on its own. -/
noncomputable def τLieEquiv : (Fin 3 → ℝ) ≃ₗ⁅ℝ⁆ (τHom (A := A)).range :=
  LieEquiv.ofInjective τHom τ_injective

end Qubit
