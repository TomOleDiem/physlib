/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OneParameterSubgroups.Matrix
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!

# Stone's theorem, finite-dimensional form

## i. Overview

This file characterizes continuous homomorphisms from `Multiplicative ℝ` into the complex unitary
group. Their exponential generators are precisely the anti-Hermitian matrices. Equivalently, after
multiplication by `i`, they admit a unique Hermitian generator `H` in the representation
`U(t) = exp (-itH)`.

Together with `ofHermitian` (the converse: every Hermitian matrix genuinely generates such a
subgroup), this is **Stone's theorem, finite-dimensional form**: continuous one-parameter unitary
groups correspond bijectively to Hermitian generators (`stoneEquiv`) -- the algebraic heart of why
a Hermitian Hamiltonian generates unitary time evolution, specialized to finite-dimensional
(e.g. finite-level/qubit) quantum systems. The pure Banach-algebra/matrix infrastructure this is
built from lives in `Physlib.Mathematics.OneParameterSubgroups`.

## ii. Key results

Definitions:
* `Matrix.UnitaryOneParameterSubgroup`: Continuous one-parameter subgroups of the complex unitary
    group.
* `Matrix.UnitaryOneParameterSubgroup.ofHermitian`: The converse direction -- every Hermitian
    matrix generates a genuine continuous unitary one-parameter subgroup.
* `Matrix.UnitaryOneParameterSubgroup.stoneEquiv`: Stone's theorem, finite-dimensional form, as a
    bijection between the unitary one-parameter subgroups and the Hermitian matrices.

Theorems:
* `Matrix.UnitaryOneParameterSubgroup.existsUnique_antiHermitian_generator`: Existence and
    uniqueness in the anti-Hermitian convention.
* `Matrix.UnitaryOneParameterSubgroup.existsUnique_hermitian_generator`: The equivalent Hermitian
    formulation `U(t) = exp (-itH)`.

## iii. Table of contents

- A. Anti-Hermitian and Hermitian generators
- B. The converse direction: from a generator to a subgroup

## iv. References

* M. H. Stone, *Linear Transformations in Hilbert Space III. Operational Methods and Group Theory*,
  Proc. Natl. Acad. Sci. 18 (1932), 172-175.

-/

@[expose] public section

open Matrix

noncomputable section

/-- A matrix is anti-Hermitian when its conjugate transpose is its negation. -/
def _root_.Matrix.IsAntiHermitian {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) : Prop := star A = -A

namespace Matrix

/-- A continuous one-parameter subgroup of the unitary group. -/
abbrev UnitaryOneParameterSubgroup (n : ℕ) :=
  ContinuousMonoidHom (Multiplicative ℝ) (Matrix.unitaryGroup (Fin n) ℂ)

namespace UnitaryOneParameterSubgroup

variable {n : ℕ}

/-!

## A. Anti-Hermitian and Hermitian generators

-/

/-- The value of a unitary one-parameter subgroup as a matrix. -/
def value (U : Matrix.UnitaryOneParameterSubgroup n) (t : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  U (.ofAdd t)

@[simp] theorem value_zero (U : Matrix.UnitaryOneParameterSubgroup n) : value U 0 = 1 := by
  simp [value]

@[simp] theorem value_add (U : Matrix.UnitaryOneParameterSubgroup n) (s t : ℝ) :
    value U (s + t) = value U s * value U t := by
  exact congrArg Subtype.val (map_mul U (.ofAdd s) (.ofAdd t))

/-- Forget that the values are unitary, retaining the bundled homomorphism into matrix units. -/
def toMatrix (U : Matrix.UnitaryOneParameterSubgroup n) : Matrix.OneParameterSubgroup n where
  toMonoidHom := Unitary.toUnits.comp U.toMonoidHom
  continuous_toFun := by
    rw [Units.continuous_iff]
    constructor
    · exact continuous_subtype_val.comp (map_continuous U)
    · exact continuous_star.comp (continuous_subtype_val.comp (map_continuous U))

@[simp] theorem toMatrix_value (U : Matrix.UnitaryOneParameterSubgroup n) (t : ℝ) :
    Matrix.OneParameterSubgroup.value U.toMatrix t = value U t := rfl

theorem star_value_neg (U : Matrix.UnitaryOneParameterSubgroup n) (t : ℝ) :
    star (value U (-t)) = value U t := by
  exact left_inv_eq_right_inv
    (Matrix.mem_unitaryGroup_iff'.mp (U (.ofAdd (-t))).property)
    (by rw [← value_add, neg_add_cancel, value_zero])

/-- The generator of a unitary one-parameter subgroup is anti-Hermitian. -/
theorem generator_isAntiHermitian (U : Matrix.UnitaryOneParameterSubgroup n)
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : ∀ t : ℝ, value U t = NormedSpace.exp ((t : ℂ) • A)) :
    A.IsAntiHermitian := by
  have hnegstar : ∀ t : ℝ,
      Matrix.OneParameterSubgroup.value U.toMatrix t =
        NormedSpace.exp ((t : ℂ) • (-star A)) := by
    intro t
    calc
      Matrix.OneParameterSubgroup.value U.toMatrix t = value U t := toMatrix_value U t
      _ = star (value U (-t)) := (U.star_value_neg t).symm
      _ = star (NormedSpace.exp (((-t : ℝ) : ℂ) • A)) := by rw [hA (-t)]
      _ = NormedSpace.exp (star (((-t : ℝ) : ℂ) • A)) := NormedSpace.star_exp _
      _ = NormedSpace.exp ((t : ℂ) • (-star A)) := by
        congr 1
        simp [star_smul]
  have hgen : A = -star A := Matrix.OneParameterSubgroup.generator_eq
    (U := U.toMatrix) (fun t => (toMatrix_value U t).trans (hA t)) hnegstar
  rw [Matrix.IsAntiHermitian]
  simpa using (congrArg Neg.neg hgen).symm

/-- Exponentiating an anti-Hermitian matrix produces a unitary matrix. -/
theorem exp_mem_unitaryGroup {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsAntiHermitian) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • A) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', NormedSpace.star_exp]
  have hstar : star ((t : ℂ) • A) = -((t : ℂ) • A) := by
    rw [star_smul, Complex.star_def, Complex.conj_ofReal, hA]
    module
  rw [hstar, Matrix.exp_neg]
  exact Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp ((t : ℂ) • A)))

/-- A unitary one-parameter subgroup has a unique anti-Hermitian generator. -/
theorem existsUnique_antiHermitian_generator (U : Matrix.UnitaryOneParameterSubgroup n) :
    ∃! A : Matrix (Fin n) (Fin n) ℂ,
      A.IsAntiHermitian ∧ ∀ t : ℝ, value U t = NormedSpace.exp ((t : ℂ) • A) := by
  obtain ⟨A, hA, hA_unique⟩ := Matrix.OneParameterSubgroup.existsUnique_generator U.toMatrix
  have hA' (t : ℝ) : value U t = NormedSpace.exp ((t : ℂ) • A) :=
    (toMatrix_value U t).symm.trans (hA t)
  refine ⟨A, ⟨U.generator_isAntiHermitian hA', hA'⟩, ?_⟩
  intro B hB
  apply hA_unique B
  intro t
  exact (toMatrix_value U t).trans (hB.2 t)

/-- Multiplication by `i` turns an anti-Hermitian matrix into a Hermitian matrix. -/
theorem isSelfAdjoint_I_smul {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsAntiHermitian) : IsSelfAdjoint (Complex.I • A) := by
  rw [isSelfAdjoint_iff, star_smul, Complex.star_def, Complex.conj_I, hA]
  module

/-- A unitary one-parameter subgroup has a unique Hermitian generator `H` satisfying
`U(t) = exp (-itH)`. -/
theorem existsUnique_hermitian_generator (U : Matrix.UnitaryOneParameterSubgroup n) :
    ∃! H : Matrix (Fin n) (Fin n) ℂ,
      IsSelfAdjoint H ∧
        ∀ t : ℝ, value U t = NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) := by
  obtain ⟨A, ⟨hAanti, hA⟩, hA_unique⟩ := U.existsUnique_antiHermitian_generator
  let H := Complex.I • A
  refine ⟨H, ⟨isSelfAdjoint_I_smul hAanti, ?_⟩, ?_⟩
  · intro t
    calc
      value U t = NormedSpace.exp ((t : ℂ) • A) := hA t
      _ = NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) := by
        dsimp [H]
        rw [smul_smul]
        apply congrArg NormedSpace.exp
        apply congrArg (fun z : ℂ => z • A)
        rw [mul_assoc, Complex.I_mul_I]
        simp
  · intro K hK
    have hKrep : ∀ t : ℝ,
        value U t = NormedSpace.exp ((t : ℂ) • ((-Complex.I) • K)) := by
      intro t
      rw [hK.2 t]
      congr 1
      rw [smul_smul]
      congr 1
      ring
    have hKA : (-Complex.I) • K = A := hA_unique ((-Complex.I) • K) ⟨by
      rw [Matrix.IsAntiHermitian, star_smul, hK.1.star_eq]
      simp, hKrep⟩
    calc
      K = Complex.I • ((-Complex.I) • K) := by rw [smul_smul]; simp
      _ = Complex.I • A := by rw [hKA]
      _ = H := rfl

/-!

## B. The converse direction: from a generator to a subgroup

`existsUnique_antiHermitian_generator`/`existsUnique_hermitian_generator` extract a generator
*from* a given continuous unitary one-parameter subgroup. This section builds the subgroup *from*
a given generator, completing the finite-dimensional Stone correspondence in both directions.

-/

/-- The plain matrix-valued exponential map `t ↦ exp (tA)`, as a monoid hom out of
`Multiplicative ℝ` -- before restricting the codomain to the unitary group. -/
def expMonoidHom (A : Matrix (Fin n) (Fin n) ℂ) :
    Multiplicative ℝ →* Matrix (Fin n) (Fin n) ℂ where
  toFun t := NormedSpace.exp (((Multiplicative.toAdd t : ℝ) : ℂ) • A)
  map_one' := by simp
  map_mul' s t := by
    have hcomm : Commute (((Multiplicative.toAdd s : ℝ) : ℂ) • A)
        (((Multiplicative.toAdd t : ℝ) : ℂ) • A) :=
      ((Commute.refl A).smul_left _).smul_right _
    change NormedSpace.exp (((Multiplicative.toAdd (s * t) : ℝ) : ℂ) • A) =
      NormedSpace.exp (((Multiplicative.toAdd s : ℝ) : ℂ) • A) *
        NormedSpace.exp (((Multiplicative.toAdd t : ℝ) : ℂ) • A)
    -- `Matrix.exp_add_of_commute` (unlike the generic `NormedSpace.exp_add_of_commute`) hides its
    -- norm requirement inside the proof, so it applies here without any local norm instance.
    rw [← Matrix.exp_add_of_commute _ _ hcomm, toAdd_mul]
    push_cast
    rw [add_smul]

-- `NormedSpace.exp_continuous` needs *some* `NormedRing` instance on `Matrix (Fin n) (Fin n) ℂ`
-- to typecheck, but Mathlib deliberately leaves none canonical (see `Matrix.Normed`'s docstring).
-- `Norms.Operator`'s scoped instances are the ones `Matrix.exp_add_of_commute` etc. use
-- internally for exactly this reason; opening them here keeps every instance in this proof
-- consistent with the ambient (norm-independent) topology on matrices.
open scoped Norms.Operator in
theorem continuous_expMonoidHom (A : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (expMonoidHom A) := by
  change Continuous
    (fun t : Multiplicative ℝ => NormedSpace.exp (((Multiplicative.toAdd t : ℝ) : ℂ) • A))
  fun_prop

/-- **Every anti-Hermitian matrix generates a genuine continuous unitary one-parameter
subgroup**, `t ↦ exp (tA)`. -/
def ofAntiHermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsAntiHermitian) :
    Matrix.UnitaryOneParameterSubgroup n where
  toMonoidHom := (expMonoidHom A).codRestrict (Matrix.unitaryGroup (Fin n) ℂ)
    fun t => exp_mem_unitaryGroup hA (Multiplicative.toAdd t)
  continuous_toFun := Continuous.subtype_mk (continuous_expMonoidHom A) _

@[simp] theorem value_ofAntiHermitian {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsAntiHermitian)
    (t : ℝ) : value (ofAntiHermitian hA) t = NormedSpace.exp ((t : ℂ) • A) := by
  change (expMonoidHom A) (.ofAdd t) = _
  simp [expMonoidHom]

/-- **Every Hermitian matrix generates a genuine continuous unitary one-parameter subgroup**,
`t ↦ exp (-itH)` -- the converse of `existsUnique_hermitian_generator`. -/
def ofHermitian {H : Matrix (Fin n) (Fin n) ℂ} (hH : IsSelfAdjoint H) :
    Matrix.UnitaryOneParameterSubgroup n :=
  ofAntiHermitian (A := (-Complex.I) • H) (by
    rw [Matrix.IsAntiHermitian, star_smul, Complex.star_def, map_neg, Complex.conj_I, hH.star_eq]
    module)

theorem value_ofHermitian {H : Matrix (Fin n) (Fin n) ℂ} (hH : IsSelfAdjoint H) (t : ℝ) :
    value (ofHermitian hH) t = NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) := by
  change NormedSpace.exp ((t : ℂ) • ((-Complex.I) • H)) = _
  rw [smul_smul]
  congr 1
  ring_nf

/-- **Stone's theorem, finite-dimensional form.** Continuous one-parameter subgroups of the
`n × n` unitary group correspond bijectively to Hermitian `n × n` matrices, via
`H ↦ (t ↦ exp (-itH))` and its inverse `U ↦ ` the unique Hermitian generator of `U`. -/
noncomputable def stoneEquiv (n : ℕ) :
    Matrix.UnitaryOneParameterSubgroup n ≃ {H : Matrix (Fin n) (Fin n) ℂ // IsSelfAdjoint H} where
  toFun U := ⟨U.existsUnique_hermitian_generator.choose,
    U.existsUnique_hermitian_generator.choose_spec.1.1⟩
  invFun H := ofHermitian H.2
  left_inv U := by
    apply DFunLike.ext
    intro t
    induction t using Multiplicative.rec with
    | ofAdd a =>
      apply Subtype.ext
      change value (ofHermitian _) a = value U a
      rw [value_ofHermitian, ← U.existsUnique_hermitian_generator.choose_spec.1.2]
  right_inv H := by
    apply Subtype.ext
    exact ((ofHermitian H.2).existsUnique_hermitian_generator.choose_spec.2 H.1
      ⟨H.2, value_ofHermitian H.2⟩).symm

end UnitaryOneParameterSubgroup

end Matrix
