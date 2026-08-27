/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.HilbertSpace
public import Physlib.QuantumMechanics.OperatorAlgebra.Observables.Lie
public import Physlib.Mathematics.OneParameterSubgroups.Unitary
public import Physlib.Mathematics.OperatorAlgebra.Dynamics
public import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Automorphisms of the bounded operators

Reversible transformations of a quantum system act on its observable algebra by
⋆-automorphisms.

For a complex Hilbert space `H`, every ⋆-automorphism of `B(H)` is implemented by
unitary conjugation:
  `A ↦ U A U⋆`.

Two unitaries implement the same transformation exactly when they differ by a
scalar phase. Consequently,
  `Aut⋆(B(H)) ≅ U(H) / U(1) ≅ PU(H)`,
the projective unitary group.

For Hamiltonian dynamics, this projective ambiguity corresponds to
the freedom to shift a Hamiltonian by a scalar multiple of the identity.

A norm-continuous unitary one-parameter group `U` also acts on `B(H)` by conjugation,
`αₜ(a) = U(t) a U(t)⋆`, an `AutomorphismGroup (B(H))`; this action satisfies (and is the unique
solution of) the Heisenberg-type equation `d/dt αₜ(a) = ⁅αₜ(a), i • generator⁆`, where `⁅·,·⁆` is
the ordinary ring commutator `⁅x, y⁆ = x*y - y*x`. This is the generic, Hamiltonian-independent
content behind Hamiltonian dynamics (`Hamiltonian.lean` merely specializes `U` to
`unitaryEvolution ℏ H`).
-/

@[expose] public section

/-! ## Star automorphisms act on observables

A ⋆-automorphism `β : A ≃⋆ₐ[ℂ] A` restricts to a bijection of the self-adjoint elements: a
⋆-automorphism preserves `star`, so it takes observables to observables, and being an
automorphism (not just a homomorphism) it does so invertibly. This is the algebraic shadow of
"changing the representation of a system doesn't change which of its elements are measurable
quantities".

This section is declared in the root `StarAlgEquiv` namespace (rather than nested under
`OperatorAlgebra`), so that `β.observable` etc. resolve as dot notation on `β : A ≃⋆ₐ[ℂ] A`. -/

section StarAlgEquivObservable

open OperatorAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- A ⋆-automorphism `β` acts on observables by `a ↦ β a`. Self-adjointness of `β a` follows from
`star (β a) = β (star a) = β a`, using that `β` preserves `star` (`map_star`) and `a` is
self-adjoint. -/
def StarAlgEquiv.observable (β : A ≃⋆ₐ[ℂ] A) (a : Observable A) : Observable A :=
  ⟨β (a : A), by
    show star (β (a : A)) = β (a : A)
    rw [← map_star, a.2]⟩

/-- Unfolds `StarAlgEquiv.observable` to its underlying algebra element. -/
@[simp]
lemma StarAlgEquiv.observable_coe (β : A ≃⋆ₐ[ℂ] A) (a : Observable A) :
    (β.observable a : A) = β (a : A) := rfl

/-- The identity automorphism acts trivially on observables. -/
@[simp]
lemma StarAlgEquiv.refl_observable :
    (StarAlgEquiv.refl (R := ℂ) (A := A)).observable = id := by
  funext a
  exact Subtype.ext rfl

/-- Composing automorphisms composes their action on observables (in the same order as
`StarAlgEquiv.trans`: `(β.trans γ) a = γ (β a)`, so `β` acts first). -/
@[simp]
lemma StarAlgEquiv.trans_observable (β γ : A ≃⋆ₐ[ℂ] A) (a : Observable A) :
    (β.trans γ).observable a = γ.observable (β.observable a) :=
  Subtype.ext (StarAlgEquiv.trans_apply β γ (a : A))

/-- Undoing `β.observable` by `β.symm.observable` recovers the original observable. -/
@[simp]
lemma StarAlgEquiv.symm_observable_observable (β : A ≃⋆ₐ[ℂ] A) (a : Observable A) :
    β.symm.observable (β.observable a) = a :=
  Subtype.ext (β.symm_apply_apply (a : A))

/-- Applying `β.observable` after `β.symm.observable` recovers the original observable. -/
@[simp]
lemma StarAlgEquiv.observable_symm_observable (β : A ≃⋆ₐ[ℂ] A) (a : Observable A) :
    β.observable (β.symm.observable a) = a :=
  Subtype.ext (β.apply_symm_apply (a : A))

/-- `β.observable` preserves the observable Lie bracket: a ⋆-automorphism is in particular a
`ℂ`-linear ring homomorphism, and `Observable.coe_bracket` reduces the bracket to a `ℂ`-scalar
multiple of the ring commutator, which any such homomorphism commutes with. -/
lemma StarAlgEquiv.observable_bracket (β : A ≃⋆ₐ[ℂ] A) (a b : Observable A) :
    β.observable ⁅a, b⁆ = ⁅β.observable a, β.observable b⁆ := by
  apply Subtype.ext
  simp only [observable_coe, Observable.coe_bracket, map_smul, map_sub, map_mul]

end StarAlgEquivObservable

namespace OperatorAlgebra

/-! ## Conjugating an automorphism group by a star automorphism

Changing which ⋆-automorphism `β` is used to identify the algebra with itself changes the
description of a flow `α` by conjugation: `(conj β α) t = β ∘ α t ∘ β⁻¹`. This is the
change-of-coordinates operation needed to compare a flow generated in one representation against
the same physical flow generated in another. -/

section AutomorphismGroupConj

variable {A : Type*} [OperatorAlgebra A]

/-- The automorphism group `α`, viewed through the change of coordinates `β`: at each time,
`(conj β α) t = β ∘ (α t) ∘ β⁻¹`. -/
def AutomorphismGroup.conj (β : A ≃⋆ₐ[ℂ] A) (α : AutomorphismGroup A) : AutomorphismGroup A where
  toFun t := (β.symm.trans (α.toFun t)).trans β
  map_zero_apply a := by
    simp [StarAlgEquiv.trans_apply, α.map_zero_apply]
  map_add_apply s t a := by
    simp only [StarAlgEquiv.trans_apply, α.map_add_apply, β.symm_apply_apply]

/-- Unfolds `AutomorphismGroup.conj` to the concrete conjugation formula
`(conj β α) t a = β (α t (β⁻¹ a))`. -/
@[simp]
lemma AutomorphismGroup.conj_apply (β : A ≃⋆ₐ[ℂ] A) (α : AutomorphismGroup A) (t : ℝ) (a : A) :
    (α.conj β).toFun t a = β (α.toFun t (β.symm a)) := by
  simp [AutomorphismGroup.conj, StarAlgEquiv.trans_apply]

/-- Conjugating by the identity automorphism changes nothing. -/
@[simp]
lemma AutomorphismGroup.conj_refl (α : AutomorphismGroup A) :
    α.conj (StarAlgEquiv.refl (R := ℂ) (A := A)) = α := by
  apply AutomorphismGroup.ext
  intro t a
  simp

/-- Conjugating successively by `β` then `γ` is the same as conjugating once by `β.trans γ`. -/
lemma AutomorphismGroup.conj_conj (α : AutomorphismGroup A) (β γ : A ≃⋆ₐ[ℂ] A) :
    (α.conj β).conj γ = α.conj (β.trans γ) := by
  apply AutomorphismGroup.ext
  intro t a
  simp only [AutomorphismGroup.conj_apply, StarAlgEquiv.trans_apply, StarAlgEquiv.symm_trans_apply]

/-- Conjugating by `β` and then undoing it with `β.symm` recovers the original flow. -/
@[simp]
lemma AutomorphismGroup.conj_symm_conj (α : AutomorphismGroup A) (β : A ≃⋆ₐ[ℂ] A) :
    (α.conj β).conj β.symm = α := by
  apply AutomorphismGroup.ext
  intro t a
  simp

/-- Conjugating by `β.symm` and then undoing it with `β` recovers the original flow. -/
@[simp]
lemma AutomorphismGroup.conj_conj_symm (α : AutomorphismGroup A) (β : A ≃⋆ₐ[ℂ] A) :
    (α.conj β.symm).conj β = α := by
  apply AutomorphismGroup.ext
  intro t a
  simp

end AutomorphismGroupConj

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every ⋆-automorphism of `B(H)` is implemented by unitary conjugation. -/
lemma conjStarAlgAut_surjective :
    Function.Surjective (Unitary.conjStarAlgAut ℂ (B(H))) := by
  intro φ
  obtain ⟨U, hU⟩ :=
    φ.eq_linearIsometryEquivConjStarAlgEquiv
      (NonUnitalStarAlgHom.isometry φ φ.injective).continuous
  refine ⟨Unitary.linearIsometryEquiv.symm U, ?_⟩
  rw [Unitary.conjStarAlgAut_symm_unitaryLinearIsometryEquiv]
  exact hU.symm

/-- Two unitaries implement the same ⋆-automorphism of `B(H)` exactly when they differ by a scalar
phase. -/
lemma conjStarAlgAut_eq_iff (u v : Unitary (B(H))) :
    Unitary.conjStarAlgAut ℂ (B(H)) u =
        Unitary.conjStarAlgAut ℂ (B(H)) v ↔
      ∃ c : unitary ℂ, u = c • v :=
  Unitary.conjStarAlgAut_ext_iff' u v

/-- The projective unitary group of `H`, obtained by quotienting out scalar phases. -/
def ProjectiveUnitary (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] :=
  Unitary (B(H)) ⧸ MonoidHom.ker (Unitary.conjStarAlgAut ℂ (B(H)))

noncomputable instance : Group (ProjectiveUnitary H) := QuotientGroup.Quotient.group _

/-- Reversible transformations of `B(H)` are precisely projective unitaries. -/
noncomputable def projectiveUnitaryEquivStarAlgAut :
    ProjectiveUnitary H ≃* ((B(H)) ≃⋆ₐ[ℂ] (B(H))) :=
  QuotientGroup.quotientKerEquivOfSurjective _ conjStarAlgAut_surjective

/-! ## The automorphism group generated by unitary conjugation -/

namespace UnitaryOneParameterGroup

/-- The automorphism group induced by unitary conjugation: `t ↦ (a ↦ U(t) a U(t)⋆)`. The group
law holds because conjugation is a homomorphism and `U` already satisfies `U(s+t) = U(s)U(t)`. -/
noncomputable def toAutomorphism (U : UnitaryOneParameterGroup H) : AutomorphismGroup (B(H)) where
  toFun t :=
    Unitary.conjStarAlgAut ℂ (B(H))
      (⟨U t, U.mem_unitary t⟩ : unitary (B(H)))
  map_zero_apply a := by
    simp
  map_add_apply s t a := by
    let Us : unitary (B(H)) := ⟨U s, U.mem_unitary s⟩
    let Ut : unitary (B(H)) := ⟨U t, U.mem_unitary t⟩
    let Ust : unitary (B(H)) := ⟨U (s + t), U.mem_unitary (s + t)⟩
    have hU : Ust = Us * Ut := by
      apply Subtype.ext
      exact AddChar.map_add_eq_mul U.toAddChar s t
    change
      (Unitary.conjStarAlgAut ℂ (B(H)) Ust) a =
        ((Unitary.conjStarAlgAut ℂ (B(H)) Us) *
          (Unitary.conjStarAlgAut ℂ (B(H)) Ut)) a
    rw [hU, map_mul]

/-- Unfolds `toAutomorphism` to the concrete conjugation formula. -/
@[simp]
lemma toAutomorphism_apply (U : UnitaryOneParameterGroup H) (t : ℝ) (a : B(H)) :
    (toAutomorphism U).toFun t a = U t * a * star (U t) := by
  rfl

/-! ## Differential characterization -/

/-- The conjugation flow satisfies the Heisenberg equation of motion
`d/dt αₜ(a) = ⁅αₜ(a), i • generator⁆`: apply the product rule to `U(t) a U(t)⋆` using
`U.hasDerivAt`/`U.hasDerivAt_star`, then use `commute_generator` to match terms. -/
lemma hasDerivAt_toAutomorphism (U : UnitaryOneParameterGroup H) (a : B(H)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (toAutomorphism U).toFun s a)
      ⁅(toAutomorphism U).toFun t a, Complex.I • U.generator⁆ t := by
  simp only [toAutomorphism_apply, LieRing.of_associative_ring_bracket]
  have hd := ((U.hasDerivAt t).mul_const a).mul (U.hasDerivAt_star t)
  have hcomm := (U.commute_generator t).smul_left Complex.I
  have heq :
      U t * (-(Complex.I • U.generator)) * a * star (U t) +
          U t * a * (star (U t) * (Complex.I • U.generator)) =
        U t * a * star (U t) * (Complex.I • U.generator) -
          (Complex.I • U.generator) * (U t * a * star (U t)) := by
    rw [show U t * (-(Complex.I • U.generator)) = -((Complex.I • U.generator) * U t) by
      rw [mul_neg, hcomm.eq]]
    noncomm_ring
  rw [← heq]
  exact hd

/-- A function on `ℝ` with everywhere-zero derivative is constant. -/
private lemma const_of_hasDerivAt_zero {f : ℝ → B(H)} (hf : ∀ s, HasDerivAt f 0 s) (t : ℝ) :
    f t = f 0 := by
  apply isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
    (fun s _ => (hf s).differentiableAt.differentiableWithinAt)
  · intro s _
    exact (hf s).deriv
  · exact Set.mem_univ t
  · exact Set.mem_univ 0

/-- Along a solution `α` of the Heisenberg equation, the conjugated path
`s ↦ U(s)⋆ αₛ(a) U(s)` has zero derivative. -/
private lemma hasDerivAt_conj_zero (U : UnitaryOneParameterGroup H)
    (α : ℝ → B(H) → B(H)) (a : B(H))
    (hα : ∀ t, HasDerivAt (fun s => α s a) ⁅α t a, Complex.I • U.generator⁆ t)
    (s : ℝ) :
    HasDerivAt (fun r => star (U r) * α r a * U r) 0 s := by
  simp only [LieRing.of_associative_ring_bracket] at hα
  have hcomm := (U.commute_generator s).smul_left Complex.I
  have hd := ((U.hasDerivAt_star s).mul (hα s)).mul (U.hasDerivAt s)
  have heq :
      ((star (U s) * (Complex.I • U.generator)) * α s a +
          star (U s) *
            (α s a * (Complex.I • U.generator) - (Complex.I • U.generator) * α s a)) * U s +
          star (U s) * α s a * (U s * (-(Complex.I • U.generator))) = 0 := by
    calc
      ((star (U s) * (Complex.I • U.generator)) * α s a +
          star (U s) *
            (α s a * (Complex.I • U.generator) - (Complex.I • U.generator) * α s a)) * U s +
          star (U s) * α s a * (U s * (-(Complex.I • U.generator))) =
        star (U s) * α s a * ((Complex.I • U.generator) * U s - U s * (Complex.I • U.generator)) :=
          by noncomm_ring
      _ = 0 := by rw [hcomm.eq, sub_self, mul_zero]
  rw [← heq]
  exact hd

/-- The conjugation flow is the unique solution of its Heisenberg-type initial-value problem: any
`α` satisfying the same equation and initial condition must agree with it. Proof idea:
`hasDerivAt_conj_zero` says `U(s)⋆ αₛ(a) U(s)` is constant in `s`, so its value at `s = t` (which
unfolds to `U(t)⋆ αₜ(a) U(t)`) equals its value at `s = 0` (which is `a`, from `α₀ = id`);
conjugating that equation back by `U(t)` gives `αₜ(a) = U(t) a U(t)⋆`. -/
lemma toAutomorphism_unique (U : UnitaryOneParameterGroup H)
    (α : ℝ → B(H) → B(H)) (hα0 : α 0 = id)
    (hα : ∀ a t, HasDerivAt (fun s : ℝ => α s a) ⁅α t a, Complex.I • U.generator⁆ t) :
    α = fun t a => (toAutomorphism U).toFun t a := by
  funext t a
  have hβ := const_of_hasDerivAt_zero (hasDerivAt_conj_zero U α a (hα a)) t
  have hβ0 : star (U 0) * α 0 a * U 0 = a := by
    rw [congrFun hα0 a]
    simp
  rw [hβ0] at hβ
  have hmul : U t * star (U t) = 1 := Unitary.mul_star_self_of_mem (U.mem_unitary t)
  rw [toAutomorphism_apply]
  calc
    α t a = 1 * α t a * 1 := by simp
    _ = (U t * star (U t)) * α t a * (U t * star (U t)) := by rw [hmul]
    _ = U t * (star (U t) * α t a * U t) * star (U t) := by noncomm_ring
    _ = U t * a * star (U t) := by rw [hβ]

end UnitaryOneParameterGroup

end OperatorAlgebra
