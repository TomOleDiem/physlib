/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.OperatorAlgebra.Basic
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart

/-!

# States on observable C⋆-algebras

A state on a unital C⋆-algebra `A` is a positive normalized complex-linear functional
`ω : A → ℂ`.

## Note

This is a deliberately trimmed port: only what the abstract qubit development (`Qubit/`) needs
to state its Bloch-ball and purity results — evaluation, positivity, reality of expectation
values on observables, convex mixtures, and purity. Probabilities of effects and pullback of
states along ⋆-homomorphisms are not included; add them back (from physlib's history) if and
when something needs them.

-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder

variable {A : Type*} [OperatorAlgebra A]

namespace State

/-!
## Basic properties
-/

noncomputable instance instCoeFun :
    CoeFun (State A) (fun _ => A → ℂ) where
  coe ω := ω.toPositiveLinearMap


@[simp]
lemma apply_one (ω : State A) :
    ω 1 = 1 :=
  ω.map_one


/-- A state takes positive elements to nonnegative values. -/
lemma apply_nonneg
    (ω : State A) {a : A}
    (ha : 0 ≤ a) :
    0 ≤ ω a :=
  ω.toPositiveLinearMap.map_nonneg ha


/-- The expectation value of a self-adjoint element is real. -/
lemma apply_selfAdjoint_im_eq_zero
    (ω : State A) {a : A}
    (ha : IsSelfAdjoint a) :
    (ω a).im = 0 := by
  have h1 := Complex.le_def.mp (ω.apply_nonneg (CFC.posPart_nonneg a))
  have h2 := Complex.le_def.mp (ω.apply_nonneg (CFC.negPart_nonneg a))
  rw [← CFC.posPart_sub_negPart a ha, map_sub, Complex.sub_im, ← h1.2, ← h2.2]
  simp


/-- The expectation value of an observable is real. -/
lemma observable_im_eq_zero
    (ω : State A) (a : Observable A) :
    (ω (a : A)).im = 0 :=
  ω.apply_selfAdjoint_im_eq_zero a.property


/-!
## Convex structure

The state space is convex. Convex combinations describe probabilistic mixtures of states.
-/

/-- The convex mixture `tω + (1 - t)φ` of two states. -/
noncomputable def mix
    (ω φ : State A)
    (t : ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1) :
    State A where
  toPositiveLinearMap := PositiveLinearMap.mk₀
    { toFun := fun a => (t : ℂ) * ω a + ((1 - t : ℝ) : ℂ) * φ a
      map_add' := fun a b => by
        simp only [map_add]
        ring
      map_smul' := fun c a => by
        simp only [RingHom.id_apply, map_smul, smul_eq_mul]
        ring }
    (fun a ha => by
      show (0 : ℂ) ≤ (t : ℂ) * ω a + ((1 - t : ℝ) : ℂ) * φ a
      have h1 := Complex.le_def.mp (ω.apply_nonneg ha)
      have h2 := Complex.le_def.mp (φ.apply_nonneg ha)
      have ht1 : (0 : ℝ) ≤ 1 - t := by linarith
      rw [Complex.le_def]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im] at h1 h2 ⊢
      exact ⟨by nlinarith [h1.1, h2.1, mul_nonneg ht₀ h1.1, mul_nonneg ht1 h2.1],
        by nlinarith [h1.2, h2.2]⟩)
  map_one := by
    show (t : ℂ) * ω 1 + ((1 - t : ℝ) : ℂ) * φ 1 = 1
    rw [State.apply_one, State.apply_one]
    push_cast
    ring


/-- Evaluation of a convex mixture. -/
lemma mix_apply
    (ω φ : State A)
    (t : ℝ)
    (ht₀ : 0 ≤ t)
    (ht₁ : t ≤ 1)
    (a : A) :
    mix ω φ t ht₀ ht₁ a =
      (t : ℂ) * ω a +
        ((1 - t : ℝ) : ℂ) * φ a :=
  rfl


/-!
## Pure states

Purity is intrinsic to the convex geometry of the state space. It does not refer to vectors,
rays, ranks, or density operators.
-/

/-- A state is pure if every nontrivial convex decomposition is trivial. -/
def IsPure (ω : State A) : Prop :=
  ∀ (φ ψ : State A)
    (t : ℝ)
    (ht₀ : 0 < t)
    (ht₁ : t < 1),
    mix φ ψ t ht₀.le ht₁.le = ω →
      φ = ω ∧ ψ = ω

/-!
## Finite convex mixtures

`mix` gives binary convex combinations; `finiteMix` generalizes this to a finite convex
combination indexed by any `Fintype`. The key fact about pure states here is `eq_of_finiteMix`:
a pure state occurring with strictly positive weight in a finite convex decomposition must equal
every component with positive weight.
-/

/-- A finite convex mixture of states. -/
noncomputable def finiteMix {ι : Type*} [Fintype ι] (ω : ι → State A) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) : State A where
  toPositiveLinearMap := PositiveLinearMap.mk₀
    (∑ i, (p i : ℂ) • (ω i).toPositiveLinearMap.toLinearMap)
    (fun a ha => by
      rw [LinearMap.sum_apply]
      exact Finset.sum_nonneg fun i _ =>
        mul_nonneg (RCLike.ofReal_nonneg.mpr (hp i)) ((ω i).apply_nonneg ha))
  map_one := by
    change (∑ i, (p i : ℂ) • (ω i).toPositiveLinearMap.toLinearMap) 1 = 1
    rw [LinearMap.sum_apply]
    change (∑ i, (p i : ℂ) * ω i 1) = 1
    simp only [State.apply_one, mul_one]
    exact_mod_cast hsum

@[simp]
lemma finiteMix_apply {ι : Type*} [Fintype ι] (ω : ι → State A) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (a : A) :
    finiteMix ω p hp hsum a = ∑ i, (p i : ℂ) * ω i a := by
  change (∑ i, (p i : ℂ) • (ω i).toPositiveLinearMap.toLinearMap) a = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- A pure state occurring with strictly positive weight in a finite convex decomposition must
equal every component with positive weight. -/
lemma IsPure.eq_of_finiteMix {ι : Type*} [Fintype ι] (ω : State A) (hω : ω.IsPure)
    (φ : ι → State A) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hmix : finiteMix φ p hp hsum = ω) {i : ι} (hi : 0 < p i) : φ i = ω := by
  classical
  have hpi : p i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
  rcases hpi.eq_or_lt with hpi | hpi
  · have herase := Finset.sum_erase_add Finset.univ p (Finset.mem_univ i)
    have hrest : ∑ j ∈ Finset.univ.erase i, p j = 0 := by
      rw [hsum, hpi] at herase
      linarith
    have hz : ∀ j, j ≠ i → p j = 0 := by
      intro j hji
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun k _ => hp k)).mp hrest j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    have hsingle : finiteMix φ p hp hsum = φ i := by
      rw [State.mk.injEq]
      apply PositiveLinearMap.ext
      intro a
      rw [finiteMix_apply]
      rw [Finset.sum_eq_single i]
      · simp [hpi]
      · intro j _ hji
        simp [hz j hji]
      · simp
    exact hsingle.symm.trans hmix
  · let q : ι → ℝ := fun j => if j = i then 0 else p j / (1 - p i)
    have hden : 0 < 1 - p i := sub_pos.mpr hpi
    have hq : ∀ j, 0 ≤ q j := by
      intro j
      simp only [q]
      split
      · exact le_rfl
      · exact div_nonneg (hp j) hden.le
    have hqsum : ∑ j, q j = 1 := by
      have herase := Finset.sum_erase_add Finset.univ p (Finset.mem_univ i)
      have hrest : ∑ j ∈ Finset.univ.erase i, p j = 1 - p i := by
        rw [hsum] at herase
        linarith
      calc
        ∑ j, q j = ∑ j ∈ Finset.univ.erase i, q j := by
          rw [Finset.sum_erase (s := Finset.univ) (f := q) (by simp [q])]
        _ = ∑ j ∈ Finset.univ.erase i, p j / (1 - p i) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [q, (Finset.mem_erase.mp hj).1]
        _ = (∑ j ∈ Finset.univ.erase i, p j) / (1 - p i) :=
          (Finset.sum_div _ _ _).symm
        _ = 1 := by rw [hrest, div_self (ne_of_gt hden)]
    let χ : State A := finiteMix φ q hq hqsum
    have hbinary : mix (φ i) χ (p i) hi.le hpi.le = finiteMix φ p hp hsum := by
      rw [State.mk.injEq]
      apply PositiveLinearMap.ext
      intro a
      rw [mix_apply, finiteMix_apply, finiteMix_apply]
      have hscale : ((1 - p i : ℝ) : ℂ) *
          (∑ j, (q j : ℂ) * φ j a) =
          ∑ j ∈ Finset.univ.erase i, (p j : ℂ) * φ j a := by
        rw [Finset.mul_sum]
        rw [← Finset.sum_erase (s := Finset.univ)
          (f := fun j => ((1 - p i : ℝ) : ℂ) * ((q j : ℂ) * φ j a))]
        · apply Finset.sum_congr rfl
          intro j hj
          have hji := (Finset.mem_erase.mp hj).1
          simp only [q, if_neg hji]
          push_cast
          have hdenC : (1 - (p i : ℂ)) ≠ 0 := by
            exact_mod_cast ne_of_gt hden
          calc
            (1 - (p i : ℂ)) * ((p j : ℂ) / (1 - (p i : ℂ)) * φ j a) =
                ((1 - (p i : ℂ)) * ((p j : ℂ) / (1 - (p i : ℂ)))) *
                  φ j a := by ring
            _ = (p j : ℂ) * φ j a := by rw [mul_div_cancel₀ _ hdenC]
        · simp [q]
      rw [hscale, add_comm]
      exact Finset.sum_erase_add Finset.univ
        (fun j => (p j : ℂ) * φ j a) (Finset.mem_univ i)
    exact (hω (φ i) χ (p i) hi hpi (hbinary.trans hmix)).1

end State

end OperatorAlgebra
