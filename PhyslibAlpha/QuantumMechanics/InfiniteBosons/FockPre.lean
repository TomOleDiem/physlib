/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Sqrt
/-!

# The algebraic Fock space of an arbitrary mode set

Finitely many bosons in an arbitrary set of modes, with the creation and annihilation operators and
their canonical commutation relations.

## i. Overview

The modes form an arbitrary set `L`, finite or infinite. A state with finitely many bosons is a
finite linear combination of occupation-number vectors `α : L →₀ ℕ`. The annihilation operator of
the mode `x` lowers `α x` by one with the factor `√(α x)`. The creation operator raises it with the
factor `√(α x + 1)`. No Hilbert space completion and no global state is chosen. The sesquilinear
pairing of the occupation basis makes `a_x†` the formal adjoint of `a_x`. The operators satisfy the
canonical commutation relations `[a_x, a_y†] = δ_xy`, `[a_x, a_y] = 0` and `[a_x†, a_y†] = 0`.

## ii. Key results

- `InfiniteBosons.FockPre`: the algebraic Fock space.
- `InfiniteBosons.ann`, `InfiniteBosons.cre`: the annihilation and creation operators.
- `InfiniteBosons.pair_ann`, `InfiniteBosons.pair_cre`: formal adjointness.
- `InfiniteBosons.ann_cre_comm_same`: `[a_x, a_x†] = 1`.

## iii. Table of contents

- A. The Fock space and its pairing
- B. Creation and annihilation operators
- C. Formal adjointness
- D. Canonical commutation relations

## iv. References

* J. Dereziński and C. Gérard, Mathematics of Quantization and Quantum Fields, Cambridge
  University Press (2013), Chapter 3.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable (L : Type*) [DecidableEq L]

/-- Occupation vectors: finitely many bosons. -/
abbrev Occ := L →₀ ℕ

/-- The algebraic Fock space: finite linear combinations of occupation-number states. -/
abbrev FockPre := Occ L →₀ ℂ

variable {L}

section Pairing

variable {B : Type*} [DecidableEq B]

/-- The standard sesquilinear pairing of the algebraic Fock space. -/
def pair (f g : (B →₀ ℂ)) : ℂ := f.sum fun α c => (starRingEnd ℂ c) * g α

lemma pair_single_single (α β : B) (c d : ℂ) :
    pair (single α c) (single β d) = if α = β then (starRingEnd ℂ c) * d else 0 := by
  by_cases h : α = β
  · subst h; simp [pair]
  · simp [pair, h, Finsupp.single_apply, Ne.symm h]

lemma pair_add_left (f f' g : (B →₀ ℂ)) : pair (f + f') g = pair f g + pair f' g := by
  unfold pair
  rw [Finsupp.sum_add_index']
  · intro a; simp
  · intro a b c; simp [map_add, add_mul]

lemma pair_add_right (f g g' : (B →₀ ℂ)) : pair f (g + g') = pair f g + pair f g' := by
  unfold pair
  simp [mul_add, Finsupp.sum_add]

lemma pair_smul_right (f g : (B →₀ ℂ)) (d : ℂ) : pair f (d • g) = d * pair f g := by
  simp [pair, Finsupp.sum, Finset.mul_sum, mul_left_comm]

lemma pair_smul_left (f g : (B →₀ ℂ)) (c : ℂ) :
    pair (c • f) g = (starRingEnd ℂ c) * pair f g := by
  unfold pair
  rw [Finsupp.sum_smul_index']
  · simp [Finsupp.sum, Finset.mul_sum, mul_assoc]
  · intro a; simp

lemma pair_zero_left (g : (B →₀ ℂ)) : pair 0 g = 0 := by simp [pair]

lemma pair_zero_right (f : (B →₀ ℂ)) : pair f 0 = 0 := by simp [pair]

lemma pair_conj_symm (f g : (B →₀ ℂ)) : pair g f = starRingEnd ℂ (pair f g) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [pair_zero_left, pair_zero_right]
  | add f f' hf hf' => rw [pair_add_left, pair_add_right, map_add, hf, hf']
  | single α c =>
    induction g using Finsupp.induction_linear with
    | zero => simp [pair_zero_left, pair_zero_right]
    | add g g' hg hg' => rw [pair_add_right, pair_add_left, map_add, hg, hg']
    | single β d =>
      rw [pair_single_single, pair_single_single]
      by_cases h : α = β
      · subst h; simp [mul_comm]
      · simp [h, Ne.symm h]

/-- Two operators are formally adjoint when it holds on basis vectors. -/
lemma pair_eq_of_basis {T S : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)}
    (h : ∀ α β : B, pair (T (single α 1)) (single β 1) = pair (single α 1) (S (single β 1)))
    (f g : (B →₀ ℂ)) : pair (T f) g = pair f (S g) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [pair_zero_left, pair_zero_right]
  | add f f' hf hf' => rw [map_add, pair_add_left, pair_add_left, hf, hf']
  | single α c =>
    induction g using Finsupp.induction_linear with
    | zero => simp [pair_zero_left, pair_zero_right]
    | add g g' hg hg' => rw [map_add, pair_add_right, pair_add_right, hg, hg']
    | single β d =>
      have e1 : (single α c : (B →₀ ℂ)) = c • single α 1 := by simp [Finsupp.smul_single]
      have e2 : (single β d : (B →₀ ℂ)) = d • single β 1 := by simp [Finsupp.smul_single]
      rw [e1, e2, map_smul, pair_smul_left, pair_smul_right, map_smul, pair_smul_right,
        pair_smul_left, h α β]
      ring


lemma linearMap_ext_basis {M : Type*} [AddCommGroup M] [Module ℂ M] {f g : (B →₀ ℂ) →ₗ[ℂ] M}
    (h : ∀ α : B, f (single α 1) = g (single α 1)) : f = g := by
  refine Finsupp.lhom_ext fun α c => ?_
  have : (single α c : (B →₀ ℂ)) = c • single α 1 := by simp [Finsupp.smul_single]
  rw [this, map_smul, map_smul, h α]

end Pairing

/-- The annihilation operator of the mode `x`. -/
def ann (x : L) : FockPre L →ₗ[ℂ] FockPre L :=
  Finsupp.lsum ℂ fun α => ((Real.sqrt (α x) : ℝ) : ℂ) • Finsupp.lsingle (α - single x 1)

/-- The creation operator of the mode `x`. -/
def cre (x : L) : FockPre L →ₗ[ℂ] FockPre L :=
  Finsupp.lsum ℂ fun α => ((Real.sqrt (α x + 1) : ℝ) : ℂ) • Finsupp.lsingle (α + single x 1)

lemma ann_single (x : L) (α : Occ L) (c : ℂ) :
    ann x (single α c) = single (α - single x 1) (((Real.sqrt (α x) : ℝ) : ℂ) * c) := by
  simp [ann, Finsupp.lsum_single, Finsupp.smul_single]

lemma cre_single (x : L) (α : Occ L) (c : ℂ) :
    cre x (single α c) = single (α + single x 1) (((Real.sqrt (α x + 1) : ℝ) : ℂ) * c) := by
  simp [cre, Finsupp.lsum_single, Finsupp.smul_single]


lemma single_le_iff' (x : L) (α : Occ L) : single x 1 ≤ α ↔ 1 ≤ α x := by
  rw [Finsupp.single_le_iff]

lemma ann_adjoint_basis (x : L) (α β : Occ L) :
    pair (ann x (single α 1)) (single β 1) = pair (single α 1) (cre x (single β 1)) := by
  rw [ann_single, cre_single, pair_single_single, pair_single_single]
  by_cases h : α = β + single x 1
  · have h1 : α x = β x + 1 := by rw [h]; simp
    have h2 : α - single x 1 = β := by rw [h]; simp
    rw [if_pos h2, if_pos h, h1]
    simp
  · rw [if_neg h]
    by_cases h2 : α - single x 1 = β
    · have : α x = 0 := by
        by_contra hx
        apply h
        rw [← h2]
        exact (tsub_add_cancel_of_le ((single_le_iff' x α).mpr (Nat.one_le_iff_ne_zero.mpr hx))).symm
      simp [this]
    · rw [if_neg h2]

lemma cre_adjoint_basis (x : L) (α β : Occ L) :
    pair (cre x (single α 1)) (single β 1) = pair (single α 1) (ann x (single β 1)) := by
  rw [ann_single, cre_single, pair_single_single, pair_single_single]
  by_cases h : α + single x 1 = β
  · have h1 : β x = α x + 1 := by rw [← h]; simp
    have h2 : α = β - single x 1 := by rw [← h]; simp
    rw [if_pos h, if_pos h2, h1]
    simp
  · rw [if_neg h]
    by_cases h2 : α = β - single x 1
    · have : β x = 0 := by
        by_contra hx
        apply h
        rw [h2]
        exact tsub_add_cancel_of_le ((single_le_iff' x β).mpr (Nat.one_le_iff_ne_zero.mpr hx))
      simp [this]
    · rw [if_neg h2]

/-- `a_x†` is the formal adjoint of `a_x`. -/
lemma pair_ann (x : L) (f g : FockPre L) : pair (ann x f) g = pair f (cre x g) :=
  pair_eq_of_basis (ann_adjoint_basis x) f g

lemma pair_cre (x : L) (f g : FockPre L) : pair (cre x f) g = pair f (ann x g) :=
  pair_eq_of_basis (cre_adjoint_basis x) f g


lemma sqrt_mul_sqrt_complex (r : ℝ) (hr : 0 ≤ r) :
    ((Real.sqrt r : ℝ) : ℂ) * ((Real.sqrt r : ℝ) : ℂ) = (r : ℂ) := by
  exact_mod_cast Real.mul_self_sqrt hr

lemma ann_cre_single_same (x : L) (α : Occ L) :
    ann x (cre x (single α 1)) = (((α x : ℝ) + 1 : ℝ) : ℂ) • single α 1 := by
  rw [cre_single, ann_single]
  have h1 : ((α + single x 1 : Occ L) x) = α x + 1 := by simp
  have h2 : α + single x 1 - single x 1 = α := by simp
  rw [h1, h2]
  have hs := sqrt_mul_sqrt_complex ((α x : ℝ) + 1) (by positivity)
  simp only [Nat.cast_add, Nat.cast_one, mul_one, Finsupp.smul_single, smul_eq_mul]
  rw [hs]


lemma cre_ann_single_same (x : L) (α : Occ L) :
    cre x (ann x (single α 1)) = (α x : ℂ) • single α 1 := by
  rw [ann_single, cre_single]
  by_cases hx : α x = 0
  · simp [hx]
  · have hle : single x 1 ≤ α := (single_le_iff' x α).mpr (Nat.one_le_iff_ne_zero.mpr hx)
    have h1 : ((α - single x 1 : Occ L) x) + 1 = α x := by
      simp; omega
    have h2 : α - single x 1 + single x 1 = α := tsub_add_cancel_of_le hle
    rw [h2]
    have hs := sqrt_mul_sqrt_complex (α x : ℝ) (by positivity)
    have h1' : (((α - single x 1 : Occ L) x : ℕ) : ℝ) + 1 = (α x : ℝ) := by
      exact_mod_cast h1
    rw [h1']
    simp only [mul_one, Finsupp.smul_single, smul_eq_mul]
    rw [hs]
    simp


lemma ann_cre_single_ne {x y : L} (hxy : x ≠ y) (α : Occ L) :
    ann x (cre y (single α 1)) = cre y (ann x (single α 1)) := by
  rw [cre_single, ann_single, ann_single, cre_single]
  by_cases hx : α x = 0
  · have : ((single y 1 : Occ L) x) = 0 := by simp [Finsupp.single_apply, Ne.symm hxy]
    simp [hx, this]
  · have hle : single x 1 ≤ α := (single_le_iff' x α).mpr (Nat.one_le_iff_ne_zero.mpr hx)
    have e1 : ((α + single y 1 : Occ L) x) = α x := by simp [Finsupp.single_apply, hxy.symm]
    have e2 : ((α - single x 1 : Occ L) y) = α y := by simp [Finsupp.single_apply, hxy.symm]
    have e3 : α + single y 1 - single x 1 = α - single x 1 + single y 1 :=
      tsub_add_eq_add_tsub hle |>.symm
    rw [e1, e2, e3]
    simp only [mul_one]
    congr 1
    ring

lemma ann_ann_single (x y : L) (α : Occ L) :
    ann x (ann y (single α 1)) = ann y (ann x (single α 1)) := by
  rw [ann_single, ann_single, ann_single, ann_single]
  by_cases hxy : x = y
  · subst hxy; rfl
  · have e1 : ((α - single y 1 : Occ L) x) = α x := by simp [Finsupp.single_apply, hxy]
    have e2 : ((α - single x 1 : Occ L) y) = α y := by simp [Finsupp.single_apply, Ne.symm hxy]
    have e3 : α - single y 1 - single x 1 = α - single x 1 - single y 1 := tsub_right_comm
    rw [e1, e2, e3]
    simp only [mul_one]
    congr 1
    ring

lemma cre_cre_single (x y : L) (α : Occ L) :
    cre x (cre y (single α 1)) = cre y (cre x (single α 1)) := by
  rw [cre_single, cre_single, cre_single, cre_single]
  by_cases hxy : x = y
  · subst hxy; rfl
  · have e1 : ((α + single y 1 : Occ L) x) = α x := by simp [Finsupp.single_apply, hxy]
    have e2 : ((α + single x 1 : Occ L) y) = α y := by simp [Finsupp.single_apply, Ne.symm hxy]
    have e3 : α + single y 1 + single x 1 = α + single x 1 + single y 1 := add_right_comm _ _ _
    rw [e1, e2, e3]
    simp only [mul_one]
    congr 1
    ring


/-- **Canonical commutation relation** `[a_x, a_x†] = 1`. -/
lemma ann_cre_comm_same (x : L) :
    ann x ∘ₗ cre x - cre x ∘ₗ ann x = LinearMap.id := by
  refine linearMap_ext_basis fun α => ?_
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
  rw [ann_cre_single_same, cre_ann_single_same]
  rw [← sub_smul]
  simp

/-- **Canonical commutation relation** `[a_x, a_y†] = 0` for different modes. -/
lemma ann_cre_comm_ne {x y : L} (hxy : x ≠ y) : ann x ∘ₗ cre y = cre y ∘ₗ ann x := by
  refine linearMap_ext_basis fun α => ?_
  simp only [LinearMap.comp_apply]
  exact ann_cre_single_ne hxy α

lemma ann_comm (x y : L) : ann x ∘ₗ ann y = ann y ∘ₗ ann x := by
  refine linearMap_ext_basis fun α => ?_
  simp only [LinearMap.comp_apply]
  exact ann_ann_single x y α

lemma cre_comm (x y : L) : cre x ∘ₗ cre y = cre y ∘ₗ cre x := by
  refine linearMap_ext_basis fun α => ?_
  simp only [LinearMap.comp_apply]
  exact cre_cre_single x y α

end InfiniteBosons
