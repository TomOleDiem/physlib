/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.EssentialSelfAdjoint
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.JacobiCarleman
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.TensorAmp
/-!

# The quadrature `a_x + a_x†` is essentially self-adjoint

Carleman's criterion applied along the occupation lines of one mode.

## i. Overview

The quadrature `Q_x = a_x + a_x†` acts on the occupation basis by
`Q_x |α⟩ = √(α_x) |α - 1_x⟩ + √(α_x + 1) |α + 1_x⟩`. Fix the occupations of all modes except `x`.
Along this line the operator is the Jacobi matrix with off-diagonal entries `b_n = √(n+1)`. A vector
orthogonal to the range of `Q_x + i c` restricts to a square-summable solution of the eigenvalue
equation on every line. The sum of `1/√(n+1)` diverges. By the Carleman argument the solution
vanishes. Hence the range of `Q_x ± i` is dense and `Q_x` is essentially self-adjoint in the sense of
Physlib. The lattice is arbitrary and no sector is fixed. This is the first unbounded field
operator of the Weyl link: `W = exp(i t Q_x)` is the Weyl operator once the unitary group is
built from the self-adjoint closure.

## ii. Key results

- `InfiniteBosons.quad_orth_eq_zero`: the deficiency vectors vanish.
- `InfiniteBosons.quadOp_dense_range`: the range of `Q_x + i c` is dense.
- `InfiniteBosons.quadOp_isEssentiallySelfAdjoint`: essential self-adjointness.
- `InfiniteBosons.quadOp_resolvent`: the bounded resolvent.

## iii. Table of contents

- A. The quadrature and the orthogonality equation
- B. Vanishing of the deficiency vectors
- C. Essential self-adjointness

## iv. References

* M. Reed, B. Simon, Methods of Modern Mathematical Physics II, Section X.6.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- The quadrature `a_x + a_x†`. -/
def quadOp (x : L) : adjointable L := annOp x + creOp x

lemma quadOp_single (x : L) (α : Occ L) :
    (quadOp x).1.1 (single α 1) =
      single (α - single x 1) (((Real.sqrt (α x) : ℝ) : ℂ)) +
      single (α + single x 1) (((Real.sqrt (α x + 1) : ℝ) : ℂ)) := by
  show ann x (single α 1) + cre x (single α 1) = _
  rw [ann_single, cre_single]; simp


lemma orth_eq (x : L) (c : ℝ) (g : HilbertSp (Occ L)) (α : Occ L)
    (h : inner ℂ g (shiftMap (quadOp x).1.1 c (single α 1)) = 0) :
    (Real.sqrt (α x) : ℂ) * starRingEnd ℂ (g (α - single x 1)) +
      (Real.sqrt (α x + 1) : ℂ) * starRingEnd ℂ (g (α + single x 1)) +
      (Complex.I * c) * starRingEnd ℂ (g α) = 0 := by
  have hs : shiftMap (quadOp x).1.1 c (single α 1) =
      (lp.single 2 (α - single x 1) ((Real.sqrt (α x) : ℝ) : ℂ) : HilbertSp (Occ L)) +
      (lp.single 2 (α + single x 1) ((Real.sqrt (α x + 1) : ℝ) : ℂ) : HilbertSp (Occ L)) +
      ((Complex.I * c : ℂ)) • (lp.single 2 α (1 : ℂ) : HilbertSp (Occ L)) := by
    have e1 : shiftMap (quadOp x).1.1 c (single α 1) =
        embed ((quadOp x).1.1 (single α 1)) + ((Complex.I * c : ℂ)) • embed (single α 1) := by
      simp only [shiftMap, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_add, map_smul]
    rw [e1, quadOp_single, map_add, embed_single, embed_single, embed_single]
  rw [hs, inner_add_right, inner_add_right, inner_smul_right, lp.inner_single_right,
    lp.inner_single_right, lp.inner_single_right] at h
  simp only [RCLike.inner_apply, mul_one] at h
  simpa using h


lemma update_x (x : L) (ρ : Occ L) (n : ℕ) : (ρ.update x n) x = n := by
  simp [Finsupp.update_apply]

lemma update_succ (x : L) (ρ : Occ L) (n : ℕ) :
    ρ.update x n + single x 1 = ρ.update x (n + 1) := by
  ext l
  by_cases h : l = x
  · subst h; simp
  · simp [Finsupp.update_apply, h, Finsupp.single_apply, Ne.symm h]

lemma update_pred (x : L) (ρ : Occ L) (n : ℕ) :
    ρ.update x (n + 1) - single x 1 = ρ.update x n := by
  ext l
  by_cases h : l = x
  · subst h; simp
  · simp [Finsupp.update_apply, h, Finsupp.single_apply, Ne.symm h]

/-- **Vanishing of the deficiency vectors of `a_x + a_x†`.** -/
theorem quad_orth_eq_zero (x : L) {c : ℝ} (hc : c ≠ 0) (g : HilbertSp (Occ L))
    (h : ∀ α, inner ℂ g (shiftMap (quadOp x).1.1 c (single α 1)) = 0) : g = 0 := by
  have hfiber : ∀ (ρ : Occ L) (n : ℕ), g (ρ.update x n) = 0 := by
    intro ρ
    set u : ℕ → ℂ := fun n => starRingEnd ℂ (g (ρ.update x n)) with hu
    have hsq : Summable fun n => ‖u n‖ ^ 2 := by
      have h1 := sq_summable g
      have hinj : Function.Injective fun n : ℕ => ρ.update x n := fun n m hnm => by
        have := congrArg (fun f : Occ L => f x) hnm
        simpa using this
      have h2 := h1.comp_injective hinj
      refine h2.congr fun n => ?_
      simp only [Function.comp, hu, RCLike.norm_conj, Real.rpow_two]
    have h0 : ((Real.sqrt ((0 : ℕ) + 1) : ℝ) : ℂ) * u 1 = -(Complex.I * c) * u 0 := by
      have := orth_eq x c g (ρ.update x 0) (h _)
      rw [update_succ] at this
      simp only [update_x, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero,
        zero_mul, zero_add] at this
      simp only [hu]
      have h2 : ((Real.sqrt (((0 : ℕ) : ℝ) + 1) : ℝ) : ℂ) * starRingEnd ℂ (g (ρ.update x (0 + 1))) =
          -(Complex.I * c) * starRingEnd ℂ (g (ρ.update x 0)) := by
        simpa using eq_neg_of_add_eq_zero_left this
      simpa using h2
    have hrec : ∀ n : ℕ, ((Real.sqrt ((n + 1 : ℕ) + 1) : ℝ) : ℂ) * u (n + 2) +
        ((Real.sqrt ((n : ℕ) + 1) : ℝ) : ℂ) * u n = -(Complex.I * c) * u (n + 1) := by
      intro n
      have := orth_eq x c g (ρ.update x (n + 1)) (h _)
      rw [update_pred, update_succ] at this
      simp only [update_x] at this
      simp only [hu]
      have h3 : ((Real.sqrt (((n + 1 : ℕ) : ℝ) + 1) : ℝ) : ℂ) *
          starRingEnd ℂ (g (ρ.update x (n + 1 + 1))) +
          ((Real.sqrt (((n : ℕ) : ℝ) + 1) : ℝ) : ℂ) * starRingEnd ℂ (g (ρ.update x n)) =
          -(Complex.I * c) * starRingEnd ℂ (g (ρ.update x (n + 1))) := by
        have h4 : ((Real.sqrt (((n + 1 : ℕ) : ℝ)) : ℝ) : ℂ) = ((Real.sqrt (((n : ℕ) : ℝ) + 1) : ℝ) : ℂ) := by
          push_cast; rfl
        rw [← h4]
        linear_combination (exp := 1) this
      exact h3
    have hdiv : ¬ Summable fun n : ℕ => 1 / Real.sqrt ((n : ℝ) + 1) := by
      intro hs
      have h1 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) := by
        refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
        have hle : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
          have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
          have hs1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := Real.one_le_sqrt.mpr this
          nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (n : ℝ) + 1 by linarith)]
        exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) hle
      have h2 : Summable fun n : ℕ => 1 / (n : ℝ) := by
        rw [← summable_nat_add_iff 1]
        simpa using h1
      exact Real.not_summable_one_div_natCast h2
    have := jacobi_no_l2_solution (fun n => Real.sqrt ((n : ℝ) + 1)) (fun n => by positivity)
      hdiv c hc u hsq h0 hrec
    intro n
    have := this n
    simpa [hu] using this
  ext α
  have := hfiber α (α x)
  simpa using this


lemma dense_of_orth {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (K : Submodule ℂ H) (h : ∀ g : H, (∀ k ∈ K, inner ℂ g k = 0) → g = 0) :
    Dense (K : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    ← Submodule.orthogonal_eq_bot_iff (K := K.topologicalClosure), Submodule.orthogonal_closure,
    Submodule.eq_bot_iff]
  intro g hg
  exact h g (fun k hk => by
    have := (Submodule.mem_orthogonal K g).mp hg k hk
    rw [← inner_conj_symm]; simp [this])

/-- **The range of `a_x + a_x† + i c` is dense.** -/
theorem quadOp_dense_range (x : L) {c : ℝ} (hc : c ≠ 0) :
    Dense (LinearMap.range (shiftMap (quadOp x).1.1 c) : Set (HilbertSp (Occ L))) := by
  refine dense_of_orth _ fun g hg => quad_orth_eq_zero x hc g fun α => ?_
  exact hg _ ⟨single α 1, rfl⟩

lemma star_quadOp (x : L) : star (quadOp x) = quadOp x := by
  simp only [quadOp, star_add, star_annOp, star_creOp]
  rw [add_comm]

/-- **The quadrature `a_x + a_x†` is essentially self-adjoint** on the algebraic Fock space of an
arbitrary lattice. The proof is Carleman's criterion for the Jacobi matrix with entries `√(n+1)`
along every occupation line of the mode `x`. -/
theorem quadOp_isEssentiallySelfAdjoint (x : L) : (polyOp (quadOp x)).IsEssentiallySelfAdjoint :=
  polyOp_isEssentiallySelfAdjoint _ (star_quadOp x) (quadOp_dense_range x one_ne_zero)
    (quadOp_dense_range x (by norm_num))

/-- The bounded resolvent of the quadrature. -/
theorem quadOp_resolvent (x : L) {c : ℝ} (hc : c ≠ 0) :
    ∃ R : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L), ‖R‖ ≤ 1 / |c| ∧
      ∀ f, R (shiftMap (quadOp x).1.1 c f) = embed f :=
  polyOp_resolvent (quadOp x) (star_quadOp x) hc (quadOp_dense_range x hc)

end InfiniteBosons
