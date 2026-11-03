/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.FieldNelson
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.QuadratureSelfAdjoint
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.JacobiCarleman
/-!

# The pairing operator is essentially self-adjoint

The number-nonconserving term `Δ a_x† a_y† + Δ̄ a_y a_x` of the Bose-Hubbard model with pairing.

## i. Overview

The pairing operator conserves the difference of the occupations of the modes `x` and `y` and the
occupations of all other modes. Along the line `(a + k, b + k)` with `a b = 0` it is a Jacobi matrix
with off-diagonal entries `|Δ| √((a+k+1)(b+k+1))`. The sum of the inverse entries diverges like the
harmonic series. The phase of `Δ` is removed by a gauge transformation. A vector orthogonal to the
range of the operator shifted by `i c` gives a square-summable solution of the eigenvalue equation
along every line. By Carleman's criterion it vanishes. Hence the range is dense and the operator is
essentially self-adjoint in the sense of Physlib. The finite-particle vectors are not analytic for
this operator, so Nelson's theorem does not apply. The lattice is arbitrary and no sector is fixed.

## ii. Key results

- `InfiniteBosons.pairOp`: the pairing operator.
- `InfiniteBosons.pair_orth_eq_zero`: the deficiency vectors vanish.
- `InfiniteBosons.pairOp_dense_range`: the shifted range is dense.
- `InfiniteBosons.pairOp_isEssentiallySelfAdjoint`: essential self-adjointness.
- `InfiniteBosons.pairOp_resolvent`: the bounded resolvent.

## iii. Table of contents

- A. The pairing operator
- B. Occupation lines and Carleman
- C. Essential self-adjointness

## iv. References

* M. Reed, B. Simon, Methods of Modern Mathematical Physics II, Section X.6.
* N. I. Akhiezer, The Classical Moment Problem, Oliver and Boyd (1965).
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- The pairing operator `Δ a_x† a_y† + Δ̄ a_y a_x`. -/
def pairOp (x y : L) (Δ : ℂ) : adjointable L :=
  Δ • (creOp x * creOp y) + (starRingEnd ℂ Δ) • (annOp y * annOp x)

lemma star_pairOp (x y : L) (Δ : ℂ) : star (pairOp x y Δ) = pairOp x y Δ := by
  simp only [pairOp, star_add, star_smul, star_mul, star_annOp, star_creOp, Complex.star_def,
    Complex.conj_conj]
  rw [add_comm]

lemma pairOp_single {x y : L} (hxy : x ≠ y) (Δ : ℂ) (α : Occ L) :
    (pairOp x y Δ).1.1 (single α 1) =
      single (α + single y 1 + single x 1)
        (Δ * ((Real.sqrt ((α x : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((α y : ℝ) + 1) : ℝ) : ℂ)) +
      single (α - single x 1 - single y 1)
        (starRingEnd ℂ Δ * ((Real.sqrt (α x : ℝ) : ℝ) : ℂ) * ((Real.sqrt (α y : ℝ) : ℝ) : ℂ)) := by
  show Δ • cre x (cre y (single α 1)) + starRingEnd ℂ Δ • ann y (ann x (single α 1)) = _
  rw [cre_single, cre_single, ann_single, ann_single]
  simp only [Finsupp.smul_single, smul_eq_mul]
  have e1 : (α + single y 1 : Occ L) x = α x := by simp [Finsupp.single_apply, hxy]
  have e2 : (α - single x 1 : Occ L) y = α y := by simp [Finsupp.single_apply, Ne.symm hxy]
  rw [e1, e2]
  congr 1 <;> congr 1 <;> ring


lemma orth_eq_pair {x y : L} (hxy : x ≠ y) (Δ : ℂ) (c : ℝ) (g : HilbertSp (Occ L)) (α : Occ L)
    (h : inner ℂ g (shiftMap (pairOp x y Δ).1.1 c (single α 1)) = 0) :
    (Δ * ((Real.sqrt ((α x : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((α y : ℝ) + 1) : ℝ) : ℂ)) *
        starRingEnd ℂ (g (α + single y 1 + single x 1)) +
      (starRingEnd ℂ Δ * ((Real.sqrt (α x : ℝ) : ℝ) : ℂ) * ((Real.sqrt (α y : ℝ) : ℝ) : ℂ)) *
        starRingEnd ℂ (g (α - single x 1 - single y 1)) +
      (Complex.I * c) * starRingEnd ℂ (g α) = 0 := by
  have hs : shiftMap (pairOp x y Δ).1.1 c (single α 1) =
      (lp.single 2 (α + single y 1 + single x 1)
        (Δ * ((Real.sqrt ((α x : ℝ) + 1) : ℝ) : ℂ) * ((Real.sqrt ((α y : ℝ) + 1) : ℝ) : ℂ)) :
          HilbertSp (Occ L)) +
      (lp.single 2 (α - single x 1 - single y 1)
        (starRingEnd ℂ Δ * ((Real.sqrt (α x : ℝ) : ℝ) : ℂ) * ((Real.sqrt (α y : ℝ) : ℝ) : ℂ)) :
          HilbertSp (Occ L)) +
      ((Complex.I * c : ℂ)) • (lp.single 2 α (1 : ℂ) : HilbertSp (Occ L)) := by
    have e1 : shiftMap (pairOp x y Δ).1.1 c (single α 1) =
        embed ((pairOp x y Δ).1.1 (single α 1)) + ((Complex.I * c : ℂ)) • embed (single α 1) := by
      simp only [shiftMap, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply, map_add, map_smul]
    rw [e1, pairOp_single hxy, map_add, embed_single, embed_single, embed_single]
  rw [hs, inner_add_right, inner_add_right, inner_smul_right, lp.inner_single_right,
    lp.inner_single_right, lp.inner_single_right] at h
  simp only [RCLike.inner_apply, mul_one] at h
  linear_combination h


/-- The occupation line: `x` carries `a + k` and `y` carries `b + k` bosons, the other modes as in `ρ`. -/
def lineVec (x y : L) (ρ : Occ L) (a b k : ℕ) : Occ L :=
  (ρ.update x (a + k)).update y (b + k)

lemma lineVec_x {x y : L} (hxy : x ≠ y) (ρ : Occ L) (a b k : ℕ) : lineVec x y ρ a b k x = a + k := by
  simp [lineVec, Finsupp.update_apply, hxy]

lemma lineVec_y {x y : L} (ρ : Occ L) (a b k : ℕ) : lineVec x y ρ a b k y = b + k := by
  simp [lineVec, Finsupp.update_apply]

lemma lineVec_succ {x y : L} (hxy : x ≠ y) (ρ : Occ L) (a b k : ℕ) :
    lineVec x y ρ a b k + single y 1 + single x 1 = lineVec x y ρ a b (k + 1) := by
  ext l
  by_cases hx : l = x
  · subst hx; simp [lineVec, Finsupp.update_apply, hxy, Finsupp.single_apply, add_assoc]
  · by_cases hy : l = y
    · subst hy; simp [lineVec, Finsupp.update_apply, hx, Finsupp.single_apply, add_assoc]
    · simp [lineVec, Finsupp.update_apply, hx, hy, Finsupp.single_apply, Ne.symm hx, Ne.symm hy]

lemma lineVec_pred {x y : L} (hxy : x ≠ y) (ρ : Occ L) (a b k : ℕ) :
    lineVec x y ρ a b (k + 1) - single x 1 - single y 1 = lineVec x y ρ a b k := by
  ext l
  by_cases hx : l = x
  · subst hx; simp [lineVec, Finsupp.update_apply, hxy, Finsupp.single_apply, add_assoc]
  · by_cases hy : l = y
    · subst hy; simp [lineVec, Finsupp.update_apply, hx, Finsupp.single_apply, add_assoc]
    · simp [lineVec, Finsupp.update_apply, hx, hy, Finsupp.single_apply, Ne.symm hx, Ne.symm hy]


lemma not_summable_inv_sqrt_mul (a b : ℕ) :
    ¬ Summable fun k : ℕ => 1 / (Real.sqrt (((a + k : ℕ) : ℝ) + 1) * Real.sqrt (((b + k : ℕ) : ℝ) + 1)) := by
  intro hs
  have hC : (0 : ℝ) < ((a : ℝ) + b + 1) := by positivity
  have h1 : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) := by
    have := hs.mul_left ((a : ℝ) + b + 1)
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) this
    set A : ℝ := ((a + k : ℕ) : ℝ) + 1 with hA
    set B : ℝ := ((b + k : ℕ) : ℝ) + 1 with hB
    have hA0 : 0 < A := by positivity
    have hB0 : 0 < B := by positivity
    have hsA := Real.sq_sqrt hA0.le
    have hsB := Real.sq_sqrt hB0.le
    have hpos : 0 < Real.sqrt A * Real.sqrt B :=
      mul_pos (Real.sqrt_pos.mpr hA0) (Real.sqrt_pos.mpr hB0)
    have hle : Real.sqrt A * Real.sqrt B ≤ ((a : ℝ) + b + 1) * ((k : ℝ) + 1) := by
      have : 2 * (Real.sqrt A * Real.sqrt B) ≤ A + B := by
        nlinarith [sq_nonneg (Real.sqrt A - Real.sqrt B)]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
      have hAB : A + B = (a : ℝ) + b + 2 * k + 2 := by rw [hA, hB]; push_cast; ring
      nlinarith [mul_nonneg ha hk, mul_nonneg hb hk]
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hpos]
    nlinarith
  have h2 : Summable fun n : ℕ => 1 / (n : ℝ) := by
    rw [← summable_nat_add_iff 1]
    simpa using h1
  exact Real.not_summable_one_div_natCast h2


/-- **Vanishing of the deficiency vectors of the pairing operator** `Δ a_x† a_y† + Δ̄ a_y a_x`.
Along every occupation line `(a + k, b + k)` with `a b = 0` the operator is a Jacobi matrix with
entries `|Δ| √((a+k+1)(b+k+1))`, and the sum of the inverse entries diverges. -/
theorem pair_orth_eq_zero {x y : L} (hxy : x ≠ y) {Δ : ℂ} (hΔ : Δ ≠ 0) {c : ℝ} (hc : c ≠ 0)
    (g : HilbertSp (Occ L))
    (h : ∀ α, inner ℂ g (shiftMap (pairOp x y Δ).1.1 c (single α 1)) = 0) : g = 0 := by
  obtain ⟨N, hN⟩ : ∃ N : ℝ, ‖Δ‖ = N := ⟨_, rfl⟩
  have hn0 : 0 < N := hN ▸ norm_pos_iff.mpr hΔ
  have hcn : (N : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  obtain ⟨lam, hlam⟩ : ∃ lam : ℂ, starRingEnd ℂ Δ = (N : ℂ) * lam :=
    ⟨starRingEnd ℂ Δ / N, by field_simp⟩
  have hΔlam : Δ = (N : ℂ) * starRingEnd ℂ lam := by
    have := congrArg (starRingEnd ℂ) hlam
    simpa [map_mul, Complex.conj_ofReal] using this
  have hlam1 : ‖lam‖ = 1 := by
    have : ‖starRingEnd ℂ Δ‖ = N * ‖lam‖ := by rw [hlam, norm_mul]; simp [abs_of_pos hn0]
    rw [RCLike.norm_conj, hN] at this
    exact (mul_left_cancel₀ hn0.ne' (this.symm.trans (mul_one N).symm))
  have hlamc : starRingEnd ℂ lam * lam = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hlam1]; simp
  have hlne : lam ≠ 0 := by intro h0; rw [h0] at hlam1; simp at hlam1
  have hfiber : ∀ (ρ : Occ L) (a b : ℕ), a * b = 0 → ∀ k : ℕ, g (lineVec x y ρ a b k) = 0 := by
    intro ρ a b hab
    set u : ℕ → ℂ := fun k => starRingEnd ℂ (g (lineVec x y ρ a b k)) with hu
    set w : ℕ → ℂ := fun k => (starRingEnd ℂ lam) ^ k * u k with hw
    have hsq : Summable fun k => ‖w k‖ ^ 2 := by
      have h1 := sq_summable g
      have hinj : Function.Injective fun k : ℕ => lineVec x y ρ a b k := fun k m hkm => by
        have := congrArg (fun f : Occ L => f x) hkm
        simpa [lineVec_x hxy] using this
      have h2 := h1.comp_injective hinj
      refine h2.congr fun k => ?_
      simp only [Function.comp, hw, hu, norm_mul, norm_pow, RCLike.norm_conj, hlam1, one_pow,
        one_mul, Real.rpow_two]
    have huw : ∀ k, u k = lam ^ k * w k := fun k => by
      simp only [hw]
      rw [← mul_assoc, ← mul_pow, mul_comm lam, hlamc, one_pow, one_mul]
    set bs : ℕ → ℝ := fun k => Real.sqrt (((a + k : ℕ) : ℝ) + 1) * Real.sqrt (((b + k : ℕ) : ℝ) + 1)
      with hbs
    have hbpos : ∀ k, 0 < bs k := fun k => by simp only [hbs]; positivity
    have hcore : ∀ k : ℕ, (N : ℂ) * (bs (k + 1) : ℝ) * w (k + 2) +
        (N : ℂ) * (bs k : ℝ) * w k = -(Complex.I * c) * w (k + 1) := by
      intro k
      have h1 := orth_eq_pair hxy Δ c g (lineVec x y ρ a b (k + 1)) (h _)
      rw [lineVec_succ hxy, lineVec_pred hxy, lineVec_x hxy, lineVec_y] at h1
      rw [show k + 1 + 1 = k + 2 from rfl] at h1
      have h2 : (Δ * (bs (k + 1) : ℝ)) * u (k + 2) +
          (starRingEnd ℂ Δ * (bs k : ℝ)) * u k + (Complex.I * c) * u (k + 1) = 0 := by
        simp only [hbs, hu]
        push_cast at h1 ⊢
        convert h1 using 3 <;> first | rfl | ring_nf
      rw [hlam, hΔlam, huw k, huw (k + 1), huw (k + 2)] at h2
      refine mul_left_cancel₀ (pow_ne_zero (k + 1) hlne) ?_
      push_cast at h2 ⊢
      linear_combination h2 - ((N : ℂ) * (bs (k + 1) : ℝ) * w (k + 2) * lam ^ (k + 1)) * hlamc
    have h0 : (bs 0 : ℂ) * w 1 = -(Complex.I * ((c / N : ℝ) : ℂ)) * w 0 := by
      have h1 := orth_eq_pair hxy Δ c g (lineVec x y ρ a b 0) (h _)
      rw [lineVec_succ hxy, lineVec_x hxy, lineVec_y] at h1
      have hz : Real.sqrt (((a + 0 : ℕ) : ℝ)) * Real.sqrt (((b + 0 : ℕ) : ℝ)) = 0 := by
        rcases Nat.mul_eq_zero.mp hab with ha | hb
        · subst ha; simp
        · subst hb; simp
      have hz' : ((Real.sqrt ((a : ℝ)) : ℝ) : ℂ) * ((Real.sqrt (b : ℝ) : ℝ) : ℂ) = 0 := by
        have : Real.sqrt (a : ℝ) * Real.sqrt (b : ℝ) = 0 := by simpa using hz
        exact_mod_cast this
      have h2 : (Δ * (bs 0 : ℝ)) * u 1 + (Complex.I * c) * u 0 = 0 := by
        simp only [hbs, hu]
        simp only [add_zero, Nat.cast_zero, Nat.cast_add] at h1 ⊢
        push_cast at h1 ⊢
        linear_combination h1 - (starRingEnd ℂ Δ *
          starRingEnd ℂ (g (lineVec x y ρ a b 0 - single x 1 - single y 1))) * hz'
      rw [hΔlam, huw 1, huw 0] at h2
      simp only [pow_zero, one_mul, pow_one] at h2
      push_cast at h2 ⊢
      field_simp
      linear_combination h2 - ((N : ℂ) * (bs 0 : ℝ) * w 1) * hlamc
    have hrec : ∀ k : ℕ, ((bs (k + 1) : ℝ) : ℂ) * w (k + 2) + ((bs k : ℝ) : ℂ) * w k =
        -(Complex.I * ((c / N : ℝ) : ℂ)) * w (k + 1) := by
      intro k
      have := hcore k
      push_cast at this ⊢
      field_simp
      linear_combination this
    have hdiv : ¬ Summable fun k : ℕ => 1 / bs k := by
      simpa [hbs] using not_summable_inv_sqrt_mul a b
    have hres := jacobi_no_l2_solution bs hbpos hdiv (c / N) (div_ne_zero hc hn0.ne') w hsq h0 hrec
    intro k
    have hw0 := hres k
    have := huw k
    rw [hw0, mul_zero] at this
    simpa [hu] using this
  ext α
  have hcov : α = lineVec x y α (α x - min (α x) (α y)) (α y - min (α x) (α y)) (min (α x) (α y)) := by
    ext l
    by_cases hx : l = x
    · subst hx; simp [lineVec, Finsupp.update_apply, hxy]
    · by_cases hy : l = y
      · subst hy; simp [lineVec, Finsupp.update_apply, hx]
      · simp [lineVec, Finsupp.update_apply, hx, hy]
  have hab : (α x - min (α x) (α y)) * (α y - min (α x) (α y)) = 0 := by
    rcases le_total (α x) (α y) with hle | hle
    · rw [min_eq_left hle]; simp
    · rw [min_eq_right hle]; simp
  have := hfiber α _ _ hab (min (α x) (α y))
  rw [← hcov] at this
  simpa using this

/-- The range of the pairing operator shifted by `i c` is dense. -/
theorem pairOp_dense_range {x y : L} (hxy : x ≠ y) {Δ : ℂ} (hΔ : Δ ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    Dense (LinearMap.range (shiftMap (pairOp x y Δ).1.1 c) : Set (HilbertSp (Occ L))) := by
  refine dense_of_orth _ fun g hg => pair_orth_eq_zero hxy hΔ hc g fun α => ?_
  exact hg _ ⟨single α 1, rfl⟩

/-- **The pairing operator `Δ a_x† a_y† + Δ̄ a_y a_x` is essentially self-adjoint** on the algebraic
Fock space of an arbitrary lattice. The finite-particle vectors are not analytic for it. The proof
is Carleman's criterion along the occupation lines of the pair of modes. -/
theorem pairOp_isEssentiallySelfAdjoint {x y : L} (hxy : x ≠ y) {Δ : ℂ} (hΔ : Δ ≠ 0) :
    (polyOp (pairOp x y Δ)).IsEssentiallySelfAdjoint :=
  polyOp_isEssentiallySelfAdjoint _ (star_pairOp x y Δ) (pairOp_dense_range hxy hΔ one_ne_zero)
    (pairOp_dense_range hxy hΔ (by norm_num))

/-- The bounded resolvent of the pairing operator. -/
theorem pairOp_resolvent {x y : L} (hxy : x ≠ y) {Δ : ℂ} (hΔ : Δ ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    ∃ R : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L), ‖R‖ ≤ 1 / |c| ∧
      ∀ f, R (shiftMap (pairOp x y Δ).1.1 c f) = embed f :=
  polyOp_resolvent (pairOp x y Δ) (star_pairOp x y Δ) hc (pairOp_dense_range hxy hΔ hc)

end InfiniteBosons
