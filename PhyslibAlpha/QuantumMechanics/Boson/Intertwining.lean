/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.Mathematics.HilbertSpace.TensorPower
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.Unbounded.EssentialSpectrum.WeakCompact
/-!

# Asymptotic intertwining of the sector generators with particle creation

Adding a particle that escapes to infinity turns an `m`-body observable on `n` particles into
the same observable on `n - 1` particles.

## i. Overview

Let `φ_j` be an orthonormal sequence in the one-particle space. The creation operators `a†(φ_j)`
map the `(n-1)`-particle space into the `n`-particle space. A generator `gen K k`, the symmetrized
`K ⊗ 1` with `K` compact on `m` particles, satisfies on coherent vectors

`gen K (k+1) a†(φ_j) ψ - ((k+1)/(m+k+1)) a†(φ_j) gen K k ψ → 0`

in norm. The error is the symmetrization of `K` applied to the derivative vector of the escaping
particle. A compact operator maps this weakly null sequence to a norm null sequence. This is the
mechanism behind the connecting maps of the Buchholz algebra.

## ii. Key results

- `HilbertPower.Dlin`: the derivative vector `φ ↦ D u φ m` as a bounded linear map.
- `HilbertPower.tendsto_embed_D`: `K` maps the derivative vectors of an orthonormal sequence to a
  null sequence.
- `HilbertPower.tendsto_gen_cre_pow`: the asymptotic intertwining on coherent vectors.

## iii. Table of contents

- A. The derivative vector as a bounded map
- B. The error term is null
- C. Asymptotic intertwining

## iv. References

* A. Deuchert, J. Lampart and M. Lemm, Dynamics and equilibrium states of infinite systems of
  lattice bosons, arXiv:2505.13170, Eq. (13).
-/

@[expose] public section

universe u

open Filter Topology HilbertPower
open scoped InnerProductSpace

noncomputable section

namespace HilbertPower

variable {h : Type u} [NormedAddCommGroup h] [InnerProductSpace ℂ h] [CompleteSpace h]

/-!

## A. The derivative vector as a bounded map

-/

/-- The derivative vector `D u φ m` as a bounded linear map in `φ`. -/
def Dlin (u : h) (m : ℕ) : h →L[ℂ] TPow h m :=
  LinearMap.mkContinuous
    { toFun := fun φ => D u φ m
      map_add' := fun a b => D_add u a b m
      map_smul' := fun c a => D_smul u c a m } ((m : ℝ) * ‖u‖ ^ (m - 1)) (by
    intro φ
    cases m with
    | zero => simp [D]
    | succ m =>
      have := norm_D_le u φ m
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Nat.add_sub_cancel]
      push_cast
      nlinarith [this])

lemma Dlin_apply (u : h) (m : ℕ) (φ : h) : Dlin u m φ = D u φ m := rfl

/-!

## B. The error term is null

-/

lemma tendsto_embed_D {m : ℕ} (K : sym h m →L[ℂ] sym h m) (hK : IsCompactOperator K) (u : h)
    {φ : ℕ → h} (hφ : Orthonormal ℂ φ) :
    Tendsto (fun j => ‖embed K (D u (φ j) m)‖) atTop (𝓝 0) := by
  set a : ℕ → sym h m := fun j => ⟨D u (φ j) m, D_mem_sym u (φ j) m⟩ with ha
  have hb : ∀ j, ‖a j‖ ≤ ‖Dlin u m‖ := fun j => by
    have := (Dlin u m).le_opNorm (φ j)
    rw [hφ.norm_eq_one j, mul_one] at this
    exact this
  have hw : ∀ g : sym h m, Tendsto (fun j => ⟪g, a j⟫_ℂ) atTop (𝓝 0) := by
    intro g
    have e : ∀ j, ⟪g, a j⟫_ℂ = ⟪ContinuousLinearMap.adjoint (Dlin u m) (g : TPow h m), φ j⟫_ℂ :=
      fun j => (ContinuousLinearMap.adjoint_inner_left (Dlin u m) (φ j) g).symm
    simp only [e]
    exact hφ.tendsto_inner_atTop_zero _
  have := hK.tendsto_norm_apply_of_weaklyNull hb hw
  refine this.congr fun j => ?_
  have hmem : (D u (φ j) m) ∈ sym h m := D_mem_sym u (φ j) m
  have e1 : (sym h m).orthogonalProjectionOnto (D u (φ j) m) = a j :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := sym h m) (a j)
  simp only [embed, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, e1,
    Submodule.norm_coe]

/-!

## C. Asymptotic intertwining

-/

/-- **Asymptotic intertwining on coherent vectors.** For an orthonormal sequence `φ_j` the
generator `gen K (k+1)` intertwines the creation operators `a†(φ_j)` with `((k+1)/(m+k+1))` times
the generator `gen K k`, up to an error that tends to zero in norm. -/
lemma tendsto_gen_cre_pow {m : ℕ} (K : sym h m →L[ℂ] sym h m) (hK : IsCompactOperator K) (u : h)
    {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (k : ℕ) :
    Tendsto (fun j =>
      ‖gen K (k + 1) (cre (φ j) (m + k) ⟨pow u (m + k), pow_mem_sym u _⟩) -
        (((k + 1 : ℂ) / (m + k + 1 : ℂ)) •
          cre (φ j) (m + k) (gen K k ⟨pow u (m + k), pow_mem_sym u _⟩))‖) atTop (𝓝 0) := by
  set c : ℝ := 1 / Real.sqrt (((m + k : ℕ) : ℝ) + 1) * ‖u‖ ^ (k + 1) with hc
  have hbound : ∀ j, ‖gen K (k + 1) (cre (φ j) (m + k) ⟨pow u (m + k), pow_mem_sym u _⟩) -
        (((k + 1 : ℂ) / (m + k + 1 : ℂ)) •
          cre (φ j) (m + k) (gen K k ⟨pow u (m + k), pow_mem_sym u _⟩))‖ ≤
      c * ‖embed K (D u (φ j) m)‖ := fun j => by
    rw [← Submodule.norm_coe, Submodule.coe_sub, Submodule.coe_smul, gen_cre_pow, norm_smul]
    simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (Real.sqrt_nonneg _)]
    calc 1 / Real.sqrt (((m + k : ℕ) : ℝ) + 1) *
          ‖symProj h (m + (k + 1)) (consIter u (embed K (D u (φ j) m)) (k + 1))‖
        ≤ 1 / Real.sqrt (((m + k : ℕ) : ℝ) + 1) *
          (‖u‖ ^ (k + 1) * ‖embed K (D u (φ j) m)‖) := by
          gcongr
          exact (Submodule.norm_starProjection_apply_le _ _).trans (norm_consIter _ _ _).le
      _ = c * ‖embed K (D u (φ j) m)‖ := by rw [hc]; ring
  have h0 := (tendsto_embed_D K hK u hφ).const_mul c
  rw [mul_zero] at h0
  exact squeeze_zero (fun j => norm_nonneg _) hbound h0

/-!

## D. From coherent vectors to the whole symmetric subspace

-/

/-- The coherent vectors span a dense subspace of the symmetric subspace. -/
lemma denseRange_coherent (n : ℕ) :
    (Submodule.span ℂ (Set.range fun z : h => (⟨pow z n, pow_mem_sym z n⟩ : sym h n))
      ).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro ψ _
  have hind : Topology.IsInducing (Subtype.val : sym h n → TPow h n) := Topology.IsInducing.subtypeVal
  rw [SetLike.mem_coe.symm.trans (Iff.rfl), Submodule.topologicalClosure_coe,
    hind.closure_eq_preimage_closure_image]
  have himg : (Subtype.val '' (Submodule.span ℂ (Set.range fun z : h =>
      (⟨pow z n, pow_mem_sym z n⟩ : sym h n)) : Set (sym h n))) =
      (Submodule.span ℂ (Set.range fun z : h => pow z n) : Set (TPow h n)) := by
    have e1 : Subtype.val '' (Submodule.span ℂ (Set.range fun z : h =>
        (⟨pow z n, pow_mem_sym z n⟩ : sym h n)) : Set (sym h n)) =
        ((Submodule.span ℂ (Set.range fun z : h =>
          (⟨pow z n, pow_mem_sym z n⟩ : sym h n))).map (sym h n).subtype : Set (TPow h n)) :=
      by rw [Submodule.map_coe]; rfl
    rw [e1, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [himg]
  show (ψ : TPow h n) ∈ closure (Submodule.span ℂ (Set.range fun z : h => pow z n) : Set (TPow h n))
  have : (ψ : TPow h n) ∈ sym h n := ψ.2
  exact this

/-- **Pointwise convergence from coherent vectors.** A uniformly bounded sequence of operators on
the symmetric subspace that tends to zero on every coherent vector tends to zero everywhere. -/
lemma tendsto_zero_of_coherent {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : ℕ → sym h n →L[ℂ] F) {C : ℝ} (hC : ∀ j, ‖A j‖ ≤ C)
    (hcoh : ∀ z : h, Tendsto (fun j => A j ⟨pow z n, pow_mem_sym z n⟩) atTop (𝓝 0))
    (ψ : sym h n) : Tendsto (fun j => A j ψ) atTop (𝓝 0) := by
  let Q : Submodule ℂ (sym h n) :=
    { carrier := {ψ | Tendsto (fun j => A j ψ) atTop (𝓝 0)}
      add_mem' := fun {a b} ha hb => by simpa using ha.add hb
      zero_mem' := by simp
      smul_mem' := fun c a ha => by simpa using ha.const_smul c }
  have hclosed : IsClosed (Q : Set (sym h n)) := by
    refine isClosed_of_closure_subset fun ψ hψ => ?_
    show Tendsto (fun j => A j ψ) atTop (𝓝 0)
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨ψ', hψ'Q, hψ'⟩ := Metric.mem_closure_iff.mp hψ (ε / (2 * (|C| + 1))) (by positivity)
    have hQ : Tendsto (fun j => A j ψ') atTop (𝓝 0) := hψ'Q
    rw [Metric.tendsto_nhds] at hQ
    filter_upwards [hQ (ε / 2) (by positivity)] with j hj
    rw [dist_zero_right] at hj ⊢
    have h1 : ‖A j (ψ - ψ')‖ ≤ |C| * ‖ψ - ψ'‖ :=
      ((A j).le_opNorm _).trans (mul_le_mul_of_nonneg_right ((hC j).trans (le_abs_self C))
        (norm_nonneg _))
    have h2 : |C| * ‖ψ - ψ'‖ < ε / 2 := by
      rw [← dist_eq_norm]
      calc |C| * dist ψ ψ' ≤ (|C| + 1) * dist ψ ψ' :=
            mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
        _ < (|C| + 1) * (ε / (2 * (|C| + 1))) := by
            exact mul_lt_mul_of_pos_left hψ' (by positivity)
        _ = ε / 2 := by field_simp
    calc ‖A j ψ‖ = ‖A j (ψ - ψ') + A j ψ'‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖A j (ψ - ψ')‖ + ‖A j ψ'‖ := norm_add_le _ _
      _ < ε := by linarith
  have hspan : (Submodule.span ℂ (Set.range fun z : h =>
      (⟨pow z n, pow_mem_sym z n⟩ : sym h n))) ≤ Q := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, rfl⟩
    exact hcoh z
  have := Submodule.topologicalClosure_minimal _ hspan hclosed
  rw [denseRange_coherent] at this
  exact this (Submodule.mem_top (x := ψ))

lemma norm_consL_le (φ : h) (n : ℕ) : ‖consL φ n‖ ≤ ‖φ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => by
    rw [consL_apply, norm_cons]

lemma norm_cre_le (φ : h) (n : ℕ) : ‖cre φ n‖ ≤ Real.sqrt (n + 1) * ‖φ‖ := by
  rw [cre, LinearIsometryEquiv.norm_map]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have h1 : ‖contr φ n (x : TPow h (n + 1))‖ ≤ ‖φ‖ * ‖x‖ := by
    refine ((contr φ n).le_opNorm _).trans ?_
    rw [contr, LinearIsometryEquiv.norm_map, Submodule.norm_coe]
    exact mul_le_mul_of_nonneg_right (norm_consL_le φ n) (norm_nonneg _)
  simp only [ann, smul_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h2 : ‖(sym h n).orthogonalProjectionOnto (contr φ n (x : TPow h (n + 1)))‖ ≤
      ‖contr φ n (x : TPow h (n + 1))‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (Submodule.orthogonalProjectionOnto_norm_le _))
  calc Real.sqrt (n + 1) * ‖(sym h n).orthogonalProjectionOnto (contr φ n (x : TPow h (n + 1)))‖
      ≤ Real.sqrt (n + 1) * (‖φ‖ * ‖x‖) := by gcongr; exact h2.trans h1
    _ = Real.sqrt (n + 1) * ‖φ‖ * ‖x‖ := by ring

/-- **Asymptotic intertwining on the whole symmetric subspace.** -/
theorem tendsto_gen_cre {m : ℕ} (K : sym h m →L[ℂ] sym h m) (hK : IsCompactOperator K)
    {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (k : ℕ) (ψ : sym h (m + k)) :
    Tendsto (fun j => gen K (k + 1) (cre (φ j) (m + k) ψ) -
        (((k + 1 : ℂ) / (m + k + 1 : ℂ)) • cre (φ j) (m + k) (gen K k ψ))) atTop (𝓝 0) := by
  set c : ℂ := (k + 1 : ℂ) / (m + k + 1 : ℂ) with hc
  let A : ℕ → sym h (m + k) →L[ℂ] sym h (m + (k + 1)) := fun j =>
    gen K (k + 1) ∘L cre (φ j) (m + k) - c • (cre (φ j) (m + k) ∘L gen K k)
  have hcn : ‖c‖ ≤ 1 := by
    rw [hc, norm_div]
    have h1 : ‖(k + 1 : ℂ)‖ = (k : ℝ) + 1 := by
      have : (k + 1 : ℂ) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : ‖(m + k + 1 : ℂ)‖ = (m : ℝ) + k + 1 := by
      have : (m + k + 1 : ℂ) = (((m : ℝ) + k + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h1, h2, div_le_one (by positivity)]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hbound : ∀ j, ‖A j‖ ≤ 2 * ‖K‖ * Real.sqrt (((m + k : ℕ) : ℝ) + 1) := fun j => by
    have hcre : ‖cre (φ j) (m + k)‖ ≤ Real.sqrt (((m + k : ℕ) : ℝ) + 1) := by
      simpa [hφ.norm_eq_one j] using norm_cre_le (φ j) (m + k)
    have hg1 : ‖gen K (k + 1)‖ ≤ ‖K‖ := norm_gen_le K (k + 1)
    have hg2 : ‖gen K k‖ ≤ ‖K‖ := norm_gen_le K k
    have hs := Real.sqrt_nonneg (((m + k : ℕ) : ℝ) + 1)
    have hK0 := ContinuousLinearMap.opNorm_nonneg K
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ψ => ?_
    simp only [A, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply]
    have e1 : ‖gen K (k + 1) (cre (φ j) (m + k) ψ)‖ ≤ ‖K‖ * (Real.sqrt (((m + k : ℕ) : ℝ) + 1) * ‖ψ‖) :=
      ((gen K (k + 1)).le_opNorm _).trans (mul_le_mul hg1
        (((cre (φ j) (m + k)).le_opNorm ψ).trans (mul_le_mul_of_nonneg_right hcre (norm_nonneg _)))
        (norm_nonneg _) hK0)
    have e2 : ‖c • cre (φ j) (m + k) (gen K k ψ)‖ ≤
        Real.sqrt (((m + k : ℕ) : ℝ) + 1) * (‖K‖ * ‖ψ‖) := by
      rw [norm_smul]
      calc ‖c‖ * ‖cre (φ j) (m + k) (gen K k ψ)‖
          ≤ 1 * (Real.sqrt (((m + k : ℕ) : ℝ) + 1) * (‖K‖ * ‖ψ‖)) := by
            gcongr
            exact ((cre (φ j) (m + k)).le_opNorm _).trans (mul_le_mul hcre
              (((gen K k).le_opNorm ψ).trans (mul_le_mul_of_nonneg_right hg2 (norm_nonneg _)))
              (norm_nonneg _) hs)
        _ = _ := one_mul _
    calc _ ≤ ‖gen K (k + 1) (cre (φ j) (m + k) ψ)‖ + ‖c • cre (φ j) (m + k) (gen K k ψ)‖ :=
          norm_sub_le _ _
      _ ≤ 2 * ‖K‖ * Real.sqrt (((m + k : ℕ) : ℝ) + 1) * ‖ψ‖ := by nlinarith [e1, e2]
  have hcoh : ∀ z : h, Tendsto (fun j => A j ⟨pow z (m + k), pow_mem_sym z _⟩) atTop (𝓝 0) := by
    intro z
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_gen_cre_pow K hK z hφ k
  exact tendsto_zero_of_coherent A hbound hcoh ψ

lemma norm_ann_le (φ : h) (n : ℕ) : ‖ann φ n‖ ≤ Real.sqrt (n + 1) * ‖φ‖ := by
  have := norm_cre_le φ n
  rwa [cre, LinearIsometryEquiv.norm_map] at this

/-- **Annihilating along an orthonormal sequence tends to zero.** -/
lemma tendsto_ann {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (n : ℕ) (g : sym h (n + 1)) :
    Tendsto (fun j => ann (φ j) n g) atTop (𝓝 0) := by
  refine tendsto_zero_of_coherent (fun j => ann (φ j) n) (C := Real.sqrt (n + 1)) (fun j => ?_)
    (fun z => ?_) g
  · simpa [hφ.norm_eq_one j] using norm_ann_le (φ j) n
  · simp only [ann_pow]
    have h1 : Tendsto (fun j => ⟪φ j, z⟫_ℂ) atTop (𝓝 0) := by
      have := (hφ.tendsto_inner_atTop_zero z).star
      simpa using this
    simpa using (h1.const_mul ((Real.sqrt (n + 1) : ℝ) : ℂ)).smul_const
      (⟨pow z n, pow_mem_sym z n⟩ : sym h n)

/-- **A compact operator kills the creation vectors along an orthonormal sequence.** -/
lemma tendsto_apply_cre_of_compact {n : ℕ} (K : sym h (n + 1) →L[ℂ] sym h (n + 1))
    (hK : IsCompactOperator K) {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (ψ : sym h n) :
    Tendsto (fun j => ‖K (cre (φ j) n ψ)‖) atTop (𝓝 0) := by
  refine hK.tendsto_norm_apply_of_weaklyNull (C := Real.sqrt (n + 1) * ‖ψ‖) (fun j => ?_) ?_
  · refine ((cre (φ j) n).le_opNorm ψ).trans ?_
    have := norm_cre_le (φ j) n
    rw [hφ.norm_eq_one j, mul_one] at this
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  · intro g
    have e : ∀ j, ⟪g, cre (φ j) n ψ⟫_ℂ = ⟪ann (φ j) n g, ψ⟫_ℂ := fun j =>
      ContinuousLinearMap.adjoint_inner_right (ann (φ j) n) g ψ
    simp only [e]
    have := Filter.Tendsto.inner (𝕜 := ℂ) (tendsto_ann hφ n g) (tendsto_const_nhds (x := ψ))
    simpa using this

/-- The Gram matrix of creation vectors of coherent vectors is exact. -/
lemma inner_cre_pow (φ v w : h) (n : ℕ) :
    ⟪cre φ n ⟨pow v n, pow_mem_sym v n⟩, cre φ n ⟨pow w n, pow_mem_sym w n⟩⟫_ℂ =
      ⟪φ, φ⟫_ℂ * ⟪v, w⟫_ℂ ^ n + n * (⟪φ, w⟫_ℂ * ⟪v, φ⟫_ℂ * ⟪v, w⟫_ℂ ^ (n - 1)) := by
  rw [cre_pow, cre_pow]
  have hne : ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs : ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ) * (Real.sqrt ((n : ℝ) + 1) : ℝ) = n + 1 := by
    exact_mod_cast Real.mul_self_sqrt (by positivity)
  show ⟪(1 / ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ)) • D v φ (n + 1),
    (1 / ((Real.sqrt ((n : ℝ) + 1) : ℝ) : ℂ)) • D w φ (n + 1)⟫_ℂ = _
  rw [inner_smul_left, inner_smul_right, inner_D_D]
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [map_div₀, map_one, Complex.conj_ofReal]
  field_simp
  rw [← hs]
  ring

/-- Creation vectors of an orthonormal sequence of coherent vectors have asymptotically the
overlaps of the coherent vectors. -/
lemma tendsto_inner_cre_pow {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (v w : h) (n : ℕ) :
    Tendsto (fun j => ⟪cre (φ j) n ⟨pow v n, pow_mem_sym v n⟩,
      cre (φ j) n ⟨pow w n, pow_mem_sym w n⟩⟫_ℂ) atTop (𝓝 (⟪v, w⟫_ℂ ^ n)) := by
  simp only [inner_cre_pow]
  have h1 : Tendsto (fun j => ⟪φ j, w⟫_ℂ) atTop (𝓝 0) := by
    simpa using (hφ.tendsto_inner_atTop_zero w).star
  have h2 : Tendsto (fun j => ⟪v, φ j⟫_ℂ) atTop (𝓝 0) := hφ.tendsto_inner_atTop_zero v
  have h3 : ∀ j, ⟪φ j, φ j⟫_ℂ = 1 := fun j => by
    rw [inner_self_eq_norm_sq_to_K, hφ.norm_eq_one j]; simp
  simp only [h3, one_mul]
  have := (((h1.mul h2).mul_const (⟪v, w⟫_ℂ ^ (n - 1))).const_mul (n : ℂ)).const_add (⟪v, w⟫_ℂ ^ n)
  simpa using this

/-- **Creation along an orthonormal sequence is asymptotically isometric**:
`⟪a†(φ_j) x, a†(φ_j) z⟫ → ⟪x, z⟫`. -/
theorem tendsto_inner_cre {φ : ℕ → h} (hφ : Orthonormal ℂ φ) (n : ℕ) (x z : sym h n) :
    Tendsto (fun j => ⟪cre (φ j) n x, cre (φ j) n z⟫_ℂ) atTop (𝓝 ⟪x, z⟫_ℂ) := by
  -- first: `z` coherent, `x` arbitrary, expressed in the linear variable `x`
  have step1 : ∀ (w : h) (x : sym h n),
      Tendsto (fun j => ⟪cre (φ j) n ⟨pow w n, pow_mem_sym w n⟩, cre (φ j) n x⟫_ℂ) atTop
        (𝓝 ⟪(⟨pow w n, pow_mem_sym w n⟩ : sym h n), x⟫_ℂ) := by
    intro w x
    let A : ℕ → sym h n →L[ℂ] ℂ := fun j =>
      (innerSL ℂ (cre (φ j) n ⟨pow w n, pow_mem_sym w n⟩)) ∘L cre (φ j) n -
        innerSL ℂ (⟨pow w n, pow_mem_sym w n⟩ : sym h n)
    have hb : ∀ j, ‖A j‖ ≤ (Real.sqrt (n + 1) * ‖pow w n‖) * Real.sqrt (n + 1) + ‖pow w n‖ := by
      intro j
      have hcre : ‖cre (φ j) n‖ ≤ Real.sqrt (n + 1) := by
        simpa [hφ.norm_eq_one j] using norm_cre_le (φ j) n
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
      simp only [A, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
      have e1 : ‖⟪cre (φ j) n ⟨pow w n, pow_mem_sym w n⟩, cre (φ j) n y⟫_ℂ‖ ≤
          (Real.sqrt (n + 1) * ‖pow w n‖) * (Real.sqrt (n + 1) * ‖y‖) := by
        refine (norm_inner_le_norm _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity))
        · exact ((cre (φ j) n).le_opNorm _).trans (mul_le_mul_of_nonneg_right hcre (norm_nonneg _))
        · exact ((cre (φ j) n).le_opNorm _).trans (mul_le_mul_of_nonneg_right hcre (norm_nonneg _))
      have e2 : ‖⟪(⟨pow w n, pow_mem_sym w n⟩ : sym h n), y⟫_ℂ‖ ≤ ‖pow w n‖ * ‖y‖ :=
        norm_inner_le_norm _ _
      calc _ ≤ ‖⟪cre (φ j) n ⟨pow w n, pow_mem_sym w n⟩, cre (φ j) n y⟫_ℂ‖ +
            ‖⟪(⟨pow w n, pow_mem_sym w n⟩ : sym h n), y⟫_ℂ‖ := norm_sub_le _ _
        _ ≤ _ := by nlinarith [e1, e2, norm_nonneg y]
    have hc : ∀ v : h, Tendsto (fun j => A j ⟨pow v n, pow_mem_sym v n⟩) atTop (𝓝 0) := by
      intro v
      have := (tendsto_inner_cre_pow hφ w v n).sub_const (⟪w, v⟫_ℂ ^ n)
      simp only [sub_self] at this
      simpa [A, inner_pow] using this
    have := tendsto_zero_of_coherent A hb hc x
    simp only [A, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply] at this
    simpa using this.add_const ⟪(⟨pow w n, pow_mem_sym w n⟩ : sym h n), x⟫_ℂ
  -- second: `z` arbitrary, linear in `z`
  let B : ℕ → sym h n →L[ℂ] ℂ := fun j =>
    (innerSL ℂ (cre (φ j) n x)) ∘L cre (φ j) n - innerSL ℂ x
  have hb : ∀ j, ‖B j‖ ≤ (Real.sqrt (n + 1) * ‖x‖) * Real.sqrt (n + 1) + ‖x‖ := by
    intro j
    have hcre : ‖cre (φ j) n‖ ≤ Real.sqrt (n + 1) := by
      simpa [hφ.norm_eq_one j] using norm_cre_le (φ j) n
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
    simp only [B, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    have e1 : ‖⟪cre (φ j) n x, cre (φ j) n y⟫_ℂ‖ ≤
        (Real.sqrt (n + 1) * ‖x‖) * (Real.sqrt (n + 1) * ‖y‖) := by
      refine (norm_inner_le_norm _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity))
      · exact ((cre (φ j) n).le_opNorm _).trans (mul_le_mul_of_nonneg_right hcre (norm_nonneg _))
      · exact ((cre (φ j) n).le_opNorm _).trans (mul_le_mul_of_nonneg_right hcre (norm_nonneg _))
    have e2 : ‖⟪x, y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
    calc _ ≤ ‖⟪cre (φ j) n x, cre (φ j) n y⟫_ℂ‖ + ‖⟪x, y⟫_ℂ‖ := norm_sub_le _ _
      _ ≤ _ := by nlinarith [e1, e2, norm_nonneg y]
  have hc : ∀ w : h, Tendsto (fun j => B j ⟨pow w n, pow_mem_sym w n⟩) atTop (𝓝 0) := by
    intro w
    have h1 := (step1 w x).star
    have h2 : ∀ j, star ⟪cre (φ j) n ⟨pow w n, pow_mem_sym w n⟩, cre (φ j) n x⟫_ℂ =
        ⟪cre (φ j) n x, cre (φ j) n ⟨pow w n, pow_mem_sym w n⟩⟫_ℂ := fun j => inner_conj_symm _ _
    simp only [h2] at h1
    have h3 : star ⟪(⟨pow w n, pow_mem_sym w n⟩ : sym h n), x⟫_ℂ =
        ⟪x, (⟨pow w n, pow_mem_sym w n⟩ : sym h n)⟫_ℂ := inner_conj_symm _ _
    rw [h3] at h1
    have := h1.sub_const ⟪x, (⟨pow w n, pow_mem_sym w n⟩ : sym h n)⟫_ℂ
    simp only [sub_self] at this
    simpa [B] using this
  have := tendsto_zero_of_coherent B hb hc z
  simp only [B, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply] at this
  simpa using this.add_const ⟪x, z⟫_ℂ

end HilbertPower
