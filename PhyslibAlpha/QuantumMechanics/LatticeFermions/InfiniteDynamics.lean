/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.LatticeFermions.ThermodynamicLimit
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.Automorphism
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!

# The infinite-volume dynamics

For a locally finite interaction bounded by `J`, the limit `α_t(B) = lim_{Λ ↑ V} α_t^Λ(B)` exists
for every quasi-local `B`, uniformly for `t` in compact intervals, and defines a strongly
continuous one-parameter group of `⋆`-automorphisms of the quasi-local algebra which commutes
with the parity. Local observables are differentiable at `t = 0`, with derivative given by the
commutator with the finitely many terms meeting their support.

## i. Overview

The finite-volume dynamics of a local observable are uniformly Cauchy on compact time intervals
(`Interaction.uniformCauchySeqOn_evolution`). Since every `α_t^Λ` is isometric, the same holds for
every quasi-local `B`, approximated in norm by local observables. The limit is taken along the
filter `atTop` of finite regions, so it is the same along every exhaustion `Λ_n ↑ V`.

The algebraic properties pass to the limit: `α_t` is a `⋆`-homomorphism and isometric, `α_0 = id`,
and `α_{s+t} = α_s ∘ α_t` because `‖α_s^Λ(α_t^Λ(B)) - α_s^Λ(α_t(B))‖ = ‖α_t^Λ(B) - α_t(B)‖`. So
`α_t` is a `⋆`-automorphism of the quasi-local algebra with inverse `α_{-t}`. The parity commutes
with every `α_t^Λ`, since `H_Λ` is even, and so with `α_t`. A uniform limit of continuous
functions is continuous, so `t ↦ α_t(B)` is continuous.

For `A ∈ 𝔄_X` let `R ⊇ X` be the sites reached from `X` by one nonzero interaction term. For
`Λ ⊇ R`, `[H_Λ, A] = [H_R, A]`, and this is
`δ(A) = i Σ_{Z ∩ X ≠ ∅} [Φ(Z), A] + i Σ_{x ∈ X} [D_x, A]`. The second order Taylor estimate
`‖α_t^Λ(A) - A - t δ(A)‖ ≤ t² ‖[H_Λ, δ(A)]‖`, where the right side is again independent of `Λ`
for large `Λ`, passes to the limit and shows that `δ(A)` is the derivative of `t ↦ α_t(A)` at
zero.

## ii. Key results

- `LatticeFermions.Interaction.dynamics` : the infinite-volume dynamics `α_t`.
- `LatticeFermions.Interaction.tendstoUniformlyOn_dynamics` : uniform convergence on `[-T, T]`.
- `LatticeFermions.Interaction.tendsto_dynamics_of_tendsto` : independence of the exhaustion.
- `LatticeFermions.Interaction.dynamicsAut` : `α_t` as a `⋆`-automorphism of the quasi-local
  algebra.
- `LatticeFermions.Interaction.dynamicsGroup` : the one-parameter automorphism group.
- `LatticeFermions.Interaction.continuous_dynamics` : strong continuity.
- `LatticeFermions.Interaction.parity_dynamics` : the dynamics preserves parity.
- `LatticeFermions.Interaction.hasDerivAt_dynamics` : the generator on local observables.

## iii. Table of contents

- A. Uniform convergence on the quasi-local algebra
- B. The infinite-volume dynamics
- C. Algebraic properties
- D. The automorphism group
- E. Strong continuity, parity and exhaustions
- F. Taylor estimates for bounded Hamiltonians
- G. The generator on local observables

## iv. References

* O. Bratteli, D. W. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Theorem 6.2.11.
* B. Nachtergaele, R. Sims, A. Young, Quasi-locality bounds for quantum lattice systems. Part I,
  arXiv:1810.02428, Theorem 3.5.

-/

@[expose] public section

noncomputable section

namespace LatticeFermions

open Finset Complex Filter Topology

/-!

## F. Taylor estimates for bounded Hamiltonians

-/

section taylor

variable {𝔄 : Type*} [CStarAlgebra 𝔄]

lemma evolution_zero_hamiltonian (t : ℝ) (a : 𝔄) : evolution (0 : selfAdjoint 𝔄) t a = a := by
  simp [evolution_apply, propagator_coe]

/-- First order Taylor estimate `‖α_t(a) - a‖ ≤ ‖[H, a]‖ t` for `t ≥ 0`. -/
lemma norm_evolution_sub_self_le (H : selfAdjoint 𝔄) (a : 𝔄) {t : ℝ} (ht : 0 ≤ t) :
    ‖evolution H t a - a‖ ≤ ‖(H : 𝔄) * a - a * H‖ * t := by
  have h := norm_evolution_sub_evolution_le 0 H a ht (C := ‖(H : 𝔄) * a - a * H‖)
    fun r _ _ => by simp [evolution_zero_hamiltonian]
  simpa [evolution_zero_hamiltonian] using h

lemma hasDerivAt_evolution_sub_smul (H : selfAdjoint 𝔄) (a d : 𝔄) (s : ℝ) :
    HasDerivAt (fun r => evolution H r a - r • d)
      (evolution H s (I • ((H : 𝔄) * a - a * H)) - d) s := by
  have h := (hasDerivAt_evolution H a s).sub ((hasDerivAt_id s).smul_const d)
  convert h using 1
  · rfl
  · rw [one_smul]

/-- Second order Taylor estimate `‖α_t(a) - a - t δ(a)‖ ≤ ‖[H, δ(a)]‖ t²` for `t ≥ 0`, where
`δ(a) = i[H, a]`. -/
lemma norm_evolution_sub_sub_le (H : selfAdjoint 𝔄) (a : 𝔄) {t : ℝ} (ht : 0 ≤ t) :
    ‖evolution H t a - a - t • (I • ((H : 𝔄) * a - a * H))‖ ≤
      ‖(H : 𝔄) * (I • ((H : 𝔄) * a - a * H)) - (I • ((H : 𝔄) * a - a * H)) * H‖ * t ^ 2 := by
  set d := I • ((H : 𝔄) * a - a * H)
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun r => evolution H r a - r • d) (C := ‖(H : 𝔄) * d - d * H‖ * t)
    (fun s _ => (hasDerivAt_evolution_sub_smul H a d s).hasDerivWithinAt)
    (fun s hs => (norm_evolution_sub_self_le H d hs.1).trans
      (mul_le_mul_of_nonneg_left hs.2.le (norm_nonneg _))) t ⟨ht, le_rfl⟩
  simp only [evolution_zero, zero_smul, sub_zero] at h
  calc _ = ‖evolution H t a - t • d - a‖ := by congr 1; abel
    _ ≤ _ := h.trans_eq (by ring)

/-- The second order Taylor estimate for all `t`. -/
lemma norm_evolution_sub_sub_le' (H : selfAdjoint 𝔄) (a : 𝔄) (t : ℝ) :
    ‖evolution H t a - a - t • (I • ((H : 𝔄) * a - a * H))‖ ≤
      ‖(H : 𝔄) * (I • ((H : 𝔄) * a - a * H)) - (I • ((H : 𝔄) * a - a * H)) * H‖ * t ^ 2 := by
  rcases le_total 0 t with ht | ht
  · exact norm_evolution_sub_sub_le H a ht
  · have h := norm_evolution_sub_sub_le (-H) a (neg_nonneg.mpr ht)
    have hd : I • (((-H : selfAdjoint 𝔄) : 𝔄) * a - a * ((-H : selfAdjoint 𝔄) : 𝔄)) =
        -(I • ((H : 𝔄) * a - a * H)) := by
      simp only [AddSubgroup.coe_neg, neg_mul, mul_neg, smul_sub, smul_neg]
      abel
    rw [evolution_neg_hamiltonian, neg_neg, hd] at h
    simpa only [neg_smul_neg, AddSubgroup.coe_neg, neg_mul_neg, neg_sq] using h

end taylor

namespace Interaction

variable {V : Type*} [DecidableEq V] {𝔄 : Type*} [CStarAlgebra 𝔄] {N : GradedLocalNet V 𝔄}
  {Φ : Interaction N} {J : ℝ} (hJ : Φ.IsBoundedBy J) (hfin : Φ.LocallyFinite)

/-!

## A. Uniform convergence on the quasi-local algebra

-/

omit [DecidableEq V] in
lemma dist_evolution_evolution (Λ : Finset V) (t : ℝ) (a b : 𝔄) :
    dist (evolution (Φ.hamiltonian Λ) t a) (evolution (Φ.hamiltonian Λ) t b) = dist a b := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_evolution]

include hJ hfin in
/-- The finite-volume dynamics of a quasi-local element are uniformly Cauchy on `[-T, T]`. -/
lemma uniformCauchySeqOn_evolution_of_mem_quasiLocal {B : 𝔄} (hB : B ∈ N.quasiLocal) (T : ℝ) :
    UniformCauchySeqOn (fun Λ t => evolution (Φ.hamiltonian Λ) t B) atTop (Set.Icc (-T) T) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨A, hA, hBA⟩ := Metric.mem_closure_iff.mp hB (ε / 3) (by positivity)
  obtain ⟨X, hAX⟩ := N.mem_localUnion_iff.mp hA
  obtain ⟨Λ₀, hΛ₀⟩ := Metric.uniformCauchySeqOn_iff.mp
    (uniformCauchySeqOn_evolution hfin hJ hAX T) (ε / 3) (by positivity)
  refine ⟨Λ₀, fun m hm n hn t ht => ?_⟩
  calc dist (evolution (Φ.hamiltonian m) t B) (evolution (Φ.hamiltonian n) t B)
      ≤ dist (evolution (Φ.hamiltonian m) t B) (evolution (Φ.hamiltonian m) t A) +
        dist (evolution (Φ.hamiltonian m) t A) (evolution (Φ.hamiltonian n) t A) +
        dist (evolution (Φ.hamiltonian n) t A) (evolution (Φ.hamiltonian n) t B) :=
        dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
        rw [dist_evolution_evolution, dist_evolution_evolution, dist_comm A B]
        gcongr
        exact hΛ₀ m hm n hn t ht
    _ = ε := by ring

/-!

## B. The infinite-volume dynamics

-/

variable (Φ) in
/-- The infinite-volume dynamics `α_t(B) = lim_{Λ ↑ V} α_t^Λ(B)`, the limit along the finite
regions directed by inclusion. It is the limit for every quasi-local `B`. -/
def dynamics (t : ℝ) (B : 𝔄) : 𝔄 :=
  limUnder atTop fun Λ : Finset V => evolution (Φ.hamiltonian Λ) t B

include hJ hfin in
/-- The finite-volume dynamics of a quasi-local element converge to the infinite-volume dynamics
in norm, uniformly for `t ∈ [-T, T]`. -/
theorem tendstoUniformlyOn_dynamics {B : 𝔄} (hB : B ∈ N.quasiLocal) (T : ℝ) :
    TendstoUniformlyOn (fun Λ t => evolution (Φ.hamiltonian Λ) t B) (fun t => Φ.dynamics t B)
      atTop (Set.Icc (-T) T) := by
  have hu := uniformCauchySeqOn_evolution_of_mem_quasiLocal hJ hfin hB T
  exact hu.tendstoUniformlyOn_of_tendsto fun t ht =>
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (hu.cauchySeq ht))

include hJ hfin in
/-- The finite-volume dynamics of a quasi-local element converge in norm. -/
lemma tendsto_dynamics {B : 𝔄} (hB : B ∈ N.quasiLocal) (t : ℝ) :
    Tendsto (fun Λ : Finset V => evolution (Φ.hamiltonian Λ) t B) atTop
      (𝓝 (Φ.dynamics t B)) :=
  (tendstoUniformlyOn_dynamics hJ hfin hB |t|).tendsto_at
    ⟨neg_abs_le t, le_abs_self t⟩

/-!

## C. Algebraic properties

-/

omit [DecidableEq V] in
lemma evolution_mem_quasiLocal (Λ : Finset V) (t : ℝ) {B : 𝔄} (hB : B ∈ N.quasiLocal) :
    evolution (Φ.hamiltonian Λ) t B ∈ N.quasiLocal :=
  evolution_mem _ t N.isClosed_quasiLocal (N.loc_le_quasiLocal Λ (Φ.hamiltonian_mem Λ)) hB

include hJ hfin in
lemma dynamics_mem {B : 𝔄} (hB : B ∈ N.quasiLocal) (t : ℝ) : Φ.dynamics t B ∈ N.quasiLocal :=
  N.isClosed_quasiLocal.mem_of_tendsto (tendsto_dynamics hJ hfin hB t)
    (Eventually.of_forall fun Λ => evolution_mem_quasiLocal Λ t hB)

include hJ hfin in
lemma dynamics_mul {a b : 𝔄} (ha : a ∈ N.quasiLocal) (hb : b ∈ N.quasiLocal) (t : ℝ) :
    Φ.dynamics t (a * b) = Φ.dynamics t a * Φ.dynamics t b :=
  tendsto_nhds_unique (tendsto_dynamics hJ hfin (N.quasiLocal.mul_mem ha hb) t)
    (by simpa only [map_mul] using
      ((tendsto_dynamics hJ hfin ha t).mul (tendsto_dynamics hJ hfin hb t)))

include hJ hfin in
lemma dynamics_add {a b : 𝔄} (ha : a ∈ N.quasiLocal) (hb : b ∈ N.quasiLocal) (t : ℝ) :
    Φ.dynamics t (a + b) = Φ.dynamics t a + Φ.dynamics t b :=
  tendsto_nhds_unique (tendsto_dynamics hJ hfin (N.quasiLocal.add_mem ha hb) t)
    (by simpa only [map_add] using
      ((tendsto_dynamics hJ hfin ha t).add (tendsto_dynamics hJ hfin hb t)))

include hJ hfin in
lemma dynamics_smul (c : ℂ) {a : 𝔄} (ha : a ∈ N.quasiLocal) (t : ℝ) :
    Φ.dynamics t (c • a) = c • Φ.dynamics t a :=
  tendsto_nhds_unique (tendsto_dynamics hJ hfin (N.quasiLocal.smul_mem ha c) t)
    (by simpa only [map_smul] using (tendsto_dynamics hJ hfin ha t).const_smul c)

include hJ hfin in
lemma dynamics_star {a : 𝔄} (ha : a ∈ N.quasiLocal) (t : ℝ) :
    Φ.dynamics t (star a) = star (Φ.dynamics t a) :=
  tendsto_nhds_unique (tendsto_dynamics hJ hfin (star_mem ha) t)
    (by simpa only [map_star] using (tendsto_dynamics hJ hfin ha t).star)

include hJ hfin in
lemma dynamics_one (t : ℝ) : Φ.dynamics t (1 : 𝔄) = 1 :=
  tendsto_nhds_unique (tendsto_dynamics hJ hfin N.quasiLocal.one_mem t)
    (by simpa only [map_one] using tendsto_const_nhds)

include hJ hfin in
/-- The infinite-volume dynamics is isometric. -/
lemma norm_dynamics {a : 𝔄} (ha : a ∈ N.quasiLocal) (t : ℝ) : ‖Φ.dynamics t a‖ = ‖a‖ :=
  tendsto_nhds_unique (tendsto_dynamics hJ hfin ha t).norm
    (by simpa only [norm_evolution] using tendsto_const_nhds)

include hJ hfin in
lemma dynamics_zero {a : 𝔄} (ha : a ∈ N.quasiLocal) : Φ.dynamics 0 a = a :=
  tendsto_nhds_unique (tendsto_dynamics hJ hfin ha 0)
    (by simpa only [evolution_zero] using tendsto_const_nhds)

include hJ hfin in
/-- The group law `α_{s+t} = α_s ∘ α_t`. -/
lemma dynamics_add_time {a : 𝔄} (ha : a ∈ N.quasiLocal) (s t : ℝ) :
    Φ.dynamics (s + t) a = Φ.dynamics s (Φ.dynamics t a) := by
  refine tendsto_nhds_unique (tendsto_dynamics hJ hfin ha (s + t)) ?_
  simp only [evolution_add]
  refine (tendsto_dynamics hJ hfin (dynamics_mem hJ hfin ha t) s).congr_dist ?_
  simp only [dist_evolution_evolution]
  exact tendsto_iff_dist_tendsto_zero.mp (tendsto_dynamics hJ hfin ha t) |>.congr
    fun Λ => dist_comm _ _

include hJ hfin in
lemma dynamics_neg_dynamics {a : 𝔄} (ha : a ∈ N.quasiLocal) (t : ℝ) :
    Φ.dynamics (-t) (Φ.dynamics t a) = a := by
  rw [← dynamics_add_time hJ hfin ha, neg_add_cancel, dynamics_zero hJ hfin ha]

include hJ hfin in
lemma dynamics_dynamics_neg {a : 𝔄} (ha : a ∈ N.quasiLocal) (t : ℝ) :
    Φ.dynamics t (Φ.dynamics (-t) a) = a := by
  rw [← dynamics_add_time hJ hfin ha, add_neg_cancel, dynamics_zero hJ hfin ha]

/-!

## D. The automorphism group

-/

/-- The infinite-volume dynamics `α_t` as a `⋆`-automorphism of the quasi-local algebra, with
inverse `α_{-t}`. -/
def dynamicsAut (t : ℝ) : N.quasiLocal ≃⋆ₐ[ℂ] N.quasiLocal where
  toFun a := ⟨Φ.dynamics t a, dynamics_mem hJ hfin a.2 t⟩
  invFun a := ⟨Φ.dynamics (-t) a, dynamics_mem hJ hfin a.2 (-t)⟩
  left_inv a := Subtype.ext (dynamics_neg_dynamics hJ hfin a.2 t)
  right_inv a := Subtype.ext (dynamics_dynamics_neg hJ hfin a.2 t)
  map_mul' a b := Subtype.ext (dynamics_mul hJ hfin a.2 b.2 t)
  map_add' a b := Subtype.ext (dynamics_add hJ hfin a.2 b.2 t)
  map_star' a := Subtype.ext (dynamics_star hJ hfin a.2 t)
  map_smul' c a := Subtype.ext (dynamics_smul hJ hfin c a.2 t)

lemma dynamicsAut_apply (t : ℝ) (a : N.quasiLocal) :
    (dynamicsAut hJ hfin t a : 𝔄) = Φ.dynamics t a := rfl

/-- The infinite-volume dynamics as a one-parameter group of `⋆`-automorphisms of the
quasi-local algebra. -/
def dynamicsGroup : ProbabilisticTheory.AutomorphismGroup N.quasiLocal where
  toFun := dynamicsAut hJ hfin
  map_zero_apply a := Subtype.ext (dynamics_zero hJ hfin a.2)
  map_add_apply s t a := Subtype.ext (dynamics_add_time hJ hfin a.2 s t)

/-!

## E. Strong continuity, parity and exhaustions

-/

include hJ hfin in
/-- Strong continuity: `t ↦ α_t(a)` is norm continuous for every quasi-local `a`. -/
lemma continuous_dynamics {a : 𝔄} (ha : a ∈ N.quasiLocal) :
    Continuous fun t => Φ.dynamics t a := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  have h := (tendstoUniformlyOn_dynamics hJ hfin ha (|t| + 1)).continuousOn
    (Frequently.of_forall fun Λ => (continuous_evolution _ a).continuousOn)
  exact h.continuousAt (Icc_mem_nhds (by linarith [neg_abs_le t]) (by linarith [le_abs_self t]))

lemma continuous_dynamicsAut (a : N.quasiLocal) :
    Continuous fun t => dynamicsAut hJ hfin t a :=
  (continuous_dynamics hJ hfin a.2).subtype_mk _

include hJ hfin in
/-- The dynamics commutes with the parity. -/
lemma parity_dynamics {a : 𝔄} (ha : a ∈ N.quasiLocal) (t : ℝ) :
    N.parity (Φ.dynamics t a) = Φ.dynamics t (N.parity a) :=
  tendsto_nhds_unique (((StarAlgEquiv.isometry N.parity).continuous.tendsto _).comp
    (tendsto_dynamics hJ hfin ha t))
    ((tendsto_dynamics hJ hfin (N.parity_mem_quasiLocal ha) t).congr fun Λ =>
      (map_evolution _ N.parity (Φ.isEven_hamiltonian Λ) t a).symm)

include hJ hfin in
/-- The dynamics maps even elements to even elements. -/
lemma isEven_dynamics {a : 𝔄} (ha : a ∈ N.quasiLocal) (hae : N.IsEven a) (t : ℝ) :
    N.IsEven (Φ.dynamics t a) := by
  rw [GradedLocalNet.IsEven, parity_dynamics hJ hfin ha, show N.parity a = a from hae]

include hJ hfin in
/-- Independence of the exhaustion: along any family of regions tending to the whole lattice,
the finite-volume dynamics converge to the same limit. -/
lemma tendsto_dynamics_of_tendsto {ι : Type*} {l : Filter ι} {Λs : ι → Finset V}
    (hΛ : Tendsto Λs l atTop) {a : 𝔄} (ha : a ∈ N.quasiLocal) (t : ℝ) :
    Tendsto (fun i => evolution (Φ.hamiltonian (Λs i)) t a) l (𝓝 (Φ.dynamics t a)) :=
  (tendsto_dynamics hJ hfin ha t).comp hΛ

include hJ hfin in
/-- Independence of the exhaustion, uniformly for `t ∈ [-T, T]`. -/
lemma tendstoUniformlyOn_dynamics_of_tendsto {ι : Type*} {l : Filter ι}
    {Λs : ι → Finset V} (hΛ : Tendsto Λs l atTop) {a : 𝔄} (ha : a ∈ N.quasiLocal) (T : ℝ) :
    TendstoUniformlyOn (fun i t => evolution (Φ.hamiltonian (Λs i)) t a)
      (fun t => Φ.dynamics t a) l (Set.Icc (-T) T) :=
  fun u hu => hΛ.eventually (tendstoUniformlyOn_dynamics hJ hfin ha T u hu)

omit [DecidableEq V] in
/-- An increasing sequence of finite regions exhausting the lattice tends to the whole
lattice. -/
lemma tendsto_atTop_of_exhaustion {Λs : ℕ → Finset V} (hmono : Monotone Λs)
    (hcov : ∀ x, ∃ n, x ∈ Λs n) : Tendsto Λs atTop atTop := by
  refine tendsto_atTop.2 fun F => ?_
  have h : ∀ x ∈ F, ∀ᶠ n in atTop, x ∈ Λs n := fun x _ =>
    let ⟨n, hn⟩ := hcov x
    eventually_atTop.2 ⟨n, fun m hm => hmono hm hn⟩
  exact ((eventually_all_finset F).2 h).mono fun n hn x hx => hn x hx

/-!

## G. The generator on local observables

-/

/-- A new term of a region containing the sites reached from `X` in one step either vanishes or
is supported away from `X`, so it commutes with `𝔄_X`. -/
lemma commute_term_of_mem_newTerms {X Λ Z : Finset V} (hZ : Z ∈ newTerms (reachStep hfin X) Λ)
    {a : 𝔄} (ha : a ∈ N.loc X) : Commute a (Φ.term Z) := by
  by_cases h0 : Φ.term Z = 0
  · rw [h0]; exact Commute.zero_right a
  · refine N.commute_of_disjoint ?_ ha (Φ.term_mem Z) (Φ.isEven_term Z)
    by_contra hd
    exact (mem_sdiff.mp hZ).2 (mem_powerset.mpr
      (subset_reachStep_of hfin h0 fun h => hd h.symm))

/-- For `Λ` containing the sites `R` reached from `X` in one step, `[H_Λ, A] = [H_R, A]` for
`A ∈ 𝔄_X`. -/
lemma commutator_hamiltonian_eq {X Λ : Finset V} (hΛ : reachStep hfin X ⊆ Λ) {a : 𝔄}
    (ha : a ∈ N.loc X) :
    (Φ.hamiltonian Λ : 𝔄) * a - a * Φ.hamiltonian Λ =
      (Φ.hamiltonian (reachStep hfin X) : 𝔄) * a - a * Φ.hamiltonian (reachStep hfin X) := by
  have hc : Commute a ((Φ.hamiltonian Λ : 𝔄) - Φ.hamiltonian (reachStep hfin X)) := by
    rw [Φ.hamiltonian_sub_hamiltonian hΛ]
    refine Commute.add_right ?_ (Commute.sum_right _ _ _ fun Z hZ =>
      commute_term_of_mem_newTerms hfin hZ ha)
    exact commute_sum_of_disjoint ha _ _ (fun x => {x})
      (fun x hx => disjoint_singleton_right.mpr fun hxX =>
        (mem_sdiff.mp hx).2 (subset_reachStep hfin X hxX))
      (fun x _ => Φ.onSite_mem x) (fun x _ => Φ.isEven_onSite x)
  have h := hc.eq
  rw [mul_sub, sub_mul] at h
  calc _ = ((Φ.hamiltonian Λ : 𝔄) - Φ.hamiltonian (reachStep hfin X)) * a -
        a * ((Φ.hamiltonian Λ : 𝔄) - Φ.hamiltonian (reachStep hfin X)) +
        ((Φ.hamiltonian (reachStep hfin X) : 𝔄) * a - a * Φ.hamiltonian (reachStep hfin X)) := by
        simp only [sub_mul, mul_sub]; abel
    _ = _ := by rw [mul_sub, sub_mul, h, sub_self, zero_add]

variable (Φ) in
/-- The generator `δ(A) = i[H_R, A]` of the dynamics on `A ∈ 𝔄_X`, where `R` is the set of sites
reached from `X` in one step. By `generator_eq` it equals
`i Σ_{Z ∩ X ≠ ∅} [Φ(Z), A] + i Σ_{x ∈ X} [D_x, A]`. -/
def generator (X : Finset V) (a : 𝔄) : 𝔄 :=
  I • ((Φ.hamiltonian (reachStep hfin X) : 𝔄) * a - a * Φ.hamiltonian (reachStep hfin X))

/-- The generator on `A ∈ 𝔄_X`: `δ(A) = i Σ_{Z ∩ X ≠ ∅} [Φ(Z), A] + i Σ_{x ∈ X} [D_x, A]`, where
the first sum runs over the subregions of the sites reached from `X` in one step, which include
every `Z` meeting `X` with `Φ(Z) ≠ 0`. -/
lemma generator_eq {X : Finset V} {a : 𝔄} (ha : a ∈ N.loc X) :
    Φ.generator hfin X a = I • (∑ Z ∈ touching (reachStep hfin X) X, (Φ.term Z * a - a * Φ.term Z) +
      ∑ x ∈ X, (Φ.onSite x * a - a * Φ.onSite x)) := by
  have hsplit := Φ.hamiltonian_sub_interactionAt (subset_reachStep hfin X)
  rw [sub_eq_iff_eq_add] at hsplit
  have hr := (Φ.commute_remainder (Λ := reachStep hfin X) ha).eq
  rw [generator, hsplit, interactionAt_coe, onSiteSum]
  simp only [add_mul, mul_add, sum_mul, mul_sum, hr]
  congr 1
  rw [sum_sub_distrib, sum_sub_distrib]
  abel

lemma generator_mem {X : Finset V} {a : 𝔄} (ha : a ∈ N.loc X) :
    Φ.generator hfin X a ∈ N.loc (reachStep hfin X) := by
  have ha' := N.loc_mono (subset_reachStep hfin X) ha
  have hH := Φ.hamiltonian_mem (reachStep hfin X)
  exact (N.loc _).smul_mem ((N.loc _).sub_mem ((N.loc _).mul_mem hH ha')
    ((N.loc _).mul_mem ha' hH)) I

include hJ in
/-- The second order Taylor estimate in infinite volume:
`‖α_t(A) - A - t δ(A)‖ ≤ ‖[H_{R'}, δ(A)]‖ t²`, with `R'` the sites reached in two steps. -/
lemma norm_dynamics_sub_sub_le {X : Finset V} {a : 𝔄} (ha : a ∈ N.loc X) (t : ℝ) :
    ‖Φ.dynamics t a - a - t • Φ.generator hfin X a‖ ≤
      ‖(Φ.hamiltonian (reachStep hfin (reachStep hfin X)) : 𝔄) * Φ.generator hfin X a -
        Φ.generator hfin X a * Φ.hamiltonian (reachStep hfin (reachStep hfin X))‖ * t ^ 2 := by
  have hq := N.loc_le_quasiLocal X ha
  refine le_of_tendsto (((tendsto_dynamics hJ hfin hq t).sub_const a).sub_const _).norm ?_
  filter_upwards [eventually_ge_atTop (reachStep hfin (reachStep hfin X))] with Λ hΛ
  have h1 : reachStep hfin X ⊆ Λ := (subset_reachStep hfin _).trans hΛ
  have hgen : I • ((Φ.hamiltonian Λ : 𝔄) * a - a * Φ.hamiltonian Λ) = Φ.generator hfin X a := by
    rw [commutator_hamiltonian_eq hfin h1 ha, generator]
  have h := norm_evolution_sub_sub_le' (Φ.hamiltonian Λ) a t
  rw [hgen, commutator_hamiltonian_eq hfin hΛ (generator_mem hfin ha)] at h
  exact h

include hJ in
/-- Local observables lie in the domain of the generator: `t ↦ α_t(A)` is differentiable at
`t = 0` with derivative `δ(A) = i Σ_{Z ∩ X ≠ ∅} [Φ(Z), A] + i Σ_{x ∈ X} [D_x, A]`. -/
theorem hasDerivAt_dynamics {X : Finset V} {a : 𝔄} (ha : a ∈ N.loc X) :
    HasDerivAt (fun t => Φ.dynamics t a) (Φ.generator hfin X a) 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, dynamics_zero hJ hfin (N.loc_le_quasiLocal X ha)]
  set M := ‖(Φ.hamiltonian (reachStep hfin (reachStep hfin X)) : 𝔄) * Φ.generator hfin X a -
    Φ.generator hfin X a * Φ.hamiltonian (reachStep hfin (reachStep hfin X))‖
  have key : ∀ t : ℝ, ‖Φ.dynamics t a - a - t • Φ.generator hfin X a‖ ≤ M * ‖t ^ 2‖ :=
    fun t => by
      rw [norm_pow, Real.norm_eq_abs, sq_abs]
      exact norm_dynamics_sub_sub_le hJ hfin ha t
  exact (Asymptotics.IsBigO.of_bound M (Eventually.of_forall key)).trans_isLittleO
    (Asymptotics.isLittleO_pow_id (n := 2) one_lt_two)

end Interaction

end LatticeFermions
