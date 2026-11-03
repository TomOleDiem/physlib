/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.TensorNet
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.HilbertSpace
/-!

# Landing of resolvents in the amplified algebra

A bounded inverse of a fibrewise operator on `ℓ²(A × B)` is an amplified operator `T ⊗ 1`.

## i. Overview

A local observable of a region `X` acts on the tensor product `ℓ²(ℕ^X) ⊗ ℓ²(outside)` as an
operator of the first factor tensored with the identity. In the product basis this means that the
operator acts on each slice of the second index in the same way. Let `K` be such a fibrewise
operator on the algebraic space, for example a local polynomial observable shifted by `i c`. Let
`R` be a bounded inverse of `K` and let the range of `K` be dense. Then `R` is the amplification
of the operator `T = slice₀ ∘ R ∘ insert₀`: both sides have the same slices on the dense range of
`K`. This is the step from a polynomial observable to a bounded element of the local net `B(H_X)`.
The statement does not use any sector or finite-volume restriction.

## ii. Key results

- `InfiniteBosons.eq_amp_of_slice`: an operator with the slice property is an amplification.
- `InfiniteBosons.insertSlice`, `InfiniteBosons.insertCLM`, `InfiniteBosons.sliceCLM`: insertion
  and extraction of a slice as bounded maps.
- `InfiniteBosons.resolvent_eq_amp`: the landing theorem.

## iii. Table of contents

- A. Amplified operators and slices
- B. Algebraic slices
- C. The landing theorem

## iv. References

* R. Haag, Local Quantum Physics, Springer (1992), Chapter III.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

/-- **Characterisation of amplified operators**: an operator whose slices are `T` applied to the
slices is the amplification of `T`. -/
lemma eq_amp_of_slice (R : HilbertSp (A × B) →L[ℂ] HilbertSp (A × B))
    (T : HilbertSp A →L[ℂ] HilbertSp A) (h : ∀ b ψ, slice b (R ψ) = T (slice b ψ)) :
    R = amp T :=
  ContinuousLinearMap.ext fun ψ => ext_slices fun b => by rw [h, slice_amp]

/-- Insertion of a vector of `ℓ²(A)` into the slice `b` of `ℓ²(A × B)`. -/
def insertSlice [DecidableEq B] (b : B) (ψ : HilbertSp A) : HilbertSp (A × B) :=
  ⟨fun p => if p.2 = b then ψ p.1 else 0, (memℓp_gen_iff (by norm_num)).mpr (by
    have h2 : (2 : ENNReal).toReal = 2 := by norm_num
    simp only [h2]
    have hinj : Function.Injective fun a : A => (a, b) := fun a a' h => by simpa using h
    have key : Summable fun p : A × B => ‖(if p.2 = b then ψ p.1 else 0 : ℂ)‖ ^ (2 : ℝ) := by
      refine (hinj.summable_iff (fun p hp => ?_)).mp ?_
      · have : p.2 ≠ b := fun h' => hp ⟨p.1, by ext <;> simp [h']⟩
        simp [this]
      · refine (sq_summable ψ).congr fun a => ?_
        simp [Function.comp, Real.rpow_two]
    exact key)⟩

lemma slice_insertSlice [DecidableEq B] (b b' : B) (ψ : HilbertSp A) :
    slice b' (insertSlice b ψ) = if b' = b then ψ else 0 := by
  by_cases h : b' = b
  · subst h; exact Subtype.ext (funext fun a => by simp [slice_apply, insertSlice])
  · exact Subtype.ext (funext fun a => by simp [slice_apply, insertSlice, h])


lemma norm_slice_le (b : B) (ψ : HilbertSp (A × B)) : ‖slice b ψ‖ ≤ ‖ψ‖ := by
  have hs := summable_slices ψ
  have h1 : ‖slice b ψ‖ ^ 2 ≤ ∑' b', ‖slice b' ψ‖ ^ 2 :=
    hs.le_tsum b (fun b' _ => by positivity)
  rw [← norm_sq_eq_tsum_slices] at h1
  exact le_of_sq_le_sq h1 (norm_nonneg _)

/-- The slice at `b` as a bounded linear map. -/
def sliceCLM (b : B) : HilbertSp (A × B) →L[ℂ] HilbertSp A :=
  LinearMap.mkContinuous
    { toFun := slice b
      map_add' := slice_add b
      map_smul' := slice_smul b } 1 (fun ψ => by simpa using norm_slice_le b ψ)

lemma sliceCLM_apply (b : B) (ψ : HilbertSp (A × B)) : sliceCLM b ψ = slice b ψ := rfl

lemma norm_insertSlice [DecidableEq B] (b : B) (ψ : HilbertSp A) : ‖insertSlice b ψ‖ = ‖ψ‖ := by
  have h := norm_sq_eq_tsum_slices (insertSlice b ψ)
  rw [tsum_eq_single b (fun b' hb' => by simp [slice_insertSlice, hb'])] at h
  simp only [slice_insertSlice, if_true] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- Insertion of a slice as a bounded linear map. -/
def insertCLM [DecidableEq B] (b : B) : HilbertSp A →L[ℂ] HilbertSp (A × B) :=
  LinearMap.mkContinuous
    { toFun := insertSlice b
      map_add' := fun ψ φ => Subtype.ext (funext fun p => by
        show (if p.2 = b then (ψ + φ : HilbertSp A) p.1 else 0) =
          (if p.2 = b then ψ p.1 else 0) + (if p.2 = b then φ p.1 else 0)
        by_cases h : p.2 = b <;> simp [h, lp.coeFn_add])
      map_smul' := fun r ψ => Subtype.ext (funext fun p => by
        show (if p.2 = b then (r • ψ : HilbertSp A) p.1 else 0) =
          r * (if p.2 = b then ψ p.1 else 0)
        by_cases h : p.2 = b <;> simp [h, lp.coeFn_smul]) } 1
    (fun ψ => by simp [norm_insertSlice])


/-- The algebraic slice at `b` of a finitely supported vector on `A × B`. -/
def sliceAlg (b : B) (f : A × B →₀ ℂ) : A →₀ ℂ :=
  Finsupp.comapDomain (fun a => (a, b)) f (fun a _ a' _ h => by simpa using h)

lemma sliceAlg_apply (b : B) (f : A × B →₀ ℂ) (a : A) : sliceAlg b f a = f (a, b) := rfl

/-- Insertion of a finitely supported vector of `A` at the slice `b`. -/
def insAlg (b : B) (g : A →₀ ℂ) : A × B →₀ ℂ := Finsupp.mapDomain (fun a => (a, b)) g

lemma insAlg_apply_same (b : B) (g : A →₀ ℂ) (a : A) : insAlg b g (a, b) = g a := by
  have hinj : Function.Injective fun a : A => (a, b) := fun a a' h => by simpa using h
  exact Finsupp.mapDomain_apply' Set.univ (f := fun a : A => (a, b)) g (by simp) hinj.injOn (Set.mem_univ a)

lemma insAlg_apply_ne (b b' : B) (hb : b' ≠ b) (g : A →₀ ℂ) (a : A) : insAlg b g (a, b') = 0 := by
  rw [insAlg, Finsupp.mapDomain_of_notMem_range]
  rintro ⟨a', ha'⟩
  exact hb (by simpa using (congrArg Prod.snd ha').symm)

lemma slice_embed (b : B) (f : A × B →₀ ℂ) : slice b (embed f) = embed (sliceAlg b f) :=
  Subtype.ext (funext fun a => by
    rw [slice_apply, embed_apply, embed_apply, sliceAlg_apply])

lemma insertSlice_embed (b : B) (g : A →₀ ℂ) : insertSlice b (embed g) = embed (insAlg b g) :=
  Subtype.ext (funext fun p => by
    obtain ⟨a, b'⟩ := p
    rw [embed_apply]
    by_cases h : b' = b
    · subst h; simp [insertSlice, insAlg_apply_same, embed_apply]
    · simp [insertSlice, h, insAlg_apply_ne b b' h, embed_apply])

lemma sliceAlg_insAlg (b : B) (g : A →₀ ℂ) : sliceAlg b (insAlg b g) = g :=
  Finsupp.ext fun a => by rw [sliceAlg_apply, insAlg_apply_same]


/-- **Landing of a resolvent in the amplified algebra.** Let `K` act fibrewise on `A × B` (it acts
as `QK` on every slice). Let `R` be a bounded inverse of `K` on the algebraic space and let the range
of `K` be dense. Then `R` is the amplification of the operator `T = slice₀ R insert₀`. -/
theorem resolvent_eq_amp (K : (A × B →₀ ℂ) →ₗ[ℂ] (A × B →₀ ℂ)) (QK : (A →₀ ℂ) →ₗ[ℂ] (A →₀ ℂ))
    (hfib : ∀ b f, sliceAlg b (K f) = QK (sliceAlg b f))
    (R : HilbertSp (A × B) →L[ℂ] HilbertSp (A × B)) (hR : ∀ f, R (embed (K f)) = embed f)
    (hdense : Dense (LinearMap.range ((embed : (A × B →₀ ℂ) →ₗ[ℂ] HilbertSp (A × B)) ∘ₗ K) :
      Set (HilbertSp (A × B)))) (b0 : B) :
    R = amp (sliceCLM b0 ∘L R ∘L insertCLM b0) := by
  set T : HilbertSp A →L[ℂ] HilbertSp A := sliceCLM b0 ∘L R ∘L insertCLM b0 with hT
  refine eq_amp_of_slice R T fun b => ?_
  have hd : DenseRange ((embed : (A × B →₀ ℂ) →ₗ[ℂ] HilbertSp (A × B)) ∘ₗ K) := hdense
  have heq : (sliceCLM b ∘L R) = (T ∘L sliceCLM b) := by
    refine ContinuousLinearMap.ext fun ψ => ?_
    refine hd.induction_on ψ (isClosed_eq (by fun_prop) (by fun_prop)) fun f => ?_
    show slice b (R (embed (K f))) = T (slice b (embed (K f)))
    rw [hR, slice_embed, slice_embed, hfib]
    set g := sliceAlg b f with hg
    have hins : insAlg b0 (QK g) = K (insAlg b0 g) := by
      refine Finsupp.ext fun p => ?_
      obtain ⟨a, b'⟩ := p
      have h1 : K (insAlg b0 g) (a, b') = (QK (sliceAlg b' (insAlg b0 g))) a := by
        rw [← hfib, sliceAlg_apply]
      rw [h1]
      by_cases h : b' = b0
      · subst h; rw [sliceAlg_insAlg, insAlg_apply_same]
      · have : sliceAlg b' (insAlg b0 g) = 0 :=
          Finsupp.ext fun a => by rw [sliceAlg_apply, insAlg_apply_ne b0 b' h]; rfl
        rw [this, map_zero, insAlg_apply_ne b0 b' h]; rfl
    show embed (sliceAlg b f) = slice b0 (R (insertSlice b0 (embed (QK g))))
    rw [insertSlice_embed, hins, hR, slice_embed, sliceAlg_insAlg]
  exact fun ψ => congrArg (fun L => L ψ) heq

end InfiniteBosons
