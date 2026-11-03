/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.TensorAmp
public import PhyslibAlpha.CondensedMatter.QuasiLocal.Local
public import PhyslibAlpha.ProbabilisticTheory.QuasiLocal.AlgebraNet
/-!

# The local net of observables `B(H_X)` for arbitrary local Hilbert spaces

Sites `S` carry local configuration types `Ω x` of any cardinality. A finite region `X` has the
Hilbert space `H_X = ℓ²(Ω^X)`. The observables of `X` are all bounded operators on `H_X`.

## i. Overview

The net is specified through the finite tensor products and not through the minimal tensor
product of the algebras. The Hilbert space `ℓ²(Ω^X)` is the Hilbert tensor product of the local
spaces `ℓ²(Ω x)` for `x ∈ X`. For `X ⊆ Y` the configurations of `Y` split into those of `X` and
those of `Y \ X`. The inclusion `T ↦ T ⊗ 1` is the amplification of `TensorAmp.lean` transported
along this splitting. It is a star homomorphism. It is the identity for `X = X` and it is
compatible with composition. Hence the regions form an `AlgebraNet`. The local spaces may be
infinite-dimensional. This covers oscillators `ℓ²(ℕ)`, spins and photon plus atom.

The inductive limit of the net is the algebra of local observables of the infinite system. It is
the quasilocal algebra before completion. No sector or finite-volume truncation enters.

## ii. Key results

- `InfiniteBosons.splitEquiv`: the splitting of configurations of `Y` along `X ≤ Y`.
- `InfiniteBosons.inclE`: the inclusion of operators along a splitting of the index type.
- `InfiniteBosons.inclE_apply`: pointwise formula for the inclusion.
- `InfiniteBosons.inclE_comp`: compatible splittings give composing inclusions.
- `InfiniteBosons.tensorNet`: the net `X ↦ B(ℓ²(Ω^X))`.

## iii. Table of contents

- A. Splitting of configurations
- B. The inclusion along a splitting
- C. The net

## iv. References

* R. Haag, Local Quantum Physics, Springer (1992), Chapter III.
* O. Bratteli, D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, Section 6.2.
-/

@[expose] public section

open Finsupp

noncomputable section
namespace InfiniteBosons
open CondensedMatter.QuasiLocal

variable {S : Type*} [DecidableEq S] {Ω : S → Type*}

/-- The configurations of `Y` outside `X`. -/
abbrev RestCfg (Ω : S → Type*) (X Y : Finset S) : Type _ := Cfg Ω (Y \ X)

def splitEquiv {X Y : Finset S} (h : X ≤ Y) : Cfg Ω Y ≃ Cfg Ω X × RestCfg Ω X Y where
  toFun c := (restr h c, fun w => c ⟨w.1, (Finset.mem_sdiff.1 w.2).1⟩)
  invFun p := fun y => if hy : y.1 ∈ X then p.1 ⟨y.1, hy⟩ else
    p.2 ⟨y.1, Finset.mem_sdiff.2 ⟨y.2, hy⟩⟩
  left_inv c := by funext y; by_cases hy : y.1 ∈ X <;> simp [hy, restr]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext x; simp [restr, x.2]
    · funext w; have := (Finset.mem_sdiff.1 w.2).2; simp [this]

lemma splitEquiv_fst {X Y : Finset S} (h : X ≤ Y) (c : Cfg Ω Y) :
    (splitEquiv h c).1 = restr h c := rfl

lemma reindexEquiv_symm_apply {α β : Type*} (e : α ≃ β) (ψ : HilbertSp α) (p : β) :
    (reindexEquiv e).symm ψ p = ψ (e.symm p) := by
  have : (reindexEquiv e).symm ψ = reindexEquiv e.symm ψ :=
    (LinearIsometryEquiv.symm_apply_eq _).mpr (Subtype.ext (funext fun a => by
      simp [reindexEquiv_apply]))
  rw [this]; rfl

/-- The inclusion of operators of the first factor along a decomposition `C ≃ A × B`. -/
def inclE {A B C : Type*} (e : C ≃ A × B) : (HilbertSp A →L[ℂ] HilbertSp A) →⋆ₐ[ℂ]
    (HilbertSp C →L[ℂ] HilbertSp C) :=
  ((reindexEquiv e).conjStarAlgEquiv : (HilbertSp (A × B) →L[ℂ] HilbertSp (A × B)) ≃⋆ₐ[ℂ]
    (HilbertSp C →L[ℂ] HilbertSp C)).toStarAlgHom.comp ampStar

lemma inclE_apply {A B C : Type*} (e : C ≃ A × B) (T : HilbertSp A →L[ℂ] HilbertSp A)
    (ψ : HilbertSp C) (c : C) :
    inclE e T ψ c = T (slice (e c).2 ((reindexEquiv e).symm ψ)) (e c).1 := by
  simp only [inclE, StarAlgHom.comp_apply, ampStar_apply]
  show (reindexEquiv e (amp T ((reindexEquiv e).symm ψ))) c = _
  rw [reindexEquiv_apply]
  rfl

lemma slice_symm_apply {A B C : Type*} (e : C ≃ A × B) (ψ : HilbertSp C) (b : B) (a : A) :
    slice b ((reindexEquiv e).symm ψ) a = ψ (e.symm (a, b)) := by
  rw [slice_apply, reindexEquiv_symm_apply]

/-- Coherence of two decompositions: if the decompositions are compatible then the inclusions
compose. -/
lemma inclE_comp {A B C D E F : Type*} (e₁ : C ≃ A × B) (e₂ : D ≃ C × E) (e₃ : D ≃ A × F)
    (hfst : ∀ d, (e₃ d).1 = (e₁ (e₂ d).1).1)
    (hglue : ∀ d a, e₂.symm (e₁.symm (a, (e₁ (e₂ d).1).2), (e₂ d).2) = e₃.symm (a, (e₃ d).2))
    (T : HilbertSp A →L[ℂ] HilbertSp A) :
    inclE e₃ T = inclE e₂ (inclE e₁ T) := by
  refine ContinuousLinearMap.ext fun ψ => Subtype.ext (funext fun c => ?_)
  show inclE e₃ T ψ c = inclE e₂ (inclE e₁ T) ψ c
  rw [inclE_apply, inclE_apply, inclE_apply, hfst]
  have hv : slice (e₃ c).2 ((reindexEquiv e₃).symm ψ) =
      slice (e₁ (e₂ c).1).2 ((reindexEquiv e₁).symm (slice (e₂ c).2 ((reindexEquiv e₂).symm ψ))) :=
    Subtype.ext (funext fun a => by
      show slice (e₃ c).2 ((reindexEquiv e₃).symm ψ) a = _
      rw [slice_symm_apply]
      show _ = slice _ ((reindexEquiv e₁).symm (slice _ _)) a
      rw [slice_symm_apply, slice_apply, reindexEquiv_symm_apply, hglue])
  rw [hv]

lemma splitEquiv_comp {X Y Z : Finset S} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (c : Cfg Ω Z) :
    (splitEquiv (h₁.trans h₂) c).1 = (splitEquiv h₁ (splitEquiv h₂ c).1).1 := rfl

lemma splitEquiv_glue {X Y Z : Finset S} (h₁ : X ≤ Y) (h₂ : Y ≤ Z) (c : Cfg Ω Z)
    (a : Cfg Ω X) :
    (splitEquiv h₂).symm ((splitEquiv h₁).symm (a, (splitEquiv h₁ (splitEquiv h₂ c).1).2),
        (splitEquiv h₂ c).2) =
      (splitEquiv (h₁.trans h₂)).symm (a, (splitEquiv (h₁.trans h₂) c).2) := by
  funext z
  by_cases hy : z.1 ∈ Y
  · by_cases hx : z.1 ∈ X
    · simp [splitEquiv, hy, hx]
    · simp [splitEquiv, hy, hx]
  · have hx : z.1 ∉ X := fun hx => hy (h₁ hx)
    simp [splitEquiv, hy, hx]

/-- The net of observables `A(X) = B(ℓ²(Ω^X))` of finite regions `X`. The Hilbert space of a region
is the Hilbert tensor product of the local Hilbert spaces `ℓ²(Ω x)`. The inclusions are
`T ↦ T ⊗ 1`. -/
def tensorNet (Ω : S → Type*) : ProbabilisticTheory.QuasiLocal.AlgebraNet S where
  A X := HilbertSp (Cfg Ω X) →L[ℂ] HilbertSp (Cfg Ω X)
  incl h := inclE (splitEquiv h)
  incl_refl X T := by
    refine ContinuousLinearMap.ext fun ψ => Subtype.ext (funext fun c => ?_)
    show inclE (splitEquiv (le_refl X)) T ψ c = T ψ c
    rw [inclE_apply]
    have hv : slice (splitEquiv (le_refl X) c).2
        ((reindexEquiv (splitEquiv (le_refl X))).symm ψ) = ψ :=
      Subtype.ext (funext fun a => by
        rw [slice_symm_apply]
        refine congrArg (fun z => (ψ : Cfg Ω X → ℂ) z) ?_
        funext y
        simp [splitEquiv, y.2])
    rw [hv]
    rfl
  incl_trans h₁ h₂ T := inclE_comp _ _ _ (splitEquiv_comp h₁ h₂) (splitEquiv_glue h₁ h₂) T

end InfiniteBosons
