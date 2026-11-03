/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.TensorNet
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.NumberCalculus
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.ResolventBridge
/-!

# The Fock representation of the local net

The local net of an infinite bosonic lattice acts on the Fock space `ℓ²(Occ L)`.

## i. Overview

Finitely many bosons on a lattice `L` split along a finite region `X` into the occupations of the
modes in `X` and the occupations outside. This identifies `ℓ²(Occ L)` with the tensor product
`ℓ²(ℕ^X) ⊗ ℓ²(Occ outside X)`. An observable of `X` acts as `T ⊗ 1`. This defines a star
representation `fockRep X` of `B(ℓ²(ℕ^X))` on the Fock space. It is compatible with the inclusions
of the net `tensorNet`. Hence it is a representation of the algebraic inductive limit of the
local observables. A diagonal local observable is represented by the diagonal operator on the
Fock space. In particular the bounded Borel functions `f(N_x)` of the number operator of one mode
are local observables in `B(ℓ²(ℕ))` and are represented by the spectral calculus of the number
operator. This is the bridge from the polynomial observable `N_x` to the local net.

## ii. Key results

- `InfiniteBosons.fockSplit`: the splitting of occupation vectors along a region.
- `InfiniteBosons.fockRep`: the Fock representation of the observables of a region.
- `InfiniteBosons.fockRep_incl`: compatibility with the net inclusions.
- `InfiniteBosons.fockRep_diagOp`: diagonal observables act diagonally.
- `InfiniteBosons.fockRep_numberFunction`: `f(N_x)` is the image of a local observable.

## iii. Table of contents

- A. Splitting of occupation vectors
- B. The representation
- C. Diagonal observables and the number calculus

## iv. References

* O. Bratteli, D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, Section 5.2.
* J. Dereziński, C. Gérard, Mathematics of Quantization and Quantum Fields, Cambridge University
  Press (2013), Chapter 3.
-/

@[expose] public section

open Finsupp BoundedContinuousFunction
noncomputable section
namespace InfiniteBosons
open CondensedMatter.QuasiLocal

variable {L : Type*} [DecidableEq L]

/-- Occupation vectors supported outside the region `X`. -/
abbrev OutOcc (X : Finset L) : Type _ := {α : L →₀ ℕ // ∀ x ∈ X, α x = 0}

/-- The occupation of the modes of `X` as a finitely supported function. -/
def inOcc (X : Finset L) (c : Cfg (fun _ : L => ℕ) X) : L →₀ ℕ :=
  Finsupp.onFinset X (fun l => if h : l ∈ X then c ⟨l, h⟩ else 0) (by
    intro l hl; by_contra h; exact hl (by simp [h]))

lemma inOcc_apply (X : Finset L) (c : Cfg (fun _ : L => ℕ) X) (l : L) :
    inOcc X c l = if h : l ∈ X then c ⟨l, h⟩ else 0 := rfl

/-- Finitely many bosons split into those in the region `X` and those outside. -/
def fockSplit (X : Finset L) : (L →₀ ℕ) ≃ Cfg (fun _ : L => ℕ) X × OutOcc X where
  toFun α := (fun x => α x.1, ⟨Finsupp.filter (fun l => l ∉ X) α, fun x hx => by simp [hx]⟩)
  invFun p := inOcc X p.1 + p.2.1
  left_inv α := by
    ext l
    by_cases h : l ∈ X <;> simp [inOcc_apply, h]
  right_inv p := by
    refine Prod.ext ?_ (Subtype.ext ?_)
    · funext x
      have := p.2.2 x.1 x.2
      simp [inOcc_apply, x.2, this]
    · ext l
      by_cases h : l ∈ X
      · simp [inOcc_apply, h, p.2.2 l h]
      · simp [inOcc_apply, h]

lemma fockSplit_symm_apply (X : Finset L) (c : Cfg (fun _ : L => ℕ) X) (o : OutOcc X) (l : L) :
    (fockSplit X).symm (c, o) l = (if h : l ∈ X then c ⟨l, h⟩ else 0) + o.1 l := by
  simp [fockSplit, inOcc_apply]


/-- The Fock representation of the observables of a finite region `X`: `T ↦ T ⊗ 1` on `ℓ²(Occ L)`,
where the first factor carries the occupations of the modes in `X`. -/
def fockRep (X : Finset L) : (HilbertSp (Cfg (fun _ : L => ℕ) X) →L[ℂ]
    HilbertSp (Cfg (fun _ : L => ℕ) X)) →⋆ₐ[ℂ] (HilbertSp (L →₀ ℕ) →L[ℂ] HilbertSp (L →₀ ℕ)) :=
  inclE (fockSplit X)

/-- **The Fock representation is compatible with the net inclusions.** -/
lemma fockRep_incl {X Y : Finset L} (h : X ≤ Y) (T : HilbertSp (Cfg (fun _ : L => ℕ) X) →L[ℂ]
    HilbertSp (Cfg (fun _ : L => ℕ) X)) :
    fockRep Y ((tensorNet (fun _ : L => ℕ)).incl h T) = fockRep X T := by
  symm
  refine inclE_comp (splitEquiv h) (fockSplit Y) (fockSplit X) (fun d => rfl) (fun d a => ?_) T
  ext l
  rw [fockSplit_symm_apply, fockSplit_symm_apply]
  by_cases hY : l ∈ Y
  · by_cases hX : l ∈ X
    · have : ((fockSplit Y) d).2.1 l = 0 := ((fockSplit Y) d).2.2 l hY
      simp [splitEquiv, fockSplit, hX, hY, this]
    · simp [splitEquiv, fockSplit, hX, hY]
  · have hX : l ∉ X := fun hx => hY (h hx)
    simp [splitEquiv, fockSplit, hX, hY]


/-- **Diagonal observables of a region** act diagonally in the Fock representation. -/
lemma fockRep_diagOp (X : Finset L) {c : Cfg (fun _ : L => ℕ) X → ℂ} {C : ℝ}
    (hc : ∀ σ, ‖c σ‖ ≤ C) :
    fockRep X (diagOp hc) = diagOp (c := fun α : L →₀ ℕ => c (fun x => α x.1)) (C := C)
      (fun α => hc _) :=
  ContinuousLinearMap.ext fun ψ => Subtype.ext (funext fun α => by
    show inclE (fockSplit X) (diagOp hc) ψ α = _
    rw [inclE_apply, diagOp_apply, diagOp_apply, slice_symm_apply]
    rw [Prod.mk.eta, Equiv.symm_apply_apply]
    rfl)

/-- **Bridge for the number operator.** The bounded function `f` of `N_x`, as a local observable of
the region `{x}`, is represented by the spectral calculus `f(N_x)` of the Fock representation. -/
lemma fockRep_numberFunction (x : L) (f : ℕ →ᵇ ℂ) :
    fockRep {x} (diagOp (c := fun σ : Cfg (fun _ : L => ℕ) {x} => f (σ ⟨x, by simp⟩))
      (C := ‖f‖) (fun σ => f.norm_coe_le_norm _)) = numberFunction x f := by
  rw [fockRep_diagOp]
  rfl

/-- **The number operator has a bounded resolvent.** The density hypothesis of the bridge holds for
`N_x` because the occupation vectors are eigenvectors with real eigenvalues. -/
theorem numberOp_resolvent (x : L) {c : ℝ} (hc : c ≠ 0) :
    ∃ R : HilbertSp (L →₀ ℕ) →L[ℂ] HilbertSp (L →₀ ℕ), ‖R‖ ≤ 1 / |c| ∧
      ∀ f, R (shiftMap (numberOp x).1.1 c f) = embed f :=
  polyOp_resolvent (numberOp x) (by
    simp [numberOp, star_mul, star_annOp, star_creOp]) hc
    (dense_range_shiftMap_of_diag _ (fun α => (α x : ℝ)) (fun α => by
      rw [numberOp_basis]; simp) hc)

lemma numberOp_apply_coord (x : L) (g : Occ L →₀ ℂ) (α : Occ L) :
    ((numberOp x).1.1 g) α = (α x : ℂ) * g α := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg, mul_add]
  | single β d =>
    have : single β d = d • single β (1 : ℂ) := by simp
    rw [this, map_smul, numberOp_basis]
    by_cases h : β = α
    · subst h; simp; ring
    · simp [Finsupp.single_apply, h]

/-- The resolvent function `n ↦ (n + i c)⁻¹` as a bounded function on `ℕ`. -/
def resolventFun (c : ℝ) (hc : c ≠ 0) : ℕ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun n : ℕ => ((n : ℂ) + Complex.I * c)⁻¹)
    continuous_of_discreteTopology (1 / |c|) (fun n => by
      have h : |c| ≤ ‖(n : ℂ) + Complex.I * c‖ := by
        calc |c| = |((n : ℂ) + Complex.I * c).im| := by simp
          _ ≤ _ := Complex.abs_im_le_norm _
      rw [norm_inv, one_div]
      exact inv_anti₀ (abs_pos.mpr hc) h)


lemma shiftMap_number_coord (x : L) (c : ℝ) (g : Occ L →₀ ℂ) (α : Occ L) :
    (shiftMap (numberOp x).1.1 c g : HilbertSp (Occ L)) α = ((α x : ℂ) + Complex.I * c) * g α := by
  have : shiftMap (numberOp x).1.1 c g = embed ((numberOp x).1.1 g + ((Complex.I * c : ℂ)) • g) := by
    simp [shiftMap]
  rw [this, embed_apply]
  simp [numberOp_apply_coord, add_mul]

/-- **The resolvent of `N_x` is the calculus of the bounded function `(n + i c)⁻¹`.** -/
theorem numberOp_resolvent_eq (x : L) {c : ℝ} (hc : c ≠ 0)
    (R : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L))
    (hR : ∀ f, R (shiftMap (numberOp x).1.1 c f) = embed f) :
    R = numberFunction x (resolventFun c hc) := by
  have hdense := dense_range_shiftMap_of_diag (numberOp x).1.1 (fun α => (α x : ℝ))
    (fun α => by rw [numberOp_basis]; simp) hc
  refine ContinuousLinearMap.ext fun ψ => ?_
  have hmem : ψ ∈ closure (LinearMap.range (shiftMap (numberOp x).1.1 c) : Set (HilbertSp (Occ L))) :=
    hdense ψ
  refine closure_minimal ?_ (isClosed_eq R.continuous (numberFunction x _).continuous) hmem
    |> fun h => h
  rintro _ ⟨g, rfl⟩
  show R (shiftMap (numberOp x).1.1 c g) = numberFunction x (resolventFun c hc)
    (shiftMap (numberOp x).1.1 c g)
  rw [hR]
  refine Subtype.ext (funext fun α => ?_)
  rw [numberFunction_apply, shiftMap_number_coord, embed_apply]
  have hne : ((α x : ℂ) + Complex.I * c) ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; exact hc this
  show g α = ((α x : ℂ) + Complex.I * c)⁻¹ * (((α x : ℂ) + Complex.I * c) * g α)
  field_simp

/-- **The resolvent of `N_x` lies in the local net.** It is the Fock image of a local observable of
the region `{x}`. -/
theorem numberOp_resolvent_local (x : L) {c : ℝ} (hc : c ≠ 0) :
    ∃ (R : HilbertSp (Occ L) →L[ℂ] HilbertSp (Occ L)) (T : HilbertSp (CondensedMatter.QuasiLocal.Cfg
      (fun _ : L => ℕ) {x}) →L[ℂ] HilbertSp (CondensedMatter.QuasiLocal.Cfg (fun _ : L => ℕ) {x})),
      (∀ f, R (shiftMap (numberOp x).1.1 c f) = embed f) ∧ fockRep {x} T = R := by
  obtain ⟨R, -, hR⟩ := numberOp_resolvent x hc
  refine ⟨R, diagOp (c := fun σ : CondensedMatter.QuasiLocal.Cfg (fun _ : L => ℕ) {x} =>
    resolventFun c hc (σ ⟨x, by simp⟩)) (C := ‖resolventFun c hc‖)
    (fun σ => (resolventFun c hc).norm_coe_le_norm _), hR, ?_⟩
  rw [fockRep_numberFunction x (resolventFun c hc), numberOp_resolvent_eq x hc R hR]

end InfiniteBosons
