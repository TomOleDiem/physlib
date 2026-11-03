/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.EssentialSelfAdjoint
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.HilbertSpace
public import Physlib.QuantumMechanics.Operators.Unbounded
/-!

# The unbounded Hamiltonian of an infinite system: formal space and Hilbert space

Two spaces: the formal vectors in which an infinite sum of local terms exists, and the Hilbert space
on which the Hamiltonian acts as an operator.

## i. Overview

An infinite lattice Hamiltonian `H = Σ_i Φ_i` is not an element of the polynomial algebra `P(L)`.
It is an infinite sum of local terms. Its action on a finite vector is defined whenever the family
is **row finite**: every coefficient of the image receives a contribution from finitely many terms.
Then `H` is a linear map from the finitely supported vectors, the algebraic Fock space, into the
**formal vectors**, which are arbitrary coefficient functions. This is the space in which the
unbounded Hamiltonian exists. It is symmetric against finite vectors. The Hilbert space `ℓ²` sits
inside the formal vectors. The Hamiltonian acts on `ℓ²` with the domain of finite vectors whose
formal image is square summable. That domain is a submodule and `H` is a symmetric operator on it.
Whether the domain is dense is a property of the model: it holds for number conserving
Hamiltonians and for pairing Hamiltonians with square summable pairing amplitudes. Essential
self-adjointness and the dynamics are theorems for stated model classes.

## ii. Key results

- `InfiniteBosons.Formal`: the formal vectors.
- `InfiniteBosons.RowFinite`: the finiteness condition on a family of terms.
- `InfiniteBosons.formalH`: the Hamiltonian as a linear map into the formal vectors.
- `InfiniteBosons.formalH_symmetric`: `⟨g, H f⟩ = ⟨H g, f⟩` for finite vectors.
- `InfiniteBosons.hamDomainAlg`, `InfiniteBosons.hamPMap`: the operator on `ℓ²`.
- `InfiniteBosons.hamPMap_isSymmetric`: the operator is symmetric.

## iii. Table of contents

- A. Formal vectors and the formal Hamiltonian
- B. Symmetry
- C. The operator on Hilbert space

## iv. References

* K. Schmüdgen, Unbounded Operator Algebras and Representation Theory, Birkhäuser (1990).
* O. Bratteli, D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2, Section 6.2.
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {β ι : Type*} [DecidableEq β]

/-- Formal vectors: arbitrary coefficient functions on the basis. The finitely supported vectors
sit inside. -/
abbrev Formal (β : Type*) := β → ℂ

/-- A family of operators is **row finite** if every coefficient of the image of a finite vector
receives a contribution from finitely many members only. -/
def RowFinite (Φ : ι → Adjointable β) : Prop :=
  ∀ (f : β →₀ ℂ) (α : β), {i | (Φ i).1.1 f α ≠ 0}.Finite

lemma RowFinite.finite_union {Φ : ι → Adjointable β} (h : RowFinite Φ) (f : β →₀ ℂ)
    (s : Finset β) : {i | ∃ α ∈ s, (Φ i).1.1 f α ≠ 0}.Finite := by
  have : {i | ∃ α ∈ s, (Φ i).1.1 f α ≠ 0} = ⋃ α ∈ s, {i | (Φ i).1.1 f α ≠ 0} := by
    ext i; simp
  rw [this]
  exact Set.Finite.biUnion s.finite_toSet fun α _ => h f α

/-- **The formal action of a row finite family**: `(H f)(α) = Σᵢ (Φᵢ f)(α)`. This is a linear map
from the finitely supported vectors into the formal vectors. -/
def formalH (Φ : ι → Adjointable β) (h : RowFinite Φ) : (β →₀ ℂ) →ₗ[ℂ] Formal β where
  toFun f α := ∑ᶠ i, (Φ i).1.1 f α
  map_add' f g := by
    funext α
    simp only [map_add, Finsupp.coe_add, Pi.add_apply]
    exact finsum_add_distrib (h f α |>.subset fun i hi => by simpa using hi)
      (h g α |>.subset fun i hi => by simpa using hi) |> fun e => by
        simpa [Function.support] using e
  map_smul' c f := by
    funext α
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    exact (mul_finsum (fun i => (Φ i).1.1 f α) c).symm


lemma formalH_apply (Φ : ι → Adjointable β) (h : RowFinite Φ) (f : β →₀ ℂ) (α : β) :
    formalH Φ h f α = ∑ᶠ i, (Φ i).1.1 f α := rfl

/-- The pairing of a finite vector with a formal vector. -/
def pairF (g : β →₀ ℂ) (u : Formal β) : ℂ := ∑ α ∈ g.support, starRingEnd ℂ (g α) * u α

/-- The pairing of a formal vector with a finite vector. -/
def pairF' (u : Formal β) (f : β →₀ ℂ) : ℂ := ∑ α ∈ f.support, starRingEnd ℂ (u α) * f α

/-- **Symmetry of the formal Hamiltonian**: `⟨g, H f⟩ = ⟨H g, f⟩` for finite vectors `f`, `g`. -/
theorem formalH_symmetric (Φ : ι → Adjointable β) (h : RowFinite Φ) (hs : ∀ i, star (Φ i) = Φ i)
    (g f : β →₀ ℂ) : pairF g (formalH Φ h f) = pairF' (formalH Φ h g) f := by
  classical
  set T : Finset ι := ((h.finite_union f g.support).union (h.finite_union g f.support)).toFinset
    with hT
  have hsym : ∀ i, pair g ((Φ i).1.1 f) = pair ((Φ i).1.1 g) f := fun i => by
    have := star_fst_pair (Φ i) g f
    rw [hs i] at this
    exact this.symm
  have e1 : ∀ α ∈ g.support, formalH Φ h f α = ∑ i ∈ T, (Φ i).1.1 f α := fun α hα => by
    rw [formalH_apply]
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    simp only [Function.mem_support] at hi
    simp only [hT, Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union, Set.mem_setOf_eq]
    exact Or.inl ⟨α, hα, hi⟩
  have e2 : ∀ α ∈ f.support, formalH Φ h g α = ∑ i ∈ T, (Φ i).1.1 g α := fun α hα => by
    rw [formalH_apply]
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    simp only [Function.mem_support] at hi
    simp only [hT, Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union, Set.mem_setOf_eq]
    exact Or.inr ⟨α, hα, hi⟩
  have s1 : pairF g (formalH Φ h f) =
      ∑ α ∈ g.support, starRingEnd ℂ (g α) * ∑ i ∈ T, (Φ i).1.1 f α :=
    Finset.sum_congr rfl fun α hα => by rw [e1 α hα]
  have s2 : pairF' (formalH Φ h g) f =
      ∑ α ∈ f.support, starRingEnd ℂ (∑ i ∈ T, (Φ i).1.1 g α) * f α :=
    Finset.sum_congr rfl fun α hα => by rw [e2 α hα]
  rw [s1, s2]
  simp only [Finset.mul_sum, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rw [Finset.sum_comm (s := f.support)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hsym i
  unfold pair at this
  rw [Finsupp.sum, Finsupp.sum] at this
  refine this.trans ?_
  set F : β → ℂ := fun a => starRingEnd ℂ ((Φ i).1.1 g a) * f a with hF
  have h1 : ∑ a ∈ ((Φ i).1.1 g).support, F a = ∑ a ∈ ((Φ i).1.1 g).support ∪ f.support, F a :=
    Finset.sum_subset Finset.subset_union_left fun a ha hna => by
      have : ((Φ i).1.1 g) a = 0 := by simpa [Finsupp.mem_support_iff] using hna
      simp [hF, this]
  have h2 : ∑ a ∈ f.support, F a = ∑ a ∈ ((Φ i).1.1 g).support ∪ f.support, F a :=
    Finset.sum_subset Finset.subset_union_right fun a ha hna => by
      have : f a = 0 := by simpa [Finsupp.mem_support_iff] using hna
      simp [hF, this]
  rw [h1, ← h2]


/-- The finitely supported vectors on which the formal Hamiltonian is square summable. -/
def hamDomainAlg (Φ : ι → Adjointable β) (h : RowFinite Φ) : Submodule ℂ (β →₀ ℂ) where
  carrier := {f | Memℓp (formalH Φ h f) 2}
  zero_mem' := by
    show Memℓp (formalH Φ h 0) 2
    rw [map_zero]; exact zero_memℓp
  add_mem' := fun {f g} hf hg => by
    show Memℓp (formalH Φ h (f + g)) 2
    rw [map_add]; exact Memℓp.add hf hg
  smul_mem' := fun c f hf => by
    show Memℓp (formalH Φ h (c • f)) 2
    rw [map_smul]; exact hf.const_smul c

/-- The Hilbert vector `H f` for `f` in the algebraic domain. -/
def hamVec (Φ : ι → Adjointable β) (h : RowFinite Φ) (f : hamDomainAlg Φ h) : HilbertSp β :=
  ⟨formalH Φ h f.1, f.2⟩

/-- **The unbounded Hamiltonian as a densely-defined-or-not operator on `ℓ²`.** Its domain is the
set of finite vectors whose formal image is square summable. -/
def hamPMap (Φ : ι → Adjointable β) (h : RowFinite Φ) : HilbertSp β →ₗ.[ℂ] HilbertSp β where
  domain := (hamDomainAlg Φ h).map embed
  toFun :=
    { toFun := fun x => hamVec Φ h
        ((Submodule.equivMapOfInjective embed embed_injective (hamDomainAlg Φ h)).symm x)
      map_add' := fun x y => by
        refine Subtype.ext (funext fun α => ?_)
        simp [hamVec, map_add]
        rfl
      map_smul' := fun c x => by
        refine Subtype.ext (funext fun α => ?_)
        simp [hamVec, map_smul] }


lemma hamPMap_apply (Φ : ι → Adjointable β) (h : RowFinite Φ) (f : hamDomainAlg Φ h) :
    hamPMap Φ h ⟨embed f.1, Submodule.mem_map_of_mem f.2⟩ = hamVec Φ h f := by
  show hamVec Φ h ((Submodule.equivMapOfInjective embed embed_injective (hamDomainAlg Φ h)).symm
    ⟨embed f.1, Submodule.mem_map_of_mem f.2⟩) = _
  congr 1
  rw [LinearEquiv.symm_apply_eq]
  rfl

lemma inner_embed_hamVec (Φ : ι → Adjointable β) (h : RowFinite Φ) (f : hamDomainAlg Φ h)
    (g : β →₀ ℂ) : inner ℂ (hamVec Φ h f) (embed g) = pairF' (formalH Φ h f.1) g := by
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := g.support) (fun α hα => by
    have : g α = 0 := by simpa [Finsupp.mem_support_iff] using hα
    simp [embed_apply, this])]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp [hamVec, embed_apply, mul_comm]

lemma inner_embed_hamVec' (Φ : ι → Adjointable β) (h : RowFinite Φ) (f : hamDomainAlg Φ h)
    (g : β →₀ ℂ) : inner ℂ (embed g) (hamVec Φ h f) = pairF g (formalH Φ h f.1) := by
  rw [lp.inner_eq_tsum]
  rw [tsum_eq_sum (s := g.support) (fun α hα => by
    have : g α = 0 := by simpa [Finsupp.mem_support_iff] using hα
    simp [embed_apply, this])]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp [hamVec, embed_apply, mul_comm]

/-- **The Hamiltonian is a symmetric operator on `ℓ²`.** -/
theorem hamPMap_isSymmetric (Φ : ι → Adjointable β) (h : RowFinite Φ)
    (hs : ∀ i, star (Φ i) = Φ i) : (hamPMap Φ h).IsSymmetric := by
  intro x y
  obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.mp x.2
  obtain ⟨g, hg, hgy⟩ := Submodule.mem_map.mp y.2
  have hx : x = ⟨embed f, Submodule.mem_map_of_mem hf⟩ := Subtype.ext hfx.symm
  have hy : y = ⟨embed g, Submodule.mem_map_of_mem hg⟩ := Subtype.ext hgy.symm
  subst hx hy
  rw [hamPMap_apply Φ h ⟨f, hf⟩, hamPMap_apply Φ h ⟨g, hg⟩]
  show inner ℂ (hamVec Φ h ⟨f, hf⟩) (embed g) = inner ℂ (embed f) (hamVec Φ h ⟨g, hg⟩)
  rw [inner_embed_hamVec, inner_embed_hamVec']
  exact (formalH_symmetric Φ h hs f g).symm

end InfiniteBosons
