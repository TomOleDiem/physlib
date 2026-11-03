/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Algebra.StarSubalgebra
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!

# Graded local nets of C⋆-algebras

Local subalgebras of a C⋆-algebra, indexed by the finite regions of a set of sites, with a parity
automorphism whose even elements commute with the local algebras of disjoint regions.

## i. Overview

The observables of a lattice system are elements of one C⋆-algebra `𝔄`. Each finite region `X`
of the sites has a star subalgebra `𝔄_X`, its *local algebra*, growing with `X`. For spins,
observables of disjoint regions commute. For fermions they do not: two annihilators at different
sites anticommute. What survives is *even-odd locality*. A *parity* `Θ`, an involutive
`⋆`-automorphism preserving every local algebra, splits observables into even and odd ones, and

`X ∩ Y = ∅, A ∈ 𝔄_X, B ∈ 𝔄_Y, Θ B = B ⟹ A B = B A`.

The interactions of a fermion system are even, so in the commutators of the dynamics one factor
is always even and ordinary commutators suffice. This is the only locality used for the
Lieb–Robinson bound and the thermodynamic limit, so everything about dynamics is done once for
a graded local net. A spin system is the case of the trivial parity, where every element is
even.

The *quasi-local algebra* is the norm closure of the union of the local algebras, a
C⋆-subalgebra of `𝔄`. The union is itself a star subalgebra, because any two finite regions lie
in a third.

## ii. Key results

- `LatticeFermions.GradedLocalNet` : local algebras with parity and even-odd locality.
- `LatticeFermions.GradedLocalNet.IsEven` : an element fixed by the parity.
- `LatticeFermions.GradedLocalNet.commute_of_isEven` : even-odd locality, with the even
  element on either side.
- `LatticeFermions.GradedLocalNet.localUnion` : the star subalgebra of local elements.
- `LatticeFermions.GradedLocalNet.quasiLocal` : the quasi-local C⋆-algebra.
- `LatticeFermions.GradedLocalNet.ofCommute` : a spin system, with the trivial parity.
- `LatticeFermions.GradedLocalNet.ofClosure` : the graded local net of the norm closures.

## iii. Table of contents

- A. Graded local nets
- B. Even elements
- C. The local and quasi-local algebras
- D. Spin systems
- E. Graded local nets from norm closures

## iv. References

* O. Bratteli, D. W. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Sections 5.2.2 and 6.2.1.
* B. Nachtergaele, R. Sims, A. Young, Lieb-Robinson bounds, the spectral flow, and stability of
  the spectral gap for lattice fermion systems, arXiv:1705.08553, Section 2.

-/

@[expose] public section

noncomputable section

namespace LatticeFermions

/-!

## A. Graded local nets

-/

/-- A graded local net over the sites `V` in a C⋆-algebra `𝔄`: monotone, norm closed local star
subalgebras of the finite regions, an involutive parity automorphism preserving them, and even-odd
locality. -/
structure GradedLocalNet (V : Type*) (𝔄 : Type*) [CStarAlgebra 𝔄] where
  /-- The local algebra of a finite region. -/
  loc : Finset V → StarSubalgebra ℂ 𝔄
  /-- A larger region has a larger local algebra. -/
  loc_mono : Monotone loc
  /-- The local algebras are norm closed. -/
  isClosed_loc : ∀ X, IsClosed (loc X : Set 𝔄)
  /-- The parity automorphism. -/
  parity : 𝔄 ≃⋆ₐ[ℂ] 𝔄
  /-- The parity is an involution. -/
  parity_parity : ∀ a, parity (parity a) = a
  /-- The parity preserves every local algebra. -/
  parity_mem : ∀ {X : Finset V} {a : 𝔄}, a ∈ loc X → parity a ∈ loc X
  /-- Even-odd locality: an even element commutes with the local algebra of a disjoint
  region. -/
  commute_of_disjoint : ∀ {X Y : Finset V}, Disjoint X Y → ∀ {a b : 𝔄}, a ∈ loc X →
    b ∈ loc Y → parity b = b → Commute a b

namespace GradedLocalNet

variable {V : Type*} {𝔄 : Type*} [CStarAlgebra 𝔄] (N : GradedLocalNet V 𝔄)

/-!

## B. Even elements

-/

/-- An element is even if the parity fixes it. -/
def IsEven (a : 𝔄) : Prop := N.parity a = a

variable {N}

lemma IsEven.mul {a b : 𝔄} (ha : N.IsEven a) (hb : N.IsEven b) : N.IsEven (a * b) := by
  simp only [IsEven, map_mul] at *; rw [ha, hb]

lemma IsEven.add {a b : 𝔄} (ha : N.IsEven a) (hb : N.IsEven b) : N.IsEven (a + b) := by
  simp only [IsEven, map_add] at *; rw [ha, hb]

lemma IsEven.smul {a : 𝔄} (ha : N.IsEven a) (c : ℂ) : N.IsEven (c • a) := by
  simp only [IsEven, map_smul] at *; rw [ha]

lemma IsEven.star {a : 𝔄} (ha : N.IsEven a) : N.IsEven (star a) := by
  simp only [IsEven, map_star] at *; rw [ha]

lemma isEven_one : N.IsEven 1 := map_one N.parity

lemma isEven_algebraMap (c : ℂ) : N.IsEven (algebraMap ℂ 𝔄 c) := by
  simp [IsEven, Algebra.algebraMap_eq_smul_one, map_smul]

/-- An even element of `𝔄_Y` commutes with `𝔄_X` for disjoint `X` and `Y`, with the even element
on the left. -/
lemma commute_of_isEven {X Y : Finset V} (hXY : Disjoint X Y) {a b : 𝔄} (ha : a ∈ N.loc X)
    (hb : b ∈ N.loc Y) (hbe : N.IsEven b) : Commute b a :=
  (N.commute_of_disjoint hXY ha hb hbe).symm

/-- The even part `(a + Θ a) / 2` of an element. -/
def evenPart (N : GradedLocalNet V 𝔄) (a : 𝔄) : 𝔄 := (1 / 2 : ℂ) • (a + N.parity a)

lemma isEven_evenPart (a : 𝔄) : N.IsEven (N.evenPart a) := by
  simp only [IsEven, evenPart, map_smul, map_add, N.parity_parity, add_comm]

lemma evenPart_mem {X : Finset V} {a : 𝔄} (ha : a ∈ N.loc X) : N.evenPart a ∈ N.loc X :=
  (N.loc X).smul_mem ((N.loc X).add_mem ha (N.parity_mem ha)) _

lemma evenPart_of_isEven {a : 𝔄} (ha : N.IsEven a) : N.evenPart a = a := by
  rw [evenPart, show N.parity a = a from ha, ← two_smul ℂ a, smul_smul]; norm_num

/-!

## C. The local and quasi-local algebras

-/

variable (N)

lemma directed_loc : Directed (· ≤ ·) N.loc := by
  classical
  exact fun X Y => ⟨X ∪ Y, N.loc_mono Finset.subset_union_left,
    N.loc_mono Finset.subset_union_right⟩

/-- The star subalgebra of local elements: the union of the local algebras. -/
def localUnion : StarSubalgebra ℂ 𝔄 := ⨆ X, N.loc X

lemma mem_localUnion_iff [Nonempty V] {a : 𝔄} : a ∈ N.localUnion ↔ ∃ X, a ∈ N.loc X := by
  rw [localUnion, ← SetLike.mem_coe, StarSubalgebra.coe_iSup_of_directed N.directed_loc,
    Set.mem_iUnion]
  rfl

lemma loc_le_localUnion (X : Finset V) : N.loc X ≤ N.localUnion := le_iSup N.loc X

/-- The quasi-local algebra: the norm closure of the local elements. -/
def quasiLocal : StarSubalgebra ℂ 𝔄 := N.localUnion.topologicalClosure

lemma localUnion_le_quasiLocal : N.localUnion ≤ N.quasiLocal :=
  StarSubalgebra.le_topologicalClosure _

lemma loc_le_quasiLocal (X : Finset V) : N.loc X ≤ N.quasiLocal :=
  (N.loc_le_localUnion X).trans N.localUnion_le_quasiLocal

lemma isClosed_quasiLocal : IsClosed (N.quasiLocal : Set 𝔄) :=
  StarSubalgebra.isClosed_topologicalClosure _

/-!

## D. Spin systems

-/

/-- A spin system: local algebras of disjoint regions commute, and the parity is trivial. -/
def ofCommute (loc : Finset V → StarSubalgebra ℂ 𝔄) (loc_mono : Monotone loc)
    (isClosed_loc : ∀ X, IsClosed (loc X : Set 𝔄))
    (hcomm : ∀ {X Y : Finset V}, Disjoint X Y → ∀ {a b : 𝔄}, a ∈ loc X → b ∈ loc Y →
      Commute a b) : GradedLocalNet V 𝔄 where
  loc := loc
  loc_mono := loc_mono
  isClosed_loc := isClosed_loc
  parity := StarAlgEquiv.refl ℂ 𝔄
  parity_parity _ := rfl
  parity_mem h := h
  commute_of_disjoint hXY _ _ ha hb _ := hcomm hXY ha hb

lemma isEven_ofCommute (loc : Finset V → StarSubalgebra ℂ 𝔄) (loc_mono : Monotone loc)
    (isClosed_loc : ∀ X, IsClosed (loc X : Set 𝔄))
    (hcomm : ∀ {X Y : Finset V}, Disjoint X Y → ∀ {a b : 𝔄}, a ∈ loc X → b ∈ loc Y →
      Commute a b) (a : 𝔄) : (ofCommute loc loc_mono isClosed_loc hcomm).IsEven a := rfl

/-!

## E. Graded local nets from norm closures

A net of local star subalgebras which is not closed gives a graded local net by passing to the
norm closures. The parity is continuous, and even-odd locality passes to limits: an element of
the closure of `𝔄_Y` is a limit of elements of `𝔄_Y`, whose even parts converge to its even part.

-/

section closure

variable (θ : 𝔄 ≃⋆ₐ[ℂ] 𝔄)

/-- The even part `(a + θ a) / 2` of an element for an automorphism `θ`. -/
def evenPartOf (a : 𝔄) : 𝔄 := (1 / 2 : ℂ) • (a + θ a)

lemma continuous_evenPartOf : Continuous (evenPartOf θ) :=
  (continuous_id.add (StarAlgEquiv.isometry θ).continuous).const_smul _

lemma evenPartOf_of_eq {a : 𝔄} (ha : θ a = a) : evenPartOf θ a = a := by
  rw [evenPartOf, ha, ← two_smul ℂ a, smul_smul]; norm_num

lemma map_evenPartOf (hθ : ∀ a, θ (θ a) = a) (a : 𝔄) : θ (evenPartOf θ a) = evenPartOf θ a := by
  simp only [evenPartOf, map_smul, map_add, hθ, add_comm]

lemma evenPartOf_mem {T : StarSubalgebra ℂ 𝔄} (hT : ∀ b ∈ T, θ b ∈ T) {a : 𝔄} (ha : a ∈ T) :
    evenPartOf θ a ∈ T :=
  T.smul_mem (T.add_mem ha (hT a ha)) _

/-- Even-odd locality passes to the norm closures. -/
lemma commute_of_mem_topologicalClosure (hθ : ∀ a, θ (θ a) = a) {S T : StarSubalgebra ℂ 𝔄}
    (hT : ∀ b ∈ T, θ b ∈ T) (h : ∀ a ∈ S, ∀ b ∈ T, θ b = b → Commute a b) {a b : 𝔄}
    (ha : a ∈ S.topologicalClosure) (hb : b ∈ T.topologicalClosure) (hbe : θ b = b) :
    Commute a b := by
  have h1 : ∀ c ∈ T, Commute a (evenPartOf θ c) := fun c hc =>
    closure_minimal (s := (S : Set 𝔄)) (t := {a' | Commute a' (evenPartOf θ c)})
      (fun a' ha' => h a' ha' _ (evenPartOf_mem θ hT hc) (map_evenPartOf θ hθ c))
      (isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)) ha
  have h2 := closure_minimal (s := (T : Set 𝔄)) (t := {c | Commute a (evenPartOf θ c)}) h1
    ((isClosed_eq (continuous_const.mul continuous_id)
      (continuous_id.mul continuous_const)).preimage (continuous_evenPartOf θ)) hb
  simpa [evenPartOf_of_eq θ hbe] using h2

lemma map_mem_topologicalClosure {T : StarSubalgebra ℂ 𝔄} (hT : ∀ b ∈ T, θ b ∈ T) {b : 𝔄}
    (hb : b ∈ T.topologicalClosure) : θ b ∈ T.topologicalClosure :=
  closure_minimal (s := (T : Set 𝔄)) (t := θ ⁻¹' (T.topologicalClosure : Set 𝔄))
    (fun c hc => T.le_topologicalClosure (hT c hc))
    ((T.isClosed_topologicalClosure).preimage (StarAlgEquiv.isometry θ).continuous) hb

/-- The graded local net of the norm closures of a monotone net of local star subalgebras with
an involutive parity preserving them and even-odd locality. -/
def ofClosure (loc : Finset V → StarSubalgebra ℂ 𝔄) (loc_mono : Monotone loc)
    (hθ : ∀ a, θ (θ a) = a) (hmem : ∀ X, ∀ b ∈ loc X, θ b ∈ loc X)
    (hcomm : ∀ {X Y : Finset V}, Disjoint X Y → ∀ a ∈ loc X, ∀ b ∈ loc Y, θ b = b →
      Commute a b) : GradedLocalNet V 𝔄 where
  loc X := (loc X).topologicalClosure
  loc_mono _ _ h := StarSubalgebra.topologicalClosure_mono (loc_mono h)
  isClosed_loc X := (loc X).isClosed_topologicalClosure
  parity := θ
  parity_parity := hθ
  parity_mem h := map_mem_topologicalClosure θ (hmem _) h
  commute_of_disjoint hXY _ _ ha hb hbe :=
    commute_of_mem_topologicalClosure θ hθ (hmem _) (fun a ha b hb => hcomm hXY a ha b hb) ha hb
      hbe

lemma ofClosure_loc (loc : Finset V → StarSubalgebra ℂ 𝔄) (loc_mono : Monotone loc)
    (hθ : ∀ a, θ (θ a) = a) (hmem : ∀ X, ∀ b ∈ loc X, θ b ∈ loc X)
    (hcomm : ∀ {X Y : Finset V}, Disjoint X Y → ∀ a ∈ loc X, ∀ b ∈ loc Y, θ b = b →
      Commute a b) (X : Finset V) :
    (ofClosure θ loc loc_mono hθ hmem hcomm).loc X = (loc X).topologicalClosure := rfl

end closure

end GradedLocalNet

end LatticeFermions
