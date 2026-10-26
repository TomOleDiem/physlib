/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.CondensedMatter.Crystal.Symmetries
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Shifts and point operations of a crystal

A symmetry of a crystal is determined by where it sends the reference cell.

## i. Overview

A crystal is a repeating pattern: every site is a copy of a site in a unit cell. Its symmetries can
turn the lattice, permute the sites of the unit cell, and move atoms from one cell to another.

Despite this freedom, a symmetry is determined by three pieces of data: a lattice automorphism `A`,
a permutation `σ` of the labels of the unit cell, and an offset `bᵢ` for each label `i`. It sends
the site with label `i` in the cell `n` to

`(n, i) ↦ (A n + bᵢ, σ i)`,

and any such data gives a symmetry. This splits every symmetry into a point operation, which turns
the lattice and permutes the labels, followed by a shift, which moves the sites of each label along
the lattice. The symmetry group is the semidirect product of the shifts and the point operations,
and the product of two symmetries is read off from the data. This describes the symmetries of a
crystal algebraically, without embedding it in Euclidean space. Once geometry is added, the point
operations give the point group of crystallography.

## ii. Key results

- `Crystal.Symmetry.ofComponents` : the symmetry `(n, i) ↦ (A n + b i, σ i)` with lattice
  automorphism `A`, label permutation `σ` and offsets `b`.
- `Crystal.Symmetry.eq_ofComponents` : every symmetry is of this form, with `A`, `σ` and
  `b` its lattice automorphism, `labelHom` and `offset`.
- `Crystal.Symmetry.ofComponents_mul` : the product is
  `(A, σ, b) * (A', σ', b') = (A + A', σ * σ', A ∘ b' + b ∘ σ')`.
- `Crystal.Symmetry.semidirectEquiv` : the symmetry group is isomorphic to the semidirect product
  `(F → G) ⋊ (Aut G × Sym F)` of the shifts and the point operations.
- `Crystal.Symmetry.pointOp` : the point operation of a symmetry, a homomorphism.
- `Crystal.Symmetry.pointOp_eq_one_iff` : the symmetries with trivial point operation are the
  shifts.

## iii. Table of contents

- A. The data of a symmetry
  - A.1. Offsets
  - A.2. Symmetries from data
  - A.3. Products
- B. Shifts and point operations
  - B.1. Shifts
  - B.2. Point operations
  - B.3. Composites
- C. The semidirect product
- D. The point operation of a symmetry

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace Physlib.CondensedMatter.Crystal

variable {G : Type*} [AddCommGroup G] [AddGroup.FG G]

namespace Symmetry

variable {C : Crystal G} (A B : G ≃+ G) (σ τ : Equiv.Perm C.UnitCell)
  (b b' c c' : C.UnitCell → G)

/-! ## A. The data of a symmetry -/

/-! ### A.1. Offsets -/

/-- The offset of a symmetry at the label `i`. The point `i` in the reference cell gets mapped to
`φ ⟨0, i⟩`. The offset is the cell, labeled by a lattice vector in `G`, in which this new point
lives. -/
def offset (φ : Symmetry C) (i : C.UnitCell) : G := (φ ⟨0, i⟩).cell

/-- A symmetry moves the site `⟨n, i⟩` to the cell `A n + b i` and the label `σ i`. -/
lemma apply_eq_data (φ : Symmetry C) (x : C.Site) :
    φ x = ⟨φ.lattice x.cell + φ.offset x.label, labelHom C φ x.label⟩ :=
  apply_eq φ x.cell x.label

/-- The cell of the image of a site. -/
lemma cell_apply (φ : Symmetry C) (x : C.Site) :
    (φ x).cell = φ.lattice x.cell + φ.offset x.label :=
  congrArg Site.cell (apply_eq_data φ x)

/-! ### A.2. Symmetries from data -/

/-- The permutation of the sites `⟨n, i⟩ ↦ ⟨A n + b i, σ i⟩`. -/
def componentsEquiv (C : Crystal G) (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell)
    (b : C.UnitCell → G) :
    C.Site ≃ C.Site where
  toFun x := ⟨A x.cell + b x.label, σ x.label⟩
  invFun x := ⟨A.symm (x.cell - b (σ.symm x.label)), σ.symm x.label⟩
  left_inv x := Site.ext (by simp) (by simp)
  right_inv x := Site.ext (by simp) (by simp)

/-- The symmetry with lattice automorphism `A`, label permutation `σ` and offsets `b`. -/
def ofComponents (C : Crystal G) (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell)
    (b : C.UnitCell → G) :
    Symmetry C :=
  ⟨A, { toFun := componentsEquiv C A σ b
        map_vadd' _ _ := Site.ext (by simp [componentsEquiv, Site.vadd_def, add_assoc]) rfl },
    (componentsEquiv C A σ b).bijective⟩

/-- The symmetry with this data moves `⟨n, i⟩` to `⟨A n + b i, σ i⟩`. -/
@[simp] lemma ofComponents_apply (x : C.Site) :
    ofComponents C A σ b x = ⟨A x.cell + b x.label, σ x.label⟩ := rfl

@[simp] lemma lattice_ofComponents :
    (ofComponents C A σ b).lattice = A := rfl

@[simp] lemma labelHom_ofComponents :
    labelHom C (ofComponents C A σ b) = σ :=
  Equiv.ext (congrFun rfl)

@[simp] lemma offset_ofComponents :
    (ofComponents C A σ b).offset = b := by
  ext i
  show A 0 + b i = b i
  rw [map_zero, zero_add]

/-- Every symmetry is given by its lattice automorphism, label permutation and offsets. -/
lemma eq_ofComponents (φ : Symmetry C) :
    φ = ofComponents C φ.lattice (labelHom C φ) φ.offset := by
  ext x : 1
  exact apply_eq_data φ x

/-! ### A.3. Products -/

/-- The product of two symmetries, from their data.
`(A, σ, b) * (A', σ', b') = (A + A', σ * σ', A ∘ b' + b ∘ σ')`, where `A + A'` is the composite
`A ∘ A'`. -/
lemma ofComponents_mul :
    ofComponents C A σ b * ofComponents C B τ b' =
      ofComponents C (A + B) (σ * τ) (A ∘ b' + b ∘ τ) := by
  ext x : 1
  refine Site.ext ?_ rfl
  show A (B x.cell + b' x.label) + b (τ x.label) = (A + B) x.cell + (A (b' x.label) + b (τ x.label))
  rw [map_add, add_assoc]
  rfl

/-! ## B. Shifts and point operations -/

/-! ### B.1. Shifts -/

/-- Move every site with label `i` by the lattice vector `c i`. -/
def shift (C : Crystal G) (c : C.UnitCell → G) : Symmetry C := ofComponents C 0 1 c

/-- A shift does not change the lattice. -/
@[simp] lemma lattice_shift : (shift C c).lattice = 0 := rfl

/-- A shift that moves every label by the same vector is a translation. -/
lemma shift_const (a : G) : shift C (Function.const C.UnitCell a) = translation C a := by
  ext x : 1
  exact Site.ext (add_comm _ _) rfl

/-- Shifts add. -/
lemma shift_add : shift C (c + c') = shift C c * shift C c' := by
  show ofComponents C 0 1 (c + c') =
    ofComponents C 0 1 c * ofComponents C 0 1 c'
  rw [ofComponents_mul]
  simp [add_comm]

/-! ### B.2. Point operations -/

/-- Apply the lattice automorphism `A` to the cells and permute the labels within the cells by
`σ`. -/
def linear (C : Crystal G) (A : G ≃+ G) (σ : Equiv.Perm C.UnitCell) : Symmetry C :=
  ofComponents C A σ 0

/-- The lattice part of a point operation is its lattice automorphism. -/
@[simp] lemma lattice_linear :
    (linear C A σ).lattice = A := rfl

/-- A point operation moves `⟨n, i⟩` to `⟨A n, σ i⟩`. -/
@[simp] lemma linear_apply (x : C.Site) :
    linear C A σ x = ⟨A x.cell, σ x.label⟩ :=
  Site.ext (add_zero _) rfl

/-- Point operations compose. -/
lemma linear_add_mul :
    linear C (A + B) (σ * τ) = linear C A σ * linear C B τ := by
  show ofComponents C (A + B) (σ * τ) 0 =
    ofComponents C A σ 0 * ofComponents C B τ 0
  rw [ofComponents_mul]
  simp

/-! ### B.3. Composites -/

/-- A shift followed by a point operation is the symmetry with offsets `c ∘ σ`. -/
lemma shift_mul_linear :
    shift C c * linear C A σ = ofComponents C A σ (c ∘ σ) := by
  show ofComponents C 0 1 c * ofComponents C A σ 0 = _
  rw [ofComponents_mul]
  simp

@[simp] lemma labelHom_shift_mul_linear : labelHom C (shift C c * linear C A σ) = σ := by
  rw [shift_mul_linear, labelHom_ofComponents]

@[simp] lemma offset_shift_mul_linear : (shift C c * linear C A σ).offset = c ∘ σ := by
  rw [shift_mul_linear, offset_ofComponents]

/-- The product of shifts and point operations. With `A + B` the composite `A ∘ B`,
`(c, A, σ) * (c', B, τ) = (c + A ∘ c' ∘ σ⁻¹, A + B, σ * τ)`. -/
lemma shift_mul_linear_mul :
    (shift C c * linear C A σ) * (shift C c' * linear C B τ) =
      shift C (c + A ∘ c' ∘ σ.symm) * linear C (A + B) (σ * τ) := by
  rw [shift_mul_linear, shift_mul_linear, shift_mul_linear, ofComponents_mul]
  congr 1
  ext i
  simp [add_comm]

/-! ## C. The semidirect product -/

/-- The lattice automorphism and label permutation act on the shifts by `c ↦ A ∘ c ∘ σ⁻¹`. -/
def shiftAction (C : Crystal G) :
    Multiplicative (AddAut G) × Equiv.Perm C.UnitCell →*
      MulAut (Multiplicative (C.UnitCell → G)) where
  toFun p := (AddEquiv.arrowCongr p.2 (Multiplicative.toAdd p.1)).toMultiplicative
  map_one' := MulEquiv.ext (congrFun rfl)
  map_mul' _ _ := MulEquiv.ext (congrFun rfl)

/-- Every symmetry is a point operation followed by a shift. -/
lemma eq_shift_mul_linear (φ : Symmetry C) :
    φ = shift C (φ.offset ∘ (labelHom C φ).symm) * linear C φ.lattice (labelHom C φ) := by
  have h : (φ.offset ∘ ⇑(labelHom C φ).symm) ∘ ⇑(labelHom C φ) = φ.offset := by
    ext i
    simp
  rw [shift_mul_linear, h]
  exact eq_ofComponents φ

/-- The symmetry group of a crystal is the semidirect product of the shifts of each label with
the lattice automorphisms and label permutations. -/
noncomputable def semidirectEquiv (C : Crystal G) :
    Multiplicative (C.UnitCell → G) ⋊[shiftAction C]
      (Multiplicative (AddAut G) × Equiv.Perm C.UnitCell) ≃* Symmetry C where
  toFun y := shift C (Multiplicative.toAdd y.left) *
    linear C (Multiplicative.toAdd y.right.1) y.right.2
  invFun φ := ⟨Multiplicative.ofAdd (φ.offset ∘ (labelHom C φ).symm),
    Multiplicative.ofAdd φ.lattice, labelHom C φ⟩
  left_inv y := by
    refine SemidirectProduct.ext (Multiplicative.toAdd.injective ?_) (Prod.ext (by simp) (by simp))
    ext i
    simp
  right_inv φ := (eq_shift_mul_linear φ).symm
  map_mul' _ _ := (shift_mul_linear_mul _ _ _ _ _ _).symm

/-! ## D. The point operation of a symmetry -/

/-- The point operation of a symmetry: keep its lattice automorphism and its permutation of the
labels, and drop the shifts. It fixes the reference cell's position, so for `ℤᵈ` it is the rotation
or reflection of the lattice. -/
noncomputable def pointOp (C : Crystal G) : Symmetry C →* Symmetry C where
  toFun φ := linear C φ.lattice (labelHom C φ)
  map_one' := by
    ext x : 1
    exact Site.ext (add_zero _) rfl
  map_mul' φ ψ := by
    rw [lattice_mul, map_mul]
    exact linear_add_mul _ _ _ _

/-- Every symmetry is a shift followed by its point operation. -/
lemma exists_eq_shift_mul_pointOp (φ : Symmetry C) : ∃ c, φ = shift C c * pointOp C φ :=
  ⟨_, eq_shift_mul_linear φ⟩

/-- The point operation of a shift is trivial. -/
@[simp] lemma pointOp_shift : pointOp C (shift C c) = 1 := by
  ext x : 1
  exact Site.ext (add_zero _) rfl

/-- The symmetries with trivial point operation are exactly the shifts. -/
lemma pointOp_eq_one_iff (φ : Symmetry C) : pointOp C φ = 1 ↔ ∃ c, φ = shift C c := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := exists_eq_shift_mul_pointOp φ
    exact ⟨c, by rw [hc, h, mul_one]⟩
  · rintro ⟨c, rfl⟩
    exact pointOp_shift c

/-- Translations have trivial point operation. -/
lemma pointOp_translation (a : G) : pointOp C (translation C a) = 1 := by
  rw [← shift_const]
  exact pointOp_shift _

end Symmetry

end Physlib.CondensedMatter.Crystal
