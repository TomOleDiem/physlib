/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OperatorAlgebra.Basic

/-!

# Elementary properties of observables

Elementary facts about `Observable A := selfAdjoint A`.

-/

@[expose] public section

namespace OperatorAlgebra

/--
A ⋆-algebra equivalence restricts to a real-linear equivalence of self-adjoint elements.

Stated for `selfAdjoint` rather than `Observable`, so it applies even when the codomain is not
itself a `CStarAlgebra` (e.g. a bare matrix algebra).
-/
def _root_.StarAlgEquiv.selfAdjointCongr {A B : Type*}
    [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℝ A]
    [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℝ B]
    (e : A ≃⋆ₐ[ℂ] B) :
    selfAdjoint A ≃ₗ[ℝ] selfAdjoint B where
  toFun a := ⟨e a, a.property.map e⟩
  invFun b := ⟨e.symm b, b.property.map e.symm⟩
  left_inv a := Subtype.ext (e.symm_apply_apply (a : A))
  right_inv b := Subtype.ext (e.apply_symm_apply (b : B))
  map_add' a b := Subtype.ext (map_add e (a : A) (b : A))
  map_smul' r a := Subtype.ext (by
    show e (r • (a : A)) = r • e (a : A)
    rw [← Complex.coe_smul, map_smul, Complex.coe_smul])

end OperatorAlgebra
