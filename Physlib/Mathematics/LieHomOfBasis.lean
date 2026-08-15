/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
/-!

# Lifting a Lie-bracket check from a basis to everywhere

## i. Overview

Lifts a `K`-linear map between two Lie `K`-algebras from a bracket-check on basis *pairs* to a
bracket-check everywhere. Reused wherever a bilinear construction (`gl(d)`'s matrix units, in
`LadderSystem/Basic.lean`) needs its bracket-compatibility checked only on generators.

## ii. Key results

- `LinearMap.lie_apply_eq_of_lie_basis_eq` : a `K`-linear map agreeing with the bracket on basis
    pairs agrees with the bracket everywhere.

-/

@[expose] public section

noncomputable section

open Module (Basis)

variable {K : Type*} [Field K]

section BracketLinearMaps

variable (L : Type*) [LieRing L] [LieAlgebra K L]

/-- Bracketing on the right by a fixed element, as a `K`-linear self-map. -/
def bracketRight (y : L) : L →ₗ[K] L where
  toFun x := ⁅x, y⁆
  map_add' a c := add_lie a c y
  map_smul' c a := smul_lie c a y

/-- Bracketing on the left by a fixed element, as a `K`-linear self-map. -/
def bracketLeft (x : L) : L →ₗ[K] L where
  toFun y := ⁅x, y⁆
  map_add' := lie_add x
  map_smul' c a := lie_smul c x a

end BracketLinearMaps

variable {L L' : Type*} [LieRing L] [LieAlgebra K L] [LieRing L'] [LieAlgebra K L']
variable {ι : Type*}

/-- A `K`-linear map agreeing with the bracket on basis pairs agrees with the bracket
everywhere. -/
lemma LinearMap.lie_apply_eq_of_lie_basis_eq (b : Basis ι K L) (f : L →ₗ[K] L')
    (h : ∀ i j, f ⁅b i, b j⁆ = ⁅f (b i), f (b j)⁆) (x y : L) :
    f ⁅x, y⁆ = ⁅f x, f y⁆ := by
  have step1 : ∀ j : ι,
      f.comp (bracketRight L (b j)) = (bracketRight L' (f (b j))).comp f := by
    intro j
    apply b.ext
    intro i
    change f ⁅b i, b j⁆ = ⁅f (b i), f (b j)⁆
    exact h i j
  have step2 : f.comp (bracketLeft L x) = (bracketLeft L' (f x)).comp f := by
    apply b.ext
    intro j
    have hx := DFunLike.congr_fun (step1 j) x
    change f ⁅x, b j⁆ = ⁅f x, f (b j)⁆ at hx
    exact hx
  exact DFunLike.congr_fun step2 y
