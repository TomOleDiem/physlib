/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.Mathematics.OperatorAlgebra.Basic

/-!

# Channels, and the hierarchy of dynamics built from them

`Channel` itself is defined in `Basic.lean` (it needs no more than `Mathlib`'s
`CompletelyPositiveMap`). This file has its elementary API — composition, the identity channel,
`Channel A A`'s monoid structure — and the hierarchy of dynamics built on top of it, from the most
general down to the most special:

* `EvolutionFamily`: the most general dynamics this framework expresses — a channel for every
  ordered pair of times, constrained only by the cocycle law. What a time-dependent Hamiltonian or
  time-dependent Lindbladian produces.
* `ChannelSemigroup`: the time-homogeneous special case, where the channel from `s` to `t` depends
  only on `t - s`. Markov processes, quantum channels, Lindblad evolution with a time-independent
  generator.
* `RevDynamics` (`Dynamics.lean`): the further special case where every channel is also invertible
  — reversible dynamics.

-/

@[expose] public section

open scoped CStarAlgebra NNReal

namespace OperatorAlgebra

noncomputable instance Channel.instCoeFun {A₁ A₂ : Type*}
    [CStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁]
    [CStarAlgebra A₂] [PartialOrder A₂] [StarOrderedRing A₂] :
    CoeFun (Channel A₁ A₂) (fun _ => A₁ → A₂) where
  coe φ := (φ : A₁ →CP A₂)


/-!
## Composition

`Channel A A` is a monoid under composition, exactly as `A ≃⋆ₐ[ℂ] A` is a group under composition
for `RevDynamics`. This is what lets `ChannelSemigroup` below reuse `AddChar`, the same way
`RevDynamics` does: a group is a monoid, so `AddChar`'s only requirement (`[Monoid M]` on the
target) is satisfied either way.
-/

namespace CompletelyPositiveMap

variable {A₁ A₂ A₃ : Type*}
  [CStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁]
  [CStarAlgebra A₂] [PartialOrder A₂] [StarOrderedRing A₂]
  [CStarAlgebra A₃] [PartialOrder A₃] [StarOrderedRing A₃]

/-- The composite of two completely positive maps is completely positive. -/
noncomputable def comp (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) : A₁ →CP A₃ where
  toLinearMap := (ψ : A₂ →ₗ[ℂ] A₃) ∘ₗ (φ : A₁ →ₗ[ℂ] A₂)
  map_cstarMatrix_nonneg' k M hM := by
    have h1 : (0 : CStarMatrix (Fin k) (Fin k) A₂) ≤ M.map φ :=
      φ.map_cstarMatrix_nonneg M hM
    have h2 : (0 : CStarMatrix (Fin k) (Fin k) A₃) ≤ (M.map φ).map ψ :=
      ψ.map_cstarMatrix_nonneg _ h1
    have heq : (M.map φ).map ψ =
        M.map ⇑((ψ : A₂ →ₗ[ℂ] A₃) ∘ₗ (φ : A₁ →ₗ[ℂ] A₂)) := by
      ext i j
      simp [CStarMatrix.map_apply]
    rwa [heq] at h2

@[simp]
lemma comp_apply (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) (a : A₁) :
    comp ψ φ a = ψ (φ a) :=
  rfl

end CompletelyPositiveMap


namespace Channel

variable {A₁ A₂ A₃ : Type*}
  [CStarAlgebra A₁] [PartialOrder A₁] [StarOrderedRing A₁]
  [CStarAlgebra A₂] [PartialOrder A₂] [StarOrderedRing A₂]
  [CStarAlgebra A₃] [PartialOrder A₃] [StarOrderedRing A₃]

/-- The composite of two channels is again a channel. -/
noncomputable def comp (ψ : Channel A₂ A₃) (φ : Channel A₁ A₂) : Channel A₁ A₃ :=
  ⟨CompletelyPositiveMap.comp (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂), by
    show CompletelyPositiveMap.comp (ψ : A₂ →CP A₃) (φ : A₁ →CP A₂) 1 = 1
    rw [CompletelyPositiveMap.comp_apply, φ.property, ψ.property]⟩

@[simp]
lemma comp_apply (ψ : Channel A₂ A₃) (φ : Channel A₁ A₂) (a : A₁) :
    comp ψ φ a = ψ (φ a) :=
  rfl

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The identity map is a channel. -/
noncomputable def id : Channel A A :=
  ⟨(StarAlgHom.id ℂ A : A →CP A), by
    show (StarAlgHom.id ℂ A : A →CP A) 1 = 1
    rfl⟩

@[simp]
lemma id_apply (a : A) : (id : Channel A A) a = a :=
  rfl

noncomputable instance instMonoid : Monoid (Channel A A) where
  mul φ ψ := comp φ ψ
  mul_assoc φ ψ χ := Subtype.ext (DFunLike.ext _ _ fun a => rfl)
  one := id
  one_mul φ := Subtype.ext (DFunLike.ext _ _ fun a => rfl)
  mul_one φ := Subtype.ext (DFunLike.ext _ _ fun a => rfl)

end Channel


/--
A one-parameter semigroup of channels on `A` — *time-homogeneous* dynamics: the channel evolving
the system from time `s` to time `t` depends only on the elapsed time `t - s`. Covers Markov
processes, quantum channels, and Lindblad evolution with a time-independent generator.
`RevDynamics` (`Dynamics.lean`) is the further special case where every channel in the family
happens to be invertible.
-/
noncomputable abbrev ChannelSemigroup (A : Type*)
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] :=
  AddChar ℝ≥0 (Channel A A)


/-!
## The most general dynamics

`ChannelSemigroup` still assumes time-homogeneity. Dropping that assumption gives the most general
notion of dynamics this framework can express: a two-parameter family of channels, one for every
ordered pair of times, satisfying only the cocycle law. A time-dependent Hamiltonian or a
time-dependent Lindbladian produces one of these; neither need come from any `ChannelSemigroup`.
-/

/--
The most general dynamics on `A`: a channel `evolve s t h : Channel A A` for every `s ≤ t`, "the
system's evolution from time `s` to time `t`". `evolve_self` says evolving over an empty interval
does nothing; `evolve_comp` is the cocycle law, that evolving `r → s` then `s → t` agrees with
evolving `r → t` directly.

Neither invertibility nor time-homogeneity is assumed:

* `ChannelSemigroup` is the special time-homogeneous case, `evolve s t h = T (t - s)` for a
  single `T : ChannelSemigroup A`;
* `RevDynamics` is the further special case where every channel is also invertible.
-/
structure EvolutionFamily (A : Type*)
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] where
  /-- The channel evolving the system from time `s` to time `t`, for `s ≤ t`. -/
  evolve (s t : ℝ) (h : s ≤ t) : Channel A A
  /-- Evolving over an empty interval does nothing. -/
  evolve_self (t : ℝ) : evolve t t le_rfl = 1
  /-- The cocycle law: evolving in two steps agrees with evolving directly. -/
  evolve_comp (r s t : ℝ) (hrs : r ≤ s) (hst : s ≤ t) :
      (evolve s t hst).comp (evolve r s hrs) = evolve r t (hrs.trans hst)


/-- Every channel semigroup is, in particular, an evolution family: the time-homogeneous one
with `evolve s t h := T (t - s)`. -/
noncomputable def ChannelSemigroup.toEvolutionFamily {A : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (T : ChannelSemigroup A) :
    EvolutionFamily A where
  evolve s t _ := T (t - s).toNNReal
  evolve_self t := by
    show T (t - t).toNNReal = 1
    rw [sub_self, Real.toNNReal_zero, T.map_zero_eq_one]
  evolve_comp r s t hrs hst := by
    show T (t - s).toNNReal * T (s - r).toNNReal = T (t - r).toNNReal
    rw [← T.map_add_eq_mul, ← Real.toNNReal_add (by linarith) (by linarith)]
    congr 2
    ring

end OperatorAlgebra
