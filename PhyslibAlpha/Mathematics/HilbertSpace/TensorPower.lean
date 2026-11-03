/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.TensorProducts.CompleteTensorProduct
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Slope
/-!

# Hilbert tensor powers and the symmetric subspace

The `n`-fold complete tensor power of an arbitrary Hilbert space and its symmetric subspace.

## i. Overview

The state space of `n` identical particles with one-particle space `h` is a subspace of the Hilbert
tensor power of `h`. The tensor power is defined by recursion. Its zeroth power is the scalars and
its `(n+1)`-st power is `h ⊗ₕ (n-th power)`. No basis of `h` is chosen and `h` need not be separable.

The symmetric subspace is the closed span of the coherent vectors `f ⊗ ⋯ ⊗ f`. Its orthogonal
projection is the symmetrizer. A bounded operator `A` on `h` acts on every tensor power by
`A ⊗ ⋯ ⊗ A`, and it sends coherent vectors to coherent vectors.

## ii. Key results

- `HilbertPower.TPow`: the `n`-fold Hilbert tensor power.
- `HilbertPower.cons`: the product vector of a vector and an `n`-fold tensor.
- `HilbertPower.pow`: the coherent vector `f ⊗ ⋯ ⊗ f`.
- `HilbertPower.inner_pow`: `⟪f^n, g^n⟫ = ⟪f, g⟫ ^ n`.
- `HilbertPower.opPow`: the operator `A ⊗ ⋯ ⊗ A`.
- `HilbertPower.sym`, `HilbertPower.symProj`: the symmetric subspace and the symmetrizer.

## iii. Table of contents

- A. Operators on complete tensor products
- B. The tensor power
- C. Product vectors and coherent vectors
- D. The operator power
- E. The symmetric subspace

## iv. References

* None.
-/

@[expose] public section

universe u

open scoped CompleteTensorProduct TensorProduct InnerProductSpace

noncomputable section

/-!

## A. Operators on complete tensor products

-/

namespace CompleteTensorProduct

variable {E E' F F' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- The tensor product `f ⊗ g` of bounded operators on complete tensor products. -/
def mapL (f : E →L[ℂ] E') (g : F →L[ℂ] F') : E ⊗ₕ[ℂ] F →L[ℂ] E' ⊗ₕ[ℂ] F' :=
  ContinuousLinearMap.completion (TensorProduct.mapL f g)

lemma mapL_coe (f : E →L[ℂ] E') (g : F →L[ℂ] F') (x : E ⊗[ℂ] F) :
    mapL f g (coe' x) = coe' (TensorProduct.mapL f g x) :=
  ContinuousLinearMap.completion_apply_coe _ _

lemma mapL_tmul (f : E →L[ℂ] E') (g : F →L[ℂ] F') (x : E) (y : F) :
    mapL f g (coe' (x ⊗ₜ[ℂ] y)) = coe' (f x ⊗ₜ[ℂ] g y) := by
  rw [mapL_coe]
  rfl

/-- **The tensor product of operators is bounded by the product of the norms.** -/
lemma norm_mapL_le (f : E →L[ℂ] E') (g : F →L[ℂ] F') : ‖mapL f g‖ ≤ ‖f‖ * ‖g‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le (by fun_prop) (by fun_prop)
  | ih x =>
    change ‖mapL f g (coe' x)‖ ≤ ‖f‖ * ‖g‖ * ‖(coe' x : E ⊗ₕ[ℂ] F)‖
    rw [mapL_coe, norm_coe, norm_coe]
    exact (TensorProduct.mapL f g).le_of_opNorm_le (TensorProduct.norm_mapL_le f g) x

section Compose

variable {E'' F'' : Type*} [NormedAddCommGroup E''] [InnerProductSpace ℂ E'']
  [NormedAddCommGroup F''] [InnerProductSpace ℂ F'']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- Bounded maps on a complete tensor product are determined by their values on product vectors. -/
lemma ext_tmul {T T' : E ⊗ₕ[ℂ] F →L[ℂ] G}
    (h : ∀ x y, T (coe' (x ⊗ₜ[ℂ] y)) = T' (coe' (x ⊗ₜ[ℂ] y))) : T = T' := by
  ext z
  induction z using CompleteTensorProduct.induction_on with
  | tmul x y => exact h x y
  | add a b ha hb => rw [coe_add, map_add, map_add, ha, hb]
  | closed => exact isClosed_eq (by fun_prop) (by fun_prop)

lemma mapL_comp (f : E' →L[ℂ] E'') (f' : E →L[ℂ] E') (g : F' →L[ℂ] F'') (g' : F →L[ℂ] F') :
    mapL (f ∘L f') (g ∘L g') = mapL f g ∘L mapL f' g' := by
  refine ext_tmul fun x y => ?_
  simp [mapL_tmul]

lemma mapL_id : mapL (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ F) =
    ContinuousLinearMap.id ℂ (E ⊗ₕ[ℂ] F) := by
  refine ext_tmul fun x y => ?_
  simp [mapL_tmul]
end Compose

section Adjoint

variable [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F] [CompleteSpace F']

lemma inner_mapL_alg (f : E →L[ℂ] E') (g : F →L[ℂ] F') (x : E ⊗[ℂ] F) (y : E' ⊗[ℂ] F') :
    ⟪TensorProduct.mapL f g x, y⟫_ℂ =
      ⟪x, TensorProduct.mapL (ContinuousLinearMap.adjoint f) (ContinuousLinearMap.adjoint g) y⟫_ℂ := by
  induction x using TensorProduct.inductionOn with
  | add a b ha hb => rw [map_add, inner_add_left, inner_add_left, ha, hb]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add c d hc hd => rw [map_add, inner_add_right, inner_add_right, hc, hd]
    | tmul c d =>
      simp [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
        ContinuousLinearMap.adjoint_inner_right]

/-- The adjoint of a tensor product of operators. -/
lemma inner_mapL (f : E →L[ℂ] E') (g : F →L[ℂ] F') (u : E ⊗ₕ[ℂ] F) (v : E' ⊗ₕ[ℂ] F') :
    ⟪mapL f g u, v⟫_ℂ =
      ⟪u, mapL (ContinuousLinearMap.adjoint f) (ContinuousLinearMap.adjoint g) v⟫_ℂ := by
  refine UniformSpace.Completion.induction_on₂ u v ?_ fun x y => ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · show ⟪mapL f g (coe' x), coe' y⟫_ℂ = ⟪coe' x, mapL _ _ (coe' y)⟫_ℂ
    rw [mapL_coe, mapL_coe, inner_coe, inner_coe, inner_mapL_alg]
end Adjoint

end CompleteTensorProduct

/-!

## B. The tensor power

-/

namespace HilbertPower

/-- The scalars as a Hilbert space in any universe. -/
instance : InnerProductSpace ℂ (ULift.{u} ℂ) where
  inner x y := inner ℂ x.down y.down
  norm_sq_eq_re_inner x := norm_sq_eq_re_inner (𝕜 := ℂ) x.down
  conj_inner_symm x y := inner_conj_symm (𝕜 := ℂ) x.down y.down
  add_left x y z := inner_add_left (𝕜 := ℂ) x.down y.down z.down
  smul_left x y c := inner_smul_left (𝕜 := ℂ) x.down y.down c

/-- A bundled Hilbert space structure on a type. -/
structure HStr (E : Type u) where
  [nacg : NormedAddCommGroup E]
  [ips : InnerProductSpace ℂ E]
  [cs : CompleteSpace E]

variable (h : Type u) [NormedAddCommGroup h] [InnerProductSpace ℂ h]

/-- The tensor power together with its Hilbert space structure. -/
def powAux : (n : ℕ) → Σ E : Type u, HStr E
  | 0 => ⟨ULift.{u} ℂ, { }⟩
  | n + 1 =>
    letI := (powAux n).2.nacg
    letI := (powAux n).2.ips
    ⟨h ⊗ₕ[ℂ] (powAux n).1, { }⟩

/-- The `n`-fold Hilbert tensor power of `h`. -/
def TPow (n : ℕ) : Type u := (powAux h n).1

instance (n : ℕ) : NormedAddCommGroup (TPow h n) := (powAux h n).2.nacg
instance (n : ℕ) : InnerProductSpace ℂ (TPow h n) := (powAux h n).2.ips
instance (n : ℕ) : CompleteSpace (TPow h n) := (powAux h n).2.cs

/-- The recursion `h^{⊗(n+1)} = h ⊗ₕ h^{⊗n}`. -/
def succEquiv (n : ℕ) : TPow h (n + 1) ≃ₗᵢ[ℂ] h ⊗ₕ[ℂ] TPow h n := LinearIsometryEquiv.refl _ _

/-!

## C. Product vectors and coherent vectors

-/

section Cons

variable {h}

/-- The product vector `x ⊗ y` of a vector and an `n`-fold tensor. -/
def cons {n : ℕ} (x : h) (y : TPow h n) : TPow h (n + 1) :=
  (succEquiv h n).symm (CompleteTensorProduct.coe' (x ⊗ₜ[ℂ] y))

lemma inner_cons {n : ℕ} (x x' : h) (y y' : TPow h n) :
    ⟪cons x y, cons x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ := by
  unfold cons
  rw [LinearIsometryEquiv.inner_map_map, CompleteTensorProduct.inner_coe]
  simp [TensorProduct.inner_tmul]

/-- The coherent vector `f ⊗ ⋯ ⊗ f`. -/
def pow (f : h) : (n : ℕ) → TPow h n
  | 0 => ULift.up 1
  | n + 1 => cons f (pow f n)

lemma inner_pow (f g : h) (n : ℕ) : ⟪pow f n, pow g n⟫_ℂ = ⟪f, g⟫_ℂ ^ n := by
  induction n with
  | zero =>
    show ⟪(1 : ℂ), (1 : ℂ)⟫_ℂ = _
    simp
  | succ n ih => rw [pow, pow, inner_cons, ih, pow_succ']

end Cons

/-!

## D. The operator power

-/

section OpPow

variable {h}

/-- The operator `A ⊗ ⋯ ⊗ A` on the `n`-fold tensor power. -/
def opPow (A : h →L[ℂ] h) : (n : ℕ) → TPow h n →L[ℂ] TPow h n
  | 0 => ContinuousLinearMap.id ℂ _
  | n + 1 =>
    (succEquiv h n).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (CompleteTensorProduct.mapL A (opPow A n) ∘L
        (succEquiv h n).toContinuousLinearEquiv.toContinuousLinearMap)

lemma opPow_cons (A : h →L[ℂ] h) {n : ℕ} (x : h) (y : TPow h n) :
    opPow A (n + 1) (cons x y) = cons (A x) (opPow A n y) := by
  unfold cons
  simp only [opPow, ContinuousLinearMap.comp_apply]
  simp [CompleteTensorProduct.mapL_tmul]

lemma opPow_pow (A : h →L[ℂ] h) (f : h) (n : ℕ) : opPow A n (pow f n) = pow (A f) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow, pow, opPow_cons, ih]

/-- The adjoint of `A ⊗ ⋯ ⊗ A` is `A† ⊗ ⋯ ⊗ A†`. -/
lemma inner_opPow [CompleteSpace h] (A : h →L[ℂ] h) (n : ℕ) (u v : TPow h n) :
    ⟪opPow A n u, v⟫_ℂ = ⟪u, opPow (ContinuousLinearMap.adjoint A) n v⟫_ℂ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hadj : opPow (ContinuousLinearMap.adjoint A) n =
        ContinuousLinearMap.adjoint (opPow A n) := by
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      rw [← inner_conj_symm, ← ih y x, inner_conj_symm]
    have key : ∀ (u : TPow h (n + 1)) w, ⟪u, (succEquiv h n).symm w⟫_ℂ = ⟪succEquiv h n u, w⟫_ℂ := by
      intro u w
      rw [← (succEquiv h n).inner_map_map u ((succEquiv h n).symm w)]
      simp
    have key2 : ∀ w (v : TPow h (n + 1)), ⟪(succEquiv h n).symm w, v⟫_ℂ = ⟪w, succEquiv h n v⟫_ℂ := by
      intro w v
      rw [← (succEquiv h n).inner_map_map ((succEquiv h n).symm w) v]
      simp
    simp only [opPow, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [key2, key, CompleteTensorProduct.inner_mapL, hadj]

/-- **The operator power is multiplicative**: `(A B)^{⊗n} = A^{⊗n} B^{⊗n}`. -/
lemma opPow_comp (A B : h →L[ℂ] h) (n : ℕ) :
    opPow (A ∘L B) n = opPow A n ∘L opPow B n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext x
    simp only [opPow, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.apply_symm_apply]
    rw [ih, CompleteTensorProduct.mapL_comp]
    rfl

lemma opPow_id (n : ℕ) : opPow (ContinuousLinearMap.id ℂ h) n = ContinuousLinearMap.id ℂ _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext x
    simp only [opPow, ih, CompleteTensorProduct.mapL_id, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.symm_apply_apply, ContinuousLinearMap.id_apply]

/-- **The operator power commutes with taking adjoints.** -/
lemma adjoint_opPow [CompleteSpace h] (A : h →L[ℂ] h) (n : ℕ) :
    ContinuousLinearMap.adjoint (opPow A n) = opPow (ContinuousLinearMap.adjoint A) n := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [← inner_conj_symm, ← inner_opPow A n y x, inner_conj_symm]

end OpPow

/-!

## E. The symmetric subspace

-/

/-- The symmetric subspace: the closed span of the coherent vectors `f ⊗ ⋯ ⊗ f`. -/
def sym (n : ℕ) : Submodule ℂ (TPow h n) :=
  (Submodule.span ℂ (Set.range fun f : h => pow f n)).topologicalClosure

instance (n : ℕ) : CompleteSpace (sym h n) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The symmetrizer: the orthogonal projection onto the symmetric subspace. -/
def symProj (n : ℕ) : TPow h n →L[ℂ] TPow h n := (sym h n).starProjection

variable {h} in
/-- The projection onto the symmetric subspace fixes symmetric vectors. -/
lemma coe_proj_of_mem {n : ℕ} {x : TPow h n} (hx : x ∈ sym h n) :
    ((sym h n).orthogonalProjectionOnto x : TPow h n) = x :=
  congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := sym h n) ⟨x, hx⟩)

variable {h}

lemma pow_mem_sym (f : h) (n : ℕ) : pow f n ∈ sym h n :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, rfl⟩)

/-- The operator power `A ⊗ ⋯ ⊗ A` preserves the symmetric subspace. -/
lemma opPow_mem_sym (A : h →L[ℂ] h) {n : ℕ} {x : TPow h n} (hx : x ∈ sym h n) :
    opPow A n x ∈ sym h n := by
  have : sym h n ≤ (sym h n).comap (opPow A n : TPow h n →ₗ[ℂ] TPow h n) := by
    refine Submodule.topologicalClosure_minimal _ ?_
      ((Submodule.isClosed_topologicalClosure _).preimage (opPow A n).continuous)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    show opPow A n (pow f n) ∈ sym h n
    rw [opPow_pow]
    exact pow_mem_sym _ _
  exact this hx

/-- A bounded operator that preserves a closed subspace and whose adjoint preserves it commutes
with the orthogonal projection onto it. -/
lemma starProjection_comp_comm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (K : Submodule ℂ E) [K.HasOrthogonalProjection] (T : E →L[ℂ] E)
    (h₁ : ∀ x ∈ K, T x ∈ K) (h₂ : ∀ x ∈ K, ContinuousLinearMap.adjoint T x ∈ K) (x : E) :
    K.starProjection (T x) = T (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h₁ _ (K.starProjection_apply_mem x))
    fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact Submodule.inner_left_of_mem_orthogonal (h₂ w hw) (K.sub_starProjection_mem_orthogonal x)

/-- **The symmetrizer commutes with `A ⊗ ⋯ ⊗ A`.** -/
lemma symProj_comp_opPow [CompleteSpace h] (A : h →L[ℂ] h) (n : ℕ) (x : TPow h n) :
    symProj h n (opPow A n x) = opPow A n (symProj h n x) :=
  starProjection_comp_comm (sym h n) (opPow A n) (fun _ hx => opPow_mem_sym A hx)
    (fun _ hx => by rw [adjoint_opPow]; exact opPow_mem_sym _ hx) x

/-!

## F. Operators on the last factors

-/

section LiftLast

/-- The operator `1 ⊗ ⋯ ⊗ 1 ⊗ K` on `h^{⊗(m+k)}`: `K` acts on the last `m` tensor factors and the
first `k` factors are untouched. -/
def liftLast {m : ℕ} (K : TPow h m →L[ℂ] TPow h m) :
    (k : ℕ) → TPow h (m + k) →L[ℂ] TPow h (m + k)
  | 0 => K
  | k + 1 =>
    (succEquiv h (m + k)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (CompleteTensorProduct.mapL (ContinuousLinearMap.id ℂ h) (liftLast K k) ∘L
        (succEquiv h (m + k)).toContinuousLinearEquiv.toContinuousLinearMap)

lemma liftLast_cons {m : ℕ} (K : TPow h m →L[ℂ] TPow h m) (k : ℕ) (x : h) (y : TPow h (m + k)) :
    liftLast K (k + 1) (cons x y) = cons x (liftLast K k y) := by
  unfold cons
  simp only [liftLast, ContinuousLinearMap.comp_apply]
  simp [CompleteTensorProduct.mapL_tmul]

lemma norm_liftLast_le {m : ℕ} (K : TPow h m →L[ℂ] TPow h m) (k : ℕ) :
    ‖liftLast K k‖ ≤ ‖K‖ := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    simp only [liftLast, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
    calc ‖CompleteTensorProduct.mapL (ContinuousLinearMap.id ℂ h) (liftLast K k)
            (succEquiv h (m + k) x)‖
        ≤ ‖CompleteTensorProduct.mapL (ContinuousLinearMap.id ℂ h) (liftLast K k)‖ *
            ‖succEquiv h (m + k) x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖K‖ * ‖x‖ := by
        rw [LinearIsometryEquiv.norm_map]
        refine mul_le_mul ?_ le_rfl (norm_nonneg _) (norm_nonneg _)
        calc _ ≤ ‖ContinuousLinearMap.id ℂ h‖ * ‖liftLast K k‖ :=
              CompleteTensorProduct.norm_mapL_le _ _
          _ ≤ 1 * ‖K‖ := mul_le_mul ContinuousLinearMap.norm_id_le ih (norm_nonneg _) zero_le_one
          _ = ‖K‖ := one_mul _

lemma inner_liftLast [CompleteSpace h] {m : ℕ} (K : TPow h m →L[ℂ] TPow h m) (k : ℕ)
    (u v : TPow h (m + k)) :
    ⟪liftLast K k u, v⟫_ℂ = ⟪u, liftLast (ContinuousLinearMap.adjoint K) k v⟫_ℂ := by
  induction k with
  | zero => exact (ContinuousLinearMap.adjoint_inner_right K u v).symm
  | succ k ih =>
    have hadj : liftLast (ContinuousLinearMap.adjoint K) k =
        ContinuousLinearMap.adjoint (liftLast K k) := by
      rw [ContinuousLinearMap.eq_adjoint_iff]
      intro x y
      rw [← inner_conj_symm, ← ih y x, inner_conj_symm]
    have key : ∀ (u : TPow h (m + k + 1)) w, ⟪u, (succEquiv h (m + k)).symm w⟫_ℂ =
        ⟪succEquiv h (m + k) u, w⟫_ℂ := by
      intro u w
      rw [← (succEquiv h (m + k)).inner_map_map u ((succEquiv h (m + k)).symm w)]
      simp
    have key2 : ∀ w (v : TPow h (m + k + 1)), ⟪(succEquiv h (m + k)).symm w, v⟫_ℂ =
        ⟪w, succEquiv h (m + k) v⟫_ℂ := by
      intro w v
      rw [← (succEquiv h (m + k)).inner_map_map ((succEquiv h (m + k)).symm w) v]
      simp
    simp only [liftLast, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [key2, key, CompleteTensorProduct.inner_mapL, hadj]
    simp [ContinuousLinearMap.adjoint_id]

lemma adjoint_liftLast [CompleteSpace h] {m : ℕ} (K : TPow h m →L[ℂ] TPow h m) (k : ℕ) :
    ContinuousLinearMap.adjoint (liftLast K k) = liftLast (ContinuousLinearMap.adjoint K) k := by
  rw [eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [← inner_conj_symm, ← inner_liftLast, inner_conj_symm]

/-- **Intertwining the operator power with `K ⊗ 1`.** If `A^{⊗m} K = K' A^{⊗m}` then
`A^{⊗(m+k)}` intertwines `1^{⊗k} ⊗ K` with `1^{⊗k} ⊗ K'`. -/
lemma opPow_liftLast {m : ℕ} (A : h →L[ℂ] h) (K K' : TPow h m →L[ℂ] TPow h m)
    (hK : opPow A m ∘L K = K' ∘L opPow A m) (k : ℕ) :
    opPow A (m + k) ∘L liftLast K k = liftLast K' k ∘L opPow A (m + k) := by
  induction k with
  | zero => exact hK
  | succ k ih =>
    have e1 := CompleteTensorProduct.mapL_comp A (ContinuousLinearMap.id ℂ h) (opPow A (m + k))
      (liftLast K k)
    have e2 := CompleteTensorProduct.mapL_comp (ContinuousLinearMap.id ℂ h) A (liftLast K' k)
      (opPow A (m + k))
    have key : CompleteTensorProduct.mapL A (opPow A (m + k)) ∘L
        CompleteTensorProduct.mapL (ContinuousLinearMap.id ℂ h) (liftLast K k) =
        CompleteTensorProduct.mapL (ContinuousLinearMap.id ℂ h) (liftLast K' k) ∘L
        CompleteTensorProduct.mapL A (opPow A (m + k)) := by
      rw [← e1, ← e2, ih, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    ext x
    show (succEquiv h (m + k)).symm (CompleteTensorProduct.mapL A (opPow A (m + k))
        ((succEquiv h (m + k)) ((succEquiv h (m + k)).symm
          (CompleteTensorProduct.mapL (ContinuousLinearMap.id ℂ h) (liftLast K k)
            ((succEquiv h (m + k)) x))))) =
      (succEquiv h (m + k)).symm (CompleteTensorProduct.mapL (ContinuousLinearMap.id ℂ h)
        (liftLast K' k) ((succEquiv h (m + k)) ((succEquiv h (m + k)).symm
          (CompleteTensorProduct.mapL A (opPow A (m + k)) ((succEquiv h (m + k)) x)))))
    simp only [LinearIsometryEquiv.apply_symm_apply]
    congr 1
    exact congrArg (fun T => T ((succEquiv h (m + k)) x)) key

end LiftLast

/-!

## G. Generators of the observable algebras

-/

section Generators

variable [CompleteSpace h]

/-- The compression of an operator on `h^{⊗n}` to the symmetric subspace. -/
def symL {n : ℕ} (T : TPow h n →L[ℂ] TPow h n) : sym h n →L[ℂ] sym h n :=
  (sym h n).orthogonalProjectionOnto ∘L T ∘L (sym h n).subtypeL

lemma adjoint_symL {n : ℕ} (T : TPow h n →L[ℂ] TPow h n) :
    ContinuousLinearMap.adjoint (symL T) = symL (ContinuousLinearMap.adjoint T) := by
  simp only [symL, ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto, ContinuousLinearMap.comp_assoc]

lemma norm_symL_le {n : ℕ} (T : TPow h n →L[ℂ] TPow h n) : ‖symL T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  have h1 : ‖(sym h n).orthogonalProjectionOnto (T (x : TPow h n))‖ ≤ ‖T (x : TPow h n)‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (Submodule.orthogonalProjectionOnto_norm_le _))
  have h2 : ‖T (x : TPow h n)‖ ≤ ‖T‖ * ‖x‖ :=
    (T.le_opNorm _).trans (by rw [Submodule.coe_norm])
  exact h1.trans h2

/-- An operator on the symmetric subspace, extended by zero to the tensor power. -/
def embed {m : ℕ} (K : sym h m →L[ℂ] sym h m) : TPow h m →L[ℂ] TPow h m :=
  (sym h m).subtypeL ∘L K ∘L (sym h m).orthogonalProjectionOnto

lemma adjoint_embed {m : ℕ} (K : sym h m →L[ℂ] sym h m) :
    ContinuousLinearMap.adjoint (embed K) = embed (ContinuousLinearMap.adjoint K) := by
  simp only [embed, ContinuousLinearMap.adjoint_comp, Submodule.adjoint_subtypeL,
    Submodule.adjoint_orthogonalProjectionOnto, ContinuousLinearMap.comp_assoc]

lemma norm_embed_le {m : ℕ} (K : sym h m →L[ℂ] sym h m) : ‖embed K‖ ≤ ‖K‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg K) fun x => ?_
  have h1 : ‖K ((sym h m).orthogonalProjectionOnto x)‖ ≤ ‖K‖ * ‖x‖ :=
    (K.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _) (Submodule.orthogonalProjectionOnto_norm_le _)))
      (ContinuousLinearMap.opNorm_nonneg K))
  simpa [embed] using h1

/-- The operator `P_{m+k} (K ⊗ 1^{⊗k}) P_{m+k}` on the symmetric subspace, for an operator `K` on
the symmetric subspace of `m` particles. -/
def gen {m : ℕ} (K : sym h m →L[ℂ] sym h m) (k : ℕ) : sym h (m + k) →L[ℂ] sym h (m + k) :=
  symL (liftLast (embed K) k)

/-- **The generators are bounded by the norm of `K`.** -/
lemma norm_gen_le {m : ℕ} (K : sym h m →L[ℂ] sym h m) (k : ℕ) : ‖gen K k‖ ≤ ‖K‖ :=
  (norm_symL_le _).trans ((norm_liftLast_le _ k).trans (norm_embed_le K))

/-- **The adjoint of a generator** is the generator of the adjoint. -/
lemma adjoint_gen {m : ℕ} (K : sym h m →L[ℂ] sym h m) (k : ℕ) :
    ContinuousLinearMap.adjoint (gen K k) = gen (ContinuousLinearMap.adjoint K) k := by
  rw [gen, gen, adjoint_symL, adjoint_liftLast, adjoint_embed]

/-- The restriction of `A ⊗ ⋯ ⊗ A` to the symmetric subspace. -/
def symAct (A : h →L[ℂ] h) (n : ℕ) : sym h n →L[ℂ] sym h n := symL (opPow A n)

lemma coe_symAct (A : h →L[ℂ] h) (n : ℕ) (x : sym h n) :
    (symAct A n x : TPow h n) = opPow A n x :=
  coe_proj_of_mem (opPow_mem_sym A x.2)

lemma coe_orthogonalProjectionOnto {n : ℕ} (y : TPow h n) :
    ((sym h n).orthogonalProjectionOnto y : TPow h n) = symProj h n y :=
  Submodule.starProjection_apply _ _ |>.symm

/-- The compression commutes with the symmetrizer-compatible operator power. -/
lemma orthogonalProjectionOnto_opPow (A : h →L[ℂ] h) {n : ℕ} (y : TPow h n) :
    (sym h n).orthogonalProjectionOnto (opPow A n y) =
      symAct A n ((sym h n).orthogonalProjectionOnto y) := by
  apply Subtype.ext
  rw [coe_orthogonalProjectionOnto, coe_symAct, coe_orthogonalProjectionOnto,
    symProj_comp_opPow]

lemma opPow_embed {m : ℕ} (A : h →L[ℂ] h) (K K' : sym h m →L[ℂ] sym h m)
    (hK : symAct A m ∘L K = K' ∘L symAct A m) :
    opPow A m ∘L embed K = embed K' ∘L opPow A m := by
  ext y
  have := congrArg (fun T => (T ((sym h m).orthogonalProjectionOnto y) : TPow h m)) hK
  simp only [embed, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at this ⊢
  rw [orthogonalProjectionOnto_opPow, ← this, coe_symAct]

lemma symAct_comp (A B : h →L[ℂ] h) (n : ℕ) :
    symAct (A ∘L B) n = symAct A n ∘L symAct B n := by
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  rw [coe_symAct, coe_symAct, coe_symAct, opPow_comp]
  rfl

lemma symAct_id (n : ℕ) : symAct (ContinuousLinearMap.id ℂ h) n = ContinuousLinearMap.id ℂ _ := by
  ext x
  rw [coe_symAct, opPow_id]
  rfl

lemma adjoint_symAct (A : h →L[ℂ] h) (n : ℕ) :
    ContinuousLinearMap.adjoint (symAct A n) = symAct (ContinuousLinearMap.adjoint A) n := by
  rw [symAct, symAct, adjoint_symL, adjoint_opPow]

lemma coe_gen {m : ℕ} (K : sym h m →L[ℂ] sym h m) (k : ℕ) (x : sym h (m + k)) :
    (gen K k x : TPow h (m + k)) = symProj h (m + k) (liftLast (embed K) k x) := by
  simp only [gen, symL, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  exact coe_orthogonalProjectionOnto _

/-- **Covariance of the generators.** If `A^{⊗m}` intertwines `K` with `K'` on the symmetric
subspace then `A^{⊗(m+k)}` intertwines the generators `gen K k` and `gen K' k`. -/
lemma symAct_gen {m : ℕ} (A : h →L[ℂ] h) (K K' : sym h m →L[ℂ] sym h m)
    (hK : symAct A m ∘L K = K' ∘L symAct A m) (k : ℕ) :
    symAct A (m + k) ∘L gen K k = gen K' k ∘L symAct A (m + k) := by
  ext x
  have hL := opPow_liftLast A (embed K) (embed K') (opPow_embed A K K' hK) k
  have hx := congrArg (fun T => T (x : TPow h (m + k))) hL
  simp only [ContinuousLinearMap.comp_apply] at hx
  simp only [ContinuousLinearMap.comp_apply]
  rw [coe_symAct, coe_gen, coe_gen, coe_symAct, ← symProj_comp_opPow, hx]

end Generators

/-!

## H. Creation and annihilation operators

-/

section Ladder

variable [CompleteSpace h]

/-- Prepending a fixed vector `φ` to an `n`-fold tensor. -/
def consL (φ : h) (n : ℕ) : TPow h n →L[ℂ] TPow h (n + 1) :=
  (succEquiv h n).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (CompleteTensorProduct.tInclL ∘L TensorProduct.mkL ℂ h (TPow h n) φ)

lemma consL_apply (φ : h) {n : ℕ} (y : TPow h n) : consL φ n y = cons φ y := rfl

/-- The contraction of the first tensor factor with a fixed vector `φ`. -/
def contr (φ : h) (n : ℕ) : TPow h (n + 1) →L[ℂ] TPow h n :=
  ContinuousLinearMap.adjoint (consL φ n)

lemma inner_contr (φ : h) {n : ℕ} (x : TPow h (n + 1)) (y : TPow h n) :
    ⟪contr φ n x, y⟫_ℂ = ⟪x, cons φ y⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_left (consL φ n) y x

/-- **The contraction acts on coherent vectors by the overlap**:
`⟨φ| (u ⊗ ⋯ ⊗ u) = ⟪φ, u⟫ u ⊗ ⋯ ⊗ u`. -/
lemma contr_pow (φ u : h) (n : ℕ) : contr φ n (pow u (n + 1)) = ⟪φ, u⟫_ℂ • pow u n := by
  refine ext_inner_right ℂ fun y => ?_
  rw [inner_contr, pow, inner_cons, inner_smul_left, ← inner_conj_symm φ u, Complex.conj_conj]

/-- The contraction maps the symmetric subspace into the symmetric subspace. -/
lemma contr_mem_sym (φ : h) {n : ℕ} {x : TPow h (n + 1)} (hx : x ∈ sym h (n + 1)) :
    contr φ n x ∈ sym h n := by
  have : sym h (n + 1) ≤ (sym h n).comap (contr φ n : TPow h (n + 1) →ₗ[ℂ] TPow h n) := by
    refine Submodule.topologicalClosure_minimal _ ?_
      ((Submodule.isClosed_topologicalClosure _).preimage (contr φ n).continuous)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    show contr φ n (pow f (n + 1)) ∈ sym h n
    rw [contr_pow]
    exact Submodule.smul_mem _ _ (pow_mem_sym _ _)
  exact this hx

/-- The annihilation operator of the vector `φ`, normalised by `√(n+1)`. -/
def ann (φ : h) (n : ℕ) : sym h (n + 1) →L[ℂ] sym h n :=
  (Real.sqrt (n + 1) : ℂ) • ((sym h n).orthogonalProjectionOnto ∘L contr φ n ∘L
    (sym h (n + 1)).subtypeL)

/-- The creation operator of the vector `φ`: the adjoint of the annihilation operator. -/
def cre (φ : h) (n : ℕ) : sym h n →L[ℂ] sym h (n + 1) :=
  ContinuousLinearMap.adjoint (ann φ n)


/-- `cons` as a bounded bilinear map. -/
def consBL (n : ℕ) : h →L[ℂ] TPow h n →L[ℂ] TPow h (n + 1) :=
  (ContinuousLinearMap.compL ℂ (TPow h n) (h ⊗[ℂ] TPow h n) (TPow h (n + 1))
    ((succEquiv h n).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      CompleteTensorProduct.tInclL)) ∘L (TensorProduct.mkL ℂ h (TPow h n))

lemma consBL_apply (n : ℕ) (x : h) (y : TPow h n) : consBL n x y = cons x y := rfl

/-- The derivative of `s ↦ (w + sφ)^{⊗n}` at `0`. -/
def D (w φ : h) : (n : ℕ) → TPow h n
  | 0 => 0
  | n + 1 => cons φ (pow w n) + cons w (D w φ n)

lemma hasDerivAt_pow (w φ : h) (n : ℕ) :
    HasDerivAt (fun s : ℝ => pow (w + s • φ) n) (D w φ n) 0 := by
  induction n with
  | zero => exact hasDerivAt_const _ _
  | succ n ih =>
    have hc : HasDerivAt (fun s : ℝ => (consBL n (w + s • φ)).restrictScalars ℝ)
        ((consBL n φ).restrictScalars ℝ) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => (consBL n w).restrictScalars ℝ +
          s • (consBL n φ).restrictScalars ℝ) ((consBL n φ).restrictScalars ℝ) 0 := by
        simpa using HasDerivAt.const_add ((consBL n w).restrictScalars ℝ)
          (HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) ((consBL n φ).restrictScalars ℝ))
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
      ext y
      simp [map_add, ContinuousLinearMap.map_smul_of_tower]
    have := HasDerivAt.clm_apply hc ih
    have key : ∀ (s : ℝ), pow (w + s • φ) (n + 1) =
        (consBL n (w + s • φ)).restrictScalars ℝ (pow (w + s • φ) n) := fun s => rfl
    simp only [key]
    simpa [pow, D, consBL_apply] using this

lemma D_mem_sym (w φ : h) (n : ℕ) : D w φ n ∈ sym h n := by
  have h1 := HasDerivAt.tendsto_slope_zero (hasDerivAt_pow w φ n)
  have hc : IsClosed (sym h n : Set (TPow h n)) := Submodule.isClosed_topologicalClosure _
  refine hc.mem_of_tendsto h1 ?_
  filter_upwards [self_mem_nhdsWithin] with t _
  simp only [zero_add, zero_smul, add_zero]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · exact pow_mem_sym _ _
  · exact pow_mem_sym _ _

lemma cons_zero (x : h) (n : ℕ) : cons x (0 : TPow h n) = 0 := (consL x n).map_zero

lemma inner_pow_D (v w φ : h) (n : ℕ) :
    ⟪pow v (n + 1), D w φ (n + 1)⟫_ℂ = (n + 1 : ℂ) * (⟪v, φ⟫_ℂ * ⟪v, w⟫_ℂ ^ n) := by
  induction n with
  | zero =>
    have e : pow v 1 = cons v (pow v 0) := rfl
    rw [D, inner_add_right, e, D, cons_zero, inner_zero_right, add_zero, inner_cons]
    have : ⟪pow v 0, pow w 0⟫_ℂ = 1 := by simpa using inner_pow v w 0
    rw [this]
    simp
  | succ n ih =>
    have e : pow v (n + 1 + 1) = cons v (pow v (n + 1)) := rfl
    rw [D, inner_add_right, e, inner_cons, inner_cons, inner_pow, ih]
    push_cast
    ring

/-- **Coherent vectors separate the symmetric subspace**: a symmetric vector orthogonal to all
coherent vectors vanishes. -/
lemma eq_zero_of_inner_pow {n : ℕ} {x : TPow h n} (hx : x ∈ sym h n)
    (h0 : ∀ f : h, ⟪pow f n, x⟫_ℂ = 0) : x = 0 := by
  have hle : sym h n ≤ LinearMap.ker ((innerSL ℂ x : TPow h n →L[ℂ] ℂ) : TPow h n →ₗ[ℂ] ℂ) := by
    refine Submodule.topologicalClosure_minimal _ ?_ (ContinuousLinearMap.isClosed_ker _)
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    show ⟪x, pow f n⟫_ℂ = 0
    rw [← inner_conj_symm, h0 f, map_zero]
  have : ⟪x, x⟫_ℂ = 0 := hle hx
  exact inner_self_eq_zero.mp this

/-- Two symmetric vectors with the same overlaps with all coherent vectors are equal. -/
lemma eq_of_inner_pow {n : ℕ} {x y : TPow h n} (hx : x ∈ sym h n) (hy : y ∈ sym h n)
    (h0 : ∀ f : h, ⟪pow f n, x⟫_ℂ = ⟪pow f n, y⟫_ℂ) : x = y := by
  have := eq_zero_of_inner_pow (Submodule.sub_mem _ hx hy) fun f => by
    rw [inner_sub_right, h0 f, sub_self]
  exact sub_eq_zero.mp this

/-- The annihilation operator on a coherent vector. -/
lemma ann_pow (φ u : h) (n : ℕ) :
    ann φ n ⟨pow u (n + 1), pow_mem_sym u _⟩ =
      ((Real.sqrt (n + 1) : ℂ) * ⟪φ, u⟫_ℂ) • (⟨pow u n, pow_mem_sym u _⟩ : sym h n) := by
  apply Subtype.ext
  have h1 : ((sym h n).orthogonalProjectionOnto (⟪φ, u⟫_ℂ • pow u n) : TPow h n) =
      ⟪φ, u⟫_ℂ • pow u n := coe_proj_of_mem (Submodule.smul_mem _ _ (pow_mem_sym u _))
  simp only [ann, smul_apply, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Submodule.coe_smul, contr_pow, h1, smul_smul]

/-- **The creation operator on a coherent vector**:
`a†(φ) u^{⊗n} = (n+1)^{-1/2} d/ds (u + sφ)^{⊗(n+1)}`. -/
lemma cre_pow (φ u : h) (n : ℕ) :
    cre φ n ⟨pow u n, pow_mem_sym u _⟩ =
      (1 / (Real.sqrt (n + 1) : ℂ)) • (⟨D u φ (n + 1), D_mem_sym u φ _⟩ : sym h (n + 1)) := by
  apply Subtype.ext
  refine eq_of_inner_pow (cre φ n ⟨pow u n, pow_mem_sym u _⟩).2
    (Submodule.smul_mem _ _ (D_mem_sym u φ _)) fun v => ?_
  have e1 : ⟪pow v (n + 1), (cre φ n ⟨pow u n, pow_mem_sym u _⟩ : TPow h (n + 1))⟫_ℂ =
      ⟪(⟨pow v (n + 1), pow_mem_sym v _⟩ : sym h (n + 1)), cre φ n ⟨pow u n, pow_mem_sym u _⟩⟫_ℂ :=
    rfl
  rw [e1, cre, ContinuousLinearMap.adjoint_inner_right, ann_pow, Submodule.coe_smul,
    inner_smul_right]
  have e2 : ⟪(⟨pow v n, pow_mem_sym v _⟩ : sym h n), (⟨pow u n, pow_mem_sym u _⟩ : sym h n)⟫_ℂ =
      ⟪v, u⟫_ℂ ^ n := inner_pow v u n
  rw [inner_smul_left, e2, inner_pow_D]
  have hs : ((Real.sqrt (n + 1) : ℝ) : ℂ) * ((Real.sqrt (n + 1) : ℝ) : ℂ) = n + 1 := by
    exact_mod_cast Real.mul_self_sqrt (by positivity)
  have hne : ((Real.sqrt (n + 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity)).ne'
  simp only [map_mul, Complex.conj_ofReal, inner_conj_symm]
  field_simp
  rw [← hs]
  ring

lemma inner_D_pow (v w φ : h) (n : ℕ) :
    ⟪D v φ (n + 1), pow w (n + 1)⟫_ℂ = (n + 1 : ℂ) * (⟪φ, w⟫_ℂ * ⟪v, w⟫_ℂ ^ n) := by
  rw [← inner_conj_symm, inner_pow_D, map_mul, map_mul, map_pow, inner_conj_symm,
    inner_conj_symm]
  simp

/-- **The Gram matrix of the derivative vectors.** -/
lemma inner_D_D (v w φ φ' : h) (n : ℕ) :
    ⟪D v φ' (n + 1), D w φ (n + 1)⟫_ℂ =
      (n + 1 : ℂ) * (⟪φ', φ⟫_ℂ * ⟪v, w⟫_ℂ ^ n) +
        (n + 1 : ℂ) * (n * (⟪φ', w⟫_ℂ * ⟪v, φ⟫_ℂ * ⟪v, w⟫_ℂ ^ (n - 1))) := by
  induction n with
  | zero =>
    have e : D v φ' 1 = cons φ' (pow v 0) := by rw [D, D, cons_zero, add_zero]
    have e' : D w φ 1 = cons φ (pow w 0) := by rw [D, D, cons_zero, add_zero]
    have : ⟪pow v 0, pow w 0⟫_ℂ = 1 := by simpa using inner_pow v w 0
    rw [e, e', inner_cons, this]
    simp
  | succ n ih =>
    have e1 : D v φ' (n + 1 + 1) = cons φ' (pow v (n + 1)) + cons v (D v φ' (n + 1)) := rfl
    have e2 : D w φ (n + 1 + 1) = cons φ (pow w (n + 1)) + cons w (D w φ (n + 1)) := rfl
    rw [e1, e2]
    simp only [inner_add_left, inner_add_right, inner_cons, inner_pow, ih, inner_pow_D,
      inner_D_pow]
    rcases n with _ | n
    · simp
      ring
    · simp only [Nat.add_sub_cancel]
      push_cast
      ring

/-- **Overlap principle**: two tensors with the same overlaps with all coherent vectors have the
same symmetrization. -/
lemma symProj_eq_of_inner_pow {n : ℕ} {x x' : TPow h n}
    (h0 : ∀ z : h, ⟪pow z n, x⟫_ℂ = ⟪pow z n, x'⟫_ℂ) : symProj h n x = symProj h n x' := by
  have key : ∀ (y : TPow h n) (z : h), ⟪pow z n, symProj h n y⟫_ℂ = ⟪pow z n, y⟫_ℂ := by
    intro y z
    have e : symProj h n (pow z n) = pow z n := by
      have := coe_proj_of_mem (pow_mem_sym z n)
      rwa [coe_orthogonalProjectionOnto] at this
    have e' : ⟪(sym h n).starProjection (pow z n), y⟫_ℂ = ⟪pow z n, (sym h n).starProjection y⟫_ℂ :=
      Submodule.inner_starProjection_left_eq_right (sym h n) _ _
    show ⟪pow z n, (sym h n).starProjection y⟫_ℂ = ⟪pow z n, y⟫_ℂ
    rw [← e']
    exact congrArg (fun v => ⟪v, y⟫_ℂ) e
  refine eq_of_inner_pow (Submodule.starProjection_apply_mem (sym h n) x)
    (Submodule.starProjection_apply_mem (sym h n) x') fun z => ?_
  rw [key, key, h0]

/-- The symmetrizer kills tensors orthogonal to all coherent vectors. -/
lemma symProj_eq_zero_of_inner_pow {n : ℕ} {x : TPow h n}
    (h0 : ∀ z : h, ⟪pow z n, x⟫_ℂ = 0) : symProj h n x = 0 := by
  have := symProj_eq_of_inner_pow (x := x) (x' := 0) (by simpa using h0)
  simpa using this

lemma inner_pow_symProj {n : ℕ} (z : h) (y : TPow h n) :
    ⟪pow z n, symProj h n y⟫_ℂ = ⟪pow z n, y⟫_ℂ := by
  have e : symProj h n (pow z n) = pow z n := by
    have := coe_proj_of_mem (pow_mem_sym z n)
    rwa [coe_orthogonalProjectionOnto] at this
  have e' : ⟪(sym h n).starProjection (pow z n), y⟫_ℂ = ⟪pow z n, (sym h n).starProjection y⟫_ℂ :=
    Submodule.inner_starProjection_left_eq_right (sym h n) _ _
  show ⟪pow z n, (sym h n).starProjection y⟫_ℂ = ⟪pow z n, y⟫_ℂ
  rw [← e']
  exact congrArg (fun v => ⟪v, y⟫_ℂ) e

/-- **Symmetrizing after prepending** only sees the symmetric part of the tensor. -/
lemma symProj_cons {n : ℕ} (φ : h) (y : TPow h n) :
    symProj h (n + 1) (cons φ y) = symProj h (n + 1) (cons φ (symProj h n y)) :=
  symProj_eq_of_inner_pow fun z => by
    rw [pow, inner_cons, inner_cons, inner_pow_symProj]

/-- **The creation operator is the symmetrized prepending**: `a†(φ) ψ = √(n+1) P (φ ⊗ ψ)`. -/
lemma cre_eq (φ : h) {n : ℕ} (ψ : sym h n) :
    (cre φ n ψ : TPow h (n + 1)) = (Real.sqrt (n + 1) : ℂ) • symProj h (n + 1) (cons φ ψ) := by
  refine eq_of_inner_pow (cre φ n ψ).2 (Submodule.smul_mem _ _
    (Submodule.starProjection_apply_mem (sym h (n + 1)) _)) fun z => ?_
  have e1 : ⟪pow z (n + 1), (cre φ n ψ : TPow h (n + 1))⟫_ℂ =
      ⟪(⟨pow z (n + 1), pow_mem_sym z _⟩ : sym h (n + 1)), cre φ n ψ⟫_ℂ := rfl
  rw [e1, cre, ContinuousLinearMap.adjoint_inner_right, ann_pow, inner_smul_left, inner_smul_right,
    inner_pow_symProj, pow, inner_cons]
  simp only [map_mul, Complex.conj_ofReal, inner_conj_symm]
  have e2 : ⟪(⟨pow z n, pow_mem_sym z _⟩ : sym h n), ψ⟫_ℂ = ⟪pow z n, (ψ : TPow h n)⟫_ℂ := rfl
  rw [e2]
  ring

/-!

## I. Decomposition of `1 ⊗ K` on a derivative vector

-/

section Decomposition

/-- Prepending `k` copies of `u`. -/
def consIter (u : h) {m : ℕ} (y : TPow h m) : (k : ℕ) → TPow h (m + k)
  | 0 => y
  | k + 1 => cons u (consIter u y k)

lemma inner_pow_consIter (z u : h) {m : ℕ} (y : TPow h m) (k : ℕ) :
    ⟪pow z (m + k), consIter u y k⟫_ℂ = ⟪z, u⟫_ℂ ^ k * ⟪pow z m, y⟫_ℂ := by
  induction k with
  | zero => simp [consIter]
  | succ k ih =>
    have e : pow z (m + (k + 1)) = cons z (pow z (m + k)) := rfl
    rw [consIter, e, inner_cons, ih, pow_succ]
    ring

/-- `K̃ ⊗ 1` on a coherent vector: the operator acts on the last `m` factors only. -/
lemma liftLast_pow {m : ℕ} (K : TPow h m →L[ℂ] TPow h m) (u : h) (k : ℕ) :
    liftLast K k (pow u (m + k)) = consIter u (K (pow u m)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : pow u (m + (k + 1)) = cons u (pow u (m + k)) := rfl
    rw [e, liftLast_cons, ih]
    rfl

/-- The part of the derivative vector in which the perturbation `φ` sits among the `k` free
factors. -/
def Ssum (u φ : h) {m : ℕ} (K : TPow h m →L[ℂ] TPow h m) : (k : ℕ) → TPow h (m + k)
  | 0 => 0
  | k + 1 => cons φ (consIter u (K (pow u m)) k) + cons u (Ssum u φ K k)

/-- **Decomposition of `1^{⊗k} ⊗ K` on the derivative vector.** The perturbation either sits
among the free factors or hits the factors on which `K` acts. -/
lemma liftLast_D {m : ℕ} (K : TPow h m →L[ℂ] TPow h m) (u φ : h) (k : ℕ) :
    liftLast K k (D u φ (m + k)) =
      Ssum u φ K k + consIter u (K (D u φ m)) k := by
  induction k with
  | zero => simp [liftLast, Ssum, consIter]
  | succ k ih =>
    have e : D u φ (m + (k + 1)) = cons φ (pow u (m + k)) + cons u (D u φ (m + k)) := rfl
    rw [e, map_add, liftLast_cons, liftLast_cons, ih, liftLast_pow, Ssum, consIter]
    have : ∀ (x : h) {n : ℕ} (a b : TPow h n), cons x (a + b) = cons x a + cons x b :=
      fun x _ a b => (consL x _).map_add a b
    rw [this]
    abel

lemma inner_pow_Ssum {m : ℕ} (K : TPow h m →L[ℂ] TPow h m) (u φ z : h) (k : ℕ) :
    ⟪pow z (m + (k + 1)), Ssum u φ K (k + 1)⟫_ℂ =
      (k + 1 : ℂ) * (⟪z, φ⟫_ℂ * (⟪z, u⟫_ℂ ^ k * ⟪pow z m, K (pow u m)⟫_ℂ)) := by
  induction k with
  | zero =>
    have e : pow z (m + (0 + 1)) = cons z (pow z (m + 0)) := rfl
    rw [Ssum, e, inner_add_right, inner_cons, inner_cons, inner_pow_consIter]
    simp [Ssum]
  | succ k ih =>
    have e : pow z (m + (k + 1 + 1)) = cons z (pow z (m + (k + 1))) := rfl
    rw [Ssum, e, inner_add_right, inner_cons, inner_cons, inner_pow_consIter, ih]
    push_cast
    ring

/-- **The symmetrization of the sum collapses**: every term has the same overlaps with the
coherent vectors, so the sum symmetrizes to `k + 1` times one term. -/
lemma symProj_Ssum {m : ℕ} (K : TPow h m →L[ℂ] TPow h m) (u φ : h) (k : ℕ) :
    symProj h (m + (k + 1)) (Ssum u φ K (k + 1)) =
      (k + 1 : ℂ) • symProj h (m + (k + 1)) (cons φ (consIter u (K (pow u m)) k)) := by
  rw [← map_smul]
  refine symProj_eq_of_inner_pow fun z => ?_
  have e : pow z (m + (k + 1)) = cons z (pow z (m + k)) := rfl
  rw [inner_pow_Ssum, inner_smul_right, e, inner_cons, inner_pow_consIter]

/-- **Exact intertwining of a generator with the creation operator on coherent vectors.**
Up to the remainder `E`, which contains `K` applied to the derivative vector, the generator
`gen K (k+1)` on the `m+k+1` particles intertwines `a†(φ)` with `((k+1)/(m+k+1))` times the
generator `gen K k` on `m+k` particles. -/
lemma gen_cre_pow {m : ℕ} (K : sym h m →L[ℂ] sym h m) (u φ : h) (k : ℕ) :
    (gen K (k + 1) (cre φ (m + k) ⟨pow u (m + k), pow_mem_sym u _⟩) : TPow h (m + (k + 1))) -
      (((k + 1 : ℂ) / (m + k + 1 : ℂ)) •
        (cre φ (m + k) (gen K k ⟨pow u (m + k), pow_mem_sym u _⟩) : TPow h (m + (k + 1)))) =
    (1 / (Real.sqrt ((m + k : ℕ) + 1) : ℂ)) •
      symProj h (m + (k + 1)) (consIter u (embed K (D u φ m)) (k + 1)) := by
  set N : ℝ := ((m + k : ℕ) : ℝ) + 1 with hN
  have hNpos : 0 < N := by positivity
  have hs : ((Real.sqrt N : ℝ) : ℂ) * (Real.sqrt N : ℝ) = N := by
    exact_mod_cast Real.mul_self_sqrt hNpos.le
  have hne : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hNpos).ne'
  have h1 : (cre φ (m + k) ⟨pow u (m + k), pow_mem_sym u _⟩ : TPow h (m + (k + 1))) =
      (1 / (Real.sqrt N : ℂ)) • D u φ (m + (k + 1)) :=
    congrArg Subtype.val (cre_pow φ u (m + k))
  have h2 : (gen K k ⟨pow u (m + k), pow_mem_sym u _⟩ : TPow h (m + k)) =
      symProj h (m + k) (consIter u (embed K (pow u m)) k) := by
    rw [coe_gen]
    exact congrArg _ (liftLast_pow (embed K) u k)
  have h3 : (cre φ (m + k) (gen K k ⟨pow u (m + k), pow_mem_sym u _⟩) : TPow h (m + (k + 1))) =
      (Real.sqrt N : ℂ) • symProj h (m + (k + 1))
        (cons φ (consIter u (embed K (pow u m)) k)) := by
    rw [cre_eq, h2, ← symProj_cons]
    rfl
  rw [coe_gen, h1, h3, map_smul, liftLast_D]
  simp only [smul_add, map_add, map_smul]
  rw [symProj_Ssum]
  have hk : (k + 1 : ℂ) / (m + k + 1 : ℂ) = (k + 1 : ℂ) / (N : ℂ) := by
    simp only [hN]; push_cast; ring
  rw [hk, smul_smul, smul_smul]
  have : (1 / (Real.sqrt N : ℂ)) * (k + 1 : ℂ) = (k + 1 : ℂ) / (N : ℂ) * (Real.sqrt N : ℂ) := by
    rw [← hs]; field_simp
  rw [this]
  abel

lemma norm_cons {n : ℕ} (x : h) (y : TPow h n) : ‖cons x y‖ = ‖x‖ * ‖y‖ := by
  have h1 := inner_cons x x y y
  have e1 : ⟪x, x⟫_ℂ = (‖x‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K x
  have e2 : ⟪y, y⟫_ℂ = (‖y‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K y
  have e3 : ⟪cons x y, cons x y⟫_ℂ = (‖cons x y‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
  have h2 : ((‖cons x y‖ : ℝ) : ℂ) ^ 2 = ((‖x‖ * ‖y‖ : ℝ) : ℂ) ^ 2 := by
    rw [← e3, h1, e1, e2]
    push_cast
    ring
  have h3 : ‖cons x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h2
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h3

lemma norm_pow (u : h) (n : ℕ) : ‖pow u n‖ = ‖u‖ ^ n := by
  induction n with
  | zero => show ‖(ULift.up (1 : ℂ) : ULift.{u} ℂ)‖ = _; simp
  | succ n ih => rw [pow, norm_cons, ih, pow_succ]; ring

lemma norm_consIter (u : h) {m : ℕ} (y : TPow h m) (k : ℕ) :
    ‖consIter u y k‖ = ‖u‖ ^ k * ‖y‖ := by
  induction k with
  | zero => simp [consIter]
  | succ k ih => rw [consIter, norm_cons, ih, pow_succ]; ring

lemma cons_add_left {n : ℕ} (x x' : h) (y : TPow h n) : cons (x + x') y = cons x y + cons x' y :=
  congrArg (fun T => T y) ((consBL n).map_add x x')

lemma cons_smul_left {n : ℕ} (c : ℂ) (x : h) (y : TPow h n) : cons (c • x) y = c • cons x y :=
  congrArg (fun T => T y) ((consBL n).map_smul c x)

lemma cons_add_right {n : ℕ} (x : h) (a b : TPow h n) : cons x (a + b) = cons x a + cons x b :=
  (consL x n).map_add a b

lemma cons_smul_right {n : ℕ} (x : h) (c : ℂ) (a : TPow h n) : cons x (c • a) = c • cons x a :=
  (consL x n).map_smul c a

lemma D_add (u φ φ' : h) (n : ℕ) : D u (φ + φ') n = D u φ n + D u φ' n := by
  induction n with
  | zero => simp [D]
  | succ n ih =>
    simp only [D, ih, cons_add_left, cons_add_right]
    abel

lemma D_smul (u : h) (c : ℂ) (φ : h) (n : ℕ) : D u (c • φ) n = c • D u φ n := by
  induction n with
  | zero => simp [D]
  | succ n ih =>
    simp only [D, ih, cons_smul_left, cons_smul_right, smul_add]

lemma norm_D_le (u φ : h) (n : ℕ) : ‖D u φ (n + 1)‖ ≤ (n + 1) * (‖u‖ ^ n * ‖φ‖) := by
  induction n with
  | zero => simp [D, cons_zero, norm_cons, norm_pow]
  | succ n ih =>
    calc ‖D u φ (n + 1 + 1)‖ = ‖cons φ (pow u (n + 1)) + cons u (D u φ (n + 1))‖ := rfl
      _ ≤ ‖cons φ (pow u (n + 1))‖ + ‖cons u (D u φ (n + 1))‖ := norm_add_le _ _
      _ = ‖φ‖ * ‖u‖ ^ (n + 1) + ‖u‖ * ‖D u φ (n + 1)‖ := by
        rw [norm_cons, norm_cons, norm_pow]
      _ ≤ ‖φ‖ * ‖u‖ ^ (n + 1) + ‖u‖ * ((n + 1) * (‖u‖ ^ n * ‖φ‖)) := by gcongr
      _ = ((n + 1 : ℕ) + 1) * (‖u‖ ^ (n + 1) * ‖φ‖) := by push_cast; ring

end Decomposition

end Ladder

end HilbertPower
