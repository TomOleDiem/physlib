/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.TraceClass

/-!
# Hilbert--Schmidt square sums

The square-sum of the matrix of a bounded operator is the reusable analytic
step between the positive trace-class theory and the general trace ideal.  We
state it directly for Hilbert bases indexed by sets, matching the surrounding
operator-algebra API.  The proof is Parseval plus Tonelli; it does not use a
spectral theorem or a trace-class basis-independence assumption.
-/

@[expose] public section

noncomputable section

open scoped ComplexOrder InnerProductSpace
open OperatorAlgebra

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace HilbertSchmidt

/-- A bounded operator is Hilbert--Schmidt when its squared norm sum is
summable in one Hilbert basis.  The basis-independence theorem below shows
that this existential definition is equivalent to using any basis. -/
def IsHilbertSchmidt (S : B(H)) : Prop :=
  ∃ (w : Set H) (b : HilbertBasis w ℂ H),
    Summable (fun i : w => ‖S (b i)‖ ^ 2)

@[nolint unusedArguments]
private lemma hasSum_norm_sq_inner_basis {w : Set H} (b : HilbertBasis w ℂ H) (y : H) :
    HasSum (fun i : w => ‖⟪b i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner y y
  have hpt : ∀ i : w, ⟪y, b i⟫_ℂ * ⟪b i, y⟫_ℂ =
      ((‖⟪b i, y⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← inner_conj_symm y (b i), RCLike.conj_mul]
    norm_cast
  have hval : ⟪y, y⟫_ℂ = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [hpt] at h
  rw [hval] at h
  exact Complex.hasSum_ofReal.mp h

theorem hasSum_norm_sq_inner {w : Set H} (b : HilbertBasis w ℂ H) (y : H) :
    HasSum (fun i : w => ‖⟪b i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) :=
  hasSum_norm_sq_inner_basis b y

/-- The Hilbert--Schmidt square sum of `S` in one basis equals the square sum
of `S⋆` in a second basis.  This is the nonnegative double-sum identity; the
usual basis-independence statement follows by applying it twice. -/
lemma hasSum_norm_sq_apply_eq_adjoint {S : B(H)}
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : w' => ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2)
      (∑' i : w, ‖S (b i)‖ ^ 2) := by
  classical
  set F : w → w' → ℝ := fun i j => ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 with hFdef
  have hFnonneg : 0 ≤ Function.uncurry F := fun _ => sq_nonneg _
  have hrow : ∀ i : w, HasSum (F i) (‖S (b i)‖ ^ 2) := fun i =>
    hasSum_norm_sq_inner_basis c (S (b i))
  have hcol : ∀ j : w', HasSum (fun i : w => F i j)
      (‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := by
    intro j
    have e1 : ∀ i : w, ⟪c j, S (b i)⟫_ℂ =
        ⟪(ContinuousLinearMap.adjoint S) (c j), b i⟫_ℂ := fun i => by
      exact (ContinuousLinearMap.adjoint_inner_left S (b i) (c j)).symm
    have key : (fun i : w => F i j) = fun i : w =>
        ‖⟪b i, (ContinuousLinearMap.adjoint S) (c j)⟫_ℂ‖ ^ 2 := by
      funext i
      show ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 = _
      rw [e1 i, ← inner_conj_symm (b i)
        ((ContinuousLinearMap.adjoint S) (c j)), RCLike.norm_conj]
    rw [key]
    exact hasSum_norm_sq_inner_basis b ((ContinuousLinearMap.adjoint S) (c j))
  have hjoint : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg hFnonneg]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    have heq : (fun i : w => ∑' j : w', F i j) =
        fun i : w => ‖S (b i)‖ ^ 2 :=
      funext fun i => (hrow i).tsum_eq
    show Summable fun i : w => ∑' j : w', F i j
    rwa [heq]
  have hswap := hjoint.tsum_comm' (fun i => (hrow i).summable)
    (fun j => (hcol j).summable)
  have hLHS : ∑' j : w', ∑' i : w, F i j =
      ∑' j : w', ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2 :=
    tsum_congr fun j => (hcol j).tsum_eq
  have hRHS : ∑' i : w, ∑' j : w', F i j =
      ∑' i : w, ‖S (b i)‖ ^ 2 :=
    tsum_congr fun i => (hrow i).tsum_eq
  have hEq : ∑' j : w', ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2 =
      ∑' i : w, ‖S (b i)‖ ^ 2 := by
    rw [← hLHS, ← hRHS]
    exact hswap
  set G : w' → w → ℝ := fun j i => F i j with hGdef
  have hGnonneg : 0 ≤ Function.uncurry G := fun _ => sq_nonneg _
  have hjointG : Summable (Function.uncurry G) := by
    have hcomp : Function.uncurry G = Function.uncurry F ∘
        (Equiv.prodComm w' w) := by
      funext p
      simp [Function.uncurry, hGdef, Equiv.prodComm]
    rw [hcomp]
    exact (Equiv.prodComm w' w).summable_iff.mpr hjoint
  have hcolSummable : Summable
      (fun j : w' => ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := by
    have hpair := (summable_prod_of_nonneg hGnonneg).mp hjointG
    have h2 : Summable fun j : w' => ∑' i : w, G j i := hpair.2
    have heq2 : (fun j : w' => ∑' i : w, G j i) = fun j : w' =>
        ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2 :=
      funext fun j => (hcol j).tsum_eq
    rwa [heq2] at h2
  rw [← hEq]
  exact hcolSummable.hasSum

lemma summable_norm_sq_adjoint_of_summable_norm_sq {S : B(H)}
    {w : Set H} (b : HilbertBasis w ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    Summable (fun i : w => ‖(ContinuousLinearMap.adjoint S) (b i)‖ ^ 2) := by
  exact (hasSum_norm_sq_apply_eq_adjoint b b hb).summable

lemma hasSum_norm_sq_apply_of_basis {S : B(H)} {w w' : Set H}
    (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : w' => ‖S (c j)‖ ^ 2)
      (∑' i : w, ‖S (b i)‖ ^ 2) := by
  have hfirst := hasSum_norm_sq_apply_eq_adjoint b c hb
  have hstarc : Summable (fun j : w' =>
      ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := hfirst.summable
  have hsecond := hasSum_norm_sq_apply_eq_adjoint
    (S := ContinuousLinearMap.adjoint S) c c hstarc
  have hsecond' : HasSum (fun j : w' => ‖S (c j)‖ ^ 2)
      (∑' j : w', ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hsecond
  rw [← hfirst.tsum_eq]
  exact hsecond'

theorem summable_norm_sq_apply_of_hilbertBasis {S : B(H)}
    (w : Set H) (b : HilbertBasis w ℂ H) (hS : IsHilbertSchmidt S) :
    Summable (fun i : w => ‖S (b i)‖ ^ 2) := by
  rcases hS with ⟨w₀, b₀, hb₀⟩
  exact (hasSum_norm_sq_apply_of_basis b₀ b hb₀).summable

@[nolint unusedArguments]
theorem tsum_norm_sq_apply_of_hilbertBasis {S : B(H)}
    (w : Set H) (b : HilbertBasis w ℂ H) (hS : IsHilbertSchmidt S)
    {w₀ : Set H} (b₀ : HilbertBasis w₀ ℂ H)
    (hb₀ : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2)) :
    (∑' i : w, ‖S (b i)‖ ^ 2) = ∑' i : w₀, ‖S (b₀ i)‖ ^ 2 := by
  exact (hasSum_norm_sq_apply_of_basis b₀ b hb₀).tsum_eq

theorem isHilbertSchmidt_iff {S : B(H)}
    (hS : IsHilbertSchmidt S) (w : Set H) (b : HilbertBasis w ℂ H) :
    Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
  summable_norm_sq_apply_of_hilbertBasis w b hS

end HilbertSchmidt

end OperatorAlgebra
