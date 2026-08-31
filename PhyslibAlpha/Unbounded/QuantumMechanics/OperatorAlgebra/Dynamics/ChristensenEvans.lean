/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Dynamics.CPClosure
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Dynamics.Semigroup
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Dynamics.Trotter
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.HilbertSpace
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Christensen–Evans data for bounded irreversible dynamics

The finite-noise `LindbladData` API is the concrete `B(H)`/Kraus presentation.  This file records
the reusable C⋆-algebraic layer underneath it.  A bounded completely positive map `J` is the
general jump term; no Kraus or Stinespring choice is built into the definition.  The familiar
operator sum is recovered later whenever `J` has a Kraus representation.
-/

@[expose] public section

namespace OperatorAlgebra

open Filter
open scoped ComplexOrder CStarAlgebra NNReal

variable {A : Type*} [OperatorAlgebra A]

noncomputable local instance ceNormedAlgebraRat : NormedAlgebra ℚ (A →L[ℂ] A) :=
  .restrictScalars ℚ ℂ (A →L[ℂ] A)

noncomputable local instance ceNormedAlgebraReal : NormedAlgebra ℝ (A →L[ℂ] A) :=
  .restrictScalars ℝ ℂ (A →L[ℂ] A)

noncomputable local instance ceNormedAlgebraRatA : NormedAlgebra ℚ A :=
  .restrictScalars ℚ ℂ A

/-! ## Abstract bounded Lindblad data -/

/-- A bounded Christensen–Evans datum on a unital C⋆-algebra.

`jump` is an arbitrary completely positive map.  In `B(H)`, a Stinespring/Kraus theorem can turn
it into a family of operators; keeping it bundled here is the representation-independent form. -/
structure ChristensenEvansData (A : Type*) [OperatorAlgebra A] where
  /-- The self-adjoint Hamiltonian part. -/
  hamiltonian : Observable A
  /-- The completely positive jump map. -/
  jump : A →CP A

/-- A Stinespring witness for a completely positive map into bounded operators.

This is the operator-level form of the jump term used by the Lindblad expression.  The auxiliary
space and representation are data of the witness; existence of such a witness is intentionally a
separate theorem, not an instance or an axiom. -/
structure StinespringWitness
    (A H K : Type*) [OperatorAlgebra A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (J : A →CP B(H)) where
  /-- The representation of the input operator algebra on the auxiliary space. -/
  representation : Representation A K
  /-- The implementing bounded operator from the physical space to the auxiliary space. -/
  implementing : H →L[ℂ] K
  /-- The Stinespring identity. -/
  map_eq : ∀ a : A,
    J a = ContinuousLinearMap.adjoint implementing ∘L
      (representation a) ∘L implementing

lemma completelyPositiveMap_map_star_general
    {A B : Type*} [OperatorAlgebra A] [OperatorAlgebra B]
    (J : A →CP B) (a : A) : star (J a) = J (star a) := by
  obtain ⟨x, hx, _, ha⟩ := CStarAlgebra.exists_sum_four_nonneg a
  rw [ha]
  simp only [map_sum, map_smul, star_sum, star_smul]
  apply Finset.sum_congr rfl
  intro i hi
  have hxi : IsSelfAdjoint (x i) := IsSelfAdjoint.of_nonneg (hx i)
  have hJxi : IsSelfAdjoint (J (x i)) :=
    IsSelfAdjoint.of_nonneg ((PositiveLinearMap.ofClass J).map_nonneg (hx i))
  rw [hJxi.star_eq, hxi.star_eq]

namespace StinespringWitness

variable {A H K : Type*} [OperatorAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {J : A →CP B(H)} (W : StinespringWitness A H K J)

lemma map_eq_apply (a : A) :
    J a = ContinuousLinearMap.adjoint W.implementing ∘L
      (W.representation a) ∘L W.implementing :=
  W.map_eq a

end StinespringWitness

namespace StinespringWitness

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {J : B(H) →CP B(H)}

/-- Turn a Stinespring witness for a bounded-operator CP map and a bounded self-adjoint
Hamiltonian into Christensen–Evans data. -/
@[nolint unusedArguments]
noncomputable def toChristensenEvansData
    (W : StinespringWitness (B(H)) H K J) (h : Observable B(H)) :
    ChristensenEvansData B(H) where
  hamiltonian := h
  jump := J

end StinespringWitness

namespace StinespringWitness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The elementary Stinespring witness for a single Kraus/conjugation map.

This is the concrete bridge used by finite-noise Lindblad data; a general CP map needs the
separate Stinespring existence theorem. -/
noncomputable def conjugation (W : B(H)) :
    StinespringWitness (B(H)) H H (completelyPositiveMapConjugation W) where
  representation := StarAlgHom.id ℂ B(H)
  implementing := W
  map_eq := by
    intro a
    ext x
    change (star W * a * W) x = _
    rw [ContinuousLinearMap.star_eq_adjoint]
    rfl

end StinespringWitness

namespace StinespringWitness

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι]

section FiniteKraus

/-- The block-diagonal action of a bounded operator on a finite Hilbert sum. -/
noncomputable def finiteKrausDiagonalMap (a : B(H)) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) := by
  let e : PiLp 2 (fun _ : ι => H) ≃L[ℂ] (∀ _ : ι, H) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)
  let p : (∀ _ : ι, H) →L[ℂ] (∀ _ : ι, H) :=
    ContinuousLinearMap.piMap (fun _ : ι => a)
  exact e.symm.toContinuousLinearMap.comp (p.comp e.toContinuousLinearMap)

@[nolint unusedArguments, simp]
lemma finiteKrausDiagonalMap_apply (a : B(H))
    (x : PiLp 2 (fun _ : ι => H)) (i : ι) :
    (finiteKrausDiagonalMap (ι := ι) a x).ofLp i = a (x.ofLp i) := by
  simp [finiteKrausDiagonalMap]

lemma finiteKrausDiagonalMap_adjoint (a : B(H)) :
    (finiteKrausDiagonalMap (ι := ι) a).adjoint =
      finiteKrausDiagonalMap (ι := ι) (star a : B(H)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp_rw [ContinuousLinearMap.star_eq_adjoint]
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i hi
  change inner ℂ (x.ofLp i) (a (y.ofLp i)) =
    inner ℂ ((ContinuousLinearMap.adjoint a) (x.ofLp i)) (y.ofLp i)
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- The finite Kraus CP map associated with a family of bounded operators. -/
noncomputable def finiteKrausCPMap (V : ι → B(H)) : B(H) →CP B(H) :=
  completelyPositiveMapFinsetSum Finset.univ
    (fun i => completelyPositiveMapConjugation (V i))

/-- The bounded operator that sends a vector to its finite family of Kraus images. -/
noncomputable def finiteKrausImplementing (V : ι → B(H)) :
    H →L[ℂ] PiLp 2 (fun _ : ι => H) := by
  let e : PiLp 2 (fun _ : ι => H) ≃L[ℂ] (∀ _ : ι, H) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)
  let p : H →L[ℂ] (∀ _ : ι, H) := ContinuousLinearMap.pi (fun i => V i)
  exact e.symm.toContinuousLinearMap.comp p

/-- A finite Kraus family gives a Stinespring witness on the finite Hilbert sum. -/
noncomputable def finiteKraus (V : ι → B(H)) :
    StinespringWitness (B(H)) H (PiLp 2 (fun _ : ι => H)) (finiteKrausCPMap V) where
  representation := {
    toFun := finiteKrausDiagonalMap
    map_one' := by
      ext x i
      simp [finiteKrausDiagonalMap]
    map_mul' := by
      intro a b
      ext x i
      simp [finiteKrausDiagonalMap]
    map_zero' := by
      ext x i
      simp [finiteKrausDiagonalMap]
    map_add' := by
      intro a b
      ext x i
      simp [finiteKrausDiagonalMap]
    commutes' := by
      intro r
      ext x i
      simp [finiteKrausDiagonalMap]
    map_star' := by
      intro a
      simpa only [ContinuousLinearMap.star_eq_adjoint] using
        (finiteKrausDiagonalMap_adjoint (ι := ι) a).symm }
  implementing := finiteKrausImplementing V
  map_eq := by
    intro a
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    change inner ℂ ((finiteKrausCPMap V a) x) y =
      inner ℂ ((ContinuousLinearMap.adjoint (finiteKrausImplementing V))
        (finiteKrausDiagonalMap a (finiteKrausImplementing V x))) y
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [finiteKrausCPMap, completelyPositiveMap_finsetSum_apply,
      completelyPositiveMap_conjugation_apply, finiteKrausImplementing,
      PiLp.inner_apply, finiteKrausDiagonalMap_apply]
    simp_rw [ContinuousLinearMap.star_eq_adjoint]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ContinuousLinearMap.adjoint_inner_left]

end FiniteKraus

end StinespringWitness

namespace StinespringWitness

/-! ### The finite block representation

The standard Stinespring pre-Hilbert space uses positivity of finite operator matrices.  The
following representation is the concrete bridge from that C⋆-algebraic positivity to the usual
Hilbert-space quadratic form.  It is useful independently of any choice of Kraus family. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def blockMatrixMap
    {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) B(H)) :
    PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin n => H) := by
  let e : PiLp 2 (fun _ : Fin n => H) ≃L[ℂ] (∀ _ : Fin n, H) :=
    PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => H)
  let p : (∀ _ : Fin n, H) →L[ℂ] (∀ _ : Fin n, H) :=
    ContinuousLinearMap.pi (fun i =>
      ∑ j, (M i j).comp (ContinuousLinearMap.proj j))
  exact e.symm.toContinuousLinearMap.comp (p.comp e.toContinuousLinearMap)

@[nolint unusedArguments, simp]
lemma blockMatrixMap_apply
    {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) B(H))
    (x : PiLp 2 (fun _ : Fin n => H)) (i : Fin n) :
    (blockMatrixMap M x).ofLp i = ∑ j, M i j (x.ofLp j) := by
  simp [blockMatrixMap, PiLp.coe_continuousLinearEquiv]

lemma blockMatrixMap_star
    {n : ℕ} (M : CStarMatrix (Fin n) (Fin n) B(H)) :
    blockMatrixMap (star M) = (blockMatrixMap M).adjoint := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, blockMatrixMap_apply,
    CStarMatrix.star_eq_conjTranspose, CStarMatrix.conjTranspose_apply,
    ContinuousLinearMap.star_eq_adjoint, sum_inner, inner_sum]
  simp_rw [ContinuousLinearMap.adjoint_inner_left]
  rw [Finset.sum_comm]

lemma blockMatrixMap_mul
    {n : ℕ} (M N : CStarMatrix (Fin n) (Fin n) B(H)) :
    blockMatrixMap (M * N) = blockMatrixMap M ∘L blockMatrixMap N := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  simp only [blockMatrixMap_apply, ContinuousLinearMap.comp_apply, CStarMatrix.mul_apply]
  simp_rw [ContinuousLinearMap.sum_apply]
  rw [Finset.sum_comm]
  simp_rw [mul_apply_eq_comp]
  simp_rw [map_sum]

lemma blockMatrixMap_one
    {n : ℕ} :
    blockMatrixMap (1 : CStarMatrix (Fin n) (Fin n) B(H)) = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  rw [blockMatrixMap_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Ne.symm hji]
  · simp

lemma blockMatrixMap_add
    {n : ℕ} (M N : CStarMatrix (Fin n) (Fin n) B(H)) :
    blockMatrixMap (M + N) = blockMatrixMap M + blockMatrixMap N := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  rw [blockMatrixMap_apply]
  rw [add_apply, PiLp.add_apply]
  simp only [CStarMatrix.add_apply]
  simp_rw [add_apply]
  rw [Finset.sum_add_distrib]
  rw [blockMatrixMap_apply, blockMatrixMap_apply]

lemma blockMatrixMap_zero
    {n : ℕ} :
    blockMatrixMap (0 : CStarMatrix (Fin n) (Fin n) B(H)) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  simp [blockMatrixMap_apply]

noncomputable def blockMatrixRepresentation
    {n : ℕ} :
    CStarMatrix (Fin n) (Fin n) B(H) →⋆ₐ[ℂ]
      B(PiLp 2 (fun _ : Fin n => H)) where
  toFun := blockMatrixMap
  map_one' := blockMatrixMap_one
  map_mul' := blockMatrixMap_mul
  map_zero' := blockMatrixMap_zero
  map_add' := blockMatrixMap_add
  commutes' := by
    intro c
    apply ContinuousLinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    rw [blockMatrixMap_apply]
    simp only [Algebra.algebraMap_eq_smul_one, smul_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [Ne.symm hji]
    · simp
  map_star' := blockMatrixMap_star

lemma blockMatrixMap_isPositive
    {n : ℕ} {M : CStarMatrix (Fin n) (Fin n) B(H)} (hM : 0 ≤ M) :
    (blockMatrixMap M).IsPositive := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mp
  change 0 ≤ (blockMatrixRepresentation (H := H) (n := n)) M
  exact map_nonneg (blockMatrixRepresentation (H := H) (n := n)) hM

lemma blockMatrixMap_inner_nonneg
    {n : ℕ} {M : CStarMatrix (Fin n) (Fin n) B(H)} (hM : 0 ≤ M)
    (x : PiLp 2 (fun _ : Fin n => H)) :
    0 ≤ ∑ i, ∑ j, inner ℂ (M i j (x.ofLp j)) (x.ofLp i) := by
  have h := (blockMatrixMap_isPositive hM).inner_nonneg_left x
  simpa [PiLp.inner_apply, blockMatrixMap_apply, sum_inner, inner_sum] using h

/-- A square matrix whose only nonzero row is the zeroth row. -/
noncomputable def rowMatrix
    {A : Type*} [OperatorAlgebra A] {n : ℕ} [NeZero n] (a : Fin n → A) :
    CStarMatrix (Fin n) (Fin n) A := fun i j => if i = 0 then a j else 0

/-- The Gram matrix of a finite family of elements of a C⋆-algebra. -/
noncomputable def gramMatrix
    {A : Type*} [OperatorAlgebra A] {n : ℕ} [NeZero n] (a : Fin n → A) :
    CStarMatrix (Fin n) (Fin n) A := star (rowMatrix a) * rowMatrix a

@[simp]
lemma gramMatrix_apply
    {A : Type*} [OperatorAlgebra A] {n : ℕ} [NeZero n] (a : Fin n → A) (i j : Fin n) :
    gramMatrix a i j = star (a i) * a j := by
  simp [gramMatrix, rowMatrix, CStarMatrix.mul_apply, CStarMatrix.star_eq_conjTranspose]

lemma gramMatrix_nonneg
    {A : Type*} [OperatorAlgebra A] {n : ℕ} [NeZero n] (a : Fin n → A) :
    0 ≤ gramMatrix a := by
  exact star_mul_self_nonneg (rowMatrix a)

lemma cpGramMatrix_nonneg
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {n : ℕ} [NeZero n] (J : A →CP B(H)) (a : Fin n → A) :
    0 ≤ (gramMatrix a).map J := by
  exact J.map_cstarMatrix_nonneg _ (gramMatrix_nonneg a)

lemma cpKernel_inner_nonneg
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {n : ℕ} [NeZero n] (J : A →CP B(H)) (a : Fin n → A)
    (x : PiLp 2 (fun _ : Fin n => H)) :
    0 ≤ ∑ i, ∑ j, inner ℂ (J (star (a i) * a j) (x.ofLp j)) (x.ofLp i) := by
  have h := blockMatrixMap_inner_nonneg (cpGramMatrix_nonneg J a) x
  simpa [gramMatrix_apply] using h

lemma cpKernel_inner_nonneg'
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {n : ℕ} (J : A →CP B(H)) (a : Fin n → A)
    (x : PiLp 2 (fun _ : Fin n => H)) :
    0 ≤ ∑ i, ∑ j, inner ℂ (J (star (a i) * a j) (x.ofLp j)) (x.ofLp i) := by
  rcases n with _ | n
  · simp
  · letI : NeZero (Nat.succ n) := ⟨Nat.succ_ne_zero n⟩
    exact cpKernel_inner_nonneg J a x

lemma cpKernel_inner_nonneg_natural
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {n : ℕ} [NeZero n] (J : A →CP B(H)) (a : Fin n → A)
    (x : PiLp 2 (fun _ : Fin n => H)) :
    0 ≤ ∑ i, ∑ j, inner ℂ (x.ofLp i) (J (star (a i) * a j) (x.ofLp j)) := by
  have hM : 0 ≤ (star (gramMatrix a)).map J := by
    exact J.map_cstarMatrix_nonneg _ (star_nonneg_iff.mpr (gramMatrix_nonneg a))
  have h := blockMatrixMap_inner_nonneg hM x
  rw [Finset.sum_comm] at h
  have hterm (i j : Fin n) :
      inner ℂ ((J (star (a j) * a i)) (x.ofLp i)) (x.ofLp j) =
        inner ℂ (x.ofLp i) ((J (star (a i) * a j)) (x.ofLp j)) := by
    rw [← ContinuousLinearMap.adjoint_inner_left]
    have hop : J (star (a j) * a i) =
        ContinuousLinearMap.adjoint (J (star (a i) * a j)) := by
      calc
        J (star (a j) * a i) = J (star (star (a i) * a j)) := by
          congr 1
          simp [star_mul]
        _ = star (J (star (a i) * a j)) :=
          (completelyPositiveMap_map_star_general J _).symm
        _ = ContinuousLinearMap.adjoint (J (star (a i) * a j)) := by
          rfl
    rw [hop]
  have h' : 0 ≤ ∑ i, ∑ j,
      inner ℂ ((J (star (a j) * a i)) (x.ofLp i)) (x.ofLp j) := by
    simpa [gramMatrix_apply, CStarMatrix.star_apply] using h
  have hEq : (∑ i, ∑ j,
      inner ℂ ((J (star (a j) * a i)) (x.ofLp i)) (x.ofLp j)) =
      ∑ i, ∑ j, inner ℂ (x.ofLp i) ((J (star (a i) * a j)) (x.ofLp j)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact hterm i j
  rw [← hEq]
  exact h'

lemma cpKernel_inner_nonneg_natural'
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {n : ℕ} (J : A →CP B(H)) (a : Fin n → A)
    (x : PiLp 2 (fun _ : Fin n => H)) :
    0 ≤ ∑ i, ∑ j, inner ℂ (x.ofLp i) (J (star (a i) * a j) (x.ofLp j)) := by
  rcases n with _ | n
  · simp
  · letI : NeZero (Nat.succ n) := ⟨Nat.succ_ne_zero n⟩
    exact cpKernel_inner_nonneg_natural J a x

noncomputable def cpKernelInner
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (x y : A →₀ H) : ℂ :=
  ∑ a : x.support, (∑ b : y.support,
    inner ℂ (x a) (J (star (a : A) * (b : A)) (y b)))

lemma cpKernelInner_nonneg
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (x : A →₀ H) : 0 ≤ cpKernelInner J x x := by
  classical
  let s := x.support
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let v : PiLp 2 (fun _ : Fin (Fintype.card s) => H) :=
    WithLp.toLp 2 (fun i => x (e.symm i))
  have h := cpKernel_inner_nonneg_natural' J (fun i => (e.symm i : A)) v
  have hv (i : Fin (Fintype.card s)) : v.ofLp i = x (e.symm i : A) := rfl
  dsimp [cpKernelInner, s]
  change 0 ≤ ∑ a : s, ∑ b : s,
    inner ℂ (x a) (J (star (a : A) * (b : A)) (x b))
  rw [← e.symm.sum_comp]
  simp_rw [← e.symm.sum_comp]
  simpa [hv] using h

/-! ### The Stinespring pre-inner product

The finite-support formula is most convenient for proving positivity.  The equivalent `Finsupp`
sum formula is the convenient one for the algebraic inner-product identities.  Keeping both
spellings makes the construction readable and avoids hiding the finite-support reduction in
later representation arguments. -/

noncomputable def cpKernelInnerSum
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (x y : A →₀ H) : ℂ :=
  x.sum fun a u => y.sum fun b v =>
    inner ℂ u (J (star (a : A) * (b : A)) v)

lemma cpKernelInnerSum_eq
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (x y : A →₀ H) :
    cpKernelInnerSum J x y = cpKernelInner J x y := by
  classical
  simp only [cpKernelInnerSum, cpKernelInner, Finsupp.sum]
  rw [← Finset.sum_attach x.support]
  simp_rw [← Finset.sum_attach y.support]
  rfl

lemma cpKernelInnerSum_add_left
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (x y z : A →₀ H) :
    cpKernelInnerSum J (x + y) z = cpKernelInnerSum J x z + cpKernelInnerSum J y z := by
  classical
  unfold cpKernelInnerSum
  rw [Finsupp.sum_add_index']
  · simp
  · intro a b₁ b₂
    simp

lemma cpKernelInnerSum_smul_left
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (r : ℂ) (x y : A →₀ H) :
    cpKernelInnerSum J (r • x) y = starRingEnd ℂ r * cpKernelInnerSum J x y := by
  classical
  unfold cpKernelInnerSum
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp_rw [inner_smul_left]
  simp only [Finsupp.sum]
  simp_rw [← Finset.mul_sum]

lemma cpKernelInnerSum_conj_symm
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (x y : A →₀ H) :
    starRingEnd ℂ (cpKernelInnerSum J y x) = cpKernelInnerSum J x y := by
  classical
  unfold cpKernelInnerSum
  simp only [Finsupp.sum]
  simp_rw [map_sum]
  simp_rw [inner_conj_symm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hop : J (star (b : A) * (a : A)) =
      ContinuousLinearMap.adjoint (J (star (a : A) * (b : A))) := by
    calc
      J (star (b : A) * (a : A)) = J (star (star (a : A) * (b : A))) := by
        congr 1
        simp [star_mul]
      _ = star (J (star (a : A) * (b : A))) :=
        (completelyPositiveMap_map_star_general J _).symm
      _ = ContinuousLinearMap.adjoint (J (star (a : A) * (b : A))) := by
        rfl
  rw [hop]
  rw [ContinuousLinearMap.adjoint_inner_left]

lemma cpKernelInnerSum_nonneg
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (x : A →₀ H) : 0 ≤ cpKernelInnerSum J x x := by
  rw [cpKernelInnerSum_eq]
  exact cpKernelInner_nonneg J x

/-- The canonical pre-inner-product core associated with a CP map.

This is the algebraic starting point of the general Stinespring construction.  Its null space is
quotiented and completed in the next layer; no finite-dimensional or Kraus choice occurs here. -/
noncomputable def cpKernelCore
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) : PreInnerProductSpace.Core ℂ (A →₀ H) where
  inner := cpKernelInnerSum J
  conj_inner_symm := cpKernelInnerSum_conj_symm J
  re_inner_nonneg := by
    intro x
    exact (cpKernelInnerSum_nonneg J x).1
  add_left := cpKernelInnerSum_add_left J
  smul_left := by
    intro x y r
    simpa only [starRingEnd_apply] using cpKernelInnerSum_smul_left J r x y

/-! ### The algebra action on the Stinespring pre-Hilbert space

The CP kernel is not merely a positive form: left multiplication by `a` is the prospective
representation of `A`.  The next lemmas establish its algebraic adjoint relation.  The norm bound
is proved below from positivity of the weighted CP kernel; together they are the input needed to
pass this action through the separation quotient and its completion. -/

@[nolint unusedArguments]
noncomputable def stinespringLeftMap
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (a : A) : (A →₀ H) →ₗ[ℂ] (A →₀ H) :=
  Finsupp.lsum ℂ (fun b => Finsupp.lsingle (a * b))

@[simp]
lemma stinespringLeftMap_single
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (a b : A) (h : H) :
    stinespringLeftMap a (Finsupp.single b h) = Finsupp.single (a * b) h := by
  simp [stinespringLeftMap]

lemma stinespringLeftMap_apply
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (a : A) (x : A →₀ H) :
    stinespringLeftMap a x = x.sum (fun b h => Finsupp.single (a * b) h) := by
  rw [stinespringLeftMap, Finsupp.lsum_apply]
  rfl

lemma cpKernelInnerSum_add_right
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (x y z : A →₀ H) :
    cpKernelInnerSum J x (y + z) =
      cpKernelInnerSum J x y + cpKernelInnerSum J x z := by
  calc
    cpKernelInnerSum J x (y + z) =
        starRingEnd ℂ (cpKernelInnerSum J (y + z) x) :=
      (cpKernelInnerSum_conj_symm J x (y + z)).symm
    _ = starRingEnd ℂ (cpKernelInnerSum J y x + cpKernelInnerSum J z x) := by
      rw [cpKernelInnerSum_add_left]
    _ = starRingEnd ℂ (cpKernelInnerSum J y x) +
        starRingEnd ℂ (cpKernelInnerSum J z x) := by simp
    _ = cpKernelInnerSum J x y + cpKernelInnerSum J x z := by
      rw [cpKernelInnerSum_conj_symm, cpKernelInnerSum_conj_symm]

lemma cpKernelInnerSum_smul_right
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (r : ℂ) (x y : A →₀ H) :
    cpKernelInnerSum J x (r • y) = r * cpKernelInnerSum J x y := by
  calc
    cpKernelInnerSum J x (r • y) =
        starRingEnd ℂ (cpKernelInnerSum J (r • y) x) :=
      (cpKernelInnerSum_conj_symm J x (r • y)).symm
    _ = starRingEnd ℂ (starRingEnd ℂ r * cpKernelInnerSum J y x) := by
      rw [cpKernelInnerSum_smul_left]
    _ = r * starRingEnd ℂ (cpKernelInnerSum J y x) := by simp
    _ = r * cpKernelInnerSum J x y := by rw [cpKernelInnerSum_conj_symm]

lemma cpKernelInnerSum_zero_left
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (x : A →₀ H) :
    cpKernelInnerSum J 0 x = 0 := by
  simp [cpKernelInnerSum]

lemma cpKernelInnerSum_zero_right
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (x : A →₀ H) :
    cpKernelInnerSum J x 0 = 0 := by
  simp [cpKernelInnerSum]

lemma stinespringLeftMap_inner
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (a : A) (x y : A →₀ H) :
    cpKernelInnerSum J (stinespringLeftMap a x) y =
      cpKernelInnerSum J x (stinespringLeftMap (star a) y) := by
  have single_action_inner : ∀ (b : A) (h : H) (y : A →₀ H),
      cpKernelInnerSum J (stinespringLeftMap a (Finsupp.single b h)) y =
        cpKernelInnerSum J (Finsupp.single b h)
          (stinespringLeftMap (star a) y) := by
    intro b h y
    induction y using Finsupp.induction with
    | zero =>
        exact (cpKernelInnerSum_zero_right J
          (stinespringLeftMap a (Finsupp.single b h))).trans
          (cpKernelInnerSum_zero_right J (Finsupp.single b h)).symm
    | @single_add c k y hc hk iy =>
        calc
          cpKernelInnerSum J (stinespringLeftMap a (Finsupp.single b h))
              (Finsupp.single c k + y) =
              cpKernelInnerSum J (stinespringLeftMap a (Finsupp.single b h))
                  (Finsupp.single c k) +
                cpKernelInnerSum J (stinespringLeftMap a (Finsupp.single b h)) y :=
            cpKernelInnerSum_add_right J _ _ _
          _ = cpKernelInnerSum J (Finsupp.single b h)
                (stinespringLeftMap (star a) (Finsupp.single c k)) +
                cpKernelInnerSum J (Finsupp.single b h)
                  (stinespringLeftMap (star a) y) := by
            rw [iy]
            congr 1
            rw [stinespringLeftMap_single]
            simp [cpKernelInnerSum, Finsupp.sum_single_index, mul_assoc]
          _ = cpKernelInnerSum J (Finsupp.single b h)
                (stinespringLeftMap (star a) (Finsupp.single c k + y)) := by
            rw [map_add (stinespringLeftMap (star a)), cpKernelInnerSum_add_right]
  induction x using Finsupp.induction with
  | zero =>
      exact (cpKernelInnerSum_zero_left J (stinespringLeftMap (star a) y)).symm
  | @single_add b h x hb hh ih =>
    calc
      cpKernelInnerSum J (stinespringLeftMap a (Finsupp.single b h + x)) y =
          cpKernelInnerSum J (stinespringLeftMap a (Finsupp.single b h)) y +
            cpKernelInnerSum J (stinespringLeftMap a x) y := by
        rw [map_add, cpKernelInnerSum_add_left]
      _ = cpKernelInnerSum J (Finsupp.single b h)
            (stinespringLeftMap (star a) y) +
            cpKernelInnerSum J x (stinespringLeftMap (star a) y) := by
        rw [single_action_inner b h y, ih]
      _ = cpKernelInnerSum J (Finsupp.single b h + x)
            (stinespringLeftMap (star a) y) := by
        rw [cpKernelInnerSum_add_left]

/-! ### Positivity with a positive middle factor

The weighted kernel is the matrix compression used to prove the boundedness of the left action.
Its proof is exactly the finite-matrix CP argument, with a positive diagonal matrix in the middle.
-/

noncomputable def stinespringWeightedInner
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) (q : A) (x y : A →₀ H) : ℂ :=
  x.sum fun a u => y.sum fun b v =>
    inner ℂ u (J (star (a : A) * q * (b : A)) v)

lemma stinespringWeightedInner_nonneg
    {A : Type*} [OperatorAlgebra A] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : A →CP B(H)) {q : A} (hq : 0 ≤ q) (x : A →₀ H) :
    0 ≤ stinespringWeightedInner J q x x := by
  classical
  by_cases hs : x.support.Nonempty
  · obtain ⟨i, hi⟩ := hs
    letI : Nonempty x.support := ⟨i, hi⟩
    letI : NeZero (Fintype.card x.support) := ⟨Fintype.card_ne_zero⟩
    let s := x.support
    let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
    let v : PiLp 2 (fun _ : Fin (Fintype.card s) => H) :=
      WithLp.toLp 2 (fun i => x (e.symm i))
    let Q : CStarMatrix (Fin (Fintype.card s)) (Fin (Fintype.card s)) A :=
      CStarMatrix.ofMatrix (Matrix.diagonal (fun _ => q))
    let D : CStarMatrix (Fin (Fintype.card s)) (Fin (Fintype.card s)) A :=
      CStarMatrix.ofMatrix (Matrix.diagonal (fun _ => CFC.sqrt q))
    have hQ : 0 ≤ Q := by
      have hD : 0 ≤ star D * D := star_mul_self_nonneg D
      have hEq : star D * D = Q := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [D, Q, CStarMatrix.star_eq_conjTranspose, CStarMatrix.mul_apply,
            Matrix.diagonal, (CFC.sqrt_nonneg q).isSelfAdjoint.star_eq,
            CFC.sqrt_mul_sqrt_self q hq]
        · have hji : ¬j = i := Ne.symm hij
          simp [D, Q, CStarMatrix.star_eq_conjTranspose, CStarMatrix.mul_apply,
            Matrix.diagonal, hij, hji]
      rw [← hEq]
      exact hD
    let r : Fin (Fintype.card s) → A := fun i => (e.symm i : A)
    let R : CStarMatrix (Fin (Fintype.card s)) (Fin (Fintype.card s)) A := rowMatrix r
    let M := star R * Q * R
    have hM : 0 ≤ M := by
      exact star_left_conjugate_nonneg hQ R
    have hJM : 0 ≤ M.map J := J.map_cstarMatrix_nonneg M hM
    have hinner := blockMatrixMap_inner_nonneg hJM v
    have hentry (i j : Fin (Fintype.card s)) :
        M i j = star (r i) * q * r j := by
      simp [M, R, Q, rowMatrix, CStarMatrix.mul_apply,
        CStarMatrix.star_eq_conjTranspose, Matrix.diagonal]
    have hv (i : Fin (Fintype.card s)) : v.ofLp i = x (e.symm i : A) := rfl
    dsimp [stinespringWeightedInner, s]
    simp only [Finsupp.sum]
    rw [← Finset.sum_attach x.support]
    simp_rw [← Finset.sum_attach x.support]
    change 0 ≤ ∑ i : s, ∑ j : s,
      inner ℂ (x i) (J (star (i : A) * q * (j : A)) (x j))
    rw [← e.symm.sum_comp]
    simp_rw [← e.symm.sum_comp]
    let S : ℂ := ∑ i, ∑ j,
      inner ℂ ((J (M i j)) (v.ofLp j)) (v.ofLp i)
    let T : ℂ := ∑ i, ∑ j,
      inner ℂ (v.ofLp i) ((J (M i j)) (v.ofLp j))
    have hST : starRingEnd ℂ S = T := by
      dsimp [S, T]
      simp_rw [map_sum, inner_conj_symm]
    have hSS : starRingEnd ℂ S = S := by
      apply (IsSelfAdjoint.of_nonneg hinner).star_eq
    have hT : 0 ≤ T := by
      rw [← hST, hSS]
      exact hinner
    simpa [T, hentry, hv, blockMatrixMap_apply] using hT
  · have hx : x = 0 :=
      Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
    rw [hx]
    simp [stinespringWeightedInner]

end StinespringWitness

namespace ChristensenEvansData

variable (D : ChristensenEvansData A)

/-- The bounded jump map underlying the bundled completely positive map. -/
noncomputable def jumpMap : A →L[ℂ] A :=
  completelyPositiveMapToContinuousLinearMap D.jump

/-- The effective no-jump operator.

The normalization is chosen so that the no-jump contribution plus the jump contribution
annihilates the identity. -/
noncomputable def noJumpOperator : A :=
  -Complex.I • (D.hamiltonian : A) -
    (2 : ℂ)⁻¹ • D.jump (1 : A)

/-- The no-jump bounded map `a ↦ N⋆a + aN`. -/
noncomputable def noJumpMap : A →L[ℂ] A :=
  ContinuousLinearMap.mulLeftRight ℂ A (star D.noJumpOperator) 1 +
    ContinuousLinearMap.mulLeftRight ℂ A 1 D.noJumpOperator

/-- The Hamiltonian commutator part. -/
noncomputable def hamiltonianPart : A →L[ℂ] A :=
  Complex.I •
    (ContinuousLinearMap.mulLeftRight ℂ A (D.hamiltonian : A) 1 -
      ContinuousLinearMap.mulLeftRight ℂ A 1 (D.hamiltonian : A))

/-- The bounded Christensen–Evans/Lindblad generator.

This is the representation-independent form
`L(a) = i[H,a] + J(a) - ½(J(1)a + aJ(1))`. -/
noncomputable def generator : A →L[ℂ] A :=
  D.hamiltonianPart + D.jumpMap -
    (2 : ℂ)⁻¹ •
      (ContinuousLinearMap.mulLeftRight ℂ A (D.jump (1 : A)) 1 +
        ContinuousLinearMap.mulLeftRight ℂ A 1 (D.jump (1 : A)))

@[simp]
lemma jumpMap_apply (a : A) :
    D.jumpMap a = D.jump a :=
  rfl

@[simp]
lemma noJumpMap_apply (a : A) :
    D.noJumpMap a = star D.noJumpOperator * a + a * D.noJumpOperator := by
  simp [noJumpMap, ContinuousLinearMap.mulLeftRight_apply]

@[simp]
lemma hamiltonianPart_apply (a : A) :
    D.hamiltonianPart a =
      Complex.I • ((D.hamiltonian : A) * a - a * (D.hamiltonian : A)) := by
  simp [hamiltonianPart, ContinuousLinearMap.mulLeftRight_apply, sub_eq_add_neg]

@[simp]
lemma generator_apply (a : A) :
    D.generator a =
      Complex.I • ((D.hamiltonian : A) * a - a * (D.hamiltonian : A)) + D.jump a -
        (2 : ℂ)⁻¹ •
          (D.jump (1 : A) * a + a * D.jump (1 : A)) := by
  simp [generator, hamiltonianPart, jumpMap,
    ContinuousLinearMap.mulLeftRight_apply, sub_eq_add_neg, smul_add]

lemma generator_eq_noJumpMap_add_jumpMap (D : ChristensenEvansData A) :
    D.generator = D.noJumpMap + D.jumpMap := by
  apply ContinuousLinearMap.ext
  intro a
  change D.generator a = D.noJumpMap a + D.jumpMap a
  rw [generator_apply, noJumpMap_apply, noJumpOperator,
    jumpMap_apply]
  have h01 : (0 : A) ≤ 1 := by
    simpa using (star_mul_self_nonneg (1 : A))
  have hJ1 : star (D.jump (1 : A)) = D.jump (1 : A) := by
    exact (IsSelfAdjoint.of_nonneg
      ((PositiveLinearMap.ofClass D.jump).map_nonneg h01)).star_eq
  simp [star_sub, star_smul, star_mul, star_star, smul_add, smul_sub,
    sub_mul, mul_sub, add_mul, mul_add, neg_mul, mul_neg, hJ1]
  noncomm_ring

lemma generator_apply_one (D : ChristensenEvansData A) :
    D.generator 1 = 0 := by
  rw [generator_apply]
  simp only [mul_one, one_mul, sub_self, smul_zero, zero_add]
  rw [← two_smul ℂ (D.jump (1 : A))]
  simp [smul_smul]

namespace StinespringWitness

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {J : B(H) →CP B(H)} (W : StinespringWitness (B(H)) H K J)

/- The Stinespring witness exposes the usual operator form of the bounded
Christensen--Evans generator.  This is only an algebraic repackaging: the
existence of `W` is deliberately not asserted here. -/
lemma generator_apply_operator_form
    (h : Observable B(H)) (a : B(H)) :
    (W.toChristensenEvansData h).generator a =
      Complex.I • ((h : B(H)) * a - a * (h : B(H))) +
        (ContinuousLinearMap.adjoint W.implementing ∘L
          (W.representation a) ∘L W.implementing) -
        (2 : ℂ)⁻¹ •
          ((ContinuousLinearMap.adjoint W.implementing ∘L
            (W.representation (1 : B(H))) ∘L W.implementing) * a +
            a * (ContinuousLinearMap.adjoint W.implementing ∘L
              (W.representation (1 : B(H))) ∘L W.implementing)) := by
  rw [ChristensenEvansData.generator_apply]
  change Complex.I • ((h : B(H)) * a - a * (h : B(H))) + J a -
      (2 : ℂ)⁻¹ • (J (1 : B(H)) * a + a * J (1 : B(H))) = _
  rw [W.map_eq_apply, W.map_eq_apply]

end StinespringWitness

lemma generator_star (D : ChristensenEvansData A) (a : A) :
    star (D.generator a) = D.generator (star a) := by
  rw [generator_apply, generator_apply]
  simp only [star_add, star_smul, star_sub, star_mul, star_star]
  rw [selfAdjoint.star_val_eq]
  rw [completelyPositiveMap_map_star]
  have hJ1 : star (D.jump (1 : A)) = D.jump (1 : A) := by
    exact (IsSelfAdjoint.of_nonneg
      ((PositiveLinearMap.ofClass D.jump).map_nonneg (by
        simpa using (star_mul_self_nonneg (1 : A))))).star_eq
  simp [add_comm, mul_assoc, hJ1]
  rw [← smul_neg]
  congr 1
  noncomm_ring

lemma generator_isHermitianPreserving (D : ChristensenEvansData A) :
    ∀ ⦃a : A⦄, IsSelfAdjoint a → IsSelfAdjoint (D.generator a) := by
  intro a ha
  rw [isSelfAdjoint_iff]
  rw [D.generator_star, ha.star_eq]

/-! ## Completely positive product approximants -/

noncomputable def noJumpEvolution (D : ChristensenEvansData A) (t : ℝ) :
    A →CP A :=
  completelyPositiveMapConjugation (NormedSpace.exp (t • D.noJumpOperator))

@[simp]
lemma noJumpEvolution_apply (D : ChristensenEvansData A) (t : ℝ) (a : A) :
    D.noJumpEvolution t a =
      star (NormedSpace.exp (t • D.noJumpOperator)) * a *
        NormedSpace.exp (t • D.noJumpOperator) :=
  rfl

@[simp]
lemma noJumpEvolution_zero (D : ChristensenEvansData A) :
    D.noJumpEvolution 0 = completelyPositiveMapId A := by
  apply DFunLike.coe_injective
  funext a
  simp [noJumpEvolution]

lemma noJumpEvolution_add (D : ChristensenEvansData A) (s t : ℝ) :
    D.noJumpEvolution (s + t) =
      completelyPositiveMapComp (D.noJumpEvolution s) (D.noJumpEvolution t) := by
  apply DFunLike.coe_injective
  funext a
  rw [completelyPositiveMap_comp_apply, noJumpEvolution_apply,
    noJumpEvolution_apply, noJumpEvolution_apply]
  let X := NormedSpace.exp (s • D.noJumpOperator)
  let Y := NormedSpace.exp (t • D.noJumpOperator)
  have hcommST : Commute (s • D.noJumpOperator) (t • D.noJumpOperator) := by
    rw [commute_iff_eq]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [mul_comm s t]
  have hcomm : Commute X Y := by
    dsimp [X, Y]
    exact hcommST.exp_left.exp_right
  have hexp : NormedSpace.exp ((s + t) • D.noJumpOperator) = X * Y := by
    rw [add_smul]
    exact NormedSpace.exp_add_of_commute hcommST
  rw [hexp]
  change star (X * Y) * a * (X * Y) = star X * (star Y * a * Y) * X
  rw [star_mul]
  have hright : Y * X = X * Y := hcomm.symm.eq
  have hstar : star Y * star X = star X * star Y := by
    have h := congrArg star hright
    simpa only [star_mul] using h.symm
  rw [hstar]
  simp only [mul_assoc]
  rw [hright]

noncomputable def jumpEulerStep (D : ChristensenEvansData A) (t : ℝ≥0) :
    A →CP A :=
  completelyPositiveMapAdd (completelyPositiveMapId A)
    (completelyPositiveMapRealSmul (t : ℝ) (by positivity) D.jump)

@[simp]
lemma jumpEulerStep_apply (D : ChristensenEvansData A) (t : ℝ≥0) (a : A) :
    D.jumpEulerStep t a = a + (t : ℂ) • D.jump a :=
  rfl

lemma jumpEulerStep_toContinuousLinearMap (D : ChristensenEvansData A) (t : ℝ≥0) :
    completelyPositiveMapToContinuousLinearMap (D.jumpEulerStep t) =
      (1 : A →L[ℂ] A) + (t : ℂ) • D.jumpMap := by
  ext a
  simp [jumpEulerStep, jumpMap]

noncomputable def eulerStep (D : ChristensenEvansData A) (t : ℝ≥0) (n : ℕ) :
    A →CP A :=
  completelyPositiveMapComp
    (D.noJumpEvolution (t / (n + 1)))
    (D.jumpEulerStep (t / (n + 1)))

noncomputable def eulerApproximation (D : ChristensenEvansData A) (t : ℝ≥0) (n : ℕ) :
    A →CP A :=
  cpPow (D.eulerStep t n) (n + 1)

lemma eulerApproximation_toContinuousLinearMap (D : ChristensenEvansData A)
    (t : ℝ≥0) (n : ℕ) :
    completelyPositiveMapToContinuousLinearMap (D.eulerApproximation t n) =
      (completelyPositiveMapToContinuousLinearMap (D.eulerStep t n)) ^ (n + 1) := by
  apply ContinuousLinearMap.ext
  intro a
  rw [completelyPositiveMap_toContinuousLinearMap_apply]
  change (cpPow (D.eulerStep t n) (n + 1)).toLinearMap a = _
  rw [cpPow_toLinearMap]
  let P := completelyPositiveMapToContinuousLinearMap (D.eulerStep t n)
  have hP : P.toLinearMap = (D.eulerStep t n).toLinearMap := by
    apply LinearMap.ext
    intro b
    rfl
  have hpow := ContinuousLinearMap.toLinearMap_pow P (n + 1)
  have hpowA := congrArg (fun f : A →ₗ[ℂ] A => f a) hpow
  change ((D.eulerStep t n).toLinearMap ^ (n + 1)) a = (P ^ (n + 1)) a
  rw [← hP]
  exact hpowA.symm

/-! ### Norm convergence of the CP Euler products -/

lemma eulerApproximation_tendsto (D : ChristensenEvansData A) [Nontrivial A]
    (t : ℝ≥0) :
    Tendsto
      (fun n => completelyPositiveMapToContinuousLinearMap (D.eulerApproximation t n))
      atTop (nhds (NormedSpace.exp ((t : ℝ) • D.generator))) := by
  let N : A := D.noJumpOperator
  let J : A →L[ℂ] A := D.jumpMap
  let M : A →L[ℂ] A := D.noJumpMap
  let c : ℝ := 2 * ‖N‖ + ‖J‖
  let a : ℝ → (A →L[ℂ] A) := fun s =>
    ContinuousLinearMap.mulLeftRight ℂ A
      (star (NormedSpace.exp (s • N))) (NormedSpace.exp (s • N))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have ha0 : a 0 = 1 := by
    ext X
    simp [a]
  have ha : HasDerivAt a M 0 := by
    have he : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • D.noJumpOperator))
        D.noJumpOperator 0 := by
      simpa using hasDerivAt_exp_smul_const D.noJumpOperator (0 : ℝ)
    have hstar : HasDerivAt (fun s : ℝ => star (NormedSpace.exp (s • D.noJumpOperator)))
        (star D.noJumpOperator) 0 := by
      simpa using he.star
    have hp := hstar.prodMk he
    let b : A × A → (A →L[ℂ] A) := fun p =>
      ContinuousLinearMap.mulLeftRight ℂ A p.1 p.2
    have hb : IsBoundedBilinearMap ℝ b := by
      refine { add_left := ?_, smul_left := ?_, add_right := ?_, smul_right := ?_, bound := ?_ }
      · intro u v w; simp [b]
      · intro r u v
        simp [b, Algebra.smul_def]
        ext z
        simp [ContinuousLinearMap.mulLeftRight_apply, ← Algebra.smul_def]
      · intro u v w; simp [b]
      · intro r u v
        simp [b, Algebra.smul_def]
        ext z
        simp [ContinuousLinearMap.mulLeftRight_apply, ← Algebra.smul_def]
      · refine ⟨1, one_pos, ?_⟩
        intro u v
        simpa [b] using
          (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℂ A u v)
    have hcomp := (hb.hasFDerivAt
      (star (NormedSpace.exp ((0 : ℝ) • D.noJumpOperator)),
        NormedSpace.exp ((0 : ℝ) • D.noJumpOperator))).comp 0 hp.hasFDerivAt
    have hd := hcomp.hasDerivAt
    have hfun : ((fun p => b p) ∘ fun s : ℝ =>
        (star (NormedSpace.exp (s • D.noJumpOperator)),
          NormedSpace.exp (s • D.noJumpOperator))) =
        (fun s : ℝ => b (star (NormedSpace.exp (s • D.noJumpOperator)),
          NormedSpace.exp (s • D.noJumpOperator))) := by
      rfl
    rw [hfun] at hd
    simpa [a, b, N, M, IsBoundedBilinearMap.deriv_apply,
      ContinuousLinearMap.mulLeftRight_apply, ChristensenEvansData.noJumpMap, add_comm] using hd
  have hqa : ∀ n : ℕ, ‖a ((t : ℝ) / (n + 1 : ℝ)) *
      (1 + (((t : ℝ) / (n + 1 : ℝ)) : ℝ) • J)‖ ≤
        Real.exp ((((t : ℝ) / (n + 1 : ℝ)) : ℝ) * c) := by
    intro n
    let h : ℝ := (t : ℝ) / (n + 1 : ℝ)
    have hh : 0 ≤ h := by dsimp [h]; positivity
    have hNnorm : ‖h • N‖ = h * ‖N‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    have he : ‖NormedSpace.exp (h • N)‖ ≤ Real.exp (h * ‖N‖) := by
      simpa [hNnorm] using norm_exp_le_exp_norm (h • N)
    have ha' : ‖a h‖ ≤ Real.exp (h * (2 * ‖N‖)) := by
      calc
        ‖a h‖ ≤ ‖star (NormedSpace.exp (h • N))‖ * ‖NormedSpace.exp (h • N)‖ := by
          simpa [a] using ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℂ A
            (star (NormedSpace.exp (h • N))) (NormedSpace.exp (h • N))
        _ = ‖NormedSpace.exp (h • N)‖ * ‖NormedSpace.exp (h • N)‖ := by rw [norm_star]
        _ ≤ Real.exp (h * ‖N‖) * Real.exp (h * ‖N‖) :=
          mul_le_mul he he (norm_nonneg _) (by positivity)
        _ = Real.exp (h * (2 * ‖N‖)) := by rw [← Real.exp_add]; congr 1 <;> ring
    have hlin : ‖(1 : A →L[ℂ] A) + h • J‖ ≤ 1 + h * ‖J‖ := by
      calc
        ‖(1 : A →L[ℂ] A) + h • J‖ ≤
            ‖(1 : A →L[ℂ] A)‖ + ‖h • J‖ := norm_add_le _ _
        _ = 1 + h * ‖J‖ := by rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    have hlinexp : 1 + h * ‖J‖ ≤ Real.exp (h * ‖J‖) := by
      simpa [add_comm] using Real.add_one_le_exp (h * ‖J‖)
    calc
      ‖a h * (1 + h • J)‖ ≤ ‖a h‖ * ‖(1 : A →L[ℂ] A) + h • J‖ := norm_mul_le _ _
      _ ≤ Real.exp (h * (2 * ‖N‖)) * (1 + h * ‖J‖) :=
        mul_le_mul ha' hlin (norm_nonneg _) (by positivity)
      _ ≤ Real.exp (h * (2 * ‖N‖)) * Real.exp (h * ‖J‖) :=
        mul_le_mul_of_nonneg_left hlinexp (by positivity)
      _ = Real.exp (h * c) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [c]
        ring
  have hr : ∀ n : ℕ, ‖(1 : A →L[ℂ] A) +
      (((t : ℝ) / (n + 1 : ℝ)) : ℝ) • (M + J)‖ ≤
        Real.exp ((((t : ℝ) / (n + 1 : ℝ)) : ℝ) * c) := by
    intro n
    let h : ℝ := (t : ℝ) / (n + 1 : ℝ)
    have hh : 0 ≤ h := by dsimp [h]; positivity
    have hnorm : ‖M + J‖ ≤ c := by
      dsimp [M, N]
      have hleft : ‖ContinuousLinearMap.mulLeftRight ℂ A
          (star D.noJumpOperator) 1‖ ≤ ‖D.noJumpOperator‖ := by
        exact (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℂ A
          (star D.noJumpOperator) (1 : A)).trans_eq (by rw [norm_star, norm_one, mul_one])
      have hright : ‖ContinuousLinearMap.mulLeftRight ℂ A
          1 D.noJumpOperator‖ ≤ ‖D.noJumpOperator‖ := by
        exact (ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℂ A
          (1 : A) D.noJumpOperator).trans_eq (by rw [norm_one, one_mul])
      have hM : ‖D.noJumpMap‖ ≤ 2 * ‖D.noJumpOperator‖ := by
        rw [ChristensenEvansData.noJumpMap]
        calc
          ‖ContinuousLinearMap.mulLeftRight ℂ A (star D.noJumpOperator) 1 +
              ContinuousLinearMap.mulLeftRight ℂ A 1 D.noJumpOperator‖ ≤
              ‖ContinuousLinearMap.mulLeftRight ℂ A (star D.noJumpOperator) 1‖ +
                ‖ContinuousLinearMap.mulLeftRight ℂ A 1 D.noJumpOperator‖ := norm_add_le _ _
          _ ≤ 2 * ‖D.noJumpOperator‖ := by
            calc
              _ ≤ ‖D.noJumpOperator‖ + ‖D.noJumpOperator‖ := add_le_add hleft hright
              _ = 2 * ‖D.noJumpOperator‖ := by ring
      calc
        ‖M + J‖ ≤ ‖M‖ + ‖J‖ := norm_add_le _ _
        _ ≤ 2 * ‖D.noJumpOperator‖ + ‖J‖ := add_le_add hM le_rfl
        _ = c := by rfl
    have hlin : ‖(1 : A →L[ℂ] A) + h • (M + J)‖ ≤ 1 + h * c := by
      calc
        ‖(1 : A →L[ℂ] A) + h • (M + J)‖ ≤
            ‖(1 : A →L[ℂ] A)‖ + ‖h • (M + J)‖ := norm_add_le _ _
        _ ≤ 1 + h * c := by
          rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
          simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hnorm hh) 1
    calc
      ‖(1 : A →L[ℂ] A) + h • (M + J)‖ ≤ 1 + h * c := hlin
      _ ≤ Real.exp (h * c) := by simpa [add_comm] using Real.add_one_le_exp (h * c)
  have hprod := lie_product_formula_of_step a M J c (t : ℝ) (by positivity) hc ha0 ha hqa hr
  change Tendsto (fun n => completelyPositiveMapToContinuousLinearMap (D.eulerApproximation t n))
      atTop (nhds (NormedSpace.exp ((t : ℝ) • D.generator)))
  rw [D.generator_eq_noJumpMap_add_jumpMap]
  convert hprod using 1
  · funext n
    rw [D.eulerApproximation_toContinuousLinearMap]
    change (completelyPositiveMapToContinuousLinearMap (D.eulerStep t n)) ^ (n + 1) = _
    rw [eulerStep, completelyPositiveMap_comp_toContinuousLinearMap_self,
      jumpEulerStep_toContinuousLinearMap]
    simp [a, M, N, ChristensenEvansData.noJumpOperator,
      ChristensenEvansData.noJumpEvolution,
      completelyPositiveMap_conjugation_toContinuousLinearMap]
    congr 2
    congr 1
    convert (RCLike.real_smul_eq_coe_smul (K := ℂ)
        ((↑t : ℝ) / (↑n + 1)) D.jumpMap).symm using 1 <;> norm_num

/-! ## The UCP evolution generated by the data -/

section Evolution

/-- The real-time Banach-space exponential generated by Christensen–Evans data. -/
noncomputable def realEvolution (D : ChristensenEvansData A) (t : ℝ) : A →L[ℂ] A :=
  NormedSpace.exp (t • D.generator)

@[simp]
lemma realEvolution_zero (D : ChristensenEvansData A) :
    D.realEvolution 0 = (1 : A →L[ℂ] A) := by
  rw [realEvolution, zero_smul ℝ D.generator, NormedSpace.exp_zero]

lemma realEvolution_add (D : ChristensenEvansData A) (s t : ℝ) :
    D.realEvolution (s + t) = D.realEvolution s * D.realEvolution t := by
  change NormedSpace.exp (((s + t : ℝ) : ℂ) • D.generator) =
    NormedSpace.exp ((s • D.generator)) * NormedSpace.exp ((t • D.generator))
  have hscalar : (((s + t : ℝ) : ℂ) • D.generator) =
      (s • D.generator) + (t • D.generator) := by
    calc
      (((s + t : ℝ) : ℂ) • D.generator) = (s + t) • D.generator :=
        (RCLike.real_smul_eq_coe_smul (K := ℂ) (s + t) D.generator).symm
      _ = (s • D.generator) + (t • D.generator) := add_smul s t D.generator
  rw [hscalar]
  apply NormedSpace.exp_add_of_commute
  rw [commute_iff_eq]
  ext a
  simp [ContinuousLinearMap.mul_def, ContinuousLinearMap.smul_comp, smul_smul, mul_comm]

@[simp]
lemma realEvolution_apply_one (D : ChristensenEvansData A) (t : ℝ) :
    D.realEvolution t 1 = 1 := by
  exact BoundedQuantumDynamicalSemigroup.exp_apply_of_apply_eq_zero
    D.generator 1 D.generator_apply_one t

lemma realEvolution_continuous (D : ChristensenEvansData A) :
    Continuous D.realEvolution := by
  change Continuous (fun t : ℝ => NormedSpace.exp (t • D.generator))
  apply NormedSpace.exp_continuous.comp
  fun_prop

lemma realEvolution_eq_complex (D : ChristensenEvansData A) (t : ℝ) :
    D.realEvolution t = NormedSpace.exp ((t : ℂ) • D.generator) := by
  change NormedSpace.exp (t • D.generator) = NormedSpace.exp ((t : ℂ) • D.generator)
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) t D.generator]
  rfl

lemma eulerApproximation_tendsto_nonnegative
    (D : ChristensenEvansData A) [Nontrivial A] (t : ℝ≥0) :
    Tendsto
      (fun n => completelyPositiveMapToContinuousLinearMap (D.eulerApproximation t n))
      atTop (nhds (D.realEvolution (t : ℝ))) := by
  exact D.eulerApproximation_tendsto t

/-- A norm-convergent CP Euler product yields a channel because the exponential fixes `1`. -/
@[nolint unusedArguments]
noncomputable def channelOfEulerLimit
    (D : ChristensenEvansData A) [Nontrivial A] (t : ℝ≥0)
    (hlim : Tendsto
      (fun n => completelyPositiveMapToContinuousLinearMap (D.eulerApproximation t n))
      atTop (nhds (D.realEvolution (t : ℝ)))) : Channel A A := by
  let Φ : A →CP A := completelyPositiveMapOfTendstoBundled
    (fun n => D.eulerApproximation t n) (D.realEvolution (t : ℝ)) hlim
  refine ⟨Φ, ?_⟩
  change D.realEvolution (t : ℝ) 1 = 1
  exact D.realEvolution_apply_one (t : ℝ)

/-- The UCP semigroup obtained from norm-convergent Christensen–Evans Euler products. -/
noncomputable def quantumDynamicalSemigroupOfEulerLimit
    (D : ChristensenEvansData A) [Nontrivial A]
    (hlim : ∀ t : ℝ≥0,
      Tendsto
        (fun n => completelyPositiveMapToContinuousLinearMap (D.eulerApproximation t n))
        atTop (nhds (D.realEvolution (t : ℝ)))) :
    QuantumDynamicalSemigroup A where
  map := fun t => D.channelOfEulerLimit t (hlim t)
  map_zero := by
    intro a
    change D.realEvolution 0 a = a
    rw [D.realEvolution_zero]
    rfl
  map_add := by
    intro s t a
    change D.realEvolution ((s + t : ℝ≥0) : ℝ) a =
      D.realEvolution (s : ℝ) (D.realEvolution (t : ℝ) a)
    rw [NNReal.coe_add, D.realEvolution_add]
    rfl
  continuous := by
    intro a
    change Continuous (fun t : ℝ≥0 => D.realEvolution (t : ℝ) a)
    apply Continuous.clm_apply
    · exact D.realEvolution_continuous.comp continuous_subtype_val
    · fun_prop

/-- A Christensen–Evans realization with its norm-convergent product formula is a bounded
quantum dynamical semigroup with the displayed generator. -/
noncomputable def boundedQuantumDynamicalSemigroupOfEulerLimit
    (D : ChristensenEvansData A) [Nontrivial A]
    (hlim : ∀ t : ℝ≥0,
      Tendsto
        (fun n => completelyPositiveMapToContinuousLinearMap (D.eulerApproximation t n))
        atTop (nhds (D.realEvolution (t : ℝ)))) :
    BoundedQuantumDynamicalSemigroup A where
  toQuantumDynamicalSemigroup := D.quantumDynamicalSemigroupOfEulerLimit hlim
  generator := D.generator
  map_eq_exp := by
    intro t a
    change D.realEvolution (t : ℝ) a = NormedSpace.exp ((t : ℂ) • D.generator) a
    rw [D.realEvolution_eq_complex]

end Evolution

/-- The canonical UCP semigroup generated by Christensen–Evans data. -/
noncomputable def quantumDynamicalSemigroup [Nontrivial A]
    (D : ChristensenEvansData A) : QuantumDynamicalSemigroup A :=
  D.quantumDynamicalSemigroupOfEulerLimit
    (fun t => D.eulerApproximation_tendsto_nonnegative t)

/-- The canonical bounded semigroup realization of Christensen–Evans data. -/
noncomputable def boundedQuantumDynamicalSemigroup [Nontrivial A]
    (D : ChristensenEvansData A) : BoundedQuantumDynamicalSemigroup A :=
  D.boundedQuantumDynamicalSemigroupOfEulerLimit
    (fun t => D.eulerApproximation_tendsto_nonnegative t)

end ChristensenEvansData

/-! ## The converse boundary

The construction above proves the forward direction for arbitrary C⋆-algebras: Christensen–Evans
data produce a norm-continuous UCP semigroup.  The representation-free converse remains an
abstract question for a general C⋆-algebra.  For `B(H)`, however, the companion
`Stinespring.lean` file constructs the positive-kernel completion, the CP compression, and the
full converse theorem `QuantumDynamicalSemigroup.generator_isChristensenEvans`.
-/

/-- A bounded generator admits a representation-independent Christensen–Evans decomposition. -/
def IsChristensenEvansGenerator (L : A →L[ℂ] A) : Prop :=
  ∃ D : ChristensenEvansData A, D.generator = L

lemma ChristensenEvansData.isChristensenEvansGenerator
    (D : ChristensenEvansData A) :
  IsChristensenEvansGenerator D.generator :=
  ⟨D, rfl⟩

/-! ### The positive-shift reduction

One standard route to the converse is to first produce a completely positive map `J` with
`J = L + r id` for some `r ≥ 0`.  The scalar part then cancels against the normalization term in
the Christensen--Evans formula.  This reduction is elementary and independent of how the
positive shift is eventually constructed (for example by a kernel-extension argument). -/

/-- A bounded map admits a completely positive positive shift.

The definition uses the continuous linear realization of the bundled CP map, so it is directly
compatible with the bounded-generator API.  It deliberately records the shift as nonnegative
real scalar data; no choice of Kraus or Stinespring representation is involved. -/
def HasCompletelyPositiveShift (L : A →L[ℂ] A) : Prop :=
  ∃ r : ℝ≥0, ∃ J : A →CP A,
    completelyPositiveMapToContinuousLinearMap J =
      L + (r : ℂ) • (1 : A →L[ℂ] A)

/-- The bounded Hamiltonian commutator associated with an observable. -/
noncomputable def hamiltonianPartOf (H : Observable A) : A →L[ℂ] A :=
  Complex.I •
    (ContinuousLinearMap.mulLeftRight ℂ A (H : A) 1 -
      ContinuousLinearMap.mulLeftRight ℂ A 1 (H : A))

@[simp]
lemma hamiltonianPartOf_apply (H : Observable A) (a : A) :
    hamiltonianPartOf H a =
      Complex.I • ((H : A) * a - a * (H : A)) := by
  simp [hamiltonianPartOf, ContinuousLinearMap.mulLeftRight_apply, sub_eq_add_neg]

lemma hamiltonianPartOf_apply_one (H : Observable A) :
    hamiltonianPartOf H 1 = 0 := by
  simp [hamiltonianPartOf]

/-- A bounded map admits a completely positive shift after removal of a bounded Hamiltonian
commutator.  This is the exact algebraic shape needed for the full Lindblad converse. -/
def HasHamiltonianCompletelyPositiveShift (L : A →L[ℂ] A) : Prop :=
  ∃ H : Observable A, ∃ r : ℝ≥0, ∃ J : A →CP A,
    completelyPositiveMapToContinuousLinearMap J =
      L - hamiltonianPartOf H + (r : ℂ) • (1 : A →L[ℂ] A)

lemma isChristensenEvansGenerator_of_completelyPositiveShift
    (L : A →L[ℂ] A) (hL1 : L 1 = 0)
    (hshift : HasCompletelyPositiveShift L) :
    IsChristensenEvansGenerator L := by
  obtain ⟨r, J, hJ⟩ := hshift
  let H : Observable A := ⟨0, by simp⟩
  let D : ChristensenEvansData A := { hamiltonian := H, jump := J }
  have hJa (a : A) : J a = L a + (r : ℂ) • a := by
    have h := congrArg (fun K : A →L[ℂ] A => K a) hJ
    simpa [completelyPositiveMap_toContinuousLinearMap_apply] using h
  have hJ1 : J 1 = (r : ℂ) • (1 : A) := by
    have h := hJa (1 : A)
    simpa [hL1] using h
  refine ⟨D, ?_⟩
  apply ContinuousLinearMap.ext
  intro a
  rw [ChristensenEvansData.generator_apply]
  have hH : (H : A) = 0 := rfl
  have hJ1_left (x : A) : J 1 * x = (r : ℂ) • x := by
    rw [hJ1]
    simp [smul_mul_assoc]
  have hJ1_right (x : A) : x * J 1 = (r : ℂ) • x := by
    rw [hJ1]
    simp [mul_smul_comm]
  rw [hH, hJa, hJ1_left, hJ1_right]
  simp only [zero_mul, mul_zero, sub_zero, zero_smul, add_zero, one_mul, mul_one]
  module

lemma isChristensenEvansGenerator_of_hamiltonianShift
    (L : A →L[ℂ] A) (hL1 : L 1 = 0)
    (hshift : HasHamiltonianCompletelyPositiveShift L) :
    IsChristensenEvansGenerator L := by
  obtain ⟨H, r, J, hJ⟩ := hshift
  let D : ChristensenEvansData A := { hamiltonian := H, jump := J }
  have hJa (a : A) : J a = L a - hamiltonianPartOf H a + (r : ℂ) • a := by
    have h := congrArg (fun K : A →L[ℂ] A => K a) hJ
    simpa [completelyPositiveMap_toContinuousLinearMap_apply] using h
  have hJ1 : J 1 = (r : ℂ) • (1 : A) := by
    have h := hJa (1 : A)
    simpa [hL1] using h
  refine ⟨D, ?_⟩
  apply ContinuousLinearMap.ext
  intro a
  rw [ChristensenEvansData.generator_apply]
  dsimp [D]
  rw [← hamiltonianPartOf_apply H a]
  have hJ1_left (x : A) : J 1 * x = (r : ℂ) • x := by
    rw [hJ1]
    simp [smul_mul_assoc]
  have hJ1_right (x : A) : x * J 1 = (r : ℂ) • x := by
    rw [hJ1]
    simp [mul_smul_comm]
  rw [hJa, hJ1_left, hJ1_right]
  simp only [sub_eq_add_neg, zero_mul, mul_zero, sub_zero, zero_smul, add_zero,
    one_mul, mul_one]
  module

/-! ### Conditional complete positivity

For a general C⋆-algebra it is useful to state conditional positivity through finite matrix
compressions.  If `X C = 0`, then `Xᴴ X` is a positive matrix and the correction terms in a
Christensen–Evans generator disappear after compression by `C`.  Testing the compressed element
against all positive linear functionals avoids choosing a Hilbert-space representation at this
stage.
-/

/-- Matrix-compression form of conditional complete positivity for a bounded map.

The square-matrix formulation is equivalent to the usual finite-column formulation by adjoining
zero rows and columns.  It is chosen here because it works directly with Mathlib's C⋆-matrix
positivity API and is representation-independent. -/
def IsConditionallyCompletelyPositiveBounded (L : A →L[ℂ] A) : Prop :=
  ∀ (n : ℕ) (X C : CStarMatrix (Fin n) (Fin n) A),
    X * C = 0 →
      ∀ f : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ,
        0 ≤ Complex.re (f (CStarMatrix.conjTranspose C *
          ((CStarMatrix.conjTranspose X * X).map L) * C))

/-! ### The Evans--Lewis kernel

The conditional-positivity statement is often written using the associated carré-du-champ
kernel.  Keeping this expression explicit is useful for the converse theorem: on `B(H)`, the
positive-kernel factorisation and the resulting completely positive jump map are constructed in
`Stinespring.lean`.
-/

/-- The (un-normalised) Evans--Lewis kernel of a bounded map.

For a unital generator the last term vanishes.  It is retained in the definition because this is
the expression invariant under the usual affine change of a generator and because it makes the
kernel formula valid before imposing `L 1 = 0`. -/
noncomputable def evansLewisKernel (L : A →L[ℂ] A) (a b : A) : A :=
  L (star a * b) - L (star a) * b - star a * L b + star a * L 1 * b

@[simp]
lemma evansLewisKernel_apply_one_left (L : A →L[ℂ] A) (b : A) :
    evansLewisKernel L 1 b = 0 := by
  simp only [evansLewisKernel, star_one, one_mul]
  noncomm_ring

@[simp]
lemma evansLewisKernel_apply_one_right (L : A →L[ℂ] A) (a : A) :
    evansLewisKernel L a 1 = 0 := by
  simp [evansLewisKernel]

/-- A derivation has zero Evans--Lewis kernel. -/
lemma evansLewisKernel_eq_zero_of_leibniz
    (L : A →L[ℂ] A)
    (hL : ∀ a b : A, L (a * b) = L a * b + a * L b) :
    (h1 : L 1 = 0) → ∀ a b : A, evansLewisKernel L a b = 0 := by
  intro h1
  intro a b
  rw [evansLewisKernel, hL]
  simp [h1]

/-- Conversely, a normalized map with vanishing Evans--Lewis kernel is a derivation. -/
lemma leibniz_of_evansLewisKernel_eq_zero
    (L : A →L[ℂ] A) (h1 : L 1 = 0)
    (hK : ∀ a b : A, evansLewisKernel L a b = 0) :
    ∀ a b : A, L (a * b) = L a * b + a * L b := by
  intro a b
  have h := hK (star a) b
  rw [evansLewisKernel, h1] at h
  simp only [star_star, zero_mul, mul_zero, add_zero] at h
  apply sub_eq_zero.mp
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

/-- Star preservation makes the Evans--Lewis kernel Hermitian in its two arguments. -/
lemma evansLewisKernel_star
    (L : A →L[ℂ] A)
    (hL : ∀ a : A, star (L a) = L (star a)) (a b : A) :
    star (evansLewisKernel L a b) = evansLewisKernel L b a := by
  rw [evansLewisKernel, evansLewisKernel]
  simp only [star_add, star_sub, star_mul, star_star, star_one]
  rw [hL, hL, hL, hL]
  simp only [star_mul, star_star, star_one]
  noncomm_ring

/-- The representation-free infinitesimal data of a bounded Heisenberg quantum Markov generator.

The three fields are exactly what survives differentiation of a norm-continuous UCP semigroup:
unitality, star preservation, and conditional complete positivity.  A Christensen–Evans witness
is stronger data and is deliberately kept separate from this interface. -/
structure BoundedQuantumMarkovGenerator (A : Type*) [OperatorAlgebra A] where
  /-- The bounded infinitesimal map. -/
  map : A →L[ℂ] A
  /-- Infinitesimal unitality. -/
  map_one : map 1 = 0
  /-- Preservation of the star operation. -/
  map_star : ∀ a, star (map a) = map (star a)
  /-- Conditional complete positivity on the matrix nullspace. -/
  isConditionallyCompletelyPositive : IsConditionallyCompletelyPositiveBounded map

namespace BoundedQuantumMarkovGenerator

variable (G : BoundedQuantumMarkovGenerator A)

@[simp]
lemma map_one_apply : G.map 1 = 0 :=
  G.map_one

lemma isHermitianPreserving :
    ∀ ⦃a : A⦄, IsSelfAdjoint a → IsSelfAdjoint (G.map a) := by
  intro a ha
  rw [isSelfAdjoint_iff]
  rw [G.map_star, ha.star_eq]

end BoundedQuantumMarkovGenerator

namespace ChristensenEvansData

variable (D : ChristensenEvansData A)

lemma matrix_map_noJump_compression_zero
    (n : ℕ) (X C : CStarMatrix (Fin n) (Fin n) A)
    (hXC : X * C = 0) :
    CStarMatrix.conjTranspose C *
      ((CStarMatrix.conjTranspose X * X).map D.noJumpMap) * C = 0 := by
  let M : CStarMatrix (Fin n) (Fin n) A := CStarMatrix.conjTranspose X * X
  let K₁ : CStarMatrix (Fin n) (Fin n) A := CStarMatrix.ofMatrix (Matrix.diagonal
    (fun _ => star D.noJumpOperator))
  let K₂ : CStarMatrix (Fin n) (Fin n) A := CStarMatrix.ofMatrix (Matrix.diagonal
    (fun _ => D.noJumpOperator))
  have hdiag_left (k : A) (N : CStarMatrix (Fin n) (Fin n) A) :
      CStarMatrix.ofMatrix (Matrix.diagonal (fun _ => k)) * N =
        CStarMatrix.ofMatrix (fun i j => k * N i j) := by
    ext i j
    change (∑ q, (if i = q then k else 0) * N q j) = k * N i j
    simp
  have hdiag_right (k : A) (N : CStarMatrix (Fin n) (Fin n) A) :
      N * CStarMatrix.ofMatrix (Matrix.diagonal (fun _ => k)) =
        CStarMatrix.ofMatrix (fun i j => N i j * k) := by
    ext i j
    change (∑ q, N i q * (if q = j then k else 0)) = N i j * k
    simp
  have hmap : M.map D.noJumpMap = K₁ * M + M * K₂ := by
    rw [show K₁ = CStarMatrix.ofMatrix (Matrix.diagonal
        (fun _ => star D.noJumpOperator)) by rfl,
      show K₂ = CStarMatrix.ofMatrix (Matrix.diagonal
        (fun _ => D.noJumpOperator)) by rfl,
      hdiag_left, hdiag_right]
    ext i j
    change D.noJumpMap (M i j) =
      star D.noJumpOperator * M i j + M i j * D.noJumpOperator
    rw [D.noJumpMap_apply]
  have hright : M * C = 0 := by
    change (CStarMatrix.conjTranspose X * X) * C = 0
    rw [mul_assoc, hXC, mul_zero]
  have hleft : CStarMatrix.conjTranspose C * M = 0 := by
    have hstar : CStarMatrix.conjTranspose C * CStarMatrix.conjTranspose X = 0 := by
      apply CStarMatrix.ext
      intro i j
      have h := congrArg (fun Z => star (Z j i)) hXC
      simpa [CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply,
        Matrix.mul_apply, star_sum, star_mul] using h
    change CStarMatrix.conjTranspose C *
      (CStarMatrix.conjTranspose X * X) = 0
    rw [← mul_assoc, hstar, zero_mul]
  calc
    CStarMatrix.conjTranspose C * (M.map D.noJumpMap) * C =
        CStarMatrix.conjTranspose C * (K₁ * M + M * K₂) * C := by rw [hmap]
    _ = CStarMatrix.conjTranspose C * K₁ * (M * C) +
        (CStarMatrix.conjTranspose C * M) * (K₂ * C) := by
      rw [mul_add, add_mul]
      simp only [mul_assoc]
    _ = 0 := by
      rw [hright, hleft, mul_zero, zero_mul, zero_add]

lemma generator_isConditionallyCompletelyPositive :
    IsConditionallyCompletelyPositiveBounded D.generator := by
  intro n X C hXC f
  let M : CStarMatrix (Fin n) (Fin n) A := CStarMatrix.conjTranspose X * X
  have hM : 0 ≤ M := by
    change 0 ≤ CStarMatrix.conjTranspose X * X
    rw [← CStarMatrix.star_eq_conjTranspose]
    exact star_mul_self_nonneg X
  have hJ : 0 ≤ M.map D.jump := D.jump.map_cstarMatrix_nonneg M hM
  have hcompressed : 0 ≤ CStarMatrix.conjTranspose C * (M.map D.jump) * C :=
    star_left_conjugate_nonneg hJ C
  have hf : 0 ≤ f (CStarMatrix.conjTranspose C * (M.map D.jump) * C) :=
    f.map_nonneg hcompressed
  have hgenerator : M.map D.generator = M.map D.jump + M.map D.noJumpMap := by
    rw [D.generator_eq_noJumpMap_add_jumpMap]
    ext i j
    change (D.noJumpMap + D.jumpMap) (M i j) =
      D.jump (M i j) + D.noJumpMap (M i j)
    simp [add_comm]
  have hzero : CStarMatrix.conjTranspose C * (M.map D.noJumpMap) * C = 0 := by
    exact D.matrix_map_noJump_compression_zero n X C hXC
  have hEq : CStarMatrix.conjTranspose C * (M.map D.generator) * C =
      CStarMatrix.conjTranspose C * (M.map D.jump) * C := by
    rw [hgenerator]
    calc
      CStarMatrix.conjTranspose C *
          (M.map D.jump + M.map D.noJumpMap) * C =
          (CStarMatrix.conjTranspose C * M.map D.jump) * C +
          (CStarMatrix.conjTranspose C * M.map D.noJumpMap) * C := by
              rw [mul_add, add_mul]
      _ = CStarMatrix.conjTranspose C * (M.map D.jump) * C := by
        rw [hzero, add_zero]
  rw [hEq]
  exact (RCLike.nonneg_iff.mp hf).1

/-- Christensen–Evans data package directly into the representation-free Markov-generator API. -/
noncomputable def toBoundedQuantumMarkovGenerator : BoundedQuantumMarkovGenerator A where
  map := D.generator
  map_one := D.generator_apply_one
  map_star := D.generator_star
  isConditionallyCompletelyPositive := D.generator_isConditionallyCompletelyPositive

end ChristensenEvansData

namespace BoundedQuantumDynamicalSemigroup

variable {A : Type*} [OperatorAlgebra A]

/-- A semigroup whose bounded generator has a Christensen–Evans witness has the corresponding
canonical CP/UCP realization.  This is the precise abstract converse interface: the hard
infinite-dimensional theorem is isolated in the hypothesis
`IsChristensenEvansGenerator Φ.generator`. -/
lemma map_eq_christensenEvans_of_isChristensenEvansGenerator
    [Nontrivial A] (Φ : BoundedQuantumDynamicalSemigroup A)
    (hΦ : IsChristensenEvansGenerator Φ.generator) :
    ∃ D : ChristensenEvansData A, ∀ (t : ℝ≥0) (a : A),
      Φ.toQuantumDynamicalSemigroup.map t a =
        D.boundedQuantumDynamicalSemigroup.toQuantumDynamicalSemigroup.map t a := by
  obtain ⟨D, hD⟩ := hΦ
  refine ⟨D, ?_⟩
  intro t a
  rw [Φ.map_eq_exp, D.boundedQuantumDynamicalSemigroup.map_eq_exp]
  change (NormedSpace.exp ((t : ℂ) • Φ.generator)) a =
    (NormedSpace.exp ((t : ℂ) • D.generator)) a
  rw [hD]

/-- Exact semigroup-level characterization of the Christensen–Evans interface.

For a bounded semigroup, saying that its generator has a Christensen–Evans decomposition is
equivalent to saying that the semigroup agrees with the canonical CE semigroup generated by that
datum.  The nontrivial existence question is therefore isolated entirely in the implication from
the UCP semigroup hypotheses to `IsChristensenEvansGenerator Φ.generator`. -/
lemma isChristensenEvansGenerator_iff_exists_matching_semigroup
    [Nontrivial A] (Φ : BoundedQuantumDynamicalSemigroup A) :
    IsChristensenEvansGenerator Φ.generator ↔
      ∃ D : ChristensenEvansData A, ∀ (t : ℝ≥0) (a : A),
        Φ.toQuantumDynamicalSemigroup.map t a =
          D.boundedQuantumDynamicalSemigroup.toQuantumDynamicalSemigroup.map t a := by
  constructor
  · exact Φ.map_eq_christensenEvans_of_isChristensenEvansGenerator
  · rintro ⟨D, hD⟩
    unfold IsChristensenEvansGenerator
    refine ⟨D, ?_⟩
    apply Φ.generator_eq_of_hasDerivWithinAt D.generator
    intro a
    have hD' := D.boundedQuantumDynamicalSemigroup.hasDerivWithinAt_generator a
    apply hD'.congr
    · intro t ht
      have ht' := hD (BoundedQuantumDynamicalSemigroup.nonnegativeTime t) a
      rw [ht']
    · have hn : BoundedQuantumDynamicalSemigroup.nonnegativeTime (0 : ℝ) =
          (0 : ℝ≥0) := by
        apply Subtype.ext
        simp [BoundedQuantumDynamicalSemigroup.nonnegativeTime]
      rw [hn]
      exact hD 0 a

/-- A bounded semigroup with a completely-positive generator shift has a
Christensen--Evans generator.  The only input not already forced by the UCP semigroup axioms is
the positive-shift certificate itself. -/
lemma isChristensenEvansGenerator_of_hasCompletelyPositiveShift
    (Φ : BoundedQuantumDynamicalSemigroup A)
    (hshift : HasCompletelyPositiveShift Φ.generator) :
    IsChristensenEvansGenerator Φ.generator := by
  exact isChristensenEvansGenerator_of_completelyPositiveShift
    Φ.generator Φ.generator_isUnital hshift

/-- The full semigroup-facing form of the Hamiltonian-adjusted positive-shift reduction. -/
lemma isChristensenEvansGenerator_of_hamiltonianShift
    (Φ : BoundedQuantumDynamicalSemigroup A)
    (hshift : HasHamiltonianCompletelyPositiveShift Φ.generator) :
    IsChristensenEvansGenerator Φ.generator := by
  exact OperatorAlgebra.isChristensenEvansGenerator_of_hamiltonianShift
    Φ.generator Φ.generator_isUnital hshift

end BoundedQuantumDynamicalSemigroup

namespace QuantumDynamicalSemigroup.HasBoundedGenerator

variable {Φ : QuantumDynamicalSemigroup A}

/-- A bounded generator of a unital completely positive semigroup annihilates the unit.

This is the abstract infinitesimal unitality condition.  It is independent of a matrix or
Hilbert-space representation and is the first hypothesis in every Evans–Lewis/GKSL converse. -/
lemma generator_apply_one (G : HasBoundedGenerator Φ) :
    G.generator 1 = 0 := by
  have hmap : ∀ t : ℝ, Φ.map (BoundedQuantumDynamicalSemigroup.nonnegativeTime t) 1 = 1 := by
    intro t
    exact (Φ.map (BoundedQuantumDynamicalSemigroup.nonnegativeTime t)).property
  have hzero := G.has_deriv 1
  have hconst : HasDerivWithinAt (fun _ : ℝ => (1 : A)) 0 (Set.Ici 0) 0 :=
    hasDerivWithinAt_const (𝕜 := ℝ) (c := (1 : A)) (x := (0 : ℝ)) (s := Set.Ici 0)
  have hcongr := hzero.congr
    (fun t ht => (hmap t).symm)
    (hmap 0).symm
  have heq := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq
    hcongr.hasFDerivWithinAt hconst.hasFDerivWithinAt
  have heq' := congrArg (fun f => f (1 : ℝ)) heq
  simpa [ContinuousLinearMap.toSpanSingleton_apply_one] using heq'

/-- A bounded generator of a completely positive semigroup preserves the star operation.

Complete positivity gives star preservation at every time; differentiating that identity gives
the corresponding infinitesimal statement. -/
lemma generator_map_star (G : HasBoundedGenerator Φ) (a : A) :
    star (G.generator a) = G.generator (star a) := by
  have hstar := (G.has_deriv a).hasFDerivWithinAt.star
  have hstar' : HasFDerivWithinAt
      (fun t : ℝ => Φ.map
        (BoundedQuantumDynamicalSemigroup.nonnegativeTime t) (star a))
      ((starL' ℝ : A ≃L[ℝ] A).toContinuousLinearMap ∘L
        ContinuousLinearMap.toSpanSingleton ℝ (G.generator a))
      (Set.Ici 0) 0 := hstar.congr
    (fun t ht => by
      exact (completelyPositiveMap_map_star (Φ.map
        (BoundedQuantumDynamicalSemigroup.nonnegativeTime t)).1 a).symm)
    (by
      exact (completelyPositiveMap_map_star (Φ.map
        (BoundedQuantumDynamicalSemigroup.nonnegativeTime 0)).1 a).symm)
  have heq := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq
    hstar' (G.has_deriv (star a)).hasFDerivWithinAt
  have heq' := congrArg (fun f => f (1 : ℝ)) heq
  simpa [ContinuousLinearMap.toSpanSingleton_apply_one] using heq'

lemma hasDerivWithinAt_matrix_map
    (G : HasBoundedGenerator Φ) (n : ℕ) (M : CStarMatrix (Fin n) (Fin n) A) :
    HasDerivWithinAt
      (fun t : ℝ => M.map (Φ.map
        (BoundedQuantumDynamicalSemigroup.nonnegativeTime t)))
      (M.map G.generator) (Set.Ici 0) 0 := by
  apply hasDerivWithinAt_pi.2
  intro i
  apply hasDerivWithinAt_pi.2
  intro j
  change HasDerivWithinAt
    (fun t : ℝ => Φ.map
      (BoundedQuantumDynamicalSemigroup.nonnegativeTime t) (M i j))
    (G.generator (M i j)) (Set.Ici 0) 0
  exact G.has_deriv (M i j)

noncomputable def positiveLinearMapToContinuousLinearMap
    {B C : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
      [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (f : B →ₚ[ℂ] C) : B →L[ℝ] C := by
  classical
  let c : ℝ≥0 := Classical.choose (PositiveLinearMap.exists_norm_apply_le f)
  have hc : ∀ b : B, ‖f b‖ ≤ (c : ℝ) * ‖b‖ := by
    simpa [c] using Classical.choose_spec (PositiveLinearMap.exists_norm_apply_le f)
  exact (f.toLinearMap.restrictScalars ℝ).mkContinuousOfExistsBound
    ⟨(c : ℝ), by
      intro b
      simpa using hc b⟩

lemma positiveLinearMap_toContinuousLinearMap_apply
    {B C : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
      [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    (f : B →ₚ[ℂ] C) (b : B) :
    positiveLinearMapToContinuousLinearMap f b = f b := by
  simp [positiveLinearMapToContinuousLinearMap,
    LinearMap.mkContinuousOfExistsBound_apply]

/-- Every bounded generator of a norm-continuous UCP semigroup is conditionally completely
positive in the matrix-compression sense used above. -/
lemma generator_isConditionallyCompletelyPositive
    (G : HasBoundedGenerator Φ) :
    IsConditionallyCompletelyPositiveBounded G.generator := by
  intro n X C hXC f
  let M : CStarMatrix (Fin n) (Fin n) A := CStarMatrix.conjTranspose X * X
  let q : ℝ → CStarMatrix (Fin n) (Fin n) A := fun t =>
    CStarMatrix.conjTranspose C *
      (M.map (Φ.map (BoundedQuantumDynamicalSemigroup.nonnegativeTime t))) * C
  let q' : CStarMatrix (Fin n) (Fin n) A :=
    CStarMatrix.conjTranspose C * (M.map G.generator) * C
  have hM : 0 ≤ M := by
    change 0 ≤ CStarMatrix.conjTranspose X * X
    rw [← CStarMatrix.star_eq_conjTranspose]
    exact star_mul_self_nonneg X
  have hright : M * C = 0 := by
    change (CStarMatrix.conjTranspose X * X) * C = 0
    rw [mul_assoc, hXC, mul_zero]
  have hleft : CStarMatrix.conjTranspose C * M = 0 := by
    have hstar : CStarMatrix.conjTranspose C * CStarMatrix.conjTranspose X = 0 := by
      apply CStarMatrix.ext
      intro i j
      have h := congrArg (fun Z => star (Z j i)) hXC
      simpa [CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply,
        Matrix.mul_apply, star_sum, star_mul] using h
    change CStarMatrix.conjTranspose C *
      (CStarMatrix.conjTranspose X * X) = 0
    rw [← mul_assoc, hstar, zero_mul]
  have hq_zero : q 0 = 0 := by
    apply CStarMatrix.ext
    intro i j
    change (CStarMatrix.conjTranspose C *
      (M.map (Φ.map (BoundedQuantumDynamicalSemigroup.nonnegativeTime 0))) * C) i j = 0
    have ht : BoundedQuantumDynamicalSemigroup.nonnegativeTime 0 = 0 := by
      apply Subtype.ext
      simp [BoundedQuantumDynamicalSemigroup.nonnegativeTime]
    have hmap0 : M.map (Φ.map 0) = M := by
      apply CStarMatrix.ext
      intro i j
      change Φ.map 0 (M i j) = M i j
      exact Φ.map_zero (M i j)
    rw [ht, hmap0]
    change (CStarMatrix.conjTranspose C * M * C) i j = 0
    rw [hleft, zero_mul]
    simp
  have hq : HasDerivWithinAt q q' (Set.Ici 0) 0 := by
    have hMcurve := hasDerivWithinAt_matrix_map G n M
    have hleft' := HasDerivWithinAt.const_mul
      (CStarMatrix.conjTranspose C) hMcurve
    have hright' := hleft'.mul_const C
    exact hright'
  let fCLM : CStarMatrix (Fin n) (Fin n) A →L[ℝ] ℂ :=
    positiveLinearMapToContinuousLinearMap
      (B := CStarMatrix (Fin n) (Fin n) A) (C := ℂ) f
  have hfq : HasDerivWithinAt (fun t : ℝ => f (q t))
      ((fCLM ∘SL ContinuousLinearMap.toSpanSingleton ℝ q') 1)
      (Set.Ici 0) 0 := by
    have h := (fCLM.hasFDerivAt (x := q 0)).comp_hasFDerivWithinAt 0 hq
    have h' := h.hasDerivWithinAt
    have hfun : (⇑fCLM ∘ q) = (fun t : ℝ => f (q t)) := by
      funext t
      exact positiveLinearMap_toContinuousLinearMap_apply f (q t)
    rw [hfun] at h'
    exact h'
  have hreal : HasDerivWithinAt
      (fun t : ℝ => Complex.re (f (q t)))
      ((RCLike.reCLM ∘SL ContinuousLinearMap.toSpanSingleton ℝ
        ((fCLM ∘SL ContinuousLinearMap.toSpanSingleton ℝ q') 1)) 1)
      (Set.Ici 0) 0 := by
    have h := (RCLike.reCLM.hasFDerivAt (x := f (q 0))).comp_hasFDerivWithinAt 0 hfq
    have h' := h.hasDerivWithinAt
    have hfun : (⇑RCLike.reCLM ∘ (fun t : ℝ => f (q t))) =
        (fun t : ℝ => Complex.re (f (q t))) := by
      funext t
      rfl
    rw [hfun] at h'
    exact h'
  let g : ℝ → ℝ := fun t => Complex.re (f (q t))
  have hmin : IsLocalMinOn g (Set.Ici 0) 0 := by
    rw [IsLocalMinOn]
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hcp : 0 ≤ M.map (Φ.map
        (BoundedQuantumDynamicalSemigroup.nonnegativeTime t)) := by
      exact CompletelyPositiveMap.map_cstarMatrix_nonneg
        (Φ.map (BoundedQuantumDynamicalSemigroup.nonnegativeTime t)).1 M hM
    have hqpos : 0 ≤ q t := by
      exact star_left_conjugate_nonneg hcp C
    have hfpos : 0 ≤ f (q t) := f.map_nonneg hqpos
    have hg0 : g 0 = 0 := by
      change Complex.re (f (q 0)) = 0
      rw [hq_zero]
      simp [g]
    rw [hg0]
    exact (RCLike.nonneg_iff.mp hfpos).1
  have hone : (1 : ℝ) ∈ posTangentConeAt (Set.Ici 0) 0 := by
    apply mem_posTangentConeAt_of_segment_subset (x := (0 : ℝ)) (y := (1 : ℝ))
    have hseg : segment ℝ (0 : ℝ) 1 ⊆ Set.Ici 0 :=
      (convex_Ici (0 : ℝ)).segment_subset (show (0 : ℝ) ≤ 0 from le_rfl)
        (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    simpa using hseg
  have hderiv_nonneg := hmin.hasFDerivWithinAt_nonneg hreal hone
  have hderiv' : 0 ≤ Complex.re (fCLM q') := by
    simpa [ContinuousLinearMap.toSpanSingleton_apply_one] using hderiv_nonneg
  have hfclm : fCLM q' = f q' := by
    change positiveLinearMapToContinuousLinearMap f q' = f q'
    exact positiveLinearMap_toContinuousLinearMap_apply f q'
  rw [hfclm] at hderiv'
  exact hderiv'

/-- Package the infinitesimal invariants of a norm-continuous UCP semigroup. -/
noncomputable def toBoundedQuantumMarkovGenerator
    (G : HasBoundedGenerator Φ) : BoundedQuantumMarkovGenerator A where
  map := G.generator
  map_one := G.generator_apply_one
  map_star := G.generator_map_star
  isConditionallyCompletelyPositive := G.generator_isConditionallyCompletelyPositive

end QuantumDynamicalSemigroup.HasBoundedGenerator

namespace BoundedQuantumDynamicalSemigroup

variable {A : Type*} [OperatorAlgebra A]

/-- Extract the representation-free Markov generator carried by a bounded semigroup. -/
noncomputable def toBoundedQuantumMarkovGenerator
    (Φ : BoundedQuantumDynamicalSemigroup A) : BoundedQuantumMarkovGenerator A :=
  Φ.toHasBoundedGenerator.toBoundedQuantumMarkovGenerator

end BoundedQuantumDynamicalSemigroup

namespace QuantumDynamicalSemigroup

variable {A : Type*} [OperatorAlgebra A]

/-- A norm-continuous raw UCP semigroup inherits the positive-shift converse through its canonical
bounded-generator package. -/
lemma isChristensenEvansGenerator_of_hasCompletelyPositiveShift
    (Φ : QuantumDynamicalSemigroup A)
    (hΦ : QuantumDynamicalSemigroup.IsNormContinuous Φ)
    (hshift : HasCompletelyPositiveShift
      (Φ.toBoundedQuantumDynamicalSemigroup hΦ).generator) :
    IsChristensenEvansGenerator
      (Φ.toBoundedQuantumDynamicalSemigroup hΦ).generator := by
  exact BoundedQuantumDynamicalSemigroup.isChristensenEvansGenerator_of_hasCompletelyPositiveShift
    (Φ.toBoundedQuantumDynamicalSemigroup hΦ) hshift

/-- The raw norm-continuous semigroup form of the Hamiltonian-adjusted reduction. -/
lemma isChristensenEvansGenerator_of_hamiltonianShift
    (Φ : QuantumDynamicalSemigroup A)
    (hΦ : QuantumDynamicalSemigroup.IsNormContinuous Φ)
    (hshift : HasHamiltonianCompletelyPositiveShift
      (Φ.toBoundedQuantumDynamicalSemigroup hΦ).generator) :
    IsChristensenEvansGenerator
      (Φ.toBoundedQuantumDynamicalSemigroup hΦ).generator := by
  exact BoundedQuantumDynamicalSemigroup.isChristensenEvansGenerator_of_hamiltonianShift
    (Φ.toBoundedQuantumDynamicalSemigroup hΦ) hshift

/-- A norm-continuous UCP semigroup has a canonical bounded Markov-generator package. -/
noncomputable def toBoundedQuantumMarkovGenerator
    (Φ : QuantumDynamicalSemigroup A)
    (hΦ : QuantumDynamicalSemigroup.IsNormContinuous Φ) :
    BoundedQuantumMarkovGenerator A :=
  (Φ.toHasBoundedGenerator hΦ).toBoundedQuantumMarkovGenerator

end QuantumDynamicalSemigroup

end OperatorAlgebra
