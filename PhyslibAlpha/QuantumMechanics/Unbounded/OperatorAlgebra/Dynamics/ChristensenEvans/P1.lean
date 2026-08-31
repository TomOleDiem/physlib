/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Dynamics.CPClosure
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Dynamics.Semigroup
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Dynamics.Trotter
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.HilbertSpace
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Christensen-Evans data for bounded irreversible dynamics (part 1 of 2)

Split out of `ChristensenEvans.lean` to stay under the file-length style limit; see
`ChristensenEvans.lean` for the full module overview. This part covers the C*-algebraic
`StinespringWitness` layer for the general bounded jump term.
-/

@[expose] public section

namespace OperatorAlgebra

open Filter
open scoped ComplexOrder CStarAlgebra NNReal

variable {A : Type*} [OperatorAlgebra A]

open Filter
open scoped ComplexOrder CStarAlgebra NNReal

variable {A : Type*} [OperatorAlgebra A]

/-- The scalar restriction needed to view `A →L[ℂ] A` as a ℚ-normed algebra. -/
noncomputable local instance ceNormedAlgebraRat : NormedAlgebra ℚ (A →L[ℂ] A) :=
  .restrictScalars ℚ ℂ (A →L[ℂ] A)

/-- The scalar restriction needed to view `A →L[ℂ] A` as an ℝ-normed algebra. -/
noncomputable local instance ceNormedAlgebraReal : NormedAlgebra ℝ (A →L[ℂ] A) :=
  .restrictScalars ℝ ℂ (A →L[ℂ] A)

/-- The scalar restriction needed to view `A` itself as a ℚ-normed algebra. -/
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

/-- The bounded operator on `PiLp 2 (Fin n → H)` acting block-by-block by `M`. -/
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

/-- `blockMatrixMap`, packaged as a star algebra homomorphism from
`CStarMatrix (Fin n) (Fin n) B(H)`. -/
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

/-- The finite-support sesquilinear form on `A →₀ H` induced by the CP kernel `J`. -/
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

/-- `cpKernelInner`, in the equivalent `Finsupp.sum` form (see `cpKernelInnerSum_eq`). -/
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

/-- Left multiplication by `a`, lifted from `A` to the Stinespring pre-Hilbert space `A →₀ H`. -/
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

/-- The CP kernel weighted by a positive middle factor `q`, `⟪u, J(a⋆ q b) v⟫`. -/
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

end OperatorAlgebra
