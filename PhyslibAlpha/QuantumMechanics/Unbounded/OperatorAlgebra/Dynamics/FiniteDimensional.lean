/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import QuantumInfo.Channels.CPTP
public import QuantumInfo.Channels.Dual
public import PhyslibAlpha.QuantumMechanics.Unbounded.OperatorAlgebra.Dynamics.Semigroup
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Finite-dimensional GKSL algebra

This file is the finite-dimensional bridge between the abstract operator-algebraic dynamics and
the Choi/Kraus API in `QuantumInfo`.  It contains no semigroup assumption: it isolates the exact
algebraic ingredients that are used in the GKSL proof.  In particular, the completely positive
Kraus part is proved independently of the damping and Hamiltonian terms.
-/

@[expose] public section

namespace OperatorAlgebra

open scoped ComplexOrder NNReal Matrix.Norms.L2Operator

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {ι : Type*} [Fintype ι]

/-! ## Finite-dimensional quantum dynamical semigroups -/

/-
The finite-dimensional Schrödinger-picture API in `QuantumInfo` already bundles complete
positivity and trace preservation into `CPTPMap`.  The following structure adds only the
identity, semigroup, and continuity laws.  Continuity is continuity in the Choi topology supplied
by `QuantumInfo`, so this is a genuine norm/topological finite-dimensional semigroup and not a
pointwise family of unrelated channels.
-/

/-- A norm-continuous, identity-at-zero, additive-in-time family of CPTP channels on `d`: the
Schrödinger-picture finite-dimensional quantum dynamical semigroup. -/
structure FiniteDimensionalQuantumDynamicalSemigroup (d : Type*) [Fintype d]
    [DecidableEq d] where
  /-- The channel at each nonnegative time. -/
  map : ℝ≥0 → CPTPMap d d
  /-- Time zero is the identity channel. -/
  map_zero : map 0 = CPTPMap.id
  /-- The time-addition law. -/
  map_add : ∀ s t, map (s + t) = map s ∘ₘ map t
  /-- Continuity in the Choi topology. -/
  continuous : Continuous map

/-- Composition of finite-dimensional Heisenberg channels. -/
noncomputable def cpuId (d : Type*) [Fintype d] [DecidableEq d] : CPUMap d d where
  toLinearMap := MatrixMap.id d ℂ
  cp := MatrixMap.IsCompletelyPositive.id
  unital := MatrixMap.Unital.id

/-- Composition of finite-dimensional unital completely positive maps. -/
noncomputable def cpuCompose
    {dIn dM dOut : Type*} [Fintype dIn] [Fintype dM] [Fintype dOut]
    [DecidableEq dIn] [DecidableEq dM] [DecidableEq dOut]
    (Λ₂ : CPUMap dM dOut) (Λ₁ : CPUMap dIn dM) : CPUMap dIn dOut where
  toLinearMap := Λ₂.toLinearMap ∘ₗ Λ₁.toLinearMap
  cp := MatrixMap.IsCompletelyPositive.comp Λ₁.cp Λ₂.cp
  unital := by
    change Λ₂.toLinearMap (Λ₁.toLinearMap 1) = 1
    rw [Λ₁.unital, Λ₂.unital]

@[simp]
lemma cpuCompose_apply
    {dIn dM dOut : Type*} [Fintype dIn] [Fintype dM] [Fintype dOut]
    [DecidableEq dIn] [DecidableEq dM] [DecidableEq dOut]
    (Λ₂ : CPUMap dM dOut) (Λ₁ : CPUMap dIn dM) (X : Matrix dIn dIn ℂ) :
    (cpuCompose Λ₂ Λ₁).toCPMap.toLinearMap X =
      Λ₂.toCPMap.toLinearMap (Λ₁.toCPMap.toLinearMap X) :=
  rfl

@[simp]
lemma cpuCompose_id_left
    {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
    [DecidableEq dIn] [DecidableEq dOut] (Λ : CPUMap dIn dOut) :
    cpuCompose (cpuId dOut) Λ = Λ := by
  apply CPUMap.ext
  ext X
  simp [cpuCompose, cpuId, MatrixMap.id]

@[simp]
lemma cpuCompose_id_right
    {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
    [DecidableEq dIn] [DecidableEq dOut] (Λ : CPUMap dIn dOut) :
    cpuCompose Λ (cpuId dIn) = Λ := by
  apply CPUMap.ext
  ext X
  simp [cpuCompose, cpuId, MatrixMap.id]

@[simp]
lemma cpuCompose_assoc
    {d₁ d₂ d₃ d₄ : Type*} [Fintype d₁] [Fintype d₂] [Fintype d₃] [Fintype d₄]
    [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] [DecidableEq d₄]
    (Λ₄ : CPUMap d₃ d₄) (Λ₃ : CPUMap d₂ d₃)
    (Λ₂ : CPUMap d₁ d₂) :
    cpuCompose Λ₄ (cpuCompose Λ₃ Λ₂) =
      cpuCompose (cpuCompose Λ₄ Λ₃) Λ₂ := by
  apply CPUMap.ext
  ext X
  rfl

/-- A finite-dimensional Heisenberg quantum dynamical semigroup. -/
structure FiniteDimensionalHeisenbergQuantumDynamicalSemigroup (d : Type*) [Fintype d]
    [DecidableEq d] where
  /-- The unital completely positive evolution at each nonnegative time. -/
  map : ℝ≥0 → CPUMap d d
  /-- Time zero is the identity map. -/
  map_zero : map 0 = cpuId d
  /-- The semigroup composition law. -/
  map_add : ∀ s t, map (s + t) = cpuCompose (map s) (map t)
  /-- Pointwise continuity on Hermitian observables. -/
  continuous : ∀ X : HermitianMat d ℂ, Continuous (fun t => map t X)

namespace FiniteDimensionalHeisenbergQuantumDynamicalSemigroup

variable (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d)

@[simp]
lemma map_zero_apply (X : HermitianMat d ℂ) : Φ.map 0 X = X := by
  rw [Φ.map_zero]
  rfl

lemma map_add_apply (s t : ℝ≥0) (X : HermitianMat d ℂ) :
    Φ.map (s + t) X = Φ.map s (Φ.map t X) := by
  rw [Φ.map_add]
  rfl

end FiniteDimensionalHeisenbergQuantumDynamicalSemigroup

namespace FiniteDimensionalQuantumDynamicalSemigroup

variable (Φ : FiniteDimensionalQuantumDynamicalSemigroup d)

@[simp]
lemma map_zero_apply (ρ : MState d) : Φ.map 0 ρ = ρ := by
  rw [Φ.map_zero]
  simp

@[simp]
lemma map_add_apply (s t : ℝ≥0) (ρ : MState d) :
    Φ.map (s + t) ρ = Φ.map s (Φ.map t ρ) := by
  rw [Φ.map_add]
  simp

end FiniteDimensionalQuantumDynamicalSemigroup

/-- A generator preserves the trace of states infinitesimally when its trace is zero on every
input.  This is the generator-level counterpart of `MatrixMap.IsTracePreserving`. -/
def IsTraceAnnihilating (M : MatrixMap d d ℂ) : Prop :=
  ∀ X, (M X).trace = 0

/-- The unnormalised maximally entangled vector used in the Choi criterion. -/
def maxEntangledVector : (d × d) → ℂ :=
  fun p => if p.1 = p.2 then 1 else 0

/-- Conditional complete positivity, expressed as positivity of the Choi quadratic form on the
orthogonal complement of the maximally entangled vector. -/
def IsConditionallyCompletelyPositive (M : MatrixMap d d ℂ) : Prop :=
  ∀ x : (d × d) → ℂ,
    (star x) ⬝ᵥ maxEntangledVector = 0 →
      0 ≤ (star x) ⬝ᵥ (M.choi_matrix.mulVec x)

/-- The infinitesimal form of unitality for a Heisenberg-picture generator. -/
def IsUnitalInfinitesimal (M : MatrixMap d d ℂ) : Prop :=
  M 1 = 0

/-! ### Real-time parameterization -/

/-- Extend a nonnegative time to a real parameter by truncating negative values at zero. -/
def nonnegativeTime (t : ℝ) : ℝ≥0 :=
  ⟨max t 0, le_max_right _ _⟩

@[simp]
lemma nonnegativeTime_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    nonnegativeTime t = ⟨t, ht⟩ := by
  ext
  simp [nonnegativeTime, max_eq_left ht]

namespace FiniteDimensionalHeisenbergQuantumDynamicalSemigroup

/-- The Choi curve of a Heisenberg-picture CPU semigroup, extended constantly to negative times. -/
noncomputable def choiCurve
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) (t : ℝ) :
  Matrix (d × d) (d × d) ℂ :=
  MatrixMap.choi_matrix ((Φ.map (nonnegativeTime t)).toCPMap.toLinearMap)

/-- A matrix map is a Choi-generator of a Heisenberg CPU semigroup when it is the right
derivative of its Choi curve. -/
def HasChoiGenerator
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d)
    (L : MatrixMap d d ℂ) : Prop :=
  HasDerivWithinAt Φ.choiCurve L.choi_matrix (Set.Ici 0) 0

@[simp]
lemma choiCurve_zero
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) :
    Φ.choiCurve 0 = (MatrixMap.id d ℂ).choi_matrix := by
  change MatrixMap.choi_matrix
    ((Φ.map (nonnegativeTime 0)).toCPMap.toLinearMap) = _
  have ht : nonnegativeTime 0 = 0 := by
    apply Subtype.ext
    simp [nonnegativeTime]
  rw [ht, Φ.map_zero]
  rfl

/-! ### Automatic differentiability via the transfer matrix

The finite-dimensional semigroup is presented on Hermitian matrices, while the integrated
semigroup theorem is an algebra theorem.  The transfer matrix supplies exactly that algebra: map
composition becomes matrix multiplication.  Continuity on Hermitian inputs extends to arbitrary
matrix inputs by the real/imaginary decomposition, and the Choi map is then applied as a fixed
continuous linear map. -/

/-- The Choi matrix of `Φ.map` at nonnegative time `t`, as a curve in `t : ℝ` (see
`nonnegativeTime`). -/
noncomputable def transferCurve
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) (t : ℝ) :
    Matrix (d × d) (d × d) ℂ :=
  MatrixMap.toMatrix ((Φ.map (nonnegativeTime t)).toCPMap.toLinearMap)

lemma transferCurve_apply_of_nonneg
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d)
    {t : ℝ} (ht : 0 ≤ t) :
    Φ.transferCurve t = MatrixMap.toMatrix ((Φ.map ⟨t, ht⟩).toCPMap.toLinearMap) := by
  simp [transferCurve, nonnegativeTime_of_nonneg ht]

lemma transferCurve_continuous_on_inputs
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) (X : Matrix d d ℂ) :
    Continuous (fun t : ℝ =>
      (Φ.map (nonnegativeTime t)).toCPMap.toLinearMap X) := by
  have htime : Continuous (nonnegativeTime : ℝ → ℝ≥0) := by
    change Continuous (fun s : ℝ =>
      (⟨max s 0, le_max_right _ _⟩ : ℝ≥0))
    exact (continuous_id.max continuous_const).subtype_mk fun _ => le_max_right _ _
  let Xr : HermitianMat d ℂ := ⟨(realPart X : Matrix d d ℂ), by
    exact (realPart X).property⟩
  let Xi : HermitianMat d ℂ := ⟨(imaginaryPart X : Matrix d d ℂ), by
    exact (imaginaryPart X).property⟩
  have hr := HermitianMat.continuous_mat.comp ((Φ.continuous Xr).comp htime)
  have hi := HermitianMat.continuous_mat.comp ((Φ.continuous Xi).comp htime)
  have h := hr.add (hi.const_smul Complex.I)
  have heq : (Xr : Matrix d d ℂ) + Complex.I • (Xi : Matrix d d ℂ) = X := by
    change (realPart X : Matrix d d ℂ) +
      Complex.I • (imaginaryPart X : Matrix d d ℂ) = X
    exact realPart_add_I_smul_imaginaryPart X
  convert h using 1
  · funext t
    rw [← heq]
    simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply]
    rw [LinearMap.map_add, LinearMap.map_smul]
    rfl

lemma transferCurve_continuous
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) :
    Continuous Φ.transferCurve := by
  apply continuous_pi
  intro p
  apply continuous_pi
  intro q
  rcases p with ⟨j₁, i₁⟩
  rcases q with ⟨j₂, i₂⟩
  dsimp [transferCurve]
  have hout := transferCurve_continuous_on_inputs Φ (Matrix.single j₂ i₂ 1)
  have hrepr := (Matrix.stdBasis ℂ d d).continuous_coe_repr.comp hout
  have hcoord := (continuous_apply (j₁, i₁)).comp hrepr
  simpa [Function.comp_def, MatrixMap.toMatrix, LinearMap.toMatrix_apply,
    Matrix.stdBasis_eq_single] using hcoord

lemma transferCurve_zero
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) :
    Φ.transferCurve 0 = 1 := by
  dsimp [transferCurve]
  have ht : nonnegativeTime (0 : ℝ) = 0 := by
    apply Subtype.ext
    simp [nonnegativeTime]
  rw [ht, Φ.map_zero]
  simp [MatrixMap.toMatrix, cpuId, MatrixMap.id]

lemma transferCurve_add
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    Φ.transferCurve (s + t) = Φ.transferCurve s * Φ.transferCurve t := by
  have hst : nonnegativeTime (s + t) = nonnegativeTime s + nonnegativeTime t := by
    apply Subtype.ext
    change max (s + t) 0 = max s 0 + max t 0
    rw [max_eq_left (add_nonneg hs ht), max_eq_left hs, max_eq_left ht]
  dsimp [transferCurve]
  rw [hst, Φ.map_add]
  change MatrixMap.toMatrix
      (((Φ.map (nonnegativeTime s)).toCPMap.toLinearMap) ∘ₗ
        ((Φ.map (nonnegativeTime t)).toCPMap.toLinearMap)) = _
  rw [MatrixMap.toMatrix_comp]

lemma exists_transfer_generator
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) :
    ∃ G : Matrix (d × d) (d × d) ℂ,
      HasDerivWithinAt Φ.transferCurve G (Set.Ici 0) 0 := by
  let T := Φ.transferCurve
  have hT : Continuous T := Φ.transferCurve_continuous
  have hzero : T 0 = 1 := Φ.transferCurve_zero
  have hsg : ∀ {s t : ℝ}, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t := by
    intro s t hs ht
    exact Φ.transferCurve_add hs ht
  obtain ⟨a, ha, haunit⟩ :=
    NormedAlgebraSemigroup.exists_integrated_isUnit T hT hzero
  have hderiv := NormedAlgebraSemigroup.hasDerivWithinAt_of_integrated_isUnit
    T hT hzero hsg ha haunit
  refine ⟨(T a - T 0) * (↑(haunit.unit⁻¹) : Matrix (d × d) (d × d) ℂ), ?_⟩
  exact hderiv

/-- The Choi-matrix map, as a continuous linear map on matrix maps. -/
def choiLinearMap : MatrixMap d d ℂ →ₗ[ℂ]
    Matrix (d × d) (d × d) ℂ where
  toFun M := M.choi_matrix
  map_add' M N := by ext; simp [MatrixMap.choi_matrix]
  map_smul' c M := by ext; simp [MatrixMap.choi_matrix]

lemma exists_choi_generator
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) :
    ∃ L : MatrixMap d d ℂ, HasChoiGenerator Φ L := by
  obtain ⟨G, hderiv⟩ := Φ.exists_transfer_generator
  let T := Φ.transferCurve
  let e : MatrixMap d d ℂ ≃ₗ[ℂ] Matrix (d × d) (d × d) ℂ := MatrixMap.toMatrix
  let L : MatrixMap d d ℂ := e.symm G
  let F : Matrix (d × d) (d × d) ℂ →ₗ[ℂ]
      Matrix (d × d) (d × d) ℂ := choiLinearMap.comp e.symm.toLinearMap
  let Fℝ : Matrix (d × d) (d × d) ℂ →L[ℝ]
      Matrix (d × d) (d × d) ℂ := by
    let q := F.restrictScalars ℝ
    exact { toLinearMap := q, cont := q.continuous_of_finiteDimensional }
  have hF : HasDerivWithinAt (fun _ : ℝ => Fℝ) 0 (Set.Ici 0) 0 :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := Fℝ)).hasDerivWithinAt
  have hchoi := hF.clm_apply hderiv
  refine ⟨L, ?_⟩
  change HasDerivWithinAt
    (fun t : ℝ => MatrixMap.choi_matrix
      ((Φ.map (nonnegativeTime t)).toCPMap.toLinearMap))
    L.choi_matrix (Set.Ici 0) 0
  have hchoi' : HasDerivWithinAt (fun t : ℝ => Fℝ (T t)) (Fℝ G)
      (Set.Ici 0) 0 := by
    simpa only [zero_apply, zero_add, Function.comp_apply] using hchoi
  simpa [Fℝ, F, L, e, T, transferCurve, choiLinearMap,
    MatrixMap.choi_matrix] using hchoi'

end FiniteDimensionalHeisenbergQuantumDynamicalSemigroup

/-! ### Differentiable Heisenberg semigroups

Pointwise continuity is enough to state a semigroup, but not enough to speak about its generator.
The following certificate records a right derivative on Hermitian observables and keeps the
Hermitian-preserving property of the matrix map explicit.
-/

/-- A right derivative on Hermitian observables for a finite-dimensional Heisenberg semigroup,
together with the fact that the derivative is Hermitian-preserving. -/
structure HasFiniteDimensionalHeisenbergGenerator
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) where
  /-- The underlying complex-linear matrix map. -/
  map : MatrixMap d d ℂ
  /-- The map preserves Hermitian matrices. -/
  is_hermitian_preserving : MatrixMap.IsHermitianPreserving map
  /-- The Heisenberg semigroup has this right derivative on Hermitian observables. -/
  has_deriv : ∀ X : HermitianMat d ℂ,
    HasDerivWithinAt
      (fun t : ℝ => (Φ.map (nonnegativeTime t) X : Matrix d d ℂ))
      (map X) (Set.Ici 0) 0

/-- Conjugate transpose, as a continuous ℝ-linear map on matrices. -/
noncomputable def matrixConjTransposeRealCLM : Matrix d d ℂ →L[ℝ] Matrix d d ℂ := by
  let f : Matrix d d ℂ →ₗ[ℝ] Matrix d d ℂ :=
    { toFun := Matrix.conjTranspose
      map_add' := by intro X Y; exact Matrix.conjTranspose_add X Y
      map_smul' := by intro c X; simp [Matrix.conjTranspose_smul] }
  exact { toLinearMap := f, cont := f.continuous_of_finiteDimensional }

/-- Evaluation of a Choi-matrix-indexed linear map at the fixed matrix `X`. -/
noncomputable def transferEval (X : Matrix d d ℂ) :
    Matrix (d × d) (d × d) ℂ →ₗ[ℂ] Matrix d d ℂ where
  toFun M := (MatrixMap.toMatrix.symm M) X
  map_add' M N := by simp
  map_smul' c M := by simp

/-- The generator certificate obtained from `exists_transfer_generator`, in
`HasFiniteDimensionalHeisenbergGenerator` form. -/
noncomputable def finiteDimensionalGenerator
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) :
    HasFiniteDimensionalHeisenbergGenerator Φ := by
  let K := Classical.choose (Φ.exists_transfer_generator)
  have hK : HasDerivWithinAt Φ.transferCurve K (Set.Ici 0) 0 :=
    Classical.choose_spec (Φ.exists_transfer_generator)
  let e : MatrixMap d d ℂ ≃ₗ[ℂ] Matrix (d × d) (d × d) ℂ := MatrixMap.toMatrix
  let L : MatrixMap d d ℂ := e.symm K
  have hderiv_matrix : ∀ X : Matrix d d ℂ,
      HasDerivWithinAt
        (fun t : ℝ => (Φ.map (nonnegativeTime t)).toCPMap.toLinearMap X)
        (L X) (Set.Ici 0) 0 := by
    intro X
    let F := transferEval X
    let Fℝ : Matrix (d × d) (d × d) ℂ →L[ℝ] Matrix d d ℂ := by
      let q := F.restrictScalars ℝ
      exact { toLinearMap := q, cont := q.continuous_of_finiteDimensional }
    have hF : HasDerivWithinAt (fun _ : ℝ => Fℝ) 0 (Set.Ici 0) 0 :=
      (hasDerivAt_const (x := (0 : ℝ)) (c := Fℝ)).hasDerivWithinAt
    have h := hF.clm_apply hK
    have h' : HasDerivWithinAt (fun t : ℝ => Fℝ (Φ.transferCurve t))
        (Fℝ K) (Set.Ici 0) 0 := by
      simpa only [zero_apply, zero_add, Function.comp_apply] using h
    simpa [Fℝ, F, L, e, transferEval,
      FiniteDimensionalHeisenbergQuantumDynamicalSemigroup.transferCurve] using h'
  have hHP : MatrixMap.IsHermitianPreserving L := by
    intro X hX
    have hderivX := hderiv_matrix X
    let starℝ := matrixConjTransposeRealCLM (d := d)
    have hc : HasDerivWithinAt (fun _ : ℝ => starℝ) 0 (Set.Ici 0) 0 :=
      (hasDerivAt_const (x := (0 : ℝ)) (c := starℝ)).hasDerivWithinAt
    have hs := hc.clm_apply hderivX
    have heq : ∀ t ∈ Set.Ici (0 : ℝ),
        starℝ ((Φ.map (nonnegativeTime t) ⟨X, hX⟩ : HermitianMat d ℂ) : Matrix d d ℂ) =
          (Φ.map (nonnegativeTime t) ⟨X, hX⟩ : Matrix d d ℂ) := by
      intro t ht
      exact (Φ.map (nonnegativeTime t)).toCPMap.toPMap.toHPMap.HP hX
    have hs' := hs.congr (fun t ht => (heq t ht).symm) (heq 0 (by simp)).symm
    have hu := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq
      hderivX.hasFDerivWithinAt hs'.hasFDerivWithinAt
    have hu' := congrArg (fun f => f (1 : ℝ)) hu
    change (L X).conjTranspose = L X
    convert hu'.symm using 1
    all_goals simp [starℝ, matrixConjTransposeRealCLM]
  refine { map := L, is_hermitian_preserving := hHP, has_deriv := ?_ }
  intro X
  exact hderiv_matrix X

namespace HasFiniteDimensionalHeisenbergGenerator

variable {Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d}
variable (G : HasFiniteDimensionalHeisenbergGenerator Φ)

lemma is_unital_infinitesimal : IsUnitalInfinitesimal G.map := by
  have h := G.has_deriv (1 : HermitianMat d ℂ)
  have hconst : Set.EqOn
      (fun t : ℝ => (Φ.map (nonnegativeTime t) (1 : HermitianMat d ℂ) : Matrix d d ℂ))
      (fun _ : ℝ => (1 : Matrix d d ℂ)) (Set.Ici 0) := by
    intro t ht
    simp
  have hzero := h.congr
    (fun t ht => (hconst (x := t) ht).symm)
    (hconst (x := 0) (by simp)).symm
  have hz : HasDerivWithinAt (fun _ : ℝ => (1 : Matrix d d ℂ))
      0 (Set.Ici 0) 0 := by
    exact hasDerivWithinAt_const (𝕜 := ℝ) (c := (1 : Matrix d d ℂ))
      (x := (0 : ℝ)) (s := Set.Ici 0)
  have heq := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq
    hzero.hasFDerivWithinAt hz.hasFDerivWithinAt
  have heq' := congrArg (fun f => f (1 : ℝ)) heq
  calc
    G.map (1 : Matrix d d ℂ) =
        (ContinuousLinearMap.toSpanSingleton ℝ (G.map (1 : Matrix d d ℂ))) 1 := by
      symm
      exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ _
    _ = (ContinuousLinearMap.toSpanSingleton ℝ 0) 1 := heq'
    _ = 0 := by
      rw [ContinuousLinearMap.toSpanSingleton_apply_one]

lemma has_deriv_matrix (X : Matrix d d ℂ) :
    HasDerivWithinAt
      (fun t : ℝ => (Φ.map (nonnegativeTime t)).toCPMap.toLinearMap X)
      (G.map X) (Set.Ici 0) 0 := by
  have hreal := G.has_deriv (realPart X)
  have himag := G.has_deriv (imaginaryPart X)
  have h := hreal.add (himag.const_smul Complex.I)
  have h' : HasDerivWithinAt
      (fun t : ℝ => (Φ.map (nonnegativeTime t)).toCPMap.toLinearMap X)
      (G.map (realPart X) + Complex.I • G.map (imaginaryPart X)) (Set.Ici 0) 0 := by
    exact h.congr
      (fun t ht => by
        change (Φ.map (nonnegativeTime t)).toCPMap.toLinearMap X =
          ((Φ.map (nonnegativeTime t)) (realPart X) : Matrix d d ℂ) +
            Complex.I • ((Φ.map (nonnegativeTime t)) (imaginaryPart X) : Matrix d d ℂ)
        conv_lhs => rw [← realPart_add_I_smul_imaginaryPart X]
        simp only [map_add, map_smul]
        rfl)
      (by
        change (Φ.map (nonnegativeTime 0)).toCPMap.toLinearMap X =
          ((Φ.map (nonnegativeTime 0)) (realPart X) : Matrix d d ℂ) +
            Complex.I • ((Φ.map (nonnegativeTime 0)) (imaginaryPart X) : Matrix d d ℂ)
        conv_lhs => rw [← realPart_add_I_smul_imaginaryPart X]
        simp only [map_add, map_smul]
        rfl)
  convert h' using 1
  conv_lhs => rw [← realPart_add_I_smul_imaginaryPart X]
  simp only [map_add, map_smul]

lemma has_choi_generator :
    FiniteDimensionalHeisenbergQuantumDynamicalSemigroup.HasChoiGenerator Φ G.map := by
  change HasDerivWithinAt
    (fun t : ℝ =>
      MatrixMap.choi_matrix ((Φ.map (nonnegativeTime t)).toCPMap.toLinearMap))
    G.map.choi_matrix (Set.Ici 0) 0
  apply hasDerivWithinAt_pi.2
  intro p
  apply hasDerivWithinAt_pi.2
  intro q
  rcases p with ⟨j₁, i₁⟩
  rcases q with ⟨j₂, i₂⟩
  change HasDerivWithinAt
    (fun t : ℝ =>
      ((Φ.map (nonnegativeTime t)).toCPMap.toLinearMap
        (Matrix.single i₁ i₂ 1)) j₁ j₂)
    ((G.map (Matrix.single i₁ i₂ 1)) j₁ j₂) (Set.Ici 0) 0
  exact (hasDerivWithinAt_pi.1
    ((hasDerivWithinAt_pi.1
      (G.has_deriv_matrix (Matrix.single i₁ i₂ 1))) j₁)) j₂

end HasFiniteDimensionalHeisenbergGenerator

/--
An infinitesimal Heisenberg-picture quantum Markov generator.

The two fields are the algebraic conditions that survive differentiation of a unital completely
positive semigroup: conditional complete positivity on the Choi nullspace, and preservation of
the identity.  This package is deliberately independent of a choice of Kraus representation or
of a topology on the time parameter.
-/
structure FiniteDimensionalHeisenbergGenerator (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The underlying linear map on matrices. -/
  map : MatrixMap d d ℂ
  /-- Infinitesimal unitality. -/
  is_unital_infinitesimal : IsUnitalInfinitesimal map
  /-- The generator maps Hermitian observables to Hermitian observables. -/
  is_hermitian_preserving : MatrixMap.IsHermitianPreserving map
  /-- Infinitesimal conditional complete positivity. -/
  is_conditionally_completely_positive : IsConditionallyCompletelyPositive map

namespace HasFiniteDimensionalHeisenbergGenerator

variable {Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d}
variable (G : HasFiniteDimensionalHeisenbergGenerator Φ)

/-- Package a differentiable Heisenberg semigroup as infinitesimal quantum-Markov data once the
conditional Choi positivity of its derivative has been established.  The latter is kept as an
explicit hypothesis: it is the genuinely positivity-sensitive part of the converse theorem. -/
noncomputable def toGenerator
    (hccp : IsConditionallyCompletelyPositive G.map) :
    FiniteDimensionalHeisenbergGenerator d :=
  { map := G.map
    is_unital_infinitesimal := G.is_unital_infinitesimal
    is_hermitian_preserving := G.is_hermitian_preserving
    is_conditionally_completely_positive := hccp }

@[simp]
lemma toGenerator_map
    (hccp : IsConditionallyCompletelyPositive G.map) :
    (G.toGenerator hccp).map = G.map :=
  rfl

end HasFiniteDimensionalHeisenbergGenerator

/-- The Schrödinger-side infinitesimal data: Hermitian preservation and trace annihilation. -/
structure FiniteDimensionalSchrodingerGenerator (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The underlying linear map on density matrices. -/
  map : MatrixMap d d ℂ
  /-- The generator maps Hermitian matrices to Hermitian matrices. -/
  is_hermitian_preserving : MatrixMap.IsHermitianPreserving map
  /-- The generator has zero trace on every input. -/
  is_trace_annihilating : IsTraceAnnihilating map

namespace FiniteDimensionalHeisenbergGenerator

variable (G : FiniteDimensionalHeisenbergGenerator d)

/-- The trace-dual of a Heisenberg generator. -/
noncomputable def toSchrodingerMap : MatrixMap d d ℂ := G.map.dual

lemma toSchrodingerMap_isHermitianPreserving :
    MatrixMap.IsHermitianPreserving G.toSchrodingerMap :=
  MatrixMap.IsHermitianPreserving.dual G.is_hermitian_preserving

lemma toSchrodingerMap_isTraceAnnihilating :
    IsTraceAnnihilating G.toSchrodingerMap := by
  intro X
  have h := MatrixMap.Dual.trace_eq G.map (1 : Matrix d d ℂ) X
  rw [G.is_unital_infinitesimal, zero_mul, one_mul] at h
  simpa [toSchrodingerMap] using h.symm

/-- `G`'s generator, repackaged in Schrödinger-picture form. -/
noncomputable def toSchrodingerGenerator : FiniteDimensionalSchrodingerGenerator d :=
  { map := G.toSchrodingerMap
    is_hermitian_preserving := G.toSchrodingerMap_isHermitianPreserving
    is_trace_annihilating := G.toSchrodingerMap_isTraceAnnihilating }

end FiniteDimensionalHeisenbergGenerator

/-- The quadratic expression is linear in the Choi matrix once the test vector is fixed.  Making
that linearity explicit is what lets the derivative of a Choi-valued semigroup be composed with
the positivity test in the infinitesimal argument. -/
def choiQuadraticFunctional (x : (d × d) → ℂ) :
    Matrix (d × d) (d × d) ℂ →ₗ[ℂ] ℂ where
  toFun C := (star x) ⬝ᵥ (C.mulVec x)
  map_add' C D := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' c C := by simp [Matrix.smul_mulVec, dotProduct_smul]

/-- `choiQuadraticFunctional`, as a continuous ℝ-linear map. -/
noncomputable def choiQuadraticContinuousLinearMap (x : (d × d) → ℂ) :
    Matrix (d × d) (d × d) ℂ →L[ℝ] ℂ := by
  let q : Matrix (d × d) (d × d) ℂ →ₗ[ℝ] ℂ :=
    (choiQuadraticFunctional x).restrictScalars ℝ
  exact { toLinearMap := q, cont := q.continuous_of_finiteDimensional }

omit [DecidableEq d] in
@[simp]
lemma choiQuadraticContinuousLinearMap_apply
    (x : (d × d) → ℂ) (C : Matrix (d × d) (d × d) ℂ) :
    choiQuadraticContinuousLinearMap x C = (star x) ⬝ᵥ (C.mulVec x) := by
  rfl

/-! ### The trace-side generator interface

The Choi derivative is the right input for conditional complete positivity.  Trace preservation is
an independent linear invariant, so we expose its scalar differential form as well.  Keeping the
two hypotheses separate is useful when a generator is obtained from a matrix exponential, a
coordinate calculation, or a dual semigroup.
-/

/-- `L` is the trace-side generator of `Φ`: the trace of `Φ.map (nonnegativeTime t) X` has right
derivative `(L X).trace` at `t = 0`, for every `X`. -/
def HasTraceGenerator
    (Φ : FiniteDimensionalQuantumDynamicalSemigroup d) (L : MatrixMap d d ℂ) : Prop :=
  ∀ X : Matrix d d ℂ,
    HasDerivWithinAt
      (fun t : ℝ =>
        ((Φ.map (nonnegativeTime t)).toPTPMap.toPMap.toHPMap.map X).trace)
      ((L X).trace) (Set.Ici 0) 0

lemma hasTraceGenerator_isTraceAnnihilating
    (Φ : FiniteDimensionalQuantumDynamicalSemigroup d) (L : MatrixMap d d ℂ)
    (hL : HasTraceGenerator Φ L) :
    IsTraceAnnihilating L := by
  intro X
  have htrace := hL X
  have hconst : Set.EqOn
      (fun t : ℝ =>
        ((Φ.map (nonnegativeTime t)).toPTPMap.toPMap.toHPMap.map X).trace)
      (fun _ : ℝ => X.trace) (Set.Ici 0) := by
    intro t ht
    exact (Φ.map (nonnegativeTime t)).toPTPMap.TP X
  have hzero := htrace.congr
    (fun t ht => (hconst (x := t) ht).symm)
    (hconst (x := 0) (by simp)).symm
  have hz : HasDerivWithinAt (fun _ : ℝ => X.trace) 0 (Set.Ici 0) 0 :=
    hasDerivWithinAt_const (𝕜 := ℝ) (c := X.trace) (x := (0 : ℝ)) (s := Set.Ici 0)
  have heq := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq
    hzero.hasFDerivWithinAt hz.hasFDerivWithinAt
  have heq' := congrArg (fun f => f (1 : ℝ)) heq
  simpa using heq'

namespace FiniteDimensionalQuantumDynamicalSemigroup

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Choi curve of a nonnegative-time CPTP semigroup, extended constantly to negative times. -/
noncomputable def choiCurve (Φ : FiniteDimensionalQuantumDynamicalSemigroup d) (t : ℝ) :
    Matrix (d × d) (d × d) ℂ := (Φ.map (nonnegativeTime t)).choi

/-- A matrix map `L` is a Choi-generator of `Φ` when the Choi curve has right derivative `L`. -/
def HasChoiGenerator (Φ : FiniteDimensionalQuantumDynamicalSemigroup d)
    (L : MatrixMap d d ℂ) : Prop :=
  HasDerivWithinAt Φ.choiCurve L.choi_matrix (Set.Ici 0) 0

@[simp]
lemma choiCurve_zero (Φ : FiniteDimensionalQuantumDynamicalSemigroup d) :
    Φ.choiCurve 0 = (Φ.map 0).choi := by
  change (Φ.map (nonnegativeTime 0)).choi = (Φ.map 0).choi
  have ht : nonnegativeTime 0 = 0 := by
    apply Subtype.ext
    simp [nonnegativeTime]
  rw [ht]

lemma choiCurve_of_nonneg (Φ : FiniteDimensionalQuantumDynamicalSemigroup d)
    {t : ℝ} (ht : 0 ≤ t) :
    Φ.choiCurve t = (Φ.map ⟨t, ht⟩).choi := by
  simp [choiCurve, nonnegativeTime_of_nonneg ht]

lemma choi_id_quadratic_zero (x : (d × d) → ℂ)
    (hx : (star x) ⬝ᵥ maxEntangledVector = 0) :
    (star x) ⬝ᵥ ((CPTPMap.id (dIn := d)).choi.mulVec x) = 0 := by
  change (star x) ⬝ᵥ ((MatrixMap.id d ℂ).choi_matrix.mulVec x) = 0
  let v : (d × d) → ℂ := fun p => if p.1 = p.2 then 1 else 0
  have hC : (MatrixMap.id d ℂ).choi_matrix =
      Matrix.of (fun (i j : d × d) => v i * star (v j)) := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp [MatrixMap.choi_matrix, Matrix.single, v]
    aesop
  have h_inner : (star x) ⬝ᵥ (MatrixMap.id d ℂ).choi_matrix.mulVec x =
      star (star x ⬝ᵥ v) * (star x ⬝ᵥ v) := by
    simp [hC, Matrix.mulVec, dotProduct]
    simp [Finset.mul_sum, mul_comm, v]
    exact Finset.sum_congr rfl fun i hi => by split_ifs <;> simp [*]
  rw [h_inner]
  have hvx : (star x) ⬝ᵥ v = 0 := by
    change (star x) ⬝ᵥ v = 0 at hx
    exact hx
  simp [hvx]

end FiniteDimensionalQuantumDynamicalSemigroup

/-- The correction terms in a GKSL generator have zero Choi quadratic form on this subspace.  We
record that property separately, since it is the exact interface needed to add them to a CP
Kraus part. -/
def IsChoiQuadraticNull (M : MatrixMap d d ℂ) : Prop :=
  ∀ x : (d × d) → ℂ,
    (star x) ⬝ᵥ maxEntangledVector = 0 →
      (star x) ⬝ᵥ (M.choi_matrix.mulVec x) = 0

lemma IsConditionallyCompletelyPositive.add_null
    {M N : MatrixMap d d ℂ} (hM : IsConditionallyCompletelyPositive M)
    (hN : IsChoiQuadraticNull N) :
    IsConditionallyCompletelyPositive (M + N) := by
  intro x hx
  have hchoi : (M + N).choi_matrix = M.choi_matrix + N.choi_matrix := by
    ext i j
    simp [MatrixMap.choi_matrix]
  rw [hchoi, Matrix.add_mulVec, dotProduct_add]
  exact add_nonneg (hM x hx) (le_of_eq (hN x hx).symm)

lemma IsChoiQuadraticNull.add
    {M N : MatrixMap d d ℂ} (hM : IsChoiQuadraticNull M)
    (hN : IsChoiQuadraticNull N) :
    IsChoiQuadraticNull (M + N) := by
  intro x hx
  have hchoi : (M + N).choi_matrix = M.choi_matrix + N.choi_matrix := by
    ext i j
    simp [MatrixMap.choi_matrix]
  rw [hchoi, Matrix.add_mulVec, dotProduct_add]
  rw [hM x hx, hN x hx, add_zero]

lemma IsChoiQuadraticNull.smul
    {M : MatrixMap d d ℂ} (hM : IsChoiQuadraticNull M) (c : ℂ) :
    IsChoiQuadraticNull (c • M) := by
  intro x hx
  have hchoi : (c • M).choi_matrix = c • M.choi_matrix := by
    ext i j
    simp [MatrixMap.choi_matrix]
  rw [hchoi, Matrix.smul_mulVec, dotProduct_smul, hM x hx, smul_zero]

lemma IsChoiQuadraticNull.zero :
    IsChoiQuadraticNull (0 : MatrixMap d d ℂ) := by
  intro x hx
  have hchoi : (0 : MatrixMap d d ℂ).choi_matrix = 0 := by
    ext i j
    simp [MatrixMap.choi_matrix]
  rw [hchoi, Matrix.zero_mulVec, dotProduct_zero]

lemma IsChoiQuadraticNull.neg {M : MatrixMap d d ℂ}
    (hM : IsChoiQuadraticNull M) : IsChoiQuadraticNull (-M) := by
  intro x hx
  have hchoi : (-M).choi_matrix = -M.choi_matrix := by
    ext i j
    simp [MatrixMap.choi_matrix]
  rw [hchoi, Matrix.neg_mulVec, dotProduct_neg, hM x hx, neg_zero]

lemma IsChoiQuadraticNull.sub {M N : MatrixMap d d ℂ}
    (hM : IsChoiQuadraticNull M) (hN : IsChoiQuadraticNull N) :
    IsChoiQuadraticNull (M - N) := by
  simpa only [sub_eq_add_neg] using hM.add hN.neg

lemma IsChoiQuadraticNull.finset_sum {κ : Type*} [Fintype κ]
    (M : κ → MatrixMap d d ℂ) (hM : ∀ i, IsChoiQuadraticNull (M i)) :
    IsChoiQuadraticNull (∑ i, M i) := by
  exact Finset.sum_induction M _ (fun _ _ hN hP => hN.add hP) .zero
    (by intro i hi; exact hM i)

/-- The scalar form of the Choi-generator hypothesis.

This is the exact differential interface needed by conditional complete positivity.  It is kept
separate from `HasChoiGenerator` because the latter uses the matrix topology chosen by the Choi
API, whereas this formulation records only the quadratic forms and is consequently portable
across equivalent finite-dimensional matrix norms.
-/
abbrev HasNormedComplexDeriv (f : ℝ → ℂ) (f' : ℂ) (s : Set ℝ) (x : ℝ) : Prop :=
  @HasDerivWithinAt ℝ _ ℂ Complex.instNormedAddCommGroup.toAddCommGroup
    (RCLike.toInnerProductSpaceReal : InnerProductSpace ℝ ℂ).toModule
    inferInstance inferInstance f f' s x

/-- `L` is a Choi generator of `Φ` in the weaker, quadratic-form-only sense: the scalar curve
`t ↦ ⟪x, Φ.choiCurve t x⟫` has the expected derivative, for every `x` orthogonal to the
maximally-entangled vector. -/
def HasChoiQuadraticGenerator
    (Φ : FiniteDimensionalQuantumDynamicalSemigroup d) (L : MatrixMap d d ℂ) : Prop :=
  ∀ x : (d × d) → ℂ,
    (star x) ⬝ᵥ maxEntangledVector = 0 →
      HasNormedComplexDeriv
        (fun t : ℝ => (star x) ⬝ᵥ (Φ.choiCurve t).mulVec x)
        ((star x) ⬝ᵥ (L.choi_matrix.mulVec x)) (Set.Ici 0) 0

lemma hasChoiGenerator_hasChoiQuadraticGenerator
    (Φ : FiniteDimensionalQuantumDynamicalSemigroup d) (L : MatrixMap d d ℂ)
    (hL : FiniteDimensionalQuantumDynamicalSemigroup.HasChoiGenerator Φ L) :
    HasChoiQuadraticGenerator Φ L := by
  change HasDerivWithinAt Φ.choiCurve L.choi_matrix (Set.Ici 0) 0 at hL
  intro x hx
  let q : Matrix (d × d) (d × d) ℂ →L[ℝ] ℂ := by
    let qₗ : Matrix (d × d) (d × d) ℂ →ₗ[ℝ] ℂ :=
      (choiQuadraticFunctional x).restrictScalars ℝ
    exact { toLinearMap := qₗ, cont := qₗ.continuous_of_finiteDimensional }
  have hq' : HasFDerivAt (𝕜 := ℝ) (q : Matrix (d × d) (d × d) ℂ → ℂ) q
      (Φ.choiCurve 0) := q.hasFDerivAt
  have hL' : HasFDerivWithinAt (𝕜 := ℝ) Φ.choiCurve
      (ContinuousLinearMap.toSpanSingleton ℝ L.choi_matrix) (Set.Ici 0) 0 :=
    hL.hasFDerivWithinAt
  have h := hq'.comp_hasFDerivWithinAt (𝕜 := ℝ) 0 hL'
  convert h.hasDerivWithinAt using 1
  · funext t
    rfl
  · change (star x) ⬝ᵥ (L.choi_matrix.mulVec x) =
      (star x) ⬝ᵥ (((1 : ℝ) • L.choi_matrix).mulVec x)
    simp

lemma hasChoiQuadraticGenerator_isConditionallyCompletelyPositive
    (Φ : FiniteDimensionalQuantumDynamicalSemigroup d) (L : MatrixMap d d ℂ)
    (hL : HasChoiQuadraticGenerator Φ L) :
    IsConditionallyCompletelyPositive L := by
  intro x hx
  let q : ℝ → ℂ := fun t => (star x) ⬝ᵥ (Φ.choiCurve t).mulVec x
  have hq := hL x hx
  let f : ℝ → ℝ := fun t => Complex.re (q t)
  have hf : HasDerivWithinAt f (Complex.re ((star x) ⬝ᵥ (L.choi_matrix.mulVec x)))
      (Set.Ici 0) 0 := by
    have h := (hasDerivWithinAt_const (𝕜 := ℝ) (c := RCLike.reCLM) (x := (0 : ℝ))
      (s := Set.Ici 0)).clm_apply hq
    simpa [f, Function.comp_apply] using h
  have hzero : f 0 = 0 := by
    change Complex.re ((star x) ⬝ᵥ (Φ.choiCurve 0).mulVec x) = 0
    rw [FiniteDimensionalQuantumDynamicalSemigroup.choiCurve_zero, Φ.map_zero]
    exact congrArg Complex.re
      (FiniteDimensionalQuantumDynamicalSemigroup.choi_id_quadratic_zero x hx)
  have hmin : IsLocalMinOn f (Set.Ici 0) 0 := by
    rw [IsLocalMinOn]
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hzero]
    have hC : (Φ.map (nonnegativeTime t)).choi.PosSemidef :=
      (Φ.map (nonnegativeTime t)).choi_PSD_of_CPTP
    have hpos : (0 : ℂ) ≤ q t := by
      change 0 ≤ (star x) ⬝ᵥ ((Φ.map (nonnegativeTime t)).choi.mulVec x)
      exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp hC).2 x
    exact (Complex.le_def.mp hpos).1
  have hone : (1 : ℝ) ∈ posTangentConeAt (Set.Ici 0) 0 := by
    apply mem_posTangentConeAt_of_segment_subset (x := (0 : ℝ)) (y := (1 : ℝ))
    have hseg : segment ℝ (0 : ℝ) 1 ⊆ Set.Ici 0 :=
      (convex_Ici (0 : ℝ)).segment_subset (show (0 : ℝ) ≤ 0 from le_rfl)
        (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    simpa using hseg
  have hderiv : 0 ≤ Complex.re ((star x) ⬝ᵥ (L.choi_matrix.mulVec x)) := by
    convert hmin.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt hone using 1 <;>
      simp [ContinuousLinearMap.toSpanSingleton_apply]
  have him : HasDerivWithinAt (fun t : ℝ => Complex.im (q t))
      (Complex.im ((star x) ⬝ᵥ (L.choi_matrix.mulVec x))) (Set.Ici 0) 0 := by
    have h := (hasDerivWithinAt_const (𝕜 := ℝ) (c := RCLike.imCLM) (x := (0 : ℝ))
      (s := Set.Ici 0)).clm_apply hq
    simpa [Function.comp_apply] using h
  have himzero : ∀ t ∈ Set.Ici (0 : ℝ), Complex.im (q t) = 0 := by
    intro t ht
    have hC : (Φ.map (nonnegativeTime t)).choi.PosSemidef :=
      (Φ.map (nonnegativeTime t)).choi_PSD_of_CPTP
    have hpos : (0 : ℂ) ≤ q t := by
      change 0 ≤ (star x) ⬝ᵥ ((Φ.map (nonnegativeTime t)).choi.mulVec x)
      exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp hC).2 x
    exact ((Complex.le_def.mp hpos).2).symm
  have hmin_im : IsLocalMinOn (fun t : ℝ => Complex.im (q t)) (Set.Ici 0) 0 := by
    rw [IsLocalMinOn]
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [himzero 0 (by simp), himzero t ht]
  have hmax_im : IsLocalMaxOn (fun t : ℝ => Complex.im (q t)) (Set.Ici 0) 0 := by
    rw [IsLocalMaxOn]
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [himzero 0 (by simp), himzero t ht]
  have him_nonneg : 0 ≤ Complex.im ((star x) ⬝ᵥ (L.choi_matrix.mulVec x)) := by
    convert hmin_im.hasFDerivWithinAt_nonneg him.hasFDerivWithinAt hone using 1 <;>
      simp [ContinuousLinearMap.toSpanSingleton_apply]
  have him_nonpos : Complex.im ((star x) ⬝ᵥ (L.choi_matrix.mulVec x)) ≤ 0 := by
    convert hmax_im.hasFDerivWithinAt_nonpos him.hasFDerivWithinAt hone using 1 <;>
      simp [ContinuousLinearMap.toSpanSingleton_apply]
  exact Complex.le_def.mpr ⟨hderiv, (le_antisymm him_nonpos him_nonneg).symm⟩

lemma finiteDimensionalQDS_hasChoiGenerator_isConditionallyCompletelyPositive
    (Φ : FiniteDimensionalQuantumDynamicalSemigroup d) (L : MatrixMap d d ℂ)
    (hL : FiniteDimensionalQuantumDynamicalSemigroup.HasChoiGenerator Φ L) :
    IsConditionallyCompletelyPositive L :=
  hasChoiQuadraticGenerator_isConditionallyCompletelyPositive Φ L
    (hasChoiGenerator_hasChoiQuadraticGenerator Φ L hL)

namespace FiniteDimensionalHeisenbergQuantumDynamicalSemigroup

/-- The scalar Choi derivative condition for a CPU semigroup.

This is the same quadratic-form interface as on the Schrödinger side, but it is stated directly
for the Heisenberg Choi curve.  Keeping it explicit makes the positivity-to-generator argument
independent of the later choice of a derivative certificate on observables.
-/
def HasChoiQuadraticGenerator
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d)
    (L : MatrixMap d d ℂ) : Prop :=
  ∀ x : (d × d) → ℂ,
    (star x) ⬝ᵥ maxEntangledVector = 0 →
      HasNormedComplexDeriv
        (fun t : ℝ => (star x) ⬝ᵥ (Φ.choiCurve t).mulVec x)
        ((star x) ⬝ᵥ (L.choi_matrix.mulVec x)) (Set.Ici 0) 0

lemma hasChoiGenerator_hasChoiQuadraticGenerator
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) (L : MatrixMap d d ℂ)
    (hL : HasChoiGenerator Φ L) :
    HasChoiQuadraticGenerator Φ L := by
  change HasDerivWithinAt Φ.choiCurve L.choi_matrix (Set.Ici 0) 0 at hL
  intro x hx
  let q : Matrix (d × d) (d × d) ℂ →L[ℝ] ℂ := by
    let qₗ : Matrix (d × d) (d × d) ℂ →ₗ[ℝ] ℂ :=
      (choiQuadraticFunctional x).restrictScalars ℝ
    exact { toLinearMap := qₗ, cont := qₗ.continuous_of_finiteDimensional }
  have hq' : HasFDerivAt (𝕜 := ℝ) (q : Matrix (d × d) (d × d) ℂ → ℂ) q
      (Φ.choiCurve 0) := q.hasFDerivAt
  have hL' : HasFDerivWithinAt (𝕜 := ℝ) Φ.choiCurve
      (ContinuousLinearMap.toSpanSingleton ℝ L.choi_matrix) (Set.Ici 0) 0 :=
    hL.hasFDerivWithinAt
  have h := hq'.comp_hasFDerivWithinAt (𝕜 := ℝ) 0 hL'
  convert h.hasDerivWithinAt using 1
  · funext t
    rfl
  · change (star x) ⬝ᵥ (L.choi_matrix.mulVec x) =
      (star x) ⬝ᵥ (((1 : ℝ) • L.choi_matrix).mulVec x)
    simp

lemma hasChoiQuadraticGenerator_isConditionallyCompletelyPositive
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) (L : MatrixMap d d ℂ)
    (hL : HasChoiQuadraticGenerator Φ L) :
    IsConditionallyCompletelyPositive L := by
  intro x hx
  let q : ℝ → ℂ := fun t => (star x) ⬝ᵥ (Φ.choiCurve t).mulVec x
  have hq := hL x hx
  let f : ℝ → ℝ := fun t => Complex.re (q t)
  have hf : HasDerivWithinAt f (Complex.re ((star x) ⬝ᵥ (L.choi_matrix.mulVec x)))
      (Set.Ici 0) 0 := by
    have h := (hasDerivWithinAt_const (𝕜 := ℝ) (c := RCLike.reCLM) (x := (0 : ℝ))
      (s := Set.Ici 0)).clm_apply hq
    simpa [f, Function.comp_apply] using h
  have hzero : f 0 = 0 := by
    change Complex.re ((star x) ⬝ᵥ (Φ.choiCurve 0).mulVec x) = 0
    rw [Φ.choiCurve_zero]
    exact congrArg Complex.re
      (FiniteDimensionalQuantumDynamicalSemigroup.choi_id_quadratic_zero x hx)
  have hmin : IsLocalMinOn f (Set.Ici 0) 0 := by
    rw [IsLocalMinOn]
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hzero]
    have hC : (Φ.choiCurve t).PosSemidef := by
      change (MatrixMap.choi_matrix ((Φ.map (nonnegativeTime t)).toCPMap.toLinearMap)).PosSemidef
      exact MatrixMap.choi_PSD_iff_CP_map _ |>.1 (Φ.map (nonnegativeTime t)).cp
    have hpos : (0 : ℂ) ≤ q t := by
      change 0 ≤ (star x) ⬝ᵥ ((Φ.choiCurve t).mulVec x)
      exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp hC).2 x
    exact (Complex.le_def.mp hpos).1
  have hone : (1 : ℝ) ∈ posTangentConeAt (Set.Ici 0) 0 := by
    apply mem_posTangentConeAt_of_segment_subset (x := (0 : ℝ)) (y := (1 : ℝ))
    have hseg : segment ℝ (0 : ℝ) 1 ⊆ Set.Ici 0 :=
      (convex_Ici (0 : ℝ)).segment_subset (show (0 : ℝ) ≤ 0 from le_rfl)
        (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    simpa using hseg
  have hderiv : 0 ≤ Complex.re ((star x) ⬝ᵥ (L.choi_matrix.mulVec x)) := by
    convert hmin.hasFDerivWithinAt_nonneg hf.hasFDerivWithinAt hone using 1 <;>
      simp [ContinuousLinearMap.toSpanSingleton_apply]
  have him : HasDerivWithinAt (fun t : ℝ => Complex.im (q t))
      (Complex.im ((star x) ⬝ᵥ (L.choi_matrix.mulVec x))) (Set.Ici 0) 0 := by
    have h := (hasDerivWithinAt_const (𝕜 := ℝ) (c := RCLike.imCLM) (x := (0 : ℝ))
      (s := Set.Ici 0)).clm_apply hq
    simpa [Function.comp_apply] using h
  have himzero : ∀ t ∈ Set.Ici (0 : ℝ), Complex.im (q t) = 0 := by
    intro t ht
    have hC : (Φ.choiCurve t).PosSemidef := by
      change (MatrixMap.choi_matrix ((Φ.map (nonnegativeTime t)).toCPMap.toLinearMap)).PosSemidef
      exact MatrixMap.choi_PSD_iff_CP_map _ |>.1 (Φ.map (nonnegativeTime t)).cp
    have hpos : (0 : ℂ) ≤ q t := by
      change 0 ≤ (star x) ⬝ᵥ ((Φ.choiCurve t).mulVec x)
      exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp hC).2 x
    exact ((Complex.le_def.mp hpos).2).symm
  have hmin_im : IsLocalMinOn (fun t : ℝ => Complex.im (q t)) (Set.Ici 0) 0 := by
    rw [IsLocalMinOn]
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [himzero 0 (by simp), himzero t ht]
  have hmax_im : IsLocalMaxOn (fun t : ℝ => Complex.im (q t)) (Set.Ici 0) 0 := by
    rw [IsLocalMaxOn]
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [himzero 0 (by simp), himzero t ht]
  have him_nonneg : 0 ≤ Complex.im ((star x) ⬝ᵥ (L.choi_matrix.mulVec x)) := by
    convert hmin_im.hasFDerivWithinAt_nonneg him.hasFDerivWithinAt hone using 1 <;>
      simp [ContinuousLinearMap.toSpanSingleton_apply]
  have him_nonpos : Complex.im ((star x) ⬝ᵥ (L.choi_matrix.mulVec x)) ≤ 0 := by
    convert hmax_im.hasFDerivWithinAt_nonpos him.hasFDerivWithinAt hone using 1 <;>
      simp [ContinuousLinearMap.toSpanSingleton_apply]
  exact Complex.le_def.mpr ⟨hderiv, (le_antisymm him_nonpos him_nonneg).symm⟩

lemma hasChoiGenerator_isConditionallyCompletelyPositive
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) (L : MatrixMap d d ℂ)
    (hL : HasChoiGenerator Φ L) :
    IsConditionallyCompletelyPositive L :=
  hasChoiQuadraticGenerator_isConditionallyCompletelyPositive Φ L
    (hasChoiGenerator_hasChoiQuadraticGenerator Φ L hL)

end FiniteDimensionalHeisenbergQuantumDynamicalSemigroup

lemma isCompletelyPositive_isConditionallyCompletelyPositive
    (M : MatrixMap d d ℂ) (hM : M.IsCompletelyPositive) :
    IsConditionallyCompletelyPositive M := by
  intro x hx
  have hC : M.choi_matrix.PosSemidef :=
    MatrixMap.choi_PSD_iff_CP_map M |>.1 hM
  exact (Matrix.posSemidef_iff_dotProduct_mulVec.mp hC).2 x

/-- The Heisenberg jump map associated with a finite family of noise matrices. -/
def matrixJumpMap (V : ι → Matrix d d ℂ) : MatrixMap d d ℂ :=
  MatrixMap.of_kraus (fun i => (V i).conjTranspose) (fun i => (V i).conjTranspose)

omit [DecidableEq d] in
@[simp]
lemma matrixJumpMap_apply (V : ι → Matrix d d ℂ) (X : Matrix d d ℂ) :
    matrixJumpMap V X = ∑ i, (V i).conjTranspose * X * V i := by
  simp [matrixJumpMap, MatrixMap.of_kraus]

lemma matrixJumpMap_apply_one (V : ι → Matrix d d ℂ) :
    matrixJumpMap V 1 = ∑ i, (V i).conjTranspose * V i := by
  simp [matrixJumpMap_apply]

lemma matrixJumpMap_isUnital_iff (V : ι → Matrix d d ℂ) :
    matrixJumpMap V 1 = 1 ↔ ∑ i, (V i).conjTranspose * V i = 1 := by
  rw [matrixJumpMap_apply_one]

/-- The jump part of a finite-dimensional Lindblad generator is completely positive. -/
lemma matrixJumpMap_isCompletelyPositive (V : ι → Matrix d d ℂ) :
    (matrixJumpMap V).IsCompletelyPositive := by
  classical
  exact MatrixMap.of_kraus_isCompletelyPositive (fun i => (V i).conjTranspose)

lemma matrixJumpMap_isConditionallyCompletelyPositive (V : ι → Matrix d d ℂ) :
    IsConditionallyCompletelyPositive (matrixJumpMap V) := by
  exact isCompletelyPositive_isConditionallyCompletelyPositive _
    (matrixJumpMap_isCompletelyPositive V)

lemma isCompletelyPositive_exists_matrixJumpMap
    (M : MatrixMap d d ℂ) (hM : M.IsCompletelyPositive) :
    ∃ V : (d × d) → Matrix d d ℂ, M = matrixJumpMap V := by
  obtain ⟨K, hK⟩ := MatrixMap.IsCompletelyPositive.exists_kraus M hM
  refine ⟨fun i => (K i).conjTranspose, ?_⟩
  rw [hK]
  ext X
  simp [matrixJumpMap_apply, MatrixMap.of_kraus]

/-- Left multiplication by a fixed matrix. -/
def matrixMulLeft (Q : Matrix d d ℂ) : MatrixMap d d ℂ where
  toFun X := Q * X
  map_add' X Y := Q.mul_add X Y
  map_smul' c X := Q.mul_smul c X

/-- Right multiplication by a fixed matrix. -/
def matrixMulRight (Q : Matrix d d ℂ) : MatrixMap d d ℂ where
  toFun X := X * Q
  map_add' X Y := X.add_mul Y Q
  map_smul' c X := Matrix.smul_mul c X Q

lemma matrixMulLeft_choi_apply (Q : Matrix d d ℂ)
    (j₁ i₁ j₂ i₂ : d) :
    (matrixMulLeft Q).choi_matrix (j₁, i₁) (j₂, i₂) =
      Q j₁ i₁ * if i₂ = j₂ then 1 else 0 := by
  by_cases h : i₂ = j₂
  · subst j₂
    simp [MatrixMap.choi_matrix, matrixMulLeft, Matrix.mul_apply, Matrix.single]
  · simp [MatrixMap.choi_matrix, matrixMulLeft, Matrix.mul_apply, Matrix.single, h]

lemma matrixMulRight_choi_apply (Q : Matrix d d ℂ)
    (j₁ i₁ j₂ i₂ : d) :
    (matrixMulRight Q).choi_matrix (j₁, i₁) (j₂, i₂) =
      (if j₁ = i₁ then 1 else 0) * Q i₂ j₂ := by
  by_cases h : j₁ = i₁
  · subst i₁
    simp [MatrixMap.choi_matrix, matrixMulRight, Matrix.mul_apply, Matrix.single]
  · simp [MatrixMap.choi_matrix, matrixMulRight, Matrix.mul_apply, Matrix.single, h, eq_comm]

lemma matrixMulLeft_isChoiQuadraticNull (Q : Matrix d d ℂ) :
    IsChoiQuadraticNull (matrixMulLeft Q) := by
  intro x hx
  have hdiag : ∑ i : d, star (x (i, i)) = 0 := by
    simpa [maxEntangledVector, dotProduct, Fintype.sum_prod_type, Finset.sum_ite_eq'] using hx
  have hdiag' : ∑ i : d, x (i, i) = 0 := by
    have h := congrArg star hdiag
    simpa [map_sum] using h
  have hentry (j₁ i₁ j₂ i₂ : d) :
      (matrixMulLeft Q).choi_matrix (j₁, i₁) (j₂, i₂) =
        Q j₁ i₁ * if i₂ = j₂ then 1 else 0 := by
    by_cases h : i₂ = j₂
    · subst j₂
      simp [MatrixMap.choi_matrix, matrixMulLeft, Matrix.mul_apply, Matrix.single]
    · simp [MatrixMap.choi_matrix, matrixMulLeft, Matrix.mul_apply, Matrix.single, h]
  simp [Matrix.mulVec, dotProduct, hentry, Fintype.sum_prod_type, Finset.sum_ite_eq',
    ← Finset.mul_sum, hdiag']

lemma matrixMulRight_isChoiQuadraticNull (Q : Matrix d d ℂ) :
    IsChoiQuadraticNull (matrixMulRight Q) := by
  intro x hx
  have hdiag : ∑ i : d, star (x (i, i)) = 0 := by
    simpa [maxEntangledVector, dotProduct, Fintype.sum_prod_type, Finset.sum_ite_eq'] using hx
  have hentry (j₁ i₁ j₂ i₂ : d) :
      (matrixMulRight Q).choi_matrix (j₁, i₁) (j₂, i₂) =
        (if j₁ = i₁ then 1 else 0) * Q i₂ j₂ := by
    by_cases h : j₁ = i₁
    · subst i₁
      simp [MatrixMap.choi_matrix, matrixMulRight, Matrix.mul_apply, Matrix.single]
    · simp [MatrixMap.choi_matrix, matrixMulRight, Matrix.mul_apply, Matrix.single, h, eq_comm]
  simp [Matrix.mulVec, dotProduct, hentry, Fintype.sum_prod_type]
  calc
    (∑ x₁, star (x (x₁, x₁)) * (∑ x₂, ∑ i, Q i x₂ * x (x₂, i))) =
        (∑ x₁, star (x (x₁, x₁))) * (∑ x₂, ∑ i, Q i x₂ * x (x₂, i)) := by
          rw [Finset.sum_mul]
    _ = 0 := by rw [hdiag, zero_mul]

/-- A single Heisenberg Kraus term `X ↦ V⋆ X V`. -/
def matrixJumpTerm (V : Matrix d d ℂ) : MatrixMap d d ℂ where
  toFun X := V.conjTranspose * X * V
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

/-- A single Schrödinger Kraus term `X ↦ V X V⋆`. -/
def matrixSchrodingerJumpTerm (V : Matrix d d ℂ) : MatrixMap d d ℂ where
  toFun X := V * X * V.conjTranspose
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp

lemma matrixJumpMap_eq_sum_jumpTerm (V : ι → Matrix d d ℂ) :
    matrixJumpMap V = ∑ i, matrixJumpTerm (V i) := by
  ext X
  simp [matrixJumpMap_apply, matrixJumpTerm, Matrix.mul_assoc]

lemma matrixJumpTerm_dual (V : Matrix d d ℂ) :
    MatrixMap.dual (matrixJumpTerm V) = matrixSchrodingerJumpTerm V := by
  apply MatrixMap.dual_unique
  intro A B
  simp [matrixJumpTerm, matrixSchrodingerJumpTerm]
  calc
    (V.conjTranspose * A * V * B).trace =
        (V.conjTranspose * (A * V) * B).trace := by
      simp only [Matrix.mul_assoc]
    _ = (B * V.conjTranspose * (A * V)).trace := by
      exact Matrix.trace_mul_cycle V.conjTranspose (A * V) B
    _ = (B * V.conjTranspose * A * V).trace := by
      simp only [Matrix.mul_assoc]
    _ = (B * V.conjTranspose * (A * V)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (A * V * B * V.conjTranspose).trace := by
      exact Matrix.trace_mul_cycle B V.conjTranspose (A * V)
    _ = (A * (V * B * V.conjTranspose)).trace := by
      simp only [Matrix.mul_assoc]

lemma matrixMulLeft_dual (Q : Matrix d d ℂ) :
    MatrixMap.dual (matrixMulLeft Q) = matrixMulRight Q := by
  apply MatrixMap.dual_unique
  intro A B
  simp [matrixMulLeft, matrixMulRight]
  calc
    (Q * A * B).trace = ((Q * A) * B).trace := by
      simp only [Matrix.mul_assoc]
    _ = (B * Q * A).trace := by
      exact Matrix.trace_mul_cycle Q A B
    _ = (B * (Q * A)).trace := by
      simp only [Matrix.mul_assoc]
    _ = (A * B * Q).trace := by
      simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle B Q A)
    _ = (A * (B * Q)).trace := by
      simp only [Matrix.mul_assoc]

lemma matrixMulRight_dual (Q : Matrix d d ℂ) :
    MatrixMap.dual (matrixMulRight Q) = matrixMulLeft Q := by
  apply MatrixMap.dual_unique
  intro A B
  simp [matrixMulLeft, matrixMulRight]
  simp [Matrix.mul_assoc]

lemma matrixJumpTerm_isHermitianPreserving (V : Matrix d d ℂ) :
    MatrixMap.IsHermitianPreserving (matrixJumpTerm V) := by
  intro X hX
  change (V.conjTranspose * X * V).conjTranspose = V.conjTranspose * X * V
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hX]
  simp [Matrix.mul_assoc]

@[nolint unusedArguments]
lemma matrixMulLeft_add_right_isHermitianPreserving
    (Q : Matrix d d ℂ) (hQ : Q.conjTranspose = Q) :
    MatrixMap.IsHermitianPreserving (matrixMulLeft Q + matrixMulRight Q) := by
  intro X hX
  change (Q * X + X * Q).conjTranspose = Q * X + X * Q
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hX, hQ]
  ac_rfl

@[nolint unusedArguments]
lemma matrixHamiltonianPart_isHermitianPreserving
    (H : Matrix d d ℂ) (hH : H.conjTranspose = H) :
    MatrixMap.IsHermitianPreserving (Complex.I • (matrixMulLeft H - matrixMulRight H)) := by
  intro X hX
  change (Complex.I • (H * X - X * H)).conjTranspose = Complex.I • (H * X - X * H)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, hX, hH]
  have hI : star Complex.I = -Complex.I := by norm_num
  rw [hI]
  module

/-- A finite-dimensional Heisenberg GKSL generator.

The Hamiltonian is supplied with a self-adjointness proof.  The expression is written directly as
a matrix map so it can be compared with Choi matrices and differentiated in finite dimension. -/
noncomputable def matrixLindbladGenerator (H : Matrix d d ℂ) (_hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) : MatrixMap d d ℂ :=
  Complex.I • (matrixMulLeft H - matrixMulRight H) +
    ∑ i, (matrixJumpTerm (V i) -
      (2 : ℂ)⁻¹ • (matrixMulLeft ((V i).conjTranspose * V i) +
        matrixMulRight ((V i).conjTranspose * V i)))

@[simp]
lemma matrixLindbladGenerator_apply (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) (X : Matrix d d ℂ) :
    matrixLindbladGenerator H hH V X =
      Complex.I • (H * X - X * H) +
        ∑ i, ((V i).conjTranspose * X * V i -
          (2 : ℂ)⁻¹ • ((V i).conjTranspose * V i * X +
            X * (V i).conjTranspose * V i)) := by
    simp [matrixLindbladGenerator, matrixMulLeft, matrixMulRight, matrixJumpTerm,
      Matrix.mul_assoc]

lemma matrixLindbladGenerator_apply_one (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) :
    matrixLindbladGenerator H hH V 1 = 0 := by
  simp only [matrixLindbladGenerator_apply, Matrix.mul_one, Matrix.one_mul, sub_self,
    smul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← two_smul ℂ]
  simp [smul_smul]

/-- A finite-dimensional matrix generator is GKSL if it has a self-adjoint Hamiltonian and a
finite noise family in the standard Heisenberg form.  The canonical noise index `d × d` is used
here because every completely positive matrix map admits a representation with that index. -/
def IsGKSLGenerator (L : MatrixMap d d ℂ) (ι : Type*) [Fintype ι] : Prop :=
  ∃ (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ), L = matrixLindbladGenerator H hH V

/-- The canonical remainder condition for a Heisenberg generator.  The jump map `J` contributes
`J(1)` to the anticommutator term; the only freedom left in the remainder is the self-adjoint
Hamiltonian commutator. -/
def IsLindbladRemainder (L J : MatrixMap d d ℂ) : Prop :=
  ∃ H : Matrix d d ℂ, H.conjTranspose = H ∧
    L = J + Complex.I • (matrixMulLeft H - matrixMulRight H) -
      (2 : ℂ)⁻¹ • (matrixMulLeft (J 1) + matrixMulRight (J 1))

lemma matrixLindbladGenerator_eq_of_matrixJumpMap
    (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) :
    matrixLindbladGenerator H hH V =
      matrixJumpMap V + Complex.I • (matrixMulLeft H - matrixMulRight H) -
        (2 : ℂ)⁻¹ •
          (matrixMulLeft (matrixJumpMap V 1) + matrixMulRight (matrixJumpMap V 1)) := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [matrixJumpMap_apply_one, matrixLindbladGenerator_apply, matrixJumpMap_apply]
  simp [matrixMulLeft, matrixMulRight, Matrix.mul_assoc, Matrix.sum_mul, Matrix.mul_sum,
    Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  module

lemma exists_matrixLindbladGenerator_of_isLindbladRemainder
    (L J : MatrixMap d d ℂ) (hJ : J.IsCompletelyPositive)
    (hrem : IsLindbladRemainder L J) :
    IsGKSLGenerator L (d × d) := by
  obtain ⟨H, hH, hEq⟩ := hrem
  obtain ⟨V, hV⟩ := isCompletelyPositive_exists_matrixJumpMap J hJ
  refine ⟨H, hH, V, ?_⟩
  rw [hV] at hEq
  exact hEq.trans (matrixLindbladGenerator_eq_of_matrixJumpMap H hH V).symm

lemma matrixLindbladGenerator_isConditionallyCompletelyPositive
    (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) :
    IsConditionallyCompletelyPositive (matrixLindbladGenerator H hH V) := by
  have hjump : IsConditionallyCompletelyPositive (∑ i, matrixJumpTerm (V i)) := by
    rw [← matrixJumpMap_eq_sum_jumpTerm]
    exact matrixJumpMap_isConditionallyCompletelyPositive V
  have hham : IsChoiQuadraticNull
      (Complex.I • (matrixMulLeft H - matrixMulRight H)) := by
    exact (matrixMulLeft_isChoiQuadraticNull H).sub
      (matrixMulRight_isChoiQuadraticNull H) |>.smul Complex.I
  have hcorrection : IsChoiQuadraticNull
      (∑ i, (2 : ℂ)⁻¹ •
        (matrixMulLeft ((V i).conjTranspose * V i) +
          matrixMulRight ((V i).conjTranspose * V i))) := by
    apply IsChoiQuadraticNull.finset_sum
    intro i
    apply IsChoiQuadraticNull.smul
    exact (matrixMulLeft_isChoiQuadraticNull _).add
      (matrixMulRight_isChoiQuadraticNull _)
  have hsplit :
      Complex.I • (matrixMulLeft H - matrixMulRight H) +
          ∑ i, (matrixJumpTerm (V i) - (2 : ℂ)⁻¹ •
            (matrixMulLeft ((V i).conjTranspose * V i) +
              matrixMulRight ((V i).conjTranspose * V i))) =
        (∑ i, matrixJumpTerm (V i)) +
          (Complex.I • (matrixMulLeft H - matrixMulRight H) -
            ∑ i, (2 : ℂ)⁻¹ •
              (matrixMulLeft ((V i).conjTranspose * V i) +
                matrixMulRight ((V i).conjTranspose * V i))) := by
    apply LinearMap.ext
    intro X
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.sum_apply]
    rw [Finset.sum_sub_distrib]
    abel
  rw [matrixLindbladGenerator, hsplit]
  exact hjump.add_null (hham.sub hcorrection)

lemma matrixLindbladGenerator_isHermitianPreserving
    (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) :
    MatrixMap.IsHermitianPreserving (matrixLindbladGenerator H hH V) := by
  intro X hX
  rw [matrixLindbladGenerator_apply]
  apply Matrix.IsHermitian.add
  · exact matrixHamiltonianPart_isHermitianPreserving H hH hX
  · rw [Matrix.IsHermitian]
    simp only [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Matrix.IsHermitian.sub
    · exact matrixJumpTerm_isHermitianPreserving (V i) hX
    · apply Matrix.IsHermitian.smul
      · simpa [matrixMulLeft, matrixMulRight, Matrix.mul_assoc] using
          (matrixMulLeft_add_right_isHermitianPreserving ((V i).conjTranspose * V i)
            (by simp [Matrix.conjTranspose_mul]) hX)
      · change star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹
        norm_num

/-- Every finite-dimensional GKSL expression is an infinitesimal Heisenberg quantum Markov
generator. -/
noncomputable def matrixLindbladGenerator.toHeisenbergGenerator
    (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) : FiniteDimensionalHeisenbergGenerator d :=
  { map := matrixLindbladGenerator H hH V
    is_unital_infinitesimal := by
      exact matrixLindbladGenerator_apply_one H hH V
    is_hermitian_preserving :=
      matrixLindbladGenerator_isHermitianPreserving H hH V
    is_conditionally_completely_positive :=
      matrixLindbladGenerator_isConditionallyCompletelyPositive H hH V }

/-- The Schrödinger-picture generator dual to a Heisenberg GKSL expression. -/
noncomputable def matrixSchrodingerGenerator (H : Matrix d d ℂ) (_hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) : MatrixMap d d ℂ :=
  (-Complex.I) • (matrixMulLeft H - matrixMulRight H) +
    ∑ i, (matrixSchrodingerJumpTerm (V i) -
      (2 : ℂ)⁻¹ • (matrixMulLeft ((V i).conjTranspose * V i) +
        matrixMulRight ((V i).conjTranspose * V i)))

@[simp]
lemma matrixSchrodingerGenerator_apply (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) (X : Matrix d d ℂ) :
    matrixSchrodingerGenerator H hH V X =
      (-Complex.I) • (H * X - X * H) +
        ∑ i, (V i * X * (V i).conjTranspose -
          (2 : ℂ)⁻¹ • ((V i).conjTranspose * V i * X +
            X * (V i).conjTranspose * V i)) := by
  simp [matrixSchrodingerGenerator, matrixMulLeft, matrixMulRight,
    matrixSchrodingerJumpTerm, Matrix.mul_assoc]

lemma matrixSchrodingerGenerator_isTraceAnnihilating
    (H : Matrix d d ℂ) (hH : H.conjTranspose = H) (V : ι → Matrix d d ℂ) :
    IsTraceAnnihilating (matrixSchrodingerGenerator H hH V) := by
  intro X
  rw [matrixSchrodingerGenerator_apply]
  simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_sum,
    Matrix.mul_assoc]
  have hham : (H * X).trace = (X * H).trace :=
    Matrix.trace_mul_comm H X
  have hjump (i : ι) :
      (V i * (X * (V i).conjTranspose)).trace =
        ((V i).conjTranspose * (V i * X)).trace := by
    exact Matrix.trace_mul_cycle' (V i) X (V i).conjTranspose
  have hright (i : ι) :
      (X * ((V i).conjTranspose * V i)).trace =
        ((V i).conjTranspose * (V i * X)).trace := by
    rw [Matrix.trace_mul_comm]
    simp [Matrix.mul_assoc]
  rw [hham]
  simp only [sub_self, smul_zero, zero_add]
  apply Finset.sum_eq_zero
  intro i hi
  rw [hjump i, hright i]
  simp only [smul_eq_mul]
  ring

lemma matrixLindbladGenerator_dual
    (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) :
    MatrixMap.dual (matrixLindbladGenerator H hH V) =
      matrixSchrodingerGenerator H hH V := by
  apply MatrixMap.dual_unique
  intro A B
  rw [matrixLindbladGenerator_apply, matrixSchrodingerGenerator_apply]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_sum, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_sub, Matrix.trace_sum, Finset.sum_mul, Matrix.mul_assoc]
  congr 1
  · have hcyc₁ : (H * (A * B)).trace = (A * (B * H)).trace := by
      calc
        (H * (A * B)).trace = (H * A * B).trace := by simp [Matrix.mul_assoc]
        _ = (B * H * A).trace := by exact Matrix.trace_mul_cycle H A B
        _ = (B * (H * A)).trace := by simp [Matrix.mul_assoc]
        _ = (A * B * H).trace := by
          simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_cycle B H A)
        _ = (A * (B * H)).trace := by simp [Matrix.mul_assoc]
    rw [hcyc₁]
    simp only [smul_eq_mul]
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    have hjump :
        ((V i).conjTranspose * (A * (V i * B))).trace =
          (A * (V i * (B * (V i).conjTranspose))).trace := by
      have h := MatrixMap.Dual.trace_eq (matrixJumpTerm (V i)) A B
      rw [matrixJumpTerm_dual] at h
      simpa [matrixJumpTerm, matrixSchrodingerJumpTerm, Matrix.mul_assoc] using h
    have hleft :
        ((V i).conjTranspose * (V i * (A * B))).trace =
          (A * (B * ((V i).conjTranspose * V i))).trace := by
      have h := MatrixMap.Dual.trace_eq
        (matrixMulLeft ((V i).conjTranspose * V i)) A B
      rw [matrixMulLeft_dual] at h
      simpa [matrixMulLeft, matrixMulRight, Matrix.mul_assoc] using h
    rw [hjump, hleft]
    simp [add_comm]

lemma matrixLindbladGenerator_toSchrodingerGenerator_map
    (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) :
    (matrixLindbladGenerator.toHeisenbergGenerator H hH V).toSchrodingerGenerator.map =
      matrixSchrodingerGenerator H hH V := by
  change MatrixMap.dual (matrixLindbladGenerator H hH V) =
    matrixSchrodingerGenerator H hH V
  exact matrixLindbladGenerator_dual H hH V

lemma matrixLindbladGenerator_isGKSLGenerator
    (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
    (V : ι → Matrix d d ℂ) :
    IsGKSLGenerator (matrixLindbladGenerator H hH V) ι :=
  ⟨H, hH, V, rfl⟩

lemma isGKSLGenerator_isUnital
    (L : MatrixMap d d ℂ) (hL : IsGKSLGenerator L ι) : IsUnitalInfinitesimal L := by
  obtain ⟨H, hH, V, rfl⟩ := hL
  exact matrixLindbladGenerator_apply_one H hH V

lemma isGKSLGenerator_isHermitianPreserving
    (L : MatrixMap d d ℂ) (hL : IsGKSLGenerator L ι) : MatrixMap.IsHermitianPreserving L := by
  obtain ⟨H, hH, V, rfl⟩ := hL
  exact matrixLindbladGenerator_isHermitianPreserving H hH V

lemma isGKSLGenerator_isConditionallyCompletelyPositive
    (L : MatrixMap d d ℂ) (hL : IsGKSLGenerator L ι) : IsConditionallyCompletelyPositive L := by
  obtain ⟨H, hH, V, rfl⟩ := hL
  exact matrixLindbladGenerator_isConditionallyCompletelyPositive H hH V

/-! ### Choi compression

The conditional Choi inequality says that the Choi matrix is positive on the orthogonal
complement of the maximally-entangled vector.  The following definitions make the corresponding
orthogonal compression explicit.  They are the finite-dimensional core of the GKSL converse.
-/

section ChoiCompression

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-- The squared norm of the unnormalised maximally-entangled vector. -/
def maxEntangledNormSq : ℂ := (Fintype.card d : ℂ)

@[nolint unusedArguments]
lemma maxEntangledVector_normSq :
    (star (maxEntangledVector (d := d))) ⬝ᵥ maxEntangledVector = maxEntangledNormSq (d := d) := by
  simp [maxEntangledVector, maxEntangledNormSq, dotProduct, Fintype.sum_prod_type,
    Finset.sum_ite_eq']

@[nolint unusedArguments]
lemma maxEntangledNormSq_ne_zero : maxEntangledNormSq (d := d) ≠ 0 := by
  simp [maxEntangledNormSq, Fintype.card_ne_zero]

/-- The orthogonal projection onto the complement of the maximally-entangled line. -/
noncomputable def maxEntangledComplementProjection :
    Matrix (d × d) (d × d) ℂ :=
  1 - (maxEntangledNormSq (d := d))⁻¹ •
    Matrix.vecMulVec (maxEntangledVector (d := d)) (star (maxEntangledVector (d := d)))

/-- The rank-one projection onto the maximally-entangled line. -/
noncomputable def maxEntangledLineProjection :
    Matrix (d × d) (d × d) ℂ :=
  (maxEntangledNormSq (d := d))⁻¹ •
    Matrix.vecMulVec (maxEntangledVector (d := d)) (star (maxEntangledVector (d := d)))

@[nolint unusedArguments]
lemma maxEntangledComplementProjection_eq_one_sub_line :
    maxEntangledComplementProjection (d := d) =
      1 - maxEntangledLineProjection (d := d) := rfl

lemma maxEntangledLineProjection_mul_self :
    maxEntangledLineProjection (d := d) * maxEntangledLineProjection (d := d) =
      maxEntangledLineProjection (d := d) := by
  ext i j
  simp [maxEntangledLineProjection, maxEntangledNormSq, Matrix.mul_apply,
    Matrix.vecMulVec, maxEntangledVector, dotProduct, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, Finset.sum_ite_eq']

@[nolint unusedArguments]
lemma maxEntangledLineProjection_isHermitian :
    (maxEntangledLineProjection (d := d)).IsHermitian := by
  rw [Matrix.IsHermitian, maxEntangledLineProjection,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec]
  simp [maxEntangledNormSq]

@[nolint unusedArguments]
lemma maxEntangledComplementProjection_apply (x : (d × d) → ℂ) :
    (maxEntangledComplementProjection (d := d)).mulVec x =
      x - (maxEntangledNormSq (d := d))⁻¹ •
        ((star (maxEntangledVector (d := d))) ⬝ᵥ x) • maxEntangledVector := by
  simp [maxEntangledComplementProjection, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.vecMulVec_mulVec, smul_smul]

lemma maxEntangledComplementProjection_orthogonal (x : (d × d) → ℂ) :
    (star (maxEntangledVector (d := d))) ⬝ᵥ
        ((maxEntangledComplementProjection (d := d)).mulVec x) = 0 := by
  rw [maxEntangledComplementProjection_apply, dotProduct_sub, dotProduct_smul,
    dotProduct_smul]
  rw [maxEntangledVector_normSq]
  simp only [smul_eq_mul]
  field_simp [maxEntangledNormSq_ne_zero]
  simp

@[nolint unusedArguments]
lemma maxEntangledComplementProjection_isHermitian :
    (maxEntangledComplementProjection (d := d)).IsHermitian := by
  rw [Matrix.IsHermitian, maxEntangledComplementProjection,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_vecMulVec]
  simp [maxEntangledNormSq]

lemma matrix_sub_compressedChoi_expansion
    (C : Matrix (d × d) (d × d) ℂ) :
    C - (maxEntangledComplementProjection (d := d)).conjTranspose * C *
        maxEntangledComplementProjection (d := d) =
      maxEntangledLineProjection (d := d) * C +
        C * maxEntangledLineProjection (d := d) -
        maxEntangledLineProjection (d := d) * C *
          maxEntangledLineProjection (d := d) := by
  rw [maxEntangledComplementProjection_isHermitian.eq,
    maxEntangledComplementProjection_eq_one_sub_line]
  noncomm_ring

/-- The `(d × d)`-block left coefficient of `C` along the maximally-entangled line. -/
noncomputable def lineLeftCoefficient (C : Matrix (d × d) (d × d) ℂ) : Matrix d d ℂ :=
  fun j i => (maxEntangledNormSq (d := d))⁻¹ *
    ∑ k : d, C (j, i) (k, k)

/-- The `(d × d)`-block right coefficient of `C` along the maximally-entangled line. -/
noncomputable def lineRightCoefficient (C : Matrix (d × d) (d × d) ℂ) : Matrix d d ℂ :=
  fun i j => (maxEntangledNormSq (d := d))⁻¹ *
    ∑ k : d, C (k, k) (j, i)

/-- The scalar coefficient of `C` along the maximally-entangled line. -/
noncomputable def lineScalarCoefficient (C : Matrix (d × d) (d × d) ℂ) : ℂ :=
  (maxEntangledNormSq (d := d))⁻¹ *
    ∑ k : d, ∑ l : d, C (k, k) (l, l)

@[nolint unusedArguments]
lemma lineProjection_mul_apply (C : Matrix (d × d) (d × d) ℂ)
    (j₁ i₁ j₂ i₂ : d) :
    (maxEntangledLineProjection (d := d) * C) (j₁, i₁) (j₂, i₂) =
      (if j₁ = i₁ then 1 else 0) * lineRightCoefficient (d := d) C i₂ j₂ := by
  by_cases h : j₁ = i₁
  · subst i₁
    simp [maxEntangledLineProjection, lineRightCoefficient, Matrix.mul_apply,
      Matrix.vecMulVec, maxEntangledVector, maxEntangledNormSq,
      Fintype.sum_prod_type, Finset.sum_ite_eq']
    rw [Finset.mul_sum]
  · simp [maxEntangledLineProjection, lineRightCoefficient, Matrix.mul_apply,
      Matrix.vecMulVec, maxEntangledVector, maxEntangledNormSq, h]

@[nolint unusedArguments]
lemma matrix_mul_lineProjection_apply (C : Matrix (d × d) (d × d) ℂ)
    (j₁ i₁ j₂ i₂ : d) :
    (C * maxEntangledLineProjection (d := d)) (j₁, i₁) (j₂, i₂) =
      lineLeftCoefficient (d := d) C j₁ i₁ * (if j₂ = i₂ then 1 else 0) := by
  by_cases h : j₂ = i₂
  · subst i₂
    simp [maxEntangledLineProjection, lineLeftCoefficient, Matrix.mul_apply,
      Matrix.vecMulVec, maxEntangledVector, maxEntangledNormSq,
      Fintype.sum_prod_type, Finset.sum_ite_eq']
    calc
      (∑ x : d, C (j₁, i₁) (x, x) * (maxEntangledNormSq (d := d))⁻¹) =
          (∑ x : d, C (j₁, i₁) (x, x)) *
            (maxEntangledNormSq (d := d))⁻¹ := by
              rw [Finset.sum_mul]
      _ = (maxEntangledNormSq (d := d))⁻¹ *
          ∑ x : d, C (j₁, i₁) (x, x) := by rw [mul_comm]
  · simp [maxEntangledLineProjection, lineLeftCoefficient, Matrix.mul_apply,
      Matrix.vecMulVec, maxEntangledVector, maxEntangledNormSq, h]

lemma line_supported_choi_of_coefficients
    (C : Matrix (d × d) (d × d) ℂ) :
    maxEntangledLineProjection (d := d) * C + C *
        maxEntangledLineProjection (d := d) -
        maxEntangledLineProjection (d := d) * C *
          maxEntangledLineProjection (d := d) =
      (matrixMulLeft (lineLeftCoefficient (d := d) C) +
        matrixMulRight (lineRightCoefficient (d := d) C) -
        matrixMulLeft (lineLeftCoefficient (d := d) (
          maxEntangledLineProjection (d := d) * C))).choi_matrix := by
  ext ⟨j₁, i₁⟩ ⟨j₂, i₂⟩
  change (maxEntangledLineProjection (d := d) * C) (j₁, i₁) (j₂, i₂) +
      (C * maxEntangledLineProjection (d := d)) (j₁, i₁) (j₂, i₂) -
      (maxEntangledLineProjection (d := d) * C *
        maxEntangledLineProjection (d := d)) (j₁, i₁) (j₂, i₂) =
    (matrixMulLeft (lineLeftCoefficient (d := d) C)).choi_matrix
        (j₁, i₁) (j₂, i₂) +
      (matrixMulRight (lineRightCoefficient (d := d) C)).choi_matrix
        (j₁, i₁) (j₂, i₂) -
      (matrixMulLeft (lineLeftCoefficient (d := d) (
        maxEntangledLineProjection (d := d) * C))).choi_matrix
        (j₁, i₁) (j₂, i₂)
  rw [matrixMulLeft_choi_apply, matrixMulRight_choi_apply,
    matrixMulLeft_choi_apply]
  rw [lineProjection_mul_apply, matrix_mul_lineProjection_apply,
    matrix_mul_lineProjection_apply]
  simp [eq_comm] <;> ring

lemma lineLeftCoefficient_lineProjection_mul (C : Matrix (d × d) (d × d) ℂ) :
    lineLeftCoefficient (d := d) (maxEntangledLineProjection (d := d) * C) =
      ((maxEntangledNormSq (d := d))⁻¹ * lineScalarCoefficient (d := d) C) •
        (1 : Matrix d d ℂ) := by
  ext j i
  by_cases h : j = i
  · subst i
    simp only [lineLeftCoefficient, Matrix.smul_apply, Matrix.one_apply, dite_true,
      if_true, mul_one, lineProjection_mul_apply]
    simp [lineRightCoefficient, lineScalarCoefficient, maxEntangledNormSq,
      maxEntangledVector, Fintype.sum_prod_type, Finset.sum_ite_eq']
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_comm]
  · simp [lineLeftCoefficient, lineProjection_mul_apply, h]

@[nolint unusedArguments]
lemma lineRightCoefficient_eq_conjTranspose_lineLeftCoefficient
    (C : Matrix (d × d) (d × d) ℂ) (hC : C.IsHermitian) :
    lineRightCoefficient (d := d) C =
      (lineLeftCoefficient (d := d) C).conjTranspose := by
  ext i j
  simp only [lineRightCoefficient, lineLeftCoefficient, Matrix.conjTranspose_apply,
    star_mul, star_sum]
  have hentry : ∀ k : d, star (C (j, i) (k, k)) = C (k, k) (j, i) := by
    intro k
    have h := congr_fun (congr_fun hC.eq (j, i)) (k, k)
    simpa [Matrix.conjTranspose_apply] using (congrArg star h).symm
  simp_rw [hentry]
  simp [maxEntangledNormSq]
  ring

@[nolint unusedArguments]
lemma lineScalarCoefficient_isSelfAdjoint
    (C : Matrix (d × d) (d × d) ℂ) (hC : C.IsHermitian) :
    star (lineScalarCoefficient (d := d) C) =
      lineScalarCoefficient (d := d) C := by
  unfold lineScalarCoefficient
  rw [star_mul, star_sum]
  simp only [star_sum]
  have hentry : ∀ k l : d, star (C (k, k) (l, l)) = C (l, l) (k, k) := by
    intro k l
    have h := congr_fun (congr_fun hC.eq (k, k)) (l, l)
    simpa [Matrix.conjTranspose_apply] using (congrArg star h).symm
  simp_rw [hentry]
  rw [Finset.sum_comm]
  simp [maxEntangledNormSq]
  ring

/-- The Hermitian, scalar-multiple-of-identity part of `lineLeftCoefficient`. -/
noncomputable def lineCorrectionCoefficient
    (C : Matrix (d × d) (d × d) ℂ) : Matrix d d ℂ :=
  ((2 : ℂ)⁻¹ * ((maxEntangledNormSq (d := d))⁻¹ *
    lineScalarCoefficient (d := d) C)) • (1 : Matrix d d ℂ)

/-- What's left of `lineLeftCoefficient` after subtracting its correction term. -/
noncomputable def lineRemainderCoefficient
    (C : Matrix (d × d) (d × d) ℂ) : Matrix d d ℂ :=
  lineLeftCoefficient (d := d) C - lineCorrectionCoefficient (d := d) C

lemma lineCorrectionCoefficient_isSelfAdjoint
    (C : Matrix (d × d) (d × d) ℂ) (hC : C.IsHermitian) :
    (lineCorrectionCoefficient (d := d) C).conjTranspose =
      lineCorrectionCoefficient (d := d) C := by
  unfold lineCorrectionCoefficient
  rw [Matrix.conjTranspose_smul]
  simp [lineScalarCoefficient_isSelfAdjoint C hC, maxEntangledNormSq]

/-- The line-projection-supported part of the Choi matrix, written as a `matrixMulLeft +
matrixMulRight` correction map. -/
noncomputable def lineSupportedRemainderMap
    (C : Matrix (d × d) (d × d) ℂ) : MatrixMap d d ℂ :=
  matrixMulLeft (lineLeftCoefficient (d := d) C) +
    matrixMulRight (lineRightCoefficient (d := d) C) -
    matrixMulLeft (lineLeftCoefficient (d := d) (
      maxEntangledLineProjection (d := d) * C))

lemma lineSupportedRemainderMap_eq_lineRemainder
    (C : Matrix (d × d) (d × d) ℂ) (hC : C.IsHermitian) :
    lineSupportedRemainderMap (d := d) C =
      matrixMulLeft (lineRemainderCoefficient (d := d) C) +
        matrixMulRight (lineRemainderCoefficient (d := d) C).conjTranspose := by
  have hright := lineRightCoefficient_eq_conjTranspose_lineLeftCoefficient C hC
  have hleft := lineLeftCoefficient_lineProjection_mul C
  have hscalar := lineScalarCoefficient_isSelfAdjoint C hC
  apply LinearMap.ext
  intro X
  simp only [lineSupportedRemainderMap, lineRemainderCoefficient,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  rw [hright, hleft]
  simp [lineCorrectionCoefficient, matrixMulLeft, matrixMulRight, hscalar,
    maxEntangledNormSq]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]
  module

lemma lineSupportedRemainderMap_eq_hamiltonianForm
    (C : Matrix (d × d) (d × d) ℂ) (hC : C.IsHermitian) :
    ∃ Q : Matrix d d ℂ,
      lineSupportedRemainderMap (d := d) C =
        matrixMulLeft Q + matrixMulRight Q.conjTranspose := by
  refine ⟨lineRemainderCoefficient (d := d) C, ?_⟩
  exact lineSupportedRemainderMap_eq_lineRemainder C hC

@[nolint unusedArguments]
lemma matrixMap_map_star_of_isHermitianPreserving
    (L : MatrixMap d d ℂ) (hL : MatrixMap.IsHermitianPreserving L) :
    ∀ X : Matrix d d ℂ, L (star X) = star (L X) := by
  intro X
  let A : Matrix d d ℂ := (2 : ℂ)⁻¹ • (X + X.conjTranspose)
  let B : Matrix d d ℂ := (2 : ℂ)⁻¹ • (Complex.I • (X - X.conjTranspose))
  have hA : A.IsHermitian := by
    dsimp [A]
    apply Matrix.IsHermitian.smul (Matrix.isHermitian_add_transpose_self X)
    simp
  have hB : B.IsHermitian := by
    dsimp [B]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_sub]
    simp [smul_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hi : Complex.I * ((2 : ℂ)⁻¹ * Complex.I) = -(2 : ℂ)⁻¹ := by
    calc
      Complex.I * ((2 : ℂ)⁻¹ * Complex.I) =
          (2 : ℂ)⁻¹ * (Complex.I * Complex.I) := by ring
      _ = -(2 : ℂ)⁻¹ := by rw [Complex.I_mul_I]; ring
  have htwo : (2 : ℂ)⁻¹ + (2 : ℂ)⁻¹ = 1 := by norm_num
  have hXA : X = A + (-Complex.I) • B := by
    dsimp [A, B]
    simp [smul_add, smul_sub, smul_smul, hi]
    rw [← add_smul, htwo, one_smul]
  have hXstar : star X = A + Complex.I • B := by
    calc
      star X = star (A + (-Complex.I) • B) := congrArg star hXA
      _ = A + Complex.I • B := by
        change (A + (-Complex.I) • B).conjTranspose = A + Complex.I • B
        rw [Matrix.conjTranspose_add A ((-Complex.I) • B),
          Matrix.conjTranspose_smul (-Complex.I) B, hA.eq, hB.eq]
        simp
  calc
    L (star X) = L (A + Complex.I • B) := congrArg L hXstar
    _ = L A + Complex.I • L B := by
      simp only [map_add, map_smul]
    _ = (L A).conjTranspose + Complex.I • (L B).conjTranspose := by
      rw [(hL hA).eq, (hL hB).eq]
    _ = (L A + (-Complex.I) • L B).conjTranspose := by
      symm
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
      simp
    _ = (L (A + (-Complex.I) • B)).conjTranspose := by
      simp only [map_add, map_smul]
    _ = (L X).conjTranspose := by
      exact congrArg Matrix.conjTranspose (congrArg L hXA).symm
    _ = star (L X) := (Matrix.star_eq_conjTranspose (L X)).symm

lemma choi_matrix_isHermitian_of_isHermitianPreserving
    (L : MatrixMap d d ℂ) (hL : MatrixMap.IsHermitianPreserving L) :
    L.choi_matrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  rintro ⟨j₁, i₁⟩ ⟨j₂, i₂⟩
  rw [MatrixMap.choi_matrix, MatrixMap.choi_matrix]
  have hstar := matrixMap_map_star_of_isHermitianPreserving L hL
    (Matrix.single i₂ i₁ (1 : ℂ))
  rw [Matrix.star_eq_conjTranspose] at hstar
  have he : (Matrix.single i₂ i₁ (1 : ℂ)).conjTranspose =
      Matrix.single i₁ i₂ (1 : ℂ) := by
    simp [Matrix.conjTranspose_single]
  rw [he] at hstar
  simpa [Matrix.conjTranspose_apply] using
    congr_fun (congr_fun hstar.symm j₁) j₂

/-- The Choi matrix of `L`, compressed onto the maximally-entangled line's orthogonal
complement. -/
noncomputable def compressedChoi (L : MatrixMap d d ℂ) :
    Matrix (d × d) (d × d) ℂ :=
  (maxEntangledComplementProjection (d := d)).conjTranspose *
    L.choi_matrix * maxEntangledComplementProjection (d := d)

@[nolint unusedArguments]
lemma compressedChoi_apply_quadratic (L : MatrixMap d d ℂ)
    (x : (d × d) → ℂ) :
    (star x) ⬝ᵥ ((compressedChoi (d := d) L).mulVec x) =
      (star ((maxEntangledComplementProjection (d := d)).mulVec x)) ⬝ᵥ
        (L.choi_matrix.mulVec ((maxEntangledComplementProjection (d := d)).mulVec x)) := by
  simp only [compressedChoi]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose, star_star]

lemma compressedChoi_isHermitian_of_isHermitianPreserving
    (L : MatrixMap d d ℂ) (hL : MatrixMap.IsHermitianPreserving L) :
    (compressedChoi (d := d) L).IsHermitian := by
  apply Matrix.isHermitian_conjTranspose_mul_mul
  exact choi_matrix_isHermitian_of_isHermitianPreserving L hL

lemma compressedChoi_posSemidef_of_isConditionallyCompletelyPositive
    (L : MatrixMap d d ℂ) (hL : MatrixMap.IsHermitianPreserving L)
    (hccp : IsConditionallyCompletelyPositive L) :
    (compressedChoi (d := d) L).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (compressedChoi_isHermitian_of_isHermitianPreserving L hL)
  intro x
  rw [compressedChoi_apply_quadratic]
  apply hccp _
  rw [Matrix.star_dotProduct]
  simp [maxEntangledComplementProjection_orthogonal]

/-- The matrix map recovered from `compressedChoi`: the jump part of a GKSL generator with the
line-supported correction removed. -/
noncomputable def compressedJumpMap (L : MatrixMap d d ℂ) : MatrixMap d d ℂ :=
  MatrixMap.of_choi_matrix (compressedChoi (d := d) L)

lemma compressedJumpMap_isCompletelyPositive
    (L : MatrixMap d d ℂ) (hL : MatrixMap.IsHermitianPreserving L)
    (hccp : IsConditionallyCompletelyPositive L) :
    (compressedJumpMap (d := d) L).IsCompletelyPositive := by
  rw [MatrixMap.choi_PSD_iff_CP_map]
  simpa [compressedJumpMap] using
    compressedChoi_posSemidef_of_isConditionallyCompletelyPositive L hL hccp

@[simp, nolint unusedArguments]
lemma compressedJumpMap_choi_matrix (L : MatrixMap d d ℂ) :
    (compressedJumpMap (d := d) L).choi_matrix = compressedChoi (d := d) L := by
  simp [compressedJumpMap]

lemma maxEntangledComplementProjection_fix_of_orthogonal
    (x : (d × d) → ℂ)
    (hx : (star x) ⬝ᵥ maxEntangledVector = 0) :
    (maxEntangledComplementProjection (d := d)).mulVec x = x := by
  rw [maxEntangledComplementProjection_apply]
  have hx' : (star maxEntangledVector) ⬝ᵥ x = 0 := by
    calc
      (star maxEntangledVector) ⬝ᵥ x = star ((star x) ⬝ᵥ maxEntangledVector) :=
        Matrix.star_dotProduct _ _
      _ = 0 := by simp [hx]
  simp [hx']

@[nolint unusedArguments]
lemma compressedJumpMap_remainder_isChoiQuadraticNull
    (L : MatrixMap d d ℂ) (hL : MatrixMap.IsHermitianPreserving L)
    (hccp : IsConditionallyCompletelyPositive L) :
    IsChoiQuadraticNull (L - compressedJumpMap (d := d) L) := by
  intro x hx
  have hfix := maxEntangledComplementProjection_fix_of_orthogonal x hx
  have hquadJ :
      (star x) ⬝ᵥ ((compressedJumpMap (d := d) L).choi_matrix.mulVec x) =
        (star x) ⬝ᵥ (L.choi_matrix.mulVec x) := by
    rw [compressedJumpMap_choi_matrix, compressedChoi_apply_quadratic]
    rw [hfix]
  have hchoi : (L - compressedJumpMap (d := d) L).choi_matrix =
      L.choi_matrix - (compressedJumpMap (d := d) L).choi_matrix := by
    ext ⟨j₁, i₁⟩ ⟨j₂, i₂⟩
    change (L (Matrix.single i₁ i₂ (1 : ℂ)) -
        compressedJumpMap (d := d) L (Matrix.single i₁ i₂ (1 : ℂ))) j₁ j₂ =
      L (Matrix.single i₁ i₂ (1 : ℂ)) j₁ j₂ -
        compressedJumpMap (d := d) L (Matrix.single i₁ i₂ (1 : ℂ)) j₁ j₂
    rfl
  rw [hchoi, Matrix.sub_mulVec, dotProduct_sub, hquadJ, sub_self]

lemma compressedJumpMap_remainder_choi_line_expansion
    (L : MatrixMap d d ℂ) :
    (L - compressedJumpMap (d := d) L).choi_matrix =
      maxEntangledLineProjection (d := d) * L.choi_matrix +
        L.choi_matrix * maxEntangledLineProjection (d := d) -
        maxEntangledLineProjection (d := d) * L.choi_matrix *
          maxEntangledLineProjection (d := d) := by
  have hchoi : (L - compressedJumpMap (d := d) L).choi_matrix =
      L.choi_matrix - (compressedJumpMap (d := d) L).choi_matrix := by
    ext ⟨j₁, i₁⟩ ⟨j₂, i₂⟩
    change (L (Matrix.single i₁ i₂ (1 : ℂ)) -
        compressedJumpMap (d := d) L (Matrix.single i₁ i₂ (1 : ℂ))) j₁ j₂ =
      L (Matrix.single i₁ i₂ (1 : ℂ)) j₁ j₂ -
        compressedJumpMap (d := d) L (Matrix.single i₁ i₂ (1 : ℂ)) j₁ j₂
    rfl
  rw [hchoi, compressedJumpMap_choi_matrix]
  exact matrix_sub_compressedChoi_expansion L.choi_matrix

lemma compressedJumpMap_remainder_eq_lineSupportedRemainderMap
    (L : MatrixMap d d ℂ) :
    L - compressedJumpMap (d := d) L =
      lineSupportedRemainderMap (d := d) L.choi_matrix := by
  apply MatrixMap.choi_matrix_inj
  rw [compressedJumpMap_remainder_choi_line_expansion,
    line_supported_choi_of_coefficients]
  rfl

lemma exists_matrixJumpMap_compressedJumpMap
    (L : MatrixMap d d ℂ) (hL : MatrixMap.IsHermitianPreserving L)
    (hccp : IsConditionallyCompletelyPositive L) :
    ∃ V : (d × d) → Matrix d d ℂ,
      compressedJumpMap (d := d) L = matrixJumpMap V := by
  exact isCompletelyPositive_exists_matrixJumpMap _
    (compressedJumpMap_isCompletelyPositive L hL hccp)

lemma exists_matrixLindbladGenerator_of_isGKSLGenerator
    (L : MatrixMap d d ℂ) (hUnital : IsUnitalInfinitesimal L)
    (hHP : MatrixMap.IsHermitianPreserving L)
    (hCCP : IsConditionallyCompletelyPositive L) :
    IsGKSLGenerator L (d × d) := by
  let J : MatrixMap d d ℂ := compressedJumpMap (d := d) L
  have hJ : J.IsCompletelyPositive := by
    exact compressedJumpMap_isCompletelyPositive L hHP hCCP
  have hC : L.choi_matrix.IsHermitian :=
    choi_matrix_isHermitian_of_isHermitianPreserving L hHP
  obtain ⟨Q, hQ⟩ := lineSupportedRemainderMap_eq_hamiltonianForm L.choi_matrix hC
  have hrem : L - J = matrixMulLeft Q + matrixMulRight Q.conjTranspose := by
    calc
      L - J = lineSupportedRemainderMap (d := d) L.choi_matrix := by
        simpa [J] using compressedJumpMap_remainder_eq_lineSupportedRemainderMap L
      _ = matrixMulLeft Q + matrixMulRight Q.conjTranspose := hQ
  have hLone : L (1 : Matrix d d ℂ) = 0 := hUnital
  have hunit := congrArg (fun M : MatrixMap d d ℂ => M (1 : Matrix d d ℂ)) hrem
  have hQunit : Q + Q.conjTranspose = -(J 1) := by
    simpa [matrixMulLeft, matrixMulRight, hLone] using hunit.symm
  have hJunit : J 1 = -(Q + Q.conjTranspose) := by
    calc
      J 1 = - (-(J 1)) := by simp
      _ = -(Q + Q.conjTranspose) := by rw [← hQunit]
  let H : Matrix d d ℂ := (-(Complex.I) / 2) • (Q - Q.conjTranspose)
  have hH : H.conjTranspose = H := by
    dsimp [H]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose]
    simp
    module
  obtain ⟨V, hV⟩ := isCompletelyPositive_exists_matrixJumpMap J hJ
  refine ⟨H, hH, V, ?_⟩
  apply LinearMap.ext
  intro X
  have hremX := congrArg (fun M : MatrixMap d d ℂ => M X) hrem
  have hremX' : L X - J X = Q * X + X * Q.conjTranspose := by
    simpa [matrixMulLeft, matrixMulRight] using hremX
  calc
    L X = J X + (L X - J X) := by abel
    _ = J X + (Q * X + X * Q.conjTranspose) := by rw [hremX']
    _ = matrixLindbladGenerator H hH V X := by
      rw [matrixLindbladGenerator_eq_of_matrixJumpMap]
      rw [← hV]
      simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
      rw [hJunit]
      dsimp [H]
      simp [matrixMulLeft, matrixMulRight, Matrix.sub_mul, Matrix.mul_sub,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, Complex.I_sq]
      ring_nf
      simp only [smul_sub, smul_add, smul_smul]
      have hscalar : Complex.I * (Complex.I * (-1 / 2 : ℂ)) = (1 / 2 : ℂ) := by
        rw [← mul_assoc, Complex.I_mul_I]
        norm_num
      simp [hscalar, Matrix.add_mul, Matrix.neg_mul, Matrix.mul_add, Matrix.mul_neg]
      module

lemma isGKSLGenerator_iff
    (L : MatrixMap d d ℂ) :
    IsGKSLGenerator L (d × d) ↔
      IsUnitalInfinitesimal L ∧
        MatrixMap.IsHermitianPreserving L ∧
          IsConditionallyCompletelyPositive L := by
  constructor
  · intro hL
    exact ⟨isGKSLGenerator_isUnital L hL,
      isGKSLGenerator_isHermitianPreserving L hL,
      isGKSLGenerator_isConditionallyCompletelyPositive L hL⟩
  · rintro ⟨hUnital, hHP, hCCP⟩
    exact exists_matrixLindbladGenerator_of_isGKSLGenerator
      L hUnital hHP hCCP

lemma HasFiniteDimensionalHeisenbergGenerator.isGKSLGenerator
    {Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d}
    (G : HasFiniteDimensionalHeisenbergGenerator Φ) :
    IsGKSLGenerator G.map (d × d) := by
  exact exists_matrixLindbladGenerator_of_isGKSLGenerator
    G.map G.is_unital_infinitesimal G.is_hermitian_preserving
      (Φ.hasChoiGenerator_isConditionallyCompletelyPositive G.map G.has_choi_generator)

/-- The finite-dimensional GKSL converse in its explicit generator form.

The semigroup supplies the dynamical hypotheses (complete positivity, unitality, the semigroup
law, and the right derivative).  The Choi compression argument then produces one self-adjoint
Hamiltonian and a finite noise family whose Lindblad expression is exactly the infinitesimal
generator.  This theorem is the reusable statement; concrete matrix bases are only used inside
the proof. -/
lemma HasFiniteDimensionalHeisenbergGenerator.exists_lindblad_generator
    {Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d}
    (G : HasFiniteDimensionalHeisenbergGenerator Φ) :
    ∃ (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
      (V : (d × d) → Matrix d d ℂ),
      G.map = matrixLindbladGenerator H hH V := by
  obtain ⟨H, hH, V, hG⟩ := G.isGKSLGenerator
  exact ⟨H, hH, V, hG⟩

lemma finite_dimensional_generator_isGKSL
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) :
    IsGKSLGenerator (finiteDimensionalGenerator Φ).map (d × d) := by
  exact (finiteDimensionalGenerator Φ).isGKSLGenerator

lemma exists_lindblad_generator_of_continuous
    (Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d) :
    ∃ (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
      (V : (d × d) → Matrix d d ℂ),
      (finiteDimensionalGenerator Φ).map = matrixLindbladGenerator H hH V := by
  exact (finiteDimensionalGenerator Φ).exists_lindblad_generator

lemma HasFiniteDimensionalHeisenbergGenerator.exists_schrodinger_lindblad
    {Φ : FiniteDimensionalHeisenbergQuantumDynamicalSemigroup d}
    (G : HasFiniteDimensionalHeisenbergGenerator Φ) :
    ∃ (H : Matrix d d ℂ) (hH : H.conjTranspose = H)
      (V : (d × d) → Matrix d d ℂ),
      MatrixMap.dual G.map = matrixSchrodingerGenerator H hH V := by
  obtain ⟨H, hH, V, hG⟩ := G.isGKSLGenerator
  refine ⟨H, hH, V, ?_⟩
  rw [hG]
  exact matrixLindbladGenerator_dual H hH V

end ChoiCompression

end OperatorAlgebra
