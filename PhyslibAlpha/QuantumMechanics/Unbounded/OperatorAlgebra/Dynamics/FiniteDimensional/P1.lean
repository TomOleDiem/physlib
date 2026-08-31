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
# Finite-dimensional GKSL algebra (part 1 of 2)

Split out of `FiniteDimensional.lean` to stay under the file-length style limit; see
`FiniteDimensional.lean` for the full module overview. This part covers the finite-dimensional
Schrodinger-picture quantum dynamical semigroup and Heisenberg-picture generator structures.
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

end OperatorAlgebra
