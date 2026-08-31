/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded
public import PhyslibAlpha.Unbounded.QuantumMechanics.Operators.Core.UnboundedExtras
public import PhyslibAlpha.Unbounded.QuantumMechanics.OperatorAlgebra.Unbounded.Core.EssentialSelfAdjointCriteria
public import Physlib.Meta.Sorry
public import Physlib.Meta.TODO.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Analytic vectors for an unbounded operator

This file states, at the level of `LinearPMap`, the hypothesis that Nelson's analytic-vector
theorem (1959) is built on: a vector `x` is *analytic* for `T : H →ₗ.[ℂ] H` if it lies in the
domain of every iterated power `Tⁿ`, and the formal exponential series `∑ ‖Tⁿx‖ tⁿ/n!` converges
for some radius `t > 0`. This is exactly Reed–Simon Vol. II's definition (§X.6); their Theorem
X.39 (Nelson's theorem) is the fact that if a symmetric operator has a *dense* set of analytic
vectors, it is essentially self-adjoint, and the corresponding joint-commutation theorem lets two
symmetric operators that commute algebraically on a common core of joint analytic vectors be
promoted to strongly commuting self-adjoint closures.

Proving the single-operator criterion in full requires constructing, for every analytic vector
`x` and small `|t|`, the locally-convergent vector-valued power series `∑ (it)ⁿ/n! Tⁿx` as a
genuine local one-parameter semigroup, showing this local semigroup is isometric (using
symmetry of `T`), and then patching countably many local pieces together into a global strongly
continuous unitary group, whose Stone generator is then identified with `T`'s closure via the
deficiency-space argument already available in `EssentialSelfAdjointCriteria.lean`. This is a
substantial, genuinely hard analytic argument (a full textbook chapter — Reed–Simon Vol. II,
§X.6, or Nelson's original 1959 Annals paper).  The finite-radius continuation, gluing, and
deficiency arguments are implemented below as a checked Lean proof.

What *is* proved here is the tractable structural content around that hard core:

## Key results

- `LinearPMap.IsAnalyticVector` : the precise Reed–Simon definition, specialized to `LinearPMap`.
- `LinearPMap.IteratesSeq.ext` and `LinearPMap.analyticExp_congr_iterates` : iterate witnesses
  and the resulting exponential orbit are independent of the chosen dependent-domain witness.
- `LinearPMap.IsAnalyticVector.smul`, `.add` : analytic vectors form a submodule of `T.domain`
  (the standard "min of the two radii" argument).
- `LinearPMap.analyticExp` and its surrounding lemmas : the radius-controlled vector-valued
  exponential series, its exact term norm, summability, zero-time value, and iterate recurrence.
- `LinearPMap.analyticExpTerm_hasDerivAt` and
  `LinearPMap.analyticExp_hasDerivAt_of_mem_half_radius` : termwise real differentiability and a
  genuine locally-uniform derivative theorem on the half-radius interval.  The latter is the
  analytic input needed before proving the local flow equation.
- `LinearPMap.analyticExp_smul_iterates` and `.analyticExp_add_iterates` : the local exponential
  is linear in scalar and additive combinations of iterate witnesses whenever a common radius
  controls the relevant majorants.  These are the algebraic comparison lemmas needed to pass from
  individual analytic vectors to their dense analytic span.
- `LinearPMap.analyticExp_mem_closure_graph`, `.analyticExp_mem_closure_domain`, and
  `.closure_analyticExp_apply` : the finite partial sums converge in the graph of the closure,
  so the local exponential is an actual closure-domain vector with the expected closure value.
- `LinearPMap.analyticExp_hasDerivAt_eq_smul_closure` and
  `LinearPMap.analyticExp_normSq_eq_normSq_zero` : the local orbit satisfies the closure-valued
  differential equation, and symmetry makes its norm square constant on the half-radius interval.
- `LinearPMap.analyticExp_eq_zero_iff` : on that same interval the local orbit is non-degenerate;
  it vanishes exactly when its initial vector does.  This is the injectivity consequence used by
  the eventual local-to-global unitary-flow construction.
- `LinearPMap.IsEntireVector` and its global-orbit lemmas : the stronger class with a factorial
  majorant at every positive radius.  For these vectors the local graph and norm arguments apply
  at every real time, providing the global-flow prototype used to isolate the remaining patching
  step in Nelson's theorem.  `LinearPMap.entireVectors` packages this class as a complex
  submodule, with proved zero, scalar, and additive closure.  The explicit
  `analyticExp_mem_closure_domain_of_entire` and `analyticExp_hasDerivAt_of_entire` lemmas expose
  the arbitrary-time closure-domain and differential facts without hiding the chosen witness.
- `LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseEntireVectors` : a complete
  deficiency-index proof for the stronger dense-entire-vector hypothesis.  Both signs are handled
  by the global scalar ODE and the real-time limit; this is a usable criterion for eigenvector and
  other entire-vector models, while the finite-radius Nelson implication remains separate.
- `LinearPMap.analyticVectors` : the analytic vectors packaged as a submodule contained in
  `T.domain`, with a direct density equivalence.
- `LinearPMap.isAnalyticVector_of_eigenvector` and
  `LinearPMap.isEntireVector_of_eigenvector` : every eigenvector of `T` is analytic for *every*
  radius `t`, since its iterate sequence has an exactly geometric norm. In particular every vector
  in `EssentialSelfAdjointCriteria.lean`'s dense eigenbasis-span criterion is automatically an
  analytic vector, so that already-proved theorem is the "totally elementary" special case of
  Nelson's theorem in which the analytic vectors are exhibited as an explicit eigenbasis rather
  than only assumed to exist.
- `LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors` : Nelson's
  single-operator analytic-vector criterion, proved by the uniform-radius integer continuation and
  the global-orbit deficiency argument below.
-/

@[expose] public section

noncomputable section

namespace LinearPMap

open scoped InnerProductSpace Topology
open Filter

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The definition -/

/-- `v` is the iterate sequence of `x` under `T`: `v 0 = x` and `v (n+1) = T (v n)`, as elements
of `T.domain` (so this packages, in particular, the assertion that `x` lies in the domain of every
power `Tⁿ`). Since `T` is single-valued, `v` is uniquely determined by `x` whenever it exists at
all. -/
def IteratesSeq (T : H →ₗ.[ℂ] H) (x : H) (v : ℕ → T.domain) : Prop :=
  (v 0 : H) = x ∧ ∀ n, (v (n + 1) : H) = T (v n)

lemma IteratesSeq.ext {T : H →ₗ.[ℂ] H} {x : H} {v w : ℕ → T.domain}
    (hv : IteratesSeq T x v) (hw : IteratesSeq T x w) :
    ∀ n, (v n : H) = (w n : H) := by
  intro n
  induction n with
  | zero => exact hv.1.trans hw.1.symm
  | succ n ih =>
    calc
      (v (n + 1) : H) = T (v n) := hv.2 n
      _ = T (w n) := by
        congr 1
        exact Subtype.ext ih
      _ = (w (n + 1) : H) := (hw.2 n).symm

/-- **Analytic vector** (Reed–Simon Vol. II, §X.6). `x` is an analytic vector for `T` if it lies
in the domain of every iterated power `Tⁿ` (witnessed by an iterate sequence `v`, so `v n`
represents `Tⁿ x`) and the exponential-type series `∑ ‖Tⁿx‖ tⁿ / n!` converges for some `t > 0`. -/
def IsAnalyticVector (T : H →ₗ.[ℂ] H) (x : H) : Prop :=
  ∃ v : ℕ → T.domain, IteratesSeq T x v ∧
    ∃ t : ℝ, 0 < t ∧ Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)

/-- The data hidden by `IsAnalyticVector`, retained as a structure for recursive continuation.
The proposition is ideal for stating density assumptions; this structure is the corresponding
proof-relevant package needed to name the next exponential chart. -/
structure AnalyticVectorWitness (T : H →ₗ.[ℂ] H) where
  state : H
  iterates : ℕ → T.domain
  iterates_spec : IteratesSeq T state iterates
  radius : ℝ
  radius_pos : 0 < radius
  summable : Summable (fun n => ‖(iterates n : H)‖ * radius ^ n / n.factorial)

lemma AnalyticVectorWitness.isAnalytic {T : H →ₗ.[ℂ] H} (W : AnalyticVectorWitness T) :
    T.IsAnalyticVector W.state :=
  ⟨W.iterates, W.iterates_spec, W.radius, W.radius_pos, W.summable⟩

noncomputable def AnalyticVectorWitness.of_isAnalytic
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsAnalyticVector x) : AnalyticVectorWitness T := by
  let v : ℕ → T.domain := Classical.choose h
  have hv : IteratesSeq T x v := (Classical.choose_spec h).1
  let t : ℝ := Classical.choose (Classical.choose_spec h).2
  have ht : 0 < t := (Classical.choose_spec (Classical.choose_spec h).2).1
  have hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial) :=
    (Classical.choose_spec (Classical.choose_spec h).2).2
  exact ⟨x, v, hv, t, ht, hsum⟩

/-- An entire vector has an iterate witness whose factorial majorant converges at every positive
radius.  This is stronger than `IsAnalyticVector`; it is the class on which the local exponential
series can be evaluated at arbitrary real times without the global patching argument. -/
def IsEntireVector (T : H →ₗ.[ℂ] H) (x : H) : Prop :=
  ∃ v : ℕ → T.domain, IteratesSeq T x v ∧
    ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)

/-! ## The local exponential series -/

/-- The `n`th term of the formal exponential orbit of an analytic vector.  The factor is written
with the `I • T` convention used by Stone's theorem: for a real time `s` it is
`(I * s)^n / n! • T^n x`.  Keeping the iterate witness explicit is useful because a
`LinearPMap` power is only defined on a nested domain. -/
def analyticExpTerm (T : H →ₗ.[ℂ] H) (v : ℕ → T.domain) (s : ℝ) (n : ℕ) : H :=
  (((Complex.I * (s : ℂ)) ^ n) / n.factorial) • (v n : H)

/-- The formal local exponential orbit associated to an iterate witness.  It is deliberately a
`tsum`, rather than a new bundled operator: convergence is supplied by
`IsAnalyticVector.summable_analyticExpTerm` below, while later Nelson/Stone developments can add
the local semigroup laws without changing this scalar-series interface. -/
def analyticExp (T : H →ₗ.[ℂ] H) (v : ℕ → T.domain) (s : ℝ) : H :=
  ∑' n, analyticExpTerm T v s n

lemma analyticExp_congr_iterates {T : H →ₗ.[ℂ] H} {x : H}
    {v w : ℕ → T.domain} (hv : IteratesSeq T x v) (hw : IteratesSeq T x w) (s : ℝ) :
    analyticExp T v s = analyticExp T w s := by
  unfold analyticExp
  congr 1
  funext n
  simp only [analyticExpTerm, IteratesSeq.ext hv hw n]

omit [CompleteSpace H] in
lemma norm_analyticExpTerm (T : H →ₗ.[ℂ] H) (v : ℕ → T.domain) (s : ℝ) (n : ℕ) :
    ‖analyticExpTerm T v s n‖ = ‖(v n : H)‖ * |s| ^ n / n.factorial := by
  unfold analyticExpTerm
  rw [norm_smul, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_natCast]
  ring

/-- The formal derivative of an exponential-series term with respect to its real time parameter.
The `n - 1` convention makes the definition uniform at `n = 0`, where the leading factor `n`
annihilates the term. -/
def analyticExpDerivTerm (T : H →ₗ.[ℂ] H) (v : ℕ → T.domain) (s : ℝ) (n : ℕ) : H :=
  (((n : ℂ) * Complex.I * (Complex.I * (s : ℂ)) ^ (n - 1)) / n.factorial) • (v n : H)

omit [CompleteSpace H] in
lemma analyticExpTerm_hasDerivAt (T : H →ₗ.[ℂ] H) (v : ℕ → T.domain) (s : ℝ) (n : ℕ) :
    HasDerivAt (fun r : ℝ => analyticExpTerm T v r n)
      (analyticExpDerivTerm T v s n) s := by
  have hbase : HasDerivAt (fun r : ℝ => Complex.I * (r : ℂ)) Complex.I s := by
    have hreal : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 s := by
      change HasDerivAt (⇑Complex.ofRealCLM) (Complex.ofRealCLM 1) s
      exact Complex.ofRealCLM.hasDerivAt
    simpa using hreal.const_mul Complex.I
  have hpow := hbase.pow n
  have hcoeff := hpow.div_const (n.factorial : ℂ)
  have hterm := HasDerivAt.smul_const hcoeff (v n : H)
  convert hterm using 1 <;> simp only [analyticExpTerm, analyticExpDerivTerm]
  · funext r
    rfl
  · ring_nf

omit [CompleteSpace H] in
lemma norm_analyticExpDerivTerm (T : H →ₗ.[ℂ] H) (v : ℕ → T.domain) (s : ℝ) (n : ℕ) :
    ‖analyticExpDerivTerm T v s n‖ =
      ‖(v n : H)‖ * n * |s| ^ (n - 1) / n.factorial := by
  unfold analyticExpDerivTerm
  simp only [norm_smul, norm_div, norm_mul, norm_pow, Complex.norm_natCast,
    Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  ring

lemma analyticExp_hasDerivAt_of_mem_half_radius
    {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain} {t s : ℝ} (ht : 0 < t)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    HasDerivAt (fun r : ℝ => analyticExp T v r)
      (∑' n, analyticExpDerivTerm T v s n) s := by
  have ht0 : 0 ≤ t := ht.le
  have hnat : ∀ k : ℕ, (k + 1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      calc
        (↑(Nat.succ k) + 1 : ℝ) = (k + 1 + 1 : ℝ) := by norm_num
        _ ≤ 2 * (k + 1 : ℝ) := by
          have hk : (0 : ℝ) ≤ k := by positivity
          linarith
        _ ≤ 2 * (2 : ℝ) ^ (k + 1) := by gcongr
        _ = (2 : ℝ) ^ (k + 2) := by ring
  have hderiv_bound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-t / 2) (t / 2) →
      ‖analyticExpDerivTerm T v y n‖ ≤
        (2 / t) * (‖(v n : H)‖ * t ^ n / n.factorial) := by
    intro n y hy
    rw [norm_analyticExpDerivTerm]
    have hyabs : |y| ≤ t / 2 := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    cases n with
    | zero => simp; positivity
    | succ k =>
      have hkpow : |y| ^ k ≤ (t / 2) ^ k :=
        pow_le_pow_left₀ (abs_nonneg y) hyabs k
      have hmain : (k + 1 : ℝ) * |y| ^ k ≤ 2 * t ^ k := by
        calc
          (k + 1 : ℝ) * |y| ^ k ≤ (k + 1 : ℝ) * (t / 2) ^ k := by gcongr
          _ ≤ (2 : ℝ) ^ (k + 1) * (t / 2) ^ k := by
            exact mul_le_mul_of_nonneg_right (hnat k) (by positivity)
          _ = 2 * t ^ k := by
            rw [div_pow]
            field_simp
            ring
      have hfac : 0 ≤ ‖(v (Nat.succ k) : H)‖ / (Nat.succ k).factorial := by positivity
      calc
        ‖(v (Nat.succ k) : H)‖ * ↑(Nat.succ k) * |y| ^ k / (Nat.succ k).factorial
            = (‖(v (Nat.succ k) : H)‖ / (Nat.succ k).factorial) *
                ((k + 1 : ℝ) * |y| ^ k) := by
          simp only [Nat.cast_succ]
          ring
        _ ≤ (‖(v (Nat.succ k) : H)‖ / (Nat.succ k).factorial) * (2 * t ^ k) := by
          gcongr
        _ = (2 / t) *
            (‖(v (Nat.succ k) : H)‖ * t ^ (Nat.succ k) / (Nat.succ k).factorial) := by
          field_simp
          rw [pow_succ]
          ring
  have hu : Summable (fun n => (2 / t) * (‖(v n : H)‖ * t ^ n / n.factorial)) :=
    hsum.mul_left (2 / t)
  have hzero : (0 : ℝ) ∈ Set.Ioo (-t / 2) (t / 2) := by
    constructor <;> linarith
  have hsum_zero : Summable (fun n => analyticExpTerm T v 0 n) := by
    apply Summable.of_norm_bounded hsum
    intro n
    rw [norm_analyticExpTerm]
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
      positivity
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun n y hy => analyticExpTerm_hasDerivAt T v y n)
    (fun n y hy => hderiv_bound n y hy) hzero hsum_zero hs

lemma analyticExp_hasDerivAt_zero {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain}
    (hv : IteratesSeq T x v) {t : ℝ} (ht : 0 < t)
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    HasDerivAt (fun s : ℝ => analyticExp T v s) (Complex.I • T (v 0)) 0 := by
  have hlocal := analyticExp_hasDerivAt_of_mem_half_radius (T := T) (v := v) ht
    (by
      change (0 : ℝ) ∈ Set.Ioo (-t / 2) (t / 2)
      constructor <;> linarith [ht]) hsum
  have hsum_deriv : (∑' n, analyticExpDerivTerm T v 0 n) = Complex.I • T (v 0) := by
    rw [tsum_eq_single 1]
    · simpa [analyticExpDerivTerm] using congrArg (fun z : H => Complex.I • z) (hv.2 0)
    · intro n hn
      cases n with
      | zero => simp [analyticExpDerivTerm]
      | succ n =>
        cases n with
        | zero => exact (hn rfl).elim
        | succ n => simp [analyticExpDerivTerm]
  rw [hsum_deriv] at hlocal
  exact hlocal

lemma summable_analyticExpDerivTerm_of_mem_half_radius
    {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain} {t s : ℝ} (ht : 0 < t)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    Summable (fun n => analyticExpDerivTerm T v s n) := by
  have hnat : ∀ k : ℕ, (k + 1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      calc
        (↑(Nat.succ k) + 1 : ℝ) = (k + 1 + 1 : ℝ) := by norm_num
        _ ≤ 2 * (k + 1 : ℝ) := by
          have hk : (0 : ℝ) ≤ k := by positivity
          linarith
        _ ≤ 2 * (2 : ℝ) ^ (k + 1) := by gcongr
        _ = (2 : ℝ) ^ (k + 2) := by ring
  have hbound : ∀ (n : ℕ),
      ‖analyticExpDerivTerm T v s n‖ ≤
        (2 / t) * (‖(v n : H)‖ * t ^ n / n.factorial) := by
    intro n
    rw [norm_analyticExpDerivTerm]
    cases n with
    | zero => simp; positivity
    | succ k =>
      have hyabs : |s| ≤ t / 2 := by
        rw [abs_le]
        constructor <;> linarith [hs.1, hs.2]
      have hkpow : |s| ^ k ≤ (t / 2) ^ k :=
        pow_le_pow_left₀ (abs_nonneg s) hyabs k
      have hmain : (k + 1 : ℝ) * |s| ^ k ≤ 2 * t ^ k := by
        calc
          (k + 1 : ℝ) * |s| ^ k ≤ (k + 1 : ℝ) * (t / 2) ^ k := by gcongr
          _ ≤ (2 : ℝ) ^ (k + 1) * (t / 2) ^ k := by
            exact mul_le_mul_of_nonneg_right (hnat k) (by positivity)
          _ = 2 * t ^ k := by
            rw [div_pow]
            field_simp
            ring
      calc
        ‖(v (Nat.succ k) : H)‖ * ↑(Nat.succ k) * |s| ^ k /
              (Nat.succ k).factorial
            = (‖(v (Nat.succ k) : H)‖ / (Nat.succ k).factorial) *
                ((k + 1 : ℝ) * |s| ^ k) := by
          simp only [Nat.cast_succ]
          ring
        _ ≤ (‖(v (Nat.succ k) : H)‖ / (Nat.succ k).factorial) *
              (2 * t ^ k) := by gcongr
        _ = (2 / t) *
            (‖(v (Nat.succ k) : H)‖ * t ^ (Nat.succ k) /
              (Nat.succ k).factorial) := by
          field_simp
          rw [pow_succ]
          ring
  exact Summable.of_norm_bounded (hsum.mul_left (2 / t)) hbound

lemma analyticExp_mem_closure_graph
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hT : T.IsClosable)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    (analyticExp T v s, (-Complex.I) • (∑' n, analyticExpDerivTerm T v s n)) ∈
      T.closure.graph := by
  have hexp : Summable (fun n => analyticExpTerm T v s n) := by
    apply Summable.of_norm_bounded hsum
    intro n
    rw [norm_analyticExpTerm]
    have ht : 0 ≤ t := le_of_lt (by linarith [hs.2, hs.1])
    have hsabs : |s| ≤ t := by
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2]
    have hpow : |s| ^ n ≤ t ^ n := pow_le_pow_left₀ (abs_nonneg s) hsabs n
    have hnonneg : 0 ≤ ‖(v n : H)‖ / n.factorial := by positivity
    calc
      ‖(v n : H)‖ * |s| ^ n / n.factorial
          = (‖(v n : H)‖ / n.factorial) * |s| ^ n := by ring
      _ ≤ (‖(v n : H)‖ / n.factorial) * t ^ n := by gcongr
      _ = ‖(v n : H)‖ * t ^ n / n.factorial := by ring
  have hderiv := summable_analyticExpDerivTerm_of_mem_half_radius
    (T := T) (v := v) (by linarith [hs.2, hs.1]) hs hsum
  let p : ℕ → T.domain := fun N => ∑ n ∈ Finset.range N,
    (((Complex.I * (s : ℂ)) ^ n) / n.factorial) • v n
  let q : ℕ → H := fun N => T (p N)
  have hp : Filter.Tendsto (fun N => (p N : H)) Filter.atTop (𝓝 (analyticExp T v s)) := by
    simpa [p, analyticExp, analyticExpTerm] using (hexp.hasSum.tendsto_sum_nat)
  have hq_eq : ∀ N, q N = (-Complex.I) •
      (∑ n ∈ Finset.range (N + 1), analyticExpDerivTerm T v s n) := by
    intro N
    have hterm : ∀ n : ℕ,
        T ((((Complex.I * (s : ℂ)) ^ n) / n.factorial) • v n) =
          (-Complex.I) • analyticExpDerivTerm T v s (n + 1) := by
      intro n
      rw [map_smul, ← hv.2 n]
      simp [analyticExpDerivTerm, Nat.factorial_succ, smul_smul]
      field_simp
      ring_nf
      rw [Complex.I_sq]
      simp
    induction N with
    | zero => simp [q, p, analyticExpDerivTerm]
    | succ N ih =>
      change T (∑ n ∈ Finset.range (N + 1),
        (((Complex.I * (s : ℂ)) ^ n) / n.factorial) • v n) = _
      rw [Finset.sum_range_succ, map_add]
      rw [show T (∑ n ∈ Finset.range N,
          (((Complex.I * (s : ℂ)) ^ n) / n.factorial) • v n) = q N by rfl]
      rw [ih]
      rw [hterm N]
      rw [← smul_add]
      congr 1
      rw [show N + (1 + 1) = (N + 1) + 1 by omega]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
  have hq : Filter.Tendsto q Filter.atTop (𝓝 ((-Complex.I) • (∑' n,
      analyticExpDerivTerm T v s n))) := by
    have hd := hderiv.hasSum.tendsto_sum_nat
    have hshift := hd.comp (Filter.tendsto_add_atTop_nat 1)
    have hshift' := hshift.const_smul (-Complex.I)
    exact hshift'.congr' (Filter.Eventually.of_forall fun N => (hq_eq N).symm)
  change (analyticExp T v s, (-Complex.I) • (∑' n, analyticExpDerivTerm T v s n)) ∈
    T.closure.graph
  rw [← hT.graph_closure_eq_closure_graph]
  apply mem_closure_iff_seq_limit.mpr
  refine ⟨fun N => ((p N : H), q N), ?_, ?_⟩
  · exact fun N => T.mem_graph (p N)
  · rw [nhds_prod_eq]
    exact hp.prodMk hq

lemma analyticExp_mem_closure_domain
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hT : T.IsClosable)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    analyticExp T v s ∈ T.closure.domain :=
  mem_domain_of_mem_graph (analyticExp_mem_closure_graph hv hT hs hsum)

lemma closure_analyticExp_apply
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hT : T.IsClosable)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    T.closure ⟨analyticExp T v s, analyticExp_mem_closure_domain hv hT hs hsum⟩ =
      (-Complex.I) • (∑' n, analyticExpDerivTerm T v s n) := by
  apply T.closure.mem_graph_snd_inj'
    (T.closure.mem_graph ⟨analyticExp T v s, analyticExp_mem_closure_domain hv hT hs hsum⟩)
    (analyticExp_mem_closure_graph hv hT hs hsum)
  rfl

lemma analyticExp_hasDerivAt_eq_smul_closure
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hT : T.IsClosable)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    HasDerivAt (fun r : ℝ => analyticExp T v r)
      (Complex.I • T.closure ⟨analyticExp T v s,
        analyticExp_mem_closure_domain hv hT hs hsum⟩) s := by
  have h := analyticExp_hasDerivAt_of_mem_half_radius
    (T := T) (v := v) (by linarith [hs.2, hs.1]) hs hsum
  convert h using 1
  rw [closure_analyticExp_apply hv hT hs hsum]
  simp [smul_smul]

lemma IsSymmetric.re_inner_smul_I_apply_self
    {T : H →ₗ.[ℂ] H} (hT : T.IsSymmetric) (x : T.domain) :
    (⟪(x : H), Complex.I • T x⟫_ℂ).re = 0 := by
  have hreal := (isSymmetric_iff_inner_map_self_real.mp hT x)
  have hxy : ⟪(x : H), T x⟫_ℂ = ⟪T x, (x : H)⟫_ℂ := by
    calc
      ⟪(x : H), T x⟫_ℂ = (starRingEnd ℂ) ⟪T x, (x : H)⟫_ℂ :=
        (inner_conj_symm (x : H) (T x)).symm
      _ = ⟪T x, (x : H)⟫_ℂ := hreal
  have hconj : (starRingEnd ℂ) ⟪(x : H), T x⟫_ℂ = ⟪(x : H), T x⟫_ℂ := by
    calc
      (starRingEnd ℂ) ⟪(x : H), T x⟫_ℂ =
          (starRingEnd ℂ) ⟪T x, (x : H)⟫_ℂ := congrArg (starRingEnd ℂ) hxy
      _ = ⟪T x, (x : H)⟫_ℂ := hreal
      _ = ⟪(x : H), T x⟫_ℂ := hxy.symm
  have him : (⟪(x : H), T x⟫_ℂ).im = 0 := by
    have him' := congrArg Complex.im hconj
    rw [Complex.conj_im] at him'
    linarith
  rw [inner_smul_right]
  simp [Complex.I_mul, him]

lemma analyticExp_normSq_hasDerivAt_eq_zero
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    HasDerivAt (fun r : ℝ => ‖analyticExp T v r‖ ^ 2) 0 s := by
  have hspan : Dense (Submodule.span ℂ {x : H | T.IsAnalyticVector x} : Set H) := by
    rw [dense_iff_closure_eq]
    change _root_.closure (Submodule.span ℂ {x : H | T.IsAnalyticVector x} : Set H) = Set.univ
    rw [← Submodule.topologicalClosure_coe]
    exact congrArg (fun s : Submodule ℂ H => (s : Set H)) hdense
  have hdomain : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}) ≤ T.domain := by
    refine Submodule.span_le.2 (fun y hy => ?_)
    obtain ⟨w, ⟨hw0, -⟩, -⟩ := hy
    exact hw0 ▸ (w 0).2
  have hTdense : T.HasDenseDomain := hspan.mono hdomain
  have hclosure_symm : T.closure.IsSymmetric := hsym.closure hTdense
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have hlocal := analyticExp_hasDerivAt_eq_smul_closure hv
    (hsym.isClosable hTdense) hs hsum
  have hnorm : HasDerivAt (fun r : ℝ => ‖analyticExp T v r‖ ^ 2)
      (2 * ⟪analyticExp T v s,
        Complex.I • T.closure ⟨analyticExp T v s,
          analyticExp_mem_closure_domain hv (hsym.isClosable hTdense) hs hsum⟩⟫_ℝ) s :=
    by
      simpa [ContinuousLinearMap.toSpanSingleton_apply] using
        hlocal.hasFDerivAt.norm_sq.hasDerivAt
  have hzero :
      (2 : ℝ) * (⟪analyticExp T v s,
        Complex.I • T.closure ⟨analyticExp T v s,
          analyticExp_mem_closure_domain hv (hsym.isClosable hTdense) hs hsum⟩⟫_ℂ).re = 0 := by
    have hinner := hclosure_symm.re_inner_smul_I_apply_self
      ⟨analyticExp T v s,
        analyticExp_mem_closure_domain hv (hsym.isClosable hTdense) hs hsum⟩
    simp [hinner]
  convert hnorm using 1
  simpa [real_inner_eq_re_inner] using hzero.symm

lemma analyticExp_normSq_eq_normSq_zero
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    ‖analyticExp T v s‖ ^ 2 = ‖x‖ ^ 2 := by
  have ht : 0 < t := by linarith [hs.2, hs.1]
  have hconst : ∀ {r u : ℝ}, r ∈ Set.Ioo (-t / 2) (t / 2) →
      u ∈ Set.Ioo (-t / 2) (t / 2) →
      ‖analyticExp T v r‖ ^ 2 = ‖analyticExp T v u‖ ^ 2 := by
    intro r u hr hu
    refine isOpen_Ioo.is_const_of_deriv_eq_zero
      (s := Set.Ioo (-t / 2) (t / 2)) (f := fun y : ℝ => ‖analyticExp T v y‖ ^ 2)
      (isPreconnected_Ioo (a := -t / 2) (b := t / 2)) ?_ ?_ hr hu
    · intro y hy
      exact (analyticExp_normSq_hasDerivAt_eq_zero hsym hdense hv hy hsum).differentiableAt.differentiableWithinAt
    · intro y hy
      exact (analyticExp_normSq_hasDerivAt_eq_zero hsym hdense hv hy hsum).deriv
  have hzero : (0 : ℝ) ∈ Set.Ioo (-t / 2) (t / 2) := by
    constructor <;> linarith
  rw [hconst hs hzero]
  rw [analyticExp, tsum_eq_single 0]
  · simp [analyticExpTerm, hv.1]
  · intro n hn
    simp [analyticExpTerm, hn]

lemma analyticExp_norm_eq_norm
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    ‖analyticExp T v s‖ = ‖x‖ := by
  have hsq := analyticExp_normSq_eq_normSq_zero hsym hdense hv hs hsum
  nlinarith [norm_nonneg (analyticExp T v s), norm_nonneg x]

lemma analyticExp_eq_zero_iff
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    analyticExp T v s = 0 ↔ x = 0 := by
  rw [← norm_eq_zero]
  rw [analyticExp_norm_eq_norm hsym hdense hv hs hsum]
  exact norm_eq_zero

lemma IsEntireVector.isAnalyticVector
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsEntireVector x) : T.IsAnalyticVector x := by
  obtain ⟨v, hv, hall⟩ := h
  exact ⟨v, hv, 1, one_pos, hall 1 one_pos⟩

lemma analyticExp_mem_closure_domain_of_entire
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    (hall : ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hT : T.IsClosable) (s : ℝ) :
    analyticExp T v s ∈ T.closure.domain := by
  let t : ℝ := 2 * |s| + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hs : s ∈ Set.Ioo (-t / 2) (t / 2) := by
    dsimp [t]
    constructor <;> linarith [neg_le_abs s, le_abs_self s]
  exact analyticExp_mem_closure_domain hv hT hs (hall t ht)

lemma IsEntireVector.analyticExp_mem_closure_domain
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsEntireVector x)
    (hT : T.IsClosable) (s : ℝ) :
    ∃ v : ℕ → T.domain, IteratesSeq T x v ∧
      analyticExp T v s ∈ T.closure.domain := by
  obtain ⟨v, hv, hall⟩ := h
  let t : ℝ := 2 * |s| + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hs : s ∈ Set.Ioo (-t / 2) (t / 2) := by
    dsimp [t]
    constructor <;> linarith [neg_le_abs s, le_abs_self s]
  exact ⟨v, hv, analyticExp_mem_closure_domain_of_entire hv hall hT s⟩

lemma IsEntireVector.analyticExp_norm_eq_norm
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsEntireVector x)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (s : ℝ) :
    ∃ v : ℕ → T.domain, IteratesSeq T x v ∧ ‖analyticExp T v s‖ = ‖x‖ := by
  obtain ⟨v, hv, hall⟩ := h
  let t : ℝ := 2 * |s| + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hs : s ∈ Set.Ioo (-t / 2) (t / 2) := by
    dsimp [t]
    constructor <;> linarith [neg_le_abs s, le_abs_self s]
  exact ⟨v, hv, LinearPMap.analyticExp_norm_eq_norm hsym hdense hv hs (hall t ht)⟩

lemma analyticExp_hasDerivAt_of_entire
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    (hall : ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hT : T.IsClosable) (s : ℝ) :
    HasDerivAt (fun r : ℝ => analyticExp T v r)
      (Complex.I • T.closure ⟨analyticExp T v s,
        analyticExp_mem_closure_domain_of_entire hv hall hT s⟩) s := by
  let t : ℝ := 2 * |s| + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hs : s ∈ Set.Ioo (-t / 2) (t / 2) := by
    dsimp [t]
    constructor <;> linarith [neg_le_abs s, le_abs_self s]
  exact analyticExp_hasDerivAt_eq_smul_closure hv hT hs (hall t ht)

lemma analyticExp_inner_deficiency_hasDerivAt
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    (hall : ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hT : T.IsClosable) {y : H}
    (hy : y ∈ (T.closure - Complex.I • 1).toFun.rangeᗮ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => ⟪y, analyticExp T v r⟫_ℂ)
      (-⟪y, analyticExp T v s⟫_ℂ) s := by
  have hdom : analyticExp T v s ∈ T.closure.domain :=
    analyticExp_mem_closure_domain_of_entire hv hall hT s
  have hderiv := analyticExp_hasDerivAt_of_entire hv hall hT s
  let z : (T.closure - Complex.I • 1).domain :=
    ⟨analyticExp T v s, by
      rw [sub_domain]
      exact ⟨hdom, by simp⟩⟩
  have horth : ⟪y, T.closure ⟨analyticExp T v s, hdom⟩ -
      Complex.I • (analyticExp T v s)⟫_ℂ = 0 := by
    have hz := (Submodule.mem_orthogonal' _ y).mp hy ((T.closure - Complex.I • 1).toFun z)
      ⟨z, rfl⟩
    simpa [z, sub_apply] using hz
  have hrelation : ⟪y, T.closure ⟨analyticExp T v s, hdom⟩⟫_ℂ =
      Complex.I * ⟪y, analyticExp T v s⟫_ℂ := by
    rw [inner_sub_right, inner_smul_right] at horth
    exact sub_eq_zero.mp horth
  have hinner := (hasDerivAt_const (x := s) y).inner ℂ hderiv
  convert hinner using 1
  · rfl
  · simp only [inner_zero_left, inner_smul_right]
    rw [hrelation]
    ring_nf
    rw [Complex.I_sq]
    simp

lemma analyticExp_inner_deficiency_eq_zero
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    (hall : ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hT : T.IsClosable) {y : H}
    (hy : y ∈ (T.closure - Complex.I • 1).toFun.rangeᗮ) :
    ⟪y, x⟫_ℂ = 0 := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let f : ℝ → ℂ := fun s => ⟪y, analyticExp T v s⟫_ℂ
  let g : ℝ → ℂ := fun s => (Real.exp s : ℂ) * f s
  have hg : ∀ s : ℝ, HasDerivAt g 0 s := by
    intro s
    have he : HasDerivAt (fun r : ℝ => (Real.exp r : ℂ)) (Real.exp s) s :=
      (Real.hasDerivAt_exp s).ofReal_comp
    have hf : HasDerivAt f (-f s) s := by
      simpa [f] using analyticExp_inner_deficiency_hasDerivAt hv hall hT hy s
    have hp := he.mul hf
    have hz : (Real.exp s : ℂ) * f s + (Real.exp s : ℂ) * (-f s) = 0 := by
      ring
    have hp' : HasDerivAt ((fun r : ℝ => (Real.exp r : ℂ)) * f) 0 s := by
      simpa only [hz] using hp
    change HasDerivAt (fun r : ℝ => (Real.exp r : ℂ) * f r) 0 s
    convert hp' using 1
    funext r
    rfl
  have hconst : ∀ s : ℝ, g s = g 0 := by
    intro s
    exact is_const_of_deriv_eq_zero (fun r => (hg r).differentiableAt)
      (fun r => (hg r).deriv) s 0
  have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hupper : Filter.Tendsto
      (fun n : ℕ => Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖)) atTop (𝓝 0) := by
    simpa only [Pi.mul_apply, zero_mul] using
      hexp.mul (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => ‖y‖ * ‖x‖) atTop (𝓝 (‖y‖ * ‖x‖)))
  have hnorm_lim : Filter.Tendsto (fun n : ℕ => ‖g (-(n : ℝ))‖) atTop (𝓝 0) := by
    refine squeeze_zero' (f := fun n : ℕ => ‖g (-(n : ℝ))‖)
      (g := fun n : ℕ => Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖))
      (Filter.Eventually.of_forall fun n => norm_nonneg _)
      (Filter.Eventually.of_forall (fun n => ?_)) hupper
    calc
      ‖g (-(n : ℝ))‖ = Real.exp (-(n : ℝ)) *
          ‖⟪y, analyticExp T v (-(n : ℝ))⟫_ℂ‖ := by
            dsimp [g, f]
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-(n : ℝ)) *
          (‖y‖ * ‖analyticExp T v (-(n : ℝ))‖) := by
            gcongr
            exact norm_inner_le_norm _ _
      _ = Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖) := by
        have hnorm : ‖analyticExp T v (-(n : ℝ))‖ = ‖x‖ := by
          obtain ⟨w, hw, heq⟩ := IsEntireVector.analyticExp_norm_eq_norm
            ⟨v, hv, hall⟩ hsym hdense (-(n : ℝ))
          rw [analyticExp_congr_iterates hv hw, heq]
        rw [hnorm]
  have hlim : Filter.Tendsto (fun n : ℕ => g (-(n : ℝ))) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_lim
  have hconst_zero : g 0 = 0 := by
    have hc : Tendsto (fun _ : ℕ => g 0) atTop (𝓝 0) :=
      hlim.congr' (Filter.Eventually.of_forall fun n => hconst (-(n : ℝ)))
    exact (tendsto_nhds_unique hc tendsto_const_nhds).symm
  have hexp_zero : analyticExp T v 0 = x := by
    rw [analyticExp, tsum_eq_single 0]
    · simpa [analyticExpTerm] using hv.1
    · intro n hn
      simp [analyticExpTerm, hn]
  simpa [g, f, hexp_zero] using hconst_zero

lemma analyticExp_inner_deficiency_hasDerivAt_neg
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    (hall : ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hT : T.IsClosable) {y : H}
    (hy : y ∈ (T.closure - (-Complex.I) • 1).toFun.rangeᗮ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => ⟪y, analyticExp T v r⟫_ℂ)
      (⟪y, analyticExp T v s⟫_ℂ) s := by
  have hdom : analyticExp T v s ∈ T.closure.domain :=
    analyticExp_mem_closure_domain_of_entire hv hall hT s
  have hderiv := analyticExp_hasDerivAt_of_entire hv hall hT s
  let z : (T.closure - (-Complex.I) • 1).domain :=
    ⟨analyticExp T v s, by
      rw [sub_domain]
      exact ⟨hdom, by simp⟩⟩
  have horth : ⟪y, T.closure ⟨analyticExp T v s, hdom⟩ -
      (-Complex.I) • (analyticExp T v s)⟫_ℂ = 0 := by
    have hz := (Submodule.mem_orthogonal' _ y).mp hy ((T.closure - (-Complex.I) • 1).toFun z)
      ⟨z, rfl⟩
    simpa [z, sub_apply] using hz
  have hrelation : ⟪y, T.closure ⟨analyticExp T v s, hdom⟩⟫_ℂ =
      (-Complex.I) * ⟪y, analyticExp T v s⟫_ℂ := by
    rw [inner_sub_right, inner_smul_right] at horth
    exact sub_eq_zero.mp horth
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have hinner := (hasDerivAt_const (x := s) y).inner ℂ hderiv
  convert hinner using 1
  · rfl
  · simp only [inner_zero_left, inner_smul_right]
    rw [hrelation]
    ring_nf
    rw [Complex.I_sq]
    simp

lemma analyticExp_inner_deficiency_eq_zero_neg
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    (hall : ∀ t : ℝ, 0 < t → Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hT : T.IsClosable) {y : H}
    (hy : y ∈ (T.closure - (-Complex.I) • 1).toFun.rangeᗮ) :
    ⟪y, x⟫_ℂ = 0 := by
  let f : ℝ → ℂ := fun s => ⟪y, analyticExp T v s⟫_ℂ
  let g : ℝ → ℂ := fun s => (Real.exp (-s) : ℂ) * f s
  have hg : ∀ s : ℝ, HasDerivAt g 0 s := by
    intro s
    have he : HasDerivAt (fun r : ℝ => (Real.exp (-r) : ℂ))
        (-Real.exp (-s)) s := by
      have hreal := (Real.hasDerivAt_exp (-s)).scomp s
        (hasDerivAt_id' (𝕜 := ℝ) s).neg
      convert hreal.ofReal_comp using 1
      · funext r
        rfl
      · simp
    have hf : HasDerivAt f (f s) s := by
      simpa [f] using analyticExp_inner_deficiency_hasDerivAt_neg hv hall hT hy s
    have hp := he.mul hf
    have hz : (-Real.exp (-s) : ℂ) * f s + (Real.exp (-s) : ℂ) * f s = 0 := by
      ring
    have hp' : HasDerivAt ((fun r : ℝ => (Real.exp (-r) : ℂ)) * f) 0 s := by
      simpa only [hz] using hp
    change HasDerivAt (fun r : ℝ => (Real.exp (-r) : ℂ) * f r) 0 s
    convert hp' using 1
    funext r
    rfl
  have hconst : ∀ s : ℝ, g s = g 0 := by
    intro s
    exact is_const_of_deriv_eq_zero (fun r => (hg r).differentiableAt)
      (fun r => (hg r).deriv) s 0
  have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hupper : Filter.Tendsto
      (fun n : ℕ => Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖)) atTop (𝓝 0) := by
    simpa only [Pi.mul_apply, zero_mul] using
      hexp.mul (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => ‖y‖ * ‖x‖) atTop (𝓝 (‖y‖ * ‖x‖)))
  have hnorm_lim : Filter.Tendsto (fun n : ℕ => ‖g (n : ℝ)‖) atTop (𝓝 0) := by
    refine squeeze_zero' (f := fun n : ℕ => ‖g (n : ℝ)‖)
      (g := fun n : ℕ => Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖))
      (Filter.Eventually.of_forall fun n => norm_nonneg _)
      (Filter.Eventually.of_forall (fun n => ?_)) hupper
    calc
      ‖g (n : ℝ)‖ = Real.exp (-(n : ℝ)) *
          ‖⟪y, analyticExp T v (n : ℝ)⟫_ℂ‖ := by
            dsimp [g, f]
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-(n : ℝ)) *
          (‖y‖ * ‖analyticExp T v (n : ℝ)‖) := by
            gcongr
            exact norm_inner_le_norm _ _
      _ = Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖) := by
        have hnorm : ‖analyticExp T v (n : ℝ)‖ = ‖x‖ := by
          obtain ⟨w, hw, heq⟩ := IsEntireVector.analyticExp_norm_eq_norm
            ⟨v, hv, hall⟩ hsym hdense (n : ℝ)
          rw [analyticExp_congr_iterates hv hw, heq]
        rw [hnorm]
  have hlim : Filter.Tendsto (fun n : ℕ => g (n : ℝ)) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_lim
  have hconst_zero : g 0 = 0 := by
    have hc : Tendsto (fun _ : ℕ => g 0) atTop (𝓝 0) :=
      hlim.congr' (Filter.Eventually.of_forall fun n => hconst (n : ℝ))
    exact (tendsto_nhds_unique hc tendsto_const_nhds).symm
  have hexp_zero : analyticExp T v 0 = x := by
    rw [analyticExp, tsum_eq_single 0]
    · simpa [analyticExpTerm] using hv.1
    · intro n hn
      simp [analyticExpTerm, hn]
  simpa [g, f, hexp_zero] using hconst_zero

lemma analyticExp_continuousAt_of_mem_half_radius
    {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain} {t s : ℝ} (ht : 0 < t)
    (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    ContinuousAt (fun r : ℝ => analyticExp T v r) s :=
  (analyticExp_hasDerivAt_of_mem_half_radius ht hs hsum).continuousAt

lemma IsAnalyticVector.exists_analyticExp_summable
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsAnalyticVector x) :
    ∃ v : ℕ → T.domain, IteratesSeq T x v ∧ ∃ t : ℝ, 0 < t ∧ ∀ s : ℝ, |s| ≤ t →
      Summable (fun n => analyticExpTerm T v s n) := by
  obtain ⟨v, hv, t, ht, hsum⟩ := h
  refine ⟨v, hv, t, ht, fun s hs ↦ ?_⟩
  apply Summable.of_norm_bounded hsum
  intro n
  rw [norm_analyticExpTerm]
  have hpow : |s| ^ n ≤ t ^ n := pow_le_pow_left₀ (abs_nonneg s) hs n
  have hnonneg : 0 ≤ ‖(v n : H)‖ / n.factorial := by positivity
  calc
    ‖(v n : H)‖ * |s| ^ n / n.factorial
        = (‖(v n : H)‖ / n.factorial) * |s| ^ n := by ring
    _ ≤ (‖(v n : H)‖ / n.factorial) * t ^ n := by gcongr
    _ = ‖(v n : H)‖ * t ^ n / n.factorial := by ring

lemma IsAnalyticVector.summable_analyticExpTerm
    {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain} {s : ℝ} {t : ℝ} (hs : |s| ≤ t)
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    Summable (fun n => analyticExpTerm T v s n) := by
  apply Summable.of_norm_bounded hsum
  intro n
  rw [norm_analyticExpTerm]
  have hpow : |s| ^ n ≤ t ^ n := pow_le_pow_left₀ (abs_nonneg s) hs n
  have hnonneg : 0 ≤ ‖(v n : H)‖ / n.factorial := by positivity
  calc
    ‖(v n : H)‖ * |s| ^ n / n.factorial
        = (‖(v n : H)‖ / n.factorial) * |s| ^ n := by ring
    _ ≤ (‖(v n : H)‖ / n.factorial) * t ^ n := by gcongr
    _ = ‖(v n : H)‖ * t ^ n / n.factorial := by ring

lemma IsAnalyticVector.hasSum_analyticExp
    {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain} {s : ℝ} {t : ℝ} (hs : |s| ≤ t)
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    HasSum (fun n => analyticExpTerm T v s n) (analyticExp T v s) := by
  simpa only [analyticExp] using
    (summable_analyticExpTerm hs hsum).hasSum

lemma analyticExp_smul_iterates
    {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain} {c : ℂ} {s t : ℝ}
    (hs : |s| ≤ t)
    (hsum : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    analyticExp T (fun n => c • v n) s = c • analyticExp T v s := by
  have hsum_smul : Summable (fun n => ‖((c • v n : T.domain) : H)‖ * t ^ n /
      n.factorial) := by
    have heq : (fun n => ‖((c • v n : T.domain) : H)‖ * t ^ n / n.factorial) =
        (fun n => ‖c‖ * (‖(v n : H)‖ * t ^ n / n.factorial)) := by
      funext n
      rw [SetLike.val_smul, norm_smul]
      ring
    rw [heq]
    exact hsum.mul_left _
  have hleft := (IsAnalyticVector.hasSum_analyticExp (T := T)
    (v := fun n => c • v n) hs hsum_smul)
  have hright := (IsAnalyticVector.hasSum_analyticExp (T := T) (v := v) hs hsum).const_smul c
  have hterms : (fun n => analyticExpTerm T (fun n => c • v n) s n) =
      (fun n => c • analyticExpTerm T v s n) := by
    funext n
    unfold analyticExpTerm
    rw [SetLike.val_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [hterms] at hleft
  exact hleft.unique hright

lemma analyticExp_add_iterates
    {T : H →ₗ.[ℂ] H} {v w : ℕ → T.domain} {s t : ℝ}
    (hs : |s| ≤ t)
    (hv : Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hw : Summable (fun n => ‖(w n : H)‖ * t ^ n / n.factorial)) :
    analyticExp T (fun n => v n + w n) s =
      analyticExp T v s + analyticExp T w s := by
  have hsum_add : Summable (fun n => ‖((v n + w n : T.domain) : H)‖ * t ^ n /
      n.factorial) := by
    have ht : 0 ≤ t := le_trans (abs_nonneg s) hs
    have hbound : ∀ n, ‖((v n + w n : T.domain) : H)‖ * t ^ n /
        n.factorial ≤ ‖(v n : H)‖ * t ^ n / n.factorial +
          ‖(w n : H)‖ * t ^ n / n.factorial := by
      intro n
      have htri : ‖((v n + w n : T.domain) : H)‖ ≤ ‖(v n : H)‖ + ‖(w n : H)‖ := by
        exact norm_add_le _ _
      calc
        ‖((v n + w n : T.domain) : H)‖ * t ^ n / n.factorial
            ≤ (‖(v n : H)‖ + ‖(w n : H)‖) * t ^ n / n.factorial := by
              gcongr
        _ = ‖(v n : H)‖ * t ^ n / n.factorial +
            ‖(w n : H)‖ * t ^ n / n.factorial := by ring
    exact Summable.of_nonneg_of_le (fun n => by positivity) hbound (hv.add hw)
  have hleft := (IsAnalyticVector.hasSum_analyticExp (T := T)
    (v := fun n => v n + w n) hs hsum_add)
  have hright := (IsAnalyticVector.hasSum_analyticExp (T := T) (v := v) hs hv).add
    (IsAnalyticVector.hasSum_analyticExp (T := T) (v := w) hs hw)
  have hterms : (fun n => analyticExpTerm T (fun n => v n + w n) s n) =
      (fun n => analyticExpTerm T v s n + analyticExpTerm T w s n) := by
    funext n
    simp [analyticExpTerm, smul_add]
  rw [hterms] at hleft
  exact hleft.unique hright

omit [CompleteSpace H] in
lemma analyticExp_zero {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain}
    (hv : IteratesSeq T x v) : analyticExp T v 0 = x := by
  rw [analyticExp, tsum_eq_single 0]
  · simpa [analyticExpTerm] using hv.1
  · intro n hn
    simp [analyticExpTerm, hn]

omit [CompleteSpace H] in
lemma analyticExpTerm_succ {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain}
    (hv : IteratesSeq T x v) (s : ℝ) (n : ℕ) :
    analyticExpTerm T v s (n + 1) =
      (((Complex.I * (s : ℂ)) ^ (n + 1)) / (n + 1).factorial) • T (v n) := by
  unfold analyticExpTerm
  rw [hv.2 n]

omit [CompleteSpace H] in
lemma IsAnalyticVector.mem_domain {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsAnalyticVector x) :
    x ∈ T.domain := by
  obtain ⟨v, ⟨hv0, -⟩, -⟩ := h
  exact hv0 ▸ (v 0).2

omit [CompleteSpace H] in
/-- An analytic-vector witness for a closable operator is also a witness for its closure.

The iterate sequence is transported pointwise along `T.le_closure`; the closure agrees with `T`
on the original domain, so no regularity beyond closability is needed for this transfer. -/
lemma IsAnalyticVector.for_closure {T : H →ₗ.[ℂ] H} {x : H}
    (h : T.IsAnalyticVector x) :
    T.closure.IsAnalyticVector x := by
  obtain ⟨v, hv, t, ht, hsum⟩ := h
  let w : ℕ → T.closure.domain := fun n =>
    ⟨(v n : H), T.le_closure.1 (v n).property⟩
  have hw : IteratesSeq T.closure x w := by
    refine ⟨?_, fun n => ?_⟩
    · exact hv.1
    · have hcl : T ⟨(v n : H), (v n).property⟩ =
          T.closure (w n) := by
        exact T.le_closure.2 rfl
      calc
        (w (n + 1) : H) = T (v n) := hv.2 n
        _ = T.closure (w n) := hcl
  refine ⟨w, hw, t, ht, ?_⟩
  simpa [w] using hsum

omit [CompleteSpace H] in
/-- Applying `T` to an analytic vector preserves analyticity, with a smaller radius.

The shifted iterate sequence is `n ↦ v (n+1)`.  The loss of radius absorbs the linear factor
`n+1` introduced when the factorial denominator is shifted. -/
lemma IsAnalyticVector.apply {T : H →ₗ.[ℂ] H} {x : H}
    (h : T.IsAnalyticVector x) :
    T.IsAnalyticVector (T ⟨x, IsAnalyticVector.mem_domain h⟩) := by
  have hx : x ∈ T.domain := IsAnalyticVector.mem_domain h
  obtain ⟨v, hv, t, ht, hsum⟩ := h
  let w : ℕ → T.domain := fun n => v (n + 1)
  have hw : IteratesSeq T (T ⟨x, hx⟩) w := by
    refine ⟨?_, fun n => ?_⟩
    · change (v (0 + 1) : H) = T ⟨x, hx⟩
      rw [show (0 + 1 : ℕ) = 1 by rfl, hv.2 0]
      congr 1
      exact Subtype.ext hv.1
    · change (v ((n + 1) + 1) : H) = T (v (n + 1))
      exact hv.2 (n + 1)
  have htail : Summable (fun n : ℕ =>
      ‖(v (n + 1) : H)‖ * t ^ (n + 1) / (n + 1).factorial) := by
    simpa only [Nat.add_assoc] using
      ((summable_nat_add_iff
        (f := fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial) 1).2 hsum)
  have hfactor : ∀ n : ℕ, (n + 1 : ℝ) * ((1 : ℝ) / 2) ^ n ≤ 2 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        calc
          (n.succ + 1 : ℝ) * ((1 : ℝ) / 2) ^ n.succ =
              ((n + 2 : ℝ) / 2) * ((1 : ℝ) / 2) ^ n := by
                rw [pow_succ]
                rw [Nat.cast_succ]
                ring
          _ ≤ (n + 1 : ℝ) * ((1 : ℝ) / 2) ^ n := by
            gcongr
            nlinarith
          _ ≤ 2 := ih
  have hbound : ∀ n : ℕ,
      ‖(w n : H)‖ * (t / 2) ^ n / n.factorial ≤
        (2 / t) * (‖(v (n + 1) : H)‖ * t ^ (n + 1) / (n + 1).factorial) := by
    intro n
    have htn : t ≠ 0 := ne_of_gt ht
    have hfactor' : (n + 1 : ℝ) * ((1 : ℝ) / 2) ^ n / t ≤ 2 / t :=
      div_le_div_of_nonneg_right (hfactor n) ht.le
    calc
      ‖(w n : H)‖ * (t / 2) ^ n / n.factorial =
          ((n + 1 : ℝ) * ((1 : ℝ) / 2) ^ n / t) *
            (‖(v (n + 1) : H)‖ * t ^ (n + 1) / (n + 1).factorial) := by
              dsimp [w]
              rw [Nat.factorial_succ]
              field_simp [htn]
              push_cast
              ring
      _ ≤ (2 / t) * (‖(v (n + 1) : H)‖ * t ^ (n + 1) / (n + 1).factorial) := by
        gcongr
  have ht2 : 0 < t / 2 := by linarith
  refine ⟨w, hw, t / 2, ht2, ?_⟩
  apply Summable.of_nonneg_of_le (fun n => by positivity) hbound
  exact htail.mul_left (2 / t)

omit [CompleteSpace H] in
/-- Applying the closed operator to a transported analytic vector preserves analyticity.

This is the form used by continuation arguments: after transporting an analytic witness from
`T` to `T.closure`, the smaller-radius invariance lemma can be iterated without leaving the closed
operator's domain. -/
lemma IsAnalyticVector.closure_apply {T : H →ₗ.[ℂ] H} {x : H}
    (h : T.IsAnalyticVector x) :
    T.closure.IsAnalyticVector
      (T.closure ⟨x, IsAnalyticVector.mem_domain (IsAnalyticVector.for_closure h)⟩) := by
  exact IsAnalyticVector.apply (IsAnalyticVector.for_closure h)

/-! ## Structural closure properties -/

omit [CompleteSpace H] in
lemma isAnalyticVector_zero (T : H →ₗ.[ℂ] H) : T.IsAnalyticVector 0 := by
  let v : ℕ → T.domain := fun _ => ⟨0, T.domain.zero_mem⟩
  refine ⟨v, ⟨by simp [v], fun n => ?_⟩, 1, one_pos, ?_⟩
  · change (0 : H) = T (v n)
    change (0 : H) = T (0 : T.domain)
    exact (map_zero T).symm
  · simpa [v] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

omit [CompleteSpace H] in
/-- Analytic vectors are closed under scalar multiplication, with the same radius. -/
lemma IsAnalyticVector.smul {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsAnalyticVector x) (c : ℂ) :
    T.IsAnalyticVector (c • x) := by
  obtain ⟨v, ⟨hv0, hvS⟩, t, ht, hsum⟩ := h
  refine ⟨fun n => c • v n, ⟨by simp [hv0], fun n => ?_⟩, t, ht, ?_⟩
  · show (c • v (n + 1) : H) = T (c • v n)
    rw [hvS n, ← LinearPMap.map_smul]
  · have heq : (fun n => ‖(c • v n : T.domain).1‖ * t ^ n / n.factorial)
        = fun n => ‖c‖ * (‖(v n : H)‖ * t ^ n / n.factorial) := by
      funext n
      rw [SetLike.val_smul, norm_smul]
      ring
    rw [heq]
    exact hsum.mul_left _

omit [CompleteSpace H] in
/-- Analytic vectors form an additive submodule: if `x` is analytic with radius `t₁` and `y` with
radius `t₂`, then `x + y` is analytic with radius `min t₁ t₂` — the standard argument, since
`T.domain` is a submodule (so `x + y` and every iterate stay in the domain, with `T` additive
there) and the two majorizing power series compare termwise once the smaller radius is used for
both. -/
lemma IsAnalyticVector.add {T : H →ₗ.[ℂ] H} {x y : H}
    (hx : T.IsAnalyticVector x) (hy : T.IsAnalyticVector y) :
    T.IsAnalyticVector (x + y) := by
  obtain ⟨v, ⟨hv0, hvS⟩, t1, ht1, hsum1⟩ := hx
  obtain ⟨w, ⟨hw0, hwS⟩, t2, ht2, hsum2⟩ := hy
  have ht : (0:ℝ) < min t1 t2 := lt_min ht1 ht2
  refine ⟨fun n => v n + w n, ⟨by simp [hv0, hw0], fun n => ?_⟩, min t1 t2, ht, ?_⟩
  · show ((v (n + 1) + w (n + 1) : T.domain) : H) = T (v n + w n)
    show ((v (n+1) : H) + (w (n+1) : H)) = T (v n + w n)
    rw [hvS n, hwS n, LinearPMap.map_add]
  · have hbound : ∀ n, ‖((v n + w n : T.domain) : H)‖ * (min t1 t2) ^ n / n.factorial
        ≤ ‖(v n : H)‖ * t1 ^ n / n.factorial + ‖(w n : H)‖ * t2 ^ n / n.factorial := by
      intro n
      have htri : ‖((v n + w n : T.domain) : H)‖ ≤ ‖(v n : H)‖ + ‖(w n : H)‖ := by
        show ‖((v n : H) + (w n : H))‖ ≤ _
        exact norm_add_le _ _
      have h1 : (min t1 t2) ^ n ≤ t1 ^ n := pow_le_pow_left₀ ht.le (min_le_left t1 t2) n
      have h2 : (min t1 t2) ^ n ≤ t2 ^ n := pow_le_pow_left₀ ht.le (min_le_right t1 t2) n
      have hv1 : (0:ℝ) ≤ ‖(v n : H)‖ := norm_nonneg _
      have hw1 : (0:ℝ) ≤ ‖(w n : H)‖ := norm_nonneg _
      calc ‖((v n + w n : T.domain) : H)‖ * (min t1 t2) ^ n / n.factorial
          ≤ (‖(v n : H)‖ + ‖(w n : H)‖) * (min t1 t2) ^ n / n.factorial := by
            gcongr
        _ = ‖(v n : H)‖ * (min t1 t2) ^ n / n.factorial
              + ‖(w n : H)‖ * (min t1 t2) ^ n / n.factorial := by ring
        _ ≤ ‖(v n : H)‖ * t1 ^ n / n.factorial + ‖(w n : H)‖ * t2 ^ n / n.factorial := by
            gcongr
    exact Summable.of_nonneg_of_le (fun n => by positivity) hbound (hsum1.add hsum2)

/-- The analytic vectors form a genuine complex submodule.  This packages the set used in the
density hypothesis of Nelson's theorem and is also the natural candidate for the common analytic
core in the joint-commutation theorem. -/
def analyticVectors (T : H →ₗ.[ℂ] H) : Submodule ℂ H where
  carrier := {x | T.IsAnalyticVector x}
  zero_mem' := isAnalyticVector_zero T
  add_mem' := IsAnalyticVector.add
  smul_mem' := fun c _ hx => hx.smul c

omit [CompleteSpace H] in
@[simp]
lemma mem_analyticVectors {T : H →ₗ.[ℂ] H} {x : H} :
    x ∈ T.analyticVectors ↔ T.IsAnalyticVector x := Iff.rfl

omit [CompleteSpace H] in
lemma analyticVectors_le_domain {T : H →ₗ.[ℂ] H} :
    T.analyticVectors ≤ T.domain := by
  intro x hx
  exact IsAnalyticVector.mem_domain hx

omit [CompleteSpace H] in
lemma dense_analyticVectors_iff {T : H →ₗ.[ℂ] H} :
    (T.analyticVectors : Submodule ℂ H).topologicalClosure = ⊤ ↔
      (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤ := by
  change T.analyticVectors.topologicalClosure = ⊤ ↔
    (Submodule.span ℂ (T.analyticVectors : Set H)).topologicalClosure = ⊤
  rw [Submodule.span_eq]

/-! ## Eigenvectors are analytic -/

omit [CompleteSpace H] in
/-- Every eigenvector is analytic for `T`, with *every* radius `t > 0`: its iterate sequence has
exactly geometric norm `‖x‖ * |μ|ⁿ`, so the series is dominated by a genuine exponential series,
convergent by `Real.summable_pow_div_factorial`. In particular every vector in a dense eigenbasis
(as in `EssentialSelfAdjointCriteria.lean`'s `isEssentiallySelfAdjoint_of_dense_eigenvectors`) is
already an analytic vector: that theorem is the special case of Nelson's theorem where the dense
set of analytic vectors is exhibited concretely as an eigenbasis, rather than only assumed to
exist abstractly. -/
lemma isAnalyticVector_of_eigenvector {T : H →ₗ.[ℂ] H} {x : H} (hx : x ∈ T.domain) (μ : ℂ)
    (heig : T ⟨x, hx⟩ = μ • x) (t : ℝ) (ht : 0 < t) : T.IsAnalyticVector x := by
  have hmem : ∀ n : ℕ, μ ^ n • x ∈ T.domain := fun n => T.domain.smul_mem _ hx
  refine ⟨fun n => ⟨μ ^ n • x, hmem n⟩, ⟨by simp, fun n => ?_⟩, t, ht, ?_⟩
  · show μ ^ (n + 1) • x = T ⟨μ ^ n • x, hmem n⟩
    have hcast : (⟨μ ^ n • x, hmem n⟩ : T.domain) = μ ^ n • (⟨x, hx⟩ : T.domain) := by
      ext; simp
    rw [hcast, LinearPMap.map_smul, heig, smul_smul, pow_succ]
  · have heq : (fun n => ‖(⟨μ ^ n • x, hmem n⟩ : T.domain).1‖ * t ^ n / n.factorial)
        = fun n => ‖x‖ * ((‖μ‖ * t) ^ n / n.factorial) := by
      funext n
      simp only [norm_smul, norm_pow, mul_pow]
      ring
    rw [heq]
    exact (Real.summable_pow_div_factorial (‖μ‖ * t)).mul_left _

lemma isEntireVector_of_eigenvector {T : H →ₗ.[ℂ] H} {x : H} (hx : x ∈ T.domain) (μ : ℂ)
    (heig : T ⟨x, hx⟩ = μ • x) : T.IsEntireVector x := by
  have hmem : ∀ n : ℕ, μ ^ n • x ∈ T.domain := fun n => T.domain.smul_mem _ hx
  refine ⟨fun n => ⟨μ ^ n • x, hmem n⟩, ⟨by simp, fun n => ?_⟩, fun t ht => ?_⟩
  · show μ ^ (n + 1) • x = T ⟨μ ^ n • x, hmem n⟩
    have hcast : (⟨μ ^ n • x, hmem n⟩ : T.domain) = μ ^ n • (⟨x, hx⟩ : T.domain) := by
      ext
      simp
    rw [hcast, LinearPMap.map_smul, heig, smul_smul, pow_succ]
  · have heq : (fun n => ‖(⟨μ ^ n • x, hmem n⟩ : T.domain).1‖ * t ^ n / n.factorial)
        = fun n => ‖x‖ * ((‖μ‖ * t) ^ n / n.factorial) := by
      funext n
      simp only [norm_smul, norm_pow, mul_pow]
      ring
    rw [heq]
    exact (Real.summable_pow_div_factorial (‖μ‖ * t)).mul_left _

omit [CompleteSpace H] in
lemma isEntireVector_zero (T : H →ₗ.[ℂ] H) : T.IsEntireVector 0 := by
  let v : ℕ → T.domain := fun _ => ⟨0, T.domain.zero_mem⟩
  refine ⟨v, ⟨by simp [v], fun n => ?_⟩, fun t ht => ?_⟩
  · change (0 : H) = T (v n)
    change (0 : H) = T (0 : T.domain)
    exact (map_zero T).symm
  · simpa [v] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

omit [CompleteSpace H] in
lemma IsEntireVector.smul {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsEntireVector x) (c : ℂ) :
    T.IsEntireVector (c • x) := by
  obtain ⟨v, ⟨hv0, hvS⟩, hall⟩ := h
  refine ⟨fun n => c • v n, ⟨by simp [hv0], fun n => ?_⟩, fun t ht => ?_⟩
  · show (c • v (n + 1) : H) = T (c • v n)
    rw [hvS n, ← LinearPMap.map_smul]
  · have heq : (fun n => ‖(c • v n : T.domain).1‖ * t ^ n / n.factorial)
        = fun n => ‖c‖ * (‖(v n : H)‖ * t ^ n / n.factorial) := by
      funext n
      rw [SetLike.val_smul, norm_smul]
      ring
    rw [heq]
    exact (hall t ht).mul_left _

omit [CompleteSpace H] in
lemma IsEntireVector.add {T : H →ₗ.[ℂ] H} {x y : H}
    (hx : T.IsEntireVector x) (hy : T.IsEntireVector y) :
    T.IsEntireVector (x + y) := by
  obtain ⟨v, ⟨hv0, hvS⟩, hallv⟩ := hx
  obtain ⟨w, ⟨hw0, hwS⟩, hallw⟩ := hy
  refine ⟨fun n => v n + w n, ⟨by simp [hv0, hw0], fun n => ?_⟩, fun t ht => ?_⟩
  · show ((v (n + 1) + w (n + 1) : T.domain) : H) = T (v n + w n)
    show ((v (n + 1) : H) + (w (n + 1) : H)) = T (v n + w n)
    rw [hvS n, hwS n, LinearPMap.map_add]
  · have hbound : ∀ n, ‖((v n + w n : T.domain) : H)‖ * t ^ n /
        n.factorial ≤ ‖(v n : H)‖ * t ^ n / n.factorial +
          ‖(w n : H)‖ * t ^ n / n.factorial := by
      intro n
      have htri : ‖((v n + w n : T.domain) : H)‖ ≤ ‖(v n : H)‖ + ‖(w n : H)‖ := by
        exact norm_add_le _ _
      calc
        ‖((v n + w n : T.domain) : H)‖ * t ^ n / n.factorial
            ≤ (‖(v n : H)‖ + ‖(w n : H)‖) * t ^ n / n.factorial := by
              gcongr
        _ = ‖(v n : H)‖ * t ^ n / n.factorial +
            ‖(w n : H)‖ * t ^ n / n.factorial := by ring
    exact Summable.of_nonneg_of_le (fun n => by positivity) hbound
      ((hallv t ht).add (hallw t ht))

omit [CompleteSpace H] in
def entireVectors (T : H →ₗ.[ℂ] H) : Submodule ℂ H where
  carrier := {x | T.IsEntireVector x}
  zero_mem' := isEntireVector_zero T
  add_mem' := IsEntireVector.add
  smul_mem' := fun c _ hx => hx.smul c

omit [CompleteSpace H] in
@[simp]
lemma mem_entireVectors {T : H →ₗ.[ℂ] H} {x : H} :
    x ∈ T.entireVectors ↔ T.IsEntireVector x := Iff.rfl

/-! ## The global-orbit essential-self-adjointness criterion -/

/-- A dense family of entire vectors is sufficient for essential self-adjointness.

This is the part of Nelson's argument for which the global exponential orbit is available without
any continuation argument.  The two deficiency spaces are killed directly: pair the global orbit
with a deficiency vector, solve the resulting scalar ODE, and send the real time to the end at
which the compensating exponential tends to zero.  The original finite-radius Nelson theorem
below is stronger; it still requires the local-semigroup continuation step. -/
theorem IsSymmetric.isEssentiallySelfAdjoint_of_denseEntireVectors
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : T.entireVectors.topologicalClosure = ⊤) :
    T.IsEssentiallySelfAdjoint := by
  have hleAnalytic : T.entireVectors ≤ T.analyticVectors := by
    intro x hx
    exact IsEntireVector.isAnalyticVector hx
  have hdenseAnalyticSubmodule : T.analyticVectors.topologicalClosure = ⊤ := by
    apply top_unique
    rw [← hdense]
    exact Submodule.topologicalClosure_mono hleAnalytic
  have hdenseAnalytic :
      (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤ :=
    (dense_analyticVectors_iff (T := T)).mp hdenseAnalyticSubmodule
  have hleDomain : T.entireVectors ≤ T.domain := by
    intro x hx
    exact analyticVectors_le_domain (IsEntireVector.isAnalyticVector hx)
  have hdenseDomain : T.HasDenseDomain := by
    have hdomainClosure : T.domain.topologicalClosure = ⊤ := by
      apply top_unique
      rw [← hdense]
      exact Submodule.topologicalClosure_mono hleDomain
    rw [LinearPMap.hasDenseDomain_def, dense_iff_closure_eq]
    change _root_.closure (T.domain : Set H) = Set.univ
    rw [← Submodule.topologicalClosure_coe, hdomainClosure]
    rfl
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  have hspanEntire :
      (Submodule.span ℂ (T.entireVectors : Set H)).topologicalClosure = ⊤ := by
    rw [Submodule.span_eq]
    exact hdense
  have hdefect_plus : T.defectNumber Complex.I = 0 := by
    rw [← defectNumber_closure (T := T) (z := Complex.I)
      (hsym.mem_regularityDomain_of_im_ne_zero (by simp))]
    show Module.rank ℂ ↥((T.closure - Complex.I • 1).toFun.rangeᗮ) = 0
    apply Submodule.rank_eq_zero.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hyspan : y ∈ (Submodule.span ℂ (T.entireVectors : Set H))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction (p := fun z _ ↦ ⟪y, z⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
      · rintro z hz
        obtain ⟨w, hw, hallw⟩ := mem_entireVectors.mp hz
        exact analyticExp_inner_deficiency_eq_zero hsym hdenseAnalytic hw hallw hT hy
      · simp
      · intro z₁ z₂ _ _ hz₁ hz₂
        simp [inner_add_right, hz₁, hz₂]
      · intro c z _ hz
        simp [inner_smul_right, hz]
    have hspanBot :
        (Submodule.span ℂ (T.entireVectors : Set H))ᗮ = (⊥ : Submodule ℂ H) :=
      Submodule.topologicalClosure_eq_top_iff.mp hspanEntire
    exact (Submodule.mem_bot ℂ).mp (hspanBot ▸ hyspan)
  have hdefect_minus : T.defectNumber (-Complex.I) = 0 := by
    rw [← defectNumber_closure (T := T) (z := -Complex.I)
      (hsym.mem_regularityDomain_of_im_ne_zero (by simp))]
    show Module.rank ℂ ↥((T.closure - (-Complex.I) • 1).toFun.rangeᗮ) = 0
    apply Submodule.rank_eq_zero.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hyspan : y ∈ (Submodule.span ℂ (T.entireVectors : Set H))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction (p := fun z _ ↦ ⟪y, z⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
      · rintro z hz
        obtain ⟨w, hw, hallw⟩ := mem_entireVectors.mp hz
        exact analyticExp_inner_deficiency_eq_zero_neg hsym hdenseAnalytic hw hallw hT hy
      · simp
      · intro z₁ z₂ _ _ hz₁ hz₂
        simp [inner_add_right, hz₁, hz₂]
      · intro c z _ hz
        simp [inner_smul_right, hz]
    have hspanBot :
        (Submodule.span ℂ (T.entireVectors : Set H))ᗮ = (⊥ : Submodule ℂ H) :=
      Submodule.topologicalClosure_eq_top_iff.mp hspanEntire
    exact (Submodule.mem_bot ℂ).mp (hspanBot ▸ hyspan)
  exact hsym.isEssentiallySelfAdjoint_of_defectNumber_eq_zero
    hdenseDomain hdefect_plus hdefect_minus

/-! ## Common domain infrastructure for the finite-radius argument -/

lemma hasDenseDomain_of_denseAnalyticVectors
    {T : H →ₗ.[ℂ] H}
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    T.HasDenseDomain := by
  have hspan : Dense (Submodule.span ℂ {x : H | T.IsAnalyticVector x} : Set H) := by
    rw [dense_iff_closure_eq]
    change _root_.closure (Submodule.span ℂ {x : H | T.IsAnalyticVector x} : Set H) = Set.univ
    rw [← Submodule.topologicalClosure_coe]
    exact congrArg (fun s : Submodule ℂ H => (s : Set H)) hdense
  have hdomain : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}) ≤ T.domain := by
    refine Submodule.span_le.2 (fun x hx => ?_)
    exact IsAnalyticVector.mem_domain (by simpa using hx)
  exact hspan.mono hdomain

lemma IsSymmetric.closure_of_denseAnalyticVectors
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    T.closure.IsSymmetric :=
  hsym.closure (hasDenseDomain_of_denseAnalyticVectors hdense)

/-! ## The global-orbit certificate targeted by Nelson continuation -/

/-- A local norm-preserving orbit on a symmetric operator's analytic radius.  The finite-radius
Nelson construction starts with this object and must extend it by overlapping local pieces. -/
structure LocalAnalyticOrbit (T : H →ₗ.[ℂ] H) (x : H) where
  radius : ℝ
  radius_pos : 0 < radius
  toFun : ℝ → H
  initial : toFun 0 = x
  mem_domain : ∀ s, |s| < radius → toFun s ∈ T.closure.domain
  hasDerivAt : ∀ (s : ℝ) (hs : |s| < radius),
    HasDerivAt toFun
      (Complex.I • T.closure ⟨toFun s, mem_domain s hs⟩) s
  norm_eq : ∀ (s : ℝ) (hs : |s| < radius), ‖toFun s‖ = ‖x‖

namespace LocalAnalyticOrbit

instance {T : H →ₗ.[ℂ] H} {x : H} : CoeFun (LocalAnalyticOrbit T x)
    (fun _ => ℝ → H) := ⟨LocalAnalyticOrbit.toFun⟩

/- Recentring is the basic overlap operation in the finite-radius continuation argument. -/
def translateTo {T : H →ₗ.[ℂ] H} {x : H} (U : LocalAnalyticOrbit T x) (a : ℝ)
    (ha : |a| < U.radius) : LocalAnalyticOrbit T (U a) :=
  let r : ℝ := U.radius - |a|
  { radius := r
    radius_pos := sub_pos.mpr ha
    toFun := fun s => U (a + s)
    initial := by simp
    mem_domain := fun s hs => by
      have hsum : |a + s| ≤ |a| + |s| := abs_add_le _ _
      have hlt : |a| + |s| < U.radius := by
        dsimp [r] at hs
        linarith
      exact U.mem_domain (a + s) (lt_of_le_of_lt hsum hlt)
    hasDerivAt := fun s hs => by
      have hsum : |a + s| ≤ |a| + |s| := abs_add_le _ _
      have hlt : |a| + |s| < U.radius := by
        dsimp [r] at hs
        linarith
      have hcomp := U.hasDerivAt (a + s) (lt_of_le_of_lt hsum hlt)
      have hcomp' := hcomp.comp_const_add a s
      simpa only [Function.comp_def] using hcomp'
    norm_eq := fun s hs => by
      have hsum : |a + s| ≤ |a| + |s| := abs_add_le _ _
      have hlt : |a| + |s| < U.radius := by
        dsimp [r] at hs
        linarith
      calc
        ‖U (a + s)‖ = ‖x‖ := U.norm_eq (a + s) (lt_of_le_of_lt hsum hlt)
        _ = ‖U a‖ := (U.norm_eq a ha).symm }

lemma translate {T : H →ₗ.[ℂ] H} {x : H} (U : LocalAnalyticOrbit T x) (a : ℝ)
    (ha : |a| < U.radius) : Nonempty (LocalAnalyticOrbit T (U a)) :=
  ⟨U.translateTo a ha⟩

/-- The direct (non-`Nonempty`) form of chart restriction. -/
def restrictTo {T : H →ₗ.[ℂ] H} {x : H} (U : LocalAnalyticOrbit T x)
    {r : ℝ} (hr : 0 < r) (hrU : r ≤ U.radius) : LocalAnalyticOrbit T x :=
  { radius := r
    radius_pos := hr
    toFun := U
    initial := U.initial
    mem_domain := fun s hs => U.mem_domain s (lt_of_lt_of_le hs hrU)
    hasDerivAt := fun s hs => U.hasDerivAt s (lt_of_lt_of_le hs hrU)
    norm_eq := fun s hs => U.norm_eq s (lt_of_lt_of_le hs hrU) }

/-- Restrict a local orbit to a smaller symmetric radius.  Keeping this operation explicit is
useful for gluing: adjacent recentered charts need only agree on a deliberately chosen core of
their domains, while the original charts may have larger asymmetric overlaps. -/
lemma restrict {T : H →ₗ.[ℂ] H} {x : H} (U : LocalAnalyticOrbit T x)
    {r : ℝ} (hr : 0 < r) (hrU : r ≤ U.radius) :
    Nonempty (LocalAnalyticOrbit T x) := by
  exact ⟨U.restrictTo hr hrU⟩

lemma eq_of_same_initial
    {T : H →ₗ.[ℂ] H} {x : H} (U V : LocalAnalyticOrbit T x)
    (hclosure_symm : T.closure.IsSymmetric) {s : ℝ}
    (hs : |s| < min U.radius V.radius) : U s = V s := by
  let r : ℝ := min U.radius V.radius
  have hr : 0 < r := lt_min U.radius_pos V.radius_pos
  have hinterval : ∀ y : ℝ, y ∈ Set.Ioo (-r) r →
      HasDerivAt (fun q : ℝ => ‖U q - V q‖ ^ 2) 0 y := by
    intro y hy
    have hyabs : |y| < r := by
      rw [abs_lt]
      exact ⟨hy.1, hy.2⟩
    have hyU : |y| < U.radius := lt_of_lt_of_le hyabs (min_le_left _ _)
    have hyV : |y| < V.radius := lt_of_lt_of_le hyabs (min_le_right _ _)
    have hdom : U y - V y ∈ T.closure.domain :=
      T.closure.domain.sub_mem (U.mem_domain y hyU) (V.mem_domain y hyV)
    let z : T.closure.domain := ⟨U y - V y, hdom⟩
    let u : T.closure.domain := ⟨U y, U.mem_domain y hyU⟩
    let v : T.closure.domain := ⟨V y, V.mem_domain y hyV⟩
    have hderivU := U.hasDerivAt y hyU
    have hderivV := V.hasDerivAt y hyV
    have hderiv : HasDerivAt (fun q : ℝ => U q - V q)
        (Complex.I • T.closure z) y := by
      have hsub := hderivU.sub hderivV
      have hz : z = u - v := by
        apply Subtype.ext
        rfl
      rw [hz, map_sub]
      have hfun : (U.toFun - V.toFun) = (fun q : ℝ => U q - V q) := by
        funext q
        rfl
      rw [hfun] at hsub
      simpa [u, v, smul_sub] using hsub
    letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
    have hnorm : HasDerivAt (fun q : ℝ => ‖U q - V q‖ ^ 2)
        (2 * ⟪U y - V y, Complex.I • T.closure z⟫_ℝ) y := by
      simpa [ContinuousLinearMap.toSpanSingleton_apply, inner_sub_left] using
        hderiv.hasFDerivAt.norm_sq.hasDerivAt
    have hinner := hclosure_symm.re_inner_smul_I_apply_self z
    have hinner' : ⟪U y - V y, Complex.I • T.closure z⟫_ℝ = 0 := by
      simpa [z, real_inner_eq_re_inner] using hinner
    simpa [hinner'] using hnorm
  have hconst : ∀ {a b : ℝ}, a ∈ Set.Ioo (-r) r → b ∈ Set.Ioo (-r) r →
      ‖U a - V a‖ ^ 2 = ‖U b - V b‖ ^ 2 := by
    intro a b ha hb
    exact isOpen_Ioo.is_const_of_deriv_eq_zero
      (s := Set.Ioo (-r) r) (f := fun q : ℝ => ‖U q - V q‖ ^ 2)
      (isPreconnected_Ioo (a := -r) (b := r))
      (fun q hq => (hinterval q hq).differentiableAt.differentiableWithinAt)
      (fun q hq => (hinterval q hq).deriv) ha hb
  have hzero_mem : (0 : ℝ) ∈ Set.Ioo (-r) r := by
    constructor <;> linarith
  have hs_mem : s ∈ Set.Ioo (-r) r := by
    change -r < s ∧ s < r
    exact abs_lt.mp hs
  have hnormsq : ‖U s - V s‖ ^ 2 = 0 := by
    rw [hconst hs_mem hzero_mem]
    simp [U.initial, V.initial]
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  nlinarith [sq_nonneg ‖U s - V s‖]

/-! A translated chart and a chart independently based at the translated state agree on every
smaller symmetric core.  This is the elementary overlap statement used by the integer-chart
continuation below; the explicit radius inequalities keep the asymmetric translated radius out of
the later gluing proof. -/
lemma translate_eq_of_same_initial_on_core
    {T : H →ₗ.[ℂ] H} {x : H} (U : LocalAnalyticOrbit T x)
    (hclosure_symm : T.closure.IsSymmetric) {δ R : ℝ}
    (hδ : 0 < δ) (hR : 0 < R) (hδU : δ + R ≤ U.radius)
    (V : LocalAnalyticOrbit T (U δ)) (hVR : R ≤ V.radius) {s : ℝ}
    (hs : |s| < R) : U (δ + s) = V s := by
  have hδU' : |δ| < U.radius := by
    rw [abs_of_pos hδ]
    linarith
  let W : LocalAnalyticOrbit T (U δ) := U.translateTo δ hδU'
  have hWR : R ≤ W.radius := by
    dsimp [W, translateTo]
    rw [abs_of_pos hδ]
    linarith
  have hsW : |s| < W.radius := lt_of_lt_of_le hs hWR
  have hsV : |s| < V.radius := lt_of_lt_of_le hs hVR
  have heq := LocalAnalyticOrbit.eq_of_same_initial W V hclosure_symm
    (lt_min hsW hsV)
  change U (δ + s) = V s at heq
  exact heq

lemma translate_eq_of_same_initial_on_core'
    {T : H →ₗ.[ℂ] H} {x : H} (U : LocalAnalyticOrbit T x)
    (hclosure_symm : T.closure.IsSymmetric) {a R : ℝ}
    (hR : 0 < R) (haU : |a| + R ≤ U.radius)
    (V : LocalAnalyticOrbit T (U a)) (hVR : R ≤ V.radius) {s : ℝ}
    (hs : |s| < R) : U (a + s) = V s := by
  have haU' : |a| < U.radius := by linarith
  let W : LocalAnalyticOrbit T (U a) := U.translateTo a haU'
  have hWR : R ≤ W.radius := by
    dsimp [W, translateTo]
    linarith
  have heq := LocalAnalyticOrbit.eq_of_same_initial W V hclosure_symm
    (lt_min (lt_of_lt_of_le hs hWR) (lt_of_lt_of_le hs hVR))
  change U (a + s) = V s at heq
  exact heq

/-- Transport a local orbit certificate for the closure back to a closable operator.  This is the
local counterpart of `GlobalAnalyticOrbit.of_closure`; it is needed when a fresh chart is produced
recursively for the closed operator but the public continuation interface is phrased for `T`. -/
lemma of_closure {T : H →ₗ.[ℂ] H} {x : H} (hT : T.IsClosable)
    (U : LocalAnalyticOrbit T.closure x) : Nonempty (LocalAnalyticOrbit T x) := by
  have hclosed : T.closure.closure = T.closure := hT.closure_isClosed.closure_eq
  have happly : ∀ (z : H) (hz : z ∈ T.closure.domain)
      (hz' : z ∈ T.closure.closure.domain),
      T.closure.closure ⟨z, hz'⟩ = T.closure ⟨z, hz⟩ := by
    intro z hz hz'
    have hgraph : (z, T.closure.closure ⟨z, hz'⟩) ∈ T.closure.graph := by
      have hgraph_eq : T.closure.closure.graph = T.closure.graph :=
        congrArg (fun R : H →ₗ.[ℂ] H => R.graph) hclosed
      exact hgraph_eq ▸ T.closure.closure.mem_graph ⟨z, hz'⟩
    exact T.closure.mem_graph_snd_inj' hgraph
      (T.closure.mem_graph ⟨z, hz⟩) rfl
  refine ⟨
    { radius := U.radius
      radius_pos := U.radius_pos
      toFun := U
      initial := U.initial
      mem_domain := fun s hs => by
        simpa only [hclosed] using U.mem_domain s hs
      hasDerivAt := fun s hs => by
        have hz' : U s ∈ T.closure.closure.domain := U.mem_domain s hs
        have hz : U s ∈ T.closure.domain := by
          simpa only [hclosed] using hz'
        have hd := U.hasDerivAt s hs
        convert hd using 1
        congr 1
        exact (happly _ hz hz').symm
      norm_eq := U.norm_eq }⟩

end LocalAnalyticOrbit

/-- A global norm-preserving orbit for a vector, with the differential equation interpreted in the
closed operator.  This is the exact analytic certificate needed by the deficiency argument; the
finite-radius Nelson proof constructs it by patching the local exponential series. -/
structure GlobalAnalyticOrbit (T : H →ₗ.[ℂ] H) (x : H) where
  toFun : ℝ → H
  initial : toFun 0 = x
  mem_domain : ∀ s, toFun s ∈ T.closure.domain
  hasDerivAt : ∀ s, HasDerivAt toFun
    (Complex.I • T.closure ⟨toFun s, mem_domain s⟩) s
  norm_eq : ∀ s, ‖toFun s‖ = ‖x‖

namespace GlobalAnalyticOrbit

instance {T : H →ₗ.[ℂ] H} {x : H} : CoeFun (GlobalAnalyticOrbit T x)
    (fun _ => ℝ → H) := ⟨GlobalAnalyticOrbit.toFun⟩

lemma exists_bound_choose_mul_geometric {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) (k : ℕ) :
    ∃ C : ℝ, ∀ n : ℕ, (n + k).choose k * r ^ n ≤ C := by
  have hnorm : ‖r‖ < 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr'
  have hsum : Summable (fun n : ℕ => (n + k).choose k * r ^ n) :=
    summable_choose_mul_geometric_of_norm_lt_one k hnorm
  refine ⟨∑' n : ℕ, (n + k).choose k * r ^ n, fun n => ?_⟩
  exact hsum.le_tsum n (fun j _ => by positivity)

lemma summable_shifted_factorial_majorant {a : ℕ → ℝ} {t q : ℝ}
    (ha : ∀ n, 0 ≤ a n) (ht : 0 < t) (hq : 0 ≤ q) (hqt : q < t) (k : ℕ)
    (hsum : Summable (fun n : ℕ => a n * t ^ n / n.factorial)) :
    Summable (fun n : ℕ => a (n + k) * q ^ n / n.factorial) := by
  let r : ℝ := q / t
  have hr : 0 ≤ r := div_nonneg hq ht.le
  have hr' : r < 1 := by
    dsimp [r]
    exact (div_lt_one ht).2 hqt
  obtain ⟨C, hC⟩ := exists_bound_choose_mul_geometric hr hr' k
  have hC0 : 0 ≤ C := by
    have h := hC 0
    norm_num at h
    linarith
  let b : ℕ → ℝ := fun n => a (n + k) * t ^ (n + k) / (n + k).factorial
  have hb : Summable b := by
    dsimp [b]
    exact (summable_nat_add_iff
      (f := fun n : ℕ => a n * t ^ n / n.factorial) k).2 hsum
  let K : ℝ := C * (k.factorial : ℝ) / t ^ k
  have hK : 0 ≤ K := by
    positivity
  refine Summable.of_nonneg_of_le
    (fun n => div_nonneg (mul_nonneg (ha (n + k)) (pow_nonneg hq _)) (by positivity)) ?_
    (hb.mul_left K)
  intro n
  have hchoose : (n + k).choose k * r ^ n ≤ C := hC n
  have hbase : 0 ≤ b n := by
    dsimp [b]
    exact div_nonneg (mul_nonneg (ha (n + k)) (pow_nonneg ht.le _)) (by positivity)
  have hcoef : (k.factorial : ℝ) * (n + k).choose k * r ^ n / t ^ k ≤
      C * (k.factorial : ℝ) / t ^ k := by
    have hfac : 0 ≤ (k.factorial : ℝ) / t ^ k := by positivity
    calc
      (k.factorial : ℝ) * (n + k).choose k * r ^ n / t ^ k =
          ((n + k).choose k * r ^ n) * ((k.factorial : ℝ) / t ^ k) := by
            ring
      _ ≤ C * ((k.factorial : ℝ) / t ^ k) :=
        mul_le_mul_of_nonneg_right hchoose hfac
      _ = C * (k.factorial : ℝ) / t ^ k := by ring
  calc
    a (n + k) * q ^ n / n.factorial =
        b n * ((k.factorial : ℝ) * (n + k).choose k * r ^ n / t ^ k) := by
      dsimp [b, r]
      have hfact : (n.factorial : ℝ) * (k.factorial : ℝ) *
          (n + k).choose k = (n + k).factorial := by
        have h := Nat.factorial_mul_descFactorial
          (n := n + k) (k := k) (Nat.le_add_left k n)
        rw [Nat.descFactorial_eq_factorial_mul_choose] at h
        have hnk : n + k - k = n := by omega
        rw [hnk] at h
        norm_cast
        simpa [mul_assoc] using h
      have hfact' : (n + k).factorial =
          (n.factorial : ℝ) * ((k.factorial : ℝ) * (n + k).choose k) := by
        rw [← hfact]
        ring
      rw [div_pow]
      field_simp [ne_of_gt ht]
      rw [hfact']
      ring
    _ ≤ b n * K := mul_le_mul_of_nonneg_left hcoef hbase
    _ = K * b n := by rw [mul_comm]

def shiftedIterates {T : H →ₗ.[ℂ] H} (v : ℕ → T.domain) (k : ℕ) : ℕ → T.domain :=
  fun n => v (n + k)

lemma IteratesSeq.shift {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain}
    (hv : IteratesSeq T x v) (k : ℕ) :
    IteratesSeq T (v k) (shiftedIterates v k) := by
  refine ⟨?_, fun n => ?_⟩
  · simp [shiftedIterates]
  · change (v (n + 1 + k) : H) = T (v (n + k))
    rw [show n + 1 + k = (n + k) + 1 by omega, hv.2]

lemma summable_shifted_iterates {T : H →ₗ.[ℂ] H} {v : ℕ → T.domain}
    {t q : ℝ} (ht : 0 < t) (hq : 0 ≤ q) (hqt : q < t) (k : ℕ)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial)) :
    Summable (fun n : ℕ => ‖(shiftedIterates v k n : H)‖ * q ^ n / n.factorial) := by
  exact summable_shifted_factorial_majorant
    (a := fun n : ℕ => ‖(v n : H)‖) (t := t) (q := q)
    (fun n => norm_nonneg _) ht hq hqt k (by simpa using hsum)

lemma neg_I_smul_tsum_analyticExpDerivTerm_shift_eq
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t s : ℝ} (ht : 0 < t) (hs : s ∈ Set.Ioo (-t / 2) (t / 2))
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial)) (k : ℕ) :
    (-Complex.I) • (∑' n, analyticExpDerivTerm T (shiftedIterates v k) s n) =
      analyticExp T (shiftedIterates v (k + 1)) s := by
  have hsabs : |s| < t / 2 := by
    rw [abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  let t' : ℝ := (t + 2 * |s|) / 2
  have ht' : 0 < t' := by
    dsimp [t']
    linarith [ht, abs_nonneg s]
  have h2s : 2 * |s| < t' := by
    dsimp [t']
    linarith [hsabs]
  have ht't : t' < t := by
    dsimp [t']
    linarith [hsabs]
  have hsum_k : Summable (fun n : ℕ =>
      ‖(shiftedIterates v k n : H)‖ * t' ^ n / n.factorial) :=
    summable_shifted_iterates (v := v) ht ht'.le ht't k hsum
  have hsum_k1 : Summable (fun n : ℕ =>
      ‖(shiftedIterates v (k + 1) n : H)‖ * t' ^ n / n.factorial) :=
    summable_shifted_iterates (v := v) ht ht'.le ht't (k + 1) hsum
  have hs' : s ∈ Set.Ioo (-t' / 2) (t' / 2) := by
    change -t' / 2 < s ∧ s < t' / 2
    constructor <;> linarith [neg_le_abs s, le_abs_self s, h2s]
  have hderiv := summable_analyticExpDerivTerm_of_mem_half_radius
    (T := T) (v := shiftedIterates v k) ht' hs' hsum_k
  have hsum_next : Summable (fun n : ℕ => analyticExpTerm T
      (shiftedIterates v (k + 1)) s n) := by
    exact IsAnalyticVector.summable_analyticExpTerm
      (t := t') (le_of_lt (by linarith [h2s])) hsum_k1
  let d : ℕ → H := fun n => (-Complex.I) •
    analyticExpDerivTerm T (shiftedIterates v k) s n
  have htail : HasSum (fun n => d (n + 1))
      (analyticExp T (shiftedIterates v (k + 1)) s - d 0) := by
    convert hsum_next.hasSum using 1
    · funext n
      dsimp [d, analyticExpDerivTerm, analyticExpTerm, shiftedIterates]
      rw [show n + 1 + k = n + (k + 1) by omega]
      simp only [smul_smul]
      congr 1
      rw [Nat.factorial_succ]
      field_simp [Nat.factorial_ne_zero]
      push_cast
      ring_nf
      simp [Complex.I_sq]
    · simp [analyticExp, d, analyticExpDerivTerm]
  have hd : HasSum d ((-Complex.I) •
      (∑' n, analyticExpDerivTerm T (shiftedIterates v k) s n)) := by
    simpa [d] using hderiv.hasSum.const_smul (-Complex.I)
  have hd' : HasSum d (analyticExp T (shiftedIterates v (k + 1)) s) := by
    have htail0 : HasSum (fun n => d (n + 1))
        (analyticExp T (shiftedIterates v (k + 1)) s -
          ∑ i ∈ Finset.range 1, d i) := by
      simpa [d, analyticExpDerivTerm] using htail
    have htail' := (hasSum_nat_add_iff' (G := H) (f := d)
      (g := analyticExp T (shiftedIterates v (k + 1)) s) 1).mp htail0
    simpa [d, analyticExpDerivTerm, analyticExp] using htail'
  exact hd.unique hd'

lemma IsAnalyticVector.localAnalyticOrbit_at_exp
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t a : ℝ} (ht : 0 < t) (ha : |a| < t / 2)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    Nonempty (LocalAnalyticOrbit T (analyticExp T v a)) := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  have hTcloseSym : T.closure.IsSymmetric := hsym.closure hdenseDomain
  have hTcloseDense : T.closure.HasDenseDomain := hdenseDomain.closure
  have hspan_le : Submodule.span ℂ {x : H | T.IsAnalyticVector x} ≤
      Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x} := by
    apply Submodule.span_mono
    intro z hz
    exact IsAnalyticVector.for_closure hz
  have hclosedense :
      (Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x}).topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    exact hdense ▸ Submodule.topologicalClosure_mono hspan_le
  have hsabs : |a| < t / 2 := ha
  let t' : ℝ := (t + 2 * |a|) / 2
  have ht' : 0 < t' := by
    dsimp [t']
    linarith [ht, abs_nonneg a]
  have h2a : 2 * |a| < t' := by
    dsimp [t']
    linarith [hsabs]
  have ht't : t' < t := by
    dsimp [t']
    linarith [hsabs]
  have hs' : a ∈ Set.Ioo (-t' / 2) (t' / 2) := by
    change -t' / 2 < a ∧ a < t' / 2
    constructor <;> linarith [neg_le_abs a, le_abs_self a, h2a]
  have hsum_shift : ∀ k : ℕ, Summable (fun n : ℕ =>
      ‖(shiftedIterates v k n : H)‖ * t' ^ n / n.factorial) := by
    intro k
    exact summable_shifted_iterates (v := v) ht ht'.le ht't k hsum
  let w : ℕ → T.closure.domain := fun k =>
    ⟨analyticExp T (shiftedIterates v k) a,
      analyticExp_mem_closure_domain (IteratesSeq.shift hv k) hT hs' (hsum_shift k)⟩
  have hw : IteratesSeq T.closure (analyticExp T v a) w := by
    refine ⟨?_, fun k => ?_⟩
    · change analyticExp T (shiftedIterates v 0) a = analyticExp T v a
      congr 2
    · have happly := closure_analyticExp_apply (IteratesSeq.shift hv k) hT hs' (hsum_shift k)
      have ha_mem : a ∈ Set.Ioo (-t / 2) (t / 2) := by
        change -t / 2 < a ∧ a < t / 2
        exact ⟨by linarith [neg_le_abs a, ha], by linarith [le_abs_self a, ha]⟩
      have hshift := neg_I_smul_tsum_analyticExpDerivTerm_shift_eq hv ht ha_mem hsum k
      change analyticExp T (shiftedIterates v (k + 1)) a =
        T.closure ⟨analyticExp T (shiftedIterates v k) a, _⟩
      rw [happly, hshift]
  have hsum_half : Summable (fun k : ℕ =>
      ‖(shiftedIterates v 0 k : H)‖ * (t / 2) ^ k / k.factorial) := by
    exact summable_shifted_iterates (v := v) ht (by positivity) (by linarith) 0 hsum
  have hsum_w : Summable (fun k : ℕ => ‖(w k : H)‖ * (t / 2) ^ k / k.factorial) := by
    refine hsum_half.congr (fun k => ?_)
    have hnorm := analyticExp_norm_eq_norm hsym hdense (IteratesSeq.shift hv k) hs' (hsum_shift k)
    change ‖(shiftedIterates v 0 k : H)‖ * (t / 2) ^ k / k.factorial =
      ‖analyticExp T (shiftedIterates v k) a‖ * (t / 2) ^ k / k.factorial
    rw [hnorm]
    simp [shiftedIterates]
  have hTclose : T.closure.closure = T.closure := hT.closure_isClosed.closure_eq
  have hSclosable : T.closure.IsClosable := hT.closure_isClosed.isClosable
  have hr : 0 < (t / 2) / 2 := by linarith
  have happly_closure : ∀ (z : H) (hz : z ∈ T.closure.domain)
      (hz' : z ∈ T.closure.closure.domain),
      T.closure.closure ⟨z, hz'⟩ = T.closure ⟨z, hz⟩ := by
    intro z hz hz'
    have hgraph : (z, T.closure.closure ⟨z, hz'⟩) ∈ T.closure.graph := by
      have hgraph_eq : T.closure.closure.graph = T.closure.graph :=
        congrArg (fun R : H →ₗ.[ℂ] H => R.graph) hTclose
      exact hgraph_eq ▸ T.closure.closure.mem_graph ⟨z, hz'⟩
    exact T.closure.mem_graph_snd_inj' hgraph
      (T.closure.mem_graph ⟨z, hz⟩) rfl
  refine ⟨
    { radius := (t / 2) / 2
      radius_pos := hr
      toFun := fun s => analyticExp T.closure w s
      initial := analyticExp_zero hw
      mem_domain := fun s hs => by
        rw [abs_lt] at hs
        have hs' : s ∈ Set.Ioo (-(t / 2) / 2) ((t / 2) / 2) := by
          change -(t / 2) / 2 < s ∧ s < (t / 2) / 2
          exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have hd := analyticExp_mem_closure_domain hw hSclosable hs' hsum_w
        simpa only [hTclose] using hd
      hasDerivAt := fun s hs => by
        rw [abs_lt] at hs
        have hs' : s ∈ Set.Ioo (-(t / 2) / 2) ((t / 2) / 2) := by
          change -(t / 2) / 2 < s ∧ s < (t / 2) / 2
          exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have hd := analyticExp_hasDerivAt_eq_smul_closure hw hSclosable hs' hsum_w
        have hz : analyticExp T.closure w s ∈ T.closure.domain := by
          simpa only [hTclose] using analyticExp_mem_closure_domain hw hSclosable hs' hsum_w
        convert hd using 1
        congr 1
        exact (happly_closure _ hz
          (analyticExp_mem_closure_domain hw hSclosable hs' hsum_w)).symm
      , norm_eq := fun s hs => by
        rw [abs_lt] at hs
        have hs' : s ∈ Set.Ioo (-(t / 2) / 2) ((t / 2) / 2) := by
          change -(t / 2) / 2 < s ∧ s < (t / 2) / 2
          exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        exact analyticExp_norm_eq_norm hTcloseSym hclosedense hw hs' hsum_w }⟩

/-- The change-of-origin construction exposes the actual analytic-vector witness of the reached
state.  This is the recursive part of the finite-radius continuation argument: a local chart alone
does not provide enough data to apply the same construction again, whereas this theorem supplies
the shifted iterates and their smaller-radius factorial majorant for the closed operator. -/
lemma IsAnalyticVector.analyticExp_at_isAnalyticVector
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t a : ℝ} (ht : 0 < t) (ha : |a| < t / 2)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    T.closure.IsAnalyticVector (analyticExp T v a) := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  have hspan_le : Submodule.span ℂ {x : H | T.IsAnalyticVector x} ≤
      Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x} := by
    apply Submodule.span_mono
    intro z hz
    exact IsAnalyticVector.for_closure hz
  have hclosedense :
      (Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x}).topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    exact hdense ▸ Submodule.topologicalClosure_mono hspan_le
  let t' : ℝ := (t + 2 * |a|) / 2
  have ht' : 0 < t' := by
    dsimp [t']
    linarith [ht, abs_nonneg a]
  have ht't : t' < t := by
    dsimp [t']
    linarith [ha]
  have hsum_shift : ∀ k : ℕ, Summable (fun n : ℕ =>
      ‖(shiftedIterates v k n : H)‖ * t' ^ n / n.factorial) := by
    intro k
    exact summable_shifted_iterates (v := v) ht ht'.le ht't k hsum
  have hs' : a ∈ Set.Ioo (-t' / 2) (t' / 2) := by
    change -t' / 2 < a ∧ a < t' / 2
    have h2a : 2 * |a| < t' := by
      dsimp [t']
      linarith [ha]
    constructor <;> linarith [neg_le_abs a, le_abs_self a, h2a]
  let w : ℕ → T.closure.domain := fun k =>
    ⟨analyticExp T (shiftedIterates v k) a,
      analyticExp_mem_closure_domain (IteratesSeq.shift hv k) hT hs'
        (hsum_shift k)⟩
  have hw : IteratesSeq T.closure (analyticExp T v a) w := by
    refine ⟨?_, fun k => ?_⟩
    · change analyticExp T (shiftedIterates v 0) a = analyticExp T v a
      congr 2
    · have happly := closure_analyticExp_apply (IteratesSeq.shift hv k) hT hs'
        (hsum_shift k)
      have ha_mem : a ∈ Set.Ioo (-t / 2) (t / 2) := by
        change -t / 2 < a ∧ a < t / 2
        exact ⟨by linarith [neg_le_abs a, ha], by linarith [le_abs_self a, ha]⟩
      have hshift := neg_I_smul_tsum_analyticExpDerivTerm_shift_eq hv ht ha_mem hsum k
      change analyticExp T (shiftedIterates v (k + 1)) a =
        T.closure ⟨analyticExp T (shiftedIterates v k) a, _⟩
      rw [happly, hshift]
  have hsum_half : Summable (fun k : ℕ =>
      ‖(shiftedIterates v 0 k : H)‖ * (t / 2) ^ k / k.factorial) := by
    exact summable_shifted_iterates (v := v) ht (by positivity) (by linarith) 0 hsum
  have hsum_w : Summable (fun k : ℕ =>
      ‖(w k : H)‖ * (t / 2) ^ k / k.factorial) := by
    refine hsum_half.congr (fun k => ?_)
    have hnorm := analyticExp_norm_eq_norm hsym hdense (IteratesSeq.shift hv k) hs'
      (hsum_shift k)
    change ‖(shiftedIterates v 0 k : H)‖ * (t / 2) ^ k / k.factorial =
      ‖analyticExp T (shiftedIterates v k) a‖ * (t / 2) ^ k / k.factorial
    rw [hnorm]
    simp [shiftedIterates]
  exact ⟨w, hw, t / 2, by linarith, hsum_w⟩

/-- Sharp-radius form of `analyticExp_at_isAnalyticVector`: changing origin inside the
half-radius does not consume the analytic radius.  Every strictly smaller radius than the
original one remains available at the reached state.  This is the uniform-radius estimate used
to iterate local charts indefinitely. -/
lemma IsAnalyticVector.analyticExp_at_isAnalyticVector_witness_of_radius
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t a q : ℝ} (ht : 0 < t) (ha : |a| < t / 2) (hq : 0 < q) (hqt : q < t)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    ∃ w : ℕ → T.closure.domain, IteratesSeq T.closure (analyticExp T v a) w ∧
      0 < q ∧ Summable (fun n : ℕ => ‖(w n : H)‖ * q ^ n / n.factorial) := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  have hspan_le : Submodule.span ℂ {x : H | T.IsAnalyticVector x} ≤
      Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x} := by
    apply Submodule.span_mono
    intro z hz
    exact IsAnalyticVector.for_closure hz
  have hclosedense :
      (Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x}).topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    exact hdense ▸ Submodule.topologicalClosure_mono hspan_le
  let u : ℝ := (max (2 * |a|) q + t) / 2
  have h2a : 2 * |a| < t := by linarith [ha]
  have hmax : max (2 * |a|) q < t := (max_lt_iff).2 ⟨h2a, hqt⟩
  have hmax_nonneg : 0 ≤ max (2 * |a|) q :=
    le_trans (by positivity) (le_max_left _ _)
  have hqmax : q ≤ max (2 * |a|) q := le_max_right _ _
  have h2amax : 2 * |a| ≤ max (2 * |a|) q := le_max_left _ _
  have hu : 0 < u := by
    dsimp [u]
    linarith [ht, hmax_nonneg]
  have hqu : q < u := by
    dsimp [u]
    linarith [hmax, hqmax]
  have h2au : 2 * |a| < u := by
    dsimp [u]
    linarith [hmax, h2amax]
  have hut : u < t := by
    dsimp [u]
    linarith [hmax]
  have hs' : a ∈ Set.Ioo (-u / 2) (u / 2) := by
    change -u / 2 < a ∧ a < u / 2
    constructor <;> linarith [neg_le_abs a, le_abs_self a, h2au]
  have hsum_u : ∀ k : ℕ, Summable (fun n : ℕ =>
      ‖(shiftedIterates v k n : H)‖ * u ^ n / n.factorial) := by
    intro k
    exact summable_shifted_iterates (v := v) ht hu.le hut k hsum
  have hsum_q : ∀ k : ℕ, Summable (fun n : ℕ =>
      ‖(shiftedIterates v k n : H)‖ * q ^ n / n.factorial) := by
    intro k
    exact summable_shifted_iterates (v := v) ht (le_of_lt hq) hqt k hsum
  let w : ℕ → T.closure.domain := fun k =>
    ⟨analyticExp T (shiftedIterates v k) a,
      analyticExp_mem_closure_domain (IteratesSeq.shift hv k) hT hs'
        (hsum_u k)⟩
  have hw : IteratesSeq T.closure (analyticExp T v a) w := by
    refine ⟨?_, fun k => ?_⟩
    · change analyticExp T (shiftedIterates v 0) a = analyticExp T v a
      congr 2
    · have happly := closure_analyticExp_apply (IteratesSeq.shift hv k) hT hs'
        (hsum_u k)
      have ha_mem : a ∈ Set.Ioo (-t / 2) (t / 2) := by
        change -t / 2 < a ∧ a < t / 2
        exact ⟨by linarith [neg_le_abs a, ha], by linarith [le_abs_self a, ha]⟩
      have hshift := neg_I_smul_tsum_analyticExpDerivTerm_shift_eq hv ht ha_mem hsum k
      change analyticExp T (shiftedIterates v (k + 1)) a =
        T.closure ⟨analyticExp T (shiftedIterates v k) a, _⟩
      rw [happly, hshift]
  have hsum_w : Summable (fun k : ℕ =>
      ‖(w k : H)‖ * q ^ k / k.factorial) := by
    have hsum_shift_q := hsum_q
    refine (hsum_shift_q 0).congr (fun k => ?_)
    have hnorm := analyticExp_norm_eq_norm hsym hdense (IteratesSeq.shift hv k) hs'
      (hsum_u k)
    change ‖(shiftedIterates v 0 k : H)‖ * q ^ k / k.factorial =
      ‖analyticExp T (shiftedIterates v k) a‖ * q ^ k / k.factorial
    rw [hnorm]
    simp [shiftedIterates]
  exact ⟨w, hw, hq, hsum_w⟩

lemma IsAnalyticVector.analyticExp_at_isAnalyticVector_of_radius
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t a q : ℝ} (ht : 0 < t) (ha : |a| < t / 2) (hq : 0 < q) (hqt : q < t)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    T.closure.IsAnalyticVector (analyticExp T v a) := by
  obtain ⟨w, hw, hq', hsum_w⟩ :=
    IsAnalyticVector.analyticExp_at_isAnalyticVector_witness_of_radius
      hv ht ha hq hqt hsum hsym hdense
  exact ⟨w, hw, q, hq', hsum_w⟩

/-! ### Gluing local charts

The following cover is deliberately an interface: the analytic change-of-origin estimate belongs
to the finite-radius part of Nelson's theorem, while the topological gluing is independent of it. -/

structure LocalOrbitCover (T : H →ₗ.[ℂ] H) (x : H) where
  state : ℕ → H
  center : ℕ → ℝ
  chart : ∀ n, LocalAnalyticOrbit T (state n)
  center_zero : center 0 = 0
  state_zero : state 0 = x
  state_norm : ∀ n, ‖state n‖ = ‖x‖
  cover : ∀ s : ℝ, ∃ n : ℕ, |s - center n| < (chart n).radius
  compatible : ∀ (m n : ℕ) (s : ℝ),
    |s - center m| < (chart m).radius → |s - center n| < (chart n).radius →
      chart m (s - center m) = chart n (s - center n)

/-! A cover may use smaller symmetric cores of its charts.  This avoids requiring compatibility on
the full overlap of two symmetric charts, which need not be contained in a recentered symmetric
domain. -/

structure LocalOrbitCoreCover (T : H →ₗ.[ℂ] H) (x : H) where
  state : ℕ → H
  center : ℕ → ℝ
  chart : ∀ n, LocalAnalyticOrbit T (state n)
  coreRadius : ℕ → ℝ
  core_pos : ∀ n, 0 < coreRadius n
  core_le : ∀ n, coreRadius n ≤ (chart n).radius
  center_zero : center 0 = 0
  state_zero : state 0 = x
  state_norm : ∀ n, ‖state n‖ = ‖x‖
  cover : ∀ s : ℝ, ∃ n : ℕ, |s - center n| < coreRadius n
  compatible : ∀ (m n : ℕ) (s : ℝ),
    |s - center m| < coreRadius m → |s - center n| < coreRadius n →
      chart m (s - center m) = chart n (s - center n)

lemma exists_int_center_of_pos_step {δ R s : ℝ} (hδ : 0 < δ) (hδR : δ < R) :
    ∃ n : ℤ, |s - (n : ℝ) * δ| < R := by
  let n : ℤ := ⌊s / δ⌋
  have hfloor : (n : ℝ) ≤ s / δ := by
    dsimp [n]
    exact Int.floor_le _
  have hnext : s / δ < (n : ℝ) + 1 := by
    dsimp [n]
    exact Int.lt_floor_add_one _
  have hlow : (n : ℝ) * δ ≤ s := by
    have := (le_div_iff₀ hδ).mp hfloor
    simpa [mul_comm] using this
  have hupp : s < (n : ℝ) * δ + δ := by
    have := (div_lt_iff₀ hδ).mp hnext
    simpa [add_mul] using this
  refine ⟨n, ?_⟩
  have hnonneg : 0 ≤ s - (n : ℝ) * δ := sub_nonneg.mpr hlow
  rw [abs_of_nonneg hnonneg]
  linarith

/-! The purely one-dimensional part of integer-chart gluing.  If consecutive charts agree after
translation by `δ`, agreement propagates along the whole integer chain.  The endpoint hypotheses
are enough: the distance to the affine integer grid is convex, so every intermediate coordinate
remains in the same core. -/
lemma eq_of_adjacent_of_le
    {F : ℤ → ℝ → H} {δ R s : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hadj : ∀ k : ℤ, ∀ z : ℝ, |z| < R →
      F k (δ + z) = F (k + 1) z)
    {m n : ℤ} (hmn : m ≤ n)
    (hm : |s - (m : ℝ) * δ| < R) (hn : |s - (n : ℝ) * δ| < R) :
    F m (s - (m : ℝ) * δ) = F n (s - (n : ℝ) * δ) := by
  have hinter : ∀ {k : ℤ}, m ≤ k → k ≤ n →
      |s - (k : ℝ) * δ| < R := by
    intro k hmk hkn
    have hmk' : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have hkn' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hmkδ : (m : ℝ) * δ ≤ (k : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hmk' hδ.le
    have hknδ : (k : ℝ) * δ ≤ (n : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hkn' hδ.le
    rw [abs_lt] at hm hn ⊢
    by_cases hsk : s < (k : ℝ) * δ
    · constructor
      · linarith [hn.1]
      · linarith
    · have hks : (k : ℝ) * δ ≤ s := le_of_not_gt hsk
      constructor
      · linarith
      · linarith [hm.2]
  have hchain : ∀ (k : ℤ), m ≤ k → k ≤ n → |s - (k : ℝ) * δ| < R →
      F m (s - (m : ℝ) * δ) = F k (s - (k : ℝ) * δ) := by
    intro k hmk
    refine Int.leInduction (motive := fun j _ =>
      j ≤ n → |s - (j : ℝ) * δ| < R →
        F m (s - (m : ℝ) * δ) = F j (s - (j : ℝ) * δ)) ?_ ?_ k hmk
    · intro _ _
      rfl
    · intro j hj ih hj1n hj1
      have hjn : j ≤ n := by omega
      have hj0 : |s - (j : ℝ) * δ| < R := hinter hj hjn
      have hprev := ih hjn hj0
      have hstep := hadj j (s - ((j + 1 : ℤ) : ℝ) * δ) hj1
      have hstep' : F j (s - (j : ℝ) * δ) =
          F (j + 1) (s - ((j + 1 : ℤ) : ℝ) * δ) := by
        convert hstep using 1 <;> push_cast <;> ring
      exact hprev.trans hstep'
  exact hchain n hmn le_rfl hn

lemma eq_of_adjacent
    {F : ℤ → ℝ → H} {δ R s : ℝ} (hδ : 0 < δ) (hR : 0 < R)
    (hadj : ∀ k : ℤ, ∀ z : ℝ, |z| < R →
      F k (δ + z) = F (k + 1) z)
    {m n : ℤ}
    (hm : |s - (m : ℝ) * δ| < R) (hn : |s - (n : ℝ) * δ| < R) :
    F m (s - (m : ℝ) * δ) = F n (s - (n : ℝ) * δ) := by
  rcases le_total m n with hmn | hnm
  · exact eq_of_adjacent_of_le hδ hR hadj hmn hm hn
  · exact (eq_of_adjacent_of_le hδ hR hadj hnm hn hm).symm

/-- Reindex a bi-infinite integer-indexed core cover by `ℕ`.  The reindexing is purely set-theoretic
and uses `Equiv.intEquivNat`; it lets the existing choice-based gluing implementation remain
backwards-compatible while continuation is naturally developed on integer time centers. -/
noncomputable def LocalOrbitCoreCover.of_int_index
    {T : H →ₗ.[ℂ] H} {x : H}
    (state : ℤ → H) (center coreRadius : ℤ → ℝ)
    (chart : ∀ n : ℤ, LocalAnalyticOrbit T (state n))
    (core_pos : ∀ n, 0 < coreRadius n)
    (core_le : ∀ n, coreRadius n ≤ (chart n).radius)
    (center_zero : center 0 = 0) (state_zero : state 0 = x)
    (state_norm : ∀ n, ‖state n‖ = ‖x‖)
    (cover : ∀ s : ℝ, ∃ n : ℤ, |s - center n| < coreRadius n)
    (compatible : ∀ (m n : ℤ) (s : ℝ),
      |s - center m| < coreRadius m → |s - center n| < coreRadius n →
      chart m (s - center m) = chart n (s - center n)) :
    LocalOrbitCoreCover T x where
  state := fun n => state (Equiv.intEquivNat.symm n)
  center := fun n => center (Equiv.intEquivNat.symm n)
  chart := fun n => chart (Equiv.intEquivNat.symm n)
  coreRadius := fun n => coreRadius (Equiv.intEquivNat.symm n)
  core_pos := fun n => core_pos _
  core_le := fun n => core_le _
  center_zero := by
    have hzero : Equiv.intEquivNat.symm 0 = (0 : ℤ) := by rfl
    simpa [hzero] using center_zero
  state_zero := by
    have hzero : Equiv.intEquivNat.symm 0 = (0 : ℤ) := by rfl
    simpa [hzero] using state_zero
  state_norm := fun n => state_norm _
  cover := by
    intro s
    obtain ⟨n, hn⟩ := cover s
    exact ⟨Equiv.intEquivNat n, by simpa only [Equiv.symm_apply_apply] using hn⟩
  compatible := by
    intro m n s hm hn
    exact compatible _ _ s hm hn

/-! Package the grid argument with the abstract core-cover certificate.  The analytic work needed
to construct the charts is intentionally not hidden here: callers only have to provide the local
adjacent equality, while this lemma supplies coverage and all non-adjacent compatibility. -/
noncomputable def LocalOrbitCoreCover.of_adjacent_int_index
    {T : H →ₗ.[ℂ] H} {x : H} {δ R : ℝ}
    (hδ : 0 < δ) (hδR : δ < R)
    (state : ℤ → H) (chart : ∀ n : ℤ, LocalAnalyticOrbit T (state n))
    (core_pos : 0 < R) (core_le : ∀ n : ℤ, R ≤ (chart n).radius)
    (state_zero : state 0 = x)
    (state_norm : ∀ n : ℤ, ‖state n‖ = ‖x‖)
    (hadj : ∀ n : ℤ, ∀ z : ℝ, |z| < R →
      chart n (δ + z) = chart (n + 1) z) :
    LocalOrbitCoreCover T x := by
  let center : ℤ → ℝ := fun n => (n : ℝ) * δ
  have hcenter_zero : center 0 = 0 := by
    dsimp [center]
    norm_num
  have hcover : ∀ s : ℝ, ∃ n : ℤ, |s - center n| < R := by
    intro s
    obtain ⟨n, hn⟩ := exists_int_center_of_pos_step hδ hδR
    exact ⟨n, by simpa [center] using hn⟩
  exact LocalOrbitCoreCover.of_int_index state center (fun _ => R) chart
    (fun _ => core_pos) core_le hcenter_zero state_zero state_norm hcover
    (fun m n s hm hn => eq_of_adjacent hδ core_pos hadj (by simpa [center] using hm)
      (by simpa [center] using hn))

noncomputable def LocalOrbitCoreCover.toLocalOrbitCover
    {T : H →ₗ.[ℂ] H} {x : H} (C : LocalOrbitCoreCover T x) : LocalOrbitCover T x where
  state := C.state
  center := C.center
  chart := fun n => (C.chart n).restrictTo (C.core_pos n) (C.core_le n)
  center_zero := C.center_zero
  state_zero := C.state_zero
  state_norm := C.state_norm
  cover := by
    intro s
    obtain ⟨n, hn⟩ := C.cover s
    exact ⟨n, hn⟩
  compatible := by
    intro m n s hm hn
    exact C.compatible m n s hm hn

noncomputable def LocalOrbitCover.toGlobal {T : H →ₗ.[ℂ] H} {x : H}
    (C : LocalOrbitCover T x) : GlobalAnalyticOrbit T x where
  toFun := fun s => C.chart (Classical.choose (C.cover s))
      (s - C.center (Classical.choose (C.cover s)))
  initial := by
    let n : ℕ := Classical.choose (C.cover 0)
    have hn : |0 - C.center n| < (C.chart n).radius := Classical.choose_spec (C.cover 0)
    have h0 : |0 - C.center 0| < (C.chart 0).radius := by
      simpa [C.center_zero] using (C.chart 0).radius_pos
    have hcompat := C.compatible 0 n 0 h0 hn
    calc
      C.chart (Classical.choose (C.cover 0))
          (0 - C.center (Classical.choose (C.cover 0))) = C.chart 0 (0 - C.center 0) := by
            simpa [n] using hcompat.symm
      _ = C.state 0 := by simpa [C.center_zero] using (C.chart 0).initial
      _ = x := C.state_zero
  mem_domain := by
    intro s
    let n : ℕ := Classical.choose (C.cover s)
    have hn : |s - C.center n| < (C.chart n).radius := Classical.choose_spec (C.cover s)
    exact (C.chart n).mem_domain (s - C.center n) hn
  hasDerivAt := by
    intro s
    let n : ℕ := Classical.choose (C.cover s)
    have hn : |s - C.center n| < (C.chart n).radius := Classical.choose_spec (C.cover s)
    have hsI : s ∈ Set.Ioo (C.center n - (C.chart n).radius)
        (C.center n + (C.chart n).radius) := by
      change C.center n - (C.chart n).radius < s ∧
        s < C.center n + (C.chart n).radius
      rw [abs_lt] at hn
      constructor <;> linarith
    have hlocal := (C.chart n).hasDerivAt (s - C.center n) hn
    have hcomp := hlocal.comp_add_const s (-C.center n)
    have hevent : ∀ᶠ q : ℝ in 𝓝 s,
        (fun r : ℝ => C.chart (Classical.choose (C.cover r))
            (r - C.center (Classical.choose (C.cover r)))) q =
          (fun r : ℝ => C.chart n (r + -C.center n)) q := by
      filter_upwards [isOpen_Ioo.mem_nhds hsI] with q hq
      have hq' : |q - C.center n| < (C.chart n).radius := by
        change |q - C.center n| < (C.chart n).radius
        rw [abs_lt]
        change C.center n - (C.chart n).radius < q ∧
          q < C.center n + (C.chart n).radius at hq
        constructor <;> linarith
      have hchosen := Classical.choose_spec (C.cover q)
      simpa [sub_eq_add_neg] using
        (C.compatible n (Classical.choose (C.cover q)) q hq' hchosen).symm
    have hderiv := hcomp.congr_of_eventuallyEq hevent
    convert hderiv using 1
  norm_eq := by
    intro s
    let n : ℕ := Classical.choose (C.cover s)
    have hn : |s - C.center n| < (C.chart n).radius := Classical.choose_spec (C.cover s)
    calc
      ‖C.chart (Classical.choose (C.cover s))
          (s - C.center (Classical.choose (C.cover s)))‖ = ‖C.state n‖ :=
            (C.chart n).norm_eq (s - C.center n) hn
      _ = ‖x‖ := C.state_norm n

noncomputable def LocalOrbitCoreCover.toGlobal {T : H →ₗ.[ℂ] H} {x : H}
    (C : LocalOrbitCoreCover T x) : GlobalAnalyticOrbit T x :=
  C.toLocalOrbitCover.toGlobal

lemma LocalOrbitCoreCover.toGlobal_nonempty {T : H →ₗ.[ℂ] H} {x : H}
    (C : LocalOrbitCoreCover T x) : Nonempty (GlobalAnalyticOrbit T x) :=
  ⟨C.toGlobal⟩

lemma LocalOrbitCover.toGlobal_nonempty {T : H →ₗ.[ℂ] H} {x : H}
    (C : LocalOrbitCover T x) : Nonempty (GlobalAnalyticOrbit T x) :=
  ⟨C.toGlobal⟩

/-- A global orbit for the closure of a closable operator is also a global orbit for the original
operator.  The only issue is the dependent domain proof in the differential equation; the closed
graph identity `T.closure.closure = T.closure` resolves it explicitly. -/
lemma of_closure {T : H →ₗ.[ℂ] H} {x : H} (hT : T.IsClosable)
    (U : GlobalAnalyticOrbit T.closure x) : Nonempty (GlobalAnalyticOrbit T x) := by
  have hclosed : T.closure.closure = T.closure := hT.closure_isClosed.closure_eq
  have happly : ∀ (z : H) (hz : z ∈ T.closure.domain)
      (hz' : z ∈ T.closure.closure.domain),
      T.closure.closure ⟨z, hz'⟩ = T.closure ⟨z, hz⟩ := by
    intro z hz hz'
    have hgraph : (z, T.closure.closure ⟨z, hz'⟩) ∈ T.closure.graph := by
      have hgraph_eq : T.closure.closure.graph = T.closure.graph :=
        congrArg (fun R : H →ₗ.[ℂ] H => R.graph) hclosed
      exact hgraph_eq ▸ T.closure.closure.mem_graph ⟨z, hz'⟩
    exact T.closure.mem_graph_snd_inj' hgraph
      (T.closure.mem_graph ⟨z, hz⟩) rfl
  refine ⟨
    { toFun := U
      initial := U.initial
      mem_domain := fun s => by
        simpa only [hclosed] using U.mem_domain s
      hasDerivAt := fun s => by
        have hz' : U s ∈ T.closure.closure.domain := U.mem_domain s
        have hz : U s ∈ T.closure.domain := by
          simpa only [hclosed] using hz'
        have hd := U.hasDerivAt s
        convert hd using 1
        congr 1
        exact (happly _ hz hz').symm
      norm_eq := U.norm_eq }⟩

lemma inner_deficiency_eq_zero
    {T : H →ₗ.[ℂ] H} {x : H} (U : GlobalAnalyticOrbit T x) {y : H}
    (hy : y ∈ (T.closure - Complex.I • 1).toFun.rangeᗮ) :
    ⟪y, x⟫_ℂ = 0 := by
  let f : ℝ → ℂ := fun s => ⟪y, U s⟫_ℂ
  let g : ℝ → ℂ := fun s => (Real.exp s : ℂ) * f s
  have hg : ∀ s : ℝ, HasDerivAt g 0 s := by
    intro s
    have hdom : U s ∈ T.closure.domain := U.mem_domain s
    let z : (T.closure - Complex.I • 1).domain :=
      ⟨U s, by
        rw [sub_domain]
        exact ⟨hdom, by simp⟩⟩
    have horth : ⟪y, T.closure ⟨U s, hdom⟩ -
        Complex.I • U s⟫_ℂ = 0 := by
      have hz := (Submodule.mem_orthogonal' _ y).mp hy
        ((T.closure - Complex.I • 1).toFun z) ⟨z, rfl⟩
      simpa [z, sub_apply] using hz
    have hrelation : ⟪y, T.closure ⟨U s, hdom⟩⟫_ℂ =
        Complex.I * ⟪y, U s⟫_ℂ := by
      rw [inner_sub_right, inner_smul_right] at horth
      exact sub_eq_zero.mp horth
    have hf0 : HasDerivAt (fun r : ℝ => ⟪y, U r⟫_ℂ)
        (-⟪y, U s⟫_ℂ) s := by
      have hinner := (hasDerivAt_const (x := s) y).inner ℂ (U.hasDerivAt s)
      convert hinner using 1
      · rfl
      · simp only [inner_zero_left, inner_smul_right]
        rw [hrelation]
        ring_nf
        rw [Complex.I_sq]
        simp
    have hf : HasDerivAt f (-f s) s := by
      simpa [f] using hf0
    have he : HasDerivAt (fun r : ℝ => (Real.exp r : ℂ)) (Real.exp s) s :=
      (Real.hasDerivAt_exp s).ofReal_comp
    have hp := he.mul hf
    have hz : (Real.exp s : ℂ) * f s + (Real.exp s : ℂ) * (-f s) = 0 := by
      ring
    have hp' : HasDerivAt ((fun r : ℝ => (Real.exp r : ℂ)) * f) 0 s := by
      simpa only [hz] using hp
    change HasDerivAt (fun r : ℝ => (Real.exp r : ℂ) * f r) 0 s
    convert hp' using 1
    funext r
    rfl
  have hconst : ∀ s : ℝ, g s = g 0 := by
    intro s
    exact is_const_of_deriv_eq_zero (fun r => (hg r).differentiableAt)
      (fun r => (hg r).deriv) s 0
  have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hupper : Filter.Tendsto
      (fun n : ℕ => Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖)) atTop (𝓝 0) := by
    simpa only [Pi.mul_apply, zero_mul] using
      hexp.mul (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => ‖y‖ * ‖x‖) atTop (𝓝 (‖y‖ * ‖x‖)))
  have hnorm_lim : Filter.Tendsto (fun n : ℕ => ‖g (-(n : ℝ))‖) atTop (𝓝 0) := by
    refine squeeze_zero' (f := fun n : ℕ => ‖g (-(n : ℝ))‖)
      (g := fun n : ℕ => Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖))
      (Filter.Eventually.of_forall fun n => norm_nonneg _)
      (Filter.Eventually.of_forall (fun n => ?_)) hupper
    calc
      ‖g (-(n : ℝ))‖ = Real.exp (-(n : ℝ)) * ‖⟪y, U (-(n : ℝ))⟫_ℂ‖ := by
        dsimp [g, f]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-(n : ℝ)) * (‖y‖ * ‖U (-(n : ℝ))‖) := by
        gcongr
        exact norm_inner_le_norm _ _
      _ = Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖) := by
        rw [U.norm_eq]
  have hlim : Filter.Tendsto (fun n : ℕ => g (-(n : ℝ))) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_lim
  have hconst_zero : g 0 = 0 := by
    have hc : Tendsto (fun _ : ℕ => g 0) atTop (𝓝 0) :=
      hlim.congr' (Filter.Eventually.of_forall fun n => hconst (-(n : ℝ)))
    exact (tendsto_nhds_unique hc tendsto_const_nhds).symm
  simpa [g, f, U.initial] using hconst_zero

lemma inner_deficiency_eq_zero_neg
    {T : H →ₗ.[ℂ] H} {x : H} (U : GlobalAnalyticOrbit T x) {y : H}
    (hy : y ∈ (T.closure - (-Complex.I) • 1).toFun.rangeᗮ) :
    ⟪y, x⟫_ℂ = 0 := by
  let f : ℝ → ℂ := fun s => ⟪y, U s⟫_ℂ
  let g : ℝ → ℂ := fun s => (Real.exp (-s) : ℂ) * f s
  have hg : ∀ s : ℝ, HasDerivAt g 0 s := by
    intro s
    have hdom : U s ∈ T.closure.domain := U.mem_domain s
    let z : (T.closure - (-Complex.I) • 1).domain :=
      ⟨U s, by
        rw [sub_domain]
        exact ⟨hdom, by simp⟩⟩
    have horth : ⟪y, T.closure ⟨U s, hdom⟩ -
        (-Complex.I) • U s⟫_ℂ = 0 := by
      have hz := (Submodule.mem_orthogonal' _ y).mp hy
        ((T.closure - (-Complex.I) • 1).toFun z) ⟨z, rfl⟩
      simpa [z, sub_apply] using hz
    have hrelation : ⟪y, T.closure ⟨U s, hdom⟩⟫_ℂ =
        (-Complex.I) * ⟪y, U s⟫_ℂ := by
      rw [inner_sub_right, inner_smul_right] at horth
      exact sub_eq_zero.mp horth
    have hf0 : HasDerivAt (fun r : ℝ => ⟪y, U r⟫_ℂ)
        (⟪y, U s⟫_ℂ) s := by
      have hinner := (hasDerivAt_const (x := s) y).inner ℂ (U.hasDerivAt s)
      convert hinner using 1
      · rfl
      · simp only [inner_zero_left, inner_smul_right]
        rw [hrelation]
        ring_nf
        rw [Complex.I_sq]
        simp
    have hf : HasDerivAt f (f s) s := by
      simpa [f] using hf0
    have he : HasDerivAt (fun r : ℝ => (Real.exp (-r) : ℂ))
        (-Real.exp (-s)) s := by
      have hreal := (Real.hasDerivAt_exp (-s)).scomp s
        (hasDerivAt_id' (𝕜 := ℝ) s).neg
      convert hreal.ofReal_comp using 1
      · funext r
        rfl
      · simp
    have hp := he.mul hf
    have hz : (-Real.exp (-s) : ℂ) * f s + (Real.exp (-s) : ℂ) * f s = 0 := by
      ring
    have hp' : HasDerivAt ((fun r : ℝ => (Real.exp (-r) : ℂ)) * f) 0 s := by
      simpa only [hz] using hp
    change HasDerivAt (fun r : ℝ => (Real.exp (-r) : ℂ) * f r) 0 s
    convert hp' using 1
    funext r
    rfl
  have hconst : ∀ s : ℝ, g s = g 0 := by
    intro s
    exact is_const_of_deriv_eq_zero (fun r => (hg r).differentiableAt)
      (fun r => (hg r).deriv) s 0
  have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop :
          Filter.Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hupper : Filter.Tendsto
      (fun n : ℕ => Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖)) atTop (𝓝 0) := by
    simpa only [Pi.mul_apply, zero_mul] using
      hexp.mul (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => ‖y‖ * ‖x‖) atTop (𝓝 (‖y‖ * ‖x‖)))
  have hnorm_lim : Filter.Tendsto (fun n : ℕ => ‖g (n : ℝ)‖) atTop (𝓝 0) := by
    refine squeeze_zero' (f := fun n : ℕ => ‖g (n : ℝ)‖)
      (g := fun n : ℕ => Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖))
      (Filter.Eventually.of_forall fun n => norm_nonneg _)
      (Filter.Eventually.of_forall (fun n => ?_)) hupper
    calc
      ‖g (n : ℝ)‖ = Real.exp (-(n : ℝ)) * ‖⟪y, U (n : ℝ)⟫_ℂ‖ := by
        dsimp [g, f]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-(n : ℝ)) * (‖y‖ * ‖U (n : ℝ)‖) := by
        gcongr
        exact norm_inner_le_norm _ _
      _ = Real.exp (-(n : ℝ)) * (‖y‖ * ‖x‖) := by
        rw [U.norm_eq]
  have hlim : Filter.Tendsto (fun n : ℕ => g (n : ℝ)) atTop (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnorm_lim
  have hconst_zero : g 0 = 0 := by
    have hc : Tendsto (fun _ : ℕ => g 0) atTop (𝓝 0) :=
      hlim.congr' (Filter.Eventually.of_forall fun n => hconst (n : ℝ))
    exact (tendsto_nhds_unique hc tendsto_const_nhds).symm
  simpa [g, f, U.initial] using hconst_zero

end GlobalAnalyticOrbit

/-- Every entire vector supplies a `GlobalAnalyticOrbit` once the operator is known to be
symmetric on a dense domain.  This packages the global case through the same certificate used by
the finite-radius Nelson argument. -/
lemma IsEntireVector.globalAnalyticOrbit
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsEntireVector x)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    Nonempty (GlobalAnalyticOrbit T x) := by
  obtain ⟨v, hv, hall⟩ := h
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  refine ⟨
    { toFun := fun s => analyticExp T v s
      initial := analyticExp_zero hv
      mem_domain := fun s => analyticExp_mem_closure_domain_of_entire hv hall hT s
      hasDerivAt := fun s => analyticExp_hasDerivAt_of_entire hv hall hT s
      norm_eq := ?_ }⟩
  intro s
  let t : ℝ := 2 * |s| + 1
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hs : s ∈ Set.Ioo (-t / 2) (t / 2) := by
    dsimp [t]
    constructor <;> linarith [neg_le_abs s, le_abs_self s]
  exact LinearPMap.analyticExp_norm_eq_norm hsym hdense hv hs (hall t ht)

/-- The local exponential series attached to an explicit analytic witness is a local orbit
certificate.  Keeping the witness in the constructor is important for continuation: the next
state is the value of this very series, rather than an unspecified member of a `Nonempty` proof. -/
noncomputable def IsAnalyticVector.localAnalyticOrbitOfWitness
    {T : H →ₗ.[ℂ] H} {x : H} (v : ℕ → T.domain) (hv : IteratesSeq T x v)
    {t : ℝ} (ht : 0 < t)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    LocalAnalyticOrbit T x := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  refine
    { radius := t / 2
      radius_pos := by linarith
      toFun := fun s => analyticExp T v s
      initial := analyticExp_zero hv
      mem_domain := ?_
      hasDerivAt := ?_
      norm_eq := ?_ }
  · intro s hs
    have hs' : s ∈ Set.Ioo (-t / 2) (t / 2) := by
      rw [abs_lt] at hs
      exact ⟨by simpa only [neg_div] using hs.1, hs.2⟩
    exact analyticExp_mem_closure_domain hv hT hs' hsum
  · intro s hs
    have hs' : s ∈ Set.Ioo (-t / 2) (t / 2) := by
      rw [abs_lt] at hs
      exact ⟨by simpa only [neg_div] using hs.1, hs.2⟩
    exact analyticExp_hasDerivAt_eq_smul_closure hv hT hs' hsum
  · intro s hs
    have hs' : s ∈ Set.Ioo (-t / 2) (t / 2) := by
      rw [abs_lt] at hs
      exact ⟨by simpa only [neg_div] using hs.1, hs.2⟩
    exact LinearPMap.analyticExp_norm_eq_norm hsym hdense hv hs' hsum

/- The local exponential series attached to an analytic vector is a local orbit certificate.
The radius is halved to leave room for termwise differentiation and passage to the closed graph. -/
lemma IsAnalyticVector.localAnalyticOrbit
    {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsAnalyticVector x)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    Nonempty (LocalAnalyticOrbit T x) := by
  obtain ⟨v, hv, t, ht, hsum⟩ := h
  exact ⟨IsAnalyticVector.localAnalyticOrbitOfWitness v hv ht hsum hsym hdense⟩

/-- A fresh local chart at a reached state can be chosen with any radius strictly below the
original analytic radius (up to the usual local half-radius).  The sharp-radius witness is first
constructed for the closed operator, then its local certificate is transported back to `T`. -/
lemma IsAnalyticVector.localAnalyticOrbit_at_exp_of_radius
    {T : H →ₗ.[ℂ] H} {x : H} {v : ℕ → T.domain} (hv : IteratesSeq T x v)
    {t a q : ℝ} (ht : 0 < t) (ha : |a| < t / 2) (hq : 0 < q) (hqt : q < t)
    (hsum : Summable (fun n : ℕ => ‖(v n : H)‖ * t ^ n / n.factorial))
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    Nonempty (LocalAnalyticOrbit T (analyticExp T v a)) := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  have hclosedSym : T.closure.IsSymmetric := hsym.closure hdenseDomain
  have hspan_le : Submodule.span ℂ {x : H | T.IsAnalyticVector x} ≤
      Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x} := by
    apply Submodule.span_mono
    intro z hz
    exact IsAnalyticVector.for_closure hz
  have hclosedense :
      (Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x}).topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    exact hdense ▸ Submodule.topologicalClosure_mono hspan_le
  have hy : T.closure.IsAnalyticVector (analyticExp T v a) :=
    GlobalAnalyticOrbit.IsAnalyticVector.analyticExp_at_isAnalyticVector_of_radius
      hv ht ha hq hqt hsum hsym hdense
  obtain ⟨U⟩ := IsAnalyticVector.localAnalyticOrbit hy hclosedSym hclosedense
  exact LocalAnalyticOrbit.of_closure hT U

/-! Advance a proof-relevant analytic witness by a prescribed real step.  The new radius is chosen
as the midpoint of a fixed lower bound and the old radius; consequently repeated advancement
preserves a uniform positive lower bound instead of consuming the radius geometrically. -/
noncomputable def AnalyticVectorWitness.advance
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W : AnalyticVectorWitness T) {r a : ℝ}
    (hr : 0 < r) (hrW : r < W.radius) (ha : |a| < W.radius / 2) :
    AnalyticVectorWitness T := by
  let q : ℝ := (r + W.radius) / 2
  have hq : 0 < q := by
    dsimp [q]
    linarith [hr, W.radius_pos]
  have hqr : r < q := by
    dsimp [q]
    linarith
  have hqW : q < W.radius := by
    dsimp [q]
    linarith
  have hex : ∃ w : ℕ → T.domain,
      IteratesSeq T (analyticExp T W.iterates a) w ∧
        Summable (fun n : ℕ => ‖(w n : H)‖ * q ^ n / n.factorial) := by
    obtain ⟨w, hw, hq', hsum_w⟩ :=
      GlobalAnalyticOrbit.IsAnalyticVector.analyticExp_at_isAnalyticVector_witness_of_radius
        W.iterates_spec W.radius_pos ha hq hqW W.summable hsym hdense
    have hdom : T.closure.domain = T.domain := congrArg LinearPMap.domain hclosed
    let wT : ℕ → T.domain := fun n =>
      ⟨(w n : H), hdom ▸ (w n).property⟩
    have happly : ∀ (z : H) (hz : z ∈ T.domain) (hz' : z ∈ T.closure.domain),
        T.closure ⟨z, hz'⟩ = T ⟨z, hz⟩ := by
      intro z hz hz'
      have hgraph : (z, T.closure ⟨z, hz'⟩) ∈ T.graph := by
        have hgraph_eq : T.closure.graph = T.graph :=
          congrArg (fun R : H →ₗ.[ℂ] H => R.graph) hclosed
        exact hgraph_eq ▸ T.closure.mem_graph ⟨z, hz'⟩
      exact T.mem_graph_snd_inj' hgraph (T.mem_graph ⟨z, hz⟩) rfl
    have hwT : IteratesSeq T (analyticExp T W.iterates a) wT := by
      refine ⟨?_, fun n => ?_⟩
      · change (w 0 : H) = analyticExp T W.iterates a
        exact hw.1
      · change (w (n + 1) : H) = T (wT n)
        calc
          (w (n + 1) : H) = T.closure (w n) := hw.2 n
          _ = T (wT n) := happly (w n : H) (wT n).property (w n).property
    have hsum_wT : Summable
        (fun n : ℕ => ‖(wT n : H)‖ * q ^ n / n.factorial) := by
      change Summable (fun n : ℕ => ‖(w n : H)‖ * q ^ n / n.factorial)
      exact hsum_w
    exact ⟨wT, hwT, hsum_wT⟩
  let wT : ℕ → T.domain := Classical.choose hex
  have hwT : IteratesSeq T (analyticExp T W.iterates a) wT :=
    (Classical.choose_spec hex).1
  have hsum_wT : Summable (fun n : ℕ => ‖(wT n : H)‖ * q ^ n / n.factorial) :=
    (Classical.choose_spec hex).2
  exact ⟨analyticExp T W.iterates a, wT, hwT, q, hq, hsum_wT⟩

lemma AnalyticVectorWitness.advance_radius
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W : AnalyticVectorWitness T) {r a : ℝ}
    (hr : 0 < r) (hrW : r < W.radius) (ha : |a| < W.radius / 2) :
    (W.advance hclosed hsym hdense hr hrW ha).radius = (r + W.radius) / 2 := by
  rfl

lemma AnalyticVectorWitness.advance_norm
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W : AnalyticVectorWitness T) {r a : ℝ}
    (hr : 0 < r) (hrW : r < W.radius) (ha : |a| < W.radius / 2) :
    ‖(W.advance hclosed hsym hdense hr hrW ha).state‖ = ‖W.state‖ := by
  have ha' : a ∈ Set.Ioo (-W.radius / 2) (W.radius / 2) := by
    change -W.radius / 2 < a ∧ a < W.radius / 2
    rcases (abs_lt.mp ha) with ⟨ha₁, ha₂⟩
    exact ⟨by linarith [ha₁], by linarith [ha₂]⟩
  have hnorm := analyticExp_norm_eq_norm hsym hdense W.iterates_spec ha' W.summable
  simpa [AnalyticVectorWitness.advance] using hnorm

/-! A two-sided line of witnesses with a fixed lower-radius invariant.  Positive indices advance
by `δ`, negative indices by `-δ`; the midpoint choice in `advance` makes the invariant stable in
both directions. -/
noncomputable def AnalyticVectorWitness.uniformIntegerLineData
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W0 : AnalyticVectorWitness T) {r δ : ℝ}
    (hr : 0 < r) (hrW0 : r < W0.radius)
    (hδ : 0 < δ) (h2δ : 2 * δ < r) :
    ℤ → {W : AnalyticVectorWitness T // r < W.radius ∧ ‖W.state‖ = ‖W0.state‖} := by
  let motive : ℤ → Type _ := fun _ =>
    {W : AnalyticVectorWitness T // r < W.radius ∧ ‖W.state‖ = ‖W0.state‖}
  let base : motive 0 := ⟨W0, hrW0, rfl⟩
  let succ : ∀ k : ℤ, 0 ≤ k → motive k → motive (k + 1) := fun _ _ ih => by
    have ha : |δ| < ih.1.radius / 2 := by
      rw [abs_of_pos hδ]
      linarith [ih.2.1]
    let W := AnalyticVectorWitness.advance hclosed hsym hdense ih.1 hr ih.2.1 ha
    refine ⟨W, ?_, ?_⟩
    rw [AnalyticVectorWitness.advance_radius hclosed hsym hdense ih.1 hr ih.2.1 ha]
    · linarith [ih.2.1]
    · exact (AnalyticVectorWitness.advance_norm hclosed hsym hdense ih.1 hr ih.2.1 ha).trans ih.2.2
  let pred : ∀ k : ℤ, k ≤ 0 → motive k → motive (k - 1) := fun _ _ ih => by
    have ha : |-δ| < ih.1.radius / 2 := by
      rw [abs_neg, abs_of_pos hδ]
      linarith [ih.2.1]
    let W := AnalyticVectorWitness.advance hclosed hsym hdense ih.1 hr ih.2.1 ha
    refine ⟨W, ?_, ?_⟩
    rw [AnalyticVectorWitness.advance_radius hclosed hsym hdense ih.1 hr ih.2.1 ha]
    · linarith [ih.2.1]
    · exact (AnalyticVectorWitness.advance_norm hclosed hsym hdense ih.1 hr ih.2.1 ha).trans ih.2.2
  exact fun n => Int.inductionOn' (motive := motive) n 0 base succ pred

noncomputable def AnalyticVectorWitness.uniformIntegerLine
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W0 : AnalyticVectorWitness T) {r δ : ℝ}
    (hr : 0 < r) (hrW0 : r < W0.radius)
    (hδ : 0 < δ) (h2δ : 2 * δ < r) :
    ℤ → AnalyticVectorWitness T :=
  fun n => (AnalyticVectorWitness.uniformIntegerLineData hclosed hsym hdense W0
    hr hrW0 hδ h2δ n).1

lemma AnalyticVectorWitness.uniformIntegerLine_succ_of_nonneg
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W0 : AnalyticVectorWitness T) {r δ : ℝ}
    (hr : 0 < r) (hrW0 : r < W0.radius)
    (hδ : 0 < δ) (h2δ : 2 * δ < r) {n : ℤ} (hn : 0 ≤ n) :
    (AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
      hr hrW0 hδ h2δ (n + 1)).state =
      analyticExp T (AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
      hr hrW0 hδ h2δ n).iterates δ := by
  simp [AnalyticVectorWitness.uniformIntegerLine,
    AnalyticVectorWitness.uniformIntegerLineData,
    Int.inductionOn'_add_one, hn]
  rfl

lemma AnalyticVectorWitness.uniformIntegerLine_pred_of_nonpos
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W0 : AnalyticVectorWitness T) {r δ : ℝ}
    (hr : 0 < r) (hrW0 : r < W0.radius)
    (hδ : 0 < δ) (h2δ : 2 * δ < r) {n : ℤ} (hn : n ≤ 0) :
    (AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
      hr hrW0 hδ h2δ (n - 1)).state =
      analyticExp T (AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
        hr hrW0 hδ h2δ n).iterates (-δ) := by
  simp [AnalyticVectorWitness.uniformIntegerLine,
    AnalyticVectorWitness.uniformIntegerLineData,
    Int.inductionOn'_sub_one, hn]
  rfl

lemma AnalyticVectorWitness.uniformIntegerLine_step
    {T : H →ₗ.[ℂ] H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W0 : AnalyticVectorWitness T) {r δ : ℝ}
    (hr : 0 < r) (hrW0 : r < W0.radius)
    (hδ : 0 < δ) (h4δ : 4 * δ < r) {n : ℤ} :
    (AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
      hr hrW0 hδ (by linarith) (n + 1)).state =
      analyticExp T (AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
        hr hrW0 hδ (by linarith) n).iterates δ := by
  let W : ℤ → AnalyticVectorWitness T :=
    AnalyticVectorWitness.uniformIntegerLine hclosed hsym hdense W0
      hr hrW0 hδ (by linarith)
  have hbelow : ∀ k : ℤ, r < (W k).radius := by
    intro k
    exact (AnalyticVectorWitness.uniformIntegerLineData hclosed hsym hdense W0
      hr hrW0 hδ (by linarith) k).2.1
  have hδR : δ < r / 4 := by linarith
  have hclosedSym : T.closure.IsSymmetric := by simpa only [hclosed] using hsym
  rcases le_total 0 n with hn | hn
  · exact AnalyticVectorWitness.uniformIntegerLine_succ_of_nonneg
      hclosed hsym hdense W0 hr hrW0 hδ (by linarith) hn
  · by_cases hn0 : 0 ≤ n
    · exact AnalyticVectorWitness.uniformIntegerLine_succ_of_nonneg
        hclosed hsym hdense W0 hr hrW0 hδ (by linarith) hn0
    have hnneg : n + 1 ≤ 0 := by omega
    have hpred := AnalyticVectorWitness.uniformIntegerLine_pred_of_nonpos
      hclosed hsym hdense W0 hr hrW0 hδ (by linarith) hnneg
    let U : LocalAnalyticOrbit T ((W (n + 1)).state) :=
      IsAnalyticVector.localAnalyticOrbitOfWitness (W (n + 1)).iterates
        (W (n + 1)).iterates_spec (W (n + 1)).radius_pos (W (n + 1)).summable
        hsym hdense
    let V : LocalAnalyticOrbit T (W n).state :=
      IsAnalyticVector.localAnalyticOrbitOfWitness (W n).iterates
        (W n).iterates_spec (W n).radius_pos (W n).summable hsym hdense
    have hpred' : (W n).state = analyticExp T (W (n + 1)).iterates (-δ) := by
      simpa [W, show n + 1 - 1 = n by omega] using hpred
    have hbase : (W n).state = U (-δ) := by
      simpa [U, IsAnalyticVector.localAnalyticOrbitOfWitness] using hpred'
    let V' : LocalAnalyticOrbit T (U (-δ)) :=
      { radius := V.radius
        radius_pos := V.radius_pos
        toFun := V
        initial := by
          calc
            V 0 = (W n).state := V.initial
            _ = U (-δ) := hbase
        mem_domain := V.mem_domain
        hasDerivAt := V.hasDerivAt
        norm_eq := by
          intro s hs
          calc
            ‖V s‖ = ‖(W n).state‖ := V.norm_eq s hs
            _ = ‖U (-δ)‖ := by rw [hbase] }
    have hmarginU : |(-δ)| + r / 4 ≤ U.radius := by
      dsimp [U, IsAnalyticVector.localAnalyticOrbitOfWitness]
      rw [abs_neg, abs_of_pos hδ]
      linarith [hbelow (n + 1)]
    have hVcore : r / 4 ≤ V'.radius := by
      dsimp [V, V', IsAnalyticVector.localAnalyticOrbitOfWitness]
      linarith [hbelow n]
    have heq := LocalAnalyticOrbit.translate_eq_of_same_initial_on_core'
      U hclosedSym (a := -δ) (R := r / 4) (by positivity) hmarginU V'
      hVcore (by rw [abs_of_pos hδ]; exact hδR)
    have hzero : analyticExp T (W (n + 1)).iterates 0 = (W (n + 1)).state :=
      analyticExp_zero (W (n + 1)).iterates_spec
    have heq' : analyticExp T (W (n + 1)).iterates 0 =
        analyticExp T (W n).iterates δ := by
      simpa [U, V', V, IsAnalyticVector.localAnalyticOrbitOfWitness] using heq
    rw [hzero] at heq'
    simpa [W] using heq'

/-! Once the analytic continuation has supplied a uniformly thick integer line of witnesses, this
lemma performs the genuinely topological part of Nelson's construction.  It is kept separate from
the choice of the line so that the same gluing theorem can be reused by other continuation
arguments. -/
lemma GlobalAnalyticOrbit.of_uniform_witness_line
    {T : H →ₗ.[ℂ] H} {x : H} (hclosed : T.closure = T)
    (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (W : ℤ → AnalyticVectorWitness T) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (h4δ : 4 * δ < r)
    (hbelow : ∀ n : ℤ, r < (W n).radius)
    (hstate_zero : (W 0).state = x)
    (hstate_norm : ∀ n : ℤ, ‖(W n).state‖ = ‖x‖)
    (hstep : ∀ n : ℤ,
      (W (n + 1)).state = analyticExp T (W n).iterates δ) :
    Nonempty (GlobalAnalyticOrbit T x) := by
  have hδR : δ < r / 4 := by linarith
  have hclosedSym : T.closure.IsSymmetric := by
    simpa only [hclosed] using hsym
  let chart : ∀ n : ℤ, LocalAnalyticOrbit T ((W n).state) := fun n =>
    IsAnalyticVector.localAnalyticOrbitOfWitness (W n).iterates
      (W n).iterates_spec (W n).radius_pos (W n).summable hsym hdense
  have hcore : ∀ n : ℤ, r / 4 ≤ (chart n).radius := by
    intro n
    dsimp [chart, IsAnalyticVector.localAnalyticOrbitOfWitness]
    linarith [hbelow n]
  have hmargin : ∀ n : ℤ, r / 4 + δ ≤ (chart n).radius := by
    intro n
    dsimp [chart, IsAnalyticVector.localAnalyticOrbitOfWitness]
    linarith [hbelow n]
  have hadj : ∀ n : ℤ, ∀ z : ℝ, |z| < r / 4 →
      chart n (δ + z) = chart (n + 1) z := by
    intro n z hz
    let U := chart n
    have hbase : (W (n + 1)).state = U δ := by
      dsimp [U, chart, IsAnalyticVector.localAnalyticOrbitOfWitness]
      simpa only [hstep n]
    let V : LocalAnalyticOrbit T (U δ) :=
      { radius := (chart (n + 1)).radius
        radius_pos := (chart (n + 1)).radius_pos
        toFun := chart (n + 1)
        initial := by
          calc
            chart (n + 1) 0 = (W (n + 1)).state := (chart (n + 1)).initial
            _ = U δ := hbase
        mem_domain := (chart (n + 1)).mem_domain
        hasDerivAt := (chart (n + 1)).hasDerivAt
        norm_eq := by
          intro s hs
          calc
            ‖chart (n + 1) s‖ = ‖(W (n + 1)).state‖ :=
              (chart (n + 1)).norm_eq s hs
            _ = ‖U δ‖ := by rw [hbase] }
    have hmarginU : |δ| + r / 4 ≤ U.radius := by
      rw [abs_of_pos hδ]
      dsimp [U]
      linarith [hmargin n]
    have heq := LocalAnalyticOrbit.translate_eq_of_same_initial_on_core'
      U hclosedSym (a := δ) (R := r / 4) (by positivity)
      hmarginU V
      (by dsimp [V]; exact hcore (n + 1)) hz
    exact heq
  let C := LocalOrbitCoreCover.of_adjacent_int_index hδ hδR
    (fun n => (W n).state) chart (by positivity)
    (fun n => hcore n) hstate_zero hstate_norm hadj
  exact ⟨C.toGlobal⟩

/-- A dense family of analytic vectors proves essential self-adjointness once its local exponential
orbits have been patched to global norm-preserving orbits.  The theorem is deliberately separated
from the construction of those orbits: it is the reusable deficiency-space end of Nelson's proof. -/
theorem IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors_of_globalOrbit
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤)
    (hOrbit : ∀ x : H, T.IsAnalyticVector x → Nonempty (GlobalAnalyticOrbit T x)) :
    T.IsEssentiallySelfAdjoint := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hdefect_plus : T.defectNumber Complex.I = 0 := by
    rw [← defectNumber_closure (T := T) (z := Complex.I)
      (hsym.mem_regularityDomain_of_im_ne_zero (by simp))]
    show Module.rank ℂ ↥((T.closure - Complex.I • 1).toFun.rangeᗮ) = 0
    apply Submodule.rank_eq_zero.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hyspan : y ∈ (Submodule.span ℂ {x : H | T.IsAnalyticVector x})ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction (p := fun z _ ↦ ⟪y, z⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
      · intro z hz
        obtain ⟨U⟩ := hOrbit z hz
        exact U.inner_deficiency_eq_zero hy
      · simp
      · intro z₁ z₂ _ _ hz₁ hz₂
        simp [inner_add_right, hz₁, hz₂]
      · intro c z _ hz
        simp [inner_smul_right, hz]
    have hspanBot :
        (Submodule.span ℂ {x : H | T.IsAnalyticVector x})ᗮ = (⊥ : Submodule ℂ H) :=
      Submodule.topologicalClosure_eq_top_iff.mp hdense
    exact (Submodule.mem_bot ℂ).mp (hspanBot ▸ hyspan)
  have hdefect_minus : T.defectNumber (-Complex.I) = 0 := by
    rw [← defectNumber_closure (T := T) (z := -Complex.I)
      (hsym.mem_regularityDomain_of_im_ne_zero (by simp))]
    show Module.rank ℂ ↥((T.closure - (-Complex.I) • 1).toFun.rangeᗮ) = 0
    apply Submodule.rank_eq_zero.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hyspan : y ∈ (Submodule.span ℂ {x : H | T.IsAnalyticVector x})ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction (p := fun z _ ↦ ⟪y, z⟫_ℂ = 0) ?_ ?_ ?_ ?_ hu
      · intro z hz
        obtain ⟨U⟩ := hOrbit z hz
        exact U.inner_deficiency_eq_zero_neg hy
      · simp
      · intro z₁ z₂ _ _ hz₁ hz₂
        simp [inner_add_right, hz₁, hz₂]
      · intro c z _ hz
        simp [inner_smul_right, hz]
    have hspanBot :
        (Submodule.span ℂ {x : H | T.IsAnalyticVector x})ᗮ = (⊥ : Submodule ℂ H) :=
      Submodule.topologicalClosure_eq_top_iff.mp hdense
    exact (Submodule.mem_bot ℂ).mp (hspanBot ▸ hyspan)
  exact hsym.isEssentiallySelfAdjoint_of_defectNumber_eq_zero
    hdenseDomain hdefect_plus hdefect_minus

/-! ## Nelson's single-operator criterion -/

/-- **Nelson's analytic-vector theorem, single-operator case** (Reed–Simon Vol. II, Theorem
X.39, first half). A symmetric operator with a dense set of analytic vectors is essentially
self-adjoint.  The proof constructs a uniform-radius two-sided integer line of local exponential
charts, proves adjacent-chart agreement by the symmetric-ODE uniqueness lemma, glues the line into
a global norm-preserving orbit, and applies the deficiency-index criterion. -/
theorem IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    T.IsEssentiallySelfAdjoint := by
  have hdenseDomain : T.HasDenseDomain := hasDenseDomain_of_denseAnalyticVectors hdense
  have hT : T.IsClosable := hsym.isClosable hdenseDomain
  have hclosed : T.closure.closure = T.closure := hT.closure_isClosed.closure_eq
  have hclosedSym : T.closure.IsSymmetric := hsym.closure hdenseDomain
  have hspan_le : Submodule.span ℂ {x : H | T.IsAnalyticVector x} ≤
      Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x} := by
    apply Submodule.span_mono
    intro z hz
    exact IsAnalyticVector.for_closure hz
  have hclosedense :
      (Submodule.span ℂ {x : H | T.closure.IsAnalyticVector x}).topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    exact hdense ▸ Submodule.topologicalClosure_mono hspan_le
  have hOrbit : ∀ z : H, T.IsAnalyticVector z →
      Nonempty (GlobalAnalyticOrbit T z) := by
    intro z hz
    let W0 : AnalyticVectorWitness T.closure :=
      AnalyticVectorWitness.of_isAnalytic (IsAnalyticVector.for_closure hz)
    let r : ℝ := W0.radius / 2
    let δ : ℝ := r / 8
    have hr : 0 < r := by
      dsimp [r]
      linarith [W0.radius_pos]
    have hrW0 : r < W0.radius := by
      dsimp [r]
      linarith [W0.radius_pos]
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    have h4δ : 4 * δ < r := by
      dsimp [δ]
      linarith
    let W : ℤ → AnalyticVectorWitness T.closure :=
      AnalyticVectorWitness.uniformIntegerLine hclosed hclosedSym hclosedense W0
        hr hrW0 hδ (by linarith)
    have hbelow : ∀ n : ℤ, r < (W n).radius := by
      intro n
      exact (AnalyticVectorWitness.uniformIntegerLineData hclosed hclosedSym hclosedense W0
        hr hrW0 hδ (by linarith) n).2.1
    have hstate_zero : (W 0).state = z := by
      have hdata0 :
          AnalyticVectorWitness.uniformIntegerLineData hclosed hclosedSym hclosedense W0
              hr hrW0 hδ (by linarith) 0 =
            (⟨W0, hrW0, rfl⟩ :
              {W : AnalyticVectorWitness T.closure //
                r < W.radius ∧ ‖W.state‖ = ‖W0.state‖}) := by
        simp [AnalyticVectorWitness.uniformIntegerLineData, Int.inductionOn'_self]
      change (AnalyticVectorWitness.uniformIntegerLineData hclosed hclosedSym hclosedense W0
        hr hrW0 hδ (by linarith) 0).1.state = z
      rw [hdata0]
      rfl
    have hstate_norm : ∀ n : ℤ, ‖(W n).state‖ = ‖z‖ := by
      intro n
      have hn := (AnalyticVectorWitness.uniformIntegerLineData hclosed hclosedSym
        hclosedense W0 hr hrW0 hδ (by linarith) n).2.2
      change ‖(AnalyticVectorWitness.uniformIntegerLineData hclosed hclosedSym hclosedense W0
        hr hrW0 hδ (by linarith) n).1.state‖ = ‖z‖
      rw [hn]
      rfl
    have hstep : ∀ n : ℤ, (W (n + 1)).state =
        analyticExp T.closure (W n).iterates δ := by
      intro n
      exact AnalyticVectorWitness.uniformIntegerLine_step
        hclosed hclosedSym hclosedense W0 hr hrW0 hδ h4δ (n := n)
    obtain ⟨U⟩ := GlobalAnalyticOrbit.of_uniform_witness_line
      (T := T.closure) (x := z) hclosed hclosedSym hclosedense W
      hr hδ h4δ hbelow hstate_zero hstate_norm (by simpa [W] using hstep)
    exact GlobalAnalyticOrbit.of_closure hT U
  exact hsym.isEssentiallySelfAdjoint_of_denseAnalyticVectors_of_globalOrbit
    hdense hOrbit

end LinearPMap
