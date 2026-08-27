/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded
public import Physlib.Meta.Sorry
public import Physlib.Meta.TODO.Basic
public import Mathlib.Analysis.SpecificLimits.Normed

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
§X.6, or Nelson's original 1959 Annals paper); it is recorded honestly below as `@[sorryful]`
rather than faked.

What *is* proved here is the tractable structural content around that hard core:

## Key results

- `LinearPMap.IsAnalyticVector` : the precise Reed–Simon definition, specialized to `LinearPMap`.
- `LinearPMap.IsAnalyticVector.smul`, `.add` : analytic vectors form a submodule of `T.domain`
  (the standard "min of the two radii" argument).
- `LinearPMap.isAnalyticVector_of_eigenvector` : every eigenvector of `T` is analytic for *every*
  radius `t`, since its iterate sequence has an exactly geometric norm. In particular every vector
  in `EssentialSelfAdjointCriteria.lean`'s dense eigenbasis-span criterion is automatically an
  analytic vector, so that already-proved theorem is the "totally elementary" special case of
  Nelson's theorem in which the analytic vectors are exhibited as an explicit eigenbasis rather
  than only assumed to exist.
- `LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors` : Nelson's
  single-operator analytic-vector criterion, stated precisely. `@[sorryful]`; see its docstring
  and the module docstring above for exactly what is missing and why.
-/

@[expose] public section

noncomputable section

namespace LinearPMap

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## The definition -/

/-- `v` is the iterate sequence of `x` under `T`: `v 0 = x` and `v (n+1) = T (v n)`, as elements
of `T.domain` (so this packages, in particular, the assertion that `x` lies in the domain of every
power `Tⁿ`). Since `T` is single-valued, `v` is uniquely determined by `x` whenever it exists at
all. -/
def IteratesSeq (T : H →ₗ.[ℂ] H) (x : H) (v : ℕ → T.domain) : Prop :=
  (v 0 : H) = x ∧ ∀ n, (v (n + 1) : H) = T (v n)

/-- **Analytic vector** (Reed–Simon Vol. II, §X.6). `x` is an analytic vector for `T` if it lies
in the domain of every iterated power `Tⁿ` (witnessed by an iterate sequence `v`, so `v n`
represents `Tⁿ x`) and the exponential-type series `∑ ‖Tⁿx‖ tⁿ / n!` converges for some `t > 0`. -/
def IsAnalyticVector (T : H →ₗ.[ℂ] H) (x : H) : Prop :=
  ∃ v : ℕ → T.domain, IteratesSeq T x v ∧
    ∃ t : ℝ, 0 < t ∧ Summable (fun n => ‖(v n : H)‖ * t ^ n / n.factorial)

omit [CompleteSpace H] in
lemma IsAnalyticVector.mem_domain {T : H →ₗ.[ℂ] H} {x : H} (h : T.IsAnalyticVector x) :
    x ∈ T.domain := by
  obtain ⟨v, ⟨hv0, -⟩, -⟩ := h
  exact hv0 ▸ (v 0).2

/-! ## Structural closure properties -/

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

/-! ## Nelson's single-operator criterion -/

/-- **Nelson's analytic-vector theorem, single-operator case** (Reed–Simon Vol. II, Theorem
X.39, first half). A symmetric operator with a *dense* set of analytic vectors is essentially
self-adjoint.

**Honesty note.** This is recorded `@[sorryful]`, not proved. The standard proof (Reed–Simon
§X.6, or Nelson's original 1959 paper "Analytic vectors", *Annals of Mathematics* 70) builds, for
each analytic vector `x` with radius `t`, the locally-convergent power series
`Uₓ(s) := ∑ₙ (is)ⁿ/n! Tⁿx` for `|s| < t`, shows `Uₓ` is a local isometric semigroup using
`T`'s symmetry (`⟪Tx,x⟫` real), extends it past the local radius using a further analytic-vector
argument on `Uₓ(s₀)` itself (the delicate "patch countably many local pieces" step, which needs
the density hypothesis to know the patched target vectors are themselves analytic), and finally
identifies the resulting global strongly continuous one-parameter unitary group's Stone generator
with `T.closure`, feeding the resulting surjectivity of `T.closure ∓ i` into the deficiency-index
criterion already proved as `LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_defectNumber_eq_zero`
(`EssentialSelfAdjointCriteria.lean`'s ambient theorem). None of this construction — the local
power series as an actual `HasSum`, its semigroup/isometry law, or the patching argument — is
attempted here; each step is itself several pages of analysis. This is genuinely open, not a
placeholder for routine `simp`/`gcongr` work. -/
@[sorryful]
theorem IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors
    {T : H →ₗ.[ℂ] H} (hsym : T.IsSymmetric)
    (hdense : (Submodule.span ℂ {x : H | T.IsAnalyticVector x}).topologicalClosure = ⊤) :
    T.IsEssentiallySelfAdjoint := by
  sorry

TODO "Prove `LinearPMap.IsSymmetric.isEssentiallySelfAdjoint_of_denseAnalyticVectors` (Nelson's \
  single-operator analytic-vector criterion). This needs: (1) a `HasSum` construction of the local \
  power series `∑ (is)ⁿ/n! Tⁿx` for `|s|` inside the analytic-vector radius; (2) its local semigroup \
  and isometry laws, from `T.IsSymmetric`; (3) the patching argument extending the local semigroup \
  globally, using density of analytic vectors to keep re-patching; (4) identifying the resulting \
  Stone generator with `T.closure` and feeding surjectivity of `T.closure ∓ i` into \
  `IsSymmetric.isEssentiallySelfAdjoint_of_defectNumber_eq_zero`. Each step is independently \
  substantial (Reed-Simon Vol. II Theorem X.39 / Nelson 1959); see the theorem's docstring."

end LinearPMap
