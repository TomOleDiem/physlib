# Session notes: C⋆-algebras, Lie/Jordan structure, CCR and dynamics

Research notes for future development. Not roadmap items yet — see `todo.md` for what's
actually queued. Overarching viewpoint: a unital C⋆-algebra `A` as the fundamental quantum
system, states as positive unital functionals, dynamics as maps of the algebra.

## 1. Observables automatically have Jordan + Lie structure

`A_sa = {a ∈ A : a* = a}` is a real vector space with two canonical operations:

- **Jordan product** `a ∘ b = ½(ab + ba)` — commutative, generally non-associative. The symmetric
  part of operator multiplication. **Implemented**: `OperatorAlgebra.Observable.jordan`.
- **Observable Lie bracket** `[a,b]_obs = -i(ab - ba)` — antisymmetric. **Implemented**:
  `OperatorAlgebra.Observable.obsBracket`.

Together they recover the original product: `ab = a∘b + (i/2)[a,b]_obs`. **Implemented**:
`OperatorAlgebra.Observable.mul_eq_jordan_add_obsBracket`. All three are fully proved, no
`sorry`s — see `Physlib/Mathematics/OperatorAlgebra/JordanLie.lean`. `obsBracket` is a genuine
`LieRing`/`LieAlgebra ℝ` instance on `Observable A` (Mathlib's real notion,
`Mathlib.Algebra.Lie.OfAssociative`); the Jordan identity for `jordan` is proved concretely rather
than via a registered instance (Mathlib does have `IsJordan`/`IsCommJordan`/`SymAlg`,
`Mathlib.Algebra.Jordan.Basic`/`Mathlib.Algebra.Symmetrized` — connecting `Observable A` to that
abstractly is a logged `TODO`, needing `Invertible (2 : A)` and care around a `Mul` diamond with
`selfAdjoint`'s own instance when `A` is commutative).

Schematically: `C⋆-algebra ⤳ Jordan geometry + Lie dynamics`.

For selected observables `Xᵢ`, if `[Xᵢ,Xⱼ]_obs = Σₖ cᵢⱼᵏ Xₖ`, their real span is a Lie subalgebra
— this is how familiar physical Lie algebras arise inside the observable algebra. (Not yet
formalized: a general "structure constants ⟹ Lie subalgebra" statement.)

## 2. Qubit: Jordan = dot product, Lie = cross product

For `A = M₂(ℂ)`, every observable is `a = a₀ I + a⃗·σ`. For traceless observables,

`(a⃗·σ)(b⃗·σ) = (a⃗·b⃗) I + i(a⃗×b⃗)·σ`

so `(a⃗·σ) ∘ (b⃗·σ) = (a⃗·b⃗) I` and `(1/2i)[a⃗·σ, b⃗·σ] = (a⃗×b⃗)·σ`. This is already what
`Qubit.σ_mul_σ`/`Qubit.σ_commutator` say, specialized to the traceless case — the general
`Observable.jordan`/`obsBracket` above should recover them as a corollary once proved (not yet
checked/connected explicitly).

Hence: Jordan ↔ Euclidean/Bloch geometry, Lie ↔ rotations/dynamics. The self-adjoint qubit
algebra is the **Jordan spin factor** `ℝ ⊕ ℝ³`; its positive cone `a₀ ≥ ‖a⃗‖` is exactly
`Qubit.nonneg_scalar_add_σ_iff`, leading directly to the Bloch ball. The traceless part under the
Lie bracket is `su(2) ≅ so(3)` — `Qubit/Lie.lean`'s `τ`/`τ_mul_sub_mul` — explaining Hamiltonian
Bloch rotations.

Jordan theory is useful conceptually but should stay a *derived* structure, not replace the
C⋆-algebra as the foundation.

## 3. Oscillator: CCR and the Heisenberg Lie algebra

`Qᵢ, Pᵢ, aᵢ, aᵢ†` are unbounded, so they cannot themselves live inside a C⋆-algebra.
Algebraically `[aᵢ,aⱼ†] = δᵢⱼ I`, `[aᵢ,aⱼ] = [aᵢ†,aⱼ†] = 0`. `span{I, aᵢ, aᵢ†}` is the Heisenberg
Lie algebra `𝔥_{2d+1}`. Its enveloping algebra modulo `Z = 1` gives the polynomial CCR algebra
`U(𝔥)/(Z-1)` — a `*`-algebra but not a C⋆-algebra (unbounded generators). Exponentiating instead
gives bounded Weyl operators `W(ξ)` with `W(ξ)W(η) = exp(-iσ(ξ,η)/2) W(ξ+η)`; their
C⋆-completion is the Weyl/CCR C⋆-algebra.

So: `Heisenberg Lie algebra → polynomial CCR → Weyl CCR C⋆-algebra`.

A compatible complex structure gives the one-particle space `𝔥`; the vacuum quasifree state
followed by GNS produces the bosonic Fock space `F_s(𝔥) = ⊕ₙ Symⁿ 𝔥`. For `d` modes,
`H = dΓ(h) + E₀ I`; if `h eⱼ = ωⱼ eⱼ` then `E_n = Σⱼ ωⱼ(nⱼ + ½)`. Isotropic case:
`E_N = ω(N + d/2)`, `dim E_N = C(N+d-1, N)`. Quadratic combinations of the CCR generators lead
to `sp(2d, ℝ)`, explaining why quadratic Hamiltonians act symplectically.

Not started in Lean at all — a substantially different, unbounded-operator development from the
qubit's bounded/finite-dimensional one.

## 4. Channels: UCP maps are the general transformations

Heisenberg picture: a channel `Φ : A → A` is unital and completely positive; states evolve by
pullback `ω ↦ ω∘Φ`. UCP maps form a monoid `UCP(A)` under composition, reversible elements the
`*`-automorphisms — this is `Physlib.Mathematics.OperatorAlgebra.Dynamics`'s
`Channel A A ⊃ ... ⊃ AutomorphismGroup A` picture, already in the repo.

For a qubit, `Φ(σⱼ) = tⱼ I + Σᵢ Tᵢⱼ σᵢ`, so on states the Bloch vector undergoes an affine map
`r ↦ Tr + t` (up to transpose convention). Complete positivity constrains `T, t` nontrivially —
Choi gives the straightforward test, generalized Fujiwara–Algoet a more geometric one. Not
formalized.

## 5. Continuous dynamics: Hamiltonian ⊂ Lindblad

Hamiltonian dynamics is a one-parameter automorphism group `αₜ(a) = e^{itH} a e^{-itH}`,
`α_{t+s} = αₜαₛ`, generator (derivation) `L_H(a) = i[H,a]` — this is `Qubit/Dynamics.lean`,
already in the repo. Open Markovian dynamics replaces the group with a UCP semigroup
`Φₜ = e^{tL}`, `t ≥ 0`. The theorem hierarchy: **Evans–Lewis → Christensen–Evans → GKSL**.

- **General C⋆-algebra (Evans–Lewis)**: for bounded `L : A → A`, `eᵗᴸ` is UCP for all `t ≥ 0` iff
  `L(1) = 0` and `L` is conditionally completely positive. The abstract characterization.
- **`B(H)` (Christensen–Evans / GKSL)**: `L(a) = i[H,a] + Ψ(a) - ½{Ψ(1),a}` with `H = H*`, `Ψ`
  CP. Stinespring/Kraus gives the familiar GKSL form `L(a) = i[H,a] + Σₖ(Vₖ*aVₖ - ½{Vₖ*Vₖ,a})`.
  Finite dimensions turns this largely into linear algebra (Choi, Kraus).

This is the "Stone's theorem for semigroups" analogue — real, well-known, not yet in Mathlib
(nothing semigroup-related is) or formalized here. A natural next target, given
`DynamicalSemigroup A` already exists.

## 6. Qubit Lindblad dynamics = generalized Bloch equation

Most general time-independent qubit Lindblad dynamics: `ṙ = Ar + b`. Hamiltonian dynamics is the
antisymmetric part `ṙ = h×r` (`Qubit.hasDerivAt_blochTrajectory`, already in the repo); the rest
gives contraction/dephasing/relaxation. Optical Bloch equations are a particular example:
`ẋ = -x/T₂ - Δy`, `ẏ = Δx - y/T₂ - Ωz`, `ż = Ωy - (z - z_eq)/T₁`. Constant `A, b`: exactly
solvable, `r(t) = r_∞ + e^{tA}(r(0) - r_∞)`. Dissipative info can be encoded by a positive
`3×3` Kossakowski matrix `C ≥ 0`.

## 7. Time-dependent Lindblad dynamics

If `L = Lₜ`, get an evolution family `Φ_{t,s}` (a **propagator**, the rung between semigroup and
channel that was deliberately left out of the current 3-level hierarchy — see
`Dynamics.lean`'s docstring) rather than a semigroup: `Φ_{t,s}Φ_{s,r} = Φ_{t,r}`. Formally
`Φ_{t,s} = 𝒯 exp(∫ₛᵗ Lτ dτ)`. For a qubit, `ṙ = A(t)r + b(t)`; the homogeneous propagator via
time ordering or the Magnus expansion. Instantaneous GKSL generators correspond to CP-divisible
Markovian evolution, subject to regularity qualifications.

## Overall architecture

```
unital C⋆-algebra A
  ↓
A_sa: Jordan + Lie structure                    [Jordan.lean — done]
  ↓
states, effects, UCP maps                       [Basic/Effect/State.lean — done]
  ↓
Aut(A) ⊂ UCP(A)                                 [Dynamics.lean — done, structures only]
  ↓
1-parameter automorphism groups → Hamiltonian   [Qubit/Dynamics.lean — done, stubbed]
UCP semigroups → Evans–Lewis/GKSL               [not started]
```

For bounded finite systems (the qubit) this all lives directly inside the C⋆-algebra. For
bosonic systems with unbounded `Q, P, a, a†`:

```
Heisenberg Lie algebra → polynomial CCR → Weyl C⋆-algebra → GNS/Fock representation
  → unbounded generators and spectrum
```

— the main conceptual bridge between the C⋆-algebraic, Lie-theoretic, oscillator, and
open-dynamics viewpoints. Genuinely separate development from the qubit work; not queued.
