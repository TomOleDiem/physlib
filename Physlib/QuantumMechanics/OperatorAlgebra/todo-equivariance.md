# TODO: Hamiltonian equivalence under automorphisms

## TL;DR for the implementation agent

Implement the structural statement that changing the representation of a
Hamiltonian changes its flow by the corresponding conjugation.

This TODO is for the new equivalence/equivariance layer only. Do not introduce
a quotient type yet. The important API is the explicit
intertwining/equivariance theorem and its iff classification.

## 1. Automorphisms act on observables

Ensure that a star automorphism acts on self-adjoint elements:

```lean
β.observable : Observable A → Observable A
```

If no clean API exists, add the minimal restriction of
`β : A ≃⋆ₐ[ℂ] A` to self-adjoint elements, together with the basic lemmas
needed below (coercion, identity, composition, inverse, and preservation of
the observable Lie/Jordan operations as appropriate).

## 2. Conjugation of automorphism groups

Define the change-of-coordinates operation

```lean
AutomorphismGroup.conj
    (β : A ≃⋆ₐ[ℂ] A)
    (α : AutomorphismGroup A) :
    AutomorphismGroup A
```

with

```text
(conj β α) t = β ∘ α t ∘ β⁻¹.
```

Prove the basic identity, inverse, composition, and group-action laws needed
to use `conj` without unfolding its implementation.

## 3. Hamiltonian-flow equivariance

Prove the structural theorem

```lean
lemma hamiltonianFlow_map
    (β : B(𝓗) ≃⋆ₐ[ℂ] B(𝓗))
    (H : Observable (B(𝓗))) :
    hamiltonianFlow ℏ (β.observable H) =
      (hamiltonianFlow ℏ H).conj β
```

Equivalently,

```text
α_t^(β(H)) = β ∘ α_t^H ∘ β⁻¹.
```

Prefer proving this from the existing Heisenberg equation, uniqueness, and
preservation of the observable Lie bracket:

```text
β(⟦H, A⟧) = ⟦β(H), β(A)⟧.
```

Keep the theorem at the explicit flow/intertwining level; do not hide the
content behind an equivalence-class construction.

## 4. Unitary specialization

Add the unitary specialization using `Unitary.conjStarAlgAut`:

```text
K = V H V*  ⟹
α_t^K = Ad_V ∘ α_t^H ∘ Ad_{V*}.
```

Connect this result to the general automorphism theorem and avoid duplicating
the proof when the unitary automorphism is already an instance of the general
case.

## 5. Combine with scalar-shift invariance

Combine equivariance with the already-proved scalar-shift invariance:

```text
K = β(H) + c 1  ⟹  α^K = β α^H β⁻¹.
```

Make the scalar type and the embedding of `c 1` explicit in Lean, and retain
the exact time-parameter conventions of the existing Hamiltonian-flow API.

## 6. Converse and classification

Add the converse/classification theorem:

```text
α^K = β α^H β⁻¹
  ↔ ∃ c : ℝ, K = β(H) + c 1.
```

Use `conjStarAlgAut_surjective` to package the physical/unitary version:

```text
α^H ≅ α^K
  ↔ ∃ V, c, K = V H V* + c 1.
```

`ProjectiveUnitary ≃ Aut⋆(B(𝓗))` already provides the static group-theoretic
interpretation. Reuse it rather than introducing a new quotient or duplicate
automorphism representation.

## Acceptance checklist

- [x] Star automorphisms restrict cleanly to observables. `StarAlgEquiv.observable` (and its
      coercion/identity/composition/inverse/bracket-preservation API), in
      `Dynamics/Automorphism.lean`.
- [x] `AutomorphismGroup.conj` is defined and has usable API lemmas: `conj_apply`, `conj_refl`,
      `conj_conj`, `conj_symm_conj`, `conj_conj_symm`, in `Dynamics/Automorphism.lean`.
- [x] Hamiltonian flow is equivariant under star-automorphism conjugation: `hamiltonianFlow_map`,
      via the algebraic (no-derivatives) route through `unitaryEvolution_map`, in
      `Dynamics/Hamiltonian.lean`.
- [x] The unitary specialization is stated using `Unitary.conjStarAlgAut`:
      `hamiltonianFlow_conj_unitary`, in `Dynamics/Hamiltonian.lean`.
- [x] Scalar-shift invariance is combined with equivariance: `hamiltonianFlow_map_add_smul_one`,
      in `Dynamics/Hamiltonian.lean`.
- [x] The automorphism-level iff classification is proved: `hamiltonianFlow_conj_iff`, built from
      the general (`β`-independent) converse `hamiltonianFlow_eq_iff` (proved here — it was *not*
      already present despite `Qubit/todo.md` claiming otherwise) plus `hamiltonianFlow_map`, in
      `Dynamics/Hamiltonian.lean`.
- [x] The unitary/projective-unitary classification is packaged:
      `hamiltonianFlow_iff_exists_unitary`, in `Dynamics/Hamiltonian.lean`.
- [x] No quotient type is introduced. `ProjectiveUnitary`/`PU.mulEquivAut` and
      `conjStarAlgAut_surjective` (both pre-existing) are reused only to translate an existential
      over `B(𝓗) ≃⋆ₐ[ℂ] B(𝓗)` into an existential over unitaries.

