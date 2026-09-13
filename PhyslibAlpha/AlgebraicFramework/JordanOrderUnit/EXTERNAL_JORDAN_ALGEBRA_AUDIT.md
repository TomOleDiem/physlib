# Cobord/JordanAlgebra reuse audit

Audited against `Cobord/JordanAlgebra` commit `8dd1d6719cb4c5e275ed7ae578bbec5574a64a39`
(2026-08-24), using its Lean 4.31 source. PhyslibAlpha uses Lean 4.33 and has a deliberately
different hierarchy, so it is not a dependency or a source tree to vendor wholesale.

## Adopted now

`Examples/SpinFactor.lean` ports the physics-relevant algebraic core of
`Jordan/SpinFactor.lean` into the canonical PhyslibAlpha interfaces:

- the generic spin-factor carrier and product;
- its unit, additive/module structure, commutative nonassociative-ring witness, and Jordan
  identity for a symmetric bilinear form;
- vector/scalar component API;
- the rank-two determinant and quadratic Cayley--Hamilton identity.

It is intentionally only a `NonAssocCommRing`/`IsCommJordan` model. A real positive-definite
form has a Lorentz cone and a JB norm, but establishing that norm/order compatibility belongs to
the later analytic realization file. Installing a fictitious `JBAlgebra` or order-unit instance
here would violate the boundary repaired in B1.

`StructureAlgebra.lean` ports the reusable symmetry layer at the same generality as the
canonical real Jordan core:

- a bundled `JordanDerivation` carrier, proved to be a real vector space and Lie algebra under
  commutator;
- the fact that every derivation fixes the unit;
- bundled inner derivations and their proved commutator law.

This exposes infinitesimal reversible dynamics to concrete models (including the spin factor)
without creating a second multiplication-operator or Jordan-algebra hierarchy.

`FiniteRank.lean` transfers the finite-rank trace/determinant interface without conflating it
with the general order-unit or JBW state spaces:

- rank, generic trace, and homogeneous determinant data;
- density observables as the trace-one slice of Mathlib's canonical sum-of-squares cone;
- pure density observables, expectation functionals, and proved square-weighted mixing laws.

`Algebra/Alternative.lean` is the foundational exceptional-model transfer: it supplies the
alternative associator calculus, Teichmüller identity, flexible and left Moufang laws, and
McCrimmon's left bumping formula.  This is the correct common layer below octonions and the
Albert algebra; matrix-model code is intentionally not duplicated before that coordinate algebra
and its order/norm realization exist.

The executable exceptional dependency order and proof gates are recorded in
`EXCEPTIONAL_ALBERT_ROADMAP.md`.

## Already present here at a stronger or more general level

| External material | PhyslibAlpha owner | Decision |
| --- | --- | --- |
| `JordanAlgebra.lean`: powers, multiplication operators, linearized identity | `JordanOrderUnit/Operator.lean`, `Quadratic/Fundamental.lean` | Do not duplicate. Our `mulLeft_triple_normalize`, polarizations, and quadratic API are the canonical real-Jordan formulation. |
| `JordanTriple.lean` | `Quadratic/Triple.lean` | Do not duplicate; ours identifies the triple operation with the canonical bilinear quadratic representation. |
| `StructureAlgebra.lean`: derivations and inner derivations | `StructureAlgebra.lean`, `Algebra/Derivation.lean`, `JB/Dynamics.lean`, `Quadratic/Fundamental.lean` | The bundled carrier/Lie layer is ported; raw predicate, generator, and inner-derivation theorems remain at their existing canonical owners. |
| `FormallyReal.lean`: square-sum consequences | `JB/Basic.lean`, `JB/Order.lean` | Do not duplicate. The JB layer derives formal reality and the stronger exact positive-cone theorem. |
| real/complex/quaternionic Hermitian models | `CStarAlgebra/Jordan.lean` and Hilbert/Cstar realization layers | Retain the canonical self-adjoint Cstar realization. Porting finite matrices would create a parallel specialization and add no abstract physics capability. |

## Deliberately deferred concrete realizations

The following are worthwhile *only after* their analytic/order data is stated at the right level:

1. **Finite-dimensional Euclidean spin factors.** Add the Lorentz cone, Euclidean JB norm,
   state space, and symmetries as a realization of the newly ported algebraic model.
2. **Exceptional Albert algebra.** Cobord's octonion/Hermitian-matrix development is a valuable
   future finite-dimensional exceptional observable model. It depends on a substantial
   alternative-algebra, nuclear-involution, and Moore-determinant stack. Port it as a separate
   `Exceptional/Albert` realization after a compatibility audit; it must not leak octonionic
   multiplication into abstract JB/CFC/JBW files.

## Not imported

No external source is imported and no external axioms are used. This preserves a single
Mathlib/toolchain graph, prevents duplicate Jordan classes, and keeps every transferred theorem
under PhyslibAlpha's proof and lint gates.
