# Exceptional Jordan / Albert implementation roadmap

## Objective

Formalize the genuine exceptional Euclidean Jordan algebra
`H₃(𝕆)` as a canonical PhyslibAlpha Jordan model, beginning with the generalized octonion
coordinate algebra and ending with its finite-dimensional trace/determinant and ordered-JB
realization.  This is not a Cstar specialization: its purpose is precisely to cover the
exceptional non-special case.

## Already owned

- `Algebra/Alternative.lean`: associators, Teichmüller, alternation, flexibility, Moufang, and
  McCrimmon left bumping.
- `Algebra/NuclearInvolution.lean`: nuclei, nuclear slipping, star/associator replacement, and
  commutation of nuclear elements with associator values.
- `JordanOrderUnit/FiniteRank.lean`: rank/trace/determinant and density-observable interface.
- `JordanOrderUnit/StructureAlgebra.lean`: Jordan derivation and Lie-symmetry interface.

## Mandatory dependency chain

1. `Algebra/Octonion.lean`
   - Generalized Cayley--Dickson `Octonion R a b c` over a commutative star-trivial base.
   - Additive/module/ring/star structures, scalar embedding, conjugation, scalar norm, and
     proved `IsAlternative` and `IsNuclearInvolution` instances.
   - Specialize later to `R = ℝ`, `a = b = c = -1`; do not install a fake normed/JB instance.

2. `Algebra/OctonionMatrix.lean`
   - Matrix multiplication over octonions and the Hermitian subtype.
   - Diagonal-real and off-diagonal-conjugacy API.  No associative-matrix lemmas may be reused
     without an explicit associativity hypothesis.

3. `JordanOrderUnit/Exceptional/HermitianMatrixIdentity.lean`
   - Matrix associator formulae for Hermitian `3 × 3` octonionic matrices.
   - Use the nuclear-involution and left-bumping theorems to prove closure of the symmetrized
     product and the Jordan identity.  This is the central exceptional theorem.

4. `JordanOrderUnit/Exceptional/Albert.lean`
   - Define `AlbertAlgebra := HermitianOctonionMatrix (Fin 3)`.
   - Provide `NonAssocCommRing`, real module/scalar compatibility, and `IsCommJordan` from the
     central identity; expose the three real diagonal coordinates and three octonionic
     off-diagonal coordinates (hence a real dimension-27 free-module basis after specializing
     to `ℝ`).
   - Define rank `3`, generic trace, and Moore determinant, then instantiate `TraceDeterminant`.

5. `JordanOrderUnit/Exceptional/Euclidean.lean`
   - Establish the positive cone, order unit, Euclidean Jordan norm, and the explicit
     `IsJBOrderUnit` compatibility theorem.
   - Only after this stage may Albert enter the JB spectral/CFC development.  The finite-
     dimensional JBW layer must be proved from the finite-dimensional order topology and normal
     state separation; it is a consequence, not an assumed instance.

## Non-negotiable proof gates

- No `sorry`, `admit`, or new axioms.
- No import of Cobord's parallel `JordanAlgebra` class or `HermitianJordan` hierarchy.
- The Albert Jordan identity must be a theorem, not a typeclass field supplied as an assumption.
- The order-unit norm equality must be proved at the Euclidean realization stage; square
  positivity alone is insufficient.
- Every stage passes `lake build PhyslibAlpha`, project linters, import-boundary checking, and
  `git diff --check`.

## Explicit non-goals until the chain is complete

- Copying real/complex/quaternionic matrix wrappers that duplicate Cstar self-adjoint models.
- Claiming an Albert CFC, JB, or JBW instance before the respective norm/order theorem exists.
- Treating generalized octonions as associative.
