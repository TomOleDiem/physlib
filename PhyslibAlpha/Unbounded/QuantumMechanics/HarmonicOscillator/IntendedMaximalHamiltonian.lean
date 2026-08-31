/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import PhyslibAlpha.Unbounded.QuantumMechanics.HarmonicOscillator.DifferentialCore

/-! # The intended maximal differential Hamiltonian

`DifferentialCore.lean` builds `differentialHamiltonianClosure`, the canonical self-adjoint
graph closure of the Schwartz-domain differential Hamiltonian, and proves essential
self-adjointness through Hermite-basis density.  That construction is completely honest, but it
leaves open the textbook question: is this *the* Hamiltonian, i.e. the maximal operator
naturally associated to the formal differential expression `-½∂² + ½x²`, independently of any
choice of eigenbasis?

This file answers that question with the standard (Reed–Simon) definition of "the maximal
operator associated to a formal differential expression": the **adjoint** of the minimal
(Schwartz-core) operator.  Concretely, `differentialHamiltonianMaximal q := (oneDimension
q).hamiltonian†`, the `LinearPMap.adjoint` of the Schwartz-domain Hamiltonian.  This is a
genuinely independent characterization — no Hermite eigenfunction appears in its definition,
only the general adjoint construction of `Mathlib.Analysis.InnerProductSpace.LinearPMap` applied
to the plain Schwartz-domain differential operator.

The main theorem, `differentialHamiltonianMaximal_eq_closure`, proves this maximal operator
equals the already-established canonical closure.  The proof is short because it reuses two
already-proven general facts about unbounded operators (`PhyslibAlpha.Unbounded.QuantumMechanics.Operators.
Unbounded`):

* `IsUnbounded.adjoint_closure_eq_adjoint` : a densely-defined closable operator and its closure
  have the same adjoint, `T.closure† = T†`;
* essential self-adjointness itself, i.e. `IsSelfAdjoint T.closure`, i.e. `T.closure† =
  T.closure` (definitionally, `IsSelfAdjoint A ↔ A† = A`).

Chaining these two facts gives `T† = T.closure† = T.closure` directly — this is exactly the
standard operator-theoretic fact that *the adjoint of an essentially self-adjoint operator is its
closure*, specialized to the actual differential Hamiltonian.

## Main results

* `adjoint_eq_closure_of_isEssentiallySelfAdjoint` : the general fact, for any symmetric,
  densely-defined, essentially self-adjoint `LinearPMap`.
* `differentialHamiltonianMaximal` : the maximal differential Hamiltonian, `(oneDimension
  q).hamiltonian†`.
* `differentialHamiltonianMaximal_eq_closure` : it equals `differentialHamiltonianClosure q`.
-/

@[expose] public section

noncomputable section

open QuantumMechanics.HarmonicOscillator.DifferentialCore

namespace OperatorAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {T : H →ₗ.[ℂ] H}

/-- **The adjoint of an essentially self-adjoint operator is its closure.**

If `T` is symmetric, densely defined, and its closure is self-adjoint (i.e. `T` is essentially
self-adjoint), then the adjoint `T†` — the standard textbook "maximal operator" associated to the
formal expression defining `T` — coincides with the closure `T.closure`.  This is completely
general operator theory: no eigenbasis, spectral measure, or model-specific fact is used, only
`IsUnbounded.adjoint_closure_eq_adjoint` (an unbounded operator and its closure share an adjoint)
and the definitional unfolding of `IsSelfAdjoint`. -/
lemma adjoint_eq_closure_of_isEssentiallySelfAdjoint
    (hsym : T.IsSymmetric) (hdense : T.HasDenseDomain) (hesa : IsSelfAdjoint T.closure) :
    T.adjoint = T.closure := by
  have hU : T.IsUnbounded := (hsym.isUnbounded_iff_hasDenseDomain).mpr hdense
  calc T.adjoint = T.closure.adjoint := hU.adjoint_closure_eq_adjoint.symm
    _ = T.closure := hesa

end OperatorAlgebra

namespace QuantumMechanics.HarmonicOscillator.DifferentialCore

open OperatorAlgebra

variable (q : OldOscillator)

/-- **The intended maximal differential Hamiltonian.**

The adjoint of the Schwartz-domain differential Hamiltonian `(oneDimension q).hamiltonian` — the
textbook "maximal operator" for the formal expression `-½∂² + ½x²`, i.e. the `LinearPMap` on the
largest domain compatible with the formal differential expression via integration-by-parts
duality against the Schwartz-domain minimal operator.  Independent of any choice of eigenbasis. -/
noncomputable def differentialHamiltonianMaximal (q : OldOscillator) :
    NewHilbertSpace →ₗ.[ℂ] NewHilbertSpace :=
  (oneDimension q).hamiltonian.adjoint

/-- **The intended maximal differential Hamiltonian equals the canonical closure.**

This is the two-definitions-of-the-same-operator theorem asked for by item 5 of
`general-theory-status.md`: the closure built in `DifferentialCore.lean` via essential
self-adjointness from Hermite-basis density is *exactly* the maximal operator associated to the
formal differential expression, defined independently as the adjoint of the Schwartz-domain
operator. -/
lemma differentialHamiltonianMaximal_eq_closure (q : OldOscillator) :
    differentialHamiltonianMaximal q = differentialHamiltonianClosure q :=
  adjoint_eq_closure_of_isEssentiallySelfAdjoint
    (oneDimension q).hamiltonian_isSymmetric
    (oneDimension q).hamiltonian_hasDenseDomain
    (differentialHamiltonianClosure_isSelfAdjoint q)

/-- Consequently, the maximal differential Hamiltonian's domain is exactly the finite
second-moment domain of the spectral measure — the same explicit domain description proved for
the closure. -/
lemma differentialHamiltonianMaximal_domain_eq_squareMoment (q : OldOscillator) :
    (differentialHamiltonianMaximal q).domain =
      OperatorAlgebra.spectralSquareMomentDomain (differentialHamiltonianSpectralMeasure q) := by
  rw [differentialHamiltonianMaximal_eq_closure]
  exact differentialHamiltonian_domain_eq_squareMoment q

/-- Consequently, the maximal differential Hamiltonian is self-adjoint. -/
lemma differentialHamiltonianMaximal_isSelfAdjoint (q : OldOscillator) :
    IsSelfAdjoint (differentialHamiltonianMaximal q) := by
  rw [differentialHamiltonianMaximal_eq_closure]
  exact differentialHamiltonianClosure_isSelfAdjoint q

end QuantumMechanics.HarmonicOscillator.DifferentialCore
end
