/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Multiplication
public import PhyslibAlpha.QuantumMechanics.Unbounded.Operators.Core.UnboundedExtras

/-!

# Extra multiplication-operator lemmas

Two lemmas this development's staging tree added on top of the base
`Physlib.QuantumMechanics.Operators.Multiplication` file, split out into their own file (same
reason and pattern as `Operators.Core.UnboundedExtras`: duplicating the base file under a new
namespace caused a duplicate-declaration clash when both were in scope simultaneously).

## Key results

- `QuantumMechanics.SpaceDHilbertSpace.mulOperator_closure_eq` : a real maximal multiplication
  operator is already its own self-adjoint closure.
- `QuantumMechanics.SpaceDHilbertSpace.mulOperator_isEssentiallySelfAdjoint` : maximal
  multiplication operators are a concrete source of essentially self-adjoint operators.

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace

open LinearPMap MeasureTheory ComplexConjugate

variable {d : ℕ}

/-- A real maximal multiplication operator is already its own self-adjoint closure. -/
lemma mulOperator_closure_eq {μ : Measure (Space d)} [IsFiniteMeasureOnCompacts μ]
    {f : Space d → ℂ} (hf : AEStronglyMeasurable f μ) (hf' : conj ∘ f = f) :
    (𝓜 μ f).closure = 𝓜 μ f := by
  exact (mulOperator_isSelfAdjoint_ofReal hf hf').isClosed.closure_eq

/-- Maximal multiplication operators provide a concrete source of essential self-adjoint
operators: the maximal real multiplication operator is its own closure. -/
lemma mulOperator_isEssentiallySelfAdjoint {μ : Measure (Space d)}
    [IsFiniteMeasureOnCompacts μ] {f : Space d → ℂ}
    (hf : AEStronglyMeasurable f μ) (hf' : conj ∘ f = f) :
    (𝓜 μ f).IsEssentiallySelfAdjoint :=
  (mulOperator_isSelfAdjoint_ofReal hf hf').isEssentiallySelfAdjoint

end SpaceDHilbertSpace
end QuantumMechanics
