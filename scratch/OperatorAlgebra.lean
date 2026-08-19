/-
Scratch space for Mathematics/OperatorAlgebra/. Not part of any lean_lib target, not imported
anywhere, not linted or built. A holding pen for content cut during cleanup that we might still
want, pending a decision on where (or whether) it belongs.
-/

/-
Cut from Basic.lean: `IsClassicalObservableAlgebra`. It was a marker `Prop` restating
commutativity, unused anywhere else in the repo, and mathematically redundant with
`[CommCStarAlgebra A]` itself.

section Classical

variable {A : Type*}
  [CommCStarAlgebra A]
  [PartialOrder A]
  [StarOrderedRing A]

/--
A marker proposition expressing that an observable algebra is classical.

This is mathematically equivalent here to commutativity. In most theorems it is
preferable simply to assume `[CommCStarAlgebra A]` directly.
-/
def IsClassicalObservableAlgebra : Prop :=
  ∀ a b : A, a * b = b * a

omit [PartialOrder A] [StarOrderedRing A]
@[simp]
lemma isClassicalObservableAlgebra :
    IsClassicalObservableAlgebra (A := A) := by
  intro a b
  exact mul_comm a b

end Classical
-/
