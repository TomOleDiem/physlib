/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann, Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded
public import Physlib.Meta.TODO.Basic

/-!

# Extra unbounded-operator lemmas

Two lemmas about `LinearPMap.IsEssentiallySelfAdjoint`/`LinearPMap.unitaryConj` that this
development's staging tree added on top of the base `Physlib.QuantumMechanics.Operators.Unbounded`
file, split out into their own file (rather than duplicating the ~1000-line base file under a new
namespace, which caused a duplicate-declaration clash when both were in scope simultaneously) so
they can be imported alongside the genuine base file with no risk of that clash.

## Key results

- `LinearPMap.IsClosable.unitaryConj_closure` : closure commutes with unitary conjugation.
- `LinearPMap.IsEssentiallySelfAdjoint.of_le_of_isSymmetric` : essential self-adjointness passes to
  a densely-defined symmetric extension.

-/

@[expose] public section

namespace LinearPMap

open Submodule

variable
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {T : H →ₗ.[ℂ] H}

variable (u : H ≃ₗᵢ[ℂ] H') (A : H →ₗ.[ℂ] H)

/-- Closure commutes with unitary conjugation.  This is the graph-level transport theorem used
to move a core theorem through a unitary representation. -/
lemma IsClosable.unitaryConj_closure [CompleteSpace H] [CompleteSpace H']
    (u : H ≃ₗᵢ[ℂ] H') (A : H →ₗ.[ℂ] H) (hA : A.IsClosable) :
    (unitaryConj u A).closure = unitaryConj u A.closure := by
  let e : (H' × H') ≃L[ℂ] (H × H) :=
    u.symm.toContinuousLinearEquiv.prodCongr u.symm.toContinuousLinearEquiv
  have graph_conj (D : H →ₗ.[ℂ] H) :
      e '' ((unitaryConj u D).graph : Set (H' × H')) =
        (D.graph : Set (H × H)) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨z, hz, hzy⟩ := (mem_graph_iff _).mp hq
      let w : D.domain :=
        ⟨u.symm (z : H'), (mem_unitaryConj_domain_iff u D).mp z.2⟩
      refine (mem_graph_iff D).mpr ⟨w, ?_, ?_⟩
      · change u.symm (z : H') = u.symm q.1
        rw [hz]
      · change D w = u.symm q.2
        apply u.injective
        have hh := unitaryConj_apply u D z
        rw [u.apply_symm_apply]
        exact hh.symm.trans hzy
    · rintro hp
      obtain ⟨z, hz, hzy⟩ := (mem_graph_iff D).mp hp
      let z' : (unitaryConj u D).domain :=
        ⟨u (z : H), map_mem_unitaryConj_domain u D z⟩
      refine ⟨(u (z : H), u (D z)), ?_, ?_⟩
      · exact (mem_graph_iff _).mpr
          ⟨z', rfl, unitaryConj_apply_map u D z⟩
      · simp [e, hz, hzy]
  have himage : e '' ((unitaryConj u A).graph.topologicalClosure : Set _) =
      (A.closure.graph : Set _) := by
    rw [Submodule.topologicalClosure_coe]
    rw [e.image_closure]
    rw [graph_conj A]
    rw [← Submodule.topologicalClosure_coe]
    exact congrArg (fun s : Submodule ℂ (H × H) => (s : Set (H × H)))
      hA.graph_closure_eq_closure_graph
  have himage' : e '' ((unitaryConj u A.closure).graph : Set _) =
      (A.closure.graph : Set _) := graph_conj A.closure
  have hgraphs : ((unitaryConj u A).graph.topologicalClosure : Set _) =
      ((unitaryConj u A.closure).graph : Set _) :=
    (Set.image_injective.mpr e.injective) (himage.trans himage'.symm)
  have hgraphs' : (unitaryConj u A).graph.topologicalClosure =
      (unitaryConj u A.closure).graph := by
    apply SetLike.ext'
    exact hgraphs
  have hB : (unitaryConj u A).IsClosable :=
    ⟨unitaryConj u A.closure, hgraphs'⟩
  exact eq_of_eq_graph (hB.graph_closure_eq_closure_graph.symm.trans hgraphs')

variable {u A}

/-- Essential self-adjointness passes to a densely-defined symmetric extension.

This is the operator-theoretic fact needed when a convenient eigenvector core is first shown to be
essentially self-adjoint and the differential expression is then identified as a symmetric
extension of that core.  The proof is purely about graph closure and adjoints: if `S` is
essentially self-adjoint, then every symmetric extension `T` is squeezed between the self-adjoint
closure of `S` and its adjoint, so both closures coincide. -/
lemma IsEssentiallySelfAdjoint.of_le_of_isSymmetric [CompleteSpace H]
    {S T : H →ₗ.[ℂ] H} (hS : S.IsEssentiallySelfAdjoint) (hST : S ≤ T)
    (hT : T.IsSymmetric) : T.IsEssentiallySelfAdjoint := by
  have hTdense : T.HasDenseDomain := hS.hasDenseDomain.mono hST.1
  have hTclosable : T.IsClosable := hT.isClosable hTdense
  have hSclosure_le : S.closure ≤ T.closure := by
    exact hTclosable.closure_isClosed.closure_eq ▸
      hTclosable.closure_isClosed.isClosable.closure_mono
        (hST.trans T.le_closure)
  have hTclosure_le : T.closure ≤ S.closure := by
    have hTadj : T.closure ≤ T† := hT.closure_le_adjoint hTdense
    have hAdj : T† ≤ S† := adjoint_antitone (Or.inl hS.hasDenseDomain) hST
    have hSadj : S† = S.closure := by
      rw [← hS.isUnbounded.adjoint_closure_eq_adjoint]
      exact isSelfAdjoint_def.mp hS
    exact hTadj.trans (hAdj.trans_eq hSadj)
  change IsSelfAdjoint T.closure
  rw [← eq_of_le_of_ge hSclosure_le hTclosure_le]
  exact hS

end LinearPMap
