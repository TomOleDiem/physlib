/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.AtomPhotonBounds
public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.ResolventBridge
/-!

# The Jaynes-Cummings coupling has a bounded resolvent

The coupling `g a†σ⁻ + ḡ σ⁺a` of a cavity and its atom is essentially self-adjoint on the algebraic
atom-photon space.

## i. Overview

The coupling preserves the number of quanta `n = N_ph + σ⁺σ⁻` at the cavity. For fixed `n` and fixed
state of everything else it acts on at most two basis vectors: `n` photons with the atom in the
ground state and `n - 1` photons with the atom excited. These blocks are finite and invariant. The
criterion `dense_range_shiftMap_of_finite_invariant` gives density of the range of `JC + i c`. No
particle-number sector of the whole lattice is fixed.

## ii. Key results

- `InfiniteBosons.jcBlock`: the invariant block of a basis vector.
- `InfiniteBosons.jc_support_subset`: the coupling preserves the block.
- `InfiniteBosons.jaynesCummings_resolvent`: the bounded resolvent.

## iii. Table of contents

- A. The invariant block
- B. The resolvent

## iv. References

* B. W. Shore, P. L. Knight, The Jaynes-Cummings model, J. Mod. Opt. 40 (1993) 1195.
-/

@[expose] public section

open Finsupp

noncomputable section
namespace InfiniteBosons
variable {L : Type*} [DecidableEq L]

lemma jc_apply_single (x : L) (g : ℂ) (b : SBBasis L) :
    (jaynesCummings x g).1.1 (single b 1) =
      g • creS x (lowS x (single b 1)) + (starRingEnd ℂ g) • raiseS x (annS x (single b 1)) := rfl

/-- The photon plus atom excitation number at `x`. -/
def jcCount (x : L) (b : SBBasis L) : ℕ := b.1 x + (if x ∈ b.2 then 1 else 0)

/-- The state with `n` quanta at `x` and the atom in the ground state. -/
def jcFirst (x : L) (b : SBBasis L) : SBBasis L :=
  (b.1.update x (jcCount x b), b.2.erase x)

/-- The state with `n - 1` photons at `x` and the atom excited. -/
def jcSecond (x : L) (b : SBBasis L) : SBBasis L :=
  (b.1.update x (jcCount x b - 1), insert x (b.2.erase x))

/-- The invariant block of the Jaynes-Cummings coupling at `x`. -/
def jcBlock (x : L) (b : SBBasis L) : Finset (SBBasis L) :=
  if jcCount x b = 0 then {jcFirst x b} else {jcFirst x b, jcSecond x b}

lemma mem_jcBlock_self (x : L) (b : SBBasis L) : b ∈ jcBlock x b := by
  unfold jcBlock jcFirst jcSecond jcCount
  by_cases h : x ∈ b.2
  · have hn : b.1 x + (if x ∈ b.2 then 1 else 0) ≠ 0 := by simp [h]
    rw [if_neg hn]
    refine Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr ?_))
    simp only [h, if_true]
    refine Prod.ext ?_ ?_
    · ext l; by_cases hl : l = x
      · subst hl; simp
      · simp [Finsupp.update_apply, hl]
    · simp [Finset.insert_erase h]
  · by_cases h0 : b.1 x = 0
    · have hn : b.1 x + (if x ∈ b.2 then 1 else 0) = 0 := by simp [h, h0]
      rw [if_pos hn]
      refine Finset.mem_singleton.mpr (Prod.ext ?_ ?_)
      · ext l; by_cases hl : l = x
        · subst hl; simp [h0, h]
        · simp [Finsupp.update_apply, hl]
      · simp [Finset.erase_eq_of_notMem h]
    · have hn : b.1 x + (if x ∈ b.2 then 1 else 0) ≠ 0 := by simp [h, h0]
      rw [if_neg hn]
      refine Finset.mem_insert.mpr (Or.inl (Prod.ext ?_ ?_))
      · ext l; by_cases hl : l = x
        · subst hl; simp [h]
        · simp [Finsupp.update_apply, hl]
      · simp [Finset.erase_eq_of_notMem h]

lemma support_single_subset_of' {a : SBBasis L} {c : ℂ} {F : Finset (SBBasis L)}
    (h : c ≠ 0 → a ∈ F) : ((single a c).support : Set (SBBasis L)) ⊆ F := by
  intro γ hγ
  by_cases hc : c = 0
  · simp [hc] at hγ
  · have := Finsupp.support_single_subset (Finset.mem_coe.mp hγ)
    rw [Finset.mem_singleton] at this
    rw [this]; exact h hc

lemma jcBlock_cases (x : L) (b β : SBBasis L) (hβ : β ∈ jcBlock x b) :
    (β = jcFirst x b ∧ x ∉ β.2 ∧ β.1 x = jcCount x b) ∨
    (β = jcSecond x b ∧ x ∈ β.2 ∧ β.1 x + 1 = jcCount x b ∧ jcCount x b ≠ 0) := by
  unfold jcBlock at hβ
  have hfirst : x ∉ (jcFirst x b).2 ∧ (jcFirst x b).1 x = jcCount x b := by
    simp [jcFirst]
  by_cases h0 : jcCount x b = 0
  · rw [if_pos h0, Finset.mem_singleton] at hβ
    subst hβ
    exact Or.inl ⟨rfl, hfirst⟩
  · rw [if_neg h0] at hβ
    rcases Finset.mem_insert.mp hβ with h | h
    · subst h; exact Or.inl ⟨rfl, hfirst⟩
    · rw [Finset.mem_singleton] at h
      subst h
      refine Or.inr ⟨rfl, ?_, ?_, h0⟩
      · simp [jcSecond]
      · simp [jcSecond]; omega

lemma jcFirst_mem (x : L) (b : SBBasis L) : jcFirst x b ∈ jcBlock x b := by
  unfold jcBlock
  split_ifs
  · exact Finset.mem_singleton_self _
  · exact Finset.mem_insert_self _ _

lemma jcSecond_mem (x : L) (b : SBBasis L) (h : jcCount x b ≠ 0) : jcSecond x b ∈ jcBlock x b := by
  unfold jcBlock
  rw [if_neg h]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

lemma jc_support_subset (x : L) (g : ℂ) (b : SBBasis L) {β : SBBasis L}
    (hβ : β ∈ jcBlock x b) :
    (((jaynesCummings x g).1.1 (single β 1)).support : Set (SBBasis L)) ⊆ jcBlock x b := by
  rw [jc_apply_single]
  intro γ hγ
  have hγ' := Finset.mem_coe.mp hγ
  have hsub := Finsupp.support_add hγ'
  rcases Finset.mem_union.mp hsub with h | h
  · -- g • creS (lowS single)
    have h1 := Finsupp.support_smul h
    rw [lowS_single] at h1
    by_cases hx : x ∈ β.2
    · rw [if_pos hx, creS_single] at h1
      have := Finsupp.support_single_subset h1
      rw [Finset.mem_singleton] at this
      subst this
      rcases jcBlock_cases x b β hβ with ⟨_, hx', _⟩ | ⟨hs, _, hn, hn0⟩
      · exact absurd hx hx'
      · subst hs
        have hγeq : ((jcSecond x b).1 + single x 1, ((jcSecond x b).2).erase x) = jcFirst x b := by
          refine Prod.ext ?_ ?_
          · ext l; by_cases hl : l = x
            · subst hl; simp [jcSecond, jcFirst] at hn ⊢; omega
            · simp [jcSecond, jcFirst, Finsupp.update_apply, hl]
          · simp [jcSecond, jcFirst]
        rw [hγeq]
        exact Finset.mem_coe.mpr (jcFirst_mem x b)
    · rw [if_neg hx] at h1
      simp at h1
  · have h1 := Finsupp.support_smul h
    rw [annS_single, raiseS_single] at h1
    by_cases hx : x ∈ β.2
    · rw [if_neg (by simpa using hx)] at h1
      simp at h1
    · rw [if_pos (by simpa using hx)] at h1
      have hmem := Finsupp.support_single_subset h1
      rw [Finset.mem_singleton] at hmem
      subst hmem
      have hc : (((Real.sqrt (β.1 x) : ℝ) : ℂ) * 1) ≠ 0 := by
        intro h0
        rw [h0] at h1
        simp at h1
      rcases jcBlock_cases x b β hβ with ⟨hs, _, hn⟩ | ⟨_, hx', _⟩
      · have hn0 : jcCount x b ≠ 0 := by
          intro h0; apply hc; rw [hn, h0]; simp
        have hγeq : ((β.1 - single x 1, insert x β.2)) = jcSecond x b := by
          subst hs
          refine Prod.ext ?_ ?_
          · ext l; by_cases hl : l = x
            · subst hl; simp [jcFirst, jcSecond]
            · simp [jcSecond, jcFirst, Finsupp.update_apply, hl]
          · simp [jcSecond, jcFirst]
        rw [hγeq]
        exact Finset.mem_coe.mpr (jcSecond_mem x b hn0)
      · exact absurd hx' hx

/-- **The Jaynes-Cummings coupling has a bounded resolvent.** The coupling at one cavity conserves
the sum of the photon number and the atom excitation at that cavity and changes nothing else. Each
basis vector lies in a block of at most two basis vectors that the coupling preserves. Hence the
range of `JC + i c` is dense and the resolvent is bounded by `1/|c|`. -/
theorem jaynesCummings_resolvent (x : L) (g : ℂ) {c : ℝ} (hc : c ≠ 0) :
    ∃ R : HilbertSp (SBBasis L) →L[ℂ] HilbertSp (SBBasis L), ‖R‖ ≤ 1 / |c| ∧
      ∀ f, R (shiftMap (jaynesCummings x g).1.1 c f) = embed f := by
  have hsym : ∀ f h, pair ((jaynesCummings x g).1.1 f) h =
      pair f ((jaynesCummings x g).1.1 h) := fun f h => by
    have := star_fst_pair (jaynesCummings x g) f h
    rwa [star_jaynesCummings] at this
  exact polyOp_resolvent (jaynesCummings x g) (star_jaynesCummings x g) hc
    (dense_range_shiftMap_of_finite_invariant _ hsym
      (fun b => ⟨jcBlock x b, mem_jcBlock_self x b, fun β hβ =>
        jc_support_subset x g b (Finset.mem_coe.mp hβ)⟩) hc)

end InfiniteBosons
