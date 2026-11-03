/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.PolynomialAlgebra
/-!

# The atom-photon space of an arbitrary lattice

Photons in every site and two-level atoms at every site, with finitely many excitations, and the
operators of the Jaynes-Cummings coupling.

## i. Overview

A state of the atom-photon system has finitely many photons and finitely many excited atoms. It is
a finite linear combination of basis vectors `(α, s)` with the occupation numbers `α : L →₀ ℕ` and
the finite set `s` of excited atoms. No particle-number sector, no finite lattice and no Hilbert
space completion is used. The photon operators act on `α` as in the pure boson space. The atom
operators `σ_x^±` act on `s`. All four are formally adjointable for the sesquilinear pairing of the
basis. The Jaynes-Cummings coupling `g a_x† σ_x⁻ + ḡ σ_x⁺ a_x` is a self-adjoint element of the
algebra of adjointable operators. It does not conserve the photon number. It conserves the sum of
the photon number and the number of excited atoms.

## ii. Key results

- `InfiniteBosons.SBPre`: the algebraic atom-photon space.
- `InfiniteBosons.annOpS`, `InfiniteBosons.creOpS`, `InfiniteBosons.lowOpS`,
  `InfiniteBosons.raiseOpS`: the operators as adjointable operators.
- `InfiniteBosons.jaynesCummings`, `InfiniteBosons.star_jaynesCummings`: the coupling and its
  self-adjointness.

## iii. Table of contents

- A. The space and its operators
- B. Formal adjointness
- C. The algebra elements

## iv. References

* E. T. Jaynes and F. W. Cummings, Comparison of quantum and semiclassical radiation theories with
  application to the beam maser, Proc. IEEE 51, 89 (1963).
-/

@[expose] public section

open Finsupp

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- Basis of the atom-photon space: boson occupation numbers and the finite set of excited atoms. -/
abbrev SBBasis (L : Type*) := Occ L × Finset L

/-- The algebraic atom-photon space: finitely many photons and finitely many excited two-level
atoms, in arbitrary modes and sites. -/
abbrev SBPre (L : Type*) := SBBasis L →₀ ℂ

/-- Photon annihilation at the site `x`. -/
def annS (x : L) : SBPre L →ₗ[ℂ] SBPre L :=
  Finsupp.lsum ℂ fun b => ((Real.sqrt (b.1 x) : ℝ) : ℂ) •
    Finsupp.lsingle (b.1 - single x 1, b.2)

/-- Photon creation at the site `x`. -/
def creS (x : L) : SBPre L →ₗ[ℂ] SBPre L :=
  Finsupp.lsum ℂ fun b => ((Real.sqrt (b.1 x + 1) : ℝ) : ℂ) •
    Finsupp.lsingle (b.1 + single x 1, b.2)

/-- Atom lowering `σ⁻` at the site `x`: the atom goes from excited to ground. -/
def lowS (x : L) : SBPre L →ₗ[ℂ] SBPre L :=
  Finsupp.lsum ℂ fun b => if x ∈ b.2 then Finsupp.lsingle (b.1, b.2.erase x) else 0

/-- Atom raising `σ⁺` at the site `x`: the atom goes from ground to excited. -/
def raiseS (x : L) : SBPre L →ₗ[ℂ] SBPre L :=
  Finsupp.lsum ℂ fun b => if x ∉ b.2 then Finsupp.lsingle (b.1, insert x b.2) else 0

lemma annS_single (x : L) (b : SBBasis L) (c : ℂ) :
    annS x (single b c) = single (b.1 - single x 1, b.2) (((Real.sqrt (b.1 x) : ℝ) : ℂ) * c) := by
  simp [annS, Finsupp.lsum_single, Finsupp.smul_single]

lemma creS_single (x : L) (b : SBBasis L) (c : ℂ) :
    creS x (single b c) = single (b.1 + single x 1, b.2) (((Real.sqrt (b.1 x + 1) : ℝ) : ℂ) * c) := by
  simp [creS, Finsupp.lsum_single, Finsupp.smul_single]

lemma lowS_single (x : L) (b : SBBasis L) (c : ℂ) :
    lowS x (single b c) = if x ∈ b.2 then single (b.1, b.2.erase x) c else 0 := by
  by_cases h : x ∈ b.2 <;> simp [lowS, Finsupp.lsum_single, h]

lemma raiseS_single (x : L) (b : SBBasis L) (c : ℂ) :
    raiseS x (single b c) = if x ∉ b.2 then single (b.1, insert x b.2) c else 0 := by
  by_cases h : x ∈ b.2 <;> simp [raiseS, Finsupp.lsum_single, h]


lemma sb_pair_single (b b' : SBBasis L) :
    pair (single b (1 : ℂ)) (single b' (1 : ℂ)) = if b = b' then 1 else 0 := by
  rw [pair_single_single]; simp

lemma lowS_raiseS_basis (x : L) (b b' : SBBasis L) :
    pair (lowS x (single b 1)) (single b' 1) = pair (single b 1) (raiseS x (single b' 1)) := by
  rw [lowS_single, raiseS_single]
  by_cases h1 : x ∈ b.2
  · by_cases h2 : x ∉ b'.2
    · rw [if_pos h1, if_pos h2, sb_pair_single, sb_pair_single]
      by_cases e : (b.1, b.2.erase x) = b'
      · have : b = (b'.1, insert x b'.2) := by
          rw [← e]; ext <;> simp [Finset.insert_erase h1]
        rw [if_pos e, if_pos this]
      · have : ¬ b = (b'.1, insert x b'.2) := by
          intro hb
          apply e
          rw [hb]; ext <;> simp [Finset.erase_insert h2]
        rw [if_neg e, if_neg this]
    · rw [if_pos h1, if_neg h2, sb_pair_single]
      have : ¬ (b.1, b.2.erase x) = b' := by
        intro e; apply h2; rw [← e]; simp
      simp [this, pair_zero_right]
  · rw [if_neg h1]
    by_cases h2 : x ∉ b'.2
    · rw [if_pos h2, sb_pair_single]
      have : ¬ b = (b'.1, insert x b'.2) := by
        intro hb; apply h1; rw [hb]; simp
      simp [this, pair_zero_left]
    · rw [if_neg h2]; simp [pair_zero_left, pair_zero_right]


lemma single_le_iff'' (x : L) (α : Occ L) : single x 1 ≤ α ↔ 1 ≤ α x := by
  rw [Finsupp.single_le_iff]

lemma annS_creS_basis (x : L) (b b' : SBBasis L) :
    pair (annS x (single b 1)) (single b' 1) = pair (single b 1) (creS x (single b' 1)) := by
  rw [annS_single, creS_single, pair_single_single, pair_single_single]
  by_cases h : b.1 = b'.1 + single x 1 ∧ b.2 = b'.2
  · have h1 : b.1 x = b'.1 x + 1 := by rw [h.1]; simp
    have h2 : (b.1 - single x 1, b.2) = b' :=
      Prod.ext (by show b.1 - single x 1 = b'.1; rw [h.1]; simp) h.2
    have h3 : b = (b'.1 + single x 1, b'.2) := Prod.ext h.1 h.2
    rw [if_pos h2, if_pos h3, h1]
    simp
  · have h3 : ¬ b = (b'.1 + single x 1, b'.2) := fun hb => h ⟨by rw [hb], by rw [hb]⟩
    rw [if_neg h3]
    by_cases h2 : (b.1 - single x 1, b.2) = b'
    · have hx : b.1 x = 0 := by
        by_contra hx
        apply h
        have hle : single x 1 ≤ b.1 :=
          (single_le_iff'' x b.1).mpr (Nat.one_le_iff_ne_zero.mpr hx)
        refine ⟨?_, (Prod.ext_iff.mp h2).2⟩
        have := (Prod.ext_iff.mp h2).1
        simp only at this
        rw [← this]
        exact (tsub_add_cancel_of_le hle).symm
      simp [hx]
    · rw [if_neg h2]


lemma adjoint_basis_swap {B : Type*} [DecidableEq B] {T S : (B →₀ ℂ) →ₗ[ℂ] (B →₀ ℂ)}
    (h : ∀ b b' : B, pair (T (single b 1)) (single b' 1) = pair (single b 1) (S (single b' 1)))
    (b b' : B) : pair (S (single b 1)) (single b' 1) = pair (single b 1) (T (single b' 1)) := by
  have h1 := pair_conj_symm (S (single b 1)) (single b' 1)
  have h2 := pair_conj_symm (T (single b' 1)) (single b 1)
  have h3 := h b' b
  rw [h3] at h2
  rw [h1] at h2
  simpa using h2.symm

lemma raiseS_lowS_basis (x : L) (b b' : SBBasis L) :
    pair (raiseS x (single b 1)) (single b' 1) = pair (single b 1) (lowS x (single b' 1)) :=
  adjoint_basis_swap (T := lowS x) (S := raiseS x) (lowS_raiseS_basis x) b b'

lemma creS_annS_basis (x : L) (b b' : SBBasis L) :
    pair (creS x (single b 1)) (single b' 1) = pair (single b 1) (annS x (single b' 1)) :=
  adjoint_basis_swap (T := annS x) (S := creS x) (annS_creS_basis x) b b'

lemma pair_annS (x : L) (f g : SBPre L) : pair (annS x f) g = pair f (creS x g) :=
  pair_eq_of_basis (annS_creS_basis x) f g

lemma pair_creS (x : L) (f g : SBPre L) : pair (creS x f) g = pair f (annS x g) :=
  pair_eq_of_basis (creS_annS_basis x) f g

lemma pair_lowS (x : L) (f g : SBPre L) : pair (lowS x f) g = pair f (raiseS x g) :=
  pair_eq_of_basis (lowS_raiseS_basis x) f g

lemma pair_raiseS (x : L) (f g : SBPre L) : pair (raiseS x f) g = pair f (lowS x g) :=
  pair_eq_of_basis (raiseS_lowS_basis x) f g


/-- The photon annihilation operator at `x` in the algebra of adjointable operators. -/
def annOpS (x : L) : Adjointable (SBBasis L) :=
  ⟨(annS x, MulOpposite.op (ofEnd (creS x))), by
    rw [mem_adjointable]
    intro f g
    simp only [MulOpposite.unop_op, toEnd_ofEnd]
    exact pair_annS x f g⟩

/-- The photon creation operator at `x`. -/
def creOpS (x : L) : Adjointable (SBBasis L) :=
  ⟨(creS x, MulOpposite.op (ofEnd (annS x))), by
    rw [mem_adjointable]
    intro f g
    simp only [MulOpposite.unop_op, toEnd_ofEnd]
    exact pair_creS x f g⟩

/-- The atom lowering operator `σ⁻` at `x`. -/
def lowOpS (x : L) : Adjointable (SBBasis L) :=
  ⟨(lowS x, MulOpposite.op (ofEnd (raiseS x))), by
    rw [mem_adjointable]
    intro f g
    simp only [MulOpposite.unop_op, toEnd_ofEnd]
    exact pair_lowS x f g⟩

/-- The atom raising operator `σ⁺` at `x`. -/
def raiseOpS (x : L) : Adjointable (SBBasis L) :=
  ⟨(raiseS x, MulOpposite.op (ofEnd (lowS x))), by
    rw [mem_adjointable]
    intro f g
    simp only [MulOpposite.unop_op, toEnd_ofEnd]
    exact pair_raiseS x f g⟩

lemma star_annOpS (x : L) : star (annOpS x) = creOpS x := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show toEnd (MulOpposite.unop (MulOpposite.op (ofEnd (creS x)))) = creS x
    simp [toEnd_ofEnd]
  · rfl

lemma star_lowOpS (x : L) : star (lowOpS x) = raiseOpS x := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show toEnd (MulOpposite.unop (MulOpposite.op (ofEnd (raiseS x)))) = raiseS x
    simp [toEnd_ofEnd]
  · rfl

lemma star_creOpS (x : L) : star (creOpS x) = annOpS x := by
  rw [← star_annOpS, star_star]

lemma star_raiseOpS (x : L) : star (raiseOpS x) = lowOpS x := by
  rw [← star_lowOpS, star_star]

/-- **The Jaynes-Cummings coupling** `g a† σ⁻ + ḡ σ⁺ a` at the site `x`. -/
def jaynesCummings (x : L) (g : ℂ) : Adjointable (SBBasis L) :=
  g • (creOpS x * lowOpS x) + (starRingEnd ℂ g) • (raiseOpS x * annOpS x)

lemma star_jaynesCummings (x : L) (g : ℂ) : star (jaynesCummings x g) = jaynesCummings x g := by
  simp [jaynesCummings, star_add, star_smul, star_mul, star_creOpS, star_lowOpS, star_annOpS,
    star_raiseOpS, Complex.star_def]
  abel

end InfiniteBosons
