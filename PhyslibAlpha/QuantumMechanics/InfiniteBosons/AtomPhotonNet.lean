/-
Copyright (c) 2026 Tom Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.InfiniteBosons.OnSiteDynamics
/-!

# The tensor-product local net of the atom-photon lattice

Each cavity carries a photon mode and a two-level atom. The local configuration type is
`ℕ × Bool` with the photon number and the atom state.

## i. Overview

The local Hilbert space of a cavity is `ℓ²(ℕ × Bool) = ℓ²(ℕ) ⊗ ℂ²`. The net of the lattice is
`tensorNet` for this local type. The observables of a finite set of cavities are all bounded
operators on the tensor product. No photon-number sector enters. The free part of the
Hamiltonian `ω a†a + ε σ⁺σ⁻` is a real on-site energy, and `onSiteFlow` gives its dynamics on every
local algebra for any frequencies `ω_x` and `ε_x`.

## ii. Key results

- `InfiniteBosons.atomPhotonNet`: the local net of the lattice.
- `InfiniteBosons.atomPhotonEnergy`: the free on-site energy `ω n + ε [atom excited]`.
- `InfiniteBosons.atomPhotonFlow_incl`: the free dynamics commutes with the inclusions.

## iii. Table of contents

- A. The net
- B. The free dynamics

## iv. References

* B. W. Shore, P. L. Knight, The Jaynes-Cummings model, J. Mod. Opt. 40 (1993) 1195.
-/

@[expose] public section

noncomputable section

namespace InfiniteBosons

variable {L : Type*} [DecidableEq L]

/-- The local net of the atom-photon lattice. -/
def atomPhotonNet (L : Type*) [DecidableEq L] : ProbabilisticTheory.QuasiLocal.AlgebraNet L :=
  tensorNet (fun _ : L => ℕ × Bool)

/-- The free on-site energy `ω n + ε [atom excited]`. -/
def atomPhotonEnergy (ω ε : L → ℝ) (x : L) : ℕ × Bool → ℝ :=
  fun s => ω x * s.1 + if s.2 then ε x else 0

/-- **The free dynamics of the atom-photon lattice commutes with the net inclusions.** -/
theorem atomPhotonFlow_incl (ω ε : L → ℝ) (t : ℝ) {X Y : Finset L} (h : X ≤ Y)
    (T : HilbertSp (CondensedMatter.QuasiLocal.Cfg (fun _ : L => ℕ × Bool) X) →L[ℂ]
      HilbertSp (CondensedMatter.QuasiLocal.Cfg (fun _ : L => ℕ × Bool) X)) :
    (atomPhotonNet L).incl h (onSiteFlow (atomPhotonEnergy ω ε) t X T) =
      onSiteFlow (atomPhotonEnergy ω ε) t Y ((atomPhotonNet L).incl h T) :=
  onSiteFlow_incl (atomPhotonEnergy ω ε) t h T

end InfiniteBosons
