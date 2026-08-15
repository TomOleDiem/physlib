/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Qubit.Hamiltonian
public import Qubit.State
public import Qubit.Measurement
public import Qubit.Control

/-!

# Qubits

This module collects the finite-dimensional quantum mechanics of a two-level system:

* Hermitian Hamiltonians and their unitary one-parameter time evolutions;
* mixed states in Bloch form and their evolution by unitary conjugation;
* finite measurements, Born probabilities, and observable expectation values.
* constant π and π/2 pulses and piecewise-constant pulse sequences.

-/
