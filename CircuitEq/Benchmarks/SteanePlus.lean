/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Layers
import CircuitEq.Tactic

/-!
# Steane logical plus-state encoder: original versus PyZX

QECUnitaryCircuits commit `3d96b5fe14a393f8eeefe02f45e5d23916b85a4d`,
`qec_circuits/steane_713_encode_plusL.qasm`, optimized with PyZX 0.9.0.
See `benchmarks/steane_plus/` for the input, output, and reproduction steps.

The original has 19 gates; PyZX produces 13. The proof has three steps:
read the original as a seed layer, a CNOT network, and a full Hadamard
layer; apply `layer_cnotNetwork_hLayer`, which moves the final layer to the
front, reversing every CNOT, and cancels it against the seed; and let
`circuit_simp` reorder the commuting remainder into PyZX's gate order. No
step enumerates the seven-qubit basis, and the block theorem holds for
every register size.
-/

namespace Quantum.Circuit.Benchmarks.SteanePlus

open Instr

/-- Original Steane encoder, in QASM instruction order. -/
def original : Circuit 7 :=
  [H 0, H 1, H 3,
    CX 0 2, CX 0 4, CX 0 6, CX 1 2, CX 1 5, CX 1 6, CX 3 4, CX 3 5, CX 3 6,
    H 0, H 1, H 2, H 3, H 4, H 5, H 6]

/-- Actual PyZX output, in QASM instruction order. -/
def optimized : Circuit 7 :=
  [H 2, CX 2 1, CX 2 0, H 4, CX 4 3, CX 4 0,
    H 5, CX 5 3, CX 5 1, H 6, CX 6 3, CX 6 1, CX 6 0]

/-- The original's nine CNOTs as control-target edges, in time order. -/
def edges : List (Fin 7 × Fin 7) :=
  [(0, 2), (0, 4), (0, 6), (1, 2), (1, 5), (1, 6), (3, 4), (3, 5), (3, 6)]

/-- The original 19-gate circuit equals the 13-gate PyZX circuit on every
input. -/
theorem original_equiv_optimized : original ≡ᵤ optimized :=
  calc original
      = layer .H [0, 1, 3] ++ cnotNetwork edges ++ hLayer 7 := rfl
    _ ≡ᵤ _ := layer_cnotNetwork_hLayer [0, 1, 3] (by decide) edges (by decide)
    _ ≡ᵤ optimized := by circuit_simp

end Quantum.Circuit.Benchmarks.SteanePlus
