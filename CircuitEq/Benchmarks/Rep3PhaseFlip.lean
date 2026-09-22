/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Tactic

/-!
# QECUnitaryCircuits: three-qubit phase-flip repetition encoder

The original comes from `qec_circuits/rep3_phaseflip_encode.qasm` at
QECUnitaryCircuits commit `3d96b5fe14a393f8eeefe02f45e5d23916b85a4d`.
The optimized circuit is the output of PyZX 0.9.0 `full_reduce`, circuit
extraction, and `basic_optimization`. Both QASM files and reproduction
instructions are in `benchmarks/rep3_phaseflip/`.

PyZX reorders the Hadamards without reducing the five-gate count, so the
benchmark pair closes by `circuit_simp`, which moves each gate of the PyZX
order through the gates on other wires it must pass. On three distinct wires
of any register the same fact is `original_equiv_optimized.rename`.
-/

namespace Quantum.Circuit.Benchmarks.Rep3PhaseFlip

open Instr

/-- The original QECUnitaryCircuits encoder, in QASM instruction order. -/
def original : Circuit 3 := [CX 0 1, CX 0 2, H 0, H 1, H 2]

/-- The actual PyZX output, in QASM instruction order. -/
def optimized : Circuit 3 := [CX 0 1, H 1, CX 0 2, H 2, H 0]

/-- Exact equivalence of the original benchmark and the PyZX output, found
by the tactic: each step is a checked commutation of a gate past a gate on
other wires. -/
theorem original_equiv_optimized : original ≡ᵤ optimized := by
  circuit_simp

end Quantum.Circuit.Benchmarks.Rep3PhaseFlip
