/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Tactic

/-!
# `tof_3`, T-count optimised by PyZX phase teleportation

The standard `tof_3` benchmark circuit: a doubly-controlled NOT on qubits
`0, 1 → 4` computed through the clean ancilla `3` as three Toffolis
`CCX 0 1 3; CCX 3 2 4; CCX 0 1 3`, each in the textbook seven-`T`
decomposition, so 45 gates and T-count 21. PyZX 0.9.0's `teleport_reduce`
followed by `basic_optimization` keeps the gate skeleton and lowers the
T-count to 19: the two `T` gates on qubit 0, which is only ever a control,
merge into one `S`. It also commutes phases forward and rewrites three
`H; CX` pairs as `CZ; H`. See `benchmarks/tof_3/` for the fixtures.

The alignment has four windows: the `T · T = S` merge on one wire, the two
`H; CX = H; CX; H; H` rewrites (a `CZ` is `H; CX; H` in this alphabet) on
two wires, and the `CZ` that PyZX commuted through a CNOT on its control,
on three wires. Every other change is a phase gate moving through the
control of a CNOT, which `Instr.CanCommute` licenses; `circuit_windows`
checks the alignment, and the largest kernel evaluation is on three qubits.
-/

namespace Quantum.Circuit.Benchmarks.Tof3

open Instr

/-- `tof_3`: three Toffolis in the seven-`T` decomposition, QASM order. -/
def original : Circuit 5 :=
  [H 3, CX 1 3, Tdg 3, CX 0 3, T 3, CX 1 3, Tdg 3, CX 0 3,
    T 1, T 3, H 3, CX 0 1, T 0, Tdg 1, CX 0 1,
    H 4, CX 2 4, Tdg 4, CX 3 4, T 4, CX 2 4, Tdg 4, CX 3 4,
    T 2, T 4, H 4, CX 3 2, T 3, Tdg 2, CX 3 2,
    H 3, CX 1 3, Tdg 3, CX 0 3, T 3, CX 1 3, Tdg 3, CX 0 3,
    T 1, T 3, H 3, CX 0 1, T 0, Tdg 1, CX 0 1]

/-- Actual PyZX output, QASM order, with each `cz c t` as `H t; CX c t; H t`
and `rz(k·π/4)` as the corresponding diagonal Clifford+T gate. -/
def optimized : Circuit 5 :=
  [S 0, T 1, T 2, H 3, CX 1 3, H 3, H 3, Tdg 3,
    CX 0 3, T 3, CX 1 3, Tdg 3, CX 0 3, T 3, H 3, T 3,
    H 4, CX 2 4, H 4, H 4, Tdg 4, CX 3 4, T 4, CX 2 4,
    Tdg 4, CX 3 4, T 4, H 4, CX 0 1, Tdg 1, CX 0 1, T 1,
    CX 3 2, H 3, CX 1 3, H 3, Tdg 2, CX 3 2, H 3, Tdg 3,
    CX 0 3, T 3, CX 1 3, Tdg 3, CX 0 3, T 3, H 3, CX 0 1,
    Tdg 1, CX 0 1]

/-- The 45-gate original equals the T-count-19 PyZX circuit on every input. -/
theorem original_equiv_optimized : original ≡ᵤ optimized := by
  circuit_windows
    [([T 0, T 0], [S 0]),
      ([H 3, CX 1 3], [H 3, CX 1 3, H 3, H 3]),
      ([H 4, CX 2 4], [H 4, CX 2 4, H 4, H 4]),
      ([Tdg 2, CX 3 2, H 3, CX 1 3], [H 3, CX 1 3, H 3, Tdg 2, CX 3 2, H 3])]

end Quantum.Circuit.Benchmarks.Tof3
