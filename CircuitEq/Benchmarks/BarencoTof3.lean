/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Tactic

/-!
# `barenco_tof_3`, T-count optimised by PyZX phase teleportation

The `barenco_tof_3` benchmark circuit: a triply-controlled NOT on qubits
`0, 1, 2 → 4` through the dirty ancilla `3`, in the Barenco et al. (1995)
Lemma 7.2 pattern `CCX 2 3 4; CCX 0 1 3; CCX 2 3 4; CCX 0 1 3`, each Toffoli
in the textbook seven-`T` decomposition, so 60 gates and T-count 28. PyZX
0.9.0's `teleport_reduce` followed by `basic_optimization` keeps the gate
skeleton and lowers the T-count to 24: the two `T` gates on each of qubits
`0` and `2`, which are only ever CNOT controls, merge into one `S`. It also
rewrites three `H; CX` pairs as `CZ; H` and cancels the Hadamard pair on
qubit `4` between the first and the third Toffoli. See
`benchmarks/barenco_tof_3/` for the fixtures.

The alignment was found by `scripts/tcount_survey.py` and has six windows,
every one on a single wire: the two `T · T = S` merges, the inserted `H; H`
pairs of the three `CZ` rewrites (a `CZ` is `H; CX; H` in this alphabet),
and the cancelled `H; H` pair. Every other change is a phase gate moving
through the control of a CNOT, which `Instr.CanCommute` licenses;
`circuit_windows` checks the alignment, and the kernel never evaluates more
than one qubit.
-/

namespace Quantum.Circuit.Benchmarks.BarencoTof3

open Instr

/-- `barenco_tof_3`: four Toffolis in the seven-`T` decomposition, QASM order. -/
def original : Circuit 5 :=
  [H 4, CX 3 4, Tdg 4, CX 2 4, T 4, CX 3 4, Tdg 4, CX 2 4, T 3, T 4, H 4,
    CX 2 3, T 2, Tdg 3, CX 2 3, H 3, CX 1 3, Tdg 3, CX 0 3, T 3, CX 1 3, Tdg 3,
    CX 0 3, T 1, T 3, H 3, CX 0 1, T 0, Tdg 1, CX 0 1, H 4, CX 3 4, Tdg 4,
    CX 2 4, T 4, CX 3 4, Tdg 4, CX 2 4, T 3, T 4, H 4, CX 2 3, T 2, Tdg 3,
    CX 2 3, H 3, CX 1 3, Tdg 3, CX 0 3, T 3, CX 1 3, Tdg 3, CX 0 3, T 1, T 3,
    H 3, CX 0 1, T 0, Tdg 1, CX 0 1]

/-- Actual PyZX output, QASM order, with each `cz c t` as `H t; CX c t; H t`
and `rz(k·π/4)` as the corresponding diagonal Clifford+T gate. -/
def optimized : Circuit 5 :=
  [S 0, T 1, S 2, T 3, H 4, CX 3 4, H 4, H 4, Tdg 4, CX 2 4, T 4, CX 3 4,
    Tdg 4, CX 2 4, T 4, CX 2 3, Tdg 3, CX 2 3, H 3, CX 1 3, H 3, H 3, Tdg 3,
    CX 0 3, T 3, CX 1 3, Tdg 3, CX 0 3, T 3, H 3, T 3, CX 3 4, Tdg 4, CX 2 4,
    T 4, CX 3 4, Tdg 4, CX 2 4, T 4, H 4, CX 0 1, Tdg 1, CX 0 1, T 1, CX 2 3,
    Tdg 3, CX 2 3, H 3, CX 1 3, H 3, H 3, Tdg 3, CX 0 3, T 3, CX 1 3, Tdg 3,
    CX 0 3, T 3, H 3, CX 0 1, Tdg 1, CX 0 1]

/-- The 60-gate original equals the T-count-24 PyZX circuit on every input. -/
theorem original_equiv_optimized : original ≡ᵤ optimized := by
  circuit_windows
    [([T 0, T 0], [S 0]),
      ([T 2, T 2], [S 2]),
      ([], [H 4, H 4]),
      ([H 4, H 4], []),
      ([], [H 3, H 3]),
      ([], [H 3, H 3])]

end Quantum.Circuit.Benchmarks.BarencoTof3
