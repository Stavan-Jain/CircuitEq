/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import CircuitEq.Tactic

/-!
# The four-bit Cuccaro adder against phase teleportation

The survey's original alignment, checked by bounded certificate replay.
The windows and the endpoint circuits are unchanged from the recorded
survey. See `benchmarks/cuccaro_4/README.md` for provenance and measurements.
-/

set_option Elab.async false

namespace Quantum.Circuit.Benchmarks.Cuccaro4

open Instr

/-- The four-bit Cuccaro adder, in QASM order. -/
def original : Circuit 10 :=
  [CX 2 1, CX 2 0, H 2, CX 1 2, Tdg 2, CX 0 2, T 2, CX 1 2, Tdg 2, CX 0 2, T 1, T 2, H 2,
    CX 0 1, T 0, Tdg 1, CX 0 1, CX 4 3, CX 4 2, H 4, CX 3 4, Tdg 4, CX 2 4, T 4, CX 3 4, Tdg 4,
    CX 2 4, T 3, T 4, H 4, CX 2 3, T 2, Tdg 3, CX 2 3, CX 6 5, CX 6 4, H 6, CX 5 6, Tdg 6,
    CX 4 6, T 6, CX 5 6, Tdg 6, CX 4 6, T 5, T 6, H 6, CX 4 5, T 4, Tdg 5, CX 4 5, CX 8 7,
    CX 8 6, H 8, CX 7 8, Tdg 8, CX 6 8, T 8, CX 7 8, Tdg 8, CX 6 8, T 7, T 8, H 8, CX 6 7, T 6,
    Tdg 7, CX 6 7, CX 8 9, H 8, CX 7 8, Tdg 8, CX 6 8, T 8, CX 7 8, Tdg 8, CX 6 8, T 7, T 8,
    H 8, CX 6 7, T 6, Tdg 7, CX 6 7, CX 8 6, CX 6 7, H 6, CX 5 6, Tdg 6, CX 4 6, T 6, CX 5 6,
    Tdg 6, CX 4 6, T 5, T 6, H 6, CX 4 5, T 4, Tdg 5, CX 4 5, CX 6 4, CX 4 5, H 4, CX 3 4,
    Tdg 4, CX 2 4, T 4, CX 3 4, Tdg 4, CX 2 4, T 3, T 4, H 4, CX 2 3, T 2, Tdg 3, CX 2 3,
    CX 4 2, CX 2 3, H 2, CX 1 2, Tdg 2, CX 0 2, T 2, CX 1 2, Tdg 2, CX 0 2, T 1, T 2, H 2,
    CX 0 1, T 0, Tdg 1, CX 0 1, CX 2 0, CX 0 1]

/-- PyZX 0.9.0 phase-teleportation output, with CZ expanded as H; CX; H. -/
def optimized : Circuit 10 :=
  [Sdg 1, CX 2 0, CX 2 1, S 2, H 2, Tdg 2, Sdg 3, CX 4 3, S 4, Sdg 5, CX 6 5, S 6, Sdg 7,
    CX 8 7, S 8, S 0, S 1, T 1, CX 0 2, T 2, CX 1 2, Tdg 2, CX 0 2, T 2, S 3, T 3, H 4, CX 2 4,
    H 4, H 4, Tdg 4, S 5, T 5, S 7, T 7, CX 0 1, Tdg 1, CX 0 1, T 1, H 2, S 2, CX 2 4, T 4,
    CX 3 4, Tdg 4, CX 2 4, T 4, H 6, CX 4 6, H 6, H 6, Tdg 6, CX 2 3, Tdg 3, CX 2 3, T 3, H 4,
    S 4, CX 4 6, T 6, CX 5 6, Tdg 6, CX 4 6, T 6, H 8, CX 6 8, H 8, H 8, Tdg 8, CX 4 5, Tdg 5,
    CX 4 5, T 5, H 6, S 6, CX 6 8, T 8, CX 7 8, Tdg 8, CX 6 8, T 8, H 8, CX 8 9, CX 6 7, Tdg 7,
    CX 6 7, T 7, H 8, CX 7 8, H 8, H 8, Tdg 8, CX 6 8, T 8, CX 7 8, Tdg 8, CX 6 8, T 8, H 8,
    CX 6 7, Tdg 7, CX 6 7, CX 8 6, H 6, CX 5 6, H 6, CX 6 7, H 6, Tdg 6, CX 4 6, T 6, CX 5 6,
    Tdg 6, CX 4 6, T 6, H 6, CX 4 5, Tdg 5, CX 4 5, CX 6 4, H 4, CX 3 4, H 4, CX 4 5, H 4,
    Tdg 4, CX 2 4, T 4, CX 3 4, Tdg 4, CX 2 4, T 4, H 4, CX 2 3, Tdg 3, CX 2 3, CX 4 2, H 2,
    CX 1 2, H 2, CX 2 3, H 2, Tdg 2, CX 0 2, T 2, CX 1 2, Tdg 2, CX 0 2, T 2, H 2, CX 0 1,
    Tdg 1, CX 0 1, CX 2 0, CX 0 1]

/-- The original eight-window alignment certifies exact equivalence. -/
theorem original_equiv_optimized : original ≡ᵤ optimized := by
  circuit_windows [
    ([CX 2 1, CX 2 0, H 2, CX 1 2, T 0, T 0],
      [Sdg 1, CX 2 0, CX 2 1, S 2, H 2, S 0, S 1]),
    ([CX 0 2, T 2, CX 1 2, Tdg 2, CX 0 2, T 2, H 2, CX 4 3, CX 4 2, H 4, CX 3 4, T 3, T 2, T 2],
      [Sdg 3, CX 4 3, S 4, CX 0 2, T 2, CX 1 2, Tdg 2, CX 0 2, T 2, S 3, T 3, H 4, CX 2 4, H 4,
      H 4, H 2, S 2]),
    ([Tdg 4, CX 2 4, T 4, CX 3 4, Tdg 4, CX 2 4, T 4, H 4, CX 6 5, CX 6 4, H 6, CX 5 6, T 5,
      T 4, T 4],
      [Sdg 5, CX 6 5, S 6, Tdg 4, S 5, T 5, CX 2 4, T 4, CX 3 4, Tdg 4, CX 2 4, T 4, H 6,
      CX 4 6, H 6, H 6, H 4, S 4]),
    ([Tdg 6, CX 4 6, T 6, CX 5 6, Tdg 6, CX 4 6, T 6, H 6, CX 8 7, CX 8 6, H 8, CX 7 8, T 7,
      T 6, T 6],
      [Sdg 7, CX 8 7, S 8, S 7, T 7, Tdg 6, CX 4 6, T 6, CX 5 6, Tdg 6, CX 4 6, T 6, H 8,
      CX 6 8, H 8, H 8, H 6, S 6]),
    ([],
      [H 8, H 8]),
    ([CX 6 7, H 6, CX 5 6],
      [H 6, CX 5 6, H 6, CX 6 7, H 6]),
    ([CX 4 5, H 4, CX 3 4],
      [H 4, CX 3 4, H 4, CX 4 5, H 4]),
    ([CX 2 3, H 2, CX 1 2],
      [H 2, CX 1 2, H 2, CX 2 3, H 2])]

end Quantum.Circuit.Benchmarks.Cuccaro4
