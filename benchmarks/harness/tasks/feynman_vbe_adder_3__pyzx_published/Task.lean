import CircuitEq.Semantics

/-! # The task

The two circuits of this run. The harness owns this file: a run that edits
it is rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The first circuit of the pair. -/
def original : Circuit 10 :=
  [H 3, H 6, H 9, H 3, H 3, CX 2 3, Tdg 3, CX 1 3, T 3, CX 2 3, Tdg 3, CX 1 3, T 2, T 3, H 3,
    CX 1 2, T 1, Tdg 2, CX 1 2, H 3, CX 1 2, H 3, H 3, CX 2 3, Tdg 3, CX 0 3, T 3, CX 2 3,
    Tdg 3, CX 0 3, T 2, T 3, H 3, CX 0 2, T 0, Tdg 2, CX 0 2, H 3, H 3, H 6, H 6, CX 5 6,
    Tdg 6, CX 4 6, T 6, CX 5 6, Tdg 6, CX 4 6, T 5, T 6, H 6, CX 4 5, T 4, Tdg 5, CX 4 5, H 6,
    CX 4 5, H 6, H 6, CX 5 6, Tdg 6, CX 3 6, T 6, CX 5 6, Tdg 6, CX 3 6, T 5, T 6, H 6,
    CX 3 5, T 3, Tdg 5, CX 3 5, H 6, H 6, H 9, H 9, CX 8 9, Tdg 9, CX 7 9, T 9, CX 8 9, Tdg 9,
    CX 7 9, T 8, T 9, H 9, CX 7 8, T 7, Tdg 8, CX 7 8, H 9, CX 7 8, H 9, H 9, CX 8 9, Tdg 9,
    CX 6 9, T 9, CX 8 9, Tdg 9, CX 6 9, T 8, T 9, H 9, CX 6 8, T 6, Tdg 8, CX 6 8, H 9,
    CX 6 8, H 9, H 6, H 6, H 6, CX 5 6, Tdg 6, CX 3 6, T 6, CX 5 6, Tdg 6, CX 3 6, T 5, T 6,
    H 6, CX 3 5, T 3, Tdg 5, CX 3 5, H 6, CX 4 5, H 6, H 6, CX 5 6, Tdg 6, CX 4 6, T 6,
    CX 5 6, Tdg 6, CX 4 6, T 5, T 6, H 6, CX 4 5, T 4, Tdg 5, CX 4 5, H 6, CX 3 5, CX 4 5,
    H 6, H 3, H 3, H 3, CX 2 3, Tdg 3, CX 0 3, T 3, CX 2 3, Tdg 3, CX 0 3, T 2, T 3, H 3,
    CX 0 2, T 0, Tdg 2, CX 0 2, H 3, CX 1 2, H 3, H 3, CX 2 3, Tdg 3, CX 1 3, T 3, CX 2 3,
    Tdg 3, CX 1 3, T 2, T 3, H 3, CX 1 2, T 1, Tdg 2, CX 1 2, H 3, CX 0 2, CX 1 2, H 3]

/-- The second circuit, which is claimed to be equivalent to the first. -/
def optimized : Circuit 10 :=
  [S 0, S 1, S 2, H 3, CX 2 3, H 3, H 3, Tdg 3, CX 2 3, CX 1 3, Tdg 3, CX 1 3, CX 0 3, S 4, S 5,
    H 6, CX 5 6, H 6, H 6, Tdg 6, CX 5 6, CX 4 6, Tdg 6, CX 4 6, T 7, T 8, H 9, CX 8 9, H 9,
    H 9, Tdg 9, CX 8 9, CX 7 9, Tdg 9, CX 7 9, CX 1 2, CX 2 3, T 3, CX 2 3, Tdg 3, CX 0 3,
    S 3, H 3, S 3, H 3, CX 0 3, H 3, CX 4 5, CX 5 6, CX 3 6, T 6, CX 5 6, Tdg 6, CX 3 6, S 6,
    H 6, T 6, H 6, CX 5 6, H 6, H 6, CX 3 6, H 6, CX 7 8, CX 8 9, CX 6 9, T 9, CX 8 9, Tdg 9,
    CX 6 9, S 9, H 9, CX 0 2, Sdg 2, CX 0 2, H 3, CX 2 3, H 3, CX 6 8, Tdg 8, H 6, T 6,
    CX 5 6, Tdg 6, CX 3 6, CX 3 5, Sdg 5, CX 3 5, CX 4 5, CX 5 6, Tdg 6, CX 5 6, CX 4 6,
    Tdg 6, CX 4 6, S 6, H 6, CX 3 5, CX 4 5, H 3, T 3, CX 2 3, Tdg 3, CX 0 3, CX 1 2, CX 2 3,
    Tdg 3, CX 1 3, CX 2 3, Tdg 3, CX 1 3, S 3, H 3, CX 1 2, CX 0 2]

end Quantum.Circuit.Harness
