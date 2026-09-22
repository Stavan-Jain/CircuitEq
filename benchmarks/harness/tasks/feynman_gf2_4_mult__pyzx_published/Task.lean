import CircuitEq.Semantics

/-! # The task

The two circuits of this run. The harness owns this file: a run that edits
it is rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The first circuit of the pair. -/
def original : Circuit 12 :=
  [H 8, H 9, H 10, H 8, H 8, CX 5 8, Tdg 8, CX 3 8, T 8, CX 5 8, Tdg 8, CX 3 8, T 5, T 8, H 8,
    CX 3 5, T 3, Tdg 5, CX 3 5, H 8, H 8, H 8, CX 6 8, Tdg 8, CX 2 8, T 8, CX 6 8, Tdg 8,
    CX 2 8, T 6, T 8, H 8, CX 2 6, T 2, Tdg 6, CX 2 6, H 8, H 8, H 8, CX 7 8, Tdg 8, CX 1 8,
    T 8, CX 7 8, Tdg 8, CX 1 8, T 7, T 8, H 8, CX 1 7, T 1, Tdg 7, CX 1 7, H 8, H 9, H 9,
    CX 6 9, Tdg 9, CX 3 9, T 9, CX 6 9, Tdg 9, CX 3 9, T 6, T 9, H 9, CX 3 6, T 3, Tdg 6,
    CX 3 6, H 9, H 9, H 9, CX 7 9, Tdg 9, CX 2 9, T 9, CX 7 9, Tdg 9, CX 2 9, T 7, T 9, H 9,
    CX 2 7, T 2, Tdg 7, CX 2 7, H 9, H 10, H 10, CX 7 10, Tdg 10, CX 3 10, T 10, CX 7 10,
    Tdg 10, CX 3 10, T 7, T 10, H 10, CX 3 7, T 3, Tdg 7, CX 3 7, H 10, H 8, H 9, H 10,
    CX 10 11, CX 9 10, CX 8 9, H 8, H 9, H 10, H 11, H 11, H 11, CX 4 11, Tdg 11, CX 3 11,
    T 11, CX 4 11, Tdg 11, CX 3 11, T 4, T 11, H 11, CX 3 4, T 3, Tdg 4, CX 3 4, H 11, H 11,
    H 11, CX 5 11, Tdg 11, CX 2 11, T 11, CX 5 11, Tdg 11, CX 2 11, T 5, T 11, H 11, CX 2 5,
    T 2, Tdg 5, CX 2 5, H 11, H 11, H 11, CX 6 11, Tdg 11, CX 1 11, T 11, CX 6 11, Tdg 11,
    CX 1 11, T 6, T 11, H 11, CX 1 6, T 1, Tdg 6, CX 1 6, H 11, H 11, H 11, CX 7 11, Tdg 11,
    CX 0 11, T 11, CX 7 11, Tdg 11, CX 0 11, T 7, T 11, H 11, CX 0 7, T 0, Tdg 7, CX 0 7,
    H 11, H 10, H 10, CX 4 10, Tdg 10, CX 2 10, T 10, CX 4 10, Tdg 10, CX 2 10, T 4, T 10,
    H 10, CX 2 4, T 2, Tdg 4, CX 2 4, H 10, H 10, H 10, CX 5 10, Tdg 10, CX 1 10, T 10,
    CX 5 10, Tdg 10, CX 1 10, T 5, T 10, H 10, CX 1 5, T 1, Tdg 5, CX 1 5, H 10, H 10, H 10,
    CX 6 10, Tdg 10, CX 0 10, T 10, CX 6 10, Tdg 10, CX 0 10, T 6, T 10, H 10, CX 0 6, T 0,
    Tdg 6, CX 0 6, H 10, H 9, H 9, CX 4 9, Tdg 9, CX 1 9, T 9, CX 4 9, Tdg 9, CX 1 9, T 4,
    T 9, H 9, CX 1 4, T 1, Tdg 4, CX 1 4, H 9, H 9, H 9, CX 5 9, Tdg 9, CX 0 9, T 9, CX 5 9,
    Tdg 9, CX 0 9, T 5, T 9, H 9, CX 0 5, T 0, Tdg 5, CX 0 5, H 9, H 8, H 8, CX 4 8, Tdg 8,
    CX 0 8, T 8, CX 4 8, Tdg 8, CX 0 8, T 4, T 8, H 8, CX 0 4, T 0, Tdg 4, CX 0 4, H 8, H 8,
    H 9, H 10, H 11]

/-- The second circuit, which is claimed to be equivalent to the first. -/
def optimized : Circuit 12 :=
  [Z 0, Z 1, Z 2, Z 3, S 4, S 5, S 6, S 7, H 8, CX 5 8, H 8, H 8, Tdg 8, CX 3 8, T 8, CX 5 8,
    Tdg 8, CX 3 8, S 8, CX 6 8, Tdg 8, CX 2 8, T 8, CX 6 8, Tdg 8, CX 2 8, CX 7 8, Tdg 8,
    CX 1 8, T 8, CX 7 8, Tdg 8, CX 1 8, T 8, H 11, CX 3 5, Tdg 5, CX 3 5, CX 2 6, Tdg 6,
    CX 2 6, CX 1 7, Tdg 7, CX 1 7, H 9, CX 6 9, H 9, H 9, Tdg 9, CX 3 9, T 9, CX 6 9, Tdg 9,
    CX 3 9, S 9, CX 7 9, Tdg 9, CX 2 9, T 9, CX 7 9, Tdg 9, CX 2 9, CX 3 6, Tdg 6, CX 3 6,
    S 6, CX 2 7, Tdg 7, CX 2 7, H 10, CX 7 10, H 10, H 10, Tdg 10, CX 3 10, T 10, CX 7 10,
    Tdg 10, CX 3 10, T 10, CX 11 10, CX 4 11, Tdg 11, CX 3 11, T 11, CX 4 11, Tdg 11, CX 3 11,
    CX 5 11, Tdg 11, CX 2 11, T 11, CX 5 11, Tdg 11, CX 2 11, S 11, CX 6 11, Tdg 11, CX 1 11,
    T 11, CX 6 11, Tdg 11, CX 1 11, CX 3 4, Tdg 4, CX 3 4, CX 2 5, Tdg 5, CX 2 5, CX 1 6,
    Tdg 6, CX 1 6, CX 3 7, Tdg 7, CX 3 7, S 7, CX 10 9, CX 4 10, Tdg 10, CX 2 10, T 10,
    CX 4 10, Tdg 10, CX 2 10, T 10, CX 5 10, Tdg 10, CX 1 10, T 10, CX 5 10, Tdg 10, CX 1 10,
    CX 6 10, Tdg 10, CX 0 10, T 10, CX 6 10, Tdg 10, CX 0 10, S 10, H 10, CX 7 11, Tdg 11,
    CX 0 11, T 11, CX 7 11, Tdg 11, CX 0 11, S 11, H 11, CX 2 4, Tdg 4, CX 2 4, CX 1 5, Tdg 5,
    CX 1 5, S 5, CX 0 6, Tdg 6, CX 0 6, CX 0 7, Tdg 7, CX 0 7, CX 9 8, CX 4 9, Tdg 9, CX 1 9,
    T 9, CX 4 9, Tdg 9, CX 1 9, CX 5 9, Tdg 9, CX 0 9, T 9, CX 5 9, Tdg 9, CX 0 9, S 9, H 9,
    CX 1 4, Tdg 4, CX 1 4, S 4, CX 0 5, Tdg 5, CX 0 5, CX 4 8, Tdg 8, CX 0 8, T 8, CX 4 8,
    Tdg 8, CX 0 8, T 8, H 8, CX 0 4, Tdg 4, CX 0 4]

end Quantum.Circuit.Harness
