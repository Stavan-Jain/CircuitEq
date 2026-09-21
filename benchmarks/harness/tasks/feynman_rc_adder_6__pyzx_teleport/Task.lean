import CircuitEq.Semantics

/-! # The task

The two circuits of this run. The harness owns this file: a run that edits
it is rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The first circuit of the pair. -/
def original : Circuit 14 :=
  [CX 4 3, CX 6 5, CX 8 7, CX 10 9, CX 12 11, CX 4 2, H 2, H 2, H 2, CX 1 2, Tdg 2, CX 0 2, T 2,
    CX 1 2, Tdg 2, CX 0 2, T 1, T 2, H 2, CX 0 1, T 0, Tdg 1, CX 0 1, H 2, H 2, CX 6 4, H 4,
    H 4, H 4, CX 3 4, Tdg 4, CX 2 4, T 4, CX 3 4, Tdg 4, CX 2 4, T 3, T 4, H 4, CX 2 3, T 2,
    Tdg 3, CX 2 3, H 4, H 4, CX 8 6, H 6, H 6, H 6, CX 5 6, Tdg 6, CX 4 6, T 6, CX 5 6, Tdg 6,
    CX 4 6, T 5, T 6, H 6, CX 4 5, T 4, Tdg 5, CX 4 5, H 6, H 6, CX 10 8, H 8, H 8, H 8,
    CX 7 8, Tdg 8, CX 6 8, T 8, CX 7 8, Tdg 8, CX 6 8, T 7, T 8, H 8, CX 6 7, T 6, Tdg 7,
    CX 6 7, H 8, H 8, CX 12 10, H 10, H 10, H 10, CX 9 10, Tdg 10, CX 8 10, T 10, CX 9 10,
    Tdg 10, CX 8 10, T 9, T 10, H 10, CX 8 9, T 8, Tdg 9, CX 8 9, H 10, H 10, CX 12 13, X 3,
    X 5, X 7, X 9, H 13, H 13, H 13, CX 11 13, Tdg 13, CX 10 13, T 13, CX 11 13, Tdg 13,
    CX 10 13, T 11, T 13, H 13, CX 10 11, T 10, Tdg 11, CX 10 11, H 13, H 13, CX 2 3, CX 4 5,
    CX 6 7, CX 8 9, CX 10 11, H 10, H 10, H 10, CX 9 10, Tdg 10, CX 8 10, T 10, CX 9 10,
    Tdg 10, CX 8 10, T 9, T 10, H 10, CX 8 9, T 8, Tdg 9, CX 8 9, H 10, H 10, H 8, H 8, H 8,
    CX 7 8, Tdg 8, CX 6 8, T 8, CX 7 8, Tdg 8, CX 6 8, T 7, T 8, H 8, CX 6 7, T 6, Tdg 7,
    CX 6 7, H 8, H 8, X 9, CX 12 10, H 6, H 6, H 6, CX 5 6, Tdg 6, CX 4 6, T 6, CX 5 6, Tdg 6,
    CX 4 6, T 5, T 6, H 6, CX 4 5, T 4, Tdg 5, CX 4 5, H 6, H 6, X 7, CX 10 8, H 4, H 4, H 4,
    CX 3 4, Tdg 4, CX 2 4, T 4, CX 3 4, Tdg 4, CX 2 4, T 3, T 4, H 4, CX 2 3, T 2, Tdg 3,
    CX 2 3, H 4, H 4, X 5, CX 8 6, H 2, H 2, H 2, CX 1 2, Tdg 2, CX 0 2, T 2, CX 1 2, Tdg 2,
    CX 0 2, T 1, T 2, H 2, CX 0 1, T 0, Tdg 1, CX 0 1, H 2, H 2, X 3, CX 6 4, CX 4 2, CX 1 0,
    CX 4 3, CX 6 5, CX 8 7, CX 10 9, CX 12 11]

/-- The second circuit, which is claimed to be equivalent to the first. -/
def optimized : Circuit 14 :=
  [S 0, T 1, CX 4 3, CX 4 2, CX 6 5, CX 6 4, CX 8 7, CX 8 6, CX 10 9, CX 10 8, CX 12 11,
    CX 12 10, CX 12 13, H 2, CX 1 2, H 2, H 2, Tdg 2, CX 0 2, T 2, CX 1 2, Tdg 2, CX 0 2, T 2,
    H 2, S 2, T 3, H 4, CX 3 4, H 4, H 4, Tdg 4, CX 2 4, T 4, CX 3 4, Tdg 4, CX 2 4, T 4, H 4,
    S 4, T 5, H 6, CX 5 6, H 6, H 6, Tdg 6, CX 4 6, T 6, CX 5 6, Tdg 6, CX 4 6, T 6, H 6, S 6,
    T 7, H 8, CX 7 8, H 8, H 8, Tdg 8, CX 6 8, T 8, CX 7 8, Tdg 8, CX 6 8, T 8, H 8, S 8, T 9,
    H 10, CX 9 10, H 10, H 10, Tdg 10, CX 8 10, T 10, CX 9 10, Tdg 10, CX 8 10, T 10, H 10,
    T 10, T 11, H 13, CX 11 13, H 13, H 13, Tdg 13, CX 10 13, T 13, CX 11 13, Tdg 13,
    CX 10 13, T 13, H 13, CX 0 1, Tdg 1, CX 0 1, T 1, H 2, CX 1 2, H 2, CX 2 3, Sdg 3, H 4,
    CX 3 4, H 4, CX 4 5, Sdg 5, H 6, CX 5 6, H 6, CX 6 7, Sdg 7, H 8, CX 7 8, H 8, CX 8 9,
    Sdg 9, H 10, CX 9 10, H 10, CX 10 11, Tdg 11, CX 12 11, H 10, T 10, CX 8 10, Tdg 10,
    CX 9 10, Tdg 10, CX 8 10, T 10, H 12, CX 10 12, H 12, CX 8 9, T 9, CX 8 9, H 8, T 8,
    CX 6 8, Tdg 8, CX 7 8, Tdg 8, CX 6 8, T 8, CX 8 10, H 10, CX 10 9, CX 6 7, T 7, CX 6 7,
    H 6, T 6, CX 4 6, Tdg 6, CX 5 6, Tdg 6, CX 4 6, T 6, CX 6 8, H 8, CX 8 7, CX 4 5, T 5,
    CX 4 5, H 4, T 4, CX 2 4, Tdg 4, CX 3 4, Tdg 4, CX 2 4, T 4, CX 4 6, H 6, CX 6 5, CX 2 3,
    T 3, CX 2 3, H 2, Tdg 2, CX 0 2, T 2, CX 1 2, Tdg 2, CX 0 2, T 2, CX 2 4, H 4, CX 4 3,
    CX 1 0, H 2, Tdg 0]

end Quantum.Circuit.Harness
