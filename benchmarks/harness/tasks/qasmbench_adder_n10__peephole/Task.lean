import CircuitEq.Semantics

/-! # The task

The two circuits of this run. The harness owns this file: a run that edits
it is rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The first circuit of the pair. -/
def original : Circuit 10 :=
  [X 1, X 5, X 6, X 7, X 8, CX 1 5, CX 1 0, H 1, CX 5 1, Tdg 1, CX 0 1, T 1, CX 5 1, Tdg 1,
    CX 0 1, T 5, T 1, H 1, CX 0 5, T 0, Tdg 5, CX 0 5, CX 2 6, CX 2 1, H 2, CX 6 2, Tdg 2,
    CX 1 2, T 2, CX 6 2, Tdg 2, CX 1 2, T 6, T 2, H 2, CX 1 6, T 1, Tdg 6, CX 1 6, CX 3 7,
    CX 3 2, H 3, CX 7 3, Tdg 3, CX 2 3, T 3, CX 7 3, Tdg 3, CX 2 3, T 7, T 3, H 3, CX 2 7,
    T 2, Tdg 7, CX 2 7, CX 4 8, CX 4 3, H 4, CX 8 4, Tdg 4, CX 3 4, T 4, CX 8 4, Tdg 4,
    CX 3 4, T 8, T 4, H 4, CX 3 8, T 3, Tdg 8, CX 3 8, CX 4 9, H 4, CX 8 4, Tdg 4, CX 3 4,
    T 4, CX 8 4, Tdg 4, CX 3 4, T 8, T 4, H 4, CX 3 8, T 3, Tdg 8, CX 3 8, CX 4 3, CX 3 8,
    H 3, CX 7 3, Tdg 3, CX 2 3, T 3, CX 7 3, Tdg 3, CX 2 3, T 7, T 3, H 3, CX 2 7, T 2, Tdg 7,
    CX 2 7, CX 3 2, CX 2 7, H 2, CX 6 2, Tdg 2, CX 1 2, T 2, CX 6 2, Tdg 2, CX 1 2, T 6, T 2,
    H 2, CX 1 6, T 1, Tdg 6, CX 1 6, CX 2 1, CX 1 6, H 1, CX 5 1, Tdg 1, CX 0 1, T 1, CX 5 1,
    Tdg 1, CX 0 1, T 5, T 1, H 1, CX 0 5, T 0, Tdg 5, CX 0 5, CX 1 0, CX 0 5]

/-- The second circuit, which is claimed to be equivalent to the first. -/
def optimized : Circuit 10 :=
  [X 1, X 5, X 6, X 7, X 8, CX 1 5, CX 1 0, H 1, CX 5 1, Tdg 1, CX 0 1, T 1, CX 5 1, Tdg 1,
    CX 0 1, T 5, T 1, H 1, CX 0 5, Tdg 5, CX 0 5, CX 2 6, CX 2 1, H 2, CX 6 2, Tdg 2, CX 1 2,
    T 2, CX 6 2, Tdg 2, CX 1 2, T 6, T 2, H 2, CX 1 6, Tdg 6, CX 1 6, CX 3 7, CX 3 2, H 3,
    CX 7 3, Tdg 3, CX 2 3, T 3, CX 7 3, Tdg 3, CX 2 3, T 7, T 3, H 3, CX 2 7, Tdg 7, CX 2 7,
    CX 4 8, CX 4 3, H 4, CX 8 4, Tdg 4, CX 3 4, T 4, CX 8 4, Tdg 4, CX 3 4, T 8, T 4, H 4,
    CX 3 8, Tdg 8, CX 3 8, CX 4 9, H 4, CX 8 4, Tdg 4, CX 3 4, T 4, CX 8 4, Tdg 4, CX 3 4,
    T 8, T 4, H 4, CX 3 8, S 3, Tdg 8, CX 3 8, CX 4 3, CX 3 8, H 3, CX 7 3, Tdg 3, CX 2 3,
    T 3, CX 7 3, Tdg 3, CX 2 3, T 7, T 3, H 3, CX 2 7, S 2, Tdg 7, CX 2 7, CX 3 2, CX 2 7,
    H 2, CX 6 2, Tdg 2, CX 1 2, T 2, CX 6 2, Tdg 2, CX 1 2, T 6, T 2, H 2, CX 1 6, S 1, Tdg 6,
    CX 1 6, CX 2 1, CX 1 6, H 1, CX 5 1, Tdg 1, CX 0 1, T 1, CX 5 1, Tdg 1, CX 0 1, T 5, T 1,
    H 1, CX 0 5, S 0, Tdg 5, CX 0 5, CX 1 0, CX 0 5]

end Quantum.Circuit.Harness
