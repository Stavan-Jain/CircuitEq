import CircuitEq.Semantics

/-! # The task

The two circuits of this run. The harness owns this file: a run that edits
it is rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The first circuit of the pair. -/
def original : Circuit 9 :=
  [H 5, H 5, H 5, CX 1 5, Tdg 5, CX 0 5, T 5, CX 1 5, Tdg 5, CX 0 5, T 1, T 5, H 5, CX 0 1, T 0,
    Tdg 1, CX 0 1, H 5, H 5, H 6, H 6, H 6, CX 5 6, Tdg 6, CX 2 6, T 6, CX 5 6, Tdg 6, CX 2 6,
    T 5, T 6, H 6, CX 2 5, T 2, Tdg 5, CX 2 5, H 6, H 6, H 7, H 7, H 7, CX 6 7, Tdg 7, CX 3 7,
    T 7, CX 6 7, Tdg 7, CX 3 7, T 6, T 7, H 7, CX 3 6, T 3, Tdg 6, CX 3 6, H 7, H 7, H 8, H 8,
    H 8, CX 7 8, Tdg 8, CX 4 8, T 8, CX 7 8, Tdg 8, CX 4 8, T 7, T 8, H 8, CX 4 7, T 4, Tdg 7,
    CX 4 7, H 8, H 8, H 7, H 7, H 7, CX 6 7, Tdg 7, CX 3 7, T 7, CX 6 7, Tdg 7, CX 3 7, T 6,
    T 7, H 7, CX 3 6, T 3, Tdg 6, CX 3 6, H 7, H 7, H 6, H 6, H 6, CX 5 6, Tdg 6, CX 2 6, T 6,
    CX 5 6, Tdg 6, CX 2 6, T 5, T 6, H 6, CX 2 5, T 2, Tdg 5, CX 2 5, H 6, H 6, H 5, H 5, H 5,
    CX 1 5, Tdg 5, CX 0 5, T 5, CX 1 5, Tdg 5, CX 0 5, T 1, T 5, H 5, CX 0 1, T 0, Tdg 1,
    CX 0 1, H 5, H 5]

/-- The second circuit, which is claimed to be equivalent to the first. -/
def optimized : Circuit 9 :=
  [S 0, T 1, S 2, S 3, T 4, H 5, CX 1 5, H 5, H 5, Tdg 5, CX 0 5, T 5, CX 1 5, Tdg 5, CX 0 5,
    T 5, CX 6 5, H 6, Tdg 6, CX 2 6, T 6, CX 0 1, Tdg 1, CX 0 1, T 1, H 5, T 5, CX 5 6, Tdg 6,
    CX 2 6, T 6, CX 7 6, H 7, Tdg 7, CX 3 7, T 7, CX 2 5, Tdg 5, CX 2 5, T 5, H 6, T 6,
    CX 6 7, Tdg 7, CX 3 7, T 7, CX 8 7, H 8, Tdg 8, CX 4 8, T 8, CX 3 6, Tdg 6, CX 3 6, T 6,
    H 7, T 7, CX 7 8, Tdg 8, CX 4 8, T 8, H 8, CX 4 7, Tdg 7, CX 4 7, H 7, CX 6 7, H 7, H 7,
    Tdg 7, CX 3 7, T 7, CX 6 7, Tdg 7, CX 3 7, T 7, H 7, CX 3 6, Tdg 6, CX 3 6, H 6, CX 5 6,
    H 6, H 6, Tdg 6, CX 2 6, T 6, CX 5 6, Tdg 6, CX 2 6, T 6, H 6, CX 2 5, Tdg 5, CX 2 5, H 5,
    CX 1 5, H 5, H 5, Tdg 5, CX 0 5, T 5, CX 1 5, Tdg 5, CX 0 5, T 5, H 5, CX 0 1, Tdg 1,
    CX 0 1]

end Quantum.Circuit.Harness
