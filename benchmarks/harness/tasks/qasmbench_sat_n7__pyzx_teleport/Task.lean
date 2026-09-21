import CircuitEq.Semantics

/-! # The task

The two circuits of this run. The harness owns this file: a run that edits
it is rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The first circuit of the pair. -/
def original : Circuit 7 :=
  [H 1, H 2, X 3, X 4, X 5, X 1, X 2, H 3, CX 2 3, Tdg 3, CX 1 3, T 3, CX 2 3, Tdg 3, CX 1 3,
    T 2, T 3, H 3, CX 1 2, T 1, Tdg 2, CX 1 2, X 2, H 4, CX 2 4, Tdg 4, CX 1 4, T 4, CX 2 4,
    Tdg 4, CX 1 4, T 2, T 4, H 4, CX 1 2, T 1, Tdg 2, CX 1 2, X 1, X 2, H 5, CX 2 5, Tdg 5,
    CX 1 5, T 5, CX 2 5, Tdg 5, CX 1 5, T 2, T 5, H 5, CX 1 2, T 1, Tdg 2, CX 1 2, X 2, H 6,
    CX 4 6, Tdg 6, CX 3 6, T 6, CX 4 6, Tdg 6, CX 3 6, T 4, T 6, H 6, CX 3 4, T 3, Tdg 4,
    CX 3 4, H 0, CX 6 0, Tdg 0, CX 5 0, T 0, CX 6 0, Tdg 0, CX 5 0, T 6, T 0, H 0, CX 5 6,
    T 5, Tdg 6, CX 5 6, H 6, CX 4 6, Tdg 6, CX 3 6, T 6, CX 4 6, Tdg 6, CX 3 6, T 4, T 6, H 6,
    CX 3 4, T 3, Tdg 4, CX 3 4, X 2, H 5, CX 2 5, Tdg 5, CX 1 5, T 5, CX 2 5, Tdg 5, CX 1 5,
    T 2, T 5, H 5, CX 1 2, T 1, Tdg 2, CX 1 2, X 1, X 2, H 4, CX 2 4, Tdg 4, CX 1 4, T 4,
    CX 2 4, Tdg 4, CX 1 4, T 2, T 4, H 4, CX 1 2, T 1, Tdg 2, CX 1 2, X 2, H 3, CX 2 3, Tdg 3,
    CX 1 3, T 3, CX 2 3, Tdg 3, CX 1 3, T 2, T 3, H 3, CX 1 2, T 1, Tdg 2, CX 1 2, X 1, X 2,
    H 1, H 2, X 0, X 1, X 2, H 0, H 0, CX 2 0, Tdg 0, CX 1 0, T 0, CX 2 0, Tdg 0, CX 1 0, T 2,
    T 0, H 0, CX 1 2, T 1, Tdg 2, CX 1 2, H 0, X 0, X 1, X 2, H 0, H 1, H 2]

/-- The second circuit, which is claimed to be equivalent to the first. -/
def optimized : Circuit 7 :=
  [H 1, Sdg 1, CX 3 2, H 3, Z 3, T 3, CX 1 3, T 3, H 2, S 2, T 2, CX 2 3, T 3, CX 1 3, T 3, H 3,
    S 3, CX 1 2, Tdg 2, CX 1 2, Z 2, T 2, H 4, CX 2 4, H 4, H 4, S 4, T 4, CX 1 4, Tdg 4,
    CX 2 4, T 4, CX 1 4, T 4, CX 6 4, H 6, Tdg 6, CX 3 6, T 6, CX 1 2, T 2, CX 1 2, S 2, T 2,
    H 4, T 4, H 5, CX 2 5, H 5, H 5, Z 5, T 5, CX 1 5, Tdg 5, CX 2 5, Tdg 5, CX 1 5, T 5, H 5,
    T 5, CX 4 6, Tdg 6, CX 3 6, T 6, CX 0 6, H 6, T 6, H 0, Tdg 0, CX 1 2, T 2, CX 1 2, Tdg 2,
    CX 3 4, Tdg 4, CX 3 4, T 4, CX 5 0, H 5, CX 2 5, H 5, T 0, CX 6 0, CX 5 6, Tdg 6, CX 5 6,
    H 6, CX 4 6, H 6, H 6, Tdg 6, CX 3 6, T 6, CX 4 6, Tdg 6, CX 3 6, T 6, H 6, Tdg 0, CX 3 4,
    Tdg 4, CX 3 4, CX 5 0, H 5, T 5, CX 1 5, Tdg 5, CX 2 5, Tdg 5, CX 1 5, T 5, H 5, T 0,
    CX 1 2, T 2, CX 1 2, T 2, H 4, CX 2 4, H 4, H 4, Tdg 4, CX 1 4, Tdg 4, CX 2 4, T 4,
    CX 1 4, T 4, H 4, CX 1 2, T 2, CX 1 2, Tdg 2, H 3, CX 2 3, H 3, H 3, T 3, CX 1 3, T 3,
    CX 2 3, T 3, CX 1 3, T 3, H 3, CX 1 2, Tdg 2, CX 0 2, CX 1 2, H 2, Tdg 2, H 0, Tdg 0, H 1,
    CX 1 0, Tdg 1, Tdg 0, CX 2 0, CX 1 2, Tdg 2, CX 1 2, H 2, Tdg 0, CX 1 0, H 1, Tdg 0, H 0]

end Quantum.Circuit.Harness
