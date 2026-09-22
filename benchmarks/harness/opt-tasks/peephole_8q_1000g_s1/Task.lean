import CircuitEq.Semantics

/-! # The task

The circuit of this run. The harness owns this file: a run that edits it is
rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The circuit to optimise. -/
def original : Circuit 8 :=
  [CX 1 2, CX 7 3, Tdg 3, CX 0 6, H 0, S 4, S 3, Tdg 1, X 0, CX 0 3, S 6, S 3, Sdg 7, T 5,
    CX 3 6, T 4, X 6, Z 1, CX 4 0, S 6, T 3, H 7, Z 6, Tdg 0, T 6, H 2, H 5, CX 1 6, CX 6 2,
    T 0, T 4, S 6, Tdg 2, T 0, Sdg 3, H 5, Y 5, T 4, Tdg 0, H 2, T 3, H 0, T 5, T 3, X 6, T 5,
    H 0, T 5, T 0, Sdg 2, T 2, Z 4, CX 1 0, Z 7, CX 4 1, CX 2 7, CX 2 1, CX 2 5, CX 4 3, S 7,
    T 0, H 5, H 3, CX 4 5, T 3, Y 6, Sdg 0, CX 6 1, CX 2 3, S 6, T 3, Y 7, CX 0 3, Tdg 5,
    Tdg 6, CX 4 1, Y 0, H 1, H 4, S 6, T 2, CX 0 4, Sdg 7, CX 0 3, CX 1 7, T 6, Tdg 7, CX 6 2,
    T 0, H 6, X 0, CX 5 6, Y 2, H 3, CX 1 6, H 5, X 7, Sdg 3, CX 0 7, CX 2 4, CX 5 4, T 4,
    H 5, CX 3 6, X 7, CX 1 2, CX 1 3, Z 2, Z 5, CX 6 0, T 3, T 4, H 4, T 1, T 4, CX 0 6,
    CX 0 7, H 0, CX 6 1, CX 2 5, CX 1 3, X 6, Sdg 4, T 7, H 3, Tdg 0, CX 4 5, Tdg 7, H 6,
    CX 5 4, Y 1, CX 7 5, H 2, T 4, CX 5 0, Sdg 1, Y 7, CX 5 1, H 4, CX 2 7, Sdg 4, CX 1 4,
    Tdg 1, CX 0 6, CX 1 2, T 1, S 0, Tdg 4, S 5, T 2, CX 5 0, T 2, CX 2 1, Z 5, H 4, CX 3 1,
    T 0, Sdg 3, CX 6 4, CX 3 2, Sdg 7, Sdg 4, T 7, CX 5 1, CX 0 6, Tdg 6, Y 0, CX 5 4, CX 2 1,
    CX 4 3, T 2, Tdg 3, T 2, T 7, X 3, CX 7 5, T 3, S 5, T 4, Y 3, CX 1 6, T 5, CX 3 2,
    CX 4 6, T 2, S 7, Tdg 1, X 6, CX 4 3, CX 0 3, S 5, H 2, T 0, T 1, Sdg 1, CX 1 7, Y 1, T 3,
    Y 6, X 6, H 5, H 7, Y 1, H 6, X 4, CX 6 5, T 3, T 0, CX 3 6, CX 2 7, CX 3 2, H 4, Z 7,
    Sdg 2, T 7, H 1, Sdg 6, CX 1 6, CX 0 4, CX 2 0, T 4, H 5, S 5, CX 7 5, T 4, T 5, Sdg 7,
    CX 6 3, CX 0 2, Tdg 3, Y 7, Tdg 6, X 4, S 7, Tdg 3, H 0, Tdg 6, Y 5, Z 1, T 3, Tdg 4,
    Tdg 6, S 2, Tdg 6, Sdg 2, Sdg 0, H 4, Sdg 6, Z 4, CX 4 3, CX 0 2, T 6, CX 1 5, T 2, T 2,
    S 6, Tdg 4, Tdg 3, T 3, X 4, CX 5 3, T 0, CX 4 2, Tdg 3, H 6, CX 4 6, Tdg 3, CX 3 6,
    Tdg 6, H 6, X 3, Sdg 3, CX 2 6, Y 7, Tdg 2, Tdg 4, T 2, CX 2 5, T 4, S 3, CX 3 5, S 1,
    CX 6 2, T 1, Y 0, CX 0 6, CX 0 3, S 7, H 4, CX 2 0, CX 3 7, T 2, Y 3, Z 7, T 6, CX 4 2,
    T 1, X 1, CX 0 6, T 6, Z 4, X 6, CX 2 6, X 0, H 0, T 4, CX 7 5, Z 0, CX 0 4, Z 0, X 1,
    H 3, CX 2 5, CX 3 5, T 5, Tdg 4, Tdg 3, CX 2 7, H 0, X 6, T 6, X 1, S 1, CX 1 7, CX 3 6,
    H 0, CX 1 6, T 5, CX 5 0, CX 0 3, Tdg 6, Sdg 7, CX 4 0, CX 5 0, H 6, CX 4 2, S 4, Sdg 1,
    Z 4, CX 3 4, T 5, X 6, Y 7, CX 7 4, Y 0, X 4, S 3, H 5, CX 5 1, T 0, H 5, H 5, H 5, S 0,
    T 2, H 5, Sdg 1, T 4, T 5, X 6, Sdg 1, X 0, CX 7 4, Z 4, Sdg 5, H 5, H 7, Tdg 5, T 2,
    CX 4 5, CX 2 0, CX 6 5, Tdg 1, Y 4, S 3, CX 1 6, CX 3 5, Z 6, CX 5 6, T 4, CX 3 4, T 3,
    H 5, T 3, Sdg 1, Sdg 4, H 0, S 6, T 7, CX 6 0, H 7, CX 4 5, S 0, T 4, T 5, Y 4, T 6,
    Tdg 4, T 2, T 2, T 2, CX 0 3, S 0, H 6, CX 0 7, X 0, H 7, CX 5 7, S 7, Sdg 6, T 1, T 2,
    H 0, Y 4, H 2, Tdg 4, X 6, CX 4 5, H 4, H 7, CX 7 3, S 1, CX 3 1, CX 0 7, CX 7 6, Y 6,
    Tdg 2, Z 1, H 0, T 6, H 1, S 6, Z 1, Y 4, CX 0 6, CX 1 6, H 7, CX 7 3, CX 7 0, CX 3 1,
    T 6, S 4, Z 3, Sdg 5, Z 1, CX 5 7, CX 7 2, S 1, CX 4 2, S 6, CX 4 1, H 0, T 2, X 4,
    CX 4 2, T 7, H 7, CX 2 4, S 7, T 0, T 2, Tdg 3, H 7, T 1, CX 2 5, CX 1 5, T 0, T 1,
    CX 3 4, T 4, H 0, Sdg 4, Z 3, CX 3 2, S 5, CX 6 0, CX 5 1, CX 2 5, T 5, CX 1 2, H 4, T 5,
    CX 2 3, H 3, CX 5 2, CX 5 0, H 2, Tdg 4, H 7, T 6, H 3, Tdg 2, CX 1 7, CX 6 2, T 4, T 4,
    T 6, S 5, CX 5 4, T 0, Tdg 7, S 2, CX 2 5, Z 3, T 5, H 4, CX 6 7, H 1, Y 2, CX 0 4, Y 2,
    H 1, T 6, Tdg 6, CX 5 3, H 7, CX 7 6, CX 0 6, CX 1 4, CX 5 4, CX 5 6, T 3, X 3, CX 5 6,
    CX 0 5, H 5, CX 0 4, H 6, H 5, T 3, Tdg 2, CX 1 4, CX 7 2, S 1, Y 0, T 3, H 2, H 3,
    CX 5 2, Tdg 7, S 5, T 3, H 6, T 7, X 2, CX 6 3, CX 0 5, CX 2 3, Sdg 4, X 2, Y 1, X 0, T 3,
    T 6, Y 3, Y 2, Tdg 5, Tdg 1, Sdg 2, CX 0 4, CX 3 6, CX 3 5, T 1, CX 7 0, T 0, H 1, Tdg 7,
    CX 3 6, CX 4 3, CX 6 1, Tdg 5, Sdg 7, Y 6, T 6, S 3, T 4, H 2, CX 4 6, CX 1 5, H 2,
    CX 4 2, H 7, CX 2 7, CX 1 6, T 3, T 3, T 7, H 3, CX 1 7, Sdg 0, CX 6 3, H 2, Tdg 2, Tdg 1,
    X 6, CX 3 5, S 6, H 2, CX 2 7, T 4, CX 4 1, S 0, CX 1 4, H 7, CX 0 7, Z 5, CX 2 5, Z 1,
    Z 3, S 6, CX 3 6, X 2, Sdg 4, S 1, Sdg 6, Tdg 3, CX 2 5, Tdg 3, Z 4, Sdg 6, H 7, CX 2 1,
    T 7, S 7, CX 5 1, CX 0 6, H 7, CX 2 4, T 6, T 3, CX 1 2, X 7, CX 2 1, Z 4, T 1, Y 6,
    CX 6 7, T 4, H 5, T 0, T 7, CX 4 7, S 2, Tdg 4, CX 5 3, H 0, T 1, CX 0 7, X 5, X 0, Tdg 1,
    T 1, Z 7, H 0, X 5, H 2, X 2, Tdg 6, H 6, Z 5, Z 5, CX 1 6, Tdg 4, S 6, T 1, CX 2 7, H 2,
    CX 4 1, CX 4 5, T 4, Sdg 3, Z 1, T 5, X 2, CX 5 6, S 0, Y 6, S 0, S 6, CX 3 1, CX 2 4,
    T 4, T 0, H 7, H 5, CX 0 7, Y 0, CX 0 7, CX 1 4, Sdg 0, X 3, CX 4 1, T 5, H 1, CX 2 1,
    S 4, Y 6, Tdg 5, CX 0 7, Tdg 6, Z 5, H 6, CX 7 6, Z 7, Tdg 7, Tdg 2, Z 4, T 6, Tdg 4,
    CX 0 4, S 7, T 5, CX 7 1, S 5, S 2, H 6, CX 1 2, Z 0, CX 0 2, H 5, H 0, CX 1 2, CX 1 7,
    Sdg 4, Y 5, CX 2 6, Sdg 5, H 6, H 7, Sdg 1, X 6, X 0, Tdg 3, CX 6 3, CX 2 5, Y 5, CX 4 3,
    T 2, CX 5 3, T 7, H 1, Tdg 4, Sdg 4, H 4, S 7, CX 3 6, Tdg 4, H 3, CX 2 1, CX 0 7, CX 0 3,
    S 0, CX 0 7, T 5, Sdg 0, T 7, CX 4 7, T 4, X 2, CX 0 1, Y 7, CX 5 3, CX 2 4, Tdg 2,
    CX 2 7, X 1, CX 5 7, CX 7 1, CX 4 2, CX 1 3, CX 3 5, CX 0 1, CX 1 0, Y 3, X 4, T 3, S 4,
    Sdg 5, H 7, Sdg 6, Z 6, CX 3 6, Z 5, X 1, CX 6 2, T 5, S 5, H 5, H 6, Y 0, H 4, CX 2 6,
    T 2, CX 2 1, CX 4 1, H 5, CX 7 2, CX 2 4, H 7, X 2, S 1, S 7, T 0, S 3, Tdg 5, T 5, Z 5,
    H 1, CX 6 0, Y 3, CX 4 2, T 3, H 0, CX 4 5, T 3, CX 2 1, H 4, CX 3 0, H 6, Z 7, Tdg 7,
    CX 5 1, H 1, CX 3 6, CX 3 0, CX 5 1, CX 5 0, Tdg 3, CX 3 4, H 0, CX 7 4, CX 0 6, H 5,
    CX 1 4, H 4, Tdg 1, T 6, Z 4, CX 5 0, Y 5, CX 4 6, Sdg 4, Y 6, Y 4, CX 4 0, CX 6 4,
    CX 5 6, Tdg 7, T 4, Tdg 5, CX 1 3, H 3, H 7, CX 7 5, CX 3 0, S 0, T 7, T 5, X 2, T 7, H 6,
    T 7, CX 5 0, Z 5, Z 7, CX 4 6, CX 5 1, CX 7 6, CX 5 4, H 2, T 7, CX 3 4, CX 2 4, CX 6 3,
    CX 4 1, Y 5, CX 4 1, T 6, T 4, CX 4 7, Z 3, CX 2 5, CX 5 0, H 2, Tdg 7, T 7, H 3, CX 1 0,
    T 2, T 2, T 0, Tdg 7, T 4, X 2, Z 4, CX 0 4, CX 1 4, CX 5 3, H 1, H 7, CX 6 3, H 1,
    CX 6 4, S 7, T 5, CX 2 4, CX 3 7, Tdg 2, CX 1 3, CX 2 7, T 4, H 6, T 7, H 4, Tdg 6, H 4,
    CX 7 1, T 7, CX 1 4, H 7, Y 5, S 5, T 7, H 6, Z 3, CX 3 6, Tdg 3, CX 5 4, S 5, H 0, H 5,
    Tdg 6, CX 4 1, H 6, Tdg 2, CX 5 4, Sdg 3, CX 5 3, CX 4 0, H 5, CX 6 1, CX 2 6, H 6, H 4,
    X 3, CX 2 4, CX 2 0, T 2, H 5, Tdg 5, Tdg 0, H 2, CX 7 4, T 1, CX 7 4, Y 3, H 2, CX 5 0,
    H 0, T 3, S 3, S 0, S 4, CX 3 0, Sdg 1, Z 5, CX 7 5, CX 6 2, Tdg 6, H 5, Y 3, CX 2 1,
    CX 3 5, H 7, T 0, CX 0 7, H 4, H 3, S 5, X 5, Tdg 0, T 2, S 5, Tdg 5, CX 3 5, Tdg 6, Y 0,
    H 2, CX 7 5, CX 1 6, Sdg 6, CX 1 7, T 6, Tdg 6, CX 6 3, Z 5, H 1, CX 5 0, CX 1 7, CX 1 0]

end Quantum.Circuit.Harness
