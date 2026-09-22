import CircuitEq.Semantics

/-! # The task

The circuit of this run. The harness owns this file: a run that edits it is
rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The circuit to optimise. -/
def original : Circuit 5 :=
  [H 3, CX 1 3, Tdg 3, CX 0 3, T 3, CX 1 3, Tdg 3, CX 0 3, T 1, T 3, H 3, CX 0 1, T 0, Tdg 1,
    CX 0 1, H 4, CX 2 4, Tdg 4, CX 3 4, T 4, CX 2 4, Tdg 4, CX 3 4, T 2, T 4, H 4, CX 3 2,
    T 3, Tdg 2, CX 3 2, H 3, CX 1 3, Tdg 3, CX 0 3, T 3, CX 1 3, Tdg 3, CX 0 3, T 1, T 3, H 3,
    CX 0 1, T 0, Tdg 1, CX 0 1]

end Quantum.Circuit.Harness
