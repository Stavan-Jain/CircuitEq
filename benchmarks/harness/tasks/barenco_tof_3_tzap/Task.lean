import CircuitEq.Semantics

/-! # The task

The two circuits of this run. The harness owns this file: a run that edits
it is rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The first circuit of the pair. -/
def original : Circuit 5 :=
  [H 4, CX 3 4, Tdg 4, CX 2 4, T 4, CX 3 4, Tdg 4, CX 2 4, T 3, T 4, H 4, CX 2 3, T 2, Tdg 3,
    CX 2 3, H 3, CX 1 3, Tdg 3, CX 0 3, T 3, CX 1 3, Tdg 3, CX 0 3, T 1, T 3, H 3, CX 0 1,
    T 0, Tdg 1, CX 0 1, H 4, CX 3 4, Tdg 4, CX 2 4, T 4, CX 3 4, Tdg 4, CX 2 4, T 3, T 4, H 4,
    CX 2 3, T 2, Tdg 3, CX 2 3, H 3, CX 1 3, Tdg 3, CX 0 3, T 3, CX 1 3, Tdg 3, CX 0 3, T 1,
    T 3, H 3, CX 0 1, T 0, Tdg 1, CX 0 1]

/-- The second circuit, which is claimed to be equivalent to the first. -/
def optimized : Circuit 5 :=
  [H 4, T 3, CX 4 3, Tdg 3, CX 2 3, T 3, CX 4 3, Tdg 3, CX 2 3, H 3, CX 1 3, Tdg 3, CX 0 3, T 3,
    CX 1 3, Tdg 3, CX 0 3, T 3, H 3, T 3, CX 4 3, Tdg 3, CX 2 3, T 3, CX 4 3, H 4, CX 2 4,
    Tdg 3, CX 2 3, H 3, CX 1 3, Tdg 3, CX 0 3, T 3, CX 1 3, Tdg 3, H 0, CX 1 0, H 0, CX 0 3,
    T 3, H 3]

end Quantum.Circuit.Harness
