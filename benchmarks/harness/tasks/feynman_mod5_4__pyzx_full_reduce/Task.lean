import CircuitEq.Semantics

/-! # The task

The two circuits of this run. The harness owns this file: a run that edits
it is rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The first circuit of the pair. -/
def original : Circuit 5 :=
  [X 4, H 4, H 4, H 4, CX 3 4, Tdg 4, CX 0 4, T 4, CX 3 4, Tdg 4, CX 0 4, T 3, T 4, H 4, CX 0 3,
    T 0, Tdg 3, CX 0 3, H 4, H 4, H 4, CX 3 4, Tdg 4, CX 2 4, T 4, CX 3 4, Tdg 4, CX 2 4, T 3,
    T 4, H 4, CX 2 3, T 2, Tdg 3, CX 2 3, H 4, H 4, CX 3 4, H 4, H 4, H 4, CX 2 4, Tdg 4,
    CX 1 4, T 4, CX 2 4, Tdg 4, CX 1 4, T 2, T 4, H 4, CX 1 2, T 1, Tdg 2, CX 1 2, H 4, H 4,
    CX 2 4, H 4, H 4, H 4, CX 1 4, Tdg 4, CX 0 4, T 4, CX 1 4, Tdg 4, CX 0 4, T 1, T 4, H 4,
    CX 0 1, T 0, Tdg 1, CX 0 1, H 4, H 4, CX 1 4, CX 0 4]

/-- The second circuit, which is claimed to be equivalent to the first. -/
def optimized : Circuit 5 :=
  [CX 1 2, H 4, CX 4 0, CX 0 3, CX 3 2, T 3, CX 1 0, T 0, CX 0 2, Tdg 2, CX 3 2, CX 3 0, CX 4 3,
    CX 3 2, Tdg 3, T 2, CX 2 3, CX 0 2, T 2, CX 2 3, Tdg 3, CX 1 3, CX 1 0, CX 4 2, H 4,
    Tdg 2, CX 1 2, CX 0 3, CX 3 0, CX 0 3]

end Quantum.Circuit.Harness
