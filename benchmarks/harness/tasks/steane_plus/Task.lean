import CircuitEq.Semantics

/-! # The task

The two circuits of this run. The harness owns this file: a run that edits
it is rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The first circuit of the pair. -/
def original : Circuit 7 :=
  [H 0, H 1, H 3, CX 0 2, CX 0 4, CX 0 6, CX 1 2, CX 1 5, CX 1 6, CX 3 4, CX 3 5, CX 3 6, H 0,
    H 1, H 2, H 3, H 4, H 5, H 6]

/-- The second circuit, which is claimed to be equivalent to the first. -/
def optimized : Circuit 7 :=
  [H 2, CX 2 1, CX 2 0, H 4, CX 4 3, CX 4 0, H 5, CX 5 3, CX 5 1, H 6, CX 6 3, CX 6 1, CX 6 0]

end Quantum.Circuit.Harness
