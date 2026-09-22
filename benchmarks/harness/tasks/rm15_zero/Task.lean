import CircuitEq.Semantics

/-! # The task

The two circuits of this run. The harness owns this file: a run that edits
it is rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The first circuit of the pair. -/
def original : Circuit 15 :=
  [H 7, H 3, H 1, H 0, CX 7 8, CX 7 9, CX 7 10, CX 7 11, CX 7 12, CX 7 13, CX 7 14, CX 3 4,
    CX 3 5, CX 3 6, CX 3 11, CX 3 12, CX 3 13, CX 3 14, CX 1 2, CX 1 5, CX 1 6, CX 1 9,
    CX 1 10, CX 1 13, CX 1 14, CX 0 2, CX 0 4, CX 0 6, CX 0 8, CX 0 10, CX 0 12, CX 0 14]

/-- The second circuit, which is claimed to be equivalent to the first. -/
def optimized : Circuit 15 :=
  [H 0, H 1, H 3, CX 3 4, CX 0 4, CX 1 5, CX 3 5, CX 3 6, H 7, CX 7 8, CX 0 8, CX 7 9, CX 1 9,
    CX 7 10, CX 0 12, CX 1 13, CX 0 1, CX 1 2, CX 1 6, CX 3 7, CX 1 10, CX 7 11, CX 7 12,
    CX 7 13, CX 7 14, CX 1 14, CX 0 1, CX 3 7]

end Quantum.Circuit.Harness
