import CircuitEq.Semantics

/-! # The task

The circuit of this run. The harness owns this file: a run that edits it is
rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The circuit to optimise. -/
def original : Circuit 3 :=
  [H 0, T 1, T 1, CX 0 1, H 2, H 2, T 2, CX 1 2]

end Quantum.Circuit.Harness
