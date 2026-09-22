import CircuitEq.Semantics

/-! # The task

The circuit of this run. The harness owns this file: a run that edits it is
rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The circuit to optimise. -/
def original : Circuit 2 :=
  [T 0, X 0, T 0, X 0, H 1]

end Quantum.Circuit.Harness
