import CircuitEq.Semantics

/-! # The task

The two circuits of this run. The harness owns this file: a run that edits
it is rejected.
-/

namespace Quantum.Circuit.Harness

open Instr

/-- The first circuit of the pair. -/
def original : Circuit 3 :=
  [CX 0 1, CX 0 2, H 0, H 1, H 2]

/-- The second circuit, which is claimed to be equivalent to the first. -/
def optimized : Circuit 3 :=
  [CX 0 1, CX 0 2, H 2, H 0]

end Quantum.Circuit.Harness
