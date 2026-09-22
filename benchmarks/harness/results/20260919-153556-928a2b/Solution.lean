import CircuitEq
import Harness.Task

namespace Quantum.Circuit.Harness

open Instr

/-- The claim holds. -/
theorem equiv : original ≡ᵤ optimized := by
  sorry

/-- The claim fails. -/
theorem not_equiv : ¬ (original ≡ᵤ optimized) := by
  sorry

end Quantum.Circuit.Harness
