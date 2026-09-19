import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a0 : Circuit 8 :=
  [CX 1 2, CX 7 3]

def b0 : Circuit 8 :=
  [CX 1 2, CX 7 3]

theorem s0 : a0 ≡ᵤ b0 := by
  circuit_simp

end Quantum.Circuit.Harness.Seg
