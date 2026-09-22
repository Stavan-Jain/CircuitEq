import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a10 : Circuit 8 :=
  [X 2, CX 6 3, CX 0 5, CX 2 3, Sdg 4, X 2, Y 1, X 0, T 3, T 6, Y 3, Y 2,
    Tdg 5]

def b10 : Circuit 8 :=
  [X 2, CX 6 3, CX 0 5, CX 2 3, Sdg 4, X 2, Y 1, X 0, T 3, T 6, Y 3, Y 2,
    Tdg 5]

theorem s10 : a10 ≡ᵤ b10 := by
  circuit_simp

end Quantum.Circuit.Harness.Seg
