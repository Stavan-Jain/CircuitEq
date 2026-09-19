import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a8 : Circuit 8 :=
  [CX 3 1, CX 0 7, CX 7 6, Y 6, Tdg 2, Z 1, H 0, T 6, H 1, S 6, Z 1, Y 4,
    CX 0 6, CX 1 6, H 7, CX 7 3, CX 7 0, CX 3 1]

def b8 : Circuit 8 :=
  [CX 3 1, CX 0 7, CX 7 6, Y 6, Tdg 2, Z 1, H 0, T 6, H 1, S 6, Z 1, Y 4,
    CX 0 6, CX 1 6, H 7, CX 7 3, CX 7 0, CX 3 1]

theorem s8 : a8 ≡ᵤ b8 := by
  circuit_simp

end Quantum.Circuit.Harness.Seg
