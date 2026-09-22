import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a12 : Circuit 8 :=
  [H 2, X 2, Tdg 6, H 6, Z 5, Z 5, CX 1 6, Tdg 4, S 6, T 1, CX 2 7, H 2,
    CX 4 1, CX 4 5, T 4, Sdg 3, Z 1, T 5, X 2, CX 5 6, S 0, Y 6, S 0, S 6,
    CX 3 1, CX 2 4, T 4, T 0, H 7, H 5, CX 0 7, Y 0]

def b12 : Circuit 8 :=
  [H 2, X 2, Tdg 6, H 6, CX 1 6, S 6, T 1, CX 2 7, H 2, CX 4 1, CX 4 5, Sdg 3,
    Z 1, T 5, X 2, CX 5 6, Y 6, Z 0, S 6, CX 3 1, CX 2 4, T 4, T 0, H 7, H 5,
    CX 0 7, Y 0]

theorem s12 : a12 ≡ᵤ b12 := by
  circuit_windows
    [([Z 5, Z 5],
        []),
      ([Tdg 4, T 4],
        []),
      ([S 0, S 0],
        [Z 0])]

end Quantum.Circuit.Harness.Seg
