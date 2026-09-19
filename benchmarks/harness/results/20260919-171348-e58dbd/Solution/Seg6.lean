import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a6 : Circuit 8 :=
  [X 1, CX 0 6, T 6, Z 4, X 6, CX 2 6, X 0, H 0, T 4, CX 7 5, Z 0, CX 0 4,
    Z 0, X 1, H 3, CX 2 5, CX 3 5, T 5, Tdg 4, Tdg 3, CX 2 7, H 0, X 6, T 6,
    X 1, S 1, CX 1 7, CX 3 6, H 0, CX 1 6, T 5, CX 5 0, CX 0 3, Tdg 6, Sdg 7,
    CX 4 0, CX 5 0, H 6, CX 4 2, S 4, Sdg 1, Z 4, CX 3 4, T 5]

def b6 : Circuit 8 :=
  [CX 0 6, T 6, Z 4, CX 2 6, X 0, H 0, T 4, CX 7 5, CX 0 4, H 3, CX 2 5,
    CX 3 5, Tdg 3, CX 2 7, T 6, X 1, CX 1 7, CX 3 6, CX 1 6, S 5, CX 5 0,
    CX 0 3, Tdg 6, Sdg 7, CX 4 0, CX 5 0, H 6, CX 4 2, T 4, Z 4, CX 3 4, T 5]

theorem s6 : a6 ≡ᵤ b6 := by
  circuit_windows
    [([X 6, X 6],
        []),
      ([Z 0, Z 0],
        []),
      ([Tdg 4, H 0, H 0, S 4],
        [T 4]),
      ([T 5, T 5],
        [S 5]),
      ([X 1, X 1, S 1, Sdg 1],
        [])]

end Quantum.Circuit.Harness.Seg
