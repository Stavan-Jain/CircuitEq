import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a17 : Circuit 8 :=
  [Tdg 2, CX 1 3, CX 2 7, T 4, H 6, T 7, H 4, Tdg 6, H 4, CX 7 1, T 7, CX 1 4,
    H 7, Y 5, S 5, T 7, H 6, Z 3, CX 3 6, Tdg 3, CX 5 4, S 5, H 0, H 5, Tdg 6,
    CX 4 1, H 6, Tdg 2, CX 5 4, Sdg 3, CX 5 3, CX 4 0, H 5, CX 6 1, CX 2 6, H 6,
    H 4, X 3, CX 2 4, CX 2 0, T 2, H 5, Tdg 5, Tdg 0, H 2, CX 7 4, T 1, CX 7 4,
    Y 3, H 2, CX 5 0, H 0, T 3, S 3, S 0, S 4, CX 3 0, Sdg 1, Z 5, CX 7 5]

def b17 : Circuit 8 :=
  [CX 1 3, CX 2 7, T 4, H 6, Tdg 6, CX 7 1, S 7, CX 1 4, H 7, Y 5, T 7, H 6,
    CX 3 6, CX 5 4, Z 5, H 0, H 5, Tdg 6, CX 4 1, H 6, CX 5 4, T 3, CX 5 3,
    CX 4 0, CX 6 1, CX 2 6, H 6, H 4, X 3, CX 2 4, CX 2 0, Tdg 2, Tdg 5, Tdg 0,
    Y 3, CX 5 0, H 0, T 3, S 3, S 0, S 4, CX 3 0, Tdg 1, Z 5, CX 7 5]

theorem s17 : a17 ≡ᵤ b17 := by
  circuit_windows
    [([Z 3, Tdg 3, Tdg 2, Sdg 3, T 2],
        [T 3]),
      ([T 7, T 7],
        [S 7]),
      ([H 4, H 4],
        []),
      ([S 5, S 5],
        [Z 5]),
      ([H 5, H 5],
        []),
      ([T 1, Sdg 1],
        [Tdg 1]),
      ([CX 7 4, CX 7 4],
        []),
      ([H 2, H 2],
        [])]

end Quantum.Circuit.Harness.Seg
