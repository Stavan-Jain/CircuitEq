import CircuitEq
import Harness.Task

set_option Elab.async false

namespace Quantum.Circuit.Harness.Seg

open Instr

def a4 : Circuit 8 :=
  [S 5, T 4, Y 3, CX 1 6, T 5, CX 3 2, CX 4 6, T 2, S 7, Tdg 1, X 6, CX 4 3,
    CX 0 3, S 5, H 2, T 0, T 1, Sdg 1, CX 1 7, Y 1, T 3, Y 6, X 6, H 5, H 7,
    Y 1, H 6, X 4, CX 6 5, T 3, T 0, CX 3 6, CX 2 7, CX 3 2, H 4, Z 7, Sdg 2,
    T 7, H 1, Sdg 6, CX 1 6, CX 0 4, CX 2 0, T 4, H 5, S 5, CX 7 5, T 4, T 5,
    Sdg 7, CX 6 3, CX 0 2]

def b4 : Circuit 8 :=
  [T 4, Y 3, CX 1 6, T 5, CX 3 2, CX 4 6, T 2, S 7, X 6, CX 4 3, CX 0 3, Z 5,
    H 2, Sdg 1, CX 1 7, Y 6, X 6, H 5, H 7, H 6, X 4, CX 6 5, S 3, S 0, CX 3 6,
    CX 2 7, CX 3 2, H 4, Sdg 2, T 7, H 1, Sdg 6, CX 1 6, CX 0 4, CX 2 0, H 5,
    S 5, CX 7 5, S 4, T 5, S 7, CX 6 3, CX 0 2]

theorem s4 : a4 ≡ᵤ b4 := by
  circuit_windows
    [([T 0, T 0],
        [S 0]),
      ([Tdg 1, T 1],
        []),
      ([S 5, S 5],
        [Z 5]),
      ([T 3, T 3],
        [S 3]),
      ([Y 1, Y 1, H 1],
        [H 1]),
      ([Z 7, Sdg 7],
        [S 7]),
      ([T 4, T 4],
        [S 4])]

end Quantum.Circuit.Harness.Seg
